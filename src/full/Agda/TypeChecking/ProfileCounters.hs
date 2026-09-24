{-# OPTIONS_GHC -Wunused-imports #-}

-- | Per-definition profiling counters.
--
--   @--profile=definitions@ answers /where did the time go/.  These answer
--   /how many times was this evaluated/, which is the question that localises
--   a pathology in a large development: the dominant failure mode there is not
--   a slow definition but a cheap one re-evaluated at many use sites, and a
--   time profile smears that cost across the consumers rather than attributing
--   it to the definition.
--
--   == Why this is not 'Agda.TypeChecking.Monad.Statistics'
--
--   Two reasons, and both are hard constraints rather than preferences.
--
--   [The existing counters are O(n) per tick.]  @modifyCounter@ deep-forces
--     the whole statistics map on every call -- deliberately, and documented
--     there: strictness in the map's /structure/ is what is wanted, and
--     @rnf@ is how it is obtained.  That is fine for a handful of aggregate
--     string keys.  Keying per 'QName' turns it into thousands of keys ticked
--     millions of times, which is quadratic in the workload being measured:
--     the profiler would dominate its own measurement.
--
--   [The hot hooks are not in a monad that can do anything.]  The counter for
--     unfoldings belongs in @unfoldDefinitionStep@, which runs in 'ReduceM' --
--     @newtype ReduceM a = ReduceM (ReduceEnv -> a)@, a pure reader with no
--     state and no @IO@.  Nothing can be written from there through the
--     ordinary state.
--
--   So the counters live in a global 'IORef', bumped through
--   'unsafePerformIO', exactly as @Agda.Benchmarking.benchmarks@ and
--   @billToPure@ already do for the benchmarking of pure code, and as
--   "Agda.TypeChecking.Reduce.Monad" already does for debug output from
--   'ReduceM'.  A 'Data.HashMap.Strict.insertWith' forces the one value it
--   inserts and nothing else, so a tick is O(1) rather than O(keys).
--
--   == What the numbers mean, and do not
--
--   [They count forced evaluations.]  A tick fires when the value it guards
--     is demanded, since that is the only thing laziness lets it mean.  For
--     the reduction counters that is the intended reading: work not forced is
--     work not done.
--
--   [They are process-global.]  As with the benchmarking counters, a process
--     that checks several files accumulates across them.  'resetCounters'
--     exists for callers that want per-file numbers.
--
--   [They are not synchronised.]  Concurrent ticks could in principle lose an
--     increment.  Agda's reduction is single-threaded, and a counter is a
--     diagnostic rather than a proof, so this is not defended against.
module Agda.TypeChecking.ProfileCounters
  ( -- * The store
    Counters (..)
  , emptyCounters
  , getCounters
  , resetCounters
    -- * Ticking
  , tickUnfold
  , tickConversion
  , tickWakeup
  , recordNormalFormSize
  , recordSerialisedSize
    -- * Reading
  , topBy
  ) where

import Data.IORef
import Data.List (sortOn)
import qualified Data.HashMap.Strict as HMap

import System.IO.Unsafe (unsafePerformIO)

import Agda.Syntax.Abstract.Name (QName)

---------------------------------------------------------------------------
-- * The store
---------------------------------------------------------------------------

-- | One map per counter, all keyed by the definition the number is about.
data Counters = Counters
  { cUnfold   :: !(HMap.HashMap QName Int)
      -- ^ Times a definition's body was unfolded during reduction.
  , cConv     :: !(HMap.HashMap QName Int)
      -- ^ Times a definition's head took part in a conversion check.
  , cWakeup   :: !(HMap.HashMap QName Int)
      -- ^ Times a postponed constraint mentioning a definition was woken.
  , cSerSize  :: !(HMap.HashMap QName Int)
      -- ^ Serialised size of a definition, in bytes.
  , cMaxSize  :: !(HMap.HashMap QName Int)
      -- ^ Largest term a definition's unfolding produced, in nodes.
  }

emptyCounters :: Counters
emptyCounters = Counters HMap.empty HMap.empty HMap.empty HMap.empty HMap.empty

-- | The counters.  Global because the hot hooks run in 'ReduceM', which is
--   pure; see the module header.
counters :: IORef Counters
counters = unsafePerformIO $ newIORef emptyCounters
{-# NOINLINE counters #-}

getCounters :: IO Counters
getCounters = readIORef counters

-- | Start again.  A process that checks several modules otherwise reports
--   their sum, which for a per-file report is not what is wanted.
resetCounters :: IO ()
resetCounters = writeIORef counters emptyCounters

---------------------------------------------------------------------------
-- * Ticking
---------------------------------------------------------------------------

-- | Bump a counter and return the value the caller was going to return
--   anyway.
--
--   'NOINLINE' is not decoration: without it GHC is entitled to float the
--   'unsafePerformIO' out of a loop, or to common up two ticks, and the count
--   would silently be wrong.  This is the same shape as
--   @Agda.Benchmarking.billToPure@.
bump :: (Counters -> Counters) -> a -> a
bump f x = unsafePerformIO $ do
  modifyIORef' counters f
  return x
{-# NOINLINE bump #-}

-- | A tick as an action in any monad.
--
--   Monad-agnostic on purpose.  Conversion checking runs under 'PureTCM',
--   which has no 'MonadIO', and reduction runs in 'ReduceM', which is a bare
--   reader -- so a tick that needed @liftIO@ could not be placed at either of
--   the sites that matter.  Sequencing the returned action is what forces the
--   bump; this is the shape of @Agda.Benchmarking.billToPure@.
bumpM :: Monad m => (Counters -> Counters) -> m ()
bumpM f = bump f (return ())
{-# NOINLINE bumpM #-}

-- | @insertWith@ from the strict map forces the combined value and leaves the
--   rest of the map alone, which is the whole point -- see the module header
--   on why the existing statistics counters cannot be used here.
addTo
  :: (Counters -> HMap.HashMap QName Int)
  -> (HMap.HashMap QName Int -> Counters -> Counters)
  -> QName -> Int -> Counters -> Counters
addTo get set q n c = set (HMap.insertWith (+) q n (get c)) c

maxIn
  :: (Counters -> HMap.HashMap QName Int)
  -> (HMap.HashMap QName Int -> Counters -> Counters)
  -> QName -> Int -> Counters -> Counters
maxIn get set q n c = set (HMap.insertWith max q n (get c)) c

-- | A definition's body was unfolded.  §4.1: the direct measurement of
--   \"evaluated N times instead of once\", and the number that distinguishes
--   an expensive definition from a cheap one in a hot loop -- which demand
--   opposite fixes.
tickUnfold :: Monad m => QName -> m ()
tickUnfold q = bumpM (addTo cUnfold (\ m c -> c { cUnfold = m }) q 1)

-- | A definition's head took part in a conversion check.  §4.6: the aggregate
--   tick already exists in "Agda.TypeChecking.Conversion"; only the key was
--   missing, which is the difference between \"conversion is hot\" and
--   \"conversion is hot because of @f@\".
--
tickConversion :: Monad m => QName -> m ()
tickConversion q = bumpM (addTo cConv (\ m c -> c { cConv = m }) q 1)

-- | A postponed constraint mentioning this definition was woken and
--   re-attempted.  §4.7: separates \"expensive once\" from \"cheap but
--   retried\", which demand different fixes.
tickWakeup :: Monad m => QName -> m ()
tickWakeup q = bumpM (addTo cWakeup (\ m c -> c { cWakeup = m }) q 1)

-- | §4.8.  Run-independent, and a good CI signal: a definition whose
--   serialised size jumps tenfold is worth looking at even when the build
--   still passes.
recordSerialisedSize :: Monad m => QName -> Int -> m ()
recordSerialisedSize q n = bumpM (maxIn cSerSize (\ m c -> c { cSerSize = m }) q n)

-- | §4.5.  Two definitions with equal unfold counts can differ by orders of
--   magnitude in the size of what they unfold /to/, and that difference is
--   what turns a slow build into an impossible one.
recordNormalFormSize :: Monad m => QName -> Int -> m ()
recordNormalFormSize q n = bumpM (maxIn cMaxSize (\ m c -> c { cMaxSize = m }) q n)

---------------------------------------------------------------------------
-- * Reading
---------------------------------------------------------------------------

-- | The @n@ largest entries, descending.  Ties break on the name so that two
--   runs of the same development order them the same way.
topBy :: Int -> HMap.HashMap QName Int -> [(QName, Int)]
topBy n = take' . sortOn (\ (q, k) -> (negate k, show q)) . HMap.toList
  where
    take' | n <= 0    = id
          | otherwise = take n
