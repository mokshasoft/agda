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
--     state and no @IO@ -- and in the fast evaluator, which runs in 'ST'.
--     Nothing can be written from there through the ordinary state.
--
--   So the counters live in a global 'IORef', bumped through
--   'unsafePerformIO', exactly as @Agda.Benchmarking.benchmarks@ and
--   @billToPure@ already do for the benchmarking of pure code, and as
--   "Agda.TypeChecking.Reduce.Monad" already does for debug output from
--   'ReduceM'.  A 'Data.HashMap.Strict.insertWith' forces the one value it
--   inserts and copies one path of the map, so a tick costs O(log keys)
--   rather than O(keys).
--
--   == What the numbers mean, and do not
--
--   [They count forced evaluations.]  A tick fires when the value it guards
--     is demanded, since that is the only thing laziness lets it mean.  For
--     the reduction counters that is the intended reading: work not forced is
--     work not done.
--
--   [They are process-global.]  As with the benchmarking counters, every
--     module checked in the process contributes, including imported modules
--     that had no up-to-date interface.  So which modules were checked is
--     recorded too ('noteChecked'): two reports are comparable only when
--     they checked the same modules.
--
--   [They are not synchronised.]  Concurrent ticks could in principle lose an
--     increment.  Agda's reduction is single-threaded, and a counter is a
--     diagnostic rather than a proof, so this is not defended against.
module Agda.TypeChecking.ProfileCounters
  ( -- * The store
    Counters (..)
  , getCounters
  , countersRequested
    -- * Ticking
  , tickUnfold
  , countUnfold
  , tickConversion
    -- * Which modules were checked
  , noteChecked
  , getChecked
  ) where

import Data.IORef
import Data.Maybe (isJust)
import qualified Data.HashMap.Strict as HMap
import qualified Data.Set as Set

import System.IO.Unsafe (unsafePerformIO)

import Agda.Syntax.Abstract.Name (QName)

import Agda.Interaction.Options.HasOptions (HasOptions (..))
import Agda.Interaction.Options.Types (optCountersFile)
import Agda.TypeChecking.Monad.Debug (MonadDebug, hasProfileOption)

import qualified Agda.Utils.ProfileOptions as Profile

---------------------------------------------------------------------------
-- * The store
---------------------------------------------------------------------------

-- | One map per counter, all keyed by the definition the number is about.
--
--   A counter is added here when something ticks it, not before: a slot
--   nothing fills would be reported as "measured, nothing found".
data Counters = Counters
  { cUnfold   :: !(HMap.HashMap QName Int)
      -- ^ Times a definition's body was unfolded during reduction.
  , cConv     :: !(HMap.HashMap QName Int)
      -- ^ Times a definition's head took part in a conversion check.
  }

emptyCounters :: Counters
emptyCounters = Counters HMap.empty HMap.empty

-- | The counters.  Global because the hot hooks run in 'ReduceM', which is
--   pure; see the module header.
counters :: IORef Counters
counters = unsafePerformIO $ newIORef emptyCounters
{-# NOINLINE counters #-}

getCounters :: IO Counters
getCounters = readIORef counters

-- | Is the counters report wanted at all?  It is when @--profile=reduction@
--   is on, or when @--counters-file@ is given.
--
--   @--profile=conversion@ alone does not ask for it: that option predates
--   the counters, and a run using it must neither write a file it did not
--   ask for nor pay for per-definition ticks.
countersRequested :: (HasOptions m, MonadDebug m) => m Bool
countersRequested = do
  red <- hasProfileOption Profile.Reduction
  if red then pure True else isJust . optCountersFile <$> commandLineOptions

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

incUnfold :: QName -> Counters -> Counters
incUnfold q = addTo cUnfold (\ m c -> c { cUnfold = m }) q 1

-- | A definition's body was unfolded.  §4.1: the direct measurement of
--   \"evaluated N times instead of once\", and the number that distinguishes
--   an expensive definition from a cheap one in a hot loop -- which demand
--   opposite fixes.
tickUnfold :: Monad m => QName -> m ()
tickUnfold q = bumpM (incUnfold q)

-- | 'tickUnfold' for the fast evaluator, whose machine runs in 'ST': the
--   tick fires when the returned value is forced, which for the next machine
--   step is when the machine takes it.
countUnfold :: QName -> a -> a
countUnfold q = bump (incUnfold q)

-- | A definition's head took part in a conversion check.  §4.6: the aggregate
--   tick already exists in "Agda.TypeChecking.Conversion"; only the key was
--   missing, which is the difference between \"conversion is hot\" and
--   \"conversion is hot because of @f@\".
tickConversion :: Monad m => QName -> m ()
tickConversion q = bumpM (addTo cConv (\ m c -> c { cConv = m }) q 1)

---------------------------------------------------------------------------
-- * Which modules were checked
---------------------------------------------------------------------------

-- | The modules type-checked in this process, as opposed to loaded from an
--   interface.  Only those contribute counts of their own checking.  Kept by
--   printed name, which is how the report lists them.
checked :: IORef (Set.Set String)
checked = unsafePerformIO $ newIORef Set.empty
{-# NOINLINE checked #-}

noteChecked :: String -> IO ()
noteChecked m = modifyIORef' checked (Set.insert m)

getChecked :: IO [String]
getChecked = Set.toList <$> readIORef checked
