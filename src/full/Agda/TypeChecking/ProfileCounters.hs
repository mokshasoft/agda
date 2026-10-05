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
--   [They count the project's checking, of anything.]  Ticks count only
--     while a module of the project is being checked ('envProfileCounting'),
--     so a library re-checked for want of an up-to-date interface does not
--     add the work of checking itself.  What is unfolded is counted wherever
--     it is defined: a definition in the project that forces a library
--     function thousands of times shows up, often only, as that library
--     function's count.
--
--   [They say who caused them.]  Checking is divided into sites
--     ('ProfileSite'): the definitions, and the work that belongs to no one
--     definition -- a module application, the constraint solving after a
--     declaration, the checks after a mutual block.
--     Each unfolding is also attributed to the site being checked when it
--     happened ('envCheckingDefinitions'), since a count on a library
--     function says what was hot but not which line of the project made it
--     so.
--
--   [Time and memory are measured per site.]  CPU time, and the bytes
--     allocated from GHC's per-thread allocation counter, read when a site's
--     checking begins and ends: cheap enough for every site, and blind to
--     neither evaluator nor elaboration.  Each is kept as the site's own
--     share and including the sites nested in it.  Allocation is not residency -- a
--     heap overflow is about what stays live -- but a definition that
--     allocates gigabytes is where to look first.  The size of normal forms
--     is not measured: the fast evaluator never builds the terms, and
--     measuring a term forces it, which changes the memory behaviour being
--     measured.
--
--   [They say what was being checked when a run stopped.]  The definitions
--     being checked are kept in a global ('inProgress') that an exception
--     leaves as it was, so the report of a run that died names them.
--
--   [They are process-global.]  As with the benchmarking counters, one
--     process accumulates across everything it checks.  Which project
--     modules were checked rather than loaded from an interface is recorded
--     ('noteChecked'): two reports are comparable only when they checked the
--     same modules.
--
--   [They are not synchronised.]  Concurrent ticks could in principle lose an
--     increment.  Agda's reduction is single-threaded, and a counter is a
--     diagnostic rather than a proof, so this is not defended against.
module Agda.TypeChecking.ProfileCounters
  ( -- * The store
    Counters (..)
  , FrameStats (..)
  , BlockInfo (..)
  , getCounters
  , countersRequested
    -- * Ticking
  , Cause
  , tickUnfold
  , countUnfold
  , tickConversion
    -- * Which modules were checked
  , noteChecked
  , getChecked
  , noteUncounted
  , getUncounted
    -- * Sites being checked, and what they cost
  , checkingSite
  , subSite
  , noteBlock
  , noteDetail
  , getInProgress
  , allocationCounter
  ) where

import Control.Monad (unless, when)
import Control.Monad.IO.Class (MonadIO (..))

import Data.Int (Int64)
import Data.IORef
import Data.Maybe (isJust, listToMaybe)
import qualified Data.HashMap.Strict as HMap
import qualified Data.Map.Strict as MapS
import qualified Data.Set as Set

import GHC.Conc (getAllocationCounter)

import System.CPUTime (getCPUTime)
import System.IO.Unsafe (unsafePerformIO)

import Agda.Syntax.Abstract.Name (QName)
import Agda.Syntax.Position (Range)

import Agda.Interaction.Options.HasOptions (HasOptions (..))
import Agda.Interaction.Options.Types (optCountersFile, optCountersFolded)
import Agda.TypeChecking.Monad.Base
  ( CheckingFrame (..), MonadTCEnv (..), ProfileSite (..), TCEnv (..), asksTC )
import Agda.TypeChecking.Monad.Debug (MonadDebug, hasProfileOption)

import qualified Agda.Utils.ProfileOptions as Profile

---------------------------------------------------------------------------
-- * The store
---------------------------------------------------------------------------

-- | One map per counter.
--
--   A counter is added here when something ticks it, not before: a slot
--   nothing fills would be reported as "measured, nothing found".
data Counters = Counters
  { cUnfold   :: !(HMap.HashMap QName Int)
      -- ^ Times a definition's body was unfolded during reduction.
  , cConv     :: !(HMap.HashMap QName Int)
      -- ^ Times a definition's head took part in a conversion check.
  , cCaused   :: !(HMap.HashMap Cause (HMap.HashMap QName Int))
      -- ^ The unfoldings again, by the site being checked when they
      --   happened: cause, then what was unfolded.
  , cFrames   :: !(HMap.HashMap ProfileSite FrameStats)
      -- ^ Every site whose checking finished, with what it cost.
  , cBlocks   :: !(HMap.HashMap QName BlockInfo)
      -- ^ The declaration or mutual block each name of a 'SiteCheck' stands
      --   for, recorded when it was entered.
  , cDetails  :: !(HMap.HashMap ProfileSite (MapS.Map String Integer))
      -- ^ Sizes a check reports about its own work, such as the positivity
      --   checker's graph, summed over every time the site was entered.
  }

-- | What checking one site cost.
data FrameStats = FrameStats
  { fsPath     :: [ProfileSite]
      -- ^ The sites enclosing it, outermost first, ending with its own.
  , fsOwnBytes :: !Int
  , fsAllBytes :: !Int
      -- ^ Including the sites nested in it.
  , fsOwnTime  :: !Integer
      -- ^ CPU time, in picoseconds.
  , fsAllTime  :: !Integer
  , fsEntries  :: !Int
      -- ^ How many times it was checked.  One for a definition; a sub-site,
      --   such as the reduction of one call's arguments by the termination
      --   checker, is entered once per call.
  }

-- | What a declaration or mutual block is, recorded when its checking
--   begins.  A report is written after the module is done, from names that
--   may by then have been read back from an interface, which keeps the
--   binding site of each name but not the range of the declaration.
data BlockInfo = BlockInfo
  { biRange     :: !Range
      -- ^ The whole declaration or block, first line to last.
  , biMembers   :: [QName]
      -- ^ Its names as written by the user, in source order.
  , biGenerated :: !Int
      -- ^ Its names made up by Agda: @with@-functions, extended lambdas.
  , biClauses   :: !Int
      -- ^ Clauses of all its functions, generated ones included.
  , biHasData   :: !Bool
      -- ^ Whether it declares a data or record type.
  }

-- | The site being checked when a tick fired, if any.
type Cause = Maybe ProfileSite

emptyCounters :: Counters
emptyCounters = Counters HMap.empty HMap.empty HMap.empty HMap.empty HMap.empty HMap.empty

-- | The counters.  Global because the hot hooks run in 'ReduceM', which is
--   pure; see the module header.
counters :: IORef Counters
counters = unsafePerformIO $ newIORef emptyCounters
{-# NOINLINE counters #-}

getCounters :: IO Counters
getCounters = readIORef counters

-- | Is the counters report wanted at all?  It is when @--profile=reduction@
--   or @--profile=allocation@ is on, or when @--counters-file@ or
--   @--counters-folded@ is given.
--
--   @--profile=conversion@ and @--profile=definitions@ alone do not ask for
--   it: they predate the counters, and a run using them must neither write
--   a file it did not ask for nor pay for per-site bookkeeping.
countersRequested :: (HasOptions m, MonadDebug m) => m Bool
countersRequested = do
  red   <- hasProfileOption Profile.Reduction
  alloc <- hasProfileOption Profile.Allocation
  if red || alloc then pure True else do
    opts <- commandLineOptions
    pure $ isJust (optCountersFile opts) || isJust (optCountersFolded opts)

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

incUnfold :: Cause -> QName -> Counters -> Counters
incUnfold by q c0 = c { cCaused = HMap.alter (Just . inner) by (cCaused c) }
  where
    c = addTo cUnfold (\ m c' -> c' { cUnfold = m }) q 1 c0
    inner = maybe (HMap.singleton q 1) (HMap.insertWith (+) q 1)

-- | A definition's body was unfolded.  §4.1: the direct measurement of
--   \"evaluated N times instead of once\", and the number that distinguishes
--   an expensive definition from a cheap one in a hot loop -- which demand
--   opposite fixes.  The caller checks 'envProfileCounting' and passes the
--   innermost of 'envCheckingDefinitions' as the cause.
tickUnfold :: Monad m => Cause -> QName -> m ()
tickUnfold by q = bumpM (incUnfold by q)

-- | 'tickUnfold' for the fast evaluator, whose machine runs in 'ST': the
--   tick fires when the returned value is forced, which for the next machine
--   step is when the machine takes it.
countUnfold :: Cause -> QName -> a -> a
countUnfold by q = bump (incUnfold by q)

-- | A definition's head took part in a conversion check.  §4.6: the aggregate
--   tick already exists in "Agda.TypeChecking.Conversion"; only the key was
--   missing, which is the difference between \"conversion is hot\" and
--   \"conversion is hot because of @f@\".
tickConversion :: Monad m => QName -> m ()
tickConversion q = bumpM (addTo cConv (\ m c -> c { cConv = m }) q 1)

---------------------------------------------------------------------------
-- * Which modules were checked
---------------------------------------------------------------------------

-- | The project modules type-checked in this process, as opposed to loaded
--   from an interface.  Only those contribute counts.  Kept by printed name,
--   which is how the report lists them.
checked :: IORef (Set.Set String)
checked = unsafePerformIO $ newIORef Set.empty
{-# NOINLINE checked #-}

noteChecked :: String -> IO ()
noteChecked m = modifyIORef' checked (Set.insert m)

getChecked :: IO [String]
getChecked = Set.toList <$> readIORef checked

-- | The modules type-checked in this process that were not counted, each
--   with the reason, so that a report's list of counted modules can be
--   squared with the modules the log says were checked.
uncounted :: IORef (MapS.Map String String)
uncounted = unsafePerformIO $ newIORef MapS.empty
{-# NOINLINE uncounted #-}

noteUncounted :: String -> String -> IO ()
noteUncounted m why = modifyIORef' uncounted (MapS.insert m why)

getUncounted :: IO [(String, String)]
getUncounted = MapS.toList <$> readIORef uncounted

---------------------------------------------------------------------------
-- * Sites being checked, and what they cost
---------------------------------------------------------------------------

-- | The sites being checked, innermost first, as of the last one entered or
--   left.  Set on entry and reset on a normal exit only, so an exception
--   leaves it naming the sites it escaped from.
inProgress :: IORef [CheckingFrame]
inProgress = unsafePerformIO $ newIORef []
{-# NOINLINE inProgress #-}

getInProgress :: IO [CheckingFrame]
getInProgress = readIORef inProgress

-- | The thread's allocation counter, which decreases as it allocates.  It is
--   per thread: only the thread doing the checking can read a meaningful
--   one.
allocationCounter :: IO Int64
allocationCounter = getAllocationCounter

-- | Check a site, recording it as the one being checked.
--
--   What it cost is recorded when it is checked normally, the counters are
--   counting, and the report was asked for.  What an inner site costs is
--   added to its parent's nested total, so a site's own share is its whole
--   less that.  Called where "Agda.TypeChecking.Rules.Decl" bills a
--   definition for @--profile=definitions@, and around module applications,
--   the work after each declaration and the checks after a mutual block.
checkingSite
  :: (MonadTCEnv m, MonadIO m, HasOptions m, MonadDebug m)
  => ProfileSite -> m a -> m a
checkingSite site m = do
  parent <- asksTC envCheckingDefinitions
  let path = maybe [] cfPath (headMay parent) ++ [site]
  frame  <- liftIO $ CheckingFrame site path
              <$> getAllocationCounter <*> getCPUTime <*> newIORef (0, 0)
  let here = frame : parent
  liftIO $ writeIORef inProgress here
  r <- localTC (\ e -> e { envCheckingDefinitions = here }) m
  counting <- asksTC envProfileCounting
  record   <- if counting then countersRequested else pure False
  liftIO $ do
    endAlloc <- getAllocationCounter
    endTime  <- getCPUTime
    (nestedAlloc, nestedTime) <- readIORef (cfNested frame)
    let allAlloc = cfAllocStart frame - endAlloc
        allTime  = endTime - cfTimeStart frame
    case parent of
      p : _ -> modifyIORef' (cfNested p) $ \ (a, t) ->
                 let a' = a + allAlloc; t' = t + allTime in a' `seq` t' `seq` (a', t')
      []    -> pure ()
    when record $ modifyIORef' counters $ \ c -> c
      { cFrames = HMap.insertWith add site
          FrameStats { fsPath     = path
                     , fsOwnBytes = fromIntegral (allAlloc - nestedAlloc)
                     , fsAllBytes = fromIntegral allAlloc
                     , fsOwnTime  = allTime - nestedTime
                     , fsAllTime  = allTime
                     , fsEntries  = 1
                     }
          (cFrames c) }
    writeIORef inProgress parent
  pure r
  where
    headMay (x : _) = Just x
    headMay []      = Nothing
    -- A site checked twice (rare) is reported once, with both costs.
    add new old = old
      { fsOwnBytes = fsOwnBytes new + fsOwnBytes old
      , fsAllBytes = fsAllBytes new + fsAllBytes old
      , fsOwnTime  = fsOwnTime new + fsOwnTime old
      , fsAllTime  = fsAllTime new + fsAllTime old
      , fsEntries  = fsEntries new + fsEntries old
      }

-- | Are the counters of the current module being recorded?  Everything
--   that only feeds the report is gated on this, so a run without the
--   report pays for no more than reading the environment.
recording :: (MonadTCEnv m, HasOptions m, MonadDebug m) => m Bool
recording = do
  counting <- asksTC envProfileCounting
  if counting then countersRequested else pure False

-- | The site being checked, if any.
innermost :: MonadTCEnv m => m (Maybe ProfileSite)
innermost = asksTC (fmap cfSite . listToMaybe . envCheckingDefinitions)

-- | Check part of the enclosing site's work as a site of its own, named
--   @[what] M.f@ after the enclosing site's name.  For the phases of a check
--   whose cost needs splitting, such as the termination checker's reduction
--   of call arguments; entered once per call, and reported once, with the
--   number of entries.  Only while recording: unlike 'checkingSite', which
--   is entered once per declaration, this may be entered once per call.
subSite
  :: (MonadTCEnv m, MonadIO m, HasOptions m, MonadDebug m)
  => String -> m a -> m a
subSite what m = recording >>= \case
  False -> m
  True  -> innermost >>= \case
    Just (SiteDefinition q) -> checkingSite (SiteCheck what q) m
    Just (SiteCheck _ q)    -> checkingSite (SiteCheck what q) m
    _                       -> m

-- | Record what a declaration or block is, under the name its sites are
--   named by.  The work after a declaration and the checks after a mutual
--   block describe the same block; the first is recorded once
--   (@replace = False@), and the second, which knows the block's generated
--   names too, replaces it.
noteBlock
  :: (MonadTCEnv m, MonadIO m, HasOptions m, MonadDebug m)
  => Bool -> QName -> m BlockInfo -> m ()
noteBlock replace q info = whenM recording $ do
  known <- liftIO $ HMap.member q . cBlocks <$> readIORef counters
  unless (known && not replace) $ do
    b <- info
    let b' = b { biMembers = forceList (biMembers b) }
    liftIO $ modifyIORef' counters $ \ c -> c { cBlocks = HMap.insert q b' (cBlocks c) }
  where
    forceList xs = length xs `seq` xs
    whenM c k = c >>= \ b -> when b k

-- | Add to a size the site being checked reports about its own work.
noteDetail
  :: (MonadTCEnv m, MonadIO m, HasOptions m, MonadDebug m)
  => String -> Integer -> m ()
noteDetail key n = recording >>= \ r -> when r $ innermost >>= \case
  Nothing -> pure ()
  Just s  -> liftIO $ modifyIORef' counters $ \ c -> c
    { cDetails = HMap.insertWith (MapS.unionWith (+)) s (MapS.singleton key n) (cDetails c) }
