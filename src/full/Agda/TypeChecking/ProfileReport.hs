{-# OPTIONS_GHC -Wunused-imports #-}

-- | Write out the counters of "Agda.TypeChecking.ProfileCounters"
--   (@--counters-file@, @--counters-format@, @--counters-folded@,
--   @--counters-snapshot@).
--
--   They are written to a file, JSON by default, like the reports of
--   @--write-ast@ and @--duplicate-types@, and for the same reason: they are
--   data to be sorted, diffed between two runs and fed to other tools, and a
--   development of any size produces far more of them than can be read off a
--   terminal.  Every counted definition is listed, not a top few, since which
--   of them matter is for the reader to decide.
--
--   Each row carries the definition's source and range as well as its name.
--   The name alone does not identify it: every @where@ block is a module
--   named @_@, so two definitions in different blocks can print the same.
--
--   == One table per site, and folded stacks
--
--   Everything measured about the checking of one site -- a definition, a
--   module application, the work after a declaration, a check after a mutual
--   block -- is one row of the
--   @sites@ table: CPU time with @--profile=definitions@, bytes allocated
--   with @--profile=allocation@, unfoldings caused with
--   @--profile=reduction@, each as the site's own share and including the
--   sites nested in it.  The same numbers, keyed by the path of sites
--   enclosing each one, are the folded stacks of @--counters-folded@, which
--   flame-graph tools read directly.
--
--   == When the run does not finish
--
--   The run these are most needed for is one that does not finish: it runs
--   out of heap, or is interrupted after an hour.  So 'withCountersOnAbort'
--   writes them when the run stops as well, marked incomplete, naming the
--   sites being checked.  The counters live outside the type-checking state
--   (see "Agda.TypeChecking.ProfileCounters"), so nothing about the stop --
--   a state rolled back by an error, a heap overflow -- loses them.
--
--   A run killed outright (SIGKILL, from an out-of-memory killer or a job
--   runner) cannot write anything as it dies.  For that, a thread rewrites
--   the report every @--counters-snapshot@ seconds while the run is going,
--   marked as a snapshot; the final report replaces it.
module Agda.TypeChecking.ProfileReport
  ( writeProfileCounters
  , withCountersOnAbort
  ) where

import Prelude hiding (null)

import Control.Concurrent (forkIO, killThread, threadDelay)
import qualified Control.Exception as E
import Control.Monad (filterM, forM, forM_, forever, unless, when)
import Control.Monad.IO.Class (liftIO)

import qualified Data.HashMap.Strict as HMap
import Data.IORef (newIORef, readIORef, writeIORef)
import Data.List (intercalate, sort, sortOn)
import Data.Int (Int64)
import Data.Maybe (fromMaybe, isJust)
import qualified Data.Map.Strict as MapS
import Data.Ord (Down (..))

import GHC.Clock (getMonotonicTime)

import System.CPUTime (getCPUTime)
import System.IO (hFlush, hPutStrLn, stderr, stdout)

import Agda.Syntax.Common.Pretty (prettyShow)
import Agda.Syntax.Internal (ModuleName, QName, qnameModule)

import Agda.Interaction.Options
  ( CommandLineOptions, ReportFormat (..), optCountersFile, optCountersFolded
  , optCountersFormat, optCountersSnapshot, optPragmaOptions, optProfiling )
import Agda.TypeChecking.AnalysisOutput
import Agda.TypeChecking.DeadCode (ModuleFileTable, moduleFileTable, sourceOfModule)
import Agda.TypeChecking.Monad
import qualified Agda.TypeChecking.ProfileCounters as PC

import Agda.Utils.Null
import Agda.Utils.ProfileOptions (ProfileOption, containsProfileOption)
import qualified Agda.Utils.ProfileOptions as Profile

-- | One kind of counter, and the profile option that turns it on.
data Kind = Kind
  { kKey    :: String
      -- ^ Its key in the JSON report.
  , kTitle  :: String
      -- ^ Its heading in the text report.
  , kOption :: ProfileOption
  , kGet    :: PC.Counters -> HMap.HashMap QName Int
  }

-- | The counters that something records.  Each further one goes here when
--   its hook exists, and not before: an empty list would read as "measured,
--   and nothing found" -- the one misreading a report must not invite.
kinds :: [Kind]
kinds =
  [ Kind "unfoldings"       "unfoldings"        Profile.Reduction  PC.cUnfold
  , Kind "conversionChecks" "conversion checks" Profile.Conversion PC.cConv
  ]

---------------------------------------------------------------------------
-- * Describing what is listed
---------------------------------------------------------------------------

-- | How a report names a definition or a site.
data Desc = Desc
  { dName   :: String
  , dKind   :: String
      -- ^ Empty when the definition is not in the signature.
  , dSource :: Maybe FilePath
      -- ^ Relative to the project, when inside it.
  , dRange  :: String
      -- ^ Empty when the name carries no range that can be trusted.
  }

-- | Describe every definition named.
--
--   The range is the definition's, read off the signature.  The key a count
--   is stored under is whichever occurrence of the name was ticked first,
--   and a name's range is that of the occurrence -- a use site, not where
--   the definition is.
--
--   The kind is part of the description because the counts mix kinds: a
--   datatype or a postulate is "unfolded" whenever reduction meets it, which
--   is cheap and frequent, and a reader filtering for functions needs to be
--   able to.
describeAll
  :: FilePath -> ModuleFileTable -> [QName] -> TCM (HMap.HashMap QName Desc)
describeAll projectDir tbl qs = fmap HMap.fromList $ forM qs $ \ q0 -> do
  def <- either (const Nothing) Just <$> getConstInfo' q0
  let q   = maybe q0 defName def
      src = MapS.findWithDefault Nothing (qnameModule q) sources
  pure (q0, Desc
    { dName   = prettyShow q
    , dKind   = maybe "" (defKind . theDef) def
    , dSource = relativeTo projectDir <$> src
    , dRange  = trustedRange projectDir src q
    })
  where
    -- Looked up once per module rather than once per name: a module
    -- lookup scans the whole file table.
    sources = MapS.fromList
      [ (x, sourceOfModule tbl x) | x <- map qnameModule qs ]

-- | Describe every site named.  A definition is described as above; a
--   module application by the module it defines; a check after a mutual
--   block, or the work after a declaration, by the first name declared.
describeSites
  :: FilePath -> ModuleFileTable -> HMap.HashMap QName Desc -> [ProfileSite]
  -> HMap.HashMap ProfileSite Desc
describeSites projectDir tbl defs = HMap.fromList . map (\ s -> (s, describe s))
  where
    describe = \case
      SiteDefinition q  -> def q
      SiteApplication m -> onModule m
      s@(SiteCheck c q) -> (def q) { dName = siteLabel s, dKind = c }
    def q = HMap.lookupDefault (Desc (prettyShow q) "" Nothing "") q defs
    onModule :: ModuleName -> Desc
    onModule m = Desc
      { dName   = prettyShow m
      , dKind   = "module application"
      , dSource = relativeTo projectDir <$> src
      , dRange  = trustedRange projectDir src m
      }
      where src = sourceOfModule tbl m

---------------------------------------------------------------------------
-- * Rows
---------------------------------------------------------------------------

-- | One listed definition.
data Row = Row
  { rDesc  :: Desc
  , rCount :: Int
  }

-- | Most counted first.  Ties break on name, then on source and range, so
--   that two runs order the same rows the same way: never on anything
--   allocation-ordered, since that shifts under unrelated edits.
rows :: HMap.HashMap QName Desc -> HMap.HashMap QName Int -> [Row]
rows descs m = sortOn rowKey
  [ Row (descs HMap.! q) c | (q, c) <- HMap.toList m ]

rowKey :: Row -> (Down Int, String, Maybe FilePath, String)
rowKey (Row d c) = (Down c, dName d, dSource d, dRange d)

-- | The unfoldings caused by checking one site, or by work done outside any
--   site ('Nothing').
data CauseRow = CauseRow
  { crCause :: Maybe Desc
  , crTotal :: Int
  , crTop   :: [Row]
      -- ^ What it unfolded most, at most 'topUnfolded' of them.
  }

-- | How many of a cause's unfolded definitions are listed.  All of them
--   would multiply the report by the number of causes.
topUnfolded :: Int
topUnfolded = 5

causeRows
  :: HMap.HashMap QName Desc -> HMap.HashMap ProfileSite Desc
  -> HMap.HashMap PC.Cause (HMap.HashMap QName Int)
  -> [CauseRow]
causeRows descs sites m = sortOn key
  [ CauseRow (fmap (sites HMap.!) by) (sum inner)
      (take topUnfolded (rows descs inner))
  | (by, inner) <- HMap.toList m
  ]
  where
    key r = (Down (crTotal r), fmap dName (crCause r), fmap dSource (crCause r))

-- | Everything measured about checking one site.  A measure that was not
--   asked for is 'Nothing'.
data SiteRow = SiteRow
  { srDesc     :: Desc
  , srTime     :: Maybe (Integer, Integer)
      -- ^ CPU microseconds: its own, and with the sites nested in it.
  , srBytes    :: Maybe (Int, Int)
      -- ^ Bytes allocated: its own, and with the sites nested in it.
  , srUnfolded :: Maybe Int
      -- ^ Unfoldings its checking caused.
  }

-- | Every site that was checked to the end or caused unfoldings, except
--   those for which every measure asked for is zero: each definition brings
--   several checks with it, and under @--profile=reduction@ alone most of
--   them unfold nothing, which a row of zeros would only bury.  Ranked by
--   the site's own share of the first measure asked for, in the order time,
--   bytes, unfoldings: by the whole, every site would sit below the one it
--   is nested in.
siteRows
  :: HMap.HashMap ProfileSite Desc -> PC.Counters -> Bool -> Bool -> Bool
  -> [SiteRow]
siteRows sites cs timeOn allocOn byCause = sortOn key $ filter measured
  [ SiteRow
      { srDesc     = sites HMap.! s
      , srTime     = if timeOn  then (\ f -> (micros (PC.fsOwnTime f), micros (PC.fsAllTime f))) <$> stats else Nothing
      , srBytes    = if allocOn then (\ f -> (PC.fsOwnBytes f, PC.fsAllBytes f)) <$> stats else Nothing
      , srUnfolded = if byCause then Just (maybe 0 sum (HMap.lookup (Just s) (PC.cCaused cs))) else Nothing
      }
  | s <- HMap.keys $ HMap.union (() <$ PC.cFrames cs) $
           HMap.fromList [ (s, ()) | Just s <- HMap.keys (PC.cCaused cs), byCause ]
  , let stats = HMap.lookup s (PC.cFrames cs)
  ]
  where
    measured r = maybe False ((/= 0) . snd) (srTime r)
              || maybe False ((/= 0) . snd) (srBytes r)
              || maybe False (/= 0) (srUnfolded r)
    key r = ( Down (maybe 0 fst (srTime r)), Down (maybe 0 fst (srBytes r))
            , Down (fromMaybe 0 (srUnfolded r))
            , dName (srDesc r), dSource (srDesc r), dRange (srDesc r) )

micros :: Integer -> Integer
micros ps = ps `div` 1000000

---------------------------------------------------------------------------
-- * Writing the report
---------------------------------------------------------------------------

-- | Write the counters of every kind whose profile option is on, when the
--   report was asked for at all ('PC.countersRequested').  Nothing is written
--   when nothing is measured: a file of empty sections would read as
--   "nothing was counted" rather than "nothing was asked for".
writeProfileCounters :: Completeness -> TCM ()
writeProfileCounters done = do
  requested <- PC.countersRequested
  enabled   <- filterM (hasProfileOption . kOption) kinds
  allocOn   <- hasProfileOption Profile.Allocation
  timeOn    <- hasProfileOption Profile.Definitions
  when (requested && (not (null enabled) || allocOn || timeOn)) $ do
    opts       <- commandLineOptions
    cs         <- liftIO PC.getCounters
    checked    <- liftIO PC.getChecked
    -- Read before anything else here allocates much.  Only the thread
    -- doing the checking has a meaningful allocation counter, so a
    -- snapshot, taken by another thread, reports no allocation so far.
    now        <- liftIO PC.allocationCounter
    nowTime    <- liftIO getCPUTime
    stack      <- case done of
                    Complete -> pure []
                    _        -> liftIO PC.getInProgress
    nested     <- liftIO $ mapM (readIORef . cfNested) stack
    projectDir <- runProjectDir "."
    tbl        <- moduleFileTable
    byCause    <- hasProfileOption Profile.Reduction
    let allocNow = case done of
          Incomplete _ -> allocOn
          _            -> False
        siteKeys = HMap.keys $ HMap.unions
          [ () <$ PC.cFrames cs
          , HMap.fromList [ (s, ()) | Just s <- HMap.keys (PC.cCaused cs) ]
          , HMap.fromList [ (cfSite f, ()) | f <- stack ]
          ]
        -- Everything counted, and every definition a site is about.
        names = HMap.keys $ HMap.unions $
          [ () <$ kGet k cs | k <- enabled ] ++
          [ HMap.fromList [ (q, ()) | Right q <- map siteAnchor siteKeys ] ]
    descs <- describeAll projectDir tbl names
    let sites   = describeSites projectDir tbl descs siteKeys
        outFile = fromMaybe "agda-counters.json" (optCountersFile opts)
        listed  = [ (k, rows descs (kGet k cs)) | k <- enabled ]
        causes  = [ causeRows descs sites (PC.cCaused cs) | byCause ]
        table   = siteRows sites cs timeOn allocOn byCause
        -- Innermost first, with what each had cost so far.
        stopped =
          [ ( sites HMap.! cfSite f
            , micros (nowTime - cfTimeStart f)
            , fromIntegral (cfAllocStart f - now) :: Int )
          | f <- stack ]
        notes   = concat
          [ [ "Counts of forced evaluations, per definition, most counted first."
            , "Counted only while checking the modules of the project listed as"
              ++ " counted; what their checking unfolded is counted wherever it is"
              ++ " defined, library or not.  Compare two reports only when they"
              ++ " counted the same modules." ]
          , [ "Checking is divided into sites: definitions; module applications;"
              ++ " the work after each declaration, [highlighting] and [constraints]"
              ++ " (solving its constraints, freezing its metas); and the checks"
              ++ " after a mutual block, such as [positivity] and [termination]."
              ++ "  Each is named by the first name the declaration or block"
              ++ " declares.  The sites table gives each"
              ++ " site's own share and the share including the sites nested in"
              ++ " it: CPU time in microseconds with --profile=definitions, bytes"
              ++ " allocated with --profile=allocation, and unfoldings caused with"
              ++ " --profile=reduction." ]
          , [ "The unfoldings are also listed by the site whose checking caused"
              ++ " them, each with the " ++ show topUnfolded ++ " definitions it"
              ++ " unfolded most; work outside every site has no name."
            | byCause ]
          , [ "Allocated, not live: a heap overflow is about what stays live, but"
              ++ " a site that allocates gigabytes is where to look first."
            | allocOn ]
          , case done of
              Complete -> []
              Incomplete why ->
                [ "INCOMPLETE: the run stopped (" ++ why ++ ").  Every count is"
                  ++ " what had been counted when it stopped.  The sites being"
                  ++ " checked when it stopped are listed, innermost first." ]
              Snapshot t ->
                [ "SNAPSHOT: the run was still going, " ++ show t ++ " s in.  The"
                  ++ " sites being checked are listed, innermost first, with the"
                  ++ " time they had taken; what they had allocated cannot be"
                  ++ " read from the snapshot's thread." ]
          ]
    withOutputSink outFile $ \ put -> case optCountersFormat opts of
      ReportJSON -> do
        put $ unlines $ ("{" :) $ concat
          [ withComma $ jField 1 "complete" $ JBool $ case done of
              Complete -> True
              _        -> False
          , case done of
              Incomplete why -> withComma $ jField 1 "stoppedBy" (JStr why)
              Snapshot t     -> withComma $ jField 1 "snapshotAtSeconds" (JNum (fromIntegral t))
              Complete       -> []
          , withComma $ jField 1 "note" (JStr (unwords notes))
          , withComma $ jField 1 "countedModules" (JArr (map JStr checked))
          , case done of
              Complete -> []
              _        -> withComma $ jField 1 "checkingWhenStopped" $ JArr
                [ JObj $ descJ d
                    ++ [ ("timeMicrosSoFar", JNum (fromIntegral t)) | timeOn ]
                    ++ [ ("allocatedSoFar", JNum a) | allocNow ]
                | (d, t, a) <- stopped ]
          ]
        put $ indent 1 ++ jsonString "counters" ++ ": {"
        let section :: Int -> String -> (a -> J) -> [a] -> TCM ()
            section i key render xs = do
              put $ (if i == 0 then "\n" else ",\n")
                ++ indent 2 ++ jsonString key ++ ": ["
              n <- streamArray put 3 (pure . render) xs
              put $ (if n == 0 then "" else "\n" ++ indent 2) ++ "]"
        forM_ (zip [0 ..] listed) $ \ (i, (k, rs)) -> section i (kKey k) rowJ rs
        forM_ causes $ section (length listed) "unfoldingsByCause" causeJ
        section (length listed + length causes) "sites" siteJ table
        put $ "\n" ++ indent 1 ++ "}\n}\n"
      ReportText -> do
        put $ unlines notes
        unless (null stopped) $ put $ unlines $
          "" : "being checked when it stopped (innermost first)"
             : [ "  " ++ (if timeOn then padLeft 14 (show t) ++ " us  " else "")
                      ++ (if allocNow then padLeft 16 (show a) ++ " B  " else "")
                      ++ descT d
               | (d, t, a) <- stopped ]
        put $ unlines $
          "" : ("counted modules (" ++ show (length checked) ++ ")")
             : map ("  " ++) checked
        forM_ listed $ \ (k, rs) -> put $ unlines $
          "" : (kTitle k ++ " (" ++ show (length rs) ++ ")")
             : map (rowT 2) rs
        forM_ causes $ \ crs -> put $ unlines $
          "" : ("unfoldings by the site being checked (" ++ show (length crs) ++ ")")
             : concat
               [ ("  " ++ padLeft 10 (show (crTotal cr)) ++ "  "
                   ++ maybe "(no site)" descT (crCause cr))
                 : map (rowT 14) (crTop cr)
               | cr <- crs ]
        put $ unlines $
          "" : ("sites (" ++ show (length table) ++ "): "
                  ++ intercalate ", " (concat
                       [ [ "own/total CPU us" | timeOn ]
                       , [ "own/total bytes" | allocOn ]
                       , [ "unfoldings caused" | byCause ] ]))
             : [ "  " ++ concat
                   [ maybe "" (\ (o, a) -> padLeft 12 (show o) ++ padLeft 13 (show a)) (srTime r)
                   , maybe "" (\ (o, a) -> padLeft 15 (show o) ++ padLeft 16 (show a)) (srBytes r)
                   , maybe "" (padLeft 12 . show) (srUnfolded r)
                   ]
                 ++ "  " ++ descT (srDesc r)
               | r <- table ]
    forM_ (optCountersFolded opts) $ \ prefix ->
      writeFolded prefix cs sites stack nested nowTime now
        (timeOn, allocOn, allocNow, byCause)
    -- A file nobody knows was written is a file nobody opens.  A snapshot
    -- is rewritten every minute and says so once, at the end.
    case done of
      Snapshot _ -> pure ()
      _ -> unless (outFile == "-") $ alwaysReportSLn "" 1 $
        "Profile counters" ++ (case done of
          Incomplete why -> " (INCOMPLETE: " ++ why ++ ")"
          _              -> "")
        ++ " written to " ++ outFile
  where
    descJ d = concat
      [ [ ("name", JStr (dName d)) ]
      , [ ("kind", JStr (dKind d)) | not (null (dKind d)) ]
      , [ ("source", JStr s) | Just s <- [dSource d] ]
      , [ ("range", JStr (dRange d)) | not (null (dRange d)) ]
      ]
    rowJ (Row d c) = JObj $ descJ d ++ [ ("count", JNum c) ]
    siteJ r = JObj $ descJ (srDesc r) ++ concat
      [ maybe [] (\ (o, a) -> [ ("timeMicros", JNum (fromIntegral o))
                              , ("timeMicrosWithNested", JNum (fromIntegral a)) ])
          (srTime r)
      , maybe [] (\ (o, a) -> [ ("bytes", JNum o), ("bytesWithNested", JNum a) ])
          (srBytes r)
      , [ ("unfoldingsCaused", JNum u) | Just u <- [srUnfolded r] ]
      ]
    causeJ cr = JObj $ concat
      [ maybe [ ("name", JNull) ] descJ (crCause cr)
      , [ ("count", JNum (crTotal cr))
        , ("unfoldedMost", JArr [ JObj [ ("name", JStr (dName d)), ("count", JNum c) ]
                                | Row d c <- crTop cr ])
        ]
      ]
    descT d = dName d
      ++ (if null (dKind d)  then "" else "  " ++ dKind d)
      ++ (if null (dRange d) then "" else "  " ++ dRange d)
    rowT k (Row d c) = replicate k ' ' ++ padLeft 10 (show c) ++ "  " ++ descT d
    padLeft k s = replicate (max 0 (k - length s)) ' ' ++ s

-- | The folded stacks of @--counters-folded@: one file per measure, one line
--   per site, @file;outer;...;site value@, the site's own share.  This is the
--   input format of flame-graph tools (speedscope, @flamegraph.pl@).
--
--   The sites still being checked when the run stopped are included with
--   what they had cost so far, which is what a flame graph of a run that
--   died needs most.  Lines are sorted, so two runs diff.  Each stack is
--   rooted at the site's file, or, when a snapshot cannot tell it, its
--   module.
writeFolded
  :: FilePath -> PC.Counters -> HMap.HashMap ProfileSite Desc
  -> [CheckingFrame] -> [(Int64, Integer)] -> Integer -> Int64
  -> (Bool, Bool, Bool, Bool) -> TCM ()
writeFolded prefix cs sites stack nested nowTime now (timeOn, allocOn, allocNow, byCause) = do
  let finished = [ (PC.fsPath f, PC.fsOwnTime f, PC.fsOwnBytes f) | f <- HMap.elems (PC.cFrames cs) ]
      running  = [ ( cfPath f
                   , (nowTime - cfTimeStart f) - nt
                   , fromIntegral ((cfAllocStart f - now) - na) )
                 | (f, (na, nt)) <- zip stack nested ]
      paths    = HMap.fromList $ [ (last p, p) | (p, _, _) <- finished ++ running, not (null p) ]
      -- The root is the file.  A snapshot cannot look up the file of a
      -- module being checked in its own state (an import), so there the
      -- root is the module, which groups the stacks the same way.
      stackOf p = intercalate ";" $
        fromMaybe (prettyShow (either id qnameModule (siteAnchor (head p))))
          (dSource (sites HMap.! head p))
        : map (dName . (sites HMap.!)) p
      write :: String -> [(String, Integer)] -> TCM ()
      write measure ls = withOutputSink (prefix ++ "." ++ measure ++ ".folded") $ \ put ->
        put $ unlines [ s ++ " " ++ show v | (s, v) <- sort ls, v > 0 ]
  when timeOn $ write "time" $
    [ (stackOf p, micros t) | (p, t, _) <- finished ++ running, not (null p) ]
  when allocOn $ write "allocation" $
    [ (stackOf p, fromIntegral b) | (p, _, b) <- finished, not (null p) ] ++
    [ (stackOf p, fromIntegral b) | allocNow, (p, _, b) <- running, not (null p) ]
  when byCause $ write "unfoldings" $
    [ (maybe "(no site)" stackOf (by >>= (`HMap.lookup` paths)), fromIntegral (sum inner))
    | (by, inner) <- HMap.toList (PC.cCaused cs) ]


---------------------------------------------------------------------------
-- * The whole run
---------------------------------------------------------------------------

-- | Run the whole session, writing the counters when it ends, whether it
--   finishes, fails, runs out of heap or is interrupted -- and, while it
--   runs, every @--counters-snapshot@ seconds.
--
--   Nothing here may mask the original failure: if writing the counters
--   fails too -- plausible after a heap overflow -- that is said and
--   swallowed, and the original exception is rethrown either way.
withCountersOnAbort :: CommandLineOptions -> TCM a -> TCM a
withCountersOnAbort opts m = do
  x <- TCM $ \ r e -> do
    snapshots <- startSnapshots r e
    ((unTCM m r e `E.finally` mapM_ killThread snapshots)
      `E.catch` \ (err :: TCErr) -> do
        -- Which counters were asked for is read from the options, and the
        -- live state may have been rolled back past them by the time the
        -- error gets here ('catchError' restores it); the state the error
        -- was raised in still has them.
        atState r (stateOfErr err) $ write (Incomplete (describeStop err)) r e
        E.throwIO err)
      `E.catch` \ (ex :: E.AsyncException) -> do
        write (Incomplete (show ex)) r e
        E.throwIO ex
  x <$ writeProfileCounters Complete
  where
    atState _ Nothing  k = k
    atState r (Just s) k = do
      saved <- readIORef r
      writeIORef r s
      k `E.finally` writeIORef r saved

    -- Flushed by hand: an interrupted process dies by re-raising the signal,
    -- which does not flush stdout.
    write done r e = do
      unTCM (writeProfileCounters done) r e `E.catch` \ (ex :: E.SomeException) ->
        hPutStrLn stderr $ "Could not write the incomplete profile counters: "
          ++ E.displayException ex
      hFlush stdout

    -- The snapshot thread, when the options make a report possible.  It
    -- writes from a copy of the state as it was at that moment, so it never
    -- races the checking, which goes on in the live state.  Of a module being
    -- checked in its own state (an import), it sees the counters but not the
    -- signature, so such definitions are named without kind or range.
    startSnapshots r e
      | every <= 0 || file == Just "-" || not wanted = pure Nothing
      | otherwise = do
          start <- getMonotonicTime
          Just <$> forkIO (forever $ do
            threadDelay (every * 1000000)
            t  <- getMonotonicTime
            st <- readIORef r
            r' <- newIORef st
            unTCM (writeProfileCounters (Snapshot (round (t - start)))) r' e
              `E.catch` \ (ex :: E.SomeException) -> case E.fromException ex of
                Just (async :: E.AsyncException) -> E.throwIO async
                Nothing -> hPutStrLn stderr $ "Could not write a profile counters snapshot: "
                             ++ E.displayException ex)
      where
        every  = optCountersSnapshot opts
        file   = optCountersFile opts
        prof   = optProfiling (optPragmaOptions opts)
        wanted = any (`containsProfileOption` prof) [Profile.Reduction, Profile.Allocation]
                 || isJust file || isJust (optCountersFolded opts)
