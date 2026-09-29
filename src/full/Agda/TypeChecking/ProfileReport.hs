{-# OPTIONS_GHC -Wunused-imports #-}

-- | Write out the per-definition counters of
--   "Agda.TypeChecking.ProfileCounters" (@--counters-file@,
--   @--counters-format@).
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
--   == When the run does not finish
--
--   The run these are most needed for is one that does not finish: it runs
--   out of heap, or is interrupted after an hour.  So 'withCountersOnAbort'
--   writes them when the run stops as well, marked incomplete.  The counters
--   live outside the type-checking state (see "Agda.TypeChecking.ProfileCounters"),
--   so nothing about the stop -- a state rolled back by an error, a heap
--   overflow -- loses them.
module Agda.TypeChecking.ProfileReport
  ( writeProfileCounters
  , withCountersOnAbort
  ) where

import Prelude hiding (null)

import qualified Control.Exception as E
import Control.Monad (filterM, forM, forM_, unless, when)
import Control.Monad.IO.Class (liftIO)

import qualified Data.HashMap.Strict as HMap
import Data.IORef (readIORef, writeIORef)
import Data.List (sortOn)
import Data.Maybe (fromMaybe)
import qualified Data.Map.Strict as MapS
import Data.Ord (Down (..))

import System.IO (hFlush, hPutStrLn, stderr, stdout)

import Agda.Syntax.Common.Pretty (prettyShow)
import Agda.Syntax.Internal (QName, qnameModule)

import Agda.Interaction.Options
  ( ReportFormat (..), optCountersFile, optCountersFormat )
import Agda.TypeChecking.AnalysisOutput
import Agda.TypeChecking.DeadCode (ModuleFileTable, moduleFileTable, sourceOfModule)
import Agda.TypeChecking.Monad
import qualified Agda.TypeChecking.ProfileCounters as PC

import Agda.Utils.Null
import Agda.Utils.ProfileOptions (ProfileOption)
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

-- | How a report names a definition.
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

-- | The unfoldings caused by checking one definition, or by work done
--   outside any definition ('Nothing').
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
  :: HMap.HashMap QName Desc -> HMap.HashMap PC.Cause (HMap.HashMap QName Int)
  -> [CauseRow]
causeRows descs m = sortOn key
  [ CauseRow (fmap (descs HMap.!) by) (sum inner)
      (take topUnfolded (rows descs inner))
  | (by, inner) <- HMap.toList m
  ]
  where
    key r = (Down (crTotal r), fmap dName (crCause r), fmap dSource (crCause r))

-- | Write the counters of every kind whose profile option is on, when the
--   report was asked for at all ('PC.countersRequested').  Nothing is written
--   when no kind is on: a file of empty sections would read as "nothing was
--   counted" rather than "nothing was asked for".
writeProfileCounters :: Completeness -> TCM ()
writeProfileCounters done = do
  requested <- PC.countersRequested
  enabled   <- filterM (hasProfileOption . kOption) kinds
  when (requested && not (null enabled)) $ do
    opts       <- commandLineOptions
    cs         <- liftIO PC.getCounters
    checked    <- liftIO PC.getChecked
    projectDir <- runProjectDir "."
    tbl        <- moduleFileTable
    byCause    <- hasProfileOption Profile.Reduction
    -- Everything counted, and every definition that caused unfoldings.
    let names = HMap.keys $ HMap.unions $
          [ () <$ kGet k cs | k <- enabled ] ++
          [ HMap.fromList [ (q, ()) | Just q <- HMap.keys (PC.cCaused cs) ]
          | byCause ]
    descs      <- describeAll projectDir tbl names
    let outFile = fromMaybe "agda-counters.json" (optCountersFile opts)
        listed  = [ (k, rows descs (kGet k cs)) | k <- enabled ]
        causes  = [ causeRows descs (PC.cCaused cs) | byCause ]
        notes   = concat
          [ [ "Counts of forced evaluations, per definition, most counted first."
            , "Counted only while checking the modules of the project listed as"
              ++ " counted; what their checking unfolded is counted wherever it is"
              ++ " defined, library or not.  Compare two reports only when they"
              ++ " counted the same modules." ]
          , [ "The unfoldings are also listed by the definition whose checking"
              ++ " caused them, each with the " ++ show topUnfolded ++ " definitions"
              ++ " it unfolded most; work outside any definition (a module"
              ++ " application, termination checking) has no name."
            | byCause ]
          , case done of
              Complete -> []
              Incomplete why ->
                [ "INCOMPLETE: the run stopped (" ++ why ++ ").  Every count is"
                  ++ " what had been counted when it stopped." ]
          ]
    withOutputSink outFile $ \ put -> case optCountersFormat opts of
      ReportJSON -> do
        put $ unlines $ ("{" :) $ concat
          [ withComma $ jField 1 "complete" $ JBool $ case done of
              Complete     -> True
              Incomplete{} -> False
          , case done of
              Complete       -> []
              Incomplete why -> withComma $ jField 1 "stoppedBy" (JStr why)
          , withComma $ jField 1 "note" (JStr (unwords notes))
          , withComma $ jField 1 "countedModules" (JArr (map JStr checked))
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
        put $ "\n" ++ indent 1 ++ "}\n}\n"
      ReportText -> do
        put $ unlines notes
        put $ unlines $
          "" : ("counted modules (" ++ show (length checked) ++ ")")
             : map ("  " ++) checked
        forM_ listed $ \ (k, rs) -> put $ unlines $
          "" : (kTitle k ++ " (" ++ show (length rs) ++ ")")
             : map (rowT 2) rs
        forM_ causes $ \ crs -> put $ unlines $
          "" : ("unfoldings by the definition being checked (" ++ show (length crs) ++ ")")
             : concat
               [ ("  " ++ padLeft 10 (show (crTotal cr)) ++ "  "
                   ++ maybe "(no definition)" descT (crCause cr))
                 : map (rowT 14) (crTop cr)
               | cr <- crs ]
    -- A file nobody knows was written is a file nobody opens.
    unless (outFile == "-") $ alwaysReportSLn "" 1 $
      "Profile counters" ++ (case done of
        Complete       -> ""
        Incomplete why -> " (INCOMPLETE: " ++ why ++ ")")
      ++ " written to " ++ outFile
  where
    descJ d = concat
      [ [ ("name", JStr (dName d)) ]
      , [ ("kind", JStr (dKind d)) | not (null (dKind d)) ]
      , [ ("source", JStr s) | Just s <- [dSource d] ]
      , [ ("range", JStr (dRange d)) | not (null (dRange d)) ]
      ]
    rowJ (Row d c) = JObj $ descJ d ++ [ ("count", JNum c) ]
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

-- | Run the whole session, writing the counters when it ends, whether it
--   finishes, fails, runs out of heap or is interrupted.
--
--   Nothing here may mask the original failure: if writing the counters
--   fails too -- plausible after a heap overflow -- that is said and
--   swallowed, and the original exception is rethrown either way.
withCountersOnAbort :: TCM a -> TCM a
withCountersOnAbort m = do
  x <- TCM $ \ r e ->
    (unTCM m r e
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
