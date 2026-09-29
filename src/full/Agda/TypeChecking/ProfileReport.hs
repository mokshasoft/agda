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

-- | One listed definition.
data Row = Row
  { rName   :: String
  , rCount  :: Int
  , rSource :: Maybe FilePath
      -- ^ Relative to the project, when inside it.
  , rRange  :: String
      -- ^ Empty when the name carries no range that can be trusted.
  }

-- | Most counted first.  Ties break on name, then on source and range, so
--   that two runs order the same rows the same way: never on anything
--   allocation-ordered, since that shifts under unrelated edits.
--
--   The range is the definition's, read off the signature.  The key a count
--   is stored under is whichever occurrence of the name was ticked first,
--   and a name's range is that of the occurrence -- a use site, not where
--   the definition is.
rows :: FilePath -> ModuleFileTable -> HMap.HashMap QName Int -> TCM [Row]
rows projectDir tbl m = do
  defined <- forM (HMap.toList m) $ \ (q, c) ->
    (, c) . either (const q) defName <$> getConstInfo' q
  pure $ sortOn (\ r -> (Down (rCount r), rName r, rSource r, rRange r))
    [ Row { rName   = prettyShow q
          , rCount  = c
          , rSource = relativeTo projectDir <$> src
          , rRange  = trustedRange projectDir src q
          }
    | (q, c) <- defined
    , let src = MapS.findWithDefault Nothing (qnameModule q) sources
    ]
  where
    -- Looked up once per module rather than once per name: a module
    -- lookup scans the whole file table.
    sources = MapS.fromList
      [ (x, sourceOfModule tbl x) | x <- map qnameModule (HMap.keys m) ]

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
    let outFile  = fromMaybe "agda-counters.json" (optCountersFile opts)
    listed     <- forM enabled $ \ k -> (k,) <$> rows projectDir tbl (kGet k cs)
    let notes    = concat
          [ [ "Counts of forced evaluations, per definition, most counted first."
            , "Only the modules listed as checked were type-checked in this run;"
              ++ " the rest were loaded from interfaces and contributed nothing"
              ++ " of their own checking.  Compare two reports only when they"
              ++ " checked the same modules." ]
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
          , withComma $ jField 1 "checkedModules" (JArr (map JStr checked))
          ]
        put $ indent 1 ++ jsonString "counters" ++ ": {"
        let kind (i, (k, rs)) = do
              put $ (if i == (0 :: Int) then "\n" else ",\n")
                ++ indent 2 ++ jsonString (kKey k) ++ ": ["
              n <- streamArray put 3 (pure . rowJ) rs
              put $ (if n == 0 then "" else "\n" ++ indent 2) ++ "]"
        mapM_ kind (zip [0 ..] listed)
        put $ "\n" ++ indent 1 ++ "}\n}\n"
      ReportText -> do
        put $ unlines notes
        put $ unlines $
          "" : ("checked modules (" ++ show (length checked) ++ ")")
             : map ("  " ++) checked
        forM_ listed $ \ (k, rs) -> put $ unlines $
          "" : (kTitle k ++ " (" ++ show (length rs) ++ ")")
             : [ "  " ++ padLeft 10 (show (rCount r)) ++ "  " ++ rName r
                 ++ (if null (rRange r) then "" else "  " ++ rRange r)
               | r <- rs ]
    -- A file nobody knows was written is a file nobody opens.
    unless (outFile == "-") $ alwaysReportSLn "" 1 $
      "Profile counters" ++ (case done of
        Complete       -> ""
        Incomplete why -> " (INCOMPLETE: " ++ why ++ ")")
      ++ " written to " ++ outFile
  where
    rowJ r = JObj $ concat
      [ [ ("name", JStr (rName r)), ("count", JNum (rCount r)) ]
      , [ ("source", JStr s) | Just s <- [rSource r] ]
      , [ ("range", JStr (rRange r)) | not (null (rRange r)) ]
      ]
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
