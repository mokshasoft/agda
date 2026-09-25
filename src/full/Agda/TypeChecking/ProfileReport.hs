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
import Control.Monad (filterM, unless)
import Control.Monad.IO.Class (liftIO)

import qualified Data.HashMap.Strict as HMap
import Data.IORef (readIORef, writeIORef)

import System.IO (hFlush, hPutStrLn, stderr, stdout)

import Agda.Syntax.Common.Pretty (prettyShow)
import Agda.Syntax.Internal (QName)

import Agda.Interaction.Options
  ( ReportFormat (..), optCountersFile, optCountersFormat, optFastReduce )
import Agda.TypeChecking.AnalysisOutput
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

-- | The counters that something records.
--
--   The store also has room for the largest normal form, constraint wakeups
--   and serialised size, but nothing ticks those yet.  They are left out
--   rather than written as empty lists, which would read as "measured, and
--   nothing found" -- the one misreading a report must not invite.  Each
--   goes here when its hook exists.
kinds :: [Kind]
kinds =
  [ Kind "unfoldings"       "unfoldings"        Profile.Reduction  PC.cUnfold
  , Kind "conversionChecks" "conversion checks" Profile.Conversion PC.cConv
  ]

-- | Write the counters of every kind whose profile option is on.  Nothing is
--   written when none is: a file of empty sections would read as "nothing
--   was counted" rather than "nothing was asked for".
writeProfileCounters :: Completeness -> TCM ()
writeProfileCounters done = do
  enabled <- filterM (hasProfileOption . kOption) kinds
  unless (null enabled) $ do
    opts <- commandLineOptions
    cs   <- liftIO PC.getCounters
    -- A silent shortfall would be the worst outcome here: Agda dispatches to
    -- the fast evaluator by default (Reduce.hs, `ifM shouldTryFastReduce`),
    -- which does not go through unfoldDefinitionStep and so is not counted.
    -- Saying so beats reporting numbers that look complete and are not.
    fast <- (&&) <$> hasProfileOption Profile.Reduction
                 <*> (optFastReduce <$> pragmaOptions)
    let outFile = optCountersFile opts
        rows k  = PC.topBy 0 (kGet k cs)
        notes   = concat
          [ [ "Counts of forced evaluations, per definition, most counted first." ]
          , [ "The unfolding counts exclude the fast evaluator,"
            ++ " which handles most reduction by default and does not go through"
            ++ " the counted path.  Re-run with --no-fast-reduce for complete"
            ++ " numbers; it is slower, but the counts are the point."
            | fast ]
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
          ]
        put $ indent 1 ++ jsonString "counters" ++ ": {"
        let kind (i, k) = do
              put $ (if i == (0 :: Int) then "\n" else ",\n")
                ++ indent 2 ++ jsonString (kKey k) ++ ": ["
              n <- streamArray put 3 (pure . rowJ) (rows k)
              put $ (if n == 0 then "" else "\n" ++ indent 2) ++ "]"
        mapM_ kind (zip [0 ..] enabled)
        put $ "\n" ++ indent 1 ++ "}\n}\n"
      ReportText -> do
        put $ unlines notes
        mapM_ (\ k -> put $ unlines $
                 ("" : (kTitle k ++ " (" ++ show (length (rows k)) ++ ")")
                   : [ "  " ++ padLeft 10 (show c) ++ "  " ++ prettyShow q
                     | (q, c) <- rows k ]))
              enabled
    -- A file nobody knows was written is a file nobody opens.
    unless (outFile == "-") $ alwaysReportSLn "" 1 $
      "Profile counters" ++ (case done of
        Complete       -> ""
        Incomplete why -> " (INCOMPLETE: " ++ why ++ ")")
      ++ " written to " ++ outFile
  where
    rowJ (q, c) = JObj [ ("name", JStr (prettyShow q)), ("count", JNum c) ]
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
