{-# OPTIONS_GHC -Wunused-imports #-}

-- | Report the sections of a development that abstract over a wide ambient
--   context (@--wide-sections=N@), ranked by what they cost.
--
--   A section is a module, so this covers both shapes that silently widen a
--   definition's context: a @where@ block, whose contents are lifted out over
--   the enclosing pattern variables, and a module application, which copies
--   every member of the applied module into that same context.  Neither says
--   so in the source: @module OB = ASP.Obligations ...@ is one line, and it
--   can create sixty definitions each sixty binders deep.
--
--   == Why this reads the signature, not the checker
--
--   Both numbers survive checking.  A section's telescope is kept in the
--   signature -- it is what a later module application of it needs -- and a
--   copy made by a module application is marked 'defCopy'.  So this is a
--   query over the signature, like @--duplicate-types@, and not a hook in the
--   checker.  Reporting from the checker instead, as a warning per section,
--   had three defects this avoids:
--
--     * a module application was reported twice, once as a section and once
--       as an application, because the two facts become known at different
--       points;
--     * a warning is serialised into the interface of the module it fired in,
--       so a run with a low threshold baked warnings into shared, cached
--       interfaces, where they replayed on later runs that never asked;
--     * a warning is one line among thousands -- at a threshold of 1 the
--       standard library alone produces several thousand -- and warnings are
--       listed in source order, which is the wrong order for this question.
--
--   Imported modules are reported on from their interfaces, without
--   re-checking them.  Their names lose their ranges in serialisation, though,
--   so only the sections of the module being checked carry a location; the
--   others are identified by name alone.
--
--   == When checking does not finish
--
--   The module this is most needed for is one that cannot be checked at all:
--   it runs out of heap, or is killed after an hour.  A report written only
--   on success says nothing about it.  So 'withWideSectionsOnAbort' also
--   writes the report when checking a module stops -- a type error, a heap
--   overflow, an interrupt -- from the state at the moment it stopped, and
--   marks it incomplete.
--
--   What makes that useful rather than merely partial is the order of
--   checking.  A module application is checked where it is written, before
--   the definitions that use it, so the copies and their width are in the
--   signature well before the expensive part begins.  In the motivating case
--   the application sat at the top of a @where@ block whose body was what ran
--   out of memory.
--
--   == The ranking
--
--   Width alone does not say what a section costs: a wide section holding one
--   definition is cheap, a narrow one holding sixty may not be.  Every
--   definition in a section carries the section's whole telescope, so the
--   cost is ranked as width times the number of definitions.  That is a count
--   of binders written by the elaborator that no one wrote in the source, not
--   a measurement of time; it says where to look, not how long it will take.
module Agda.TypeChecking.WideSections
  ( reportWideSections
  , withWideSectionsOnAbort
  ) where

import Prelude hiding (null)

import qualified Control.Exception as E
import Control.Monad (unless, when)
import Control.Monad.IO.Class (liftIO)

import Data.IORef
import Data.List (sortOn)
import Data.Maybe (listToMaybe, mapMaybe)
import qualified Data.HashMap.Strict as HMap
import qualified Data.Map.Strict as MapS
import Data.Ord (Down (..))

import System.IO (hFlush, hPutStrLn, stderr, stdout)
import System.IO.Unsafe (unsafePerformIO)

import Agda.Syntax.Common.Pretty (prettyShow)
import Agda.Syntax.Internal
import Agda.Syntax.Position (getRange, rStart')

import Agda.Interaction.Options.Types
  ( ReportFormat (..), optWideFile, optWideFormat, optWideSections )
import Agda.TypeChecking.AnalysisOutput
import Agda.TypeChecking.DeadCode
  ( moduleFileTable, sourceOfModule, pathInProject, allDefinitions )
import Agda.TypeChecking.Monad

import Agda.Utils.Lens
import Agda.Utils.Null
import Agda.Utils.Size (size)

---------------------------------------------------------------------------
-- * Collecting
---------------------------------------------------------------------------

-- | One reported section.
data Wide = Wide
  { wModule :: ModuleName
  , wSource :: Maybe FilePath
  , wWidth  :: Int
      -- ^ Context variables abstracted over.
  , wDefs   :: Int
      -- ^ Definitions directly in this section.
  , wCopies :: Int
      -- ^ How many of those a module application copied in.
  , wFrom   :: Maybe ModuleName
      -- ^ For a module application, the module applied, when it can be read
      --   off a copy.  See 'copiedFrom'.
  , wFirst  :: Maybe QName
      -- ^ The definition in it that comes first in the source.  See 'location'.
  }

cost :: Wide -> Int
cost w = wWidth w * wDefs w

-- | Every section in the project abstracting over at least @n@ context
--   variables, costliest first.
--
--   A section of width zero is never reported, whatever the threshold: it
--   abstracts over nothing.  Nor is one holding no definitions, since it
--   lifts nothing over its context; that is most parameterised modules whose
--   members all live in submodules, and every @where@ block that only opens
--   something.
collect :: FilePath -> Int -> TCM [Wide]
collect projectDir n = do
  sig      <- getSignature
  imp      <- useTC stImports
  defs     <- allDefinitions
  modTable <- moduleFileTable

  let sections = MapS.union (sig ^. sigSections) (imp ^. sigSections)

      -- Definitions grouped by the module they are directly in.
      byModule :: MapS.Map ModuleName [Definition]
      byModule = MapS.fromListWith (++)
        [ (qnameModule x, [d]) | (x, d) <- HMap.toList defs ]

      wides =
        [ Wide
          { wModule = m
          , wSource = src
          , wWidth  = w
          , wDefs   = length ds
          , wCopies = length copies
          , wFrom   = listToMaybe (mapMaybe copiedFrom copies)
          , wFirst  = listToMaybe $ sortOn (rStart' . getRange) $
                        filter (not . null . getRange) $ map defName ds
          }
        | (m, sec) <- MapS.toList sections
        , let w = size (sec ^. secTelescope)
        , w > 0, w >= n
        , let src = sourceOfModule modTable m
        , maybe False (pathInProject projectDir) src
        , let ds = MapS.findWithDefault [] m byModule
        , not (null ds)
        , let copies = filter defCopy ds
        ]

  -- Ties broken by name, so that a report is stable across runs and can be
  -- compared as a diff.
  pure $ sortOn (\ w -> (Down (cost w), prettyShow (wModule w))) wides

-- | The definition a copy was made from, read off the copy's body: a copied
--   function has one clause whose body applies the original.  Other kinds of
--   copy -- a datatype, a constructor -- do not carry it that directly, and
--   are not needed: one function in an application is enough to name the
--   module applied.
copiedFrom :: Definition -> Maybe ModuleName
copiedFrom d = case theDef d of
  Function{ funClauses = [cl] }
    | Just (Def x _) <- clauseBody cl -> Just (qnameModule x)
  _ -> Nothing

-- | Where a section is, relative to the project.
--
--   A @where@ block becomes a module named @_@, and that name has no range:
--   nested blocks of one clause are then told apart only by where their
--   first definition is, which is what is reported for them instead.
location :: FilePath -> Wide -> (String, Bool)
location projectDir w = case trustedRange projectDir (wSource w) (wModule w) of
  "" -> case trustedRange projectDir (wSource w) <$> wFirst w of
          Just r@(_ : _) -> (r, True)
          _              -> ("", False)
  r  -> (r, False)

---------------------------------------------------------------------------
-- * Reporting
---------------------------------------------------------------------------

-- | Write the report for threshold @n@ to @outFile@ (@-@ for stdout).
reportWideSections
  :: FilePath -> Int -> FilePath -> ReportFormat -> Completeness -> TCM ()
reportWideSections projectDir n outFile format done = do
  ranked <- collect projectDir n
  withOutputSink outFile $ \ put -> case format of
    ReportJSON -> renderJSON put projectDir n done ranked
    ReportText -> renderText put projectDir n done ranked
  -- A file nobody knows was written is a file nobody opens.
  unless (outFile == "-") $ alwaysReportSLn "" 1 $
    "Wide sections: " ++ show (length ranked) ++ " listed"
    ++ incompleteNote done ++ ", written to " ++ outFile
  where
    incompleteNote = \case
      Complete       -> ""
      Incomplete why -> " (INCOMPLETE: " ++ why ++ ")"

-- | The caveats, which are part of the output rather than documentation of
--   it: a reader of the report needs them and has not read this module.
caveat :: Completeness -> [String]
caveat done = concat
  [ [ "cost = width x definitions: binders the elaborator wrote that the"
    , "source does not show.  A count, not a time."
    ]
  , case done of
      Complete -> []
      Incomplete why ->
        [ "INCOMPLETE: checking stopped (" ++ why ++ ").  Every number listed"
        , "is exact, but whatever had not been checked yet is missing, including"
        , "the rest of the module that stopped."
        ]
  ]

renderText
  :: Sink -> FilePath -> Int -> Completeness -> [Wide] -> TCM ()
renderText put projectDir n done ranked = do
  put $ unlines $
    ("Wide sections (width >= " ++ show (max 1 n) ++ "): "
       ++ show (length ranked)) :
    map ("  " ++) (caveat done)
  unless (null ranked) $
    put $ unlines $
      (pad 8 "cost" ++ pad 7 "width" ++ pad 6 "defs" ++ pad 8 "copies"
        ++ "section") :
      [ pad 8 (show (cost w)) ++ pad 7 (show (wWidth w))
          ++ pad 6 (show (wDefs w)) ++ pad 8 copies
          ++ prettyShow (wModule w) ++ from ++ at
      | w <- ranked
      , let copies | wCopies w == 0 = "-"
                   | otherwise      = show (wCopies w)
            from = maybe "" (\ o -> " = " ++ prettyShow o) (wFrom w)
            at   = case location projectDir w of
                     ("", _)    -> ""
                     (r, False) -> "  " ++ r
                     (r, True)  -> "  " ++ r ++ " (first definition)"
      ]

renderJSON
  :: Sink -> FilePath -> Int -> Completeness -> [Wide] -> TCM ()
renderJSON put projectDir n done ranked = do
  put $ unlines $ ("{" :) $ concat
    [ withComma $ jField 1 "threshold" (JNum (max 1 n))
    , withComma $ jField 1 "complete" $ JBool $ case done of
        Complete     -> True
        Incomplete{} -> False
    , case done of
        Complete       -> []
        Incomplete why -> withComma $ jField 1 "stoppedBy" (JStr why)
    , withComma $ jField 1 "count" (JNum (length ranked))
    , withComma $ jField 1 "note" (JStr (oneLine (unlines (caveat done))))
    ]
  put $ indent 1 ++ jsonString "sections" ++ ": ["
  k <- streamArray put 2 (pure . wideJ) ranked
  put $ (if k == 0 then "" else "\n" ++ indent 1) ++ "]\n}\n"
  where
    wideJ w = JObj $ concat
      [ [ ("section",     JStr (prettyShow (wModule w)))
        , ("cost",        JNum (cost w))
        , ("width",       JNum (wWidth w))
        , ("definitions", JNum (wDefs w))
        , ("copies",      JNum (wCopies w))
        ]
      , [ ("copiedFrom", JStr (prettyShow o)) | Just o <- [wFrom w] ]
      , [ ("source", JStr (relativeTo projectDir s)) | Just s <- [wSource w] ]
      , case location projectDir w of
          ("", _)    -> []
          (r, byDef) -> [ ("range", JStr r)
                        , ("rangeIsFirstDefinition", JBool byDef) ]
      ]

---------------------------------------------------------------------------
-- * When checking stops
---------------------------------------------------------------------------

-- | Has the report for the current run already been written from an abort?
--
--   A stop inside an imported module passes through the handler of every
--   module importing it on the way out, and the innermost one has the most to
--   say: an imported module is checked in a fresh state ('freshTCM'), so only
--   its own handler sees its partial signature.  The first handler to run
--   writes the report and the rest leave it alone.
{-# NOINLINE abortReported #-}
abortReported :: IORef Bool
abortReported = unsafePerformIO $ newIORef False

-- | Run the check of one module; if it stops, write the wide-sections report
--   from the state it stopped in, then let it stop.
--
--   @isMain@ starts a new run, which re-arms the handler: in an interactive
--   session each reload of the main module is a new run.
--
--   Nothing here may mask the original failure.  If writing the report fails
--   too -- plausible after a heap overflow -- that is said and swallowed, and
--   the original exception is rethrown either way.
withWideSectionsOnAbort :: Bool -> TCM FilePath -> TCM a -> TCM a
withWideSectionsOnAbort isMain getProjectDir m = do
  opts <- commandLineOptions
  case optWideSections opts of
    Nothing -> m
    Just n  -> do
      when isMain $ liftIO $ writeIORef abortReported False
      let emit why = do
            projectDir <- getProjectDir
            reportWideSections projectDir n
              (optWideFile opts) (optWideFormat opts) (Incomplete why)
      TCM $ \ r e ->
        (unTCM m r e
          `E.catch` \ (err :: TCErr) -> do
            -- The partial signature is in the state the error was raised
            -- in, not in the live one; see 'stateOfErr'.
            once $ atState r (stateOfErr err) $ unTCM (emit (describeStop err)) r e
            E.throwIO err)
          `E.catch` \ (ex :: E.AsyncException) -> do
            -- A heap overflow or an interrupt is not a 'TCErr', so nothing
            -- has rolled the live state back: it is exactly where checking
            -- stopped.
            once $ unTCM (emit (show ex)) r e
            E.throwIO ex
  where
    -- Flushed by hand: an interrupted process dies by re-raising the signal,
    -- which does not flush stdout, and stdout redirected to a file is block
    -- buffered -- so without this the line saying where the report went is
    -- lost exactly when it is needed.
    once k = do
      already <- atomicModifyIORef' abortReported (True,)
      unless already $ k `E.catch` \ (ex :: E.SomeException) ->
        hPutStrLn stderr $ "Could not write the incomplete wide-sections report: "
          ++ E.displayException ex
      hFlush stdout

    atState _ Nothing  k = k
    atState r (Just s) k = do
      saved <- readIORef r
      writeIORef r s
      k `E.finally` writeIORef r saved
