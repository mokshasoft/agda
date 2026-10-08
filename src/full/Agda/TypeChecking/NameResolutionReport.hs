{-# OPTIONS_GHC -Wunused-imports #-}

-- | Say where every name came from (@--name-resolution-report[=FILE]@).
--
--   For every module scope checked in the run, one record per resolved
--   occurrence of a name: what was written, what it resolved to, and the
--   chain of @open@s, @import@s and module applications that brought it into
--   scope.  The interactive "why in scope" command answers this for one name;
--   this answers it for all of them, so that a tool can rewrite imports and
--   then check, by comparing two reports, that no name changed meaning.
--
--   The report is records only.  Which import to write is the client's
--   decision.
--
--   == Only modules checked in this run
--
--   Scope checking does not run for a module loaded from its interface, so
--   such a module has no records.  To report on a module, make sure it is
--   re-checked: check a copy, or delete its interface.
--
--   == Format, schema 1
--
--   JSON lines: one JSON object per line, so that a report of tens of
--   thousands of records can be streamed.  The first line is a header,
--
--   > {"schema": 1, "report": "name-resolution"}
--
--   and every other line one record.  Fields present in every record:
--
--   [@module@] the top-level module being checked.
--   [@file@, @line@, @col@, @endLine@, @endCol@] where the occurrence is
--     written; @file@ is relative to the project when inside it.  The end
--     is exclusive.
--   [@written@] the name as written, qualifier included (@C.String@).
--   [@kind@] one of
--
--     * @defined@, @field@, @constructor@, @patsyn@: a name defined by a
--       declaration;
--     * @var@: a use of a bound variable;
--     * @binder@: a variable bound here, a pattern variable included;
--     * @module@: a module name, as in @open M@ or @module X = M@.
--
--   [@resolved@] the fully qualified name it resolved to; for @var@ and
--     @binder@ the variable's name.
--
--   Fields present for some kinds:
--
--   [@nameKind@] for a name, Agda's finer kind (@DataName@, @ConName@,
--     ...).
--   [@lineage@] for a name or module, the way it came into scope,
--     outermost first, as a list of @{"op": "opened" | "applied", "module":
--     <as written there>}@.  An empty list means it is defined in the module
--     being checked, or, for an occurrence through a qualifier, in the module
--     the qualifier denotes; a module bound by @import M as Q@ also has an
--     empty lineage.  The hops below the outermost one are read from the
--     interfaces of the imported modules, and so are all @public@: a module
--     exports only what it opened publicly.  Only a hop written in the module
--     being checked has a range; the interfaces do not keep the others'.
--   [@qualifier@] for a qualified name (@C.x@), the module(s) the qualifier
--     @C@ denotes, as @{"resolved", "lineage"}@.  The name's own lineage
--     starts inside that module.
--
--   Not reported: the names in an import directive (@using@, @hiding@,
--   @renaming@) and the module named by an @import@, which are not looked
--   up through the scope; the hop that an @open@ adds to a name's lineage
--   carries the range of the module name in that statement instead.
--   [@alternatives@] for an overloaded constructor, field or pattern
--     synonym, every candidate as @{"resolved", "nameKind", "lineage"}@;
--     @resolved@ and @lineage@ of the record are those of the first.
--   [@binding@] for @var@ and @binder@: @lambda@ (also Π and module
--     parameters), @pattern@, @let@, @with@ or @macro@.
--
--   Records of a module are in source order.  An occurrence resolved several
--   times (the operator parser resolves every identifier to classify it) is
--   reported once, as the last resolution, which is the one the translation
--   to abstract syntax made.
module Agda.TypeChecking.NameResolutionReport
  ( startNameResolutionReport
  , writeNameResolutionReport
  ) where

import Control.Monad.IO.Class (liftIO)

import qualified Data.List.NonEmpty as NE
import Data.Maybe (isJust)

import System.FilePath (takeDirectory)
import System.IO

import Agda.Syntax.Common.Pretty (prettyShow)
import qualified Agda.Syntax.Concrete.Name as C
import Agda.Syntax.Position
import Agda.Syntax.Scope.Base
import Agda.Syntax.Scope.NameResolutionLog

import Agda.Interaction.Options.Types (optNameResolutionFile)
import Agda.TypeChecking.DeadImports (deadImportsWanted, startDeadImports)
import Agda.TypeChecking.AnalysisOutput
import Agda.TypeChecking.Monad

import Agda.Utils.FileName (filePath)
import qualified Agda.Utils.Maybe.Strict as Strict

-- | At the start of a run: turn logging on or off, and start the report
--   file with its header.
startNameResolutionReport :: TCM ()
startNameResolutionReport = do
  out <- optNameResolutionFile <$> commandLineOptions
  dead <- deadImportsWanted
  liftIO $ setLogEnabled (isJust out || dead)
  startDeadImports
  case out of
    Nothing -> pure ()
    Just fp -> liftIO $ withSink WriteMode fp $ \ h ->
      hPutStrLn h $ encodeJ $ JObj
        [ ("schema", JNum 1), ("report", JStr "name-resolution") ]

-- | After scope checking a module: append its records to the report, and
--   return them for @--dead-imports@ (which reads the same occurrences, once
--   the module is type checked).
writeNameResolutionReport :: TopLevelModuleName -> FilePath -> TCM [Occurrence]
writeNameResolutionReport m src = do
  out <- optNameResolutionFile <$> commandLineOptions
  occs <- liftIO $ takeOccurrences src
  case out of
    Nothing -> pure ()
    Just fp -> do
      projectDir <- runProjectDir (takeDirectory src)
      liftIO $ withSink AppendMode fp $ \ h ->
        mapM_ (hPutStrLn h . encodeJ . record projectDir (prettyShow m)) occs
  return occs

-- | A report spans several modules, so the file is appended to, not
--   replaced: not 'withOutputSink'.
withSink :: IOMode -> FilePath -> (Handle -> IO ()) -> IO ()
withSink _    "-" k = k stdout >> hFlush stdout
withSink mode fp  k = withFile fp mode $ \ h -> do
  -- Names are full of Unicode, and the locale encoding is not to be trusted.
  hSetEncoding h utf8
  k h

record :: FilePath -> String -> Occurrence -> J
record projectDir m (Occurrence x what) = JObj $
  [ ("module", JStr m) ] ++ rangeFields projectDir (getRange x) ++
  [ ("written", JStr (prettyShow x)) ] ++
  case what of
    Resolved r quals -> resolved r ++
      [ ("qualifier", JArr
          [ JObj [ ("resolved", JStr (prettyShow (amodName q)))
                 , ("lineage", lineage (amodLineage q)) ]
          | q <- quals ])
      | not (null quals) ]
    ModuleName am ->
      [ ("kind", JStr "module")
      , ("resolved", JStr (prettyShow (amodName am)))
      , ("lineage", lineage (amodLineage am)) ]
    Binder b y ->
      [ ("kind", JStr "binder")
      , ("resolved", JStr (prettyShow y))
      , ("binding", JStr (bindingSource b)) ]
  where
    resolved = \case
      VarName y b ->
        [ ("kind", JStr "var")
        , ("resolved", JStr (prettyShow y))
        , ("binding", JStr (bindingSource b)) ]
      DefinedName _ a _      -> names "defined" (a NE.:| [])
      FieldName as           -> names "field" as
      ConstructorName _ as   -> names "constructor" as
      PatternSynResName as   -> names "patsyn" as
      UnknownName            -> []   -- not logged
    names k as@(a NE.:| rest) =
      [ ("kind", JStr k) ] ++ name a ++
      [ ("alternatives", JArr [ JObj (name b) | b <- NE.toList as ])
      | not (null rest) ]
    name a =
      [ ("resolved", JStr (prettyShow (anameName a)))
      , ("nameKind", JStr (show (anameKind a)))
      , ("lineage", lineage (anameLineage a)) ]

    lineage :: WhyInScope -> J
    lineage = JArr . go
      where
        go = \case
          Defined     -> []
          Opened q w  -> hop "opened" q : go w
          Applied q w -> hop "applied" q : go w
        hop :: String -> C.QName -> J
        hop op q = JObj $
          [ ("op", JStr op), ("module", JStr (prettyShow q)) ] ++
          rangeFields projectDir (getRange q)

bindingSource :: BindingSource -> String
bindingSource = \case
  LambdaBound    -> "lambda"
  PatternBound{} -> "pattern"
  LetBound       -> "let"
  WithBound      -> "with"
  MacroBound     -> "macro"

-- | @file@, @line@, @col@, @endLine@, @endCol@, when the range has them.
rangeFields :: FilePath -> Range -> [(String, J)]
rangeFields projectDir r = case (rStart' r, rEnd' r) of
  (Just s, Just e) ->
    [ ("file", JStr (relativeTo projectDir (filePath (rangeFilePath f))))
    | Strict.Just f <- [rangeFile r] ] ++
    [ ("line", num (posLine s)), ("col", num (posCol s))
    , ("endLine", num (posLine e)), ("endCol", num (posCol e)) ]
  _ -> []
  where num = JNum . fromIntegral
