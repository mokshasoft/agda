{-# OPTIONS_GHC -Wunused-imports #-}

module Agda.TypeChecking.DeadCode
  ( eliminateDeadCode
  , checkUnreachableDefinitions
  , lookupQNameByString
    -- * Attributing names to source files
  , ModuleFileTable
  , moduleFileTable
  , sourceOfQName
  , qnameInProject
  ) where

import Control.Monad (filterM, when)
import Control.Monad.Trans

import Data.List (isPrefixOf, sortOn)
import Data.List.Split (splitOn)
import Data.Maybe
import qualified Data.Map.Strict as MapS
import qualified Data.HashMap.Strict as HMap
import System.FilePath (isRelative, makeRelative, normalise)

import Agda.Syntax.Common
import qualified Agda.Syntax.Concrete.Name as C
import Agda.Syntax.Internal
import Agda.Syntax.Internal.Names
import Agda.Syntax.Position (getRange, rangeFile, rangeFilePath)
import Agda.Syntax.Scope.Base

import Agda.Utils.FileName (filePath)
import qualified Agda.Utils.Maybe.Strict as Strict

import qualified Agda.Benchmarking as Bench
import qualified Agda.TypeChecking.Monad.Benchmark as Bench

import Agda.Syntax.Common.Pretty (prettyShow)

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Warnings (warning)

import Agda.Utils.Monad (mapMaybeM)
import Agda.Utils.Impossible
import Agda.Utils.Lens
import qualified Agda.Utils.List1 as List1

import qualified Agda.Utils.HashTable as HT

---------------------------------------------------------------------------
-- * Dead code elimination for interface files
---------------------------------------------------------------------------

-- | Run before serialisation to remove data that's not reachable from the
--   public interface. We do not compute reachable data precisely, because that
--   would be very expensive, mainly because of rewrite rules. The following
--   things are assumed to be "roots":
--     - public definitions
--     - definitions marked as primitive
--     - definitions with COMPILE pragma
--     - all pattern synonyms (because currently all of them go into interfaces)
--     - all parameter sections (because currently all of them go into interfaces)
--       (see also issues #6931 and #7382)
--     - local builtins
--     - all rewrite rules
--     - closed display forms
--   We only ever prune dead metavariables and definitions. We return the pruned metas,
--   pruned definitions and closed display forms.
eliminateDeadCode :: ScopeInfo -> TCM (RemoteMetaStore, Definitions, DisplayForms)
eliminateDeadCode !scope = Bench.billTo [Bench.DeadCode] $ do
  !sig <- getSignature
  let !defs = sig ^. sigDefinitions
  !metas <- useR stSolvedMetaStore

  -- #2921: Eliminating definitions with attached COMPILE pragmas results in
  -- the pragmas not being checked. Simple solution: don't eliminate these.
  -- #6022 (Andreas, 2022-09-30): Eliminating cubical primitives can lead to crashes.
  -- Simple solution: retain all primitives (shouldn't be many).
  let hasCompilePragma = not . MapS.null . defCompiledRep

      isPrimitive = \case
        Primitive{}     -> True
        PrimitiveSort{} -> True
        _               -> False

      extraRootsFilter (name, def)
        | hasCompilePragma def || isPrimitive (theDef def) = Just name
        | otherwise = Nothing

  let !pubModules = publicModules scope

    -- Ulf, 2016-04-12:
    -- Non-closed display forms are not applicable outside the module anyway,
    -- and should be dead-code eliminated (#1928).
  !rootDisplayForms <-
      HMap.filter (not . null) . HMap.map (filter isClosed) <$> useTC stImportsDisplayForms

  let !rootPubNames  = map anameName $ publicNamesOfModules pubModules
  let !rootExtraDefs = mapMaybe extraRootsFilter $ HMap.toList defs
  let !rootRewrites  = sig ^. sigRewriteRules
  let !rootModSections = sig ^. sigSections
  !rootBuiltins <- useTC stLocalBuiltins
  !rootPatSyns  <- getPatternSyns

  !seenNames <- liftIO HT.empty
  !seenMetas <- liftIO HT.empty

  let goName :: QName -> IO ()
      goName !x = HT.lookup seenNames x >>= \case
        Just _  -> pure ()
        Nothing -> do
          HT.insert seenNames x ()
          go (HMap.lookup x defs)

      goMeta :: MetaId -> IO ()
      goMeta !m = HT.lookup seenMetas m >>= \case
        Just _  -> pure ()
        Nothing -> do
          HT.insert seenMetas m ()
          case MapS.lookup m metas of
            Nothing -> pure ()
            Just mv -> do
              go (instBody (theInstantiation mv))
              go (jMetaType (mvJudgement mv))

      go :: NamesIn a => a -> IO ()
      go !x = namesAndMetasIn' (either goName goMeta) x
      {-# INLINE go #-}

  Bench.billTo [Bench.DeadCode, Bench.DeadCodeReachable] $ liftIO $ do
    go rootDisplayForms
    foldMap goName rootPubNames
    foldMap goName rootExtraDefs
    go rootRewrites
    go rootModSections
    go rootBuiltins
    foldMap (go . PSyn) rootPatSyns

  let filterMeta :: (MetaId, MetaVariable) -> IO (Maybe (MetaId, RemoteMetaVariable))
      filterMeta (!i, !m) = HT.lookup seenMetas i >>= \case
        Nothing -> pure Nothing
        Just _  -> let !m' = remoteMetaVariable m in pure $ Just (i, m')

      filterDef :: (QName, Definition) -> IO Bool
      filterDef (!x, !d) = HT.lookup seenNames x >>= \case
        Nothing -> pure False
        Just _  -> pure True

  !metas' <- liftIO $ HMap.fromList <$> mapMaybeM filterMeta (MapS.toList metas)
  !defs'  <- liftIO $ HMap.fromList <$> filterM filterDef (HMap.toList defs)
  pure (metas', defs', rootDisplayForms)

-- | Returns the instantiation.
--   Precondition: The instantiation must be of the form @'InstV' inst@.
theInstantiation :: MetaVariable -> Instantiation
theInstantiation mv = case mvInstantiation mv of
  InstV inst                     -> inst
  OpenMeta{}                     -> __IMPOSSIBLE__
  BlockedConst{}                 -> __IMPOSSIBLE__
  PostponedTypeCheckingProblem{} -> __IMPOSSIBLE__

-- | Converts from 'MetaVariable' to 'RemoteMetaVariable'.
--   Precondition: The instantiation must be of the form @'InstV' inst@.
remoteMetaVariable :: MetaVariable -> RemoteMetaVariable
remoteMetaVariable !mv = RemoteMetaVariable
  { rmvInstantiation = theInstantiation mv
  , rmvModality      = getModality mv
  , rmvJudgement     = mvJudgement mv
  }

---------------------------------------------------------------------------
-- * Attributing names to source files
---------------------------------------------------------------------------

-- | Maps a top-level module name to its source file, longest name first.
type ModuleFileTable = [(String, FilePath)]

-- | Build the module-to-file table.
--
--   Ranges must not be used for this.  A definition imported from another
--   module may carry no range at all, or a range pointing at the /importing/
--   file, so attributing names to files via 'getRange' misfiles every imported
--   definition.  The module name is reliable, so we resolve through
--   'stModuleToSource' instead.
moduleFileTable :: TCM ModuleFileTable
moduleFileTable = do
  m2s <- useTC stModuleToSource
  ids <- useTC stModuleToSourceId
  -- Only keys of stModuleToSourceId may be passed to topLevelModuleFilePath.
  pure $ sortOn (negate . length . fst)
    [ (prettyShow m, normalise $ filePath $ topLevelModuleFilePath m2s m)
    | m <- MapS.keys ids
    ]

-- | Source file of a name, resolved through its module.
sourceOfQName :: ModuleFileTable -> QName -> Maybe FilePath
sourceOfQName tbl qn = listToMaybe
    [ f | (m, f) <- tbl, mn == m || (m ++ ".") `isPrefixOf` mn ]
  where
    -- Sorted longest-first, so the first hit is the most specific module.
    mn = prettyShow (qnameModule qn)

-- | Is this name defined inside the given project directory?
qnameInProject :: FilePath -> ModuleFileTable -> QName -> Bool
qnameInProject projectDir tbl qn = case sourceOfQName tbl qn of
  Nothing -> False
  Just p  ->
    let rel = makeRelative (normalise projectDir) p
    in isRelative rel && not (".." `isPrefixOf` rel)

---------------------------------------------------------------------------
-- * Name lookup
---------------------------------------------------------------------------

-- | Look up a QName by its string representation (e.g. "Module.Name.function").
--   Returns Nothing if no such name exists in the signature.
--
--   Uses an optimized two-phase lookup:
--   1. First filters by the final name part (fast, short string comparison)
--   2. Then checks the full module path only for remaining candidates
lookupQNameByString :: String -> TCM (Maybe QName)
lookupQNameByString str = do
  sig <- getSignature
  let defs = sig ^. sigDefinitions
      -- Split the input "Module.Sub.name" into ["Module", "Sub", "name"]
      parts = splitOn "." str
  case parts of
    [] -> return Nothing
    _  -> do
      let lastPart = last parts
          -- Phase 1: Filter by final name part only (much faster than full prettyShow)
          -- Use nameCanonical to match Pretty QName instance behavior
          matchesName qn =
            C.nameToRawName (nameCanonical (qnameName qn)) == lastPart
          candidates = filter (matchesName . fst) $ HMap.toList defs
          -- Phase 2: Check full path for remaining candidates
          matchesFull qn = prettyShow qn == str
          matches = filter (matchesFull . fst) candidates
      case matches of
        [(qn, _)] -> return $ Just qn
        _         -> return Nothing

---------------------------------------------------------------------------
-- * Unreachable code warnings
---------------------------------------------------------------------------

-- | Check if a projection is unused (only referenced by its own definition and parent record).
--   A projection is considered "unused" if no other reachable definition references it.
isProjectionUnused
  :: Definitions              -- ^ All definitions
  -> HT.HashTable QName ()    -- ^ Set of reachable names
  -> (QName, Definition, QName)  -- ^ (projection name, projection def, parent record name)
  -> IO Bool
isProjectionUnused defs seenNames (projName, _projDef, recName) = do
  -- Check all reachable definitions (except the projection itself and its parent record)
  -- to see if any of them reference this projection
  reachableNames <- HT.toList seenNames
  let relevantNames = [name | (name, ()) <- reachableNames
                            , name /= projName
                            , name /= recName]

  -- Check if any relevant definition references this projection
  let referencesProj :: Definition -> Bool
      referencesProj def = projName `elem` (namesIn def :: [QName])

      isReferenced = any (\name -> maybe False referencesProj (HMap.lookup name defs)) relevantNames

  return (not isReferenced)

-- | Check for definitions not reachable from a given entry point.
--   Reports unreachable definitions and unused record fields as warnings.
--   Only reports definitions whose source file is within the given project directory.
checkUnreachableDefinitions :: FilePath -> QName -> TCM ()
checkUnreachableDefinitions projectDir root = do
  -- Get definitions from both current module and imported modules
  sig <- getSignature
  importedSig <- useTC stImports
  let defs = HMap.union (sig ^. sigDefinitions) (importedSig ^. sigDefinitions)

  -- Helper to check if a QName's source file is in the project directory.
  -- Uses makeRelative for robust path comparison:
  -- - Handles partial directory name matches (e.g., /foo vs /foobar)
  -- - Normalizes paths to handle //, ., etc.
  modTable <- moduleFileTable
  let isInProject :: QName -> Bool
      isInProject = qnameInProject projectDir modTable

  -- Build reachability set starting from root only
  -- Only recurse into definitions that are within the project directory
  -- to avoid traversing external libraries (which could cause OOM)
  seenNames <- liftIO HT.empty

  let goName :: QName -> IO ()
      goName !x = HT.lookup seenNames x >>= \case
        Just _  -> pure ()
        Nothing -> do
          HT.insert seenNames x ()
          -- Only recurse into definitions within the project directory
          when (isInProject x) $ go (HMap.lookup x defs)

      go :: NamesIn a => a -> IO ()
      go !x = namesIn' goName x

  liftIO $ goName root

  -- Collect all unreachable definitions that are in the project
  unreachable <- liftIO $ filterM
    (\(x, _) -> isNothing <$> HT.lookup seenNames x)
    (HMap.toList defs)

  -- Filter to only definitions in the project directory
  let unreachableInProject = filter (isInProject . fst) unreachable

  -- For record projections, we need special handling:
  -- A projection is "reachable" just by being defined (its parent record references it).
  -- We want to detect projections that are DEFINED but never APPLIED.
  --
  -- Strategy: For each projection in the project, check if it's referenced from
  -- anywhere OTHER than its own definition and its parent record's definition.
  let getProjectionInfo def = case theDef def of
        Function{ funProjection = Right Projection{ projProper = Just recName } } ->
          Just recName
        _ -> Nothing

      -- All projections in the project (both reachable and unreachable)
      -- Filter out defCopy projections (re-exports via module aliases)
      allProjections = [(name, def, recName)
                       | (name, def) <- HMap.toList defs
                       , isInProject name
                       , not (defCopy def)
                       , Just recName <- [getProjectionInfo def]]

  -- For each projection, check if it has references from non-parent sources
  -- by re-traversing the signature excluding the projection's own def and parent record
  unusedProjections <- liftIO $ filterM (isProjectionUnused defs seenNames) allProjections

  let unusedFields = [(recName, qnameName name) | (name, _def, recName) <- unusedProjections]

  -- Separate remaining unreachable definitions (non-projections and non-copies)
  -- defCopy marks definitions created by module application (e.g., "module M = OtherModule"),
  -- which are re-exports rather than real definitions. We exclude them since the original
  -- definition will be reported if truly unreachable.
  let isRecordProjection def = case theDef def of
        Function{ funProjection = Right Projection{ projProper = Just _ } } -> True
        _ -> False

      unreachableOther = filter (\(_, def) ->
        not (isRecordProjection def) && not (defCopy def)) unreachableInProject

  -- Emit warnings
  List1.unlessNull (map fst unreachableOther) $ \xs ->
    warning $ UnreachableDefinitions xs

  List1.unlessNull unusedFields $ \xs ->
    warning $ UnusedRecordFields xs
