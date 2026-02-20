{-# OPTIONS_GHC -Wunused-imports #-}

module Agda.TypeChecking.DeadCode
  ( eliminateDeadCode
  , checkUnreachableDefinitions
  , lookupQNameByString
  ) where

import Control.Monad (filterM, when)
import Control.Monad.Trans

import Data.List (isPrefixOf, partition)
import System.FilePath (isRelative, makeRelative, normalise)
import Data.List.Split (splitOn)
import Data.Maybe
import qualified Data.Map.Strict as MapS
import qualified Data.HashMap.Strict as HMap

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

import Agda.Utils.HashTable (HashTable)
import qualified Agda.Utils.HashTable as HT

---------------------------------------------------------------------------
-- * Reachability traversal
---------------------------------------------------------------------------

-- | Compute the set of reachable names and metas starting from the given roots.
--   Traverses both name and meta references using 'namesAndMetasIn''.
--
--   The filter predicate controls which definitions to recurse into:
--   - Pass @const True@ to recurse into all definitions
--   - Pass a filter like @isInProject@ to avoid traversing external libraries
computeReachable
  :: (QName -> Bool)           -- ^ Should we recurse into this definition's references?
  -> [QName]                   -- ^ Root names to start from
  -> Definitions               -- ^ All definitions
  -> MapS.Map MetaId MetaVariable  -- ^ Solved metas
  -> IO (HashTable QName (), HashTable MetaId ())
computeReachable shouldRecurse roots defs metas = do
  seenNames <- HT.empty
  seenMetas <- HT.empty

  let goName :: QName -> IO ()
      goName !x = HT.lookup seenNames x >>= \case
        Just _  -> pure ()
        Nothing -> do
          HT.insert seenNames x ()
          when (shouldRecurse x) $ go (HMap.lookup x defs)

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

  mapM_ goName roots
  return (seenNames, seenMetas)

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

  -- Compute reachability with no filter (traverse everything)
  (!seenNames, !seenMetas) <- Bench.billTo [Bench.DeadCode, Bench.DeadCodeReachable] $
    liftIO $ computeReachable (const True) (rootPubNames ++ rootExtraDefs) defs metas

  -- Also traverse non-name roots for additional reachable names/metas
  let go :: NamesIn a => a -> IO ()
      go !x = namesAndMetasIn' (either goName goMeta) x
      goName !n = HT.lookup seenNames n >>= \case
        Just _  -> pure ()
        Nothing -> do
          HT.insert seenNames n ()
          go (HMap.lookup n defs)
      goMeta !m = HT.lookup seenMetas m >>= \case
        Just _  -> pure ()
        Nothing -> do
          HT.insert seenMetas m ()
          case MapS.lookup m metas of
            Nothing -> pure ()
            Just mv -> do
              go (instBody (theInstantiation mv))
              go (jMetaType (mvJudgement mv))

  liftIO $ do
    go rootDisplayForms
    go rootRewrites
    go rootModSections
    go rootBuiltins
    mapM_ (go . PSyn) rootPatSyns

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

-- | Check for definitions not reachable from a given entry point.
--   Reports unreachable definitions and unused record fields as warnings.
--   Only reports definitions whose source file is within the given project directory.
checkUnreachableDefinitions :: FilePath -> QName -> TCM ()
checkUnreachableDefinitions projectDir root = do
  sig <- getSignature
  let defs = sig ^. sigDefinitions
  metas <- useR stSolvedMetaStore

  -- Helper to check if a QName's source file is in the project directory.
  -- Uses makeRelative for robust path comparison:
  -- - Handles partial directory name matches (e.g., /foo vs /foobar)
  -- - Normalizes paths to handle //, ., etc.
  let normalizedProjectDir = normalise projectDir
      isInProject :: QName -> Bool
      isInProject qn = case rangeFile (getRange qn) of
        Strict.Nothing -> False
        Strict.Just rf ->
          let defPath = normalise $ filePath (rangeFilePath rf)
              relPath = makeRelative normalizedProjectDir defPath
          -- makeRelative returns an absolute path if defPath is not under projectDir,
          -- or returns ".." prefixed path if it escapes. A truly contained path
          -- will be relative and not start with ".."
          in isRelative relPath && not (".." `isPrefixOf` relPath)

  -- Build reachability set starting from root only
  -- Only recurse into definitions that are within the project directory
  -- to avoid traversing external libraries (which could cause OOM)
  (seenNames, _seenMetas) <- liftIO $ computeReachable isInProject [root] defs metas

  -- Collect all unreachable definitions that are in the project
  unreachable <- liftIO $ filterM
    (\(x, _) -> isNothing <$> HT.lookup seenNames x)
    (HMap.toList defs)

  -- Filter to only definitions in the project directory
  let unreachableInProject = filter (isInProject . fst) unreachable

  -- Separate record projections from other definitions
  let isRecordProjection def = case theDef def of
        Function{ funProjection = Right Projection{ projProper = Just _ } } -> True
        _ -> False

      (unreachableProjs, unreachableOther) = partition
        (\(_, def) -> isRecordProjection def)
        unreachableInProject

  -- Extract record field info from projections
  let getFieldInfo (name, def) = case theDef def of
        Function{ funProjection = Right Projection{ projProper = Just recName } } ->
          Just (recName, qnameName name)
        _ -> Nothing

      unusedFields = mapMaybe getFieldInfo unreachableProjs

  -- Emit warnings
  List1.unlessNull (map fst unreachableOther) $ \xs ->
    warning $ UnreachableDefinitions xs

  List1.unlessNull unusedFields $ \xs ->
    warning $ UnusedRecordFields xs
