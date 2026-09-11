{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wunused-imports #-}

-- | Dump the portion of the internal syntax reachable from a given entry
--   point, together with the trust base (postulates and other assumptions)
--   that the entry point depends on.
--
--   This is a /lens/ into the elaborated signature: it reports what the
--   entry point actually depends on, at definition granularity rather than
--   module granularity.  It deliberately does not decide what is safe to
--   delete -- that requires project-specific knowledge Agda does not have.
--
--   Note on completeness: the reachable set is computed from the elaborated
--   internal syntax, so it captures semantic dependencies of the proof term.
--   Some source-level dependencies leave no trace there and are therefore
--   reported separately as /ambient/ assumptions rather than as reachable
--   definitions:
--
--     * rewrite rules apply during conversion checking and are never
--       name-referenced (see the note in "Agda.TypeChecking.DeadCode");
--     * macros are expanded at elaboration time, so the expansion is
--       reachable but the macro itself is not;
--     * @BUILTIN@ bindings live in a separate table.
--
--   == Streaming
--
--   The dump is written incrementally.  The reachable set of a real
--   development is large -- it includes everything the entry point touches
--   in every library it uses -- and the expensive part of an entry is
--   pretty-printing its type.  So the work is split in two: a cheap pass
--   classifies every reachable name (in the project?  an assumption?),
--   which is enough for the counts and for the trust base, and a second
--   pass renders one definition at a time straight to the output handle.
--   Nothing but the trust base is ever held in memory in rendered form, and
--   no type is printed that is not also emitted.
--
--   == Stability
--
--   Two dumps of neighbouring versions of a development should differ only
--   where the development does, so that the dump can be committed and
--   reviewed as a diff.  That rules out anything ordered by 'NameId', which
--   is allocated in typechecking order and shifts when a definition is
--   added anywhere earlier, and anything ordered by hashing, which is not
--   meaningful at all.  Every list in the output is therefore ordered by
--   printed name, paths are relative to the project, and line/column ranges
--   -- which move whenever anything above them does -- are reported only
--   for the trust base, where the point is to go and look at them.

module Agda.TypeChecking.ASTDump
  ( writeASTDump
  ) where

import Control.Monad (forM, forM_, unless)
import Control.Monad.Except (catchError, throwError)
import Control.Monad.IO.Class (liftIO)

import Data.Foldable (foldl')
import Data.List (partition, sortOn, stripPrefix)
import qualified Data.HashMap.Strict as HMap
import qualified Data.Map.Strict as MapS
import qualified Data.Set as Set

import System.FilePath (makeRelative, normalise)
import System.IO
  ( BufferMode (BlockBuffering), IOMode (WriteMode)
  , hClose, hPutStr, hSetBuffering, hSetEncoding, openFile, stdout, utf8 )

import Agda.Syntax.Common (NameId)
import Agda.Syntax.Common.Pretty (prettyShow, render)
import Agda.Syntax.Internal
import Agda.Syntax.Internal.Names (namesIn)
import Agda.Syntax.Position (getRange, rangeFile, rangeFilePath)

import Agda.Interaction.Options.Base (unsafePragmaOptions)
import Agda.Interaction.Options.Types (ASTFormat (..))
import Agda.TypeChecking.DeadCode
  ( ModuleFileTable, moduleFileTable, sourceOfQName, pathInProject )

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Pretty (prettyTCM)
import Agda.TypeChecking.Warnings (warning)

import Agda.Utils.FileName (filePath)
import Agda.Utils.Lens
import Agda.Utils.List (headWithDefault)
import qualified Agda.Utils.List1 as List1
import qualified Agda.Utils.Maybe.Strict as Strict

import Agda.Utils.Impossible

---------------------------------------------------------------------------
-- * Reachability
---------------------------------------------------------------------------

-- | Breadth-first reachability from the entry point, recording for each name
--   the predecessor that first discovered it.  BFS (rather than the DFS used
--   by "Agda.TypeChecking.DeadCode") means the recorded witness path is the
--   shortest one, which is also the most readable.
--
--   The search proceeds level by level, and each level is processed in name
--   order.  BFS already fixes the /length/ of the witness path; taking the
--   levels in name order also fixes its /shape/, by making the recorded
--   predecessor the least one among those at minimal distance.  Otherwise
--   which of two equally close callers is credited would depend on the order
--   the internal syntax happens to be traversed in, and witness paths would
--   shuffle on unrelated edits.
--
--   Sorting the levels costs one 'prettyShow' per reachable name, not per
--   edge: within a single node the order of its dependencies cannot affect
--   which predecessor they get, since it is that node either way.
--
--   Unlike 'checkUnreachableDefinitions' this traverses /everything/,
--   including external libraries.  Restricting the traversal to the project
--   would under-approximate: a postulate reached through a standard library
--   higher-order function would be silently missed, and for a trust-base
--   report a false negative is much worse than a false positive.
reachableFrom :: Definitions -> QName -> HMap.HashMap QName QName
reachableFrom defs root = go (HMap.singleton root root) [root]
  where
    go !seen [] = seen
    go !seen level =
      let (seen', discovered) = foldl' visit (seen, []) level
      in  go seen' (sortOn prettyShow discovered)

    visit acc x = foldl' (step x) acc $ depsOf x

    step x (!s, acc) y
      | HMap.member y s = (s, acc)
      | otherwise       = (HMap.insert y x s, y : acc)

    depsOf x = Set.toList $ Set.fromList
      (maybe [] namesIn (HMap.lookup x defs) :: [QName])

-- | Reconstruct the witness path from the entry point to a name.
witnessPath :: HMap.HashMap QName QName -> QName -> QName -> [QName]
witnessPath preds root = walk (0 :: Int) []
  where
    walk n acc y
      | y == root  = root : acc
      | n > 100000 = y : acc   -- cycle guard; should be unreachable
      | otherwise  = case HMap.lookup y preds of
          Nothing            -> y : acc
          Just p | p == y    -> y : acc
                 | otherwise -> walk (n + 1) (y : acc) p

---------------------------------------------------------------------------
-- * Classification
---------------------------------------------------------------------------

defKind :: Defn -> String
defKind = \case
  Axiom{}            -> "postulate"
  DataOrRecSig{}     -> "data-or-record-signature"
  GeneralizableVar{} -> "generalizable-variable"
  AbstractDefn{}     -> "abstract"
  Function{}         -> "function"
  Datatype{}         -> "datatype"
  Record{}           -> "record"
  Constructor{}      -> "constructor"
  Primitive{}        -> "primitive"
  PrimitiveSort{}    -> "primitive-sort"

-- | Why a definition is part of the trust base.
--
--   An assumption has a /site/ -- the place the user wrote it -- and a set of
--   definitions that inherit it.  Only the site is countable: a @TERMINATING@
--   pragma covers a whole mutual block, and elaboration then adds
--   with-functions and other helpers to that block, so counting definitions
--   that carry a marker reports one pragma many times over.
data Marker = Marker
  { mkMarker       :: String
      -- ^ Which assumption, e.g. @postulate@ or @terminating-pragma@.
  , mkObligation :: Bool
      -- ^ See 'obligationMarkers'.
  , mkSite       :: QName
      -- ^ Where it was written.
  }

-- | Markers that make a definition part of the trust base, i.e. things that
--   @--safe@ would reject or that otherwise represent an unproven assumption.
--
--   Ordinary primitives are deliberately /not/ flagged: @--safe@ permits them,
--   and flagging them would bury the real assumptions under every arithmetic
--   builtin the entry point happens to reach.  Only the two primitives that
--   are genuinely unsound are reported.
safetyMarkers :: Definition -> [Marker]
safetyMarkers d = concat
  [ [ own "postulate"               | isAxiom (theDef d)          ]
  , [ own "unsafe-primitive"        | isUnsafePrimitive (theDef d) ]
  , [ own "injective-pragma"        | defInjective d              ]
  , [ own "termination-unconfirmed" | defTerminationUnconfirmed d ]
  , [ own "macro"                   | isMacro (theDef d)          ]
    -- Declaration-level pragmas carry their own site, recorded where the
    -- pragma was consumed; see 'Agda.TypeChecking.Monad.Signature.pragmaSite'.
  , [ marker (pragmaMarker p) site
    | (p, site) <- MapS.toAscList $ defUnsafePragmas d ]
  ]
  where
    -- Everything but a declaration-level pragma is written at the definition
    -- it appears on.
    own n  = marker n (defName d)
    marker n site = Marker
      { mkMarker       = n
      , mkObligation = n `elem` obligationMarkers
      , mkSite       = site
      }
    isAxiom = \case { Axiom{} -> True; _ -> False }
    pragmaMarker = \case
      UnsafeNoPositivityCheck -> "no-positivity-check"
      UnsafeNoUniverseCheck   -> "no-universe-check"
      UnsafeNonCovering       -> "non-covering"
      UnsafeTerminating       -> "terminating-pragma"
      UnsafeNonTerminating    -> "non-terminating-pragma"
    isUnsafePrimitive = \case
      Primitive{ primName = p } ->
        prettyShow p `elem` [ "primTrustMe", "primEraseEquality" ]
      _ -> False

-- | Assumptions that a proof discharges: write the proof and the assumption
--   goes away, at the site where it is reported.
--
--   The rest are assertions.  @INJECTIVE@ and @NO_UNIVERSE_CHECK@ state
--   something the checker cannot confirm and that no Agda proof replaces;
--   @primTrustMe@ and @primEraseEquality@ are library-level and cannot be
--   discharged where they are used; a macro is a completeness caveat of this
--   analysis rather than an assumption at all (see the module header).
--   Separating the two keeps assertions from padding the number that matters,
--   which is how many proofs are outstanding.
obligationMarkers :: [String]
obligationMarkers =
  [ "postulate"
  , "terminating-pragma"
  , "non-terminating-pragma"
  , "termination-unconfirmed"
  , "no-positivity-check"
  , "non-covering"
  ]

-- | What is known about a reachable name without pretty-printing anything.
--
--   This is computed for every name in the reachable set, so it must stay
--   cheap: it decides the counts, the trust base, and the output order, and
--   only then are the definitions that survive rendered in full.
data Class = Class
  { clQName     :: QName
  , clName      :: String
      -- ^ 'prettyShow' of the name; computed once, it is the sort key.
  , clSource    :: Maybe FilePath
      -- ^ Absolute source file, resolved through the module.
  , clExternal  :: Bool
  , clGenerated :: Bool
      -- ^ See 'isGeneratedDefn'.  Generated definitions are never listed.
  , clMarkers   :: [Marker]
  }

classify :: FilePath -> ModuleFileTable -> Definitions -> QName -> TCM Class
classify projectDir modTable defs x = do
  let msrc     = sourceOfQName modTable x
      external = maybe True (not . pathInProject projectDir) msrc
      mdef     = HMap.lookup x defs
      markers0 = maybe [] safetyMarkers mdef

  -- The sanctioned-postulate test costs a file lookup, so only pay for it
  -- where it can change the answer.
  markers <-
    if all ((/= "postulate") . mkMarker) markers0 then pure markers0 else do
      ok <- isSanctionedPostulate x
      pure $ if ok then filter ((/= "postulate") . mkMarker) markers0 else markers0

  pure Class
    { clQName     = x
    , clName      = prettyShow x
    , clSource    = msrc
    , clExternal  = external
    , clGenerated = maybe False isGeneratedDefn mdef
    , clMarkers   = markers
    }

-- | Postulates in Agda's own builtin modules are sanctioned by @--safe@
--   (see 'Agda.Syntax.Translation.ConcreteToAbstract.niceDecls'), so they are
--   not assumptions the user can discharge.  Reporting them would put
--   @Agda.Primitive.Level@ in the trust base of every single project.
--
--   The file-based predicate covers @Agda/Builtin/*.agda@, but definitions in
--   @Agda.Primitive@ are constructed internally and carry no range at all, so
--   they are matched on the module name instead.  These are exactly the two
--   'Agda.Interaction.Library.primitiveModules'.
isSanctionedPostulate :: QName -> TCM Bool
isSanctionedPostulate x = case rangeFile (getRange x) of
  Strict.Just rf  -> isBuiltinModuleWithSafePostulates =<< idFromFile (rangeFilePath rf)
  Strict.Nothing  -> pure $ prettyShow (qnameModule x) `elem`
    [ "Agda.Primitive", "Agda.Primitive.Cubical" ]

-- | The sort order of the dump.
--
--   'prettyShow' is not injective -- generated names (with-functions,
--   extended lambdas) can print alike -- and the obvious tie-breaker,
--   'Ord QName', compares 'NameId's, which are allocated in typechecking
--   order and therefore shift whenever a definition is added earlier in the
--   development.  Break ties on the source file first, which is stable, and
--   fall back on the name id only for names that are otherwise
--   indistinguishable.
sortKey :: Class -> (String, Maybe FilePath, NameId)
sortKey c = (clName c, clSource c, nameId (qnameName (clQName c)))

---------------------------------------------------------------------------
-- * Assumptions
---------------------------------------------------------------------------

-- | One assumption: a site, and everything that inherits it.
data Assumption = Assumption
  { auMarker     :: String
  , auObligation :: Bool
  , auSite       :: QName
  , auSiteName   :: String
  , auReached    :: Class
      -- ^ The covered definition the entry point actually depends on.  The
      --   site itself need not be reachable: a pragma covers a whole mutual
      --   block, and the entry point may use only one member of it.
  , auCovered    :: [String]
      -- ^ Other source-level definitions covered, reachable from the entry
      --   point.  Excludes 'auReached'.
  , auGenerated  :: Int
      -- ^ Generated definitions covered.  Counted, never named: they are
      --   compiler internals, not something anyone wrote.
  }

-- | Group the reachable definitions that carry markers into assumptions, one
--   per (site, marker).  This is the step that turns "202 definitions carry a
--   TERMINATING pragma" into "22 TERMINATING pragmas were written".
assumptionsOf :: [Class] -> [Assumption]
assumptionsOf classes = sortOn key
  [ mkAssumption m members
  | (m, members) <- MapS.toList grouped
  ]
  where
    grouped = MapS.fromListWith (++)
      [ ((mkMarker mk, mkSite mk), [c])
      | c  <- classes
      , mk <- clMarkers c
      ]

    mkAssumption (name, site) members = Assumption
      { auMarker     = name
      , auObligation = name `elem` obligationMarkers
      , auSite       = site
      , auSiteName   = prettyShow site
      , auReached    = reached
      , auCovered    = map clName $ filter ((/= clName reached) . clName) sourceLevel
      , auGenerated  = length members - length sourceLevel
      }
      where
        ordered     = sortOn sortKey members
        sourceLevel = filter (not . clGenerated) ordered
        -- Prefer a source-level definition to stand for the assumption; fall
        -- back to a generated one only if the entry point reaches nothing else,
        -- so that an assumption is never dropped for want of a name to show.
        reached     = case ordered of
          []      -> __IMPOSSIBLE__   -- a group is built from its members
          (c : _) -> headWithDefault c sourceLevel

    key a = (not (auObligation a), auMarker a, auSiteName a)

---------------------------------------------------------------------------
-- * Rendered entries
---------------------------------------------------------------------------

-- | How much of an entry to render.
data Detail
  = Brief   -- ^ For the bulk listing: type and dependencies, no range or path.
  | Full    -- ^ For the trust base: range and witness path, no dependencies.

data Entry = Entry
  { eClass     :: Class
  , eKind      :: String
  , eType      :: String
  , eSource    :: Maybe FilePath
      -- ^ Relative to the project, when inside it.
  , eSrcRange  :: String
  , eDeps      :: [String]
  , ePath      :: [String]
  }

mkEntry
  :: Detail
  -> FilePath
  -> Definitions
  -> HMap.HashMap QName QName
  -> QName
  -> Class
  -> TCM Entry
mkEntry detail projectDir defs preds root c = do
  let x    = clQName c
      mdef = HMap.lookup x defs
  ty <- case mdef of
    Nothing -> pure ""
    Just d  -> oneLine . render <$> prettyTCM (defType d)
  pure Entry
    { eClass     = c
    , eKind      = maybe "unknown" (defKind . theDef) mdef
    , eType      = ty
    , eSource    = relativeTo projectDir <$> clSource c
    , eSrcRange  = case detail of
        Brief -> ""
        Full  -> trustedRange projectDir (clSource c) x
    , eDeps      = case detail of
        -- External definitions are emitted as boundary stubs: including their
        -- dependency lists would balloon the dump with standard library
        -- internals without telling the user anything about their project.
        -- Trust-base entries carry no dependencies either; an in-project one
        -- is listed again below, with them.
        Brief | not (clExternal c) -> sourceDeps defs x
        _                          -> []
    , ePath      = case detail of
        Brief -> []
        Full  -> sourcePath defs $ witnessPath preds root x
    }

-- | The names a definition depends on, with generated definitions contracted
--   out of the graph: a dependency on a with-function is replaced by whatever
--   that with-function depends on, transitively.
--
--   Generated definitions are never listed, so leaving edges pointing at them
--   would leave the listing referring to names it does not contain.  Contracting
--   rather than dropping keeps the dependency real: @f@ genuinely depends on
--   what its own with-block uses.
--
--   Sorting the /strings/ is what makes this stable: a @Set QName@ is ordered
--   by 'NameId', so a definition added anywhere earlier in the development
--   would reshuffle every dependency list in the dump.
--
--   Self-references are kept: they are how self-recursion appears, and the
--   graph is cyclic anyway (mutual blocks give genuine cycles).  Contraction
--   can introduce one, which is equally true: a with-function calling its
--   parent is that parent recursing.
sourceDeps :: Definitions -> QName -> [String]
sourceDeps defs =
  -- Sort the printed names, not the 'QName's: 'Ord QName' compares 'NameId's.
  Set.toAscList . Set.fromList . map prettyShow . Set.toList
    . go Set.empty Set.empty . directDeps
  where
    directDeps q = Set.fromList (maybe [] namesIn (HMap.lookup q defs) :: [QName])

    go !expanded !acc frontier = case Set.minView frontier of
      Nothing        -> acc
      Just (y, rest)
        | not (generated y)      -> go expanded (Set.insert y acc) rest
        | Set.member y expanded  -> go expanded acc rest
        | otherwise              ->
            go (Set.insert y expanded) acc (Set.union rest (directDeps y))

    generated y = maybe False isGeneratedDefn $ HMap.lookup y defs

-- | A witness path with the generated definitions dropped.
--
--   A path ending at @-invert1054@ points at a name that is not in the source
--   and cannot be navigated to; dropping those leaves the source-level route
--   the entry point takes, which is what the reader can actually follow.
sourcePath :: Definitions -> [QName] -> [String]
sourcePath defs =
  map prettyShow . filter (not . generated)
  where
    generated y = maybe False isGeneratedDefn $ HMap.lookup y defs

-- | Source range of a name, with the file made relative to the project.
--
--   A range on an imported name can point at the /importing/ file (see
--   'moduleFileTable'), so a range is reported only when it agrees with the
--   module-resolved source file.
trustedRange :: FilePath -> Maybe FilePath -> QName -> String
trustedRange projectDir msrc x = case rangeFile (getRange x) of
  Strict.Nothing -> ""
  Strict.Just rf
    | Just (normalise printed) /= fmap normalise msrc -> ""
    | otherwise -> maybe full (relativeTo projectDir printed ++) $
                     stripPrefix printed full
    where
      printed = filePath (rangeFilePath rf)
      full    = prettyShow (getRange x)

-- | Report paths relative to the project, so that a dump taken on one
--   machine is comparable with one taken on another.
relativeTo :: FilePath -> FilePath -> FilePath
relativeTo projectDir p
  | pathInProject projectDir p = makeRelative (normalise projectDir) p
  | otherwise                  = p

-- | Collapse a pretty-printed type onto a single line.  'prettyTCM' wraps
--   long types, which would otherwise break the line-oriented text format
--   and turn a JSON entry into an unreadable run of escaped newlines.
oneLine :: String -> String
oneLine = unwords . words

---------------------------------------------------------------------------
-- * Ambient assumptions
---------------------------------------------------------------------------

data Ambient = Ambient
  { amRewriteRules :: [String]
  , amBuiltins     :: [String]
  , amUnsafeOpts   :: [(String, [String])]
  }

-- | Every list here is sorted by printed name.  The underlying tables are a
--   'HMap.HashMap' keyed by 'QName' and a 'MapS.Map' keyed by 'ModuleName',
--   whose iteration orders are hash order and 'NameId' order respectively --
--   neither is meaningful, and both move under unrelated edits.
collectAmbient :: TCM Ambient
collectAmbient = do
  sig      <- getSignature
  impSig   <- useTC stImports
  builtins <- useTC stLocalBuiltins
  visited  <- getVisitedModules

  let rules = sortedNub $ concatMap (map (prettyShow . rewName)) $
                HMap.elems (sig ^. sigRewriteRules) ++
                HMap.elems (impSig ^. sigRewriteRules)

      unsafeOpts = sortOn fst
        [ (prettyShow m, flags)
        | (m, mi) <- MapS.toList visited
        , let flags = unsafePragmaOptions (iOptionsUsed (miInterface mi))
        , not (null flags)
        ]

  pure Ambient
    { amRewriteRules = rules
    , amBuiltins     = sortedNub $ map getBuiltinId $ MapS.keys builtins
    , amUnsafeOpts   = unsafeOpts
    }

sortedNub :: Ord a => [a] -> [a]
sortedNub = Set.toAscList . Set.fromList

---------------------------------------------------------------------------
-- * Output
---------------------------------------------------------------------------

-- | Where the dump goes.  Writing through a sink rather than returning a
--   'String' is what lets the reachable listing be rendered one definition
--   at a time.
type Sink = String -> TCM ()

withOutputSink :: FilePath -> (Sink -> TCM a) -> TCM a
withOutputSink "-" k = k $ liftIO . hPutStr stdout
withOutputSink fp  k = do
  h <- liftIO $ do
    h <- openFile fp WriteMode
    -- Agda types are full of Unicode, and the locale encoding is not to be
    -- trusted: under @LC_ALL=C@ the default handle encoding fails on the
    -- first arrow.
    hSetEncoding h utf8
    hSetBuffering h $ BlockBuffering Nothing
    pure h
  -- TCM is not 'MonadUnliftIO', so the handle is closed by hand on both the
  -- normal and the exceptional path.
  r <- k (liftIO . hPutStr h) `catchError` \ err -> do
         liftIO $ hClose h
         throwError err
  liftIO $ hClose h
  pure r

---------------------------------------------------------------------------
-- * Entry point
---------------------------------------------------------------------------

data Counts = Counts
  { cReachable   :: Int
      -- ^ Everything the entry point reaches, generated definitions included.
  , cInProject   :: Int
      -- ^ Source-level definitions inside the project.  These are listed.
  , cOutside     :: Int
      -- ^ Source-level definitions outside it.
  , cGenerated   :: Int
      -- ^ Definitions produced by elaboration.  Counted, never listed.
  , cObligations :: Int
      -- ^ Assumptions a proof would discharge.
  , cAssertions  :: Int
      -- ^ Assumptions no proof replaces.
  }

-- | A trust-base entry: the assumption, and the rendered definition that
--   stands for it.
data TrustEntry = TrustEntry
  { tAssumption :: Assumption
  , tEntry      :: Entry
  }

-- | Compute the reachable set from the given root and write it out.
writeASTDump :: FilePath -> FilePath -> ASTFormat -> QName -> TCM ()
writeASTDump projectDir outFile format root = do
  sig    <- getSignature
  impSig <- useTC stImports
  let defs  = HMap.union (sig ^. sigDefinitions) (impSig ^. sigDefinitions)
      preds = reachableFrom defs root

  modTable <- moduleFileTable

  -- Pass 1: classify the whole reachable set.  Cheap by construction -- no
  -- type is printed here -- which is what makes it affordable to do for
  -- definitions that will not be emitted.
  classes <- sortOn sortKey <$>
               mapM (classify projectDir modTable defs) (HMap.keys preds)

  -- Definitions elaboration produced are not listed anywhere: they are
  -- compiler internals, and nobody can go and edit a with-function.  They are
  -- still traversed, still counted, and still contribute their assumptions --
  -- which are reported at the site the user did write.
  --
  -- Of what is left, only definitions inside the project (the enclosing git
  -- repository) are listed: nothing else can be edited or deleted, so listing
  -- the standard library would only add noise.  External definitions are still
  -- traversed -- dropping the edges would be wrong -- and an external
  -- assumption is still reported, because a library postulate is every bit as
  -- much part of the trust base as one of your own.
  let sourceLevel  = filter (not . clGenerated) classes
      inProject    = filter (not . clExternal) sourceLevel
      assumptions  = assumptionsOf classes
      (obligations, assertions) = partition auObligation assumptions
      counts = Counts
        { cReachable   = length classes
        , cInProject   = length inProject
        , cOutside     = length sourceLevel - length inProject
        , cGenerated   = length classes - length sourceLevel
        , cObligations = length obligations
        , cAssertions  = length assertions
        }

  -- The trust base is the small, actionable part, and it is reported twice
  -- (in the dump and as a warning), so it is the one list that is
  -- materialised.
  trustBase <- forM assumptions $ \ a ->
    TrustEntry a <$> mkEntry Full projectDir defs preds root (auReached a)
  ambient <- collectAmbient

  -- Surface the trust base in the compiler output as well as in the dump:
  -- it is the actionable part, and it is what makes the feature visible in
  -- an editor or CI log rather than only in a file nobody opens.  External
  -- assumptions are included, for the same reason they are listed in the
  -- dump; their names are module-qualified, so they are recognisable as
  -- coming from a library.
  List1.unlessNull (map trustBaseItem assumptions) $
    \ xs -> warning $ ReachableTrustBase xs

  let render1 = mkEntry Brief projectDir defs preds root

  withOutputSink outFile $ \ put -> case format of
    ASTFormatJSON -> renderJSON put root counts trustBase ambient render1 inProject
    ASTFormatText -> renderText put root counts trustBase ambient render1 inProject

  unless (outFile == "-") $
    reportSLn "tc.ast.dump" 10 $
      "Wrote AST dump for " ++ prettyShow root ++ " to " ++ outFile ++
      " (" ++ show (cInProject counts) ++ " reachable definitions, " ++
      show (cObligations counts) ++ " obligations)"

trustBaseItem :: Assumption -> TrustBaseItem
trustBaseItem a = TrustBaseItem
  { tbSite       = auSite a
  , tbMarker     = auMarker a
  , tbObligation = auObligation a
  , tbCovered    = length (auCovered a)
  , tbGenerated  = auGenerated a
  }

---------------------------------------------------------------------------
-- * Text rendering
---------------------------------------------------------------------------

renderText
  :: Sink -> QName -> Counts -> [TrustEntry] -> Ambient
  -> (Class -> TCM Entry) -> [Class] -> TCM ()
renderText put root counts trustBase ambient render1 inProject = do
  put $ unlines
    [ "AST dump for entry point: " ++ prettyShow root
    , ""
    , "Reachable definitions: " ++ show (cInProject counts)
        ++ " in project, " ++ show (cOutside counts) ++ " outside, "
        ++ show (cGenerated counts) ++ " compiler-generated (not listed)"
    , ""
    , "Assumptions: " ++ show (cObligations counts) ++ " to discharge, "
        ++ show (cAssertions counts) ++ " taken on trust"
    , ""
    , "== TRUST BASE =="
    , ""
    ]
  if null trustBase
    then put $ unlines
      [ "  (none -- no postulates or unsafe definitions are reachable)", "" ]
    else do
      -- Counted once per site: a pragma over a mutual block is one assumption,
      -- not one per function it covers, and not one per helper elaboration
      -- added to that block.
      section "OBLIGATIONS -- a proof discharges these"
              (filter (auObligation . tAssumption) trustBase)
      section "ASSERTIONS -- no proof replaces these"
              (filter (not . auObligation . tAssumption) trustBase)
  put $ unlines $ concat
    [ [ "== AMBIENT ASSUMPTIONS =="
      , ""
      , "  These are not name-reachable from the entry point, but can still"
      , "  affect whether it typechecks.  See the module header for why."
      , ""
      ]
    , renderAmbient ambient
    , [ "== REACHABLE DEFINITIONS =="
      , ""
      ]
    ]
  forM_ inProject $ \ c -> do
    e <- render1 c
    put $ unlines $ renderEntry e
  where
    section _     [] = pure ()
    section title ts = put $ unlines $
      ("  " ++ title) : "" : concatMap renderTrust ts

    locationOf e
      | not (null (eSrcRange e)) = Just (eSrcRange e)
      | otherwise                = eSource e

    renderTrust (TrustEntry a e) = concat
      [ [ "    " ++ upper (auMarker a) ++ "  " ++ auSiteName a
            ++ (if clExternal (eClass e) then "   [outside project]" else "") ]
      , [ "      type:  " ++ eType e | not (null (eType e)) ]
      , [ "      at:    " ++ loc | Just loc <- [locationOf e] ]
        -- The site is where the assumption was written; the entry point may
        -- depend on a different member of the group it covers.
      , [ "      via:   " ++ clName (eClass e)
        | clName (eClass e) /= auSiteName a ]
      , [ "      also:  " ++ joinCommas (auCovered a)
        | not (null (auCovered a)) ]
      , [ "      plus:  " ++ show (auGenerated a) ++ " compiler-generated"
        | auGenerated a > 0 ]
      , [ "      path:  " ++ joinArrows (ePath e) ]
      , [ "" ]
      ]

    renderEntry e = concat
      [ [ pad 12 (eKind e) ++ clName (eClass e) ]
      , [ "    type: " ++ eType e | not (null (eType e)) ]
      , [ "    deps: " ++ joinCommas (eDeps e) | not (null (eDeps e)) ]
      , [ "" ]
      ]

    upper = map toUpperChar
    toUpperChar c
      | c >= 'a' && c <= 'z' = toEnum (fromEnum c - 32)
      | otherwise            = c

renderAmbient :: Ambient -> [String]
renderAmbient a = concat
  [ [ "  Rewrite rules active: " ++ show (length (amRewriteRules a)) ]
  , map ("    " ++) (amRewriteRules a)
  , [ "" ]
  , [ "  Modules compiled with unsafe options: "
        ++ show (length (amUnsafeOpts a)) ]
  , [ "    " ++ m ++ "  " ++ unwords fs | (m, fs) <- amUnsafeOpts a ]
  , [ "" ]
  , [ "  BUILTIN bindings in scope: " ++ show (length (amBuiltins a)) ]
  , [ "" ]
  ]

pad :: Int -> String -> String
pad n s = s ++ replicate (max 1 (n - length s)) ' '

joinArrows :: [String] -> String
joinArrows []       = ""
joinArrows [x]      = x
joinArrows (x : xs) = x ++ " -> " ++ joinArrows xs

joinCommas :: [String] -> String
joinCommas []       = ""
joinCommas [x]      = x
joinCommas (x : xs) = x ++ ", " ++ joinCommas xs

---------------------------------------------------------------------------
-- * JSON rendering
---------------------------------------------------------------------------

-- A tiny hand-rolled JSON writer.  Using aeson here would work, but the
-- output shape is trivial and this keeps the module free of version-
-- dependent @Key@/@Value@ differences between aeson 1.x and 2.x.
--
-- The layout is one definition per line: the document is indented enough to
-- be read, but an entry is not spread over a dozen lines, so a diff between
-- two dumps has one changed line per changed definition.

data J = JStr String | JNum Int | JBool Bool | JArr [J] | JObj [(String, J)] | JNull

renderJSON
  :: Sink -> QName -> Counts -> [TrustEntry] -> Ambient
  -> (Class -> TCM Entry) -> [Class] -> TCM ()
renderJSON put root counts trustBase ambient render1 inProject = do
  -- Everything but the reachable listing is small and comes first, so the
  -- counts can still be reported up front: they are decided by the cheap
  -- classification pass, not by the entries.
  put $ unlines $ ("{" :) $ concatMap withComma
    [ jField 1 "entryPoint" $ JStr (prettyShow root)
    , jObjField 1 "counts"
        [ ("inProject", JNum (cInProject counts))
        , ("outside",   JNum (cOutside counts))
        , ("generated", JNum (cGenerated counts))
        , ("reachable", JNum (cReachable counts))
        ]
      -- Counted per site, not per definition: one pragma over a mutual block
      -- is one assumption however many definitions inherit it.
    , jObjField 1 "assumptions"
        [ ("obligations", JNum (cObligations counts))
        , ("assertions",  JNum (cAssertions counts))
        ]
    , ambientBlock 1 ambient
    , jArrField 1 "trustBase" $ map trustJ trustBase
    ]
  put $ indent 1 ++ jsonString "reachable" ++ ": ["
  n <- streamArray put 2 (fmap entryJ . render1) inProject
  put $ (if n == 0 then "" else "\n" ++ indent 1) ++ "]\n}\n"

trustJ :: TrustEntry -> J
trustJ (TrustEntry a e) = JObj $ concat
  [ [ ("assumption", JStr (auMarker a))
    , ("class",      JStr (if auObligation a then "obligation" else "assertion"))
    , ("site",       JStr (auSiteName a))
    , ("type",       JStr (eType e))
    , ("source",     maybe JNull JStr (eSource e))
    ]
  , [ ("range",    JStr (eSrcRange e))     | not (null (eSrcRange e)) ]
  , [ ("external", JBool True)             | clExternal (eClass e)    ]
    -- The site is where the assumption was written; @via@ is the definition
    -- the entry point actually reaches, when that is a different member of
    -- the group the site covers.
  , [ ("via", JStr (clName (eClass e)))
    | clName (eClass e) /= auSiteName a ]
  , [ ("covers", JObj $ concat
        [ [ ("definitions", JArr (map JStr (auCovered a)))
          | not (null (auCovered a)) ]
          -- Generated definitions are counted but never named: nobody wrote
          -- them, so there is nothing to go and look at.
        , [ ("generated", JNum (auGenerated a)) | auGenerated a > 0 ]
        ])
    | not (null (auCovered a)) || auGenerated a > 0 ]
  , [ ("path", JArr (map JStr (ePath e))) | not (null (ePath e)) ]
  ]

-- | Write a JSON array element by element, rendering each only when it is
--   about to be written.  Returns the number of elements emitted.
streamArray :: Sink -> Int -> (a -> TCM J) -> [a] -> TCM Int
streamArray put n render = go (0 :: Int)
  where
    go !i [] = pure i
    go !i (x : xs) = do
      j <- render x
      put $ (if i == 0 then "\n" else ",\n") ++ indent n ++ encodeJ j
      go (i + 1) xs

entryJ :: Entry -> J
entryJ e = JObj $ concat
  [ [ ("name",   JStr (clName (eClass e)))
    , ("kind",   JStr (eKind e))
    , ("type",   JStr (eType e))
    , ("source", maybe JNull JStr (eSource e))
    ]
    -- The optional fields are emitted only when they say something.  In
    -- particular @external@ is absent, rather than false, on the reachable
    -- listing, which by construction contains nothing but project
    -- definitions.  @assumptions@ names the sites this definition inherits
    -- from, so that the listing points back at the trust base rather than
    -- repeating it.
  , [ ("range",    JStr (eSrcRange e)) | not (null (eSrcRange e)) ]
  , [ ("external", JBool True)         | clExternal (eClass e)    ]
  , [ ("assumptions", JArr (map JStr sites)) | not (null sites) ]
  , [ ("deps",     JArr (map JStr (eDeps e))) | not (null (eDeps e)) ]
  , [ ("path",     JArr (map JStr (ePath e))) | not (null (ePath e)) ]
  ]
  where
    sites = Set.toAscList $ Set.fromList
      [ mkMarker m ++ " " ++ prettyShow (mkSite m) | m <- clMarkers (eClass e) ]

ambientBlock :: Int -> Ambient -> [String]
ambientBlock n a = concat
  [ [ indent n ++ jsonString "ambient" ++ ": {" ]
  , joinMembers
      [ jArrField (n + 1) "rewriteRules" $ map JStr (amRewriteRules a)
      , jArrField (n + 1) "builtins"     $ map JStr (amBuiltins a)
      , jArrField (n + 1) "unsafeModuleOptions"
          [ JObj [ ("module", JStr m), ("flags", JArr (map JStr fs)) ]
          | (m, fs) <- amUnsafeOpts a ]
      ]
  , [ indent n ++ "}" ]
  ]

indent :: Int -> String
indent n = replicate (2 * n) ' '

-- | @"key": value@ on one line.
jField :: Int -> String -> J -> [String]
jField n k v = [ indent n ++ jsonString k ++ ": " ++ encodeJ v ]

-- | @"key": { ... }@, one member per line.
jObjField :: Int -> String -> [(String, J)] -> [String]
jObjField n k kvs = concat
  [ [ indent n ++ jsonString k ++ ": {" ]
  , joinMembers [ jField (n + 1) k' v | (k', v) <- kvs ]
  , [ indent n ++ "}" ]
  ]

-- | @"key": [ ... ]@, one element per line.
jArrField :: Int -> String -> [J] -> [String]
jArrField n k [] = [ indent n ++ jsonString k ++ ": []" ]
jArrField n k js = concat
  [ [ indent n ++ jsonString k ++ ": [" ]
  , joinMembers [ [ indent (n + 1) ++ encodeJ j ] | j <- js ]
  , [ indent n ++ "]" ]
  ]

-- | Separate rendered members by commas, which go on the last line of each
--   member but the last.
joinMembers :: [[String]] -> [String]
joinMembers []       = []
joinMembers [b]      = b
joinMembers (b : bs) = withComma b ++ joinMembers bs

withComma :: [String] -> [String]
withComma [] = []
withComma ls = init ls ++ [ last ls ++ "," ]

encodeJ :: J -> String
encodeJ = \case
  JNull    -> "null"
  JBool b  -> if b then "true" else "false"
  JNum n   -> show n
  JStr s   -> jsonString s
  JArr xs  -> "[" ++ joinCommas (map encodeJ xs) ++ "]"
  JObj kvs -> "{" ++ joinCommas [ jsonString k ++ ": " ++ encodeJ v
                                | (k, v) <- kvs ] ++ "}"

jsonString :: String -> String
jsonString s = '"' : concatMap esc s ++ "\""
  where
    esc = \case
      '"'  -> "\\\""
      '\\' -> "\\\\"
      '\n' -> "\\n"
      '\r' -> "\\r"
      '\t' -> "\\t"
      c | c < ' '   -> "\\u" ++ pad4 (showHex (fromEnum c))
        | otherwise -> [c]
    pad4 h = replicate (4 - length h) '0' ++ h
    showHex 0 = "0"
    showHex n = go n ""
      where
        go 0 acc = acc
        go m acc = go (m `div` 16) (hexDigit (m `mod` 16) : acc)
        hexDigit d
          | d < 10    = toEnum (fromEnum '0' + d)
          | otherwise = toEnum (fromEnum 'a' + d - 10)
