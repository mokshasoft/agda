{-# OPTIONS_GHC -Wunused-imports #-}

-- | Find definitions that are candidates for being duplicates of each other,
--   by two exact criteria over the whole signature:
--
--     * /name/ -- the same base name is defined in more than one module;
--     * /type/ -- two definitions have the same elaborated type.
--
--   Both are exact: no thresholds, no heuristics, no similarity scores.  That
--   is the point.  A duplicate is invisible from both sides at once -- the
--   copy looks self-contained to anyone reading its module, and the
--   original's module never mentions the copy -- so only a query over the
--   whole signature can see it, and noticing does not scale past one module.
--
--   == This reports candidates, never conclusions
--
--   An exact match is /not/ evidence that taking it is an improvement.  There
--   are at least three unrelated reasons two definitions can legitimately
--   share a type, and no type-level analysis distinguishes any of them from a
--   genuine duplicate, because in all three cases the types really are the
--   same:
--
--     * /deliberate parallel families/ -- the renaming and substitution twins
--       of one generated family must both exist;
--     * /load-bearing duplication/ -- a copy that exists so that one part of
--       a development need not import another.  Where a build asserts \"the
--       kernel imports no library\", the duplicate is the mechanism by which
--       the guarantee holds, and deleting it is a soundness-architecture
--       regression.  The direction matters and is easy to get backwards: if
--       the ban is one-way, it is the /library/ copy that is the candidate;
--     * /specialised routes that are cheaper/ -- a hand-written chain can be
--       faster than the library lemma it is an instance of, because it
--       operates on a closed term.
--
--   So this module emits a list to read, and deliberately offers no rewrite,
--   no auto-fix and no \"delete the duplicate\" action.
--
--   == Elaborated body size
--
--   Every reported definition carries the size of its elaborated body, in
--   internal-syntax nodes.  Two definitions with /identical types/ are still
--   different propositions to a user if one elaborates to a term ten times
--   the size of the other, and that difference -- not anything visible in the
--   statement -- is what decides whether collapsing one into the other is a
--   win or a regression.  Agda knows this number and nothing outside it does,
--   which makes it the most useful column here in a language where memory is
--   the binding constraint.
module Agda.TypeChecking.DuplicateTypes
  ( findDuplicates
    -- * Type keys
    --
    -- | Exposed because the flatterm is also the representation a
    --   discrimination tree is built over, for pattern search
    --   (@SearchType subTm _ (subTm _ _) ≡ _@).  Such an index keys on a
    --   /prefix/ of the token sequence with a wildcard matching a whole
    --   subterm, which is why every token records its arity: the extent of a
    --   subterm is recoverable from the flat sequence alone.
  , TypeKey (..)
  , Token (..)
  , typeKey
  , flattenType
  ) where

import Control.Monad (unless)

import Data.List (sort, sortOn)
import Data.Maybe (fromMaybe, listToMaybe)
import qualified Data.HashMap.Strict as HMap
import qualified Data.Map.Strict as MapS
import qualified Data.Set as Set

import Agda.Syntax.Common
import Agda.Syntax.Common.Pretty (prettyShow, render)
import Agda.Syntax.Internal
import Agda.Syntax.Literal (Literal)

import Agda.Interaction.Options.Types (ReportFormat (..))
import Agda.TypeChecking.AnalysisOutput
import Agda.TypeChecking.DeadCode
  ( ModuleFileTable, moduleFileTable, sourceOfQName, pathInProject
  , allDefinitions )
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Pretty (prettyTCM)
import Agda.TypeChecking.Substitute () -- 'Subst' instances used by 'raise'
import Agda.TypeChecking.Substitute.Class (Subst, raise)
import Agda.TypeChecking.Warnings (warning)

---------------------------------------------------------------------------
-- * Type keys
---------------------------------------------------------------------------

-- | One node of a type's /flatterm/: the preorder traversal of the internal
--   syntax, one token per node, each recording how many children follow.
--
--   Internal syntax is de Bruijn, so this is α-canonical by construction --
--   there is no name to quotient by.  What the flattening does have to
--   normalise is the handful of places where Agda's representation has more
--   than one spelling for the same type; those are called out at the
--   traversal below.
data Token
  -- Terms.
  = TVar !Int !Int
      -- ^ @x es@: de Bruijn index, and how many eliminations follow.
  | TDef !NameId !Int
  | TCon !NameId !Int
  | TMeta !MetaId !Int
  | TLit !Literal
  | TLam !Hiding
      -- ^ One child: the body, under a binder.
  | TPi !Hiding
      -- ^ Two children: the domain, then the codomain under a binder.
  | TSortTerm
      -- ^ A sort used as a term.  One child.
  | TLevelTerm
      -- ^ A level used as a term.  One child.
  | TDontCare
  | TDummy !String !Int
  -- Eliminations.
  | TApply !Hiding
  | TProj !NameId
  | TIApply
      -- ^ Three children: the two endpoints and the interval argument.
  -- Sorts.
  | TUniv !Univ
  | TInf !Univ !Integer
  | TSizeUniv
  | TLockUniv
  | TLevelUniv
  | TIntervalUniv
  | TPiSort
  | TFunSort
  | TUnivSort
  | TDefS !NameId !Int
  | TMetaS !MetaId !Int
  | TDummyS !String
  -- Levels.
  | TMax !Integer !Int
  | TPlus !Integer
  deriving (Eq, Ord, Show)

-- | The canonical key of an elaborated type: two definitions share a key
--   exactly when their types are the same up to the normalisations described
--   at 'flattenType'.
newtype TypeKey = TypeKey [Token]
  deriving (Eq, Ord, Show)

typeKey :: Type -> TypeKey
typeKey = TypeKey . flattenType

-- | Flatten a type to its preorder token sequence.
--
--   Two representational choices are worth stating, because they are what
--   decides whether a genuine duplicate is found:
--
--   [The sort annotation on @El@ is dropped.]
--     A 'Type' is a term paired with its sort, but that sort is /derived/
--     from the term rather than written by the user, and it is not kept in
--     any canonical form -- an unreduced @FunSort@/@PiSort@ in one place and
--     the reduced @Set ℓ@ in another describe the same type.  Keying on it
--     would therefore add no precision and would split genuine duplicates
--     according to how far their sorts happened to get reduced.  A sort
--     appearing /inside/ a term is real content and is kept.
--
--   [@NoAbs@ is expanded into a real binder.]
--     A non-dependent function type can be represented either as a
--     pseudo-binder ('NoAbs') or as an 'Abs' whose variable does not occur.
--     These describe the same type but number their free variables
--     differently -- under 'NoAbs' the body is not under the binder, so its
--     indices are one lower -- so the pseudo-binder is expanded by raising,
--     which makes the two spellings produce the same key.
--
--   Modality is deliberately /not/ part of the key, so that two definitions
--   differing only in erasure or relevance land in the same class.  For
--   duplicate detection that is what you want: having written both the
--   erased and the unerased copy of a lemma is exactly the kind of thing
--   worth being shown.  'Hiding' /is/ kept, since it changes how a
--   definition is called.
flattenType :: Type -> [Token]
flattenType t = goType t []

-- | Tokens are accumulated as a difference list: the traversal is a right
--   fold over a tree, and appending at each node would be quadratic.
type DL = [Token] -> [Token]

goType :: Type -> DL
goType = goTerm . unEl   -- El sort dropped; see 'flattenType'.

goTerm :: Term -> DL
goTerm = \case
  Var i es   -> (TVar i (length es) :) . goElims es
  Lam ai b   -> (TLam (getHiding ai) :) . goAbs goTerm b
  Lit l      -> (TLit l :)
  Def q es   -> (TDef (nid q) (length es) :) . goElims es
  Con c _ es -> (TCon (nid (conName c)) (length es) :) . goElims es
  Pi dom b   -> (TPi (getHiding dom) :) . goType (unDom dom) . goAbs goType b
  Sort s     -> (TSortTerm :) . goSort s
  Level l    -> (TLevelTerm :) . goLevel l
  MetaV m es -> (TMeta m (length es) :) . goElims es
  DontCare v -> (TDontCare :) . goTerm v
  Dummy s es -> (TDummy s (length es) :) . goElims es

-- | Descend under a binder, expanding a pseudo-binder into a real one so
--   that both spellings of a non-dependent function type agree.  See
--   'flattenType'.
goAbs :: Subst a => (a -> DL) -> Abs a -> DL
goAbs f = \case
  Abs   _ a -> f a
  NoAbs _ a -> f (raise 1 a)

goElims :: Elims -> DL
goElims es k = foldr goElim k es

goElim :: Elim -> DL
goElim = \case
  Apply a      -> (TApply (getHiding a) :) . goTerm (unArg a)
  Proj _ q     -> (TProj (nid q) :)
  IApply x y r -> (TIApply :) . goTerm x . goTerm y . goTerm r

goSort :: Sort -> DL
goSort = \case
  Univ u l     -> (TUniv u :) . goLevel l
  Inf u n      -> (TInf u n :)
  SizeUniv     -> (TSizeUniv :)
  LockUniv     -> (TLockUniv :)
  LevelUniv    -> (TLevelUniv :)
  IntervalUniv -> (TIntervalUniv :)
  PiSort d s b -> (TPiSort :) . goTerm (unDom d) . goSort s . goAbs goSort b
  FunSort s s' -> (TFunSort :) . goSort s . goSort s'
  UnivSort s   -> (TUnivSort :) . goSort s
  MetaS m es   -> (TMetaS m (length es) :) . goElims es
  DefS q es    -> (TDefS (nid q) (length es) :) . goElims es
  DummyS s     -> (TDummyS s :)

-- | A level is a /maximum/, so the order its summands happen to be stored in
--   carries no meaning.  Flattening each summand and sorting the results
--   makes the key independent of it; level expressions are tiny, so this
--   costs nothing.
goLevel :: Level -> DL
goLevel (Max n ls) =
  (TMax n (length ls) :) . (concat (sort (map (\ l -> goPlus l []) ls)) ++)

goPlus :: PlusLevel -> DL
goPlus (Plus n t) = (TPlus n :) . goTerm t

nid :: QName -> NameId
nid = nameId . qnameName

---------------------------------------------------------------------------
-- * Candidates
---------------------------------------------------------------------------

-- | What is known about a definition without pretty-printing anything.
--
--   As in "Agda.TypeChecking.ASTDump", the expensive part is rendering a
--   type, so the pass that decides what to report must not do any: a type is
--   printed once per reported group, not once per definition considered.
data Cand = Cand
  { cdQName    :: QName
  , cdName     :: String
      -- ^ 'prettyShow' of the whole name; computed once, it is the sort key.
  , cdBase     :: String
      -- ^ Just the last component, which is what a name collision is keyed on.
  , cdModule   :: String
  , cdSource   :: Maybe FilePath
  , cdKind     :: String
  , cdBodySize :: Int
  , cdType     :: Type
  , cdTyped    :: Bool
      -- ^ Is this definition's type its content?  See 'typeIsContent'.
  }

-- | Size of a definition's elaborated body, in internal-syntax nodes.  See
--   the note on body size in the module header.
--
--   Definitions with no body -- a postulate, a datatype, a constructor --
--   report zero rather than being excluded: zero is the truth about them,
--   and it keeps the column comparable across a class whose members are not
--   all functions.
bodySize :: Definition -> Int
bodySize d = case theDef d of
  Function{ funClauses  = cs } -> clausesSize cs
  Primitive{ primClauses = cs } -> clausesSize cs
  _ -> 0
  where
    clausesSize cs = sum [ termSize b | c <- cs, Just b <- [clauseBody c] ]

-- | Is this definition's /type/ its content, and is it a thing someone
--   wrote on its own?  Only those are grouped by type.
--
--   Everything excluded here would be pure noise, and the reason is the same
--   in each case: the definition is part of a larger declaration rather than
--   a standalone one, so two of them sharing a type is structural and not
--   duplication.
--
--     * For a datatype or record, @defType@ is its /kind/: every
--       parameterless datatype in a development has the type @Set@, so
--       grouping on that says nothing at all.
--     * Any two nullary constructors of one datatype share its type --
--       @true@ and @false@ both have type @Bool@ -- and no one can delete
--       @false@ as a duplicate of @true@.
--     * Likewise two fields of one record with the same field type: they
--       both have type @R -> A@, and a field is not removable on its own.
--
--   A collision on the /name/ of any of these is still worth knowing, so
--   this filters only the by-type pass, not the by-name one.
typeIsContent :: Definition -> Bool
typeIsContent d = case theDef d of
  Datatype{}         -> False
  Record{}           -> False
  DataOrRecSig{}     -> False
  Constructor{}      -> False
  -- A @variable@ block declaration; its type is shared by design.
  GeneralizableVar{} -> False
  PrimitiveSort{}    -> False
  Function{ funProjection = Right Projection{ projProper = Just _ } } -> False
  _                  -> True

-- | Every source-level definition inside the project.
--
--   Definitions elaboration produced are excluded, as are the copies module
--   application makes: nobody wrote them, so they cannot be duplicates of
--   anything anyone can go and edit.  Definitions outside the project are
--   excluded too -- a match against the standard library is real, but this
--   report is a list of things the reader could change.
candidates :: FilePath -> ModuleFileTable -> Definitions -> [Cand]
candidates projectDir modTable defs = sortOn sortKey
  [ Cand
      { cdQName    = x
      , cdName     = prettyShow x
      , cdBase     = prettyShow (qnameName x)
      , cdModule   = prettyShow (qnameModule x)
      , cdSource   = msrc
      , cdKind     = defKind (theDef d)
      , cdBodySize = bodySize d
      , cdType     = defType d
      , cdTyped    = typeIsContent d
      }
  | (x, d) <- HMap.toList defs
  , not (isGeneratedDefn d)
  , let msrc = sourceOfQName modTable x
  , maybe False (pathInProject projectDir) msrc
  ]

-- | The sort order of the report.
--
--   'prettyShow' is not injective and 'Ord QName' compares 'NameId's, which
--   are allocated in typechecking order and shift whenever a definition is
--   added anywhere earlier.  Break ties on the source file, which is stable,
--   and fall back on the name id only for names that are otherwise
--   indistinguishable.  See the note in "Agda.TypeChecking.ASTDump".
sortKey :: Cand -> (String, Maybe FilePath, NameId)
sortKey c = (cdName c, cdSource c, nameId (qnameName (cdQName c)))

---------------------------------------------------------------------------
-- * Groups
---------------------------------------------------------------------------

-- | A group of definitions sharing a name or a type, with at least two
--   members.
data Group = Group
  { gLabel   :: String
      -- ^ The base name, for a name collision; unused for a type class,
      --   whose label is the rendered type.
  , gMembers :: [Cand]
  }

-- | Definitions whose base name is defined in more than one module.
--
--   Most collisions in a real development are deliberate, so the modules are
--   what the report leads with: they are what tells a reader which kind of
--   collision this is.
nameClashes :: [Cand] -> [Group]
nameClashes cands = sortOn gLabel
  [ Group base (sortOn sortKey members)
  | (base, members) <- MapS.toList grouped
  , distinctModules members > 1
  ]
  where
    grouped = MapS.fromListWith (++) [ (cdBase c, [c]) | c <- cands ]
    distinctModules = Set.size . Set.fromList . map cdModule

-- | Definitions sharing an elaborated type.
--
--   Ordered by their first member, not by size: the report is meant to be
--   committed and read as a diff, and a size-ordered list reshuffles
--   wholesale when one group gains a member.
typeClasses :: [Cand] -> [Group]
typeClasses cands = sortOn (fmap sortKey . listToMaybe . gMembers)
  [ Group "" ordered
  | members <- MapS.elems grouped
  , let ordered = sortOn sortKey members
  , length members > 1
  ]
  where
    grouped = MapS.fromListWith (++)
      [ (typeKey (cdType c), [c]) | c <- cands ]

---------------------------------------------------------------------------
-- * Rendered entries
---------------------------------------------------------------------------

data Member = Member
  { mName     :: String
  , mModule   :: String
  , mKind     :: String
  , mSource   :: Maybe FilePath
  , mRange    :: String
  , mBodySize :: Int
  }

mkMember :: FilePath -> Cand -> Member
mkMember projectDir c = Member
  { mName     = cdName c
  , mModule   = cdModule c
  , mKind     = cdKind c
  , mSource   = relativeTo projectDir <$> cdSource c
  , mRange    = trustedRange projectDir (cdSource c) (cdQName c)
  , mBodySize = cdBodySize c
  }

-- | A group with its members rendered, and -- for a type class -- the shared
--   type printed once.
data Rendered = Rendered
  { rLabel   :: String
  , rType    :: String
  , rMembers :: [Member]
  }

mkRendered :: Bool -> FilePath -> Group -> TCM Rendered
mkRendered withType projectDir g = do
  -- One print per group, not one per member: the members of a type class
  -- have, by construction, the same type.
  ty <- case (withType, gMembers g) of
    (True, c : _) -> oneLine . render <$> prettyTCM (cdType c)
    _             -> pure ""
  pure Rendered
    { rLabel   = gLabel g
    , rType    = ty
    , rMembers = map (mkMember projectDir) (gMembers g)
    }

---------------------------------------------------------------------------
-- * Entry point
---------------------------------------------------------------------------

data Counts = Counts
  { cConsidered   :: Int
      -- ^ Source-level definitions in the project.
  , cTypeKeyed    :: Int
      -- ^ Of those, the ones whose type is their content ('typeIsContent').
  , cTypeGroups   :: Int
  , cTypeMembers  :: Int
  , cNameGroups   :: Int
  , cNameMembers  :: Int
  }

-- | Group the project's definitions by name and by elaborated type, and
--   write the groups with at least two members out.
findDuplicates :: FilePath -> FilePath -> ReportFormat -> TCM ()
findDuplicates projectDir outFile format = do
  defs     <- allDefinitions
  modTable <- moduleFileTable

  let cands   = candidates projectDir modTable defs
      typed   = filter cdTyped cands
      byName  = nameClashes cands
      byType  = typeClasses typed
      counts  = Counts
        { cConsidered  = length cands
        , cTypeKeyed   = length typed
        , cTypeGroups  = length byType
        , cTypeMembers = sum (map (length . gMembers) byType)
        , cNameGroups  = length byName
        , cNameMembers = sum (map (length . gMembers) byName)
        }

  -- Surface the counts in the compiler output as well as in the report, so
  -- the feature is visible in an editor or a CI log and not only in a file
  -- nobody opens.  Only the counts: a development can have hundreds of
  -- collisions, and a warning listing them all would be unreadable, whereas
  -- the file is made to be read as a diff.
  --
  -- Nothing found means no warning, as for the trust base in
  -- "Agda.TypeChecking.ASTDump".  The report is written either way, so the
  -- answer is still on record; what a clean project does not get is a
  -- warning, which would also stop its interface being written.
  unless (cTypeGroups counts == 0 && cNameGroups counts == 0) $
    warning $ DuplicateDefinitions DuplicateReport
    { drTypeGroups  = cTypeGroups counts
    , drTypeMembers = cTypeMembers counts
    , drNameGroups  = cNameGroups counts
    , drNameMembers = cNameMembers counts
    , drFile        = outFile
    }

  withOutputSink outFile $ \ put -> case format of
    ReportJSON -> renderJSON put projectDir counts byName byType
    ReportText -> renderText put projectDir counts byName byType

  reportSLn "tc.duplicates" 10 $
    "Wrote duplicate report to " ++ outFile ++
    " (" ++ show (cTypeGroups counts) ++ " type classes, " ++
    show (cNameGroups counts) ++ " name collisions)"

-- | The caveat is part of the output, not documentation of it: the whole
--   design constraint on this feature is that an exact match is a candidate
--   to read and not a conclusion to act on.  See the module header.
caveat :: [String]
caveat =
  [ "  Duplication is frequently deliberate.  Parallel families must both"
  , "  exist; a copy that lets one part of a development avoid importing"
  , "  another may be carrying an architectural invariant, and deleting it"
  , "  would be a regression; and a specialised route can be cheaper than"
  , "  the general lemma it is an instance of.  Nothing in a type"
  , "  distinguishes those from a real duplicate."
  , ""
  , "  The body size is the elaborated size of each definition's proof term."
  , "  Two definitions with the same type are still different propositions"
  , "  if one elaborates to ten times the term, and that -- not anything in"
  , "  the statement -- is what decides whether collapsing them is a win."
  ]

---------------------------------------------------------------------------
-- * Text rendering
---------------------------------------------------------------------------

renderText
  :: Sink -> FilePath -> Counts -> [Group] -> [Group] -> TCM ()
renderText put projectDir counts byName byType = do
  put $ unlines $
    [ "Duplicate definition report"
    , ""
    , "Definitions considered: " ++ show (cConsidered counts)
        ++ " in project, of which " ++ show (cTypeKeyed counts)
        ++ " are keyed by type"
    , "Sharing an elaborated type: "
        ++ tally (cTypeGroups counts) (cTypeMembers counts)
    , "Defined in more than one module: "
        ++ tally (cNameGroups counts) (cNameMembers counts)
    , ""
    ] ++ caveat ++
    [ ""
    , "== SHARING AN ELABORATED TYPE =="
    , ""
    ]
  emit True byType "no two definitions in the project share a type"
  put $ unlines
    [ "== DEFINED IN MORE THAN ONE MODULE =="
    , ""
    ]
  emit False byName "every base name in the project is defined once"
  where
    tally g d = plural g "group" ++ ", " ++ plural d "definition"
    plural n what = show n ++ " " ++ what ++ (if n == 1 then "" else "s")

    emit withType gs none
      | null gs   = put $ unlines [ "  (none -- " ++ none ++ ")", "" ]
      | otherwise = mapM_ (one withType) gs

    one withType g = do
      r <- mkRendered withType projectDir g
      put $ unlines $ renderGroup r

renderGroup :: Rendered -> [String]
renderGroup r = concat
  [ [ "  " ++ heading ]
  , [ "    " ++ pad width (mName m)
        ++ pad 14 (mKind m)
        ++ pad 10 ("body " ++ show (mBodySize m))
        ++ location m
    | m <- rMembers r ]
  , [ "" ]
  ]
  where
    heading
      | null (rLabel r) = rType r
      | otherwise       = rLabel r ++ "  (" ++
          joinCommas (Set.toAscList (Set.fromList (map mModule (rMembers r))))
          ++ ")"
    width = 2 + maximum (1 : map (length . mName) (rMembers r))
    location m
      | not (null (mRange m)) = mRange m
      | otherwise             = fromMaybe "" (mSource m)

---------------------------------------------------------------------------
-- * JSON rendering
---------------------------------------------------------------------------

renderJSON
  :: Sink -> FilePath -> Counts -> [Group] -> [Group] -> TCM ()
renderJSON put projectDir counts byName byType = do
  put $ unlines $ ("{" :) $ concat
    [ withComma $ jObjField 1 "counts"
        [ ("considered",       JNum (cConsidered counts))
        , ("keyedByType",      JNum (cTypeKeyed counts))
        , ("typeGroups",       JNum (cTypeGroups counts))
        , ("typeDefinitions",  JNum (cTypeMembers counts))
        , ("nameGroups",       JNum (cNameGroups counts))
        , ("nameDefinitions",  JNum (cNameMembers counts))
        ]
    , withComma [ indent 1 ++ jsonString "note" ++ ": "
                    ++ encodeJ (JStr (oneLine (unlines caveat))) ]
    ]
  -- Both arrays are streamed, so a group's shared type is printed only when
  -- it is about to be written.
  array "sharingType" True byType
  put ",\n"
  array "sharingName" False byName
  put "\n}\n"
  where
    array k withType gs = do
      put $ indent 1 ++ jsonString k ++ ": ["
      n <- streamArray put 2 (fmap groupJ . mkRendered withType projectDir) gs
      put $ (if n == 0 then "" else "\n" ++ indent 1) ++ "]"

groupJ :: Rendered -> J
groupJ r = JObj $ concat
  [ [ ("name", JStr (rLabel r)) | not (null (rLabel r)) ]
  , [ ("type", JStr (rType r))  | not (null (rType r))  ]
  , [ ("size", JNum (length (rMembers r)))
    , ("modules", JArr $ map JStr $ Set.toAscList $ Set.fromList $
         map mModule (rMembers r))
    , ("members", JArr (map memberJ (rMembers r)))
    ]
  ]

memberJ :: Member -> J
memberJ m = JObj $ concat
  [ [ ("name",     JStr (mName m))
    , ("kind",     JStr (mKind m))
      -- The elaborated size of the proof term; see the module header.
    , ("bodySize", JNum (mBodySize m))
    , ("source",   maybe JNull JStr (mSource m))
    ]
  , [ ("range", JStr (mRange m)) | not (null (mRange m)) ]
  ]
