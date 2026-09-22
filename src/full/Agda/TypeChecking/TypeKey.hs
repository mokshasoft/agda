{-# OPTIONS_GHC -Wunused-imports #-}

-- | The /flatterm/ of an elaborated type: its preorder traversal, one token
--   per node, each token recording how many children follow.
--
--   This is the representation both signature queries are built on.
--
--     * "Agda.TypeChecking.DuplicateTypes" uses the whole sequence as an
--       exact key, to group definitions that share a type.
--     * "Agda.TypeChecking.TypeSearch" matches a /pattern/ against it, with
--       a wildcard standing for any subterm.
--
--   Recording an arity on every token is what makes the second possible: the
--   extent of a subterm is recoverable from the flat sequence alone, so a
--   wildcard can skip exactly one subterm without reconstructing the tree.
--   'tokenArity' and 'flattenType' must therefore agree: a change to one is
--   a change to the other.
module Agda.TypeChecking.TypeKey
  ( -- * Flatterms
    Token (..)
  , TypeKey (..)
  , typeKey
  , flattenType
  , flattenTerm
  , tokenArity
    -- * Pattern matching
  , isWildcard
  , subtermSize
  , splitSubterm
  , matchesIn
  ) where

import Data.List (sort, tails)

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Literal (Literal)

import Agda.TypeChecking.Substitute () -- 'Subst' instances used by 'raise'
import Agda.TypeChecking.Substitute.Class (Subst, raise)

---------------------------------------------------------------------------
-- * Flatterms
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

-- | The flatterm of a bare term.  Used to compare two terms for syntactic
--   equality where 'Term' has no 'Eq' instance of its own -- in particular to
--   check that a hole bound twice was bound to the same thing.
flattenTerm :: Term -> [Token]
flattenTerm t = goTerm t []

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

-- | How many children a token has.  Must agree with 'flattenType'.
--
--   Tokens that carry a count -- a head applied to eliminations, a level with
--   summands -- report it; the rest are fixed by their shape.
tokenArity :: Token -> Int
tokenArity = \case
  TVar _ n     -> n
  TDef _ n     -> n
  TCon _ n     -> n
  TMeta _ n    -> n
  TLit _       -> 0
  TLam _       -> 1
  TPi _        -> 2
  TSortTerm    -> 1
  TLevelTerm   -> 1
  TDontCare    -> 1
  TDummy _ n   -> n
  TApply _     -> 1
  TProj _      -> 0
  TIApply      -> 3
  TUniv _      -> 1
  TInf _ _     -> 0
  TSizeUniv    -> 0
  TLockUniv    -> 0
  TLevelUniv   -> 0
  TIntervalUniv -> 0
  TPiSort      -> 3
  TFunSort     -> 2
  TUnivSort    -> 1
  TDefS _ n    -> n
  TMetaS _ n   -> n
  TDummyS _    -> 0
  TMax _ n     -> n
  TPlus _      -> 1

---------------------------------------------------------------------------
-- * Pattern matching
---------------------------------------------------------------------------

-- | A hole in a query pattern.
--
--   An @_@ in a search pattern elaborates to a metavariable, so that is what
--   a wildcard is.  A checked definition has no unsolved metas in its type,
--   so this cannot misfire on the candidate side.
isWildcard :: Token -> Bool
isWildcard = \case
  TMeta{} -> True
  _       -> False

-- | Length of the subterm the sequence starts with, or 'Nothing' if the
--   sequence ends inside it.
subtermSize :: [Token] -> Maybe Int
subtermSize = go (1 :: Int) 0
  where
    go 0 !k _        = Just k
    go _ _  []       = Nothing
    go n !k (t : ts) = go (n - 1 + tokenArity t) (k + 1) ts

-- | Split off exactly one subterm.
splitSubterm :: [Token] -> Maybe ([Token], [Token])
splitSubterm ts = (\ n -> splitAt n ts) <$> subtermSize ts

-- | Drop @n@ consecutive subterms.
dropSubterms :: Int -> [Token] -> Maybe [Token]
dropSubterms 0 ts = Just ts
dropSubterms n ts = dropSubterms (n - 1) . snd =<< splitSubterm ts

-- | Match a pattern against the front of a candidate sequence.
--
--   A wildcard consumes one whole subterm of the candidate, and the
--   eliminations the metavariable itself carries are skipped on the pattern
--   side -- @_ x y@ is a hole, not an application of one.
--
--   Returns what each wildcard absorbed, left to right.
matchHere :: [Token] -> [Token] -> Maybe [[Token]]
matchHere = go
  where
    go [] _ = Just []
    go (q : qs) cs
      | isWildcard q = do
          (sub, cs') <- splitSubterm cs
          qs'        <- dropSubterms (tokenArity q) qs
          (sub :) <$> go qs' cs'
    go (q : qs) (c : cs)
      | q == c    = go qs cs
    go _ _ = Nothing

-- | Every position in the candidate at which the pattern matches, with what
--   the wildcards absorbed there.
--
--   Every token of a preorder flatterm starts a subterm, so every offset is a
--   position worth trying; matching at offset 0 is matching the whole type.
--   Searching all of them is what makes @_ ⟶* _@ find a lemma whose
--   conclusion is that shape without the pattern having to spell out the
--   telescope in front of it.
matchesIn :: [Token] -> [Token] -> [(Int, [[Token]])]
matchesIn q cs =
  [ (i, binds)
  | (i, suffix) <- zip [0 ..] (tails cs)
  , Just binds  <- [matchHere q suffix]
  ]
