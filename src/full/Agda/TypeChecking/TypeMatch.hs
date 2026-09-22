{-# OPTIONS_GHC -Wunused-imports #-}

-- | First-order one-way matching on elaborated types, used by
--   "Agda.TypeChecking.TypeSearch" to confirm a hit and to recover the
--   substitution that produced it.
--
--   The flatterm in "Agda.TypeChecking.TypeKey" is a /filter/: it is fast and
--   it runs against the whole signature, but its tokens have thrown away the
--   tree, so it cannot bind a hole to a 'Term' or tell which binder a
--   variable belongs to.  This module does the same match again on the
--   'Type', where binders are explicit, for the far smaller set of candidates
--   the filter let through.  That split -- cheap over-approximation, precise
--   confirmation -- is the usual shape of a discrimination-tree search.
--
--   == One matcher, two directions
--
--   Matching is always one-way: one side has holes, the other is rigid.
--   Which side that is decides the question being asked.
--
--   [@generalises@] The /pattern/ has the holes -- the @_@ the user typed.
--     A hit is a definition that is an instance of the pattern: /is my new
--     lemma a special case of something?/
--
--   [@instance-of@] The /candidate/ has the holes -- the variables bound by
--     its own telescope.  A hit is a definition whose conclusion can be
--     instantiated to the pattern: /would this lemma close my goal?/
--
--   Both are 'matchWith', differing only in 'Flex'.
--
--   == What is deliberately not attempted
--
--   [Definitional equality.]  Matching is syntactic throughout.  Reducing
--     every candidate would cost more than the search, and the result would
--     depend on how far things happened to unfold.  A lemma about @x + 0@
--     therefore does not match a goal about @x@.
--
--   [Higher-order holes.]  A hole applied to arguments -- @P y@ where @P@ is
--     a telescope variable, as in the conclusion of @subst@ -- is refused
--     rather than guessed at.  Solving it is higher-order unification, where
--     a wrong answer is worse than no answer.  This excludes @subst@,
--     @transport@ and @J@-shaped lemmas from @instance-of@ hits, which is
--     worth knowing in a development full of them.
--
--   [Holes under binders introduced inside the match.]  A hole is bound only
--     at depth zero.  Deeper, it is treated as rigid.  Anything bound under a
--     binder would have to be strengthened out of a scope it may genuinely
--     depend on, and conclusions rarely put their holes under binders, so the
--     conservative reading costs little.
module Agda.TypeChecking.TypeMatch
  ( -- * Flexibility
    Flex (..)
  , queryHoles
  , telescopeHoles
    -- * Matching
  , Binding (..)
  , matchWith
  , matchAnywhere
    -- * Telescopes
  , stripPis
  , stripPisUpTo
  , residualPremises
  ) where

import Control.Monad (guard, zipWithM_)
import Control.Monad.State.Strict (StateT, execStateT, get, modify)
import Control.Monad.Trans (lift)

import qualified Data.Map.Strict as MapS

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.TypeChecking.Telescope (flattenTel)

import Agda.TypeChecking.Substitute () -- 'Subst' instances used by 'raise'
import Agda.TypeChecking.Substitute.Class (Subst, raise)
import Agda.TypeChecking.TypeKey (flattenTerm)

---------------------------------------------------------------------------
-- * Flexibility
---------------------------------------------------------------------------

-- | Which occurrences on the pattern side are holes.
data Flex = Flex
  { flexMetas :: Bool
      -- ^ Are metavariables holes?  They are what an @_@ in a search pattern
      --   elaborates to.
  , flexVars  :: Int
      -- ^ Pattern de Bruijn indices below this are holes, counted at the top
      --   of the pattern.  Used for a candidate's own telescope; @0@ for none.
  , flexHead  :: Bool
      -- ^ May a hole stand at the /head/ of the matched term, rather than
      --   only inside it?
      --
      --   With this off the pattern's outermost symbol has to occur in the
      --   candidate, which is what keeps the search anchored: a lemma whose
      --   conclusion is a bare variable, @(P : Set) -> P@, otherwise matches
      --   every query there is.
  }

-- | The @generalises@ direction: the user's @_@ are the holes.
queryHoles :: Flex
queryHoles = Flex { flexMetas = True, flexVars = 0, flexHead = True }

-- | The @instance-of@ direction: the candidate's own telescope variables are
--   the holes.  Metavariables stay flexible too, so a pattern may still
--   contain @_@.
telescopeHoles :: Int -> Bool -> Flex
telescopeHoles n anchored =
  Flex { flexMetas = True, flexVars = n, flexHead = not anchored }

---------------------------------------------------------------------------
-- * Substitutions
---------------------------------------------------------------------------

-- | What a hole was bound to.
data Binding
  = TelBinding Int Term
    -- ^ A candidate telescope variable, by its de Bruijn index at the top of
    --   the conclusion.  Telescope position @p@ of an @n@-entry telescope is
    --   index @n - 1 - p@.
  | HoleBinding Int Term
    -- ^ The @n@-th @_@ of the pattern.  Metavariables are numbered in
    --   allocation order, which is the order they were written in.

-- | Holes are keyed by metavariable or by telescope index; the two cannot
--   collide because a given match has at most one kind of variable hole.
data HoleId = HMeta MetaId | HVar Int
  deriving (Eq, Ord)

type Sub = MapS.Map HoleId Term

type M = StateT Sub Maybe

---------------------------------------------------------------------------
-- * Matching
---------------------------------------------------------------------------

-- | Match a pattern against a term, returning what the holes were bound to.
--
--   The bindings come back in hole order, which for @instance-of@ is the
--   order of the candidate's telescope -- the order its arguments are
--   written in.
matchWith :: Flex -> Term -> Term -> Maybe [Binding]
matchWith f pat t = toBindings <$> execStateT (matchTm f True 0 pat t) MapS.empty

toBindings :: Sub -> [Binding]
toBindings sub = tels ++ holes
  where
    entries = MapS.toAscList sub
    tels    = [ TelBinding i v | (HVar i, v) <- entries ]
    -- Numbered by their own order, not by their position among all bindings.
    holes   = [ HoleBinding n v
              | (n, v) <- zip [0 ..] [ v | (HMeta _, v) <- entries ] ]

-- | Every subterm of the type at which the pattern matches.
--
--   Used for the @generalises@ direction, where the pattern may describe the
--   conclusion of a lemma, one of its premises, or a fragment of either.
matchAnywhere :: Flex -> Term -> Type -> [[Binding]]
matchAnywhere f pat = goTy
  where
    goTy t = goTm (unEl t)

    goTm t = here t ++ inside t

    here t = maybe [] (: []) (matchWith f pat t)

    inside = \case
      Var _ es   -> concatMap goElim es
      Def _ es   -> concatMap goElim es
      Con _ _ es -> concatMap goElim es
      MetaV _ es -> concatMap goElim es
      Dummy _ es -> concatMap goElim es
      Lam _ b    -> goTm (absBody' b)
      Pi dom b   -> goTy (unDom dom) ++ goTy (absBody' b)
      DontCare v -> goTm v
      Sort{}     -> []
      Level{}    -> []
      Lit{}      -> []

    goElim = \case
      Apply a      -> goTm (unArg a)
      Proj{}       -> []
      IApply x y r -> goTm x ++ goTm y ++ goTm r

-- | 'Abs' and 'NoAbs' describe the same binder but number their bodies
--   differently; expanding the pseudo-binder makes the two agree, exactly as
--   'Agda.TypeChecking.TypeKey.flattenType' does.
absBody' :: Subst a => Abs a -> a
absBody' = \case
  Abs   _ a -> a
  NoAbs _ a -> raise 1 a

---------------------------------------------------------------------------

-- | @matchTm f atHead d pat t@ matches at binder depth @d@.
matchTm :: Flex -> Bool -> Int -> Term -> Term -> M ()
matchTm f atHead d pat t = case pat of
  -- A hole, if this side is flexible here.  Holes bind only at depth zero
  -- and only unapplied; see the module header.
  MetaV m [] | flexMetas f, d == 0, allowed -> bind (HMeta m) t
  Var i [] | isTelescopeHole i, d == 0, allowed -> bind (HVar (i - d)) t
  _ -> rigid
  where
    allowed = atHead <= flexHead f   -- False only when at the head and anchored

    isTelescopeHole i = i >= d && i - d < flexVars f

    -- Anything that is not a hole must agree structurally.  Descending into
    -- an argument means we are no longer at the head, so the anchoring
    -- restriction stops applying.
    rigid = case (pat, t) of
      (Var i es, Var j es')
        | i == j                          -> matchElims f d es es'
      (Def q es, Def q' es')
        | q == q'                         -> matchElims f d es es'
      (Con c _ es, Con c' _ es')
        | conName c == conName c'         -> matchElims f d es es'
      (MetaV m es, MetaV m' es')
        | m == m'                         -> matchElims f d es es'
      (Dummy s es, Dummy s' es')
        | s == s'                         -> matchElims f d es es'
      (Lit l, Lit l')                     -> guard (l == l')
      (Lam ai b, Lam ai' b')              -> do
        guard (getHiding ai == getHiding ai')
        matchTm f False (d + 1) (absBody' b) (absBody' b')
      (Pi dom b, Pi dom' b')              -> do
        guard (getHiding dom == getHiding dom')
        matchTm f False d (unEl (unDom dom)) (unEl (unDom dom'))
        matchTm f False (d + 1) (unEl (absBody' b)) (unEl (absBody' b'))
      (DontCare v, DontCare v')           -> matchTm f False d v v'
      -- Sorts and levels are compared whole.  A hole inside a universe level
      -- is never what a search is about, and admitting one would make the
      -- match depend on how a level expression happened to be normalised.
      (Sort{}, Sort{})                    -> same
      (Level{}, Level{})                  -> same
      _                                   -> lift Nothing

    same = guard (flattenTerm pat == flattenTerm t)

matchElims :: Flex -> Int -> Elims -> Elims -> M ()
matchElims f d es es' = do
  guard (length es == length es')
  zipWithM_ (matchElim f d) es es'

matchElim :: Flex -> Int -> Elim -> Elim -> M ()
matchElim f d e e' = case (e, e') of
  (Apply a, Apply a') -> do
    guard (getHiding a == getHiding a')
    matchTm f False d (unArg a) (unArg a')
  (Proj _ q, Proj _ q') -> guard (q == q')
  (IApply x y r, IApply x' y' r') -> do
    matchTm f False d x x'
    matchTm f False d y y'
    matchTm f False d r r'
  _ -> lift Nothing

-- | Bind a hole, or check it agrees with what it was bound to before.
--
--   The consistency check is what stops @x ≡ x@ matching @zero ≡ suc zero@.
bind :: HoleId -> Term -> M ()
bind h t = do
  sub <- get
  case MapS.lookup h sub of
    Nothing -> modify (MapS.insert h t)
    Just u  -> guard (flattenTerm u == flattenTerm t)

---------------------------------------------------------------------------
-- * Telescopes
---------------------------------------------------------------------------

-- | Strip the outer function types, returning the telescope and the
--   conclusion.
--
--   Syntactic, with no reduction: the search is syntactic throughout, and
--   reducing every type in the signature would cost more than the search it
--   is meant to serve.
stripPis :: Type -> (Telescope, Type)
stripPis = stripPisUpTo maxBound

-- | Strip at most @n@ of them.
--
--   Searching every prefix is what lets a lemma answer a goal that is itself
--   a function type: @f : Nat -> Nat -> Nat@ closes a goal @Nat -> Nat ->
--   Nat@ by being applied to nothing at all, and closes @Nat@ by being
--   applied to two arguments.  Stripping only the full telescope would see
--   the second and miss the first.
stripPisUpTo :: Int -> Type -> (Telescope, Type)
stripPisUpTo = go
  where
    go n t | n <= 0 = (EmptyTel, t)
    go n t = case unEl t of
      Pi dom b ->
        let name         = absName b
            (tel, concl) = go (n - 1) (absBody' b)
        in  (ExtendTel dom (Abs name tel), concl)
      _ -> (EmptyTel, t)

-- | The telescope entries a match left undetermined: what still has to be
--   supplied to actually use the lemma.
--
--   Matching a conclusion says the lemma /applies/, not that it /closes/
--   anything -- a lemma with three unproven premises matches just as
--   readily as one with none.  Reporting what is left turns a bare hit into
--   the bill for taking it, and it is free: the telescope and the
--   substitution are both already in hand.
--
--   Entries are returned outermost first, each with its own name, paired with
--   whether the match determined it.  Their types are stated in the
--   telescope's own context, so they must be printed under it.
residualPremises :: Telescope -> [Binding] -> [(ArgName, Dom Type, Bool)]
residualPremises tel bs =
  [ (name, dom, (n - 1 - p) `elem` bound)
  | (p, (name, dom)) <- zip [0 ..] (zip names doms)
  ]
  where
    names = [ fst (unDom d) | d <- telToList tel ]
    -- 'flattenTel' raises every entry into the context of the whole
    -- telescope, which is the context they will be printed under.  The types
    -- from 'telToList' each live in the context of the entries before them,
    -- so printing those under the full telescope would misread their indices.
    doms  = flattenTel tel
    n     = length names
    bound = [ i | TelBinding i _ <- bs ]
