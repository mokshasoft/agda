{-# OPTIONS_GHC -Wunused-imports #-}

-- | Search the signature for definitions whose type matches a /pattern/,
--   with @_@ standing for any subterm:
--
-- > agda --search-type='subTm _ (subTm _ _) ≡ _' Everything.agda
-- > agda --search-type='_ ⟶* _'                  Everything.agda
--
--   This is the query Agda did not have.  It can find a definition by name
--   ('Agda.Interaction.SearchAbout', which matches names /mentioned in/ a
--   type) and it can synthesise a term for a goal (Mimer), but not answer
--   the question in between: /which definitions have this shape?/  Coq has
--   @SearchPattern@, Lean @exact?@ and Loogle, Isabelle @find_theorems@,
--   Haskell Hoogle.
--
--   The workflow it replaces is grep.  Grep is keyed on a name over one
--   file, so it answers \"is there something called @tower@ in @Lib/Wk.agda@\"
--   -- and the way a duplicate lemma actually gets written is with the right
--   name prefix and the wrong module.  A query keyed on /shape over
--   everything in scope/ does not care where the lemma lives or what it is
--   called.
--
--   == Two questions, reported apart
--
--   The pattern is matched in both directions.  They answer different
--   questions, and one ranking over both would be comparing things that are
--   not comparable, so they are listed as separate sections.
--
--   [@generalises@] Definitions that are an instance of the pattern: the
--     pattern's @_@ are the holes.  /Is my new lemma a special case of
--     something?/  Matched at any subterm, so a pattern finds a lemma whose
--     conclusion has that shape without spelling out the telescope in front
--     of it.
--
--   [@instance-of@] Definitions whose conclusion instantiates to the
--     pattern: the candidate's own telescope variables are the holes.
--     /Would this lemma close my goal?/  Matched against the conclusion
--     only, because that is what the question is about.
--
--   An @instance-of@ hit reports what the match left undetermined, under
--   @needs@.  Matching a conclusion says the lemma /applies/, not that it
--   /closes/ anything: a lemma with three unproven premises matches as
--   readily as one with none, and the difference is the whole cost of taking
--   it.  See 'Agda.TypeChecking.TypeMatch.residualPremises'.
--
--   == Ranking, and where it differs from the obvious plan
--
--   Ranking is not optional.  In a dependently typed development the
--   interesting patterns are also the most common ones: @Γ ⊢ _ ∷ _@ matches
--   every typing derivation in the project.  A tool that returns those
--   unranked is unusable, and the fix is to /rank/ rather than to filter,
--   since no filter can know which hit the user wanted.
--
--   The obvious plan is inverse document frequency over the pattern's head
--   symbols, which is what rescues a /similarity/ search: there, two hits
--   share different subsets of the query's symbols, and the one sharing a
--   rare symbol is worth more.  That signal does not exist here.  This is
--   exact matching, so every hit contains every symbol of the pattern, and
--   an IDF score over the pattern is one number shared by the whole result
--   set.  It cannot order anything.
--
--   What discriminates depends on the direction:
--
--     * @generalises@ ranks on coverage, the fraction of the candidate's
--       type accounted for by the pattern's concrete structure.  @_ ⟶* _@
--       against a lemma whose entire type is @a ⟶* b@ has explained the
--       lemma; against a forty-premise lemma mentioning @⟶*@ in its ninth
--       hypothesis it has explained almost nothing.
--     * @instance-of@ ranks on what is left to do -- fewest undetermined
--       premises first, then the tightest instantiation.  Coverage reads
--       backwards here, since such a hit is by construction /more general/
--       than the pattern, so coverage would measure its generality rather
--       than its fit.
--
--   Document frequency is still computed, for the honest purpose: it is
--   reported per symbol of the /pattern/, so that a query returning two
--   thousand hits says why -- its symbols are ubiquitous -- instead of
--   leaving the user to guess.  See 'Selectivity'.
module Agda.TypeChecking.TypeSearch
  ( searchType
  ) where

import Control.Monad (unless)

import Data.List (sortOn, foldl')
import qualified Data.HashMap.Strict as HMap
import qualified Data.Map.Strict as MapS
import qualified Data.Set as Set

import Agda.Syntax.Common
import Agda.Syntax.Common.Pretty (prettyShow, render)
import Agda.Syntax.Internal
import Agda.Syntax.Position (noRange)
import Agda.Syntax.TopLevelModuleName (TopLevelModuleName)
import qualified Agda.Syntax.Abstract as A
import qualified Agda.Syntax.Concrete as C

import Agda.Interaction.BasicOps (parseExpr)
import Agda.Interaction.Options.Types (ReportFormat (..))
import Agda.Syntax.Translation.ConcreteToAbstract (concreteToAbstract_)

import Agda.TypeChecking.AnalysisOutput
import Agda.TypeChecking.DeadCode
  ( ModuleFileTable, moduleFileTable, sourceOfQName, pathInProject
  , allDefinitions )
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Pretty (prettyTCM)
import Agda.TypeChecking.Reduce (instantiateFull)
import Agda.TypeChecking.Rules.Term (isType_)
import Agda.TypeChecking.TypeKey
  ( Token (..), flattenTerm, flattenType, matchesIn, subtermSize )
import Agda.TypeChecking.TypeMatch
  ( Binding (..), matchWith, queryHoles, residualPremises, stripPis
  , stripPisUpTo, telescopeHoles )
import Agda.TypeChecking.Warnings (warning)

---------------------------------------------------------------------------
-- * Elaborating the pattern
---------------------------------------------------------------------------

-- | Parse and elaborate the pattern in the scope of the main module.
--
--   The pattern is checked as an ordinary type, which is what makes it agree
--   with the candidates: implicit arguments are inserted on both sides by the
--   same elaborator, so @subTm _ (subTm _ _) ≡ _@ acquires the level and type
--   arguments of @_≡_@ exactly as a definition's type would.  Matching the
--   surface syntax instead would compare two things that are not the same
--   shape.
--
--   Each @_@ becomes a metavariable, which is what a hole is.  Elaboration is
--   allowed to /solve/ some of them from the others -- in @subTm τ _ ≡ subTm
--   τ _@ the two holes are forced to agree in type -- and that is wanted: it
--   makes the pattern more precise than it was written, which is why the
--   report prints the elaborated form.
elaboratePattern :: String -> TCM (Type, String)
elaboratePattern str = do
  c <- parseExpr noRange str
  a <- concreteToAbstract_ (c :: C.Expr)
  t <- instantiateFull =<< isType_ (a :: A.Expr)
  shown <- oneLine . render <$> prettyTCM t
  pure (t, shown)

---------------------------------------------------------------------------
-- * Candidates
---------------------------------------------------------------------------

-- | A definition the pattern is matched against.
--
--   The flatterm is computed once per definition and kept: it is needed for
--   the filter, for the size coverage is a fraction of, and for the document
--   frequencies.  Nothing is pretty-printed here -- that happens only for
--   the results actually reported.
data Cand = Cand
  { cdQName    :: QName
  , cdName     :: String
  , cdSource   :: Maybe FilePath
  , cdExternal :: Bool
  , cdKind     :: String
  , cdBodySize :: Int
  , cdTokens   :: [Token]
  , cdType     :: Type
  }

-- | Everything in the signature, the project and what it imports alike.
--
--   Unlike @--dead-code@ and @--duplicate-types@ this is deliberately /not/
--   restricted to the project.  Those report things the reader might change,
--   so a library hit would be noise; a search asks whether the lemma exists
--   at all, and it is just as useful to learn that it is already in a
--   library.  External hits are marked, not dropped.
candidates :: FilePath -> ModuleFileTable -> Definitions -> [Cand]
candidates projectDir modTable defs = sortOn sortKey
  [ Cand
      { cdQName    = x
      , cdName     = prettyShow x
      , cdSource   = msrc
      , cdExternal = maybe True (not . pathInProject projectDir) msrc
      , cdKind     = defKind (theDef d)
      , cdBodySize = bodySize d
      , cdTokens   = flattenType (defType d)
      , cdType     = defType d
      }
  | (x, d) <- HMap.toList defs
  , not (isGeneratedDefn d)
  , let msrc = sourceOfQName modTable x
  ]

-- | Size of a definition's elaborated body, in internal-syntax nodes.
--
--   Reported beside every hit.  Two lemmas with the same statement are
--   different propositions to a user if one elaborates to a term ten times
--   the size of the other, and in a language where memory is the binding
--   constraint that is often the column that decides which one to call.
bodySize :: Definition -> Int
bodySize d = case theDef d of
  Function{ funClauses   = cs } -> clausesSize cs
  Primitive{ primClauses = cs } -> clausesSize cs
  _ -> 0
  where
    clausesSize cs = sum [ termSize b | c <- cs, Just b <- [clauseBody c] ]

-- | Stable order; see the note in "Agda.TypeChecking.ASTDump".
sortKey :: Cand -> (String, Maybe FilePath, NameId)
sortKey c = (cdName c, cdSource c, nameId (qnameName (cdQName c)))

---------------------------------------------------------------------------
-- * The generalises direction
---------------------------------------------------------------------------

data Hit = Hit
  { hCand     :: Cand
  , hCoverage :: Double
  , hWhole    :: Bool
  }

-- | Best match of the pattern in a candidate, if any.
--
--   A pattern can match a candidate in more than one place -- @_ ⟶* _@
--   against a lemma with three such premises matches three times.  That is
--   one hit, scored by its best position, rather than three rows saying the
--   same thing.
matchGen :: [Token] -> Cand -> Maybe Hit
matchGen pat c = case matchesIn pat (cdTokens c) of
  []       -> Nothing
  (m : ms) -> Just $ foldl' better (mk m) (map mk ms)
  where
    total = length (cdTokens c)

    mk (off, binds) = Hit
      { hCand     = c
      , hCoverage = coverage off binds
      , hWhole    = off == 0
      }

    -- The pattern's concrete structure is what it matched minus what its
    -- holes absorbed: a hole explains nothing about the candidate.
    coverage off binds
      | total == 0 = 0
      | otherwise  =
          fromIntegral (matched - sum (map length binds)) / fromIntegral total
      where
        matched = maybe 0 id $ subtermSize $ drop off $ cdTokens c

    better a b = if hCoverage b > hCoverage a then b else a

---------------------------------------------------------------------------
-- * The instance-of direction
---------------------------------------------------------------------------

data Inst = Inst
  { iCand       :: Cand
  , iTel        :: Telescope
  , iBinds      :: [Binding]
  , iUnresolved :: Int
      -- ^ Telescope entries the match did not determine: what would still
      --   have to be supplied.  The primary ranking key.
  , iSubSize    :: Int
      -- ^ Total size of the instantiation.  A lemma that /is/ the pattern
      --   beats one bent a long way to reach it.
  }

-- | Does the candidate instantiate to the pattern, after being applied to
--   some prefix of its arguments?
--
--   Every prefix is tried, not just the full telescope.  A lemma
--   @f : Nat -> Nat -> Nat@ closes a goal @Nat -> Nat -> Nat@ by taking no
--   arguments at all and a goal @Nat@ by taking two; stripping only the whole
--   telescope would find the second and silently miss the first, which is the
--   commoner question.  The best prefix wins -- the one leaving least to do.
matchInst :: Bool -> Term -> Cand -> Maybe Inst
matchInst anchored patTm c =
  case [ i | k <- [0 .. nMax], Just i <- [tryAt k] ] of
    []       -> Nothing
    (i : is) -> Just (foldl' tighter i is)
  where
    nMax = length (telToList (fst (stripPis (cdType c))))

    tighter a b = if instKey b < instKey a then b else a

    tryAt k
      | not (headCompatible anchored patTm (unEl rest)) = Nothing
      | otherwise = do
          binds <- matchWith (telescopeHoles k anchored) (unEl rest) patTm
          let residual = residualPremises tel binds
          pure Inst
            { iCand       = c
            , iTel        = tel
            , iBinds      = binds
            , iUnresolved = length [ () | (_, _, False) <- residual ]
            , iSubSize    =
                sum [ length (flattenTerm t) | TelBinding _ t <- binds ]
            }
      where
        (tel, rest) = stripPisUpTo k (cdType c)

-- | Cheap rejection before the real match: the pattern's head symbol has to
--   occur as the candidate's conclusion head.
--
--   Sound only because a hole may not stand at the head when anchored.  When
--   it may, a variable-headed conclusion has to be let through -- and that is
--   exactly the case that matches everything, which is why anchoring is the
--   default.
headCompatible :: Bool -> Term -> Term -> Bool
headCompatible anchored q concl = case headSym concl of
  Just b  -> maybe True (== b) (headSym q)
  Nothing -> case concl of
    -- Structural: not a head a hole could stand at, so let the matcher decide.
    Pi{}   -> True
    Sort{} -> True
    Lam{}  -> True
    -- A variable or metavariable at the head: the case anchoring exists for.
    _      -> not anchored

headSym :: Term -> Maybe NameId
headSym = \case
  Def q _   -> Just (nameId (qnameName q))
  Con c _ _ -> Just (nameId (qnameName (conName c)))
  _         -> Nothing

---------------------------------------------------------------------------
-- * Selectivity
---------------------------------------------------------------------------

-- | How discriminating the pattern is, per symbol: in how many of the
--   candidate types each of its constants occurs.
--
--   This is the reportable half of inverse document frequency.  It does not
--   order the results -- every hit contains every symbol of the pattern, so
--   there is nothing to order by -- but it is what explains a result set:
--   a pattern whose rarest symbol occurs in two thousand types was never
--   going to return a short list, and the user can see that and add a
--   symbol.
data Selectivity = Selectivity
  { selSymbol :: String
  , selDocs   :: Int
  }

selectivity :: Definitions -> [Cand] -> [Token] -> [Selectivity]
selectivity defs cands pat = sortOn selDocs
  [ Selectivity (nameOf n) (MapS.findWithDefault 0 n dfs)
  | n <- Set.toList (namesOfPattern pat)
  ]
  where
    dfs = MapS.fromListWith (+)
      [ (n, 1 :: Int) | c <- cands, n <- Set.toList (namesOfPattern (cdTokens c)) ]

    -- The flatterm keeps 'NameId's, which are what the match compares; the
    -- printable name has to come back from the signature.
    byId = HMap.fromList
      [ (nameId (qnameName x), prettyShow x) | x <- HMap.keys defs ]
    nameOf n = HMap.lookupDefault "?" n byId

namesOfPattern :: [Token] -> Set.Set NameId
namesOfPattern = Set.fromList . concatMap f
  where
    f = \case
      TDef  n _ -> [n]
      TCon  n _ -> [n]
      TProj n   -> [n]
      TDefS n _ -> [n]
      _         -> []

---------------------------------------------------------------------------
-- * Entry point
---------------------------------------------------------------------------

-- | Match a pattern against every type in the signature and write the
--   ranked hits out.
searchType
  :: FilePath           -- ^ Project directory.
  -> TopLevelModuleName -- ^ Main module, whose scope the pattern is read in.
  -> String             -- ^ The pattern.
  -> FilePath           -- ^ Where the report goes.
  -> ReportFormat
  -> Int                -- ^ How many hits to list per direction; @0@ for all.
  -> Bool               -- ^ Anchor on the head symbol?
  -> TCM ()
searchType projectDir top pat outFile format limit anchored = do
  scope <- getVisitedModule top >>= \case
    Just mi -> pure $ iInsideScope (miInterface mi)
    Nothing -> genericError $
      "--search-type: the scope of " ++ prettyShow top ++ " is not available"

  -- Everything happens inside 'localTCState'.  Elaborating a pattern creates
  -- metavariables and constraints, and none of that may survive into the
  -- state of the module being checked, where it would be reported as
  -- unsolved.  Rendering has to print terms that mention those metavariables,
  -- so it runs inside too, and only the counts -- plain data -- come back
  -- out.  The warning is raised afterwards: one raised inside would be rolled
  -- back with the rest of the state.
  (nGen, nGenShown, nInst, nInstShown) <-
    localTCState $ withScope_ scope $ do
      (patTy, patStr) <- elaboratePattern pat
      defs     <- allDefinitions
      modTable <- moduleFileTable

      let patToks = flattenType patTy
          patTm   = unEl patTy
          cands   = candidates projectDir modTable defs

          gens  = sortOn genKey  [ h | c <- cands, Just h <- [matchGen patToks c] ]
          insts = sortOn instKey [ i | c <- cands, Just i <- [matchInst anchored patTm c] ]

          shownG = cutTo limit gens
          shownI = cutTo limit insts
          sel    = selectivity defs cands patToks

      withOutputSink outFile $ \ put -> case format of
        ReportText ->
          renderText put projectDir pat patStr patTy sel
            (length gens) shownG (length insts) shownI
        ReportJSON ->
          renderJSON put projectDir pat patStr patTy sel
            (length gens) shownG (length insts) shownI

      pure (length gens, length shownG, length insts, length shownI)

  unless (nGen == 0 && nInst == 0) $
    warning $ TypeSearchHits TypeSearchReport
      { tsPattern   = pat
      , tsHits      = nGen
      , tsShown     = nGenShown
      , tsInstHits  = nInst
      , tsInstShown = nInstShown
      , tsFile      = outFile
      }

  reportSLn "tc.search.type" 10 $
    "Wrote type search report to " ++ outFile ++
    " (" ++ show nGen ++ " generalises, " ++ show nInst ++ " instance-of)"

-- | @--search-limit@; @0@ means everything.  A top-level definition rather
--   than a local one because it is used at two result types.
cutTo :: Int -> [a] -> [a]
cutTo n xs
  | n <= 0    = xs
  | otherwise = take n xs

-- | Most of the candidate explained first, then the smaller statement and
--   the smaller proof.  Ties break on the name, so the report is stable
--   under unrelated edits.
genKey :: Hit -> (Double, Int, Int, (String, Maybe FilePath, NameId))
genKey h =
  ( negate (hCoverage h)
  , length (cdTokens (hCand h))
  , cdBodySize (hCand h)
  , sortKey (hCand h)
  )

-- | Least left to do first, then the tightest instantiation.
instKey :: Inst -> (Int, Int, Int, (String, Maybe FilePath, NameId))
instKey i =
  ( iUnresolved i
  , iSubSize i
  , cdBodySize (iCand i)
  , sortKey (iCand i)
  )

---------------------------------------------------------------------------
-- * Rendered hits
---------------------------------------------------------------------------

data Row = Row
  { rName     :: String
  , rKind     :: String
  , rType     :: String
  , rSource   :: Maybe FilePath
  , rRange    :: String
  , rBodySize :: Int
  , rExternal :: Bool
  , rCoverage :: Maybe Double
  , rWhole    :: Bool
  , rSubst    :: [String]
      -- ^ What the holes were bound to, as @name := term@.
  , rResidual :: [String]
      -- ^ Telescope entries the match did not determine.
  }

baseRow :: FilePath -> Cand -> TCM Row
baseRow projectDir c = do
  ty <- oneLine . render <$> prettyTCM (cdType c)
  pure Row
    { rName     = cdName c
    , rKind     = cdKind c
    , rType     = ty
    , rSource   = relativeTo projectDir <$> cdSource c
    , rRange    = trustedRange projectDir (cdSource c) (cdQName c)
    , rBodySize = cdBodySize c
    , rExternal = cdExternal c
    , rCoverage = Nothing
    , rWhole    = False
    , rSubst    = []
    , rResidual = []
    }

-- | A @generalises@ hit.
--
--   The substitution is recovered by matching again on the 'Type', where
--   binders are explicit: the flatterm cannot produce a 'Term'.  It is shown
--   only when the pattern matches the conclusion, where the bound terms live
--   in exactly the telescope's context and can be printed correctly.  A match
--   buried deeper is still reported, just without its substitution -- the
--   alternative is printing terms against the wrong context, which would be
--   worse than printing nothing.
genRow :: FilePath -> Type -> Hit -> TCM Row
genRow projectDir patTy h = do
  r <- baseRow projectDir (hCand h)
  let (tel, concl) = stripPis (cdType (hCand h))
  sub <- case matchWith queryHoles (unEl patTy) (unEl concl) of
    Nothing -> pure []
    Just bs -> addContext tel $ mapM showHole [ b | b@HoleBinding{} <- bs ]
  pure r { rCoverage = Just (hCoverage h)
         , rWhole    = hWhole h
         , rSubst    = sub
         }

showHole :: Binding -> TCM String
showHole = \case
  HoleBinding n t -> do
    d <- oneLine . render <$> prettyTCM t
    pure $ "_" ++ show (n + 1 :: Int) ++ " := " ++ d
  TelBinding n t -> do
    d <- oneLine . render <$> prettyTCM t
    pure $ "@" ++ show n ++ " := " ++ d

-- | An @instance-of@ hit, with the instantiation and what it left open.
--
--   The bound terms come from the /pattern/, which is closed, so they print
--   without a context.  The residual premises come from the candidate's
--   telescope and must be printed under it, or their variables would read as
--   the wrong binders.
instRow :: FilePath -> Inst -> TCM Row
instRow projectDir i = do
  r <- baseRow projectDir (iCand i)
  let tel      = iTel i
      residual = residualPremises tel (iBinds i)
      names    = [ n | (n, _, _) <- residual ]
      n'       = length names
  sub <- sequence
    [ do d <- oneLine . render <$> prettyTCM t
         pure $ nameAt names n' ix ++ " := " ++ d
    | TelBinding ix t <- iBinds i
    ]
  left <- addContext tel $ sequence
    [ do d <- oneLine . render <$> prettyTCM (unDom dom)
         pure $ wrap dom (n ++ " : " ++ d)
    | (n, dom, False) <- residual
    ]
  pure r { rSubst = sub, rResidual = left }
  where
    -- Telescope position p has de Bruijn index n - 1 - p at the conclusion.
    nameAt names n' ix =
      let p = n' - 1 - ix
      in  if p >= 0 && p < length names then names !! p else "?"

    wrap dom s = case getHiding dom of
      Hidden     -> "{" ++ s ++ "}"
      Instance{} -> "⦃ " ++ s ++ " ⦄"
      NotHidden  -> "(" ++ s ++ ")"

pct :: Double -> Int
pct x = round (100 * x)

---------------------------------------------------------------------------
-- * Text rendering
---------------------------------------------------------------------------

renderText
  :: Sink -> FilePath -> String -> String -> Type -> [Selectivity]
  -> Int -> [Hit] -> Int -> [Inst] -> TCM ()
renderText put projectDir pat patStr patTy sel nGen shownG nInst shownI = do
  put $ unlines $ concat
    [ [ "Type search"
      , ""
      , "Pattern:    " ++ pat
      -- Elaboration inserts implicit arguments and may solve some holes from
      -- the others, so what was matched is routinely more precise than what
      -- was typed; a surprising result set is usually explained here.
      , "Elaborated: " ++ patStr
      , ""
      ]
    , selectivityLines sel
    ]
  heading "AN INSTANCE OF THE PATTERN (generalises)" nGen (length shownG)
    [ "  Is my new lemma a special case of something?  Ranked by how much of"
    , "  each hit the pattern accounts for."
    ]
  mapM_ (\ h -> putRow =<< genRow projectDir patTy h) shownG
  heading "CONCLUSION FITS THE PATTERN (instance-of)" nInst (length shownI)
    [ "  Would this lemma close my goal?  Ranked by how little is left to do."
    , "  `needs` is what the match did not determine -- matching a conclusion"
    , "  says the lemma applies, not that it closes anything."
    ]
  mapM_ (\ i -> putRow =<< instRow projectDir i) shownI
  where
    putRow r = put $ unlines $ renderRow r

    heading title total listed blurb = put $ unlines $ concat
      [ [ "== " ++ title ++ " ==", "" ]
      , [ "  " ++ show total ++ " hit" ++ (if total == 1 then "" else "s")
            ++ (if listed < total
                  then " (" ++ show listed ++ " listed)" else "")
        , "" ]
      , if total == 0 then [] else blurb ++ [ "" ]
      ]

selectivityLines :: [Selectivity] -> [String]
selectivityLines [] = []
selectivityLines sel = concat
  [ [ "  Pattern symbols, and how many types in scope mention each --"
    , "  a pattern built only from common ones cannot return a short list:"
    , "" ]
  , [ "    " ++ pad 28 (selSymbol s) ++ show (selDocs s) ++ " types" | s <- sel ]
  , [ "" ]
  ]

renderRow :: Row -> [String]
renderRow r = concat
  [ [ "  " ++ rName r ++ (if rExternal r then "  (external)" else "") ++ tags ]
  , [ "    : " ++ rType r ]
  , [ "    with " ++ joinCommas (rSubst r)    | not (null (rSubst r))    ]
  , [ "    needs " ++ joinCommas (rResidual r) | not (null (rResidual r)) ]
  , [ "    " ++ loc | let loc = location r, not (null loc) ]
  , [ "" ]
  ]
  where
    tags = "  [" ++ joinCommas (concat
      [ [ show (pct cv) ++ "%" | Just cv <- [rCoverage r] ]
      , [ "whole type" | rWhole r ]
      , [ "body " ++ show (rBodySize r) ]
      ]) ++ "]"
    location x
      | not (null (rRange x)) = rRange x
      | otherwise             = maybe "" id (rSource x)

---------------------------------------------------------------------------
-- * JSON rendering
---------------------------------------------------------------------------

renderJSON
  :: Sink -> FilePath -> String -> String -> Type -> [Selectivity]
  -> Int -> [Hit] -> Int -> [Inst] -> TCM ()
renderJSON put projectDir pat patStr patTy sel nGen shownG nInst shownI = do
  put $ unlines $ ("{" :) $ concat
    [ withComma $ jField 1 "pattern" (JStr pat)
    , withComma $ jField 1 "elaborated" (JStr patStr)
    , withComma $ jObjField 1 "counts"
        [ ("generalises",       JNum nGen)
        , ("generalisesListed", JNum (length shownG))
        , ("instanceOf",        JNum nInst)
        , ("instanceOfListed",  JNum (length shownI))
        ]
    , withComma $ jArrField 1 "patternSymbols"
        [ JObj [ ("symbol", JStr (selSymbol s)), ("types", JNum (selDocs s)) ]
        | s <- sel ]
    ]
  jsonArray put "generalises" (genRow projectDir patTy) shownG
  put ",\n"
  jsonArray put "instanceOf" (instRow projectDir) shownI
  put "\n}\n"

-- | One JSON array of rendered rows, streamed so a row is built only when it
--   is about to be written.  Top level, since it serves both directions.
jsonArray :: Sink -> String -> (a -> TCM Row) -> [a] -> TCM ()
jsonArray put k mk xs = do
  put $ indent 1 ++ jsonString k ++ ": ["
  n <- streamArray put 2 (fmap rowJ . mk) xs
  put $ (if n == 0 then "" else "\n" ++ indent 1) ++ "]"

rowJ :: Row -> J
rowJ r = JObj $ concat
  [ [ ("name",     JStr (rName r))
    , ("kind",     JStr (rKind r))
    , ("type",     JStr (rType r))
    , ("bodySize", JNum (rBodySize r))
    , ("source",   maybe JNull JStr (rSource r))
    ]
  , [ ("coverage",  JNum (pct cv))   | Just cv <- [rCoverage r] ]
  , [ ("range",     JStr (rRange r)) | not (null (rRange r)) ]
  , [ ("wholeType", JBool True)      | rWhole r    ]
  , [ ("external",  JBool True)      | rExternal r ]
  , [ ("with",  JArr (map JStr (rSubst r)))    | not (null (rSubst r))    ]
  , [ ("needs", JArr (map JStr (rResidual r))) | not (null (rResidual r)) ]
  ]
