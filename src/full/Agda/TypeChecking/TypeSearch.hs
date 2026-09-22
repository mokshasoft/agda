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
--   rare symbol is worth more.  **That signal does not exist here.** This is
--   exact pattern matching, so every hit contains every symbol of the
--   pattern, and an IDF score over the pattern is one number shared by the
--   whole result set.  It cannot order anything.
--
--   What does discriminate is how much of the hit the pattern accounts for.
--   @_ ⟶* _@ against a lemma whose entire type is @a ⟶* b@ has explained
--   the lemma; against a forty-premise lemma that happens to mention @⟶*@
--   in its ninth hypothesis it has explained almost nothing.  So the primary
--   key is 'hCoverage', the fraction of the candidate's type accounted for by
--   the pattern's concrete structure, and it is exactly what pushes the
--   thousand incidental @Γ ⊢ _ ∷ _@ matches below the handful of real ones.
--
--   Document frequency is still computed, but for the honest purpose: it is
--   reported for each symbol of the /pattern/, so that a query returning two
--   thousand hits says why -- its symbols are ubiquitous -- instead of
--   leaving the user to guess.  See 'Selectivity'.
--
--   == What this cut does not do
--
--   Two things from the design are deliberately absent, and both are
--   describable rather than subtle:
--
--     * /The directional modes/ -- @instance-of@ (\"would this lemma close my
--       goal\") and @generalises@ (\"is my new lemma a special case of
--       something\").  Both need the /candidate's/ own bound variables to be
--       flexible, which is matching under its telescope rather than the
--       wildcard matching done here.  Only the pattern's holes are flexible
--       in this cut.
--     * /The substitution that made it match/.  The wildcards' bindings are
--       recovered as token sequences, and a token sequence cannot be printed
--       as a term: that needs the match repeated on the 'Type' itself for the
--       results actually shown.  The architecture for it is the usual one --
--       cheap filter over flatterms, precise confirmation on the survivors --
--       and 'matchesIn' already returns the bindings it would need.
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
  ( Token (..), flattenType, matchesIn, subtermSize )
import Agda.TypeChecking.Warnings (warning)

---------------------------------------------------------------------------
-- * Elaborating the pattern
---------------------------------------------------------------------------

-- | Parse and elaborate the pattern in the scope of the main module, and
--   return its flatterm.
--
--   The pattern is checked as an ordinary type, which is what makes it agree
--   with the candidates: implicit arguments are inserted on both sides by the
--   same elaborator, so @subTm _ (subTm _ _) ≡ _@ acquires the level and type
--   arguments of @_≡_@ exactly as a definition's type would.  Matching the
--   surface syntax instead would compare two things that are not the same
--   shape.
--
--   Each @_@ becomes a metavariable, which is what a wildcard is (see
--   'isWildcard').  Elaboration is allowed to /solve/ some of them from the
--   others -- in @subTm τ _ ≡ subTm τ _@ the two holes are forced to agree in
--   type -- and that is wanted: it makes the pattern more precise than it was
--   written.
--
--   All of this runs inside 'localTCState'.  Elaborating a pattern creates
--   metavariables and constraints, and none of that may survive into the
--   state of the module being checked, where it would be reported as unsolved.
--   Only the flatterm, which is plain data, comes back out.
elaboratePattern :: TopLevelModuleName -> String -> TCM ([Token], String)
elaboratePattern top str = do
  scope <- getVisitedModule top >>= \case
    Just mi -> pure $ iInsideScope (miInterface mi)
    Nothing -> genericError $
      "--search-type: the scope of " ++ prettyShow top ++ " is not available"
  localTCState $ withScope_ scope $ do
    c <- parseExpr noRange str
    a <- concreteToAbstract_ (c :: C.Expr)
    t <- instantiateFull =<< isType_ (a :: A.Expr)
    -- Printed here, not by the caller: outside this block the pattern's
    -- metavariables are gone with the rest of the discarded state.
    shown <- oneLine . render <$> prettyTCM t
    pure (flattenType t, shown)

---------------------------------------------------------------------------
-- * Candidates
---------------------------------------------------------------------------

-- | A definition the pattern is matched against.
--
--   The flatterm is computed once per definition and kept: it is needed for
--   the match, for the size the coverage is a fraction of, and for the
--   document frequencies.  Nothing is pretty-printed here -- that happens
--   only for the results actually reported.
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
--   so a standard library hit would be noise; a search asks whether the lemma
--   exists at all, and it is just as useful to learn that it is already in a
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
-- * Matching and ranking
---------------------------------------------------------------------------

data Hit = Hit
  { hCand     :: Cand
  , hCoverage :: Double
      -- ^ Fraction of the candidate's type explained by the pattern's
      --   concrete structure.  The ranking key; see the module header.
  , hOffset   :: Int
      -- ^ Where in the candidate's flatterm the match starts.  Zero means
      --   the pattern matched the whole type rather than a part of it.
  , hWhole    :: Bool
  }

-- | Best match of the pattern in a candidate, if any.
--
--   A pattern can match a candidate in more than one place -- @_ ⟶* _@
--   against a lemma with three such premises matches three times.  That is
--   one hit, scored by its best position, rather than three rows saying the
--   same thing.
matchCand :: [Token] -> Cand -> Maybe Hit
matchCand pat c = case matchesIn pat (cdTokens c) of
  []       -> Nothing
  (m : ms) -> Just $ foldl' better (mk m) (map mk ms)
  where
    total = length (cdTokens c)

    mk (off, binds) = Hit
      { hCand     = c
      , hCoverage = coverage off binds
      , hOffset   = off
      , hWhole    = off == 0
      }

    -- The pattern's concrete structure is what it matched minus what its
    -- holes absorbed: a hole explains nothing about the candidate.  Taken as
    -- a fraction of the whole type, so that a pattern which is the entire
    -- statement of a small lemma outranks the same pattern buried in a large
    -- one.
    coverage off binds
      | total == 0 = 0
      | otherwise  =
          fromIntegral (matched - sum (map length binds)) / fromIntegral total
      where
        -- What the pattern consumed: the subterm of the candidate that starts
        -- where the match did.
        matched = maybe 0 id $ subtermSize $ drop off $ cdTokens c

    better a b = if hCoverage b > hCoverage a then b else a

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
  -> Int                -- ^ How many hits to list; @0@ for all.
  -> TCM ()
searchType projectDir top pat outFile format limit = do
  (tokens, patStr) <- elaboratePattern top pat
  defs     <- allDefinitions
  modTable <- moduleFileTable

  let cands = candidates projectDir modTable defs
      hits  = rank [ h | c <- cands, Just h <- [matchCand tokens c] ]
      shown = if limit <= 0 then hits else take limit hits
      sel   = selectivity defs cands tokens

  unless (null hits) $
    warning $ TypeSearchHits TypeSearchReport
      { tsPattern = pat
      , tsHits    = length hits
      , tsShown   = length shown
      , tsFile    = outFile
      }

  withOutputSink outFile $ \ put -> case format of
    ReportJSON -> renderJSON put projectDir pat patStr sel (length hits) shown
    ReportText -> renderText put projectDir pat patStr sel (length hits) shown

  reportSLn "tc.search.type" 10 $
    "Wrote type search report to " ++ outFile ++
    " (" ++ show (length hits) ++ " hits)"

-- | Rank by how much of the hit the pattern explains, then prefer the
--   smaller statement and the smaller proof.  Ties break on the name, so the
--   report is stable under unrelated edits.
rank :: [Hit] -> [Hit]
rank = sortOn $ \ h ->
  ( negate (hCoverage h)
  , length (cdTokens (hCand h))
  , cdBodySize (hCand h)
  , sortKey (hCand h)
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
  , rCoverage :: Double
  , rWhole    :: Bool
  , rExternal :: Bool
  }

mkRow :: FilePath -> Hit -> TCM Row
mkRow projectDir h = do
  ty <- oneLine . render <$> prettyTCM (cdType c)
  pure Row
    { rName     = cdName c
    , rKind     = cdKind c
    , rType     = ty
    , rSource   = relativeTo projectDir <$> cdSource c
    , rRange    = trustedRange projectDir (cdSource c) (cdQName c)
    , rBodySize = cdBodySize c
    , rCoverage = hCoverage h
    , rWhole    = hWhole h
    , rExternal = cdExternal c
    }
  where c = hCand h

pct :: Double -> Int
pct x = round (100 * x)

---------------------------------------------------------------------------
-- * Text rendering
---------------------------------------------------------------------------

renderText
  :: Sink -> FilePath -> String -> String -> [Selectivity] -> Int -> [Hit]
  -> TCM ()
renderText put projectDir pat patStr sel total shown = do
  put $ unlines $ concat
    [ [ "Type search"
      , ""
      , "Pattern:   " ++ pat
      -- Elaboration inserts implicit arguments and may solve some holes from
      -- the others, so what was matched is routinely more precise than what
      -- was typed; a surprising result set is usually explained here.
      , "Elaborated: " ++ patStr
      , "Hits: " ++ show total
          ++ (if length shown < total
                then " (" ++ show (length shown) ++ " listed)" else "")
      , ""
      ]
    , selectivityLines sel
    , [ "  Ranked by how much of each hit the pattern accounts for, so a"
      , "  lemma the pattern nearly is comes before one that merely mentions"
      , "  the shape somewhere.  `body` is the elaborated size of the proof."
      , ""
      ]
    ]
  mapM_ one shown
  where
    one h = do
      r <- mkRow projectDir h
      put $ unlines $ renderRow r

selectivityLines :: [Selectivity] -> [String]
selectivityLines [] = []
selectivityLines sel = concat
  [ [ "  Pattern symbols, and how many types in scope mention each --" ]
  , [ "  a pattern built only from common ones cannot return a short list:" ]
  , [ "" ]
  , [ "    " ++ pad 28 (selSymbol s) ++ show (selDocs s) ++ " types" | s <- sel ]
  , [ "" ]
  ]

renderRow :: Row -> [String]
renderRow r = concat
  [ [ "  " ++ rName r
        ++ (if rExternal r then "  (external)" else "")
        ++ "  [" ++ show (pct (rCoverage r)) ++ "%"
        ++ (if rWhole r then ", whole type" else "")
        ++ ", body " ++ show (rBodySize r) ++ "]" ]
  , [ "    : " ++ rType r ]
  , [ "    " ++ loc | let loc = location r, not (null loc) ]
  , [ "" ]
  ]
  where
    location x
      | not (null (rRange x)) = rRange x
      | otherwise             = maybe "" id (rSource x)

---------------------------------------------------------------------------
-- * JSON rendering
---------------------------------------------------------------------------

renderJSON
  :: Sink -> FilePath -> String -> String -> [Selectivity] -> Int -> [Hit]
  -> TCM ()
renderJSON put projectDir pat patStr sel total shown = do
  put $ unlines $ ("{" :) $ concat
    [ withComma $ jField 1 "pattern" (JStr pat)
    , withComma $ jField 1 "elaborated" (JStr patStr)
    , withComma $ jObjField 1 "counts"
        [ ("hits",   JNum total)
        , ("listed", JNum (length shown))
        ]
    , withComma $ jArrField 1 "patternSymbols"
        [ JObj [ ("symbol", JStr (selSymbol s)), ("types", JNum (selDocs s)) ]
        | s <- sel ]
    ]
  put $ indent 1 ++ jsonString "hits" ++ ": ["
  n <- streamArray put 2 (fmap rowJ . mkRow projectDir) shown
  put $ (if n == 0 then "" else "\n" ++ indent 1) ++ "]\n}\n"

rowJ :: Row -> J
rowJ r = JObj $ concat
  [ [ ("name",     JStr (rName r))
    , ("kind",     JStr (rKind r))
    , ("type",     JStr (rType r))
      -- The ranking key; see the module header on why it is not IDF.
    , ("coverage", JNum (pct (rCoverage r)))
    , ("bodySize", JNum (rBodySize r))
    , ("source",   maybe JNull JStr (rSource r))
    ]
  , [ ("range",     JStr (rRange r)) | not (null (rRange r)) ]
  , [ ("wholeType", JBool True)      | rWhole r    ]
  , [ ("external",  JBool True)      | rExternal r ]
  ]
