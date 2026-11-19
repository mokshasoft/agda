{-# OPTIONS_GHC -Wunused-imports #-}

-- | @--repair-reexports=M:LINE,…@: remove a @public@ re-export, and make
--   every importer import what it used through it itself.
--
--   A target is the @open … public@ statement at a line of module @M@ (the
--   FACADE): either @open import X … public@ (a top-level module) or
--   @open N … public@ (a submodule of the facade, e.g. a record module).
--   While each importer is checked, the lineage of every name it resolves
--   says whether the name came through the target: some hop of it is the
--   target's module @X@/@N@ as written, right after the hop that brought the
--   facade (the importer's own statement on @M@, a chain module that
--   re-exports @M@, or a qualifier denoting @M@).  The repair, per importer:
--
--   * an unqualified use through its statement @S@: the name leaves @S@'s
--     @using@ list, and a statement after @S@ opens it from the source:
--     @open import X using (…)@, or for a submodule @open N using (…)@ with
--     @module N@ added to @S@'s @using@ list (this works for an applied
--     facade too: @N@ is then the importer's own copy);
--   * a qualified use @Q.x@: @X.x@ (and @import X@), or @Q.N.x@.
--
--   The facade loses the @public@ and keeps the open.  Everything is decided
--   during the run and written at its end, and only for a target no importer
--   of which had to be skipped (a renamed name, a chain to a submodule, …):
--   a target is repaired everywhere or nowhere.  Only importers checked in
--   the run are seen, so the run must check the facade and all its
--   importers; the next run re-checks the rewritten modules, and that run is
--   the verification.

module Agda.TypeChecking.RepairReexports
  ( repairWanted
  , repairFor
  , finishRepair
  ) where

import Control.Monad (forM, forM_, unless)
import Control.Monad.IO.Class (liftIO)
import Data.Char (isDigit)
import Data.IORef
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe, isJust, isNothing, mapMaybe)
import qualified Data.Set as Set
import qualified Data.Text as T
import System.IO.Unsafe (unsafePerformIO)

import Agda.Syntax.Common.Pretty (prettyShow)
import qualified Agda.Syntax.Concrete.Name as C
import Agda.Syntax.Position
import Agda.Syntax.Scope.Base
import Agda.Syntax.Scope.NameResolutionLog

import Agda.Interaction.Options.Types (optRepairReexports)
import Agda.TypeChecking.DeadImports (Edit, readSource, applyEdits, posOf, isBlank, isInstanceName, groupEdits)
import Agda.TypeChecking.Monad

type TKey = (String, Int)

-- | A target, as found when its facade was checked.
data Target = Target
  { tFile   :: FilePath
  , tMod    :: String   -- ^ The re-exported module, as written at the line.
  , tLocal  :: Bool     -- ^ A submodule of the facade, not @open import@.
  , tPath   :: String
      -- ^ How an importer names the re-exported module: for a submodule, its
      --   path inside the facade (`FlatSimulation.C` when `C` is in scope there
      --   only through `open FlatSimulation`), else 'tMod' (R25).
  , tPublic :: Edit     -- ^ Removing the @public@.
  , tNames  :: [String] -- ^ What the statement brings in (as bound).
  , tRenames :: [(String, T.Text)]
      -- ^ Its renamings: the name as bound, and the entry as written
      --   (@map to mmap@), which an importer then writes itself (R20).
  }

-- | What an importer needs, decided while it was checked.
data Intent
  = Group FilePath [(Int, Int)] [(Int, Int)] [T.Text]
      -- ^ A @using@ group (its items' spans): items to drop, items to add.
  | Insert FilePath Int T.Text
  | Replace FilePath (Int, Int) T.Text
  | NewOpen FilePath String Int String [T.Text]
      -- ^ @open import X using (…)@ to add (module, position, indentation,
      --   names): merged over the targets at the end, one per module.
  deriving (Eq, Ord)

data St = St
  { stTargets :: Map.Map TKey (Either String Target)
  , stSkips   :: Map.Map TKey [String]
  , stIntents :: Map.Map TKey [Intent]
  , stEdited  :: Map.Map TKey (Set.Set FilePath)
  , stTouched :: Map.Map TKey (Set.Set (FilePath, Int))
  }

{-# NOINLINE state #-}
state :: IORef St
state = unsafePerformIO $ newIORef $ St Map.empty Map.empty Map.empty Map.empty Map.empty

repairWanted :: TCM Bool
repairWanted = not . null . optRepairReexports <$> commandLineOptions

-- | After a module is type checked: resolve the targets it is the facade
--   of, and decide its repairs as an importer of the others.
repairFor :: TopLevelModuleName -> FilePath -> [Occurrence] -> [OpenStmt] -> TCM ()
repairFor mname src occs opens = do
  targets <- optRepairReexports <$> commandLineOptions
  -- the directive items naming an instance (after type checking: known)
  insts <- if null targets then return Set.empty else
    fmap (Set.fromList . concat) $ forM [ it | st <- opens, it <- osItems st ] $ \ (n, _, _, qs) -> do
      i <- or <$> mapM isInstanceName qs
      return [ n | i ]
  unless (null targets) $ liftIO $ do
    txt <- readSource src
    let me = prettyShow mname
    forM_ [ k | k@(m, _) <- targets, m == me ] $ \ k -> do
      -- forced: a lazy decision would keep the whole module alive to the end
      let f = facade txt src opens k
      forceTarget f `seq` modifyIORef' state $ \ s -> s { stTargets = Map.insert k f (stTargets s) }
    St{ stTargets = ts } <- readIORef state
    forM_ [ (k, t) | (k@(m, _), Right t) <- Map.toList ts, m /= me ] $ \ (k@(fac, _), t) -> do
      let (intents, skips, handled) = importer insts txt src fac t occs opens
      forceIntents intents `seq` length (concat skips) `seq` sum handled `seq` modifyIORef' state $ \ s -> s
        { stTouched = if null handled then stTouched s else Map.insertWith Set.union k (Set.fromList [ (src, h) | h <- handled ]) (stTouched s) }
      modifyIORef' state $ \ s -> s
        { stSkips   = if null skips then stSkips s else Map.insertWith (++) k (map ((me ++ ": ") ++) skips) (stSkips s)
        , stIntents = if null intents then stIntents s else Map.insertWith (++) k intents (stIntents s)
        , stEdited  = if null intents then stEdited s else Map.insertWith Set.union k (Set.singleton src) (stEdited s)
        }

-- | The target statement in its facade.
facade :: T.Text -> FilePath -> [OpenStmt] -> TKey -> Either String Target
facade txt src opens key@(me, line) =
  case [ st | st <- opens, osPublic st, (posLine <$> rStart' (getRange (osModule st))) == Just (fromIntegral line) ] of
    [] -> Left "no public open statement starts at that line"
    (st : _)
      | Just _ <- osShown st -> Left "it re-exports a module application"
      | not (importStmtIn txt st) && not ((me ++ ".") `List.isPrefixOf` osTarget st) ->
          Left ("it opens " ++ osTarget st ++ ", which is not a submodule of the facade")
      | not (importStmtIn txt st), ".#" `List.isInfixOf` drop (length me + 1) (osTarget st) ->
          Left ("it opens " ++ osTarget st ++ ", a submodule an importer cannot name")
      | otherwise -> case (posOf (osModule st), rEnd' (getRange (osModule st))) of
          (Just ms, Just me') ->
            let me      = me'
                path | importStmtIn txt st = prettyShow (osModule st)
                     -- an anonymous section's `_` is no part of the path (R23)
                     | otherwise           = List.intercalate "." (filter (/= "_") (splitDots (drop (length (fst key) + 1) (osTarget st))))
                splitDots x = case break (== '.') x of
                  (c, [])       -> [c]
                  (c, _ : rest) -> c : splitDots rest
                mstart  = ms - 1
                mend    = fromIntegral (posPos me) - 1
                before  = T.dropWhileEnd isBlank (T.take mstart txt)
                isImp   = T.pack "import" `T.isSuffixOf` before
                end     = stmtEnd txt st mstart mend
                end'    = max end (layoutEnd txt (stmtStart txt mstart) mend)
                seg     = T.take (end' - mend) (T.drop mend txt)
            in case T.breakOn (T.pack "public") seg of
                 (pre, rest) | not (T.null rest) ->
                   let at   = mend + T.length pre
                       from = at - T.length (T.takeWhileEnd isBlank (T.take at txt))
                       -- `public` alone on its line: the line goes
                       lineAlone = startsLine txt at && T.all isBlank (T.takeWhile (/= '\n') (T.drop (at + 6) txt))
                       pubEdit | lineAlone = (lineBegin txt at - 1, at + 6 + T.length (T.takeWhile isBlank (T.drop (at + 6) txt)), T.empty)
                               | otherwise = (from, at + 6, T.empty)
                       renames = [ (n, T.unwords (T.words (T.take (b - a) (T.drop a txt))))
                                 | (n, r, True, _) <- osItems st
                                 , Just a <- [subtract 1 . fromIntegral . posPos <$> rStart' r]
                                 , Just b <- [subtract 1 . fromIntegral . posPos <$> rEnd' r] ]
                   in Right $ Target src (prettyShow (osModule st)) (not isImp) path pubEdit (map fst (osHops st)) renames
                 _ -> Left "no `public` found in the statement"
          _ -> Left "the statement has no range"

-- | An `open import` (not an open of a module in scope).
importStmtIn :: T.Text -> OpenStmt -> Bool
importStmtIn txt st = case posOf (osModule st) of
  Just ms -> T.pack "import" `T.isSuffixOf` T.dropWhileEnd isBlank (T.take (ms - 1) txt)
  Nothing -> False

-- | An importer's repairs for one target, and why it cannot be repaired.
importer :: Set.Set String -> T.Text -> FilePath -> String -> Target -> [Occurrence] -> [OpenStmt] -> ([Intent], [String], [Int])
importer insts txt src fac t occs opens = (intents, List.nub skips, handled)
  where
    byKey = Map.fromList [ (k, st) | st <- opens, Just k <- [posOf (osModule st)] ]
    -- `open import M as A` is logged as `open A`: the module it opens is M
    target st
      | isNothing (osShown st), aliasedImport st = norm (osTarget st)
      | otherwise = norm (prettyShow (fromMaybe (osModule st) (osShown st)))
    aliasedImport st = case posOf (osModule st) of
      Just ms -> T.pack " as" `T.isSuffixOf` T.dropWhileEnd isBlank (T.take (ms - 1) txt)
      Nothing -> False

    -- a lineage seen from statement `st`: its own hop dropped, and, for an
    -- application (`open F args`), the application's hop too; the generated
    -- name of an applied module (`.#F-1234`) read as `F`
    afterStmt st hs =
      let hs1 = filter (/= "_") (map norm (drop 1 hs))
      in if take 1 hs1 == [target st] && isJust (osShown st) then drop 1 hs1 else hs1
    applied = any (\ h -> take 2 h == ".#")

    -- the hop through the target, in a lineage seen from a statement whose
    -- own hop is the first (k >= 2), or from a qualifier (k >= 1)
    crossing :: Maybe String -> [String] -> Maybe Int
    crossing first hs = List.find ok [ i | (i, h) <- zip [0 ..] hs, h == tMod t ]
      where ok i | i == 0    = first == Just fac
                 | otherwise = unalias (hs !! (i - 1)) == fac
    -- a hop written as an alias of the importer's (`import F as Fx` then
    -- `module EE = Fx args`) is that module (R24, test/Rewrite/repair-alias-instance)
    unalias h = fromMaybe h (lookup h importAliases)
    importAliases = [ (a, m) | l <- T.lines txt, ["import", m, "as", a] <- [map T.unpack (T.words l)] ]

    -- A submodule of the facade reached through a chain (the importer opens
    -- G, which re-exports the facade): the importer imports the facade
    -- itself, under an alias, and opens `A.N`.  Not when the facade is applied
    -- on the way (its submodule is then a copy the importer cannot name).
    chainLocal i hs = tLocal t && i > 0

    -- an anonymous section (`module _ (v : A) where`) is opened into the
    -- module around it: its hop `_` is that module's own (R23,
    -- test/Rewrite/repair-section-instance), so it is not a hop
    anon q = prettyShow q == "_"
    hopTexts = \case
      Defined     -> []
      Opened q w  | anon q -> hopTexts w
                  | otherwise -> prettyShow q : hopTexts w
      Applied q w -> prettyShow q : hopTexts w
    -- a named instance applied with a directive (`module N = F args using (…)`)
    -- copies only what it lists: its copy of the submodule may not exist, and
    -- the application's directive is not logged, so it is not rewritten (R26)
    restricted n = case T.breakOn (T.pack ("module " ++ n ++ " = ")) txt of
      (pre, rest) | not (T.null rest), T.null pre || T.last pre == '\n' ->
        let body = T.unlines (take 1 ls ++ takeWhile (\ l -> T.null l || isBlank (T.head l)) (drop 1 ls))
            ls   = T.lines rest
        in any (`elem` map T.pack ["using", "hiding", "renaming"]) (T.words body)
      _ -> False
    -- which hops of a lineage are module applications (`module N = F args`)
    appliedOps = \case
      Defined     -> []
      Opened q w  | anon q -> appliedOps w
                  | otherwise -> False : appliedOps w
      Applied _ w -> True  : appliedOps w
    -- a chain whose facade hop is an application NAMED by the hop before it
    -- (`module FI = F T` then `open FI`, or `FI.x`): the importer names the
    -- copy of the submodule as `FI.N` itself (R22, test/Rewrite/repair-instance-submodule);
    -- an application anywhere else on the way is a copy nobody can name

    -- unqualified uses: (statement key, item text, through a chain), or a skip
    uses :: [Either String (Int, T.Text, Via)]
    uses = map snd usesAt
    usesAt = concatMap use occs
    use (Occurrence x what) = case (x, what) of
      (C.QName _, Resolved r []) ->
        [ (posOf x, through (anameLineage a) (T.pack (prettyShow (C.unqualify x)))) | a <- names r ]
      (C.QName _, ModuleName am) ->
        [ (posOf x, through (amodLineage am) (T.pack ("module " ++ prettyShow x))) ]
      -- the head of a qualifier (`Inner` in `Inner.twice`) that a statement
      -- brought through the target is a module item used: it moves (R20)
      (C.QName _, QualifierHead am) ->
        [ (posOf x, through (amodLineage am) (T.pack ("module " ++ prettyShow x))) ]
      _ -> []
    -- where those heads are written: a qualified use starting there keeps
    -- its qualifier, which still names the moved item
    movedHeads = Set.fromList [ p | o@(Occurrence _ QualifierHead{}) <- occs, (Just p, Right _) <- use o ]
    -- the occurrences this target rewrites the meaning of: two targets
    -- touching one occurrence (a chain of re-exports) are not written in
    -- the same run
    handled = [ p | (Just p, Right _) <- usesAt ] ++ [ p | (Just p, Right _) <- qualsAt ]
    through w item = case w of
      Opened q _ | Just k <- posOf q, Just st <- Map.lookup k byKey ->
        let hs  = hopTexts w
            ops = appliedOps w
            off = length hs - length (afterStmt st hs)
            -- the statement opens a NAMED instance of the facade (an
            -- anonymous one, `.#F-…`, is a copy nobody can name)
            inst i = chainLocal i hs && i == 1 && isNothing (osShown st) && off == 1 && take 1 (drop 1 ops) == [True]
                     && not (applied (drop 1 hs))
        in case crossing (Just (target st)) (afterStmt st hs) of
             Nothing -> Left ""
             Just i
               | any (\ (n, _, ren, _) -> ren && T.pack n == item) (osItems st) -> Left ("renamed: " ++ T.unpack item)
               | inst i, restricted (prettyShow (osModule st)) ->
                   Left ("the instance " ++ prettyShow (osModule st) ++ " is applied with a directive: add the submodule to it by hand")
               | inst i -> Right (k, item, ViaInst (prettyShow (osModule st)))
               | chainLocal i hs && (applied (drop 1 hs) || or (take (off + i - 1) (drop 1 ops))) ->
                   Left "a submodule re-export reached through an applied chain"
               | otherwise -> Right (k, item, if chainLocal i hs then ViaChain else ViaDirect)
      _ -> Left ""

    -- an overloaded name (constructor, field, pattern synonym) means EVERY
    -- candidate: resolution picks one by type later, so each that crosses the
    -- target must stay in scope (`c : A` from A and `c : B` through F)
    names = \case
      DefinedName _ a _    -> [a]
      FieldName as         -> toList' as
      ConstructorName _ as -> toList' as
      PatternSynResName as -> toList' as
      _                    -> []
    toList' = foldr (:) []

    -- an instance listed in a crossing directive is used without being
    -- written: it moves like a used name
    used    = List.nub ([ (k, renamed it, c) | Right (k, it, c) <- uses ] ++
                [ (k, T.pack n, ViaDirect) | (k, st) <- Map.toList byKey
                                       , (n, _, _, _) <- crossingItems st, n `Set.member` insts ])
    skipped = [ why | Left why <- uses, not (null why) ]
    -- a name the target renames is written as the entry (`map to mmap`)
    renamed it = maybe it id (lookup (T.unpack it) (tRenames t))

    -- qualified uses: only the qualifier, as written, is replaced
    quals :: [Either String (Intent, Bool)]
    quals = map snd qualsAt
    qualsAt = [ (posOf x, q') | o@(Occurrence x _) <- occs, q' <- qual o ]
    qual (Occurrence x what) = case (x, what) of
      (C.Qual _ _, Resolved _ _) | Just p <- posOf x, p `Set.member` movedHeads -> []
      (C.Qual _ _, Resolved r qms) ->
        let rawName = [ (hopTexts l, appliedOps l) | a <- names r, let l = anameLineage a ]
            rawQual = [ (hopTexts l, appliedOps l) | am <- qms, let l = amodLineage am ]
            denotesF = any (\ am -> prettyShow (amodName am) == fac) qms
            hit (hs, ops) = (\ i -> (i, hs, ops)) <$> crossing (if denotesF then Just fac else Nothing) (map norm hs)
            hitsN = mapMaybe hit rawName
            hitsQ = mapMaybe hit rawQual
            full  = prettyShow x
            qual' = take (length full - length (prettyShow (C.unqualify x)) - 1) full
            -- the qualifier denotes a submodule of the target's module (a
            -- record module, `NamedCtx` in `NamedCtx.size`): that path stays
            sub   = case [ drop (length (tMod t) + 1) m | am <- qms, let m = prettyShow (amodName am)
                                                        , (tMod t ++ ".") `List.isPrefixOf` m ] of
                      (m : _) -> m ++ "."
                      []      -> ""
        in case (hitsN, hitsQ) of
             (_ : _, _) | Just _ <- lookup (prettyShow (C.unqualify x)) (tRenames t) ->
               [ Left ("a renamed name used qualified: " ++ full) ]
             ((i, hs, ops) : _, _) -> [ requalify x qual' sub i hs ops ]
             ([], _ : _) | '.' `elem` qual' -> [ Left ("a qualified module path crossing the target: " ++ full) ]
             ([], (i, hs, ops) : _) -> [ requalify x qual' sub i hs ops ]
             _ -> []
      _ -> []
    requalify x q sub i hs ops = case span' x of
      Nothing -> Left "a qualified name without a range"
      Just (a, b)
        | not (qtext `T.isPrefixOf` slice) -> Left ("a qualified name written otherwise: " ++ T.unpack slice)
        -- `FI.x` with `module FI = F T`: the qualifier names the copy (R22)
        | inst, restricted q -> Left ("the instance " ++ q ++ " is applied with a directive: add the submodule to it by hand")
        | inst -> Right (Replace src (a, a + T.length qtext) (T.pack (q ++ "." ++ tPath t ++ ".")), False)
        | chainLocal i hs && (applied hs || or (take i ops)) -> Left "a submodule re-export reached through an applied chain"
        | otherwise ->
            let prefix | chainLocal i hs = aliasF ++ "." ++ tPath t ++ "."
                       | tLocal t        = q ++ "." ++ tPath t ++ "."
                       | otherwise       = aliasX ++ "." ++ sub
            in Right (Replace src (a, a + T.length qtext) (T.pack prefix), chainLocal i hs)
        where slice = T.take (b - a) (T.drop a txt)
              -- the whole qualifier as written (`Once.CCC.FrameSemantics`
              -- in `Once.CCC.FrameSemantics.fs-interp`), not its first part
              qtext = T.pack (q ++ ".")
              inst  = chainLocal i hs && i == 1 && take 1 ops == [True] && not (applied hs)
    span' x = case (rStart' (getRange x), rEnd' (getRange x)) of
      (Just s, Just e) -> Just (fromIntegral (posPos s) - 1, fromIntegral (posPos e) - 1)
      _ -> Nothing

    qualIntents = [ i | Right (i, _) <- quals ]

    -- aliases: an existing `import M as Q` is reused, else the last component
    -- of the module's name, primed until no qualifier of the file uses it
    aliasFor m = case T.breakOn (T.pack ("import " ++ m ++ " as ")) txt of
      (pre, rest) | not (T.null rest) ->
        (T.unpack (T.takeWhile (\ c -> not (isBlank c) && c /= '\n')
                    (T.drop (T.length pre + length m + 11) txt)), True)
      -- a plain `import M` (its own line) binds `M` already: not imported twice
      _ | any (\ l -> T.strip l == T.pack ("import " ++ m)) (T.lines txt) -> (m, True)
      _ -> (fresh (lastComponent m), False)
    lastComponent m = reverse (takeWhile (/= '.') (reverse m))
    fresh a | taken a   = fresh (a ++ "′")
            | otherwise = a
    taken a = any (\ i -> i == 0 || boundary (T.index txt (i - 1)))
                  [ T.length pre | (pre, _) <- T.breakOnAll (T.pack (a ++ ".")) txt ]
              || T.pack ("as " ++ a) `T.isInfixOf` txt || T.pack ("module " ++ a ++ " ") `T.isInfixOf` txt
    boundary c = isBlank c || c `elem` ("\n(){}[];⦃⦄@" :: String)
    (aliasX, haveX) = aliasFor (tMod t)
    (aliasF, haveF) = aliasFor fac

    -- an `open import X …` (there, or being added) binds `X` already
    needImportX = not (tLocal t) && not (null qualIntents) && not haveX
                  && not (aliasX == tMod t && (not (null neededX) || not (null ownX)))
    needImportF = not haveF && (or [ c == ViaChain | Right (_, _, c) <- uses ] || or [ c | Right (_, c) <- quals ])
    imports = [ importAs (tMod t) aliasX | needImportX ] ++
              [ importAs fac aliasF | needImportF ]
    importAs m a | a == m    = "import " ++ m
                 | otherwise = "import " ++ m ++ " as " ++ a
    importAt =
      case [ T.length pre | (pre, _) <- T.breakOnAll (T.pack ("import " ++ fac)) txt ] ++ firstImport of
        (s0 : _) -> Just (layoutEnd txt (lineBegin txt s0) s0, indentOf s0)
        []       -> Nothing
    firstImport = [ o | (o, l) <- lineStarts, any (`T.isPrefixOf` l) [T.pack "import ", T.pack "open import "] ]
    lineStarts = scanOffsets 0 (T.lines txt)
    scanOffsets _ [] = []
    scanOffsets o (l : ls) = (o, l) : scanOffsets (o + T.length l + 1) ls
    -- the statement's own indentation, not its last (continuation) line's
    indentOf s = T.unpack (T.takeWhile isBlank (T.drop (lineBegin txt s) txt))
    importIntents = case importAt of
      Just (at, ind) -> [ Insert src at (T.pack ("\n" ++ ind ++ imp)) | imp <- imports ]
      Nothing -> []

    skips = skipped ++ [ w | Left w <- quals ] ++
            [ "no import statement to put an import after" | not (null imports), Nothing <- [importAt] ]

    -- per statement: drop its crossing items, add what is used after it
    stmts = List.nub ([ k | (k, _, _) <- used ] ++
                      [ k | (k, st) <- Map.toList byKey, not (null (crossingItems st)) || not (null (osHiding st)) ])
    crossingItems st =
      [ it | it@(n, _, _, _) <- osItems st
           , Just hs <- [maybe (lookup ("module " ++ n) (osHops st)) Just (lookup n (osHops st))]
           , Just _ <- [crossing (Just (target st)) (afterStmt st hs)] ]
    perStmt = concat
      [ stmtIntents k st
      | k <- stmts, Just st <- [Map.lookup k byKey] ]
    stmtIntents k st =
      let direct = [ it | (k', it, ViaDirect) <- used, k' == k ]
          chain  = [ it | (k', it, ViaChain) <- used, k' == k ]
          insts  = List.nub [ n | (k', _, ViaInst n) <- used, k' == k ]
          spans  = [ sp | (_, r, False, _) <- osItems st, Just sp <- [rspan r] ]
          drops  = [ sp | (_, r, _, _) <- crossingItems st, Just sp <- [rspan r] ]
          -- the facade's own module the path starts with (R25)
          modItem = T.pack ("module " ++ takeWhile (/= '.') (tPath t))
          hasMod = any (\ (n, _, _, _) -> T.pack n == modItem) (osItems st)
          adds   = [ modItem | tLocal t, not (null direct), not (osWholesale st), not hasMod ]
          group  = [ Group src spans drops adds | not (null spans), not (null drops && null adds) ]
          ms     = maybe 0 (subtract 1) (posOf (osModule st))
          me     = maybe ms (\ p -> fromIntegral (posPos p) - 1) (rEnd' (getRange (osModule st)))
          start  = stmtStart txt ms
          end    = stmtEnd txt st ms me
          ind    = T.unpack (T.takeWhile isBlank (T.drop (lineBegin txt start) txt))
          opener | tLocal t  = "open " ++ tPath t
                 | otherwise = "open import " ++ tMod t
          line o its = Insert src end (T.pack ("\n" ++ ind ++ o) <> directive its)
          -- `open import X using (…)` is gathered over all statements (mergeX)
          insert = [ line opener direct | not (null direct), tLocal t ] ++
                   [ line ("open " ++ aliasF ++ "." ++ tPath t) chain | not (null chain) ] ++
                   [ line ("open " ++ n ++ "." ++ tPath t) [ it | (k', it, ViaInst n') <- used, k' == k, n' == n ] | n <- insts ]
          -- a hidden name the facade no longer exports: the hiding goes
          hspans = [ sp | (_, r) <- osHiding st, Just sp <- [rspan r] ]
          hdrops = [ sp | (n, r) <- osHiding st, Just sp <- [rspan r], target st == fac
                        , n `elem` tNames t || ("module " ++ n) `elem` tNames t ]
          hiding
            | null hdrops = []
            | length hdrops < length hspans = [ Group src hspans hdrops [] ]
            -- nothing left hidden: `hiding (…)` goes, keyword and all
            | otherwise =
                let s0    = minimum (map fst hspans)
                    e0    = maximum (map snd hspans)
                    open  = maybe 0 id (List.find (\ j -> T.index txt j == '(') [s0 - 1, s0 - 2 .. 0])
                    close = maybe (T.length txt) id (List.find (\ j -> T.index txt j == ')') [e0 .. T.length txt - 1])
                    kw    = T.dropWhileEnd (\ c -> isBlank c || c == '\n') (T.take open txt)
                    from  = T.length (T.dropWhileEnd isBlank (T.take (T.length kw - 6) txt))
                in [ Replace src (from, close + 1) T.empty | T.pack "hiding" `T.isSuffixOf` kw ]
      in group ++ hiding ++ insert

    -- what the importer needs from a re-exported top-level module X, from all
    -- its statements: nothing if it opens X wholesale at the top level
    -- already, else into its own top-level `open import X using (…)` if it
    -- has one, else one new statement after the first statement it came
    -- through, a top-level one first.  Only a top-level statement scopes
    -- the whole file: a statement inside a nested module does not reach a
    -- use in a sibling (R21, test/Rewrite/repair-merge-nested)
    neededX = List.nub [ it | (_, it, ViaDirect) <- used, not (tLocal t) ]
    ownX    = [ st | st <- opens, not (osPublic st), isNothing (osShown st)
                   , prettyShow (osModule st) == tMod t, topLevel st ]
    topLevel st = let ms = maybe 0 (subtract 1) (posOf (osModule st))
                      s0 = stmtStart txt ms
                  in lineBegin txt s0 == s0
    mergeX
      | null neededX = []
      | any osWholesale ownX = []
      | (st : _) <- [ st | st <- ownX, not (null (spansOf st)) ] =
          let have = [ T.pack n | (n, _, False, _) <- osItems st ]
              plain = [ it | it <- neededX, it `notElem` have, not (isRenaming it) ]
              rens  = [ it | it <- neededX, isRenaming it ]
              ms  = maybe 0 (subtract 1) (posOf (osModule st))
              me  = maybe ms (\ p -> fromIntegral (posPos p) - 1) (rEnd' (getRange (osModule st)))
              ind = T.unpack (T.takeWhile isBlank (T.drop (lineBegin txt (stmtStart txt ms)) txt))
          in [ Group src (spansOf st) [] plain | not (null plain) ] ++
             [ NewOpen src (tMod t) (stmtEnd txt st ms me) ind rens | not (null rens) ]
      | otherwise = case List.sortOn (\ (k, st) -> (not (topLevel st), k)) [ (k, st) | (k, _, ViaDirect) <- used, Just st <- [Map.lookup k byKey] ] of
          ((_, st) : _) ->
            let ms  = maybe 0 (subtract 1) (posOf (osModule st))
                me  = maybe ms (\ p -> fromIntegral (posPos p) - 1) (rEnd' (getRange (osModule st)))
                ind = T.unpack (T.takeWhile isBlank (T.drop (lineBegin txt (stmtStart txt ms)) txt))
            in [ NewOpen src (tMod t) (stmtEnd txt st ms me) ind neededX ]
          [] -> []
    spansOf st = [ sp | (_, r, False, _) <- osItems st, Just sp <- [rspan r] ]
    rspan r = case (rStart' r, rEnd' r) of
      (Just s, Just e) -> Just (fromIntegral (posPos s) - 1, fromIntegral (posPos e) - 1)
      _ -> Nothing

    intents = importIntents ++ perStmt ++ mergeX ++ qualIntents

-- | How an importer reaches a name the target re-exports: directly, through
--   a chain (the facade imported under an alias, its submodule opened), or
--   through a named instance of the facade (its copy of the submodule opened).
data Via = ViaDirect | ViaChain | ViaInst String
  deriving Eq

forceTarget :: Either String Target -> Int
forceTarget = \case
  Left why -> length why
  Right (Target f m l pth (a, b, x) ns rs) -> length f + length m + fromEnum l + length pth + a + b + T.length x + sum (map length ns)
                                         + sum [ length n + T.length e | (n, e) <- rs ]

forceIntents :: [Intent] -> Int
forceIntents = sum . map one
  where
    one = \case
      Group f sps ds as -> length f + sum (map (uncurry (+)) (sps ++ ds)) + sum (map T.length as)
      Insert f a x      -> length f + a + T.length x
      Replace f (a, b) x -> length f + a + b + T.length x
      NewOpen f m a ind xs -> length f + length m + a + length ind + sum (map T.length xs)

-- | The generated name of an applied module, @.#F-1234@, read as @F@.
norm :: String -> String
norm h = case h of
  '.' : '#' : rest -> let r = reverse rest
                          (ds, r') = span isDigit r
                      in if not (null ds) && take 1 r' == "-" then reverse (drop 1 r') else rest
  _ -> h

-- | At the end of the run: write the targets every importer could follow.
finishRepair :: TCM ()
finishRepair = do
  targets <- optRepairReexports <$> commandLineOptions
  unless (null targets) $ liftIO $ do
    St ts skips intents edited touched <- readIORef state
    -- targets touching a common occurrence (a chain of re-exports) are not
    -- written together: the first is, the rest wait for the next run
    claimed <- newIORef (Set.empty :: Set.Set (FilePath, Int))
    ok <- fmap concat $ forM targets $ \ k@(m, l) -> do
      let name = m ++ ":" ++ show l
      case Map.lookup k ts of
        Nothing -> [] <$ putStrLn ("repair-reexports: " ++ name ++ ": NOT applied: the module was not checked in this run")
        Just (Left why) -> [] <$ putStrLn ("repair-reexports: " ++ name ++ ": NOT applied: " ++ why)
        Just (Right t) -> do
         let mine = Map.findWithDefault Set.empty k touched
         taken <- readIORef claimed
         case Map.findWithDefault [] k skips of
          _ | not (Set.null (Set.intersection mine taken)) ->
            [] <$ putStrLn ("repair-reexports: " ++ name ++ ": NOT applied: shares occurrences with a target applied in this run (a chain); run again")
          [] -> do
            modifyIORef' claimed (Set.union mine)
            putStrLn $ "repair-reexports: " ++ name ++ ": applied, " ++
              show (Set.size (Map.findWithDefault Set.empty k edited)) ++ " importer(s) rewritten"
            return [ (t, Map.findWithDefault [] k intents) ]
          ws -> [] <$ putStrLn ("repair-reexports: " ++ name ++ ": NOT applied:\n" ++
                               unlines (map ("  " ++) (List.nub ws)))
    let pub     = [ (tFile t, tPublic t) | (t, _) <- ok ]
        is      = Set.toList (Set.fromList (concatMap snd ok))
        files   = List.nub (map fst pub ++ [ f | i <- is, let f = fileOf i ])
    forM_ files $ \ f -> do
      txt <- readSource f
      let groups = Map.fromListWith (\ (d1, a1) (d2, a2) -> (d1 ++ d2, a1 ++ a2))
                     [ (sps, (ds, as)) | Group f' sps ds as <- is, f' == f ]
          gEdits = concat [ groupEdits txt sps (List.nub ds) (List.nub as) | (sps, (ds, as)) <- Map.toList groups ]
          -- one new `open import X using (…)` per module, at the first place
          newOpens = Map.fromListWith (\ (a1, i1, n1) (a2, i2, n2) -> if a1 <= a2 then (a1, i1, n1 ++ n2) else (a2, i2, n2 ++ n1))
                       [ (m, (a, ind, ns)) | NewOpen f' m a ind ns <- is, f' == f ]
          opensE = [ (a, a, T.pack ("\n" ++ ind ++ "open import " ++ m) <> directive (List.nub ns))
                   | (m, (a, ind, ns)) <- Map.toList newOpens ]
          others = opensE ++ [ (a, a, s) | Insert f' a s <- is, f' == f ] ++
                   [ (a, b, s) | Replace f' (a, b) s <- is, f' == f ] ++
                   [ e | (f', e) <- pub, f' == f ]
      applyEdits f (gEdits ++ others)
    writeIORef state $ St Map.empty Map.empty Map.empty Map.empty Map.empty
  where
    fileOf = \case { Group f _ _ _ -> f; Insert f _ _ -> f; Replace f _ _ -> f; NewOpen f _ _ _ _ -> f }

-- | @ using (…)@, and @ renaming (…)@ for the items that are renaming
--   entries (@map to mmap@: a name cannot contain a space).
directive :: [T.Text] -> T.Text
directive its =
  let (rens, plain) = List.partition isRenaming its
  in T.pack " using (" <> T.intercalate (T.pack "; ") plain <> T.pack ")" <>
     (if null rens then T.empty else T.pack " renaming (" <> T.intercalate (T.pack "; ") rens <> T.pack ")")

isRenaming :: T.Text -> Bool
isRenaming = T.isInfixOf (T.pack " to ")

------------------------------------------------------------------------
-- Statement extents (as in DeadImports)

lineBegin :: T.Text -> Int -> Int
lineBegin txt i = maybe 0 (\ k -> i - k) (T.findIndex (== '\n') (T.reverse (T.take i txt)))

startsLine :: T.Text -> Int -> Bool
startsLine txt i = T.all isBlank (T.take (i - lineBegin txt i) (T.drop (lineBegin txt i) txt))

-- | Back from the module name over @import@ and @open@.
stmtStart :: T.Text -> Int -> Int
stmtStart txt ms =
  let skip w i = let pre = T.dropWhileEnd isBlank (T.take i txt)
                 in if T.pack w `T.isSuffixOf` pre then T.length pre - length w else i
  in skip "open" (skip "import" ms)

-- | The statement ends at its last directive's @)@, or by layout.
stmtEnd :: T.Text -> OpenStmt -> Int -> Int -> Int
stmtEnd txt st ms me
  | null (osItems st) = layoutEnd txt (stmtStart txt ms) me
  | otherwise =
      let lastItem = maximum (me : [ b | (_, r, _, _) <- osItems st, Just e <- [rEnd' r], let b = fromIntegral (posPos e) - 1 ])
          close    = maybe (T.length txt) id (List.find (\ j -> T.index txt j == ')') [lastItem .. T.length txt - 1])
      in close + 1

-- | The lines indented more than the statement's start belong to it.
layoutEnd :: T.Text -> Int -> Int -> Int
layoutEnd txt start me =
  let col   = start - lineBegin txt start
      eol i = maybe (T.length txt) (+ i) (T.findIndex (== '\n') (T.drop i txt))
      go e | e >= T.length txt = e
           | otherwise =
               let nxt  = e + 1
                   line = T.takeWhile (/= '\n') (T.drop nxt txt)
                   ind  = T.length (T.takeWhile isBlank line)
               in if not (T.all isBlank line) && ind > col then go (eol nxt) else e
  in go (eol me)
