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
  , tPublic :: Edit     -- ^ Removing the @public@.
  , tNames  :: [String] -- ^ What the statement brings in (as bound).
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
facade txt src opens (me, line) =
  case [ st | st <- opens, osPublic st, (posLine <$> rStart' (getRange (osModule st))) == Just (fromIntegral line) ] of
    [] -> Left "no public open statement starts at that line"
    (st : _)
      | Just _ <- osShown st -> Left "it re-exports a module application"
      | any (\ (_, _, ren, _) -> ren) (osItems st) -> Left "it renames"
      | not (importStmtIn txt st) && not ((me ++ ".") `List.isPrefixOf` osTarget st) ->
          Left ("it opens " ++ osTarget st ++ ", which is not a submodule of the facade")
      | otherwise -> case (posOf (osModule st), rEnd' (getRange (osModule st))) of
          (Just ms, Just me) ->
            let mstart  = ms - 1
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
                   in Right $ Target src (prettyShow (osModule st)) (not isImp) pubEdit (map fst (osHops st))
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
    target st = norm (prettyShow (fromMaybe (osModule st) (osShown st)))

    -- a lineage seen from statement `st`: its own hop dropped, and, for an
    -- application (`open F args`), the application's hop too; the generated
    -- name of an applied module (`.#F-1234`) read as `F`
    afterStmt st hs =
      let hs1 = map norm (drop 1 hs)
      in if take 1 hs1 == [target st] && isJust (osShown st) then drop 1 hs1 else hs1
    applied = any (\ h -> take 2 h == ".#")

    -- the hop through the target, in a lineage seen from a statement whose
    -- own hop is the first (k >= 2), or from a qualifier (k >= 1)
    crossing :: Maybe String -> [String] -> Maybe Int
    crossing first hs = List.find ok [ i | (i, h) <- zip [0 ..] hs, h == tMod t ]
      where ok i | i == 0    = first == Just fac
                 | otherwise = hs !! (i - 1) == fac

    -- A submodule of the facade reached through a chain (the importer opens
    -- G, which re-exports the facade): the importer imports the facade
    -- itself, under an alias, and opens `A.N`.  Not when the facade is applied
    -- on the way (its submodule is then a copy the importer cannot name).
    chainLocal i hs = tLocal t && i > 0

    -- unqualified uses: (statement key, item text, through a chain), or a skip
    uses :: [Either String (Int, T.Text, Bool)]
    uses = map snd usesAt
    usesAt = concatMap use occs
    use (Occurrence x what) = case (x, what) of
      (C.QName _, Resolved r []) ->
        [ (posOf x, through (anameLineage a) (T.pack (prettyShow (C.unqualify x)))) | a <- names r ]
      (C.QName _, ModuleName am) ->
        [ (posOf x, through (amodLineage am) (T.pack ("module " ++ prettyShow x))) ]
      _ -> []
    -- the occurrences this target rewrites the meaning of: two targets
    -- touching one occurrence (a chain of re-exports) are not written in
    -- the same run
    handled = [ p | (Just p, Right _) <- usesAt ] ++ [ p | (Just p, Right _) <- qualsAt ]
    through w item = case w of
      Opened q _ | Just k <- posOf q, Just st <- Map.lookup k byKey ->
        let hs = lineageTexts w
        in case crossing (Just (target st)) (afterStmt st hs) of
             Nothing -> Left ""
             Just i
               | chainLocal i hs && applied (drop 1 hs) -> Left "a submodule re-export reached through an applied chain"
               | any (\ (n, _, ren, _) -> ren && T.pack n == item) (osItems st) -> Left ("renamed: " ++ T.unpack item)
               | otherwise -> Right (k, item, chainLocal i hs)
      _ -> Left ""

    names = \case
      DefinedName _ a _    -> [a]
      FieldName as         -> take 1 (toList' as)
      ConstructorName _ as -> take 1 (toList' as)
      PatternSynResName as -> take 1 (toList' as)
      _                    -> []
    toList' = foldr (:) []

    -- an instance listed in a crossing directive is used without being
    -- written: it moves like a used name
    used    = List.nub ([ u | Right u <- uses ] ++
                [ (k, T.pack n, False) | (k, st) <- Map.toList byKey
                                       , (n, _, _, _) <- crossingItems st, n `Set.member` insts ])
    skipped = [ why | Left why <- uses, not (null why) ]

    -- qualified uses: only the qualifier, as written, is replaced
    quals :: [Either String (Intent, Bool)]
    quals = map snd qualsAt
    qualsAt = [ (posOf x, q') | o@(Occurrence x _) <- occs, q' <- qual o ]
    qual (Occurrence x what) = case (x, what) of
      (C.Qual _ _, Resolved r qms) ->
        let rawName = [ lineageTexts (anameLineage a) | a <- names r ]
            rawQual = [ lineageTexts (amodLineage am) | am <- qms ]
            denotesF = any (\ am -> prettyShow (amodName am) == fac) qms
            hit hs = (\ i -> (i, hs)) <$> crossing (if denotesF then Just fac else Nothing) (map norm hs)
            hitsN = mapMaybe hit rawName
            hitsQ = mapMaybe hit rawQual
            full  = prettyShow x
            qual' = take (length full - length (prettyShow (C.unqualify x)) - 1) full
        in case (hitsN, hitsQ) of
             ((i, hs) : _, _) -> [ requalify x qual' i hs ]
             ([], _ : _) | '.' `elem` qual' -> [ Left ("a qualified module path crossing the target: " ++ full) ]
             ([], (i, hs) : _) -> [ requalify x qual' i hs ]
             _ -> []
      _ -> []
    requalify x q i hs = case span' x of
      Nothing -> Left "a qualified name without a range"
      Just (a, b)
        | not (qtext `T.isPrefixOf` slice) -> Left ("a qualified name written otherwise: " ++ T.unpack slice)
        | chainLocal i hs && applied hs -> Left "a submodule re-export reached through an applied chain"
        | otherwise ->
            let prefix | chainLocal i hs = aliasF ++ "." ++ tMod t ++ "."
                       | tLocal t        = q ++ "." ++ tMod t ++ "."
                       | otherwise       = aliasX ++ "."
            in Right (Replace src (a, a + T.length qtext) (T.pack prefix), chainLocal i hs)
        where slice = T.take (b - a) (T.drop a txt)
              -- the whole qualifier as written (`Once.CCC.FrameSemantics`
              -- in `Once.CCC.FrameSemantics.fs-interp`), not its first part
              qtext = T.pack (q ++ ".")
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
    needImportF = not haveF && (or [ c | Right (_, _, c) <- uses ] || or [ c | Right (_, c) <- quals ])
    imports = [ importAs (tMod t) aliasX | needImportX ] ++
              [ importAs fac aliasF | needImportF ]
    importAs m a | a == m    = "import " ++ m
                 | otherwise = "import " ++ m ++ " as " ++ a
    importAt =
      case [ T.length pre | (pre, _) <- T.breakOnAll (T.pack ("import " ++ fac)) txt ] ++ firstImport of
        (s0 : _) -> Just (layoutEnd txt (lineBegin txt s0) s0)
        []       -> Nothing
    firstImport = [ o | (o, l) <- lineStarts, any (`T.isPrefixOf` l) [T.pack "import ", T.pack "open import "] ]
    lineStarts = scanOffsets 0 (T.lines txt)
    scanOffsets _ [] = []
    scanOffsets o (l : ls) = (o, l) : scanOffsets (o + T.length l + 1) ls
    indentAt at = let b = lineBegin txt (at - 1) in T.unpack (T.takeWhile isBlank (T.drop b txt))
    importIntents = case importAt of
      Just at -> [ Insert src at (T.pack ("\n" ++ indentAt at ++ imp)) | imp <- imports ]
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
      let direct = [ it | (k', it, False) <- used, k' == k ]
          chain  = [ it | (k', it, True) <- used, k' == k ]
          spans  = [ sp | (_, r, False, _) <- osItems st, Just sp <- [rspan r] ]
          drops  = [ sp | (_, r, _, _) <- crossingItems st, Just sp <- [rspan r] ]
          modItem = T.pack ("module " ++ tMod t)
          hasMod = any (\ (n, _, _, _) -> T.pack n == modItem) (osItems st)
          adds   = [ modItem | tLocal t, not (null direct), not (osWholesale st), not hasMod ]
          group  = [ Group src spans drops adds | not (null spans), not (null drops && null adds) ]
          ms     = maybe 0 (subtract 1) (posOf (osModule st))
          me     = maybe ms (\ p -> fromIntegral (posPos p) - 1) (rEnd' (getRange (osModule st)))
          start  = stmtStart txt ms
          end    = stmtEnd txt st ms me
          ind    = T.unpack (T.takeWhile isBlank (T.drop (lineBegin txt start) txt))
          opener | tLocal t  = "open " ++ tMod t
                 | otherwise = "open import " ++ tMod t
          line o its = Insert src end (T.pack ("\n" ++ ind ++ o ++ " using (") <> T.intercalate (T.pack "; ") its <> T.pack ")")
          -- `open import X using (…)` is gathered over all statements (mergeX)
          insert = [ line opener direct | not (null direct), tLocal t ] ++
                   [ line ("open " ++ aliasF ++ "." ++ tMod t) chain | not (null chain) ]
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
    -- its statements: nothing if it opens X wholesale already, else into its
    -- own `open import X using (…)` if it has one, else one new statement
    -- after the first statement it came through
    neededX = List.nub [ it | (_, it, False) <- used, not (tLocal t) ]
    ownX    = [ st | st <- opens, not (osPublic st), isNothing (osShown st)
                   , prettyShow (osModule st) == tMod t ]
    mergeX
      | null neededX = []
      | any osWholesale ownX = []
      | (st : _) <- [ st | st <- ownX, not (null (spansOf st)) ] =
          let have = [ T.pack n | (n, _, False, _) <- osItems st ]
          in [ Group src (spansOf st) [] [ it | it <- neededX, it `notElem` have ] ]
      | otherwise = case List.sortOn fst [ (k, st) | (k, _, False) <- used, Just st <- [Map.lookup k byKey] ] of
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

forceTarget :: Either String Target -> Int
forceTarget = \case
  Left why -> length why
  Right (Target f m l (a, b, x) ns) -> length f + length m + fromEnum l + a + b + T.length x + sum (map length ns)

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
          opensE = [ (a, a, T.pack ("\n" ++ ind ++ "open import " ++ m ++ " using (") <> T.intercalate (T.pack "; ") (List.nub ns) <> T.pack ")")
                   | (m, (a, ind, ns)) <- Map.toList newOpens ]
          others = opensE ++ [ (a, a, s) | Insert f' a s <- is, f' == f ] ++
                   [ (a, b, s) | Replace f' (a, b) s <- is, f' == f ] ++
                   [ e | (f', e) <- pub, f' == f ]
      applyEdits f (gEdits ++ others)
    writeIORef state $ St Map.empty Map.empty Map.empty Map.empty Map.empty
  where
    fileOf = \case { Group f _ _ _ -> f; Insert f _ _ -> f; Replace f _ _ -> f; NewOpen f _ _ _ _ -> f }

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
