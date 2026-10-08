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
import Data.Maybe (fromMaybe, isJust, mapMaybe)
import qualified Data.Set as Set
import qualified Data.Text as T
import System.IO.Unsafe (unsafePerformIO)

import Agda.Syntax.Common.Pretty (prettyShow)
import qualified Agda.Syntax.Concrete.Name as C
import Agda.Syntax.Position
import Agda.Syntax.Scope.Base
import Agda.Syntax.Scope.NameResolutionLog

import Agda.Interaction.Options.Types (optRepairReexports)
import Agda.TypeChecking.DeadImports (Edit, readSource, applyEdits, posOf, isBlank)
import Agda.TypeChecking.Monad

type TKey = (String, Int)

-- | A target, as found when its facade was checked.
data Target = Target
  { tFile   :: FilePath
  , tMod    :: String   -- ^ The re-exported module, as written at the line.
  , tLocal  :: Bool     -- ^ A submodule of the facade, not @open import@.
  , tPublic :: Edit     -- ^ Removing the @public@.
  }

-- | What an importer needs, decided while it was checked.
data Intent
  = Group FilePath [(Int, Int)] [(Int, Int)] [T.Text]
      -- ^ A @using@ group (its items' spans): items to drop, items to add.
  | Insert FilePath Int T.Text
  | Replace FilePath (Int, Int) T.Text
  deriving (Eq, Ord)

data St = St
  { stTargets :: Map.Map TKey (Either String Target)
  , stSkips   :: Map.Map TKey [String]
  , stIntents :: Map.Map TKey [Intent]
  , stEdited  :: Map.Map TKey (Set.Set FilePath)
  }

{-# NOINLINE state #-}
state :: IORef St
state = unsafePerformIO $ newIORef $ St Map.empty Map.empty Map.empty Map.empty

repairWanted :: TCM Bool
repairWanted = not . null . optRepairReexports <$> commandLineOptions

-- | After a module is type checked: resolve the targets it is the facade
--   of, and decide its repairs as an importer of the others.
repairFor :: TopLevelModuleName -> FilePath -> [Occurrence] -> [OpenStmt] -> TCM ()
repairFor mname src occs opens = do
  targets <- optRepairReexports <$> commandLineOptions
  unless (null targets) $ liftIO $ do
    txt <- readSource src
    let me = prettyShow mname
    forM_ [ k | k@(m, _) <- targets, m == me ] $ \ k -> do
      -- forced: a lazy decision would keep the whole module alive to the end
      let f = facade txt src opens k
      forceTarget f `seq` modifyIORef' state $ \ s -> s { stTargets = Map.insert k f (stTargets s) }
    St{ stTargets = ts } <- readIORef state
    forM_ [ (k, t) | (k@(m, _), Right t) <- Map.toList ts, m /= me ] $ \ (k@(fac, _), t) -> do
      let (intents, skips) = importer txt src fac t occs opens
      forceIntents intents `seq` length (concat skips) `seq` modifyIORef' state $ \ s -> s
        { stSkips   = if null skips then stSkips s else Map.insertWith (++) k (map ((me ++ ": ") ++) skips) (stSkips s)
        , stIntents = if null intents then stIntents s else Map.insertWith (++) k intents (stIntents s)
        , stEdited  = if null intents then stEdited s else Map.insertWith Set.union k (Set.singleton src) (stEdited s)
        }

-- | The target statement in its facade.
facade :: T.Text -> FilePath -> [OpenStmt] -> TKey -> Either String Target
facade txt src opens (_, line) =
  case [ st | st <- opens, osPublic st, (posLine <$> rStart' (getRange (osModule st))) == Just (fromIntegral line) ] of
    [] -> Left "no public open statement starts at that line"
    (st : _)
      | Just _ <- osShown st -> Left "it re-exports a module application"
      | any (\ (_, _, ren, _) -> ren) (osItems st) -> Left "it renames"
      | otherwise -> case (posOf (osModule st), rEnd' (getRange (osModule st))) of
          (Just ms, Just me) ->
            let mstart  = ms - 1
                mend    = fromIntegral (posPos me) - 1
                before  = T.dropWhileEnd isBlank (T.take mstart txt)
                isImp   = T.pack "import" `T.isSuffixOf` before
                end     = stmtEnd txt st mstart mend
                seg     = T.take (end - mend) (T.drop mend txt)
            in case T.breakOn (T.pack "public") seg of
                 (pre, rest) | not (T.null rest) ->
                   let at   = mend + T.length pre
                       from = at - T.length (T.takeWhileEnd isBlank (T.take at txt))
                       -- `public` alone on its line: the line goes
                       lineAlone = startsLine txt at && T.all isBlank (T.takeWhile (/= '\n') (T.drop (at + 6) txt))
                       pubEdit | lineAlone = (lineBegin txt at - 1, at + 6 + T.length (T.takeWhile isBlank (T.drop (at + 6) txt)), T.empty)
                               | otherwise = (from, at + 6, T.empty)
                   in Right $ Target src (prettyShow (osModule st)) (not isImp) pubEdit
                 _ -> Left "no `public` found in the statement"
          _ -> Left "the statement has no range"

-- | An importer's repairs for one target, and why it cannot be repaired.
importer :: T.Text -> FilePath -> String -> Target -> [Occurrence] -> [OpenStmt] -> ([Intent], [String])
importer txt src fac t occs opens = (intents, List.nub skips)
  where
    byKey = Map.fromList [ (k, st) | st <- opens, Just k <- [posOf (osModule st)] ]
    target st = norm (prettyShow (fromMaybe (osModule st) (osShown st)))

    -- a lineage seen from statement `st`: its own hop dropped, and, for an
    -- application (`open F args`), the application's hop too; the generated
    -- name of an applied module (`.#F-1234`) read as `F`
    afterStmt st hs =
      let hs1 = map norm (drop 1 hs)
      in if take 1 hs1 == [target st] && isJust (osShown st) then drop 1 hs1 else hs1

    -- the hop through the target, in a lineage seen from a statement whose
    -- own hop is the first (k >= 2), or from a qualifier (k >= 1)
    crossing :: Maybe String -> [String] -> Maybe Int
    crossing first hs = List.find ok [ i | (i, h) <- zip [0 ..] hs, h == tMod t ]
      where ok i | i == 0    = first == Just fac
                 | otherwise = hs !! (i - 1) == fac

    -- unqualified uses: (statement key, item text), or a skip
    uses :: [Either String (Int, T.Text)]
    uses = concatMap use occs
    use (Occurrence x what) = case (x, what) of
      (C.QName _, Resolved r []) ->
        [ through (anameLineage a) (T.pack (prettyShow (C.unqualify x))) | a <- names r ]
      (C.QName _, ModuleName am) ->
        [ through (amodLineage am) (T.pack ("module " ++ prettyShow x)) ]
      (C.Qual{}, _) -> []
      _ -> []
    through w item = case w of
      Opened q _ | Just k <- posOf q, Just st <- Map.lookup k byKey ->
        let hs = lineageTexts w
        in case crossing (Just (target st)) (afterStmt st hs) of
             Nothing -> Left ""
             Just i
               | tLocal t && i > 0 -> Left "a submodule re-export reached through a chain"
               | any (\ (n, _, ren, _) -> ren && T.pack n == item) (osItems st) -> Left ("renamed: " ++ T.unpack item)
               | otherwise -> Right (k, item)
      _ -> Left ""

    names = \case
      DefinedName _ a _    -> [a]
      FieldName as         -> take 1 (toList' as)
      ConstructorName _ as -> take 1 (toList' as)
      PatternSynResName as -> take 1 (toList' as)
      _                    -> []
    toList' = foldr (:) []

    used    = List.nub [ u | Right u <- uses ]
    skipped = [ why | Left why <- uses, not (null why) ]

    -- qualified uses
    quals :: [Either String Intent]
    quals = concatMap qual occs
    qual (Occurrence x what) = case (x, what) of
      (C.Qual q _, Resolved r qms) ->
        let viaName = [ map norm (lineageTexts (anameLineage a)) | a <- names r ]
            viaQual = [ map norm (lineageTexts (amodLineage am)) | am <- qms ]
            denotesF = any (\ am -> prettyShow (amodName am) == fac) qms
            hit hs = crossing (if denotesF then Just fac else Nothing) hs
            hits = mapMaybe hit (viaName ++ viaQual)
        in case hits of
             [] -> []
             (i : _) -> [ requalify x q i ]
      _ -> []
    requalify x q i = case span' x of
      Nothing -> Left "a qualified name without a range"
      Just (a, b)
        | T.take (b - a) (T.drop a txt) /= T.pack (prettyShow x) -> Left ("a qualified operator: " ++ prettyShow x)
        | tLocal t && i > 0 -> Left "a submodule re-export reached through a chain"
        | otherwise ->
            let rest = drop (length (prettyShow q) + 1) (prettyShow x)
                new | tLocal t  = prettyShow q ++ "." ++ tMod t ++ "." ++ rest
                    | otherwise = tMod t ++ "." ++ rest
            in Right (Replace src (a, b) (T.pack new))
    span' x = case (rStart' (getRange x), rEnd' (getRange x)) of
      (Just s, Just e) -> Just (fromIntegral (posPos s) - 1, fromIntegral (posPos e) - 1)
      _ -> Nothing

    qualIntents = [ i | Right i <- quals ]
    -- `X.x` needs `import X`
    importX | tLocal t || null qualIntents = []
            | otherwise = case importOfFacade of
                Just at -> [ Insert src at (T.pack ("\n" ++ indentAt at ++ "import " ++ tMod t)) ]
                Nothing -> []
    importOfFacade =
      let (pre, rest) = T.breakOn (T.pack ("import " ++ fac)) txt
      in if T.null rest then Nothing
         else let s0 = T.length pre in Just (layoutEnd txt (lineBegin txt s0) (s0 + 7 + length fac))
    indentAt at = let b = lineBegin txt (at - 1) in T.unpack (T.takeWhile isBlank (T.drop b txt))

    skips = skipped ++ [ w | Left w <- quals ] ++
            [ "no import of the facade to put `import X` after" | not (tLocal t), not (null qualIntents), Nothing <- [importOfFacade] ]

    -- per statement: drop its crossing items, add what is used after it
    stmts = List.nub ([ k | (k, _) <- used ] ++ [ k | (k, st) <- Map.toList byKey, not (null (crossingItems st)) ])
    crossingItems st =
      [ it | it@(n, _, _, _) <- osItems st
           , Just hs <- [lookup n (osHops st)]
           , Just _ <- [crossing (Just (target st)) (afterStmt st hs)] ]
    perStmt = concat
      [ stmtIntents k st
      | k <- stmts, Just st <- [Map.lookup k byKey] ]
    stmtIntents k st =
      let items  = [ it | (k', it) <- used, k' == k ]
          spans  = [ sp | (_, r, False, _) <- osItems st, Just sp <- [rspan r] ]
          drops  = [ sp | (_, r, _, _) <- crossingItems st, Just sp <- [rspan r] ]
          modItem = T.pack ("module " ++ tMod t)
          hasMod = any (\ (n, _, _, _) -> T.pack n == modItem) (osItems st)
          adds   = [ modItem | tLocal t, not (null items), not (osWholesale st), not hasMod ]
          group  = [ Group src spans drops adds | not (null spans), not (null drops && null adds) ]
          ms     = maybe 0 (subtract 1) (posOf (osModule st))
          me     = maybe ms (\ p -> fromIntegral (posPos p) - 1) (rEnd' (getRange (osModule st)))
          start  = stmtStart txt ms
          end    = stmtEnd txt st ms me
          ind    = T.unpack (T.takeWhile isBlank (T.drop (lineBegin txt start) txt))
          opener | tLocal t  = "open " ++ tMod t
                 | otherwise = "open import " ++ tMod t
          insert = [ Insert src end (T.pack ("\n" ++ ind ++ opener ++ " using (") <> T.intercalate (T.pack "; ") items <> T.pack ")")
                   | not (null items) ]
      in group ++ insert
    rspan r = case (rStart' r, rEnd' r) of
      (Just s, Just e) -> Just (fromIntegral (posPos s) - 1, fromIntegral (posPos e) - 1)
      _ -> Nothing

    intents = perStmt ++ qualIntents ++ importX

forceTarget :: Either String Target -> Int
forceTarget = \case
  Left why -> length why
  Right (Target f m l (a, b, x)) -> length f + length m + fromEnum l + a + b + T.length x

forceIntents :: [Intent] -> Int
forceIntents = sum . map one
  where
    one = \case
      Group f sps ds as -> length f + sum (map (uncurry (+)) (sps ++ ds)) + sum (map T.length as)
      Insert f a x      -> length f + a + T.length x
      Replace f (a, b) x -> length f + a + b + T.length x

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
    St ts skips intents edited <- readIORef state
    ok <- fmap concat $ forM targets $ \ k@(m, l) -> do
      let name = m ++ ":" ++ show l
      case Map.lookup k ts of
        Nothing -> [] <$ putStrLn ("repair-reexports: " ++ name ++ ": NOT applied: the module was not checked in this run")
        Just (Left why) -> [] <$ putStrLn ("repair-reexports: " ++ name ++ ": NOT applied: " ++ why)
        Just (Right t) -> case Map.findWithDefault [] k skips of
          [] -> do
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
          gEdits = [ groupEdit txt sps (List.nub ds) (List.nub as) | (sps, (ds, as)) <- Map.toList groups ]
          others = [ (a, a, s) | Insert f' a s <- is, f' == f ] ++
                   [ (a, b, s) | Replace f' (a, b) s <- is, f' == f ] ++
                   [ e | (f', e) <- pub, f' == f ]
      applyEdits f (gEdits ++ others)
    writeIORef state $ St Map.empty Map.empty Map.empty Map.empty
  where
    fileOf = \case { Group f _ _ _ -> f; Insert f _ _ -> f; Replace f _ _ -> f }

-- | Rewrite a @using@ group: its items minus the dropped, plus the added.
groupEdit :: T.Text -> [(Int, Int)] -> [(Int, Int)] -> [T.Text] -> Edit
groupEdit txt sps drops adds =
  let s0    = minimum (map fst sps)
      e0    = maximum (map snd sps)
      open  = maybe 0 id (List.find (\ j -> T.index txt j == '(') [s0 - 1, s0 - 2 .. 0])
      close = maybe (T.length txt) id (List.find (\ j -> T.index txt j == ')') [e0 .. T.length txt - 1])
      kept  = [ slice sp | sp <- List.sort sps, sp `notElem` drops ]
  in (open + 1, close, T.intercalate (T.pack "; ") (kept ++ adds))
  where
    slice (a, b) = let a' = withModuleKeyword a in T.take (b - a') (T.drop a' txt)
    withModuleKeyword a =
      let before = T.dropWhileEnd (\ c -> isBlank c || c == '\n') (T.take a txt)
      in if T.pack "module" `T.isSuffixOf` before then T.length before - 6 else a

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
