{-# OPTIONS_GHC -Wunused-imports #-}

-- | @--dead-imports[=FILE]@ and @--remove-dead-imports@: the names a module's
--   @open@/@import@ directives bring into scope that the module never uses.
--
--   Per module, with no entry point (unlike @--dead-code@): an item of a
--   @using@ or @renaming@ directive is DEAD when no name the module resolves
--   came into scope through it.  The scope checker already records why each
--   resolved name is in scope (its lineage); the outermost hop of a lineage
--   is the @open@ that brought the name in, identified by the range of the
--   module name in that statement.  So:
--
--   * the open statements are logged as the scope checker processes them
--     ('Agda.Syntax.Scope.Monad.openModule'), with their items;
--   * every resolution of the module contributes (statement, name) pairs —
--     its own lineage's outermost hop, and its qualifier's (@R.f@ uses the
--     item @R@ that brought module @R@ in);
--   * an item no pair names is dead.
--
--   Kept although nothing names them: @public@ re-exports (their users are
--   the importers) and items naming an instance (instance search uses them
--   without a written occurrence).
--
--   @--remove-dead-imports@ rewrites the module's source IN PLACE: dead items
--   leave their directive, and a statement left opening nothing is deleted,
--   or becomes @import M@ when @M@ is still used qualified.  The source
--   changes, so the next run re-checks exactly the rewritten modules: that run
--   is the verification.

module Agda.TypeChecking.DeadImports
  ( startDeadImports
  , finishDeadImports
  , deadImportsWanted
  , deadImportsFor
    -- * Shared with @--repair-reexports@
  , Edit, readSource, applyEdits, posOf, isBlank
  ) where

import Control.Monad (forM, when)
import Control.Monad.IO.Class (liftIO)
import Data.IORef (IORef, newIORef, modifyIORef', atomicModifyIORef')
import System.IO.Unsafe (unsafePerformIO)
import qualified Data.List as List
import qualified Data.List.NonEmpty as NE
import Data.Maybe (isJust, mapMaybe)
import qualified Data.Set as Set
import qualified Data.Text as T
import qualified Data.Text.IO as T
import System.FilePath (takeDirectory)
import System.IO

import Agda.Syntax.Common.Pretty (prettyShow)
import qualified Agda.Syntax.Concrete.Name as C
import Agda.Syntax.Abstract.Name (QName)
import Agda.Syntax.Position
import Agda.Syntax.Scope.Base
import Agda.Syntax.Scope.NameResolutionLog

import Agda.Interaction.Options.Types (optDeadImportsFile, optRemoveDeadImports)
import Agda.TypeChecking.AnalysisOutput (J (..), encodeJ, relativeTo, runProjectDir)
import Agda.TypeChecking.Monad

import Agda.Utils.FileName (filePath)
import qualified Agda.Utils.Maybe.Strict as Strict

-- | Is either mode on?  (Logging must then be on.)
deadImportsWanted :: TCM Bool
deadImportsWanted = do
  o <- commandLineOptions
  return $ isJust (optDeadImportsFile o) || optRemoveDeadImports o

-- | At the start of a run: the report file's header.
startDeadImports :: TCM ()
startDeadImports = do
  out <- optDeadImportsFile <$> commandLineOptions
  case out of
    Nothing -> pure ()
    Just fp -> liftIO $ withSink WriteMode fp $ \ h ->
      hPutStrLn h $ encodeJ $ JObj
        [ ("schema", JNum 1), ("report", JStr "dead-imports") ]

-- | After scope checking a module: its dead import items, reported and/or
--   removed.  Takes the module's occurrences (shared with the
--   name-resolution report) and its logged open statements.
deadImportsFor :: TopLevelModuleName -> FilePath -> [Occurrence] -> [OpenStmt] -> TCM ()
deadImportsFor m src occs opens = do
  wanted <- deadImportsWanted
  when wanted $ do
    let used = usedPairs occs
        quals = qualifiersUsed occs
    let usedKeys = Set.map fst used
    dead <- fmap concat $ forM opens $ \ st -> do
      let key = posOf (osModule st)
      if osPublic st || key == Nothing then return [] else
       if osWholesale st then
        -- a wholesale open is dead only as a whole (dropping one renaming
        -- would open that name under its own name instead), and only if it
        -- opens no instance
        if key `Set.member` usedKeys then return [] else do
          inst <- or <$> mapM isInstanceName (osOpened st)
          return [ (st, wholeStatement st) | not inst ]
       else do
        cands <- return [ it | it@(n, _, _, _) <- osItems st, (key, n) `Set.notMember` used ]
        -- an instance is used by instance search, unwritten: keep it
        ds <- filterM' (\ (_, _, _, qs) -> not . or <$> mapM isInstanceName qs) cands
        return [ (st, d) | not (null ds), d <- ds ]
    o <- commandLineOptions
    case optDeadImportsFile o of
      Nothing -> pure ()
      Just fp -> do
        projectDir <- runProjectDir (takeDirectory src)
        liftIO $ withSink AppendMode fp $ \ h ->
          mapM_ (hPutStrLn h . encodeJ . record projectDir (prettyShow m)) dead
    when (optRemoveDeadImports o && not (null dead)) $
      liftIO $ do
        -- the edits are computed now (the source is not touched before the
        -- end of the run) so that nothing of the scope is kept alive
        e <- planEdits src quals opens (groupByStmt dead)
        length e `seq` modifyIORef' pendingRewrites (e :)
  where
    filterM' p = fmap concat . mapM (\ x -> (\ b -> [ x | b ]) <$> p x)

-- | The marker for a statement dead as a whole (a wholesale open).
wholeStatement :: OpenStmt -> (String, Range, Bool, [QName])
wholeStatement st = ("", getRange (osModule st), False, [])

isWholeStatement :: (String, Range, Bool, [QName]) -> Bool
isWholeStatement (n, _, _, _) = null n

-- | The in-place rewrites, applied at the end of the run: rewriting a source
--   while the run goes on would make Agda check it again.
{-# NOINLINE pendingRewrites #-}
pendingRewrites :: IORef [(FilePath, [Edit])]
pendingRewrites = unsafePerformIO $ newIORef []

finishDeadImports :: TCM ()
finishDeadImports = liftIO $ do
  rs <- atomicModifyIORef' pendingRewrites (\ rs -> ([], rs))
  mapM_ (uncurry applyEdits) (reverse rs)

isInstanceName :: QName -> TCM Bool
isInstanceName q = either (const False) (isJust . defInstance) <$> getConstInfo' q

-- | A position's offset in its file.
posOf :: HasRange a => a -> Maybe Int
posOf x = fromIntegral . posPos <$> rStart' (getRange x)

-- | The (statement, name) pairs the module's resolutions went through.
usedPairs :: [Occurrence] -> Set.Set (Maybe Int, String)
usedPairs = Set.fromList . concatMap pairs
  where
    pairs (Occurrence x what) = case what of
      Resolved r quals ->
        [ (posOf h, lastName x) | a <- names r, Just h <- [outermost (anameLineage a)] ] ++
        concat [ [ (posOf h, firstName x), (posOf h, qualifierText x) ]
               | q <- quals, Just h <- [outermost (amodLineage q)] ]
      ModuleName am ->
        [ p | Just h <- [outermost (amodLineage am)]
            , p <- [ (posOf h, firstName x), (posOf h, prettyShow x) ] ]
      Binder{} -> []
    names = \case
      DefinedName _ a _    -> [a]
      FieldName as         -> NE.toList as
      ConstructorName _ as -> NE.toList as
      PatternSynResName as -> NE.toList as
      _                    -> []

-- | The first components of the qualifiers the module writes (@M@ in @M.x@):
--   a module still used qualified must stay imported.
qualifiersUsed :: [Occurrence] -> Set.Set String
qualifiersUsed = Set.fromList . mapMaybe q
  where
    q (Occurrence x _) = case x of
      C.Qual{} -> Just (qualifierText x)
      _        -> Nothing

outermost :: WhyInScope -> Maybe C.QName
outermost = \case
  Opened q _  -> Just q
  Applied q _ -> Just q
  Defined     -> Nothing

lastName, firstName, qualifierText :: C.QName -> String
lastName      = prettyShow . C.unqualify
firstName     = \case { C.Qual m _ -> prettyShow m; C.QName n -> prettyShow n }
qualifierText = \case
  C.Qual m q -> go (prettyShow m) q
  C.QName n  -> prettyShow n
  where go acc = \case { C.Qual m q -> go (acc ++ "." ++ prettyShow m) q; C.QName _ -> acc }

------------------------------------------------------------------------
-- The report

record :: FilePath -> String -> (OpenStmt, (String, Range, Bool, [QName])) -> J
record projectDir m (st, (n, r, ren, _)) = JObj $
  [ ("module", JStr m) ] ++ rangeFields projectDir r ++
  [ ("name", JStr (if null n then shown else n))
  , ("kind", JStr (if null n then "statement" else if ren then "renaming" else "using"))
  , ("opened", JStr shown) ]
  where shown = prettyShow (maybe (osModule st) id (osShown st))

rangeFields :: FilePath -> Range -> [(String, J)]
rangeFields projectDir r = case (rStart' r, rEnd' r) of
  (Just s, Just e) ->
    [ ("file", JStr (relativeTo projectDir (filePath (rangeFilePath f))))
    | Strict.Just f <- [rangeFile r] ] ++
    [ ("line", num (posLine s)), ("col", num (posCol s))
    , ("endLine", num (posLine e)), ("endCol", num (posCol e)) ]
  _ -> []
  where num = JNum . fromIntegral

withSink :: IOMode -> FilePath -> (Handle -> IO ()) -> IO ()
withSink _    "-" k = k stdout >> hFlush stdout
withSink mode fp  k = withFile fp mode $ \ h -> hSetEncoding h utf8 >> k h

------------------------------------------------------------------------
-- In place

groupByStmt :: [(OpenStmt, a)] -> [(OpenStmt, [a])]
groupByStmt xs =
  [ (st, [ a | (st', a) <- xs, key st' == key st ])
  | st <- List.nubBy (\ a b -> key a == key b) (map fst xs) ]
  where key = posOf . osModule

-- | An edit: replace the characters [from, to) (0-based) with a text.
type Edit = (Int, Int, T.Text)

readSource :: FilePath -> IO T.Text
readSource src = withFile src ReadMode $ \ h -> hSetEncoding h utf8 >> T.hGetContents h >>= \ t -> T.length t `seq` return t

-- | Apply a file's edits (non-overlapping; applied back to front).
applyEdits :: FilePath -> [Edit] -> IO ()
applyEdits _   []    = pure ()
applyEdits src edits = do
  txt <- readSource src
  let txt' = foldr apply txt (List.sortOn (\ (a, _, _) -> a) edits)
  withFile src WriteMode $ \ h -> hSetEncoding h utf8 >> T.hPutStr h txt'
  where
    apply (a, b, new) t = T.take a t <> new <> T.drop b t

planEdits :: FilePath -> Set.Set String -> [OpenStmt] -> [(OpenStmt, [(String, Range, Bool, [QName])])] -> IO (FilePath, [Edit])
planEdits src quals opens deadByStmt = do
  txt <- readSource src
  -- a module some statement still opens is in scope: a dead statement on it
  -- need not become @import M@ to keep @M.x@ working
  let key = posOf . osModule
      deadCount st = maybe 0 length (lookup (key st) [ (key st', ds) | (st', ds) <- deadByStmt ])
      wholeDead st = any (any isWholeStatement) (lookup (key st) [ (key st', ds) | (st', ds) <- deadByStmt ])
      survives st
        | osPublic st    = True
        | osWholesale st = not (wholeDead st)
        | otherwise      = length (osItems st) > deadCount st
      keptMods = Set.fromList [ prettyShow (osModule st) | st <- opens, survives st ]
      quals' = quals `Set.difference` keptMods
  let edits = concatMap (stmtEdits txt quals') deadByStmt
  -- forced: the edits must not hold on to the scope
  sum [ a + b + T.length t | (a, b, t) <- edits ] `seq` return (src, edits)

-- | The edits for one statement: each directive group (using / renaming)
--   with a dead item is rewritten to its kept items; a statement left opening
--   nothing is deleted, or becomes @import M@.
stmtEdits :: T.Text -> Set.Set String -> (OpenStmt, [(String, Range, Bool, [QName])]) -> [Edit]
stmtEdits txt quals (st, dead) =
  case (posOf (osModule st), rEnd' (getRange (osModule st))) of
    (Just mstart, Just mendP) ->
      let mend      = fromIntegral (posPos mendP) - 1
          deadRs    = Set.fromList [ rangeSpan r | (_, r, _, _) <- dead ]
          group ren = [ it | it@(_, _, g, _) <- osItems st, g == ren ]
          kept ren  = [ slice r | (_, r, g, _) <- osItems st, g == ren, rangeSpan r `Set.notMember` deadRs ]
          groupEdit ren = case group ren of
            [] -> []
            its | all (\ (_, r, _, _) -> rangeSpan r `Set.notMember` deadRs) its -> []
                | otherwise ->
                    let s0 = minimum [ a | (_, r, _, _) <- its, Just (a, _) <- [rangeSpan r] ]
                        e0 = maximum [ b | (_, r, _, _) <- its, Just (_, b) <- [rangeSpan r] ]
                        open  = lastIndexBefore '(' s0
                        close = firstIndexFrom ')' e0
                        kw    = T.dropWhileEnd isSpaceNl (T.take open txt)
                    in if ren && null (kept ren) && T.pack "renaming" `T.isSuffixOf` kw
                         -- no renaming left: the group goes, keyword and all
                         -- (an empty `using ()` stays: it means "only these")
                         then [ (T.length (T.dropWhileEnd isBlank (T.take (T.length kw - 8) txt)), close + 1, T.empty) ]
                         else [ (open + 1, close, T.intercalate (T.pack "; ") (kept ren)) ]
          nothingLeft
            | osWholesale st = any isWholeStatement dead
            | otherwise      = null (kept False) && null (kept True)
          modText = T.pack (prettyShow (osModule st))
      in if nothingLeft
           then case stmtSpan (mstart - 1) mend of
                  Just (a, b, isImport)
                    -- `import M as Q`: the alias may be used, keep the statement
                    | hasAlias mend b -> groupEdit False ++ groupEdit True
                    | isImport && prettyShow (osModule st) `Set.member` quals -> [ (a, b, T.pack "import " <> modText) ]
                    | otherwise -> [ (lineStart a, lineEnd b, T.empty) ]
                  Nothing -> groupEdit False ++ groupEdit True
           else groupEdit False ++ groupEdit True
    _ -> []
  where
    rangeSpan r = case (rStart' r, rEnd' r) of
      (Just s, Just e) -> Just (fromIntegral (posPos s) - 1, fromIntegral (posPos e) - 1)
      _                -> Nothing
    -- an item's range is its name; a @module X@ item keeps its keyword
    slice r = case rangeSpan r of
      Just (a, b) -> let a' = withModuleKeyword a in T.take (b - a') (T.drop a' txt)
      Nothing     -> T.empty
    withModuleKeyword a =
      let before = T.dropWhileEnd isSpaceNl (T.take a txt)
      in if T.pack "module" `T.isSuffixOf` before then T.length before - 6 else a
    lastIndexBefore c i = maybe 0 id $ List.find (\ j -> T.index txt j == c) [i - 1, i - 2 .. 0]
    firstIndexFrom  c i = maybe (T.length txt) id $ List.find (\ j -> T.index txt j == c) [i .. T.length txt - 1]
    -- the whole statement: back from the module name over `open [import]`,
    -- forward to the last `)` of its directives on the following lines
    stmtSpan ms me =
      let before = T.reverse (T.take ms txt)
          ws     = T.length (T.takeWhile isBlank before)
          rest1  = T.drop ws before
          (isImport, rest2)
            | T.pack "tropmi" `T.isPrefixOf` rest1 =
                (True, let r = T.drop 6 rest1 in T.drop (T.length (T.takeWhile isBlank r)) r)
            | otherwise = (False, rest1)
      in if T.pack "nepo" `T.isPrefixOf` rest2
           then let start = ms - (T.length before - T.length rest2) - 4
                    end   = closeOfStmt start me
                -- only a statement that starts its line (not `let open M in`)
                in if startsLine start then Just (start, end, isImport) else Nothing
           else Nothing
    -- the statement ends at its last directive's `)`, or at the end of the line
    closeOfStmt start me
      | null (osItems st) = layoutEnd start me
      | otherwise =
          let lastItem = maximum (me : [ b | (_, r, _, _) <- osItems st, Just (_, b) <- [rangeSpan r] ])
          in min (firstIndexFrom ')' lastItem + 1) (T.length txt)
    -- without directive items (a wholesale open, maybe applied to arguments
    -- or with `hiding`): the statement runs on over the lines indented more
    -- than its `open`
    layoutEnd start me =
      let col     = start - lineBegin start
          eol i   = maybe (T.length txt) (+ i) (T.findIndex (== '\n') (T.drop i txt))
          go e | e >= T.length txt = e
               | otherwise =
                   let nxt  = e + 1
                       line = T.takeWhile (/= '\n') (T.drop nxt txt)
                       ind  = T.length (T.takeWhile isBlank line)
                   in if not (T.all isBlank line) && ind > col then go (eol nxt) else e
      in go (eol me)
    lineBegin i = maybe 0 (\ k -> i - k) (T.findIndex (== '\n') (T.reverse (T.take i txt)))
    startsLine i = T.all isBlank (T.take (i - lineBegin i) (T.drop (lineBegin i) txt))
    -- a statement that was the whole line takes the line with it: its
    -- indentation (else it would join the next line and break the layout)
    -- and its newline
    lineStart a =
      let ind = T.length (T.takeWhileEnd isBlank (T.take a txt))
          at  = a - ind
      in if at == 0 || T.index txt (at - 1) == '\n' then at else a
    -- (with a trailing comment, which was about the statement)
    lineEnd b =
      let rest = T.takeWhile (/= '\n') (T.drop b txt)
          gap  = T.takeWhile isBlank rest
          tailOk = T.null (T.drop (T.length gap) rest) || T.pack "--" `T.isPrefixOf` T.drop (T.length gap) rest
          e = b + T.length rest
      in if tailOk then (if e < T.length txt then e + 1 else e) else b
    -- the words between the module name and the directives include `as`
    hasAlias me b =
      let ws = takeWhile (`notElem` map T.pack ["using", "renaming", "hiding", "public"])
                 (T.words (T.map (\ c -> if c == '(' then ' ' else c) (T.take (b - me) (T.drop me txt))))
      in T.pack "as" `elem` ws

isBlank, isSpaceNl :: Char -> Bool
isBlank   c = c == ' ' || c == '\t'
isSpaceNl c = isBlank c || c == '\n'
