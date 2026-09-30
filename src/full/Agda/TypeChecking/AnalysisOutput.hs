{-# OPTIONS_GHC -Wunused-imports #-}

-- | Shared output plumbing for the whole-program analyses -- @--write-ast@
--   (see "Agda.TypeChecking.ASTDump") and @--duplicate-types@ (see
--   "Agda.TypeChecking.DuplicateTypes").
--
--   Both write a report that is meant to be committed and reviewed as a
--   diff, so both want the same three things: a sink that can be a file or
--   stdout, a line-oriented JSON writer, and paths and ranges made relative
--   to the project so that a report taken on one machine is comparable with
--   one taken on another.
module Agda.TypeChecking.AnalysisOutput
  ( -- * Output sinks
    Sink
  , withOutputSink
    -- * Reports taken when a run stops
  , Completeness (..)
  , describeStop
  , stateOfErr
    -- * Naming
  , defKind
  , siteLabel
  , siteAnchor
    -- * The project
  , analysisProjectDir
  , setMainSourceDir
  , runProjectDir
    -- * Paths and ranges
  , relativeTo
  , trustedRange
  , oneLine
    -- * Text helpers
  , pad
  , joinArrows
  , joinCommas
    -- * JSON
  , J (..)
  , streamArray
  , indent
  , jField
  , jObjField
  , jArrField
  , joinMembers
  , withComma
  , encodeJ
  , jsonString
  ) where

import Control.Monad.Except (catchError, throwError)
import Control.Monad.IO.Class (liftIO)

import Control.Concurrent (myThreadId)
import qualified Control.Exception as E

import Data.Char (isDigit)
import Data.IORef
import Data.List (stripPrefix)
import Data.Maybe (fromMaybe)

import System.Directory (doesDirectoryExist, doesFileExist, removeFile, renameFile)
import System.FilePath ((</>), makeRelative, normalise, takeDirectory)
import System.IO
  ( BufferMode (BlockBuffering), IOMode (WriteMode)
  , hClose, hPutStr, hSetBuffering, hSetEncoding, openFile, stdout, utf8 )
import System.IO.Unsafe (unsafePerformIO)

import Agda.Syntax.Abstract.Name (ModuleName, QName)
import Agda.Syntax.Common.Pretty (prettyShow)
import Agda.Syntax.Position (HasRange, getRange, rangeFile, rangeFilePath)

import Agda.Interaction.Library (findProjectRoot)
import Agda.TypeChecking.DeadCode (pathInProject)
import Agda.TypeChecking.Monad

import Agda.Utils.FileName (filePath)
import Agda.Utils.Monad (orM)
import qualified Agda.Utils.Maybe.Strict as Strict

---------------------------------------------------------------------------
-- * Output sinks
---------------------------------------------------------------------------

-- | Where a report goes.  Writing through a sink rather than returning a
--   'String' is what lets a long listing be rendered one entry at a time.
type Sink = String -> TCM ()

--   A file is written under a temporary name and renamed into place when
--   complete, so a run killed mid-write leaves the previous report, never a
--   torn one.  The temporary name is the writing thread's own, since a
--   snapshot thread and the main thread may write the same report.  Where no
--   file can be created beside the target -- @/dev/null@, a read-only
--   directory holding a writable file -- the target is written directly.
withOutputSink :: FilePath -> (Sink -> TCM a) -> TCM a
withOutputSink "-" k = k $ liftIO . hPutStr stdout
withOutputSink fp  k = do
  (h, finish, abandon) <- liftIO $ do
    t <- myThreadId
    let tmp = fp ++ ".tmp-" ++ filter isDigit (show t)
    beside <- E.try (openFile tmp WriteMode)
    (h, finish, abandon) <- case beside of
      Right h -> pure (h, renameFile tmp fp, removeFile tmp)
      Left (_ :: E.IOException) -> do
        h <- openFile fp WriteMode
        pure (h, pure (), pure ())
    -- Agda types are full of Unicode, and the locale encoding is not to be
    -- trusted: under @LC_ALL=C@ the default handle encoding fails on the
    -- first arrow.
    hSetEncoding h utf8
    hSetBuffering h $ BlockBuffering Nothing
    pure (h, finish, abandon)
  -- TCM is not 'MonadUnliftIO', so the handle is closed by hand on both the
  -- normal and the exceptional path.
  r <- k (liftIO . hPutStr h) `catchError` \ err -> do
         liftIO $ hClose h >> abandon
         throwError err
  liftIO $ hClose h >> finish
  pure r

---------------------------------------------------------------------------
-- * Reports taken when a run stops
---------------------------------------------------------------------------

-- | Whether the run finished before a report was taken.
--
--   A report is most needed for a run that does not finish -- a module that
--   runs out of heap, or is interrupted after an hour -- so the measuring
--   reports are also written when a run stops, and say so.
data Completeness
  = Complete
  | Incomplete String
      -- ^ The run stopped; says what stopped it.
  | Snapshot Integer
      -- ^ The run is still going; this many seconds in.

-- | The state an error was raised in, for the errors that carry one.
--
--   By the time an error reaches a handler the live state has usually been
--   rolled back ('catchError' restores it), so this copy is the one that
--   still holds what was done before the error.
stateOfErr :: TCErr -> Maybe TCState
stateOfErr = \case
  TypeError{ tcErrState = s } -> Just s
  IOException (Just s) _ _    -> Just s
  _                           -> Nothing

-- | What stopped a run, as a report states it.
describeStop :: TCErr -> String
describeStop = \case
  TypeError{}   -> "type error"
  IOException{} -> "IO error"
  _             -> "error"

---------------------------------------------------------------------------
-- * Naming
---------------------------------------------------------------------------

-- | How a report names a kind of definition.
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

-- | How a report names a site.  A check after a mutual block is named by
--   what it is and the block's first definition, @[termination] M.f@.
siteLabel :: ProfileSite -> String
siteLabel = \case
  SiteDefinition q  -> prettyShow q
  SiteApplication m -> prettyShow m
  SiteCheck c q     -> "[" ++ c ++ "] " ++ prettyShow q

-- | What locates a site in the source: the definition, the module applied
--   to, or the first definition of the checked block.
siteAnchor :: ProfileSite -> Either ModuleName QName
siteAnchor = \case
  SiteDefinition q  -> Right q
  SiteApplication m -> Left m
  SiteCheck _ q     -> Right q

---------------------------------------------------------------------------
-- * The project
---------------------------------------------------------------------------

-- | The root of the git repository containing the given directory, if any.
--
--   This is what delimits "the project" for @--dead-code@ and @--write-ast@:
--   a repository is the unit the user can actually edit, whereas an
--   @.agda-lib@ may sit in a subdirectory or be absent altogether.
--   A @.git@ entry may be a directory or, in a worktree or submodule, a file.
gitRepoRoot :: FilePath -> IO (Maybe FilePath)
gitRepoRoot = go (256 :: Int)
  where
    go 0 _   = pure Nothing
    go n dir = do
      let dotGit = dir </> ".git"
      found <- orM [ doesDirectoryExist dotGit, doesFileExist dotGit ]
      if found then pure (Just dir) else do
        let up = takeDirectory dir
        if up == dir then pure Nothing else go (n - 1) up

-- | Directory delimiting the project for the reachability analyses:
--   the enclosing git repository, else the @.agda-lib@ location, else the
--   source file's own directory.
analysisProjectDir :: FilePath -> TCM FilePath
analysisProjectDir srcDir = do
  mGit <- liftIO $ gitRepoRoot srcDir
  case mGit of
    Just root -> pure root
    Nothing   -> fromMaybe srcDir <$> libToTCM (findProjectRoot srcDir)

-- | The directory of the run's main module.  Set when checking of the main
--   module starts; see 'runProjectDir'.
{-# NOINLINE mainSourceDir #-}
mainSourceDir :: IORef (Maybe FilePath)
mainSourceDir = unsafePerformIO $ newIORef Nothing

setMainSourceDir :: FilePath -> IO ()
setMainSourceDir = writeIORef mainSourceDir . Just

-- | The project of the run: the one its main module is in.
--
--   A report written when an imported module stops is taken inside that
--   module, whose own directory may delimit a different project -- a
--   library's, or a subdirectory when there is neither a repository nor an
--   @.agda-lib@.  Scoping every report by the main module is what makes a
--   partial report cover the same sections as a complete one.  The argument
--   is used when no main module has been recorded.
runProjectDir :: FilePath -> TCM FilePath
runProjectDir fallback =
  analysisProjectDir . fromMaybe fallback =<< liftIO (readIORef mainSourceDir)

---------------------------------------------------------------------------
-- * Paths and ranges
---------------------------------------------------------------------------

-- | Report paths relative to the project, so that a report taken on one
--   machine is comparable with one taken on another.
relativeTo :: FilePath -> FilePath -> FilePath
relativeTo projectDir p
  | pathInProject projectDir p = makeRelative (normalise projectDir) p
  | otherwise                  = p

-- | Source range of a name, with the file made relative to the project.
--
--   A range on an imported name can point at the /importing/ file (see
--   'Agda.TypeChecking.DeadCode.moduleFileTable'), so a range is reported
--   only when it agrees with the module-resolved source file.  The same
--   holds for the name of a module.
trustedRange :: HasRange a => FilePath -> Maybe FilePath -> a -> String
trustedRange projectDir msrc x = case rangeFile (getRange x) of
  Strict.Nothing -> ""
  Strict.Just rf
    | Just (normalise printed) /= fmap normalise msrc -> ""
    | otherwise -> maybe full (relativeTo projectDir printed ++) $
                     stripPrefix printed full
    where
      printed = filePath (rangeFilePath rf)
      full    = prettyShow (getRange x)

-- | Collapse a pretty-printed type onto a single line.  'prettyTCM' wraps
--   long types, which would otherwise break the line-oriented text format
--   and turn a JSON entry into an unreadable run of escaped newlines.
oneLine :: String -> String
oneLine = unwords . words

---------------------------------------------------------------------------
-- * Text helpers
---------------------------------------------------------------------------

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
-- * JSON
---------------------------------------------------------------------------

-- A tiny hand-rolled JSON writer.  Using aeson here would work, but the
-- output shape is trivial and this keeps the analyses free of version-
-- dependent @Key@/@Value@ differences between aeson 1.x and 2.x.
--
-- The layout is one entry per line: the document is indented enough to be
-- read, but an entry is not spread over a dozen lines, so a diff between two
-- reports has one changed line per changed entry.

data J = JStr String | JNum Int | JBool Bool | JArr [J] | JObj [(String, J)] | JNull

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
