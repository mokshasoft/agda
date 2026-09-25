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

import Data.List (stripPrefix)

import System.FilePath (makeRelative, normalise)
import System.IO
  ( BufferMode (BlockBuffering), IOMode (WriteMode)
  , hClose, hPutStr, hSetBuffering, hSetEncoding, openFile, stdout, utf8 )

import Agda.Syntax.Common.Pretty (prettyShow)
import Agda.Syntax.Position (HasRange, getRange, rangeFile, rangeFilePath)

import Agda.TypeChecking.DeadCode (pathInProject)
import Agda.TypeChecking.Monad

import Agda.Utils.FileName (filePath)
import qualified Agda.Utils.Maybe.Strict as Strict

---------------------------------------------------------------------------
-- * Output sinks
---------------------------------------------------------------------------

-- | Where a report goes.  Writing through a sink rather than returning a
--   'String' is what lets a long listing be rendered one entry at a time.
type Sink = String -> TCM ()

withOutputSink :: FilePath -> (Sink -> TCM a) -> TCM a
withOutputSink "-" k = k $ liftIO . hPutStr stdout
withOutputSink fp  k = do
  h <- liftIO $ do
    h <- openFile fp WriteMode
    -- Agda types are full of Unicode, and the locale encoding is not to be
    -- trusted: under @LC_ALL=C@ the default handle encoding fails on the
    -- first arrow.
    hSetEncoding h utf8
    hSetBuffering h $ BlockBuffering Nothing
    pure h
  -- TCM is not 'MonadUnliftIO', so the handle is closed by hand on both the
  -- normal and the exceptional path.
  r <- k (liftIO . hPutStr h) `catchError` \ err -> do
         liftIO $ hClose h
         throwError err
  liftIO $ hClose h
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
