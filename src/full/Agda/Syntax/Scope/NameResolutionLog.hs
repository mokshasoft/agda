{-# OPTIONS_GHC -Wunused-imports #-}

-- | The store behind @--name-resolution-report@: every name the scope
--   checker resolved, per source file, until the report for that file is
--   written.  See "Agda.TypeChecking.NameResolutionReport" for the report.
--
--   == Why a global store
--
--   The scope checker logs from 'Agda.Syntax.Scope.Monad.resolveName'', the
--   one funnel every name goes through.  Keeping the log in 'TCState' would
--   put it in the state the checker saves and restores around imports and
--   speculative parsing, and would make every module that depends on
--   'TCState' rebuild.  So it lives in a global 'IORef', as the profile
--   counters do, keyed by the file each occurrence is written in.  An import
--   checked in the middle of scope checking its importer logs under its own
--   file, so nothing interleaves.
--
--   == Duplicates
--
--   The same occurrence is resolved more than once: the operator parser
--   resolves every identifier of an expression to classify it, and the
--   translation to abstract syntax resolves it again, sometimes restricted to
--   constructors.  An occurrence is keyed by its range and what kind of
--   record it is, and the last resolution wins, which is the one the
--   translation made.
module Agda.Syntax.Scope.NameResolutionLog
  ( Occurrence (..)
  , What (..)
  , logEnabled
  , setLogEnabled
  , logOccurrence
  , takeOccurrences
  , OpenStmt (..)
  , logOpen
  , takeOpens
  , amendOpen
  , osOpened
  , resolveOpenItem
  ) where

import Data.IORef
import qualified Data.Map.Strict as Map

import System.IO.Unsafe (unsafePerformIO)

import qualified Agda.Syntax.Abstract.Name as A
import qualified Agda.Syntax.Concrete.Name as C
import Agda.Syntax.Position
import Agda.Syntax.Scope.Base

import Agda.Utils.FileName (filePath)
import qualified Agda.Utils.Maybe.Strict as Strict

-- | One resolved occurrence of a name, as written in the source.
data Occurrence = Occurrence
  { occWritten :: C.QName
      -- ^ The name as written, qualifier included, with its range.
  , occWhat    :: What
  }

-- | What the occurrence resolved to.
data What
  = Resolved ResolvedName [AbstractModule]
      -- ^ A name, and the modules its qualifier denotes (none when it is
      --   unqualified).  The qualifier is looked up separately because
      --   qualified lookup does not go through 'resolveModule', and an
      --   occurrence like @C.x@ is not explained by @x@'s lineage alone.
  | ModuleName AbstractModule
      -- ^ A module name: @open M@, @import M@, @module X = M@.
  | Binder BindingSource A.Name
      -- ^ A variable bound here.  Without these, a constructor that turns
      --   into a pattern variable leaves no record where it was.

-- | The kind of record, part of the key: an occurrence can be both a module
--   name and a name at the same range.
whatTag :: What -> Int
whatTag = \case
  ModuleName{} -> 0
  Resolved{}   -> 1
  Binder{}     -> 2

-- | Key within a file: start, end, kind of record.
type Key = (Word, Word, Int)

{-# NOINLINE enabled #-}
enabled :: IORef Bool
enabled = unsafePerformIO $ newIORef False

{-# NOINLINE store #-}
store :: IORef (Map.Map FilePath (Map.Map Key Occurrence))
store = unsafePerformIO $ newIORef Map.empty

-- | Is resolution being logged?  The one test paid per resolution when the
--   report is off.
logEnabled :: IO Bool
logEnabled = readIORef enabled

setLogEnabled :: Bool -> IO ()
setLogEnabled b = do
  writeIORef enabled b
  writeIORef store Map.empty
  writeIORef openStore Map.empty

-- | Log an occurrence.  One without a range in a file was not written in
--   the source, and is dropped.
logOccurrence :: Occurrence -> IO ()
logOccurrence o = case (rangeFile r, rStart' r, rEnd' r) of
  (Strict.Just f, Just s, Just e) ->
    let key = (fromIntegral (posPos s), fromIntegral (posPos e), whatTag (occWhat o))
    in  modifyIORef' store $
          Map.insertWith Map.union (filePath (rangeFilePath f)) (Map.singleton key o)
  _ -> pure ()
  where r = getRange (occWritten o)

-- | The occurrences logged in a file, in source order, removed from the
--   store.
takeOccurrences :: FilePath -> IO [Occurrence]
takeOccurrences fp = atomicModifyIORef' store $ \ m ->
  (Map.delete fp m, maybe [] Map.elems (Map.lookup fp m))

------------------------------------------------------------------------
-- Open statements, for @--dead-imports@

-- | An @open@ (or @open import@) as the scope checker processed it: what it
--   brings into scope by name, and where.  The module name's range is the
--   one the lineage of every name it brings in starts with
--   ('Agda.Syntax.Scope.Base.Opened'), so a resolution's outermost hop
--   identifies the statement.
data OpenStmt = OpenStmt
  { osModule    :: C.QName
      -- ^ The module as written in the statement, with its range.
  , osPublic    :: Bool
      -- ^ A @public@ re-export: its names serve the importers.
  , osWholesale :: Bool
      -- ^ No @using@ list: it opens everything not hidden.
  , osOpenedNs  :: [(String, [A.QName])]
      -- ^ Everything the statement brings into scope, by the name it is
      --   bound as (consulted for a wholesale statement nothing is used
      --   through: does it open an instance?).
  , osShown     :: Maybe C.QName
      -- ^ For @open M args@: @M@ (the statement opens an anonymous module,
      --   whose generated name 'osModule' is).
  , osItems     :: [(String, Range, Bool, [A.QName])]
      -- ^ The names its @using@ and @renaming@ directives bind, as bound
      --   (a renaming's new name), with the whole entry's range (for a
      --   renaming, @a to b@), whether it is a renaming entry, and what it
      --   resolves to (so that an instance, used without being written, is
      --   recognised).
  }

-- | Everything an open statement brings into scope.
osOpened :: OpenStmt -> [A.QName]
osOpened = concatMap snd . osOpenedNs

-- | A directive item, with what it names among the statement's bindings.
resolveOpenItem :: [(String, [A.QName])] -> (String, Range, Bool) -> (String, Range, Bool, [A.QName])
resolveOpenItem ns (n, r, ren) = (n, r, ren, concat [ as | (c, as) <- ns, c == n ])

-- | Change the logged statement whose module name is this one (same range).
amendOpen :: C.QName -> (OpenStmt -> OpenStmt) -> IO ()
amendOpen x f = case rangeFile (getRange x) of
  Strict.Just file -> modifyIORef' openStore $
    Map.adjust (map (\ o -> if getRange (osModule o) == getRange x then f o else o))
               (filePath (rangeFilePath file))
  Strict.Nothing -> pure ()

{-# NOINLINE openStore #-}
openStore :: IORef (Map.Map FilePath [OpenStmt])
openStore = unsafePerformIO $ newIORef Map.empty

-- | Log an open statement, under the file its module name is written in.
logOpen :: OpenStmt -> IO ()
logOpen o = case rangeFile (getRange (osModule o)) of
  Strict.Just f -> modifyIORef' openStore $
    Map.insertWith (flip (++)) (filePath (rangeFilePath f)) [o]
  Strict.Nothing -> pure ()

-- | The open statements logged in a file, removed from the store.
takeOpens :: FilePath -> IO [OpenStmt]
takeOpens fp = atomicModifyIORef' openStore $ \ m ->
  (Map.delete fp m, Map.findWithDefault [] fp m)

