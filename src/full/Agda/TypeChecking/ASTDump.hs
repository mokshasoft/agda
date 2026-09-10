{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wunused-imports #-}

-- | Dump the portion of the internal syntax reachable from a given entry
--   point, together with the trust base (postulates and other assumptions)
--   that the entry point depends on.
--
--   This is a /lens/ into the elaborated signature: it reports what the
--   entry point actually depends on, at definition granularity rather than
--   module granularity.  It deliberately does not decide what is safe to
--   delete -- that requires project-specific knowledge Agda does not have.
--
--   Note on completeness: the reachable set is computed from the elaborated
--   internal syntax, so it captures semantic dependencies of the proof term.
--   Some source-level dependencies leave no trace there and are therefore
--   reported separately as /ambient/ assumptions rather than as reachable
--   definitions:
--
--     * rewrite rules apply during conversion checking and are never
--       name-referenced (see the note in "Agda.TypeChecking.DeadCode");
--     * macros are expanded at elaboration time, so the expansion is
--       reachable but the macro itself is not;
--     * @BUILTIN@ bindings live in a separate table.

module Agda.TypeChecking.ASTDump
  ( writeASTDump
  ) where

import Control.Monad.IO.Class (liftIO)

import Data.Foldable (foldl')
import Data.List (sortOn, isPrefixOf)
import Data.Maybe (isJust)
import qualified Data.HashMap.Strict as HMap
import qualified Data.Map.Strict as MapS
import qualified Data.Sequence as Seq
import qualified Data.Set as Set

import System.FilePath (isRelative, makeRelative, normalise)

import Agda.Syntax.Builtin (getBuiltinId)
import Agda.Syntax.Common.Pretty (prettyShow, render)
import Agda.Syntax.Internal
import Agda.Syntax.Internal.Names (namesIn)
import Agda.Syntax.Position (getRange, rangeFile, rangeFilePath)

import Agda.Interaction.Options.Base (unsafePragmaOptions)
import Agda.Interaction.Options.Types (ASTFormat (..))
import Agda.TypeChecking.DeadCode
  ( ModuleFileTable, moduleFileTable, sourceOfQName, qnameInProject )

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Pretty (prettyTCM)
import Agda.TypeChecking.Warnings (warning)

import Agda.Utils.FileName (filePath)
import Agda.Utils.Lens
import qualified Agda.Utils.List1 as List1
import qualified Agda.Utils.Maybe.Strict as Strict
import qualified Agda.Utils.SmallSet as SmallSet

---------------------------------------------------------------------------
-- * Reachability
---------------------------------------------------------------------------

-- | Breadth-first reachability from the entry point, recording for each name
--   the predecessor that first discovered it.  BFS (rather than the DFS used
--   by "Agda.TypeChecking.DeadCode") means the recorded witness path is the
--   shortest one, which is also the most readable.
--
--   Unlike 'checkUnreachableDefinitions' this traverses /everything/,
--   including external libraries.  Restricting the traversal to the project
--   would under-approximate: a postulate reached through a standard library
--   higher-order function would be silently missed, and for a trust-base
--   report a false negative is much worse than a false positive.
reachableFrom :: Definitions -> QName -> HMap.HashMap QName QName
reachableFrom defs root = go (HMap.singleton root root) (Seq.singleton root)
  where
    go !seen q = case Seq.viewl q of
      Seq.EmptyL      -> seen
      x Seq.:< rest ->
        let deps            = maybe [] namesIn (HMap.lookup x defs) :: [QName]
            (seen', newRev) = foldl' step (seen, []) deps
            step (s, acc) y
              | HMap.member y s = (s, acc)
              | otherwise       = (HMap.insert y x s, y : acc)
        in go seen' (rest Seq.>< Seq.fromList (reverse newRev))

-- | Reconstruct the witness path from the entry point to a name.
witnessPath :: HMap.HashMap QName QName -> QName -> QName -> [QName]
witnessPath preds root = walk (0 :: Int) []
  where
    walk n acc y
      | y == root  = root : acc
      | n > 100000 = y : acc   -- cycle guard; should be unreachable
      | otherwise  = case HMap.lookup y preds of
          Nothing            -> y : acc
          Just p | p == y    -> y : acc
                 | otherwise -> walk (n + 1) (y : acc) p

---------------------------------------------------------------------------
-- * Classification
---------------------------------------------------------------------------

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

-- | Markers that make a definition part of the trust base, i.e. things that
--   @--safe@ would reject or that otherwise represent an unproven assumption.
--
--   Ordinary primitives are deliberately /not/ flagged: @--safe@ permits them,
--   and flagging them would bury the real assumptions under every arithmetic
--   builtin the entry point happens to reach.  Only the two primitives that
--   are genuinely unsound are reported.
safetyMarkers :: Definition -> [String]
safetyMarkers d = concat
  [ [ "postulate"               | isAxiom (theDef d)                 ]
  , [ "unsafe-primitive"        | isUnsafePrimitive (theDef d)       ]
  , [ "injective-pragma"        | defInjective d                     ]
  , [ "termination-unconfirmed" | defTerminationUnconfirmed d        ]
  , [ "macro"                   | isMacro (theDef d)                 ]
  , map pragmaMarker $ SmallSet.toList $ defUnsafePragmas d
  ]
  where
    isAxiom = \case { Axiom{} -> True; _ -> False }
    pragmaMarker = \case
      UnsafeNoPositivityCheck -> "no-positivity-check"
      UnsafeNoUniverseCheck   -> "no-universe-check"
      UnsafeNonCovering       -> "non-covering"
      UnsafeTerminating       -> "terminating-pragma"
      UnsafeNonTerminating    -> "non-terminating-pragma"
    isUnsafePrimitive = \case
      Primitive{ primName = p } ->
        prettyShow p `elem` [ "primTrustMe", "primEraseEquality" ]
      _ -> False

---------------------------------------------------------------------------
-- * Rendered entries
---------------------------------------------------------------------------

data Entry = Entry
  { eQName    :: QName
  , eName     :: String
  , eKind     :: String
  , eType     :: String
  , eSource   :: Maybe FilePath
  , eSrcRange    :: String
  , eExternal :: Bool
  , eMarkers  :: [String]
  , eDeps     :: [String]
  , ePath     :: [String]
  }

mkEntry
  :: FilePath
  -> ModuleFileTable
  -> Definitions
  -> HMap.HashMap QName QName
  -> QName
  -> QName
  -> TCM Entry
mkEntry projectDir modTable defs preds root x = do
  let mdef     = HMap.lookup x defs
      external = not (qnameInProject projectDir modTable x)

  -- Postulates in Agda's own builtin modules are sanctioned by @--safe@
  -- (see 'Agda.Syntax.Translation.ConcreteToAbstract.niceDecls'), so they are
  -- not assumptions the user can discharge.  Reporting them would put
  -- Agda.Primitive.Level in the trust base of every single project.
  --
  -- The file-based predicate covers Agda/Builtin/*.agda, but definitions in
  -- Agda.Primitive are constructed internally and carry no range at all, so
  -- they are matched on the module name instead.  These are exactly the two
  -- 'Agda.Interaction.Library.primitiveModules'.
  sanctioned <- case rangeFile (getRange x) of
    Strict.Just rf -> isBuiltinModuleWithSafePostulates =<< idFromFile (rangeFilePath rf)
    Strict.Nothing -> pure $ prettyShow (qnameModule x) `elem`
      [ "Agda.Primitive", "Agda.Primitive.Cubical" ]
  let markers0 = maybe [] safetyMarkers mdef
      markers | sanctioned = filter (/= "postulate") markers0
              | otherwise  = markers0

      -- A range on an imported name can point at the /importing/ file (see
      -- 'moduleFileTable'), so only report one that agrees with the
      -- module-resolved source file.  Otherwise report just the file.
      rangeFileOf = case rangeFile (getRange x) of
        Strict.Just rf -> Just $ normalise $ filePath (rangeFilePath rf)
        Strict.Nothing -> Nothing
      trustedRange
        | isJust rangeFileOf, rangeFileOf == sourceOfQName modTable x
                    = prettyShow (getRange x)
        | otherwise = ""
  ty <- case mdef of
    Nothing -> pure ""
    Just d  -> render <$> prettyTCM (defType d)
  let deps
        -- External definitions are emitted as boundary stubs: including their
        -- dependency lists would balloon the dump with standard library
        -- internals without telling the user anything about their project.
        | external  = []
          -- Self-references are kept: they are how self-recursion appears, and
          -- the graph is cyclic anyway (mutual blocks give genuine cycles).
        | otherwise = map prettyShow $ Set.toAscList $
                        Set.fromList $ maybe [] namesIn mdef
  pure Entry
    { eQName    = x
    , eName     = prettyShow x
    , eKind     = maybe "unknown" (defKind . theDef) mdef
    , eType     = ty
    , eSource   = sourceOfQName modTable x
    , eSrcRange    = trustedRange
    , eExternal = external
    , eMarkers  = markers
    , eDeps     = deps
    , ePath     = map prettyShow $ witnessPath preds root x
    }

---------------------------------------------------------------------------
-- * Ambient assumptions
---------------------------------------------------------------------------

data Ambient = Ambient
  { amRewriteRules :: [String]
  , amBuiltins     :: [String]
  , amUnsafeOpts   :: [(String, [String])]
  }

collectAmbient :: TCM Ambient
collectAmbient = do
  sig      <- getSignature
  impSig   <- useTC stImports
  builtins <- useTC stLocalBuiltins
  visited  <- getVisitedModules

  let rules = concatMap (map (prettyShow . rewName)) $
                HMap.elems (sig ^. sigRewriteRules) ++
                HMap.elems (impSig ^. sigRewriteRules)

      unsafeOpts =
        [ (prettyShow m, flags)
        | (m, mi) <- MapS.toList visited
        , let flags = unsafePragmaOptions (iOptionsUsed (miInterface mi))
        , not (null flags)
        ]

  pure Ambient
    { amRewriteRules = rules
    , amBuiltins     = map getBuiltinId $ MapS.keys builtins
    , amUnsafeOpts   = unsafeOpts
    }

---------------------------------------------------------------------------
-- * Entry point
---------------------------------------------------------------------------

-- | Compute the reachable set from the given root and write it out.
writeASTDump :: FilePath -> FilePath -> ASTFormat -> QName -> TCM ()
writeASTDump projectDir outFile format root = do
  sig    <- getSignature
  impSig <- useTC stImports
  let defs = HMap.union (sig ^. sigDefinitions) (impSig ^. sigDefinitions)

  let preds = reachableFrom defs root
      names = sortOn prettyShow $ HMap.keys preds

  modTable <- moduleFileTable
  allEntries <- mapM (mkEntry projectDir modTable defs preds root) names
  ambient    <- collectAmbient

  -- Only definitions inside the project (the enclosing git repository) are
  -- listed: nothing else can be edited or deleted, so listing the standard
  -- library would only add noise.  External definitions are still traversed --
  -- dropping the edges would be wrong -- and an external one is still listed
  -- when it is an assumption, because a library postulate is every bit as much
  -- part of the trust base as one of your own.
  let entries  = filter (not . eExternal) allEntries
      assumed  = filter (not . null . eMarkers) allEntries

  -- Surface the trust base in the compiler output as well as in the dump:
  -- it is the actionable part, and it is what makes the feature visible in
  -- an editor or CI log rather than only in a file nobody opens.
  List1.unlessNull
    [ (eQName e, unwords (eMarkers e)) | e <- entries, not (null (eMarkers e)) ]
    $ \ xs -> warning $ ReachableTrustBase xs

  let rendered = case format of
        ASTFormatJSON -> renderJSON root (length allEntries) entries assumed ambient
        ASTFormatText -> renderText root (length allEntries) entries assumed ambient

  if outFile == "-"
    then liftIO $ putStr rendered
    else do
      liftIO $ writeFile outFile rendered
      reportSLn "tc.ast.dump" 10 $
        "Wrote AST dump for " ++ prettyShow root ++ " to " ++ outFile ++
        " (" ++ show (length entries) ++ " reachable definitions)"

---------------------------------------------------------------------------
-- * Text rendering
---------------------------------------------------------------------------

renderText :: QName -> Int -> [Entry] -> [Entry] -> Ambient -> String
renderText root total entries trustBase ambient = unlines $ concat
  [ [ "AST dump for entry point: " ++ prettyShow root
    , ""
    , "Reachable definitions: " ++ show total
      ++ " (in project: " ++ show (length entries)
      ++ ", outside: " ++ show (total - length entries) ++ ")"
    , ""
    , "== TRUST BASE =="
    , ""
    ]
  , if null trustBase
      then [ "  (none -- no postulates or unsafe definitions are reachable)", "" ]
      else concatMap renderTrust trustBase
  , [ "== AMBIENT ASSUMPTIONS =="
    , ""
    , "  These are not name-reachable from the entry point, but can still"
    , "  affect whether it typechecks.  See the module header for why."
    , ""
    ]
  , renderAmbient ambient
  , [ "== REACHABLE DEFINITIONS =="
    , ""
    ]
  , concatMap renderEntry entries
  ]
  where
    locationOf e
      | not (null (eSrcRange e)) = Just (eSrcRange e)
      | otherwise                = eSource e


    renderTrust e = concat
      [ [ "  " ++ unwords (map upper (eMarkers e)) ++ "  " ++ eName e
            ++ (if eExternal e then "   [outside project]" else "") ]
      , [ "    type: " ++ eType e | not (null (eType e)) ]
      , [ "    at:   " ++ loc | Just loc <- [locationOf e] ]
      , [ "    path: " ++ joinArrows (ePath e) ]
      , [ "" ]
      ]

    renderEntry e = concat
      [ [ pad 12 (eKind e) ++ eName e ]
      , [ "    type: " ++ eType e | not (null (eType e)) ]
      , [ "    deps: " ++ joinCommas (eDeps e) | not (null (eDeps e)) ]
      , [ "" ]
      ]

    upper = map toUpperChar
    toUpperChar c
      | c >= 'a' && c <= 'z' = toEnum (fromEnum c - 32)
      | otherwise            = c

renderAmbient :: Ambient -> [String]
renderAmbient a = concat
  [ [ "  Rewrite rules active: " ++ show (length (amRewriteRules a)) ]
  , map ("    " ++) (amRewriteRules a)
  , [ "" ]
  , [ "  Modules compiled with unsafe options: "
        ++ show (length (amUnsafeOpts a)) ]
  , [ "    " ++ m ++ "  " ++ unwords fs | (m, fs) <- amUnsafeOpts a ]
  , [ "" ]
  , [ "  BUILTIN bindings in scope: " ++ show (length (amBuiltins a)) ]
  , [ "" ]
  ]

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
-- * JSON rendering
---------------------------------------------------------------------------

-- A tiny hand-rolled JSON writer.  Using aeson here would work, but the
-- output shape is trivial and this keeps the module free of version-
-- dependent @Key@/@Value@ differences between aeson 1.x and 2.x.

data J = JStr String | JNum Int | JBool Bool | JArr [J] | JObj [(String, J)] | JNull

renderJSON :: QName -> Int -> [Entry] -> [Entry] -> Ambient -> String
renderJSON root total entries trustBase ambient = encodeJ $ JObj
  [ ("entryPoint", JStr (prettyShow root))
  , ("counts", JObj
      [ ("reachable", JNum total)
      , ("inProject", JNum (length entries))
      , ("outside",   JNum (total - length entries))
      , ("trustBase", JNum (length trustBase))
      ])
  , ("trustBase", JArr (map entryJ trustBase))
  , ("ambient", JObj
      [ ("rewriteRules", JArr (map JStr (amRewriteRules ambient)))
      , ("builtins",     JArr (map JStr (amBuiltins ambient)))
      , ("unsafeModuleOptions", JArr
          [ JObj [ ("module", JStr m), ("flags", JArr (map JStr fs)) ]
          | (m, fs) <- amUnsafeOpts ambient ])
      ])
  , ("reachable", JArr (map entryJ entries))
  ]
  where
    entryJ e = JObj $
      [ ("name",     JStr (eName e))
      , ("kind",     JStr (eKind e))
      , ("type",     JStr (eType e))
      , ("source",   maybe JNull JStr (eSource e))
      , ("range",    JStr (eSrcRange e))
      , ("external", JBool (eExternal e))
      ] ++
      [ ("markers", JArr (map JStr (eMarkers e))) | not (null (eMarkers e)) ] ++
      [ ("deps",    JArr (map JStr (eDeps e)))    | not (null (eDeps e))    ] ++
      [ ("path",    JArr (map JStr (ePath e)))    | not (null (eMarkers e)) ]

encodeJ :: J -> String
encodeJ = \case
  JNull    -> "null"
  JBool b  -> if b then "true" else "false"
  JNum n   -> show n
  JStr s   -> jsonString s
  JArr xs  -> "[" ++ joinCommas (map encodeJ xs) ++ "]"
  JObj kvs -> "{" ++ joinCommas [ jsonString k ++ ":" ++ encodeJ v
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
