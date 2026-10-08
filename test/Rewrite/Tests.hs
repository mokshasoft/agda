{-# OPTIONS_GHC -Wunused-imports #-}
{-# LANGUAGE OverloadedStrings #-}

-- | The in-place rewrites, @--remove-dead-imports@ and
--   @--repair-reexports@.
--
--   Each directory under @test/Rewrite@ is a scenario: its modules, a file
--   @main@ (the module to check) and a file @runs@ (one line of flags per
--   run; the runs are applied in order to the same copy, as a chain of
--   re-exports is repaired over several runs).  The golden file
--   @test/Rewrite/<scenario>.golden@ records, for the whole scenario:
--
--   * each run's report lines (and its errors, if it failed);
--   * every module the runs changed, in full;
--   * whether the rewritten modules check again (the verification a real
--     user runs next: a rewrite that does not check is a bug).

module Rewrite.Tests where

import           Control.Monad              ( forM, forM_, when )
import qualified Data.ByteString            as BS
import           Data.List                  ( sort )
import           Data.Text                  ( Text )
import qualified Data.Text                  as T
import           Data.Text.Encoding         ( decodeUtf8 )

import           System.Directory
import           System.Exit
import           System.FilePath
import qualified System.FilePath.Find       as Find
import           System.IO.Temp             ( withSystemTempDirectory )

import           Test.Tasty                 ( TestTree, testGroup )
import           Test.Tasty.Silver          ( goldenVsAction )

import           Utils

testDir :: FilePath
testDir = "test" </> "Rewrite"

tests :: IO TestTree
tests = do
  dirs <- sort . drop 1 <$>
    Find.find (Find.depth Find.<? 1) (Find.fileType Find.==? Find.Directory) testDir
  return $ testGroup "Rewrite"
    [ goldenVsAction (takeFileName d) (d <.> "golden") (scenario d) id | d <- dirs ]

-- | The scenario's modules, relative to its directory.
agdaFiles :: FilePath -> IO [FilePath]
agdaFiles d =
  sort . map (makeRelative d) <$> Find.find Find.always (Find.extension Find.==? ".agda") d

-- | No interface survives between runs: every run checks every module.
clean :: FilePath -> IO ()
clean tmp = do
  let b = tmp </> "_build"
  e <- doesDirectoryExist b
  when e $ removeDirectoryRecursive b
  is <- Find.find Find.always (Find.extension Find.==? ".agdai") tmp
  mapM_ removeFile is

scenario :: FilePath -> IO Text
scenario dir = withSystemTempDirectory "rewrite" $ \ tmp -> do
  files <- agdaFiles dir
  forM_ files $ \ f -> do
    createDirectoryIfMissing True (takeDirectory (tmp </> f))
    copyFile (dir </> f) (tmp </> f)
  mainMod <- T.unpack . T.strip . T.pack <$> readFile (dir </> "main")
  runs    <- filter (not . null) . lines <$> readFile (dir </> "runs")
  let norm = T.replace (T.pack tmp) "TMP"
      agda args = do
        (code, out, err) <- readAgdaProcessWithCWD Nothing (Just tmp) (args ++ [mainMod <.> "agda"]) T.empty
        return (code, norm out, norm err)

  outs <- forM (zip [1 :: Int ..] runs) $ \ (i, flags) -> do
    clean tmp
    (code, out, err) <- agda (words flags)
    -- the report lines, and the reasons under a refused target (indented)
    let rep = filter (\ l -> "repair-reexports" `T.isPrefixOf` l
                           || ("  " `T.isPrefixOf` l && not ("Checking" `T.isInfixOf` l))) (T.lines out)
        bad = [ "(exit " <> T.pack (show code) <> ")" | code /= ExitSuccess ] ++
              (if code /= ExitSuccess then take 12 (filter (not . ("Checking" `T.isInfixOf`)) (T.lines out ++ T.lines err)) else [])
    return $ T.unlines $ ("== run " <> T.pack (show i) <> ": " <> T.pack flags) : rep ++ bad

  changed <- forM files $ \ f -> do
    a <- BS.readFile (dir </> f)
    b <- BS.readFile (tmp </> f)
    return [ T.unlines ["== " <> T.pack f <> " (rewritten)", decodeUtf8 b] | a /= b ]

  clean tmp
  -- with -W error: a warning (an import naming what a module no longer
  -- exports) is as much a broken rewrite as an error
  (code, out, err) <- agda ["-W", "error"]
  let recheck
        | code == ExitSuccess = "== re-check: OK\n"
        | otherwise = T.unlines $ "== re-check: FAILED" :
            take 12 (filter (not . ("Checking" `T.isInfixOf`)) (T.lines out ++ T.lines err))
  return $ T.concat outs <> T.concat (concat changed) <> recheck
