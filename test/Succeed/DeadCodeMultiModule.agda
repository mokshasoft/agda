-- Test for --dead-code option: verify that dead code in imported
-- project modules is also detected.

module DeadCodeMultiModule where

open import DeadCodeMultiModule.Helper

-- Entry point using helper module
main : Bool
main = not true

-- Dead code in main module
unusedInMain : Bool
unusedInMain = false
