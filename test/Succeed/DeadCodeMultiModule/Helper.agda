-- Helper module for multi-module dead code test
module DeadCodeMultiModule.Helper where

data Bool : Set where
  true false : Bool

-- Used by main module
not : Bool → Bool
not true  = false
not false = true

-- Dead code in helper module (should be reported)
unusedInHelper : Bool → Bool
unusedInHelper b = b
