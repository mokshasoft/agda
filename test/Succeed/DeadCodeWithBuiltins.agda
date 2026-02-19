-- Test for --dead-code option: verify that external libraries (builtins)
-- are not traversed during reachability analysis.
-- This test would cause OOM before the fix if it traversed all builtin definitions.

module DeadCodeWithBuiltins where

open import Agda.Builtin.Nat

-- Entry point using builtin Nat
main : Nat
main = 1 + 2

-- Unreachable project code (should be reported)
deadFunction : Nat → Nat
deadFunction n = n + n

-- Another unreachable definition
alsoUnused : Nat
alsoUnused = 42
