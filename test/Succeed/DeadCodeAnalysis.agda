-- Test for --dead-code option: basic unreachable definitions

module DeadCodeAnalysis where

-- Basic data type used by main
data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

-- Used function (reachable from main)
add : Nat → Nat → Nat
add zero    n = n
add (suc m) n = suc (add m n)

-- Entry point
main : Nat
main = add (suc zero) (suc (suc zero))

-- Unreachable definitions (should be reported)
unused : Nat → Nat
unused n = suc n

alsoUnused : Nat
alsoUnused = zero
