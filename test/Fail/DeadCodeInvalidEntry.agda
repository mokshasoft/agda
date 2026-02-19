-- Test for --dead-code option: invalid entry point

module DeadCodeInvalidEntry where

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

foo : Nat
foo = zero
