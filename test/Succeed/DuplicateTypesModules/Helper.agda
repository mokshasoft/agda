-- Helper module for the cross-module duplicate test.
module DuplicateTypesModules.Helper where

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

twin : Nat → Nat
twin n = suc n
