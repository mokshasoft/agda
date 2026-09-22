-- Check that --duplicate-types groups definitions by their elaborated type.
--
-- `plusOne` and `succOf` have the same type and different proofs, so they
-- form one group; `add` has a different type and joins none.  Note that
-- `zero` and `suc` are constructors and `Nat` a datatype, so none of them is
-- grouped by type -- see `typeIsContent` for why.
module DuplicateTypesBasic where

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

plusOne : Nat → Nat
plusOne n = suc n

succOf : Nat → Nat
succOf zero    = suc zero
succOf (suc n) = suc (suc n)

add : Nat → Nat → Nat
add zero    n = n
add (suc m) n = suc (add m n)
