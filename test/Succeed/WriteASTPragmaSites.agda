-- One declaration-level pragma is one assumption, however many definitions
-- inherit it.  A TERMINATING pragma covers a whole mutual block, and
-- elaboration then adds with-functions and rewrite helpers to that block, so
-- counting definitions that carry the pragma reports it many times over.
--
-- Here one pragma covers two functions and generates two helpers: it must be
-- reported once, at a site the user actually wrote.
module WriteASTPragmaSites where

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x
{-# BUILTIN EQUALITY _≡_ #-}

id : (n : Nat) → n ≡ n
id _ = refl

{-# TERMINATING #-}
mutual
  f : Nat → Nat
  f zero = zero
  f (suc n) with n
  ... | zero  = g n
  ... | suc m = f m

  g : Nat → Nat
  g n rewrite id n = f n

main : Nat
main = f (suc zero)
