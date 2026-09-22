-- Record fields and constructors are grouped by NAME but never by TYPE.
--
-- `fst` and `snd` both have type `Pair -> Nat`, and `mk` and `mk'` are two
-- constructors of the same shape.  None of that is duplication anyone can
-- act on -- a field is not removable on its own -- so only the two genuine
-- functions `wrapped` and `alsoWrapped` may be reported.
module DuplicateTypesFields where

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

record Pair : Set where
  constructor mk
  field
    fst : Nat
    snd : Nat

record Pair' : Set where
  constructor mk'
  field
    one : Nat
    two : Nat

wrapped : Nat → Nat
wrapped n = suc n

alsoWrapped : Nat → Nat
alsoWrapped zero    = zero
alsoWrapped (suc n) = suc (suc n)
