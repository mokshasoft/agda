-- --repair-reexports: a parameterised facade (its importers apply it).
module RepairG (A : Set) where

open import RepairX public

record Box : Set where
  field unbox : A

open Box public
