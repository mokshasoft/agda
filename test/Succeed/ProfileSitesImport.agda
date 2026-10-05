-- Imported by ProfileSites.  It is checked before the main module, and the
-- report is written after both, from names read back from its interface:
-- its sites must still have their ranges.
module ProfileSitesImport where

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

data Bool : Set where
  true false : Bool

double : Nat → Nat
double zero    = zero
double (suc n) = suc (suc (double n))

two : Nat
two = double (suc zero)
