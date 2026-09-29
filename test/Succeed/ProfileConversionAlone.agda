-- --profile=conversion predates the per-definition counters, and on its own
-- must not ask for them: no counters report is written, and none is
-- announced.  Only --profile=reduction or --counters-file asks for one.
module ProfileConversionAlone where

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

data _≡_ (x : Nat) : Nat → Set where
  refl : x ≡ x

two : Nat
two = suc (suc zero)

test : two ≡ suc (suc zero)
test = refl
