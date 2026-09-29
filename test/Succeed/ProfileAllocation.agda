-- --profile=allocation: bytes allocated while checking each definition.
-- The numbers depend on the GHC version and the build, so run-tests.sh
-- checks their structure instead of a golden: every definition below has a
-- row, and f's total includes what its where-bound g allocated.
module ProfileAllocation where

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

data _≡_ (x : Nat) : Nat → Set where
  refl : x ≡ x

double : Nat → Nat
double zero    = zero
double (suc n) = suc (suc (double n))

f : Nat → Nat
f n = g (g n)
  where
    g : Nat → Nat
    g m = double m

test : f (suc zero) ≡ suc (suc (suc (suc zero)))
test = refl
