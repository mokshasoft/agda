-- The sites table of --profile=allocation and --profile=definitions: bytes
-- allocated and CPU time per site checked.  Those numbers depend on the GHC
-- version, the build and the machine, so run-tests.sh checks their
-- structure instead of a golden: every definition below has a row, f's
-- total includes what its where-bound g allocated, and the termination
-- check after f is a site of its own.
--
-- Its unfolding counts are exact, so the folded stacks of
-- --counters-folded are compared against ProfileAllocation.folded: each
-- line is the file, the sites enclosing one, and its own count.
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
