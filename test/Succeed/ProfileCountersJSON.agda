-- The per-definition counters of --profile=reduction, written as JSON.
--
-- The numbers are predicted by hand, which is the point of the test: `loop
-- five` unfolds `loop` once for each of n = 5, 4, 3, 2, 1, 0, so exactly 6
-- times, and `five` exactly once.  The fast evaluator is off because it does
-- not go through the counted path.
module ProfileCountersJSON where

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

data _≡_ (x : Nat) : Nat → Set where
  refl : x ≡ x

five : Nat
five = suc (suc (suc (suc (suc zero))))

loop : Nat → Nat
loop zero    = zero
loop (suc n) = loop n

test : loop five ≡ zero
test = refl
