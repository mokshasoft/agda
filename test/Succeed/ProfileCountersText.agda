-- The per-definition counters of --profile=reduction, written as text, with
-- the fast evaluator left on.  It is counted too, so the numbers predicted by
-- hand in ProfileCountersJSON must come out here as well: `loop` 6, `five` 1.
module ProfileCountersText where

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
