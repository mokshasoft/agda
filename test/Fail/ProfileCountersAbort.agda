-- When the run stops, the per-definition counters are still written, and
-- say they are incomplete.  `loop five` is checked before `bad` fails, so its
-- 6 unfoldings of `loop` are in the report.
module ProfileCountersAbort where

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

bad : Nat
bad = Set
