-- --wide-sections with --profile=reduction: each section is also reported
-- with how often its definitions were unfolded, summed.  The application M
-- copies Inner's `add` into f's where block.  Predicted by hand: the proof
-- unfolds `f` once and the copy `M.add` once, and the copy delegates to
-- `Inner.add` at 2, 1 and 0 -- so M reports 1 and Inner 3.
module WideSectionsUnfold where

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

data _≡_ (x : Nat) : Nat → Set where
  refl : x ≡ x

module Inner (k : Nat) where
  add : Nat → Nat
  add zero    = k
  add (suc n) = suc (add n)

f : Nat → Nat
f k = M.add (suc (suc zero))
  where
    module M = Inner k

test : f zero ≡ suc (suc zero)
test = refl
