-- Ranking in the generalises direction.
--
-- All three conclusions have the shape `step _ (step _ _) ≡ _`.  `tight` is
-- very nearly the pattern; `buried` says the same thing behind three extra
-- premises.  Nothing in the statements distinguishes them to a matcher, so
-- the ranking has to: coverage -- how much of each hit the pattern accounts
-- for -- is what puts `buried` last.
--
-- Without it a common pattern returns its best and its worst hits
-- interleaved, which is the failure mode that makes a type search useless
-- in a dependently typed development.
-- Note on the .flags spelling: the harness splits a .flags file on
-- whitespace (test/Utils.hs), so the pattern cannot contain spaces.
-- Parentheses lex as their own tokens, which is what separates them -- and
-- the trailing hole has to be written `(_)` rather than `_`, or `≡_` lexes
-- as a mixfix section and elaborates to a lambda instead of a hole.
module SearchTypeRanking where

postulate
  Tm   : Set
  step : Tm → Tm → Tm
  idT  : Tm

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x
infix 4 _≡_

postulate
  tight  : ∀ a b c → step a (step b c) ≡ step a c
  middle : ∀ a b c → a ≡ a → step a (step b c) ≡ step a c
  buried : ∀ a b c → a ≡ a → b ≡ b → c ≡ c → step a (step b c) ≡ step a c
