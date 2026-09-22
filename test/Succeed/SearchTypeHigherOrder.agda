-- A hole applied to arguments is refused, and the refusal is the feature.
--
-- `substLike`'s conclusion is `P y`, where both P and y are telescope
-- variables.  That is flex-flex, not the decidable Miller fragment: a goal
-- `Q t0` is solved by `P := Q, y := t0` and equally by `P := \_ -> Q t0`
-- with y arbitrary.  There is no unique answer, so reporting one would be a
-- guess -- and admitting these would make subst, transport and J match
-- nearly every query in a development that is dense in them.
--
-- Checked under --search-unanchored, the most permissive setting: even
-- there, only `fits` may be reported.
module SearchTypeHigherOrder where

postulate
  Tm  : Set
  t0  : Tm
  Q   : Tm → Set

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x
infix 4 _≡_

postulate
  substLike : (P : Tm → Set) (x y : Tm) → x ≡ y → P x → P y
  fits      : (x : Tm) → Q x
