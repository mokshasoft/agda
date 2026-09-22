-- The JSON renderer for --search-type, including the substitution and the
-- residual premises a hit carries.
module SearchTypeJSON where

postulate
  Tm  : Set
  t0  : Tm
  P Q : Tm → Set

  direct      : P t0
  viaPremises : (x : Tm) → Q x → P x
