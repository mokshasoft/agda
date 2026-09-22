-- The default (anchored) half of the pair; see SearchTypeUnanchored.
-- The goal `P t0` must find `fits` and NOT `anything`.
module SearchTypeUnanchoredOff where

postulate
  Tm  : Set
  t0  : Tm
  P   : Tm → Set

  fits     : (x : Tm) → P x
  anything : (A : Set) → A
