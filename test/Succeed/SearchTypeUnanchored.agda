-- --search-unanchored lets a candidate's telescope variable stand at the
-- HEAD of an instance-of match.  It is off by default, and this test is the
-- reason: `anything`'s conclusion is a bare variable, so it instantiates to
-- every goal there is, and a development accumulates such definitions
-- without accumulating usefulness.
--
-- Anchored, the goal `P t0` finds only `fits`.  Compare
-- SearchTypeUnanchoredOff, which is the same module and goal without the
-- flag.
module SearchTypeUnanchored where

postulate
  Tm  : Set
  t0  : Tm
  P   : Tm → Set

  fits     : (x : Tm) → P x
  anything : (A : Set) → A
