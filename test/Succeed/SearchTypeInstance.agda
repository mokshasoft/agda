-- The instance-of direction: definitions whose conclusion can be
-- instantiated to the pattern.  "Would this lemma close my goal?"
--
-- Against the goal `P t0`, all three of these apply, and the ranking is the
-- point: `direct` owes nothing, `withImplicit` leaves an implicit
-- undetermined, and `viaPremises` still wants two proofs.  Matching a
-- conclusion says a lemma applies, not that it closes anything, so what the
-- match left open is reported beside each hit.
--
-- `wrongHead` must NOT appear: its conclusion is headed by Q, not P.
module SearchTypeInstance where

postulate
  Tm    : Set
  t0 t1 : Tm
  P Q   : Tm → Set
  _~_   : Tm → Tm → Set

  direct       : P t0
  withImplicit : {y : Tm} (x : Tm) → P x
  viaPremises  : (x : Tm) → Q x → x ~ t1 → P x
  wrongHead    : (x : Tm) → Q x
