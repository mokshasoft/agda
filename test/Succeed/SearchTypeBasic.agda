-- Check that --search-type matches a *shape* over everything in scope,
-- with _ standing for any subterm.
--
-- `nested` and `alsoNested` both have a type of the shape Wrap (Wrap _);
-- `flat` and `plain` do not, and must not be reported.  Neither of the two
-- hits mentions the other, and they are found by shape rather than by name
-- or by module -- which is the query grep cannot express.
module SearchTypeBasic where

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

data Bool : Set where
  true false : Bool

data Wrap (A : Set) : Set where
  wrap : A → Wrap A

nested : Wrap (Wrap Nat)
nested = wrap (wrap zero)

alsoNested : Wrap (Wrap Bool)
alsoNested = wrap (wrap true)

flat : Wrap Nat
flat = wrap zero

plain : Nat
plain = zero
