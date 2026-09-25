-- When checking stops, the --wide-sections report is still written, from the
-- state it stopped in, and says it is incomplete.  That is the case it exists
-- for: a module that cannot be checked is the one whose cost is unknown.
--
-- The application `M` is checked before the definition that fails, so it is
-- in the report; `after`, which comes later, is not.
module WideSectionsAbort where

postulate
  A B : Set
  a : A

module Inner (x y z : A) where
  postulate
    p q : A

f : A → A → A → A
f x y z = g
  where
    module M = Inner x y z

    g : A
    g = M.p

bad : A
bad = Set

module After (x y z : A) where
  postulate
    after : A
