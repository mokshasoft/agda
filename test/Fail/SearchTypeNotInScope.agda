-- A search pattern is scope-checked and type-checked like any other
-- expression, so a name it does not resolve is an ordinary error rather
-- than an empty result set.
module SearchTypeNotInScope where

postulate
  Tm : Set
