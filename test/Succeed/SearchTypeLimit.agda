-- --search-limit truncates the listing but not the count: the report says
-- how many hits there were and how many of them it showed, so a truncated
-- result never looks like a complete one.
module SearchTypeLimit where

postulate
  Tm            : Set
  a b c d e     : Tm
  P             : Tm → Set

  pa : P a
  pb : P b
  pc : P c
  pd : P d
  pe : P e
