-- Same content as DuplicateTypesBasic, checked through the JSON renderer:
-- one group per line, so a report can be committed and read as a diff.
module DuplicateTypesJSON where

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

plusOne : Nat → Nat
plusOne n = suc n

succOf : Nat → Nat
succOf zero    = suc zero
succOf (suc n) = suc (suc n)
