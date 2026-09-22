-- Nothing shares a name or a type, so --duplicate-types must emit NO
-- warning at all -- only the report, which still records the answer.
--
-- A warning here would also stop the interface being written, so a clean
-- project must not get one merely for asking the question.
module DuplicateTypesClean where

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

data Unit : Set where
  unit : Unit

toUnit : Nat → Unit
toUnit _ = unit
