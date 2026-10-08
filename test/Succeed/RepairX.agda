-- --repair-reexports: the module re-exported.
module RepairX where

data Bit : Set where
  o i : Bit

flip : Bit → Bit
flip o = i
flip i = o

_∧_ : Bit → Bit → Bit
i ∧ i = i
_ ∧ _ = o
