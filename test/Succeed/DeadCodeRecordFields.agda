-- Test for --dead-code option: unused record fields

module DeadCodeRecordFields where

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

-- Record with some used and some unused fields
record Point : Set where
  field
    x : Nat
    y : Nat
    z : Nat  -- This field will be unused

-- Only uses x and y fields
addXY : Point → Nat
addXY p = add (Point.x p) (Point.y p)
  where
    add : Nat → Nat → Nat
    add zero    n = n
    add (suc m) n = suc (add m n)

-- Entry point
main : Point → Nat
main = addXY
