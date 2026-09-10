-- A postulate reachable only as the type of a record field that is never
-- projected is still part of the trust base: the record cannot be formed
-- without it. (--dead-code separately reports the field itself as unused.)
module WriteASTRecordFields where

data Nat : Set where
  zero : Nat

postulate
  WeirdTy : Set          -- used only as the type of a field that is never projected
  usedAxiom : Nat        -- reached through a field that IS projected

record R : Set where
  field
    projected   : Nat
    neverUsed   : WeirdTy   -- this field is never projected anywhere

mkR : WeirdTy → R
mkR w = record { projected = usedAxiom ; neverUsed = w }

main : WeirdTy → Nat
main w = R.projected (mkR w)
