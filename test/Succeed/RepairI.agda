-- --repair-reexports: an importer using names through every target.
module RepairI where

open import RepairF using (Bit; o; both; fst)
import RepairF as F
open import RepairG Bit using (Box; unbox; flip)

g : Bit → Bit
g o = F.flip F.i
g b = fst (both b)

h : Box → Bit
h x = flip (unbox x)

open import RepairH using (snd)
import RepairH as H

k : Bit
k = snd (both o) F.∧ H.snd (both o)

-- a fully qualified use through a record-module re-export
p : RepairF.Pair → Bit
p q = RepairF.fst q
