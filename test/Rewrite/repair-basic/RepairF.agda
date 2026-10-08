-- --repair-reexports: a facade re-exporting a module and a record module.
module RepairF where

open import RepairX public

record Pair : Set where
  field fst snd : Bit

open Pair public

both : Bit → Pair
both b = record { fst = b ; snd = b }
