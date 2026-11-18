-- a re-export that renames (`map to tmap`): each importer writes the renaming
-- itself, in a new statement or next to its own statement on X (R20)
module Main where

open import F using (T; tmap)
open import X using (keep)

u : T → T
u x = keep (tmap x)
