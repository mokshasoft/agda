module I where

open import X
open import F

u : T
u = let open At T using (found; k) in found (k t)
