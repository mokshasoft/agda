module I where

open import X
open import M using (module C)
open C using (f)

u : T
u = f t
