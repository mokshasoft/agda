module I where

open import X
import F
module FI = F T
  using (f)
open FI

u : T
u = f t
