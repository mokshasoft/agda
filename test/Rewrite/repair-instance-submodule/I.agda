module I where

open import X
import F
module FI = F T
open FI

u : T
u = f t

v : T
v = FI.f t
