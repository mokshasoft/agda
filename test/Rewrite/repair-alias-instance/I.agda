module I where

open import X
import F as Fx
module FI = Fx T
open FI using (f)

u : T
u = f t

v : T
v = FI.f t
