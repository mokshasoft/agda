module I where

open import X using (T)
import F as Fx

module VC = Fx.W T

u : T
u = VC.t
