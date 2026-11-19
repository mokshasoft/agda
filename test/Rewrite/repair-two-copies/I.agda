module I where

open import X
open import Fl using (module M)
open M {T} using (S; fa)
open M {T} using (fb)

g : S → T
g s = fa s

h : S → T
h s = fb s
