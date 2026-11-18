module Main2 where

open import Agda.Builtin.Nat using (Nat)
open import G Nat

v : Nat
v = unbox (box 2)

x : Box
x = PA.Inner.twice (box 4)
