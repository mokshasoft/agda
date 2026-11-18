module F where

open import Agda.Builtin.Nat using (Nat)
import P
module PN = P Nat
open PN public

one : Box
one = box 1
