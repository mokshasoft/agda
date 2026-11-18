-- the facades' instances are named (`module PN = P Nat`); their `open … public`
-- go and every importer opens the named instance itself (plan 0.152 A(2b))
module Main where

open import Agda.Builtin.Nat using (Nat)
open import F using (one)
open import F using (Box; unbox; module Inner)
import F as Q

u : Nat
u = unbox one

w : F.Box
w = Q.box 3

t : Box
t = Inner.twice one
