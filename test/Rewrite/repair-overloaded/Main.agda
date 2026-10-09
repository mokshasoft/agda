-- `c` is overloaded: A's from A, B's through the facade F; both stay in scope
module Main where

open import A
open import F

a : A
a = c

b : B
b = c

b' : B
b' = d
