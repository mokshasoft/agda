module Main where

open import M using (a; b) public
open import M using (a)
open import M using (a)
import M as N

k : Set₁
k = let open N in a

l : Set₁
l = a
