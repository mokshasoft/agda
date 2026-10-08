module Main where

open import M
  using ( a
        ; b
        ; c
        ; needC )
open import M hiding (a)

k : Set₁
k = a

l : Set₁
l = c

m : Set₁
m = needC

n : Set₁
n = x
  where
    open import M using (b)
    x : Set₁
    x = Set
