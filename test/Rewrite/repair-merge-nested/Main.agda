module Main where

open import F

module Inner where
  open import X using (b)

  q : T
  q = b

module Sibling where

  r : T
  r = f a
