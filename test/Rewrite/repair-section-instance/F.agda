module F where

open import X
import G

module _ (v : T) where
  module GI = G T v
  open GI public

h : T
h = t
