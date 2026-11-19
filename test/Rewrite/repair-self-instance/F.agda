module F where

open import X

module G (A : Set) where
  f : A → A
  f x = x

module P (A : Set) where
  module G′ = G A
  open G′ public

module NSP = P T

u : T
u = NSP.f t
