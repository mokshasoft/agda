module F (A : Set) where

open import G
module G′ = G A
open G′ public
