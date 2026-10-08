module Main where

open import H using (Box; unbox; T)

k : Box → T
k b = unbox b
