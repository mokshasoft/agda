module G (A : Set) where

record Box : Set where
  field unbox : A

open Box public
