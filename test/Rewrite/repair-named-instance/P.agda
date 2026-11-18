module P (A : Set) where

data Box : Set where
  box : A → Box

unbox : Box → A
unbox (box a) = a

module Inner where
  twice : Box → Box
  twice (box a) = box a
