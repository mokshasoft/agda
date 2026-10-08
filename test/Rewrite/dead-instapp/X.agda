module X where

data T : Set where
  t : T

record NonZero (A : Set) : Set where

module Width (A : Set) where
  w : Set
  w = A

  instance
    nz : NonZero A
    nz = record {}

  need : {{NonZero A}} → Set
  need = A
