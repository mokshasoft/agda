module X where

data T : Set where
  t : T

record Has (A : Set) : Set where
  field v : A

get : {A : Set} {{_ : Has A}} → A
get {{h}} = Has.v h

instance
  hasT : Has T
  hasT = record { v = t }
