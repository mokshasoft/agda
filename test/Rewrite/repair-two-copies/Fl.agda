module Fl where

module M {A : Set} where
  record S : Set where
    field fa fb : A
  open S public
