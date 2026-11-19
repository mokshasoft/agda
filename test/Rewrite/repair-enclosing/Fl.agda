module Fl where

module M {A : Set} where
  record S : Set where
    field fa : A
  open S public
