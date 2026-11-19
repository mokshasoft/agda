module F where

module At (A : Set) where
  module L where
    found : A → A
    found x = x
  open L public
  k : A → A
  k x = x
