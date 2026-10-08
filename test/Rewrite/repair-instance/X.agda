module X where

record Def (A : Set) : Set where
  field def : A

open Def {{...}} public

data T : Set where
  t : T

instance
  defT : Def T
  defT = record { def = t }
