-- The trust base must be found through a chain of definitions, and through
-- a higher-order function, not just via direct references.
module WriteASTTransitive where

data Bool : Set where
  true false : Bool

apply : (Bool → Bool) → Bool → Bool
apply f x = f x

postulate
  deepAxiom : Bool → Bool

{-# TERMINATING #-}
loop : Bool → Bool
loop x = loop x

step : Bool → Bool
step x = apply deepAxiom x

main : Bool
main = apply loop (step true)
