-- Declaration-level pragmas that --safe rejects are consumed during type
-- checking and leave no trace on the Definition unless recorded explicitly.
-- Check that --write-ast reports the ones reachable from the entry point.
-- (WriteASTBasic covers the converse: unreachable assumptions are not listed.)
module WriteASTPragmas where

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

const2 : Nat → Nat → Nat
const2 x _ = x

{-# NO_POSITIVITY_CHECK #-}
data Bad : Set where
  bad : (Bad → Nat) → Bad

{-# NO_UNIVERSE_CHECK #-}
data Big : Set where
  big : Set → Big

{-# NON_COVERING #-}
partial : Nat → Nat
partial zero = zero

inj : Nat → Nat
inj x = x
{-# INJECTIVE inj #-}

{-# TERMINATING #-}
loop : Nat → Nat
loop x = x

useBad : Bad → Nat
useBad (bad f) = f (bad f)

useBig : Big → Nat
useBig (big _) = zero

main : Nat
main =
  const2 (inj (partial (loop (useBad (bad (λ _ → zero))))))
         (useBig (big Nat))
