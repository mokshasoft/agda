-- Check that --duplicate-types sees across module boundaries: the by-name
-- pass reports `twin`, defined in both this module and the helper, and the
-- by-type pass reports the two `twin`s together with `alsoNatToNat`, which
-- shares their type under a different name.
--
-- This is the case that cannot be found from either side alone: neither
-- module mentions the other's copy.
module DuplicateTypesModules where

-- `using` deliberately does not bring the helper's `twin` into scope: this
-- module defines its own, and the point of the test is that nothing in
-- either module's text mentions the other's copy.
open import DuplicateTypesModules.Helper using (Nat; zero; suc)

twin : Nat → Nat
twin n = suc n

alsoNatToNat : Nat → Nat
alsoNatToNat n = n
