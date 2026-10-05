-- Sites and their ranges when more than one module is checked, and the
-- naming of a mutual block that contains with-functions.
--
-- even? and odd? form a mutual block of forward-declared functions, with no
-- datatype in it.  Each with brings a generated with-function, which has no
-- range, into the block.  The block's checks must be named after even?,
-- the first name written in it, and carry the range of the whole block.  A
-- with-function's own row is given the range of the function it was made
-- for.
module ProfileSites where

open import ProfileSitesImport

even? : Nat → Bool
odd?  : Nat → Bool

even? zero = true
even? (suc n) with odd? n
... | true  = true
... | false = false

odd? zero = false
odd? (suc n) with even? n
... | b = b

data _≡_ (x : Bool) : Bool → Set where
  refl : x ≡ x

test : even? two ≡ true
test = refl
