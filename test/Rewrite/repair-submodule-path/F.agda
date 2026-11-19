module F where

open import X

module S where
  module C where
    hv : T
    hv = t

open S public
open C using (hv) public
