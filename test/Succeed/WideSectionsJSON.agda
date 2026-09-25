-- The --wide-sections report in JSON, its default format.  Two nested where
-- blocks are two sections named `_`, so each is located by its first
-- definition, and the application inside the inner one names the module it
-- copied from.
module WideSectionsJSON where

postulate
  A : Set

module Inner (x y : A) where
  postulate
    p q r : A

f : A → A → A → A
f x y z = g
  where
    g : A
    g = h
      where
        module M = Inner x z

        h : A
        h = M.p
