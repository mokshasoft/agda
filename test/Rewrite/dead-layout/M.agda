module M where

a b c : Set₁
a = Set
b = Set
c = Set

record C : Set where

instance
  ci : C
  ci = record {}

needC : {{C}} → Set₁
needC = Set
