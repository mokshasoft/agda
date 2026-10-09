module X where

mutual
  data G : Set where
    k : T → G

  data T : Set where
    c   : T
    _*_ : T → T → T
