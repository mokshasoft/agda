module Lib.Cl where

data N : Set where
  z : N

record Ctx : Set where
  field
    size : N
    tag  : N

lk : Ctx → N
lk = Ctx.tag
