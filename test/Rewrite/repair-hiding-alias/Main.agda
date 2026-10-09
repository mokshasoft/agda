-- every name the facade re-exports is hidden (as Once.TypeCheck.Elaborate hides IRTy's
-- constructors from Once.IR): nothing is used through the re-export, yet the hiding must
-- go; Main is itself a facade with a target in the same run (as Elaborate is), and uses
-- the data type `G` through the re-export (as Elaborate uses `IRTy`), and hidden names
-- qualified through the alias (`FF.k`, as Elaborate writes `IR.*`); the alias is
-- `FF`, not `F`: `open import F as FF` is logged as `open FF`
module Main where

open import Z public
open import Y
open import F as FF hiding (c; _*_; k)

g : Set
g = f

t : U
t = c * c

h : Set
h = G

v : G
v = FF.k FF.c
