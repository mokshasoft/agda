-- --dead-imports: which directive items the module never uses.
module DeadImportsInPlace where

open import DeadImportsA using (Arch; x86; arm; x; Box) renaming (y to y′)
open import DeadImportsA using (unused)           -- dead: opens only a dead name
import DeadImportsA as Q                          -- an alias: never reported
open DeadImportsA.P x86 using (z)                 -- a module application
open import DeadImportsA using (module P; unused) -- `module P` keeps its keyword
open import DeadImportsA as R using (unused)      -- alias used: stays, `using ()`

-- `Arch` used in a type, `x86` as a constructor in a pattern, `x` in a term;
-- `arm` never: dead. `Box` used only as a qualifier (Box.unbox): not dead.
f : Arch → Arch
f x86 = x
f _   = Box.unbox (record { unbox = z })

g : Arch
g = Q.x

h : Arch
h = P.z x86

k : Arch
k = R.x
