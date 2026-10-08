-- --dead-imports: which directive items the module never uses.
module DeadImports where

open import DeadImportsA using (Arch; x86; arm; x; Box) renaming (y to y′)
open import DeadImportsA using (unused)           -- dead: opens only a dead name
import DeadImportsA as Q                          -- an alias: never reported
open DeadImportsA.P x86 using (z; z₂)             -- an application: z₂ dead
open DeadImportsA.P arm renaming (z to z′)        -- dead: an application, nothing used
open DeadImportsA.W                               -- dead: a wholesale open, nothing used
  arm

-- `Arch` used in a type, `x86` as a constructor in a pattern, `x` in a term;
-- `arm` never: dead. `Box` used only as a qualifier (Box.unbox): not dead.
f : Arch → Arch
f x86 = x
f _   = Box.unbox (record { unbox = z })

g : Arch
g = Q.x
