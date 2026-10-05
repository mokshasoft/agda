-- --name-resolution-report: where every name came from.  A defines, B
-- re-exports A publicly, and this module reaches A's names through B in
-- each of the ways an import can be written.
module NameResolutionReport where

-- Plain open import with using.
open import NameResolutionReportA using (Arch)

-- Qualified access through an alias, across the public re-export.
import NameResolutionReportB as Q

viaAlias : Q.Arch
viaAlias = Q.x

-- A renaming, across the public re-export.
open import NameResolutionReportB renaming (x to z)

viaRenaming : Arch
viaRenaming = z

-- Box is both a record type and a module.
unboxed : Box → Arch
unboxed b = Box.unbox b

-- A constructor in a pattern, and a pattern variable.
f : Arch → Arch
f x86   = arm
f other = other

-- A module application.
module M = P arm

applied : Arch
applied = M.y
