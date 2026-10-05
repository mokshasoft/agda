-- Defines what NameResolutionReport reaches through NameResolutionReportB.
module NameResolutionReportA where

data Arch : Set where
  x86 arm : Arch

x : Arch
x = x86

-- A name that is also a module name.
record Box : Set where
  field
    unbox : Arch

-- A parameterised module, for a module application.
module P (a : Arch) where
  y : Arch
  y = a
