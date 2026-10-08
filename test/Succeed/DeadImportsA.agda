-- Defines what DeadImports imports.
module DeadImportsA where

data Arch : Set where
  x86 arm : Arch

x : Arch
x = x86

y : Arch
y = arm

unused : Arch
unused = arm

record Box : Set where
  field
    unbox : Arch

module P (a : Arch) where
  z : Arch
  z = a
