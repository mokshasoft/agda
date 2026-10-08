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

  z₂ : Arch
  z₂ = a

module W (a : Arch) where
  w : Arch
  w = a

record HasArch : Set where
  field the : Arch

pick : ⦃ HasArch ⦄ → Arch
pick ⦃ h ⦄ = HasArch.the h

module I (a : Arch) where
  instance
    hasArch : HasArch
    hasArch = record { the = a }
