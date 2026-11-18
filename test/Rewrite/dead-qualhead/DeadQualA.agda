module DeadQualA (n : Set) where

module ShapeC (m : Set) where
  module CaseShape where
    shape : Set₁
    shape = Set

record T (X : Set) : Set where
  coinductive
  field force : X

module ResuspIdC where
  module RId (x : Set) where
    resusp : Set
    resusp = x

unused : Set₁
unused = Set
