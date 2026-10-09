-- the shape of Once.TypeCheck.Soundness over the facade Once.TypeCheck.Elaborate: the
-- importer's `using` list is on a continuation line (top level), and a field is used
-- through the RECORD module `Ctx` reached through the facade (`NamedCtx.size`); the
-- qualifier keeps the record module (`Cl.Ctx.size`, not `Cl.size`: Cl has no top-level
-- `size`), and every new import line sits at the statement's indentation; an indented
-- copy inside a nested module keeps that block's indentation
module Main where

open import E
  using (N; Ctx; lk; infer)

s : Ctx → N
s ctx = Ctx.size ctx

t : Ctx → N
t ctx = infer ctx

module Inner where
    open import E
      using (N; Ctx; lk)

    u : Ctx → N
    u ctx = Ctx.size ctx
