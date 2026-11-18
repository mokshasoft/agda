-- --remove-dead-imports: the first statement's only item `T` is dead, but
-- `DeadQualLaterA.f` is written before the second statement on the same
-- module: a later statement does not scope an earlier qualified use, so the
-- first becomes `import DeadQualLaterA` (D15).
module DeadQualLater where

open import DeadQualLaterA using (T)

module Inner where
  open import DeadQualLaterA using (f)
  g : _
  g = f

u = DeadQualLaterA.f DeadQualLaterA.t

open import DeadQualLaterA using (t)

v = t
