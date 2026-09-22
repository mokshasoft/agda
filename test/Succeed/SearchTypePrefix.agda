-- A goal that is itself a function type.
--
-- `twice` closes a goal `Tm → Tm` by being applied to no arguments at all,
-- and closes a goal `Tm` by being applied to one.  Matching only the fully
-- applied conclusion would find the second and silently miss the first, so
-- every prefix of the telescope is tried.
--
-- `atom` has the wrong shape for this goal and must not appear.
module SearchTypePrefix where

postulate
  Tm    : Set
  atom  : Tm
  twice : Tm → Tm
  const : Tm → Tm → Tm
