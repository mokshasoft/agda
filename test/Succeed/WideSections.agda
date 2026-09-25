-- --wide-sections reports how much ambient context a section abstracts
-- over.  A section is a module, so this covers both shapes that silently
-- widen a definition's context:
--
--   * a `where` block, whose contents are lifted out over the enclosing
--     pattern variables;
--   * a module application, which copies every member of the applied module
--     into that same context.
--
-- Neither says so in the source.  `M = Inner x y z` is one line, and it
-- creates two definitions each abstracting over the three variables of `f`.
-- The product is the real size of the line; in a large development this is
-- how a 286-line proof becomes unbuildable.
module WideSections where

postulate
  A : Set
  a : A

module Inner (x y z : A) where
  postulate
    p : A
    q : A

f : A → A → A → A
f x y z = g
  where
    module M = Inner x y z

    g : A
    g = M.p
