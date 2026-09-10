-- Check that --write-ast reports the trust base reachable from the entry
-- point, and only the trust base that is actually reachable.
module WriteASTBasic where

data Bool : Set where
  true false : Bool

postulate
  reachedAxiom : Bool

-- Not reachable from `main`, so it must NOT appear in the trust base.
postulate
  unreachedAxiom : Bool

helper : Bool
helper = reachedAxiom

main : Bool
main = helper
