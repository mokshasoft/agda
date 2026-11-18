-- an applied facade: G's importers get their own copy of G's instance
module G (A : Set) where

import P
module PA = P A
open PA public
