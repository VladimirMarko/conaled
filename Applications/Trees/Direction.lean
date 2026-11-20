/-!
# Directions shared by pure trees and persistent tree paths

The original `Search.SharedTree.Branch` name is retained. Its declaration lives
here so pure tree operations need no heap implementation merely to share paths.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Search.SharedTree

inductive Branch where
  | left
  | right
  deriving DecidableEq, Repr

end Search.SharedTree
