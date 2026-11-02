import Applications.Search.SharedTree.Basic

/-! Connected cases for immutable binary-tree observations and sharing. -/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.SharedTree

open Search.SharedTree

def leaf : Store Nat × Root := allocate empty 7 none none
def fork : Store Nat × Root := allocate leaf.1 9 leaf.2 leaf.2

theorem leaf_observes : Represents leaf.1.heap leaf.2 (.node 7 .nil .nil) :=
  allocate_represents .nil .nil 7

/-- Two logical child occurrences use one previously allocated cell. -/
theorem fork_observes :
    Represents fork.1.heap fork.2
      (.node 9 (.node 7 .nil .nil) (.node 7 .nil .nil)) :=
  allocate_represents leaf_observes leaf_observes 9

theorem fork_shares_child : read fork.1 fork.2 = some ((9, leaf.2), leaf.2) :=
  read_allocate leaf.1 9 leaf.2 leaf.2

theorem leaf_survives : Represents fork.1.heap leaf.2 (.node 7 .nil .nil) :=
  allocate_retains leaf.1 9 leaf.2 leaf.2 leaf.2 _ leaf_observes

end Examples.SharedTree
