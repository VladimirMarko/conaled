import Applications.Search.SharedTree.OrderedTerminal

/-! A duplicate match below a copied ancestor retains a nonempty child. -/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.SharedTreeTerminal
open Search.SharedTree

private def leaf : Store Nat × Root := allocate empty 1 none none
private def matched : Store Nat × Root := allocate leaf.1 2 leaf.2 none
private def other : Store Nat × Root := allocate matched.1 5 none none
private def original : Store Nat × Root := allocate other.1 4 matched.2 other.2
private def model : BinaryTree Nat :=
  .node 4 (.node 2 (.node 1 .nil .nil) .nil) (.node 5 .nil .nil)

private theorem original_rep : Represents original.1.heap original.2 model := by
  have leafRep : Represents leaf.1.heap leaf.2 (.node 1 .nil .nil) :=
    allocate_represents .nil .nil 1
  have matchedRep : Represents matched.1.heap matched.2
      (.node 2 (.node 1 .nil .nil) .nil) := allocate_represents leafRep .nil 2
  have otherRep : Represents other.1.heap other.2 (.node 5 .nil .nil) :=
    allocate_represents .nil .nil 5
  exact allocate_represents (matchedRep.mono (allocate_extends matched.1 5 none none))
    otherRep 4

private theorem model_ordered : Search.OrderedTree.Ordered model := by
  simp [model, Search.OrderedTree.Ordered, Search.OrderedTree.OrderedBy,
    Search.OrderedTree.All]

private theorem contains_two : Search.OrderedTree.Contains 2 model := by
  simp [model, Search.OrderedTree.Contains]

/-- Searching for 2 copies the root 4, returns the old root of the subtree at
2, and keeps the old address of its nonempty child 1. The retained subtree is
not an ancestor's unselected branch: the search terminates at its root. -/
theorem duplicate_retains_terminal_and_child : ∃ out,
    insertRun original.1 original.2 2 = (some out, (3, 2, 1)) ∧
      out.1.next = 5 ∧
      follow out.1.heap [.left] out.2 = some matched.2 ∧
      follow out.1.heap [.left, .left] out.2 = some leaf.2 ∧
      Represents out.1.heap original.2 model := by
  obtain ⟨out, address, run, extension, count, oldEndpoint, newEndpoint, kept, descendants⟩ :=
    insertRun_duplicate_subtree original_rep model_ordered contains_two
  have oldFocus : follow original.1.heap (searchPath 2 model) original.2 = some matched.2 :=
    rfl
  have focus : some address = matched.2 := Option.some.inj (oldEndpoint.symm.trans oldFocus)
  have oldChild : follow original.1.heap [.left, .left] original.2 = some leaf.2 := rfl
  have sameChild := descendants [.left]
  refine ⟨out, run, count, ?_, ?_, kept⟩
  · simpa only [focus] using newEndpoint
  · exact sameChild.trans (follow_mono extension oldChild)

/-- The common matched endpoint also makes every deeper path agree, including
one that continues beyond the retained leaf and therefore fails. -/
theorem duplicate_retains_deep_observation : ∃ out,
    insertRun original.1 original.2 2 = (some out, (3, 2, 1)) ∧
      follow out.1.heap [.left, .left, .right, .left] out.2 = none := by
  obtain ⟨out, _, run, extension, _, oldEndpoint, newEndpoint, _, descendants⟩ :=
    insertRun_duplicate_subtree original_rep model_ordered contains_two
  have same := descendants [.left, .right, .left]
  have oldLeaf : follow original.1.heap [.left, .left] original.2 = some leaf.2 := rfl
  have keptLeaf := follow_mono extension oldLeaf
  refine ⟨out, run, ?_⟩
  rw [same]
  change follow out.1.heap ([.left, .left] ++ [.right, .left]) original.2 = none
  rw [follow_append, keptLeaf]
  change follow out.1.heap [.right, .left] leaf.2 = none
  have leafLookup : original.1.heap 0 = some ((1, none), none) := rfl
  rw [show leaf.2 = some 0 from rfl, follow_step (extension _ _ leafLookup)]
  rfl

end Examples.SharedTreeTerminal
