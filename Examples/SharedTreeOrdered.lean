import Applications.Search.SharedTree.OrderedObservation

/-! Ordered value semantics connected to actual retained cell addresses. -/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.SharedTreeOrdered
open Search.SharedTree

private def leftCell : Store Nat × Root := allocate empty 1 none none
private def rightCell : Store Nat × Root := allocate leftCell.1 5 none none
private def original : Store Nat × Root := allocate rightCell.1 3 leftCell.2 rightCell.2
private def value : BinaryTree Nat :=
  .node 3 (.node 1 .nil .nil) (.node 5 .nil .nil)

private theorem original_rep : Represents original.1.heap original.2 value := by
  have hl : Represents leftCell.1.heap leftCell.2 (.node 1 .nil .nil) :=
    allocate_represents .nil .nil 1
  have hr : Represents rightCell.1.heap rightCell.2 (.node 5 .nil .nil) :=
    allocate_represents .nil .nil 5
  exact allocate_represents (hl.mono (allocate_extends leftCell.1 5 none none)) hr 3

private theorem original_ordered : Search.OrderedTree.Ordered value := by
  simp [value, Search.OrderedTree.Ordered, Search.OrderedTree.OrderedBy,
    Search.OrderedTree.All]

/-- Inserting 2 copies two ancestors and creates one leaf. The right subtree
remains the very same root, and the whole old version still observes its tree. -/
theorem insert_two : ∃ out,
    insertRun original.1 original.2 2 = (some out, (3, 3, 3)) ∧
    Represents out.1.heap out.2
      (.node 3 (.node 1 .nil (.node 2 .nil .nil)) (.node 5 .nil .nil)) ∧
    Represents out.1.heap original.2 value ∧ out.1.next = 6 ∧
    follow out.1.heap [.right] out.2 = some rightCell.2 := by
  obtain ⟨out, run, extension, rep, count, rebuilt⟩ := insertRun_correct original_rep 2
  refine ⟨out, run, rep, original_rep.mono extension, count, ?_⟩
  have shared := rebuilt.off_path extension [.right]
    (by simp [Diverges, searchPath, searchPathBy, value])
  exact shared.trans (follow_mono extension
    (by rfl : follow original.1.heap [.right] original.2 = some rightCell.2))

/-- Baseline duplicate insertion still copies the ancestor above the match.
Equal resulting values do not imply that the original root was returned. -/
theorem baseline_duplicate : ∃ out,
    insertRun original.1 original.2 1 = (some out, (3, 2, 1)) ∧
    Represents out.1.heap out.2 value ∧ out.1.next = 4 ∧ out.2 ≠ original.2 := by
  obtain ⟨out, run, _, rep, count, _⟩ := insertRun_correct original_rep 1
  refine ⟨out, run, rep, count, ?_⟩
  have roots := congrArg (fun result => result.1.map Prod.snd) run
  change some (some 3) = some out.2 at roots
  have address : out.2 = some 3 := (Option.some.inj roots).symm
  rw [address]
  decide

/-- The same observed value satisfies the independent ordered-set contract. -/
theorem insertion_preserves_order : Search.OrderedTree.Ordered
    (.node 3 (.node 1 .nil (.node 2 .nil .nil)) (.node 5 .nil .nil)) :=
  Search.OrderedTree.ordered_insert original_ordered 2

/-- Composition retains the outer execution result and the inner root label. -/
theorem inserted_root_observation :
    (insertRun original.1 original.2 2).1.map rootValue = some (some 3) :=
  insertRun_rootValue_correct original_rep 2

/-- The physical execution supplies a valid set insertion and retains the
original version, with membership described independently of its search path. -/
theorem inserted_set_contents : ∃ out,
    insertRun original.1 original.2 2 = (some out, (3, 3, 3)) ∧
    Represents out.1.heap out.2 (Search.OrderedTree.insert 2 value) ∧
    Represents out.1.heap original.2 value ∧
    Search.OrderedTree.Ordered (Search.OrderedTree.insert 2 value) ∧
    (∀ y, Search.OrderedTree.Contains y (Search.OrderedTree.insert 2 value) ↔
      y = 2 ∨ Search.OrderedTree.Contains y value) :=
  insertRun_ordered original_rep original_ordered 2

end Examples.SharedTreeOrdered
