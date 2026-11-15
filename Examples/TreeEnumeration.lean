import Applications.Trees.Enumeration

/-! Exact small enumerations and uses of their general membership and
distinctness laws. Equal labels retain different ordered tree shapes.
-/
set_option autoImplicit false
set_option warningAsError true

namespace TreeEnumerationExamples
open Trees
universe u
variable {α : Type u}

theorem empty_label_enum : enumTree ([] : List Empty) = [.nil] := enumTree_nil

theorem empty_label_nodup : (enumTree ([] : List Empty)).Nodup := enumTree_nodup []

theorem singleton_enum (a : α) : enumTree [a] = [.node a .nil .nil] := rfl

theorem pair_enum (a b : α) :
    enumTree [a, b] =
      [.node a .nil (.node b .nil .nil), .node b (.node a .nil .nil) .nil] := rfl

/-- The duplicate-free theorem applies even when the input labels coincide. -/
theorem repeated_shapes_nodup (a : α) :
    ([.node a .nil (.node a .nil .nil), .node a (.node a .nil .nil) .nil] :
      List (BinaryTree α)).Nodup := by
  simpa only [pair_enum] using enumTree_nodup [a, a]

theorem repeated_shapes_distinct (a : α) :
    (.node a .nil (.node a .nil .nil) : BinaryTree α) ≠
      .node a (.node a .nil .nil) .nil := by
  intro h
  have hleft : (.nil : BinaryTree α) = .node a .nil .nil :=
    congrArg BinaryTree.left h
  cases hleft

theorem three_enum :
    enumTree ([1, 2, 3] : List Nat) =
      [.node 1 .nil (.node 2 .nil (.node 3 .nil .nil)),
        .node 2 (.node 1 .nil .nil) (.node 3 .nil .nil),
        .node 1 .nil (.node 3 (.node 2 .nil .nil) .nil),
        .node 3 (.node 1 .nil (.node 2 .nil .nil)) .nil,
        .node 3 (.node 2 (.node 1 .nil .nil) .nil) .nil] := rfl

theorem three_nodup : (enumTree ([1, 2, 3] : List Nat)).Nodup := enumTree_nodup [1, 2, 3]

def sample : BinaryTree Nat := .node 9 (.node 3 .nil .nil) (.node 7 .nil .nil)

theorem sample_member : sample ∈ enumTree [3, 9, 7] := by
  apply (mem_enumTree_iff [3, 9, 7] sample).mpr
  rfl

theorem sample_not_wrong_order : sample ∉ enumTree [9, 3, 7] := by
  intro h
  have hi := (mem_enumTree_iff [9, 3, 7] sample).mp h
  simp [sample] at hi

end TreeEnumerationExamples
