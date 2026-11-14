import Applications.Search.SharedTree.Map

/-! Concrete stored maps distinguish failed lookup, optional payloads,
ancestor sharing and replacement-node child sharing. -/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.SharedTreeMap
open Search.SharedTree

private def lower : Store (Nat × Option Nat) × Root :=
  allocate empty (1, some 7) none none

private def upper : Store (Nat × Option Nat) × Root :=
  allocate lower.1 (3, none) none none

private def initial : Store (Nat × Option Nat) × Root :=
  allocate upper.1 (2, some 4) lower.2 upper.2

private def model : BinaryTree (Nat × Option Nat) :=
  .node (2, some 4) (.node (1, some 7) .nil .nil) (.node (3, none) .nil .nil)

private theorem lower_rep :
    Represents lower.1.heap lower.2 (.node (1, some 7) .nil .nil) :=
  allocate_represents .nil .nil (1, some 7)

private theorem upper_rep :
    Represents upper.1.heap upper.2 (.node (3, none) .nil .nil) :=
  allocate_represents .nil .nil (3, none)

private theorem initial_rep : Represents initial.1.heap initial.2 model :=
  allocate_represents (lower_rep.mono (allocate_extends lower.1 (3, none) none none))
    upper_rep (2, some 4)

private theorem model_ordered : Search.OrderedTree.OrderedBy Prod.fst model := by
  simp [model, Search.OrderedTree.OrderedBy, Search.OrderedTree.All]

theorem lookup_present_none : (Map.lookupRun initial.1 initial.2 3).1 = some none := by
  have h := Map.lookupRun_observes initial_rep model_ordered 3
  exact h.trans (by rfl)

theorem lookup_missing : Map.lookupRun initial.1 initial.2 4 = (none, (4, 3)) :=
  Map.lookupRun_correct initial_rep 4

/-- A replacement at the root allocates one cell and reuses both nonempty
child addresses. The old root still returns its previous payload. -/
theorem replacement_keeps_children :
    ∃ out, Map.bindRun initial.1 initial.2 2 none = (some out, (2, 1, 1)) ∧
      out.1.next = 4 ∧
      read out.1 out.2 = some (((2, none), lower.2), upper.2) ∧
      Represents out.1.heap initial.2 model ∧
      (Map.lookupRun out.1 out.2 2).1 = some none ∧
      (Map.lookupRun out.1 initial.2 2).1 = some (some 4) := by
  obtain ⟨out, run, extension, rep, count, _, written⟩ := Map.bindRun_correct initial_rep 2 none
  have oldLookup : initial.2.bind initial.1.heap = some (((2, some 4), lower.2), upper.2) :=
    read_allocate upper.1 (2, some 4) lower.2 upper.2
  have kept := initial_rep.mono extension
  refine ⟨out, run, count, ?_, kept, ?_, ?_⟩
  · exact written.nil_children oldLookup
  · exact (congrArg Prod.fst (Map.lookupRun_correct rep 2)).trans (by rfl)
  · exact (congrArg Prod.fst (Map.lookupRun_correct kept 2)).trans (by rfl)

/-- Replacing a left child copies both nodes on that path and preserves the
actual address of the untouched right subtree. -/
theorem descendant_preserves_other_branch :
    ∃ out, Map.bindRun initial.1 initial.2 1 (some 8) = (some out, (3, 2, 2)) ∧
      out.1.next = 5 ∧
      follow out.1.heap [.right] out.2 = some upper.2 ∧
      (Map.lookupRun out.1 out.2 1).1 = some (some 8) ∧
      (Map.lookupRun out.1 initial.2 1).1 = some (some 7) := by
  obtain ⟨out, run, extension, rep, count, rebuilt, _⟩ :=
    Map.bindRun_correct initial_rep 1 (some 8)
  have oldRight : follow initial.1.heap [.right] initial.2 = some upper.2 := rfl
  have kept := initial_rep.mono extension
  refine ⟨out, run, count, ?_, ?_, ?_⟩
  · exact (rebuilt.off_path extension [.right] (by trivial)).trans
      (follow_mono extension oldRight)
  · exact (congrArg Prod.fst (Map.lookupRun_correct rep 1)).trans (by rfl)
  · exact (congrArg Prod.fst (Map.lookupRun_correct kept 1)).trans (by rfl)

/-- The shared implementation consumes the same all-key binding law as a map
client, including an unrelated key with an optional-none payload. -/
theorem graph_update_law :
    ∃ out, Map.bindRun initial.1 initial.2 1 (some 8) = (some out, (3, 2, 2)) ∧
      (Map.lookupRun out.1 out.2 1).1 = some (some 8) ∧
      (Map.lookupRun out.1 out.2 3).1 = some none := by
  obtain ⟨out, run, _, observes⟩ := Map.bind_lookup initial_rep 1 (some 8)
  refine ⟨out, run, ?_, ?_⟩
  · simpa using observes 1
  · simpa [lookup_present_none] using observes 3

/-- The existing relational-square interface observes this concrete stored map. -/
theorem lookup_square_instance :
    (Map.lookupSquare (ν := Option Nat) 3).impl initial = some none := by
  have h := (Map.lookupSquare (ν := Option Nat) 3).preserves
    (r := initial) (s := model) initial_rep
  exact h.trans (by rfl)

/-- The physically composed client observes a stored optional-none value. -/
theorem composed_present_none :
    (Map.bindThenLookupSquare 1 (some 8) 3).impl initial = some (some none) := by
  have h := Map.bindThenLookup_correct initial_rep 1 (some 8) 3
  exact h.trans (by rfl)

/-- A successful physical bind followed by a missing lookup is distinct. -/
theorem composed_missing :
    (Map.bindThenLookupSquare 1 (some 8) 4).impl initial = some none := by
  have h := Map.bindThenLookup_correct initial_rep 1 (some 8) 4
  exact h.trans (by rfl)

end Examples.SharedTreeMap
