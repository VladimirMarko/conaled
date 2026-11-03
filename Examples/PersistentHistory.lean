import Applications.Resources.Persistent.History

/-!
# Persistent-history graph cases

These examples establish representational and logical-history properties of
the public quiver interface. They do not claim that every raw graph is a
concrete source execution. The first graph retains a two-node cycle, a loop
and two distinct uses with the same endpoints. The second has two inputs and
two results, including a dependency crossing an explicit identity label.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.PersistentHistory
open Resources.Persistent

namespace Cycle

inductive Vertex where
  | left | right
  deriving DecidableEq

inductive Use : Vertex → Vertex → Type where
  | forward₀ : Use .left .right
  | forward₁ : Use .left .right
  | backward : Use .right .left
  | loop : Use .left .left

instance : Quiver Vertex where
  Hom := Use

/-- Parallel arrows remain distinct even though both support the same history
membership proposition. -/
theorem parallel_uses :
    Use.forward₀ ≠ Use.forward₁ ∧
      Vertex.left ∈ history Vertex.right ∧ Vertex.left ∈ history Vertex.right := by
  refine ⟨?_, history_of_edge Use.forward₀, history_of_edge Use.forward₁⟩
  intro same
  cases same

def roundTrip : Quiver.Path Vertex.left Vertex.left :=
  (Quiver.Hom.toPath (V := Vertex) Use.forward₀).comp
    (Quiver.Hom.toPath (V := Vertex) Use.backward)

theorem roundTrip_length : roundTrip.length = 2 := by simp [roundTrip]

/-- Two proper edges compose; self-history is not restricted to its empty
path witness. -/
theorem roundTrip_history : Vertex.left ∈ history Vertex.left :=
  history_trans (history_of_edge Use.forward₀) (history_of_edge Use.backward)

theorem loop_length_and_history :
    (Quiver.Hom.toPath (V := Vertex) Use.loop).length = 1 ∧
      Vertex.left ∈ history Vertex.left :=
  ⟨Quiver.Path.length_toPath (V := Vertex) Use.loop, history_of_edge Use.loop⟩

theorem empty_path_history : Vertex.right ∈ history Vertex.right :=
  history_refl Vertex.right

/-- Logical history is not antisymmetric on admitted raw graphs. -/
theorem history_is_not_antisymmetric :
    Vertex.left ∈ history Vertex.right ∧ Vertex.right ∈ history Vertex.left ∧
      Vertex.left ≠ Vertex.right :=
  ⟨history_of_edge Use.forward₀, history_of_edge Use.backward, by decide⟩

theorem full_scope_closed : HistoryClosed ({Vertex.left, Vertex.right} : Finset Vertex) := by
  intro _ _ u _
  cases u <;> simp

/-- The omitted predecessor is an explicit witness to the open boundary. -/
theorem singleton_scope_not_closed : ¬ HistoryClosed ({Vertex.left} : Finset Vertex) := by
  intro closed
  have absent : Vertex.right ∈ ({Vertex.left} : Finset Vertex) :=
    closed (v := Vertex.left) (by simp) (history_of_edge Use.backward)
  simp at absent

structure CopiedVertex where
  original : Vertex

instance : Quiver CopiedVertex where
  Hom u v := Use u.original v.original

def copyGraph : Prefunctor Vertex CopiedVertex where
  obj := CopiedVertex.mk
  map edge := edge

/-- Transport reuses Mathlib's graph map and the public history theorem. -/
theorem copied_cycle :
    copyGraph.obj Vertex.left ∈ history (copyGraph.obj Vertex.right) ∧
      copyGraph.obj Vertex.right ∈ history (copyGraph.obj Vertex.left) :=
  ⟨history_map copyGraph (history_of_edge Use.forward₀),
    history_map copyGraph (history_of_edge Use.backward)⟩

end Cycle

namespace Join

inductive Vertex where
  | first | second | combine | leftResult | rightResult
  deriving DecidableEq

inductive Use : Vertex → Vertex → Type where
  | firstInput : Use .first .combine
  | secondInput : Use .second .combine
  | leftOutput : Use .combine .leftResult
  | rightOutput : Use .combine .rightResult

instance : Quiver Vertex where
  Hom := Use

def identity : Vertex → Nat
  | .first | .leftResult => 0
  | .second | .rightResult => 1
  | .combine => 2

theorem distinct_inputs_and_results :
    Vertex.first ≠ Vertex.second ∧ Vertex.leftResult ≠ Vertex.rightResult := by decide

theorem both_inputs :
    Vertex.first ∈ history Vertex.combine ∧ Vertex.second ∈ history Vertex.combine :=
  ⟨history_of_edge Use.firstInput, history_of_edge Use.secondInput⟩

private theorem source_scope_closed (v : Vertex)
    (noIncoming : ∀ u, (u ⟶ v) → False) : HistoryClosed ({v} : Finset Vertex) := by
  intro w member u reached
  have same : w = v := by simpa using member
  subst w
  obtain ⟨path⟩ := reached
  cases path with
  | nil => simp
  | cons _ edge => exact (noIncoming _ edge).elim

theorem first_scope_closed : HistoryClosed ({Vertex.first} : Finset Vertex) :=
  source_scope_closed Vertex.first (fun _ edge => by cases edge)

theorem second_scope_closed : HistoryClosed ({Vertex.second} : Finset Vertex) :=
  source_scope_closed Vertex.second (fun _ edge => by cases edge)

/-- Independent input scopes combine to the two-input scope, and their
intersection is empty. Both conclusions use the public closure laws. -/
theorem input_scope_combinations :
    HistoryClosed ({Vertex.first, Vertex.second} : Finset Vertex) ∧
      HistoryClosed (∅ : Finset Vertex) := by
  constructor
  · have combined : ({Vertex.first} : Finset Vertex) ∪ {Vertex.second} =
        {Vertex.first, Vertex.second} := by decide
    rw [← combined]
    exact HistoryClosed.union first_scope_closed second_scope_closed
  · have overlap : ({Vertex.first} : Finset Vertex) ∩ {Vertex.second} = ∅ := by decide
    rw [← overlap]
    exact HistoryClosed.inter first_scope_closed second_scope_closed

/-- Each result inherits both input histories through the combining node. -/
theorem both_results_have_both_inputs :
    Vertex.first ∈ history Vertex.leftResult ∧
      Vertex.second ∈ history Vertex.leftResult ∧
      Vertex.first ∈ history Vertex.rightResult ∧
      Vertex.second ∈ history Vertex.rightResult :=
  ⟨history_trans (history_of_edge Use.firstInput) (history_of_edge Use.leftOutput),
    history_trans (history_of_edge Use.secondInput) (history_of_edge Use.leftOutput),
    history_trans (history_of_edge Use.firstInput) (history_of_edge Use.rightOutput),
    history_trans (history_of_edge Use.secondInput) (history_of_edge Use.rightOutput)⟩

theorem history_crosses_identities :
    identity Vertex.second ≠ identity Vertex.leftResult ∧
      Vertex.second ∈ history Vertex.leftResult :=
  ⟨by decide, history_trans (history_of_edge Use.secondInput) (history_of_edge Use.leftOutput)⟩

/-- A common predecessor does not place either result in its sibling's history. -/
theorem results_are_incomparable :
    Vertex.leftResult ∉ history Vertex.rightResult ∧
      Vertex.rightResult ∉ history Vertex.leftResult := by
  constructor
  · intro reached
    have same := history_eq_of_no_outgoing
      (u := Vertex.leftResult) (v := Vertex.rightResult)
      (fun _ edge => by cases edge) reached
    cases same
  · intro reached
    have same := history_eq_of_no_outgoing
      (u := Vertex.rightResult) (v := Vertex.leftResult)
      (fun _ edge => by cases edge) reached
    cases same

end Join

end Examples.PersistentHistory
