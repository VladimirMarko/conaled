import Mathlib.Data.Finset.Basic
import Mathlib.Logic.Relation

/-! Finite connectivity depends only on the vertex set and original edges.
The partition is Mathlib's equivalence closure on the valid vertex subtype. -/
set_option autoImplicit false
set_option warningAsError true

namespace Connectivity

variable {α : Type*}

/-- The least equivalence relation containing the requested edges. -/
def partition (vs : Finset α) (edges : List (α × α)) : Setoid {v // v ∈ vs} where
  r := Relation.EqvGen (fun u v => (u.val, v.val) ∈ edges)
  iseqv := Relation.EqvGen.is_equivalence _

/-- Invalid vertices have no connectivity observation, including with themselves. -/
def Connected (vs : Finset α) (edges : List (α × α)) (u v : α) : Prop :=
  ∃ (hu : u ∈ vs) (hv : v ∈ vs), (partition vs edges).r ⟨u, hu⟩ ⟨v, hv⟩

theorem Connected.refl {vs : Finset α} {edges : List (α × α)} {u : α}
    (hu : u ∈ vs) : Connected vs edges u u :=
  ⟨hu, hu, .refl _⟩

theorem Connected.edge {vs : Finset α} {edges : List (α × α)} {u v : α}
    (hu : u ∈ vs) (hv : v ∈ vs) (he : (u, v) ∈ edges) : Connected vs edges u v :=
  ⟨hu, hv, .rel _ _ he⟩

theorem Connected.symm {vs : Finset α} {edges : List (α × α)} {u v : α}
    (h : Connected vs edges u v) : Connected vs edges v u := by
  obtain ⟨hu, hv, h⟩ := h
  exact ⟨hv, hu, .symm _ _ h⟩

theorem Connected.trans {vs : Finset α} {edges : List (α × α)} {u v w : α}
    (h : Connected vs edges u v) (k : Connected vs edges v w) :
    Connected vs edges u w := by
  obtain ⟨hu, hv, h⟩ := h
  obtain ⟨_, hw, k⟩ := k
  exact ⟨hu, hw, .trans _ _ _ h k⟩

/-- A representation-independent query specification, including the invalid domain. -/
noncomputable def observe (vs : Finset α) (edges : List (α × α)) (u v : α) : Option Bool :=
  open Classical in
  if u ∈ vs ∧ v ∈ vs then some (decide (Connected vs edges u v)) else none

theorem observe_true_iff (vs : Finset α) (edges : List (α × α)) (u v : α) :
    observe vs edges u v = some true ↔ Connected vs edges u v := by
  classical
  simp only [observe]
  split
  · simp
  · rename_i h
    constructor
    · intro bad; cases bad
    · rintro ⟨hu, hv, _⟩
      exact False.elim (h ⟨hu, hv⟩)

theorem observe_none_iff (vs : Finset α) (edges : List (α × α)) (u v : α) :
    observe vs edges u v = none ↔ ¬ (u ∈ vs ∧ v ∈ vs) := by
  classical
  simp [observe]

theorem observe_false_iff (vs : Finset α) (edges : List (α × α)) (u v : α) :
    observe vs edges u v = some false ↔ u ∈ vs ∧ v ∈ vs ∧ ¬ Connected vs edges u v := by
  classical
  unfold observe
  split
  · rename_i h
    simp [h.1, h.2]
  · rename_i h
    constructor
    · intro bad; cases bad
    · rintro ⟨hu, hv, _⟩
      exact False.elim (h ⟨hu, hv⟩)

/-- Negating a successful query retains an edge only between distinct components. -/
theorem observe_retain_iff (vs : Finset α) (edges : List (α × α)) (u v : α) :
    (observe vs edges u v).map Bool.not = some true ↔
      u ∈ vs ∧ v ∈ vs ∧ ¬ Connected vs edges u v := by
  rw [← observe_false_iff]
  cases observe vs edges u v with
  | none => simp
  | some b => cases b <;> simp

end Connectivity
