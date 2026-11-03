import Mathlib.Combinatorics.Quiver.Path
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.Common

/-!
# Logical histories of operation occurrences

A history contains the vertices with a possibly empty path to the observed
vertex. The underlying quiver retains distinct argument-use arrows, loops and
cycles. No chronological order, acyclicity or single-identity restriction is
part of this graph interface. Finite accounted scopes carry a separate
closure condition. Concrete source incidence and execution correspondence are
additional obligations of a realization.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.Persistent

universe uV uW uE uF
variable {V : Type uV} [Quiver.{uE} V]

def history (v : V) : Set V := {u | Nonempty (Quiver.Path u v)}

theorem history_refl (v : V) : v ∈ history v := ⟨Quiver.Path.nil⟩

theorem history_of_path {u v : V} (path : Quiver.Path u v) : u ∈ history v :=
  ⟨path⟩

theorem history_of_edge {u v : V} (edge : u ⟶ v) : u ∈ history v :=
  history_of_path edge.toPath

theorem history_trans {u v w : V}
    (before : u ∈ history v) (after : v ∈ history w) : u ∈ history w := by
  obtain ⟨first⟩ := before
  obtain ⟨second⟩ := after
  exact history_of_path (first.comp second)

/-- A vertex with no outgoing use can only occur in its own history.
The empty path remains available. -/
theorem history_eq_of_no_outgoing {u v : V}
    (noOutgoing : ∀ w, (u ⟶ w) → False) (reached : u ∈ history v) : u = v := by
  obtain ⟨path⟩ := reached
  induction path with
  | nil => rfl
  | cons _ edge ih =>
      cases ih
      exact (noOutgoing _ edge).elim

/-- Every logical predecessor of an accounted occurrence is also accounted. -/
def HistoryClosed (scope : Finset V) : Prop :=
  ∀ ⦃v⦄, v ∈ scope → ∀ ⦃u⦄, u ∈ history v → u ∈ scope

theorem HistoryClosed.empty : HistoryClosed (∅ : Finset V) := by
  intro _ member
  simp at member

theorem HistoryClosed.union [DecidableEq V] {s t : Finset V}
    (left : HistoryClosed s) (right : HistoryClosed t) : HistoryClosed (s ∪ t) := by
  intro _ member _ reached
  rcases Finset.mem_union.mp member with member | member
  · exact Finset.mem_union.mpr (Or.inl (left member reached))
  · exact Finset.mem_union.mpr (Or.inr (right member reached))

theorem HistoryClosed.inter [DecidableEq V] {s t : Finset V}
    (left : HistoryClosed s) (right : HistoryClosed t) : HistoryClosed (s ∩ t) := by
  intro _ member _ reached
  obtain ⟨inLeft, inRight⟩ := Finset.mem_inter.mp member
  exact Finset.mem_inter.mpr ⟨left inLeft reached, right inRight reached⟩

/-- Ordinary graph maps preserve history membership by mapping its path.
This does not assert reflection or closure of an image in a larger graph. -/
theorem history_map {W : Type uW} [Quiver.{uF} W] (map : Prefunctor V W)
    {u v : V} (reached : u ∈ history v) : map.obj u ∈ history (map.obj v) := by
  obtain ⟨path⟩ := reached
  exact history_of_path (map.mapPath path)

end Resources.Persistent
