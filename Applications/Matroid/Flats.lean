import Applications.Matroid.Presentations
import Mathlib.Order.CompleteLatticeIntervals

/-! # The lattice of embedded flats

Flats retain their subsets of the labelled ground. Forgetting those subsets
leaves an abstract lattice; it need not retain loops or parallel multiplicities.
-/
set_option autoImplicit false
set_option warningAsError true

open Set
namespace Applications.Matroid

/-- Closed subsets of the ground, with their embedding retained. -/
abbrev Flat {α : Type*} (M : _root_.Matroid α) := M.subtypeClosure.Closeds

namespace Flat
variable {α : Type*} (M : _root_.Matroid α)

noncomputable instance : CompleteLattice (Flat M) := M.subtypeClosure.gi.liftCompleteLattice

/-- The underlying labelled subset. -/
def carrier (F : Flat M) : Set α := F.val.val

theorem carrier_subset (F : Flat M) : carrier M F ⊆ M.E := F.val.property

theorem carrier_isFlat (F : Flat M) : M.IsFlat (carrier M F) :=
  M.isClosed_iff_isFlat.mp F.property

/-- Package a native flat without forgetting its labelled subset. -/
def ofIsFlat (F : Set α) (hF : M.IsFlat F) : Flat M :=
  ⟨⟨F, hF.subset_ground⟩, M.isClosed_iff_isFlat.mpr hF⟩

@[simp] theorem carrier_ofIsFlat (F : Set α) (hF : M.IsFlat F) :
    carrier M (ofIsFlat M F hF) = F := rfl

@[ext] theorem ext {F G : Flat M} (h : carrier M F = carrier M G) : F = G :=
  Subtype.ext (Subtype.ext h)

/-- The lattice order is precisely subset inclusion. -/
theorem le_iff {F G : Flat M} : F ≤ G ↔ carrier M F ⊆ carrier M G := Iff.rfl

/-- Generate the least flat containing the ground portion of an ambient set. -/
def span (X : Set α) : Flat M := ofIsFlat M (M.closure X) (M.isFlat_closure X)

@[simp] theorem carrier_span (X : Set α) : carrier M (span M X) = M.closure X := rfl

theorem span_le_iff (X : Set α) (F : Flat M) :
    span M X ≤ F ↔ X ∩ M.E ⊆ carrier M F := by
  change M.closure X ⊆ carrier M F ↔ _
  rw [← M.closure_inter_ground X]
  exact ⟨fun h ↦ (M.subset_closure _ inter_subset_right).trans h,
    fun h ↦ (M.closure_subset_closure h).trans_eq (carrier_isFlat M F).closure⟩

@[simp] theorem carrier_bot : carrier M (⊥ : Flat M) = M.closure ∅ := by
  have h : span M ∅ = ⊥ := bot_unique ((span_le_iff M ∅ ⊥).mpr (by simp))
  exact congrArg (carrier M) h.symm
@[simp] theorem carrier_top : carrier M (⊤ : Flat M) = M.E := rfl

end Flat
end Applications.Matroid
