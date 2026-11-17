import Applications.Matroid.Closure
import Mathlib.Combinatorics.Matroid.Circuit

/-! # Circuit presentations

This adapter uses augmentation of circuit-free sets as its exchange condition.
It does not require a pre-existing matroid, or a witness of realizability.
-/

set_option autoImplicit false
set_option warningAsError true

open Set

namespace Applications.Matroid

/-- A finite circuit presentation with exchange expressed on circuit-free sets. -/
structure CircuitPresentation (α : Type*) where
  ground : Set α
  finite_ground : ground.Finite
  IsCircuit : Set α → Prop
  subset_ground : ∀ {C}, IsCircuit C → C ⊆ ground
  nonempty : ∀ {C}, IsCircuit C → C.Nonempty
  antichain : ∀ {C D}, IsCircuit C → IsCircuit D → C ⊆ D → C = D
  augment : ∀ {I B},
    (I ⊆ ground ∧ ∀ C ⊆ I, ¬ IsCircuit C) →
    ¬ Maximal (fun J ↦ J ⊆ ground ∧ ∀ C ⊆ J, ¬ IsCircuit C) I →
    Maximal (fun J ↦ J ⊆ ground ∧ ∀ C ⊆ J, ¬ IsCircuit C) B →
    ∃ e ∈ B \ I, insert e I ⊆ ground ∧ ∀ C ⊆ insert e I, ¬ IsCircuit C

namespace CircuitPresentation
variable {α : Type*} (P : CircuitPresentation α)

/-- Independence is avoidance of every circuit, within the labelled ground. -/
def Indep (I : Set α) : Prop := I ⊆ P.ground ∧ ∀ C ⊆ I, ¬ P.IsCircuit C

noncomputable def matroid : _root_.Matroid α :=
  (IndepMatroid.ofBdd P.ground P.Indep
    ⟨empty_subset _, fun C h hc ↦ (P.nonempty hc).ne_empty (subset_empty_iff.mp h)⟩
    (fun _ _ h hsub ↦ ⟨hsub.trans h.1, fun C hc ↦ h.2 C (hc.trans hsub)⟩)
    (fun _ _ ↦ P.augment) (fun _ h ↦ h.1)
    ⟨P.ground.ncard, fun I h ↦ by
      rw [P.finite_ground.cast_ncard_eq]
      exact encard_le_encard h.1⟩).matroid

@[simp] theorem matroid_ground : P.matroid.E = P.ground := rfl
@[simp] theorem matroid_indep {I : Set α} : P.matroid.Indep I ↔ P.Indep I := Iff.rfl
instance : P.matroid.Finite := ⟨P.finite_ground⟩

@[simp] theorem matroid_isCircuit {C : Set α} : P.matroid.IsCircuit C ↔ P.IsCircuit C := by
  classical
  constructor
  · intro hc
    have hn : ¬ ∀ D ⊆ C, ¬ P.IsCircuit D := fun h ↦ hc.not_indep ⟨hc.subset_ground, h⟩
    push Not at hn
    obtain ⟨D, hDC, hD⟩ := hn
    have hd : P.matroid.Dep D := ⟨fun hi ↦ hi.2 D Subset.rfl hD, P.subset_ground hD⟩
    have heq := (_root_.Matroid.isCircuit_iff.mp hc).2 hd hDC
    exact heq ▸ hD
  · intro hc
    apply _root_.Matroid.isCircuit_iff.mpr
    refine ⟨⟨fun hi ↦ hi.2 C Subset.rfl hc, P.subset_ground hc⟩, ?_⟩
    intro D hd hDC
    have hn : ¬ ∀ K ⊆ D, ¬ P.IsCircuit K := fun h ↦ hd.not_indep ⟨hd.subset_ground, h⟩
    push Not at hn
    obtain ⟨K, hKD, hK⟩ := hn
    have heq := P.antichain hK hc (hKD.trans hDC)
    exact hDC.antisymm (heq ▸ hKD)

/-- Native circuits satisfy the adapter's circuit-free exchange contract. -/
def ofMatroid (M : _root_.Matroid α) [M.Finite] : CircuitPresentation α where
  ground := M.E
  finite_ground := M.ground_finite
  IsCircuit := M.IsCircuit
  subset_ground := fun h ↦ h.subset_ground
  nonempty := fun h ↦ h.nonempty
  antichain := fun hC hD h ↦ hC.eq_of_subset_isCircuit hD h
  augment := by
    have hiff : ∀ I, (I ⊆ M.E ∧ ∀ C ⊆ I, ¬ M.IsCircuit C) ↔ M.Indep I := by
      intro I
      rw [M.indep_iff_forall_subset_not_isCircuit']
      exact and_comm
    simp_rw [hiff]
    exact _root_.Matroid.Indep.exists_insert_of_not_maximal M

@[simp] theorem ofMatroid_matroid (M : _root_.Matroid α) [M.Finite] :
    (ofMatroid M).matroid = M := by
  apply _root_.Matroid.ext_isCircuit (M₁ := (ofMatroid M).matroid) (M₂ := M) rfl
  intro C _
  exact (ofMatroid M).matroid_isCircuit

@[simp] theorem matroid_ofMatroid : ofMatroid P.matroid = P := by
  cases P
  simp only [ofMatroid, matroid_ground]
  congr
  exact funext fun C ↦ propext (matroid_isCircuit _)

end CircuitPresentation
end Applications.Matroid
