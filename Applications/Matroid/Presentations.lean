import Applications.Matroid.Circuit
import Applications.Matroid.Rank

/-! # Interchangeable finite matroid presentations

Native matroids are the common hub. All reconstruction routes recover the entire
labelled matroid, so native theorems can be reused from every presentation.
-/
set_option autoImplicit false
set_option warningAsError true

open Set

namespace Applications.Matroid

/-- Finite independent-set data, reusing Mathlib's axioms. -/
structure IndependencePresentation (α : Type*) extends IndepMatroid α where
  finite_ground : E.Finite

namespace IndependencePresentation
variable {α : Type*} (P : IndependencePresentation α)

abbrev matroid : _root_.Matroid α := P.toIndepMatroid.matroid
instance : P.matroid.Finite := ⟨P.finite_ground⟩

def ofMatroid (M : _root_.Matroid α) [M.Finite] : IndependencePresentation α where
  E := M.E
  Indep := M.Indep
  indep_empty := M.empty_indep
  indep_subset := fun _ _ h hsub ↦ h.subset hsub
  indep_aug := _root_.Matroid.Indep.exists_insert_of_not_maximal M
  indep_maximal := M.existsMaximalSubsetProperty_indep
  subset_ground := fun _ h ↦ h.subset_ground
  finite_ground := M.ground_finite

@[simp] theorem ofMatroid_matroid (M : _root_.Matroid α) [M.Finite] :
    (ofMatroid M).matroid = M := by
  exact _root_.Matroid.ext_indep (M₁ := (ofMatroid M).matroid) (M₂ := M) rfl (fun _ _ ↦ Iff.rfl)

@[simp] theorem matroid_ofMatroid : ofMatroid P.matroid = P := rfl
end IndependencePresentation

/-- Finite basis-exchange data, with no extra independence predicate. -/
structure BasisPresentation (α : Type*) where
  ground : Set α
  finite_ground : ground.Finite
  IsBase : Set α → Prop
  exists_base : ∃ B, IsBase B
  exchange : _root_.Matroid.ExchangeProperty IsBase
  subset_ground : ∀ B, IsBase B → B ⊆ ground

namespace BasisPresentation
variable {α : Type*} (P : BasisPresentation α)

noncomputable def matroid : _root_.Matroid α :=
  _root_.Matroid.ofIsBaseOfFinite P.finite_ground P.IsBase P.exists_base P.exchange P.subset_ground
instance : P.matroid.Finite := ⟨P.finite_ground⟩

@[simp] theorem matroid_ground : P.matroid.E = P.ground := rfl
@[simp] theorem matroid_isBase {B : Set α} : P.matroid.IsBase B ↔ P.IsBase B := Iff.rfl

def ofMatroid (M : _root_.Matroid α) [M.Finite] : BasisPresentation α where
  ground := M.E
  finite_ground := M.ground_finite
  IsBase := M.IsBase
  exists_base := M.exists_isBase
  exchange := M.isBase_exchange
  subset_ground := fun _ h ↦ h.subset_ground

@[simp] theorem ofMatroid_matroid (M : _root_.Matroid α) [M.Finite] :
    (ofMatroid M).matroid = M := by
  apply _root_.Matroid.ext_indep (M₁ := (ofMatroid M).matroid) (M₂ := M) rfl
  intro I _
  exact M.indep_iff.symm

@[simp] theorem matroid_ofMatroid : ofMatroid P.matroid = P := rfl
end BasisPresentation

/-- Finite matroids with labelled ground, used as a hub rather than a category. -/
abbrev FiniteMatroid (α : Type*) := {M : _root_.Matroid α // M.Finite}

namespace FiniteMatroid
variable {α : Type*}

instance (M : FiniteMatroid α) : M.val.Finite := M.property

noncomputable def closureEquiv : FiniteMatroid α ≃ ClosurePresentation α where
  toFun M := ClosurePresentation.ofMatroid M.val
  invFun P := ⟨P.matroid, inferInstance⟩
  left_inv M := Subtype.ext (ClosurePresentation.ofMatroid_matroid M.val)
  right_inv P := P.matroid_ofMatroid

noncomputable def rankEquiv : FiniteMatroid α ≃ RankPresentation α where
  toFun M := RankPresentation.ofMatroid M.val
  invFun P := ⟨P.matroid, inferInstance⟩
  left_inv M := Subtype.ext (RankPresentation.ofMatroid_matroid M.val)
  right_inv P := P.matroid_ofMatroid

noncomputable def circuitEquiv : FiniteMatroid α ≃ CircuitPresentation α where
  toFun M := CircuitPresentation.ofMatroid M.val
  invFun P := ⟨P.matroid, inferInstance⟩
  left_inv M := Subtype.ext (CircuitPresentation.ofMatroid_matroid M.val)
  right_inv P := P.matroid_ofMatroid

noncomputable def basisEquiv : FiniteMatroid α ≃ BasisPresentation α where
  toFun M := BasisPresentation.ofMatroid M.val
  invFun P := ⟨P.matroid, inferInstance⟩
  left_inv M := Subtype.ext (BasisPresentation.ofMatroid_matroid M.val)
  right_inv P := P.matroid_ofMatroid

noncomputable def independenceEquiv : FiniteMatroid α ≃ IndependencePresentation α where
  toFun M := IndependencePresentation.ofMatroid M.val
  invFun P := ⟨P.matroid, inferInstance⟩
  left_inv M := Subtype.ext (IndependencePresentation.ofMatroid_matroid M.val)
  right_inv P := P.matroid_ofMatroid

/-- Routes through any intermediate presentation agree, as entire objects. -/
theorem route_agreement {P Q T : Type*} (p : FiniteMatroid α ≃ P)
    (q : FiniteMatroid α ≃ Q) (t : FiniteMatroid α ≃ T) (x : P) :
    (q.symm.trans t) ((p.symm.trans q) x) = (p.symm.trans t) x := by simp

end FiniteMatroid
section Relabelling
variable {α β : Type*} (M : _root_.Matroid α) (f : α ≃ β)

/-- Carrier relabelling acts on all labelled elements, including those outside the ground. -/
theorem relabel_indep (I : Set α) : (M.mapEquiv f).Indep (f '' I) ↔ M.Indep I := by
  simp

theorem relabel_circuit (C : Set α) : (M.mapEquiv f).IsCircuit (f '' C) ↔ M.IsCircuit C := by
  simp only [_root_.Matroid.isCircuit_iff_dep_forall_sdiff_singleton_indep,
    _root_.Matroid.mapEquiv_dep_iff, Equiv.symm_image_image, forall_mem_image,
    _root_.Matroid.mapEquiv_indep_iff]
  have h : ∀ e, f.symm '' (f '' C \ {f e}) = C \ {e} := by
    intro e
    rw [← image_singleton, ← image_sdiff f.injective]
    simp
  simp only [h]

theorem relabel_closure (X : Set α) : (M.mapEquiv f).closure (f '' X) = f '' M.closure X := by
  rw [_root_.Matroid.mapEquiv_eq_map, _root_.Matroid.map_closure_eq,
    preimage_image_eq _ f.injective]

private theorem relabel_eq_comap : M.mapEquiv f = M.comap f.symm := by
  apply _root_.Matroid.ext_indep
  · ext x; simp
  · intro I _
    simp [_root_.Matroid.comap_indep_iff, f.symm.injective.injOn]

theorem relabel_rank (X : Set α) : (M.mapEquiv f).eRk (f '' X) = M.eRk X := by
  rw [relabel_eq_comap, _root_.Matroid.eRk_comap, Equiv.symm_image_image]

end Relabelling
end Applications.Matroid
