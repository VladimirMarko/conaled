import Applications.Matroid.Presentations

/-! # Finite matroids from circuit elimination

Circuit elimination derives exchange of maximal circuit-free sets and hence
augmentation. Reconstruction and all presentation routes use the existing hub.
-/
set_option autoImplicit false
set_option warningAsError true

open Set
namespace Applications.Matroid

/-- The usual circuit axioms on a finite labelled ground set. -/
structure CircuitEliminationPresentation (α : Type*) where
  ground : Set α
  finite_ground : ground.Finite
  IsCircuit : Set α → Prop
  subset_ground : ∀ {C}, IsCircuit C → C ⊆ ground
  nonempty : ∀ {C}, IsCircuit C → C.Nonempty
  antichain : ∀ {C D}, IsCircuit C → IsCircuit D → C ⊆ D → C = D
  eliminate : ∀ {C D e}, IsCircuit C → IsCircuit D → C ≠ D → e ∈ C ∩ D →
    ∃ K, IsCircuit K ∧ K ⊆ (C ∪ D) \ {e}

namespace CircuitEliminationPresentation
variable {α : Type*} (P : CircuitEliminationPresentation α)

/-- Independence retains the ground and excludes every supplied circuit. -/
def Indep (I : Set α) : Prop := I ⊆ P.ground ∧ ∀ C ⊆ I, ¬ P.IsCircuit C

theorem indep_subset {I J : Set α} (hJ : P.Indep J) (hIJ : I ⊆ J) : P.Indep I :=
  ⟨hIJ.trans hJ.1, fun C hC ↦ hJ.2 C (hC.trans hIJ)⟩

theorem circuit_mem_insert {I C : Set α} {e : α} (hI : P.Indep I)
    (hC : P.IsCircuit C) (hsub : C ⊆ insert e I) : e ∈ C := by
  by_contra he
  exact hI.2 C (fun x hx ↦ (hsub hx).resolve_left (fun h ↦ he (h ▸ hx))) hC

/-- An independent set plus one element contains at most one circuit. -/
theorem circuit_unique {I C D : Set α} {e : α} (hI : P.Indep I)
    (hC : P.IsCircuit C) (hD : P.IsCircuit D)
    (hCsub : C ⊆ insert e I) (hDsub : D ⊆ insert e I) : C = D := by
  by_contra hne
  obtain ⟨K, hK, hsub⟩ := P.eliminate hC hD hne
    ⟨P.circuit_mem_insert hI hC hCsub, P.circuit_mem_insert hI hD hDsub⟩
  apply hI.2 K _ hK
  intro x hx
  have h := hsub hx
  have hi : x ∈ insert e I := h.1.elim (fun hx ↦ hCsub hx) (fun hx ↦ hDsub hx)
  exact hi.resolve_left h.2

/-- Maximality supplies the unique circuit created by an outside element. -/
theorem exists_circuit_insert {B : Set α} (hB : Maximal P.Indep B)
    {e : α} (he : e ∈ P.ground) (hne : e ∉ B) :
    ∃ C, P.IsCircuit C ∧ C ⊆ insert e B := by
  classical
  by_contra h
  push Not at h
  apply hne
  exact hB.2 ⟨insert_subset he hB.1.1, fun C hc hC ↦ h C hC hc⟩ (subset_insert _ _) (mem_insert _ _)

/-- Removing an element of that circuit restores independence. -/
theorem exchange_indep {B C : Set α} {e x : α} (hB : P.Indep B)
    (he : e ∈ P.ground) (_hne : e ∉ B) (hC : P.IsCircuit C)
    (hCsub : C ⊆ insert e B) (hx : x ∈ C) (hxe : x ≠ e) :
    P.Indep (insert e (B \ {x})) := by
  refine ⟨insert_subset he (sdiff_subset.trans hB.1), ?_⟩
  intro D hDsub hD
  have hDe : D ⊆ insert e B := hDsub.trans (insert_subset_insert sdiff_subset)
  have hCD := P.circuit_unique hB hC hD hCsub hDe
  have hxD : x ∈ D := hCD ▸ hx
  rcases hDsub hxD with h | h
  · exact hxe h
  · exact h.2 rfl

/-- The exchange preserves maximality, not merely independence. -/
theorem exchange_maximal {B C : Set α} {e x : α} (hB : Maximal P.Indep B)
    (he : e ∈ P.ground) (hne : e ∉ B) (hC : P.IsCircuit C)
    (hCsub : C ⊆ insert e B) (hx : x ∈ C) (hxe : x ≠ e) :
    Maximal P.Indep (insert e (B \ {x})) := by
  classical
  refine ⟨P.exchange_indep hB.1 he hne hC hCsub hx hxe, ?_⟩
  intro J hJ hsub y hy
  by_contra hy'
  have hey : e ≠ y := fun h ↦ hy' (h ▸ mem_insert e (B \ {x}))
  have hCx : C \ {x} ⊆ J := by
    intro z hz
    exact hsub ((hCsub hz.1).elim (fun h ↦ Or.inl h) (fun h ↦ Or.inr ⟨h, hz.2⟩))
  by_cases hyB : y ∈ B
  · have hyx : y = x := by
      by_contra h
      exact hy' (mem_insert_of_mem _ ⟨hyB, h⟩)
    apply hJ.2 C _ hC
    intro z hz
    by_cases hzx : z = x
    · exact hzx ▸ hyx ▸ hy
    · exact hCx ⟨hz, hzx⟩
  obtain ⟨D, hD, hDsub⟩ := P.exists_circuit_insert hB (hJ.1 hy) hyB
  have heD : e ∉ D := by
    intro h
    exact (hDsub h).elim hey hne
  by_cases hxD : x ∈ D
  · have hCD : C ≠ D := fun h ↦ heD (h ▸ P.circuit_mem_insert hB.1 hC hCsub)
    obtain ⟨K, hK, hKsub⟩ := P.eliminate hC hD hCD ⟨hx, hxD⟩
    apply hJ.2 K _ hK
    intro z hz
    have h := hKsub hz
    rcases h.1 with hzC | hzD
    · exact hCx ⟨hzC, h.2⟩
    · rcases hDsub hzD with hzy | hzB
      · exact hzy ▸ hy
      · exact hsub (mem_insert_of_mem _ ⟨hzB, h.2⟩)
  · apply hJ.2 D _ hD
    intro z hz
    rcases hDsub hz with hzy | hzB
    · exact hzy ▸ hy
    · exact hsub (mem_insert_of_mem _ ⟨hzB, fun h ↦ hxD (h ▸ hz)⟩)

/-- Extend an independent set using only it and a chosen maximal independent set.
The finite induction exchanges elements while preserving the previously included set. -/
theorem exists_maximal_extension {I B : Set α} (hI : P.Indep I)
    (hB : Maximal P.Indep B) :
    ∃ J, Maximal P.Indep J ∧ I ⊆ J ∧ J ⊆ I ∪ B := by
  classical
  have hf := P.finite_ground.subset hI.1
  induction I, hf using Set.Finite.induction_on with
  | empty => exact ⟨B, hB, empty_subset _, by simp⟩
  | @insert e I heI hfin ih =>
    obtain ⟨J, hJ, hIJ, hJsub⟩ := ih (P.indep_subset hI (subset_insert _ _))
    by_cases heJ : e ∈ J
    · exact ⟨J, hJ, insert_subset heJ hIJ, hJsub.trans (union_subset_union_left _ (subset_insert _ _))⟩
    obtain ⟨C, hC, hCsub⟩ := P.exists_circuit_insert hJ (hI.1 (mem_insert _ _)) heJ
    have hn : ¬ C ⊆ insert e I := fun h ↦ hI.2 C h hC
    obtain ⟨x, hxC, hxI⟩ := not_subset.mp hn
    have hxe : x ≠ e := fun h ↦ hxI (h ▸ mem_insert _ _)
    refine ⟨insert e (J \ {x}),
      P.exchange_maximal hJ (hI.1 (mem_insert _ _)) heJ hC hCsub hxC hxe, ?_, ?_⟩
    · apply insert_subset_insert
      intro z hz
      exact ⟨hIJ hz, fun h ↦ hxI (mem_insert_of_mem _ (h ▸ hz))⟩
    · intro z hz
      rcases hz with h | hz
      · exact Or.inl (Or.inl h)
      · exact (hJsub hz.1).elim (fun h ↦ Or.inl (Or.inr h)) Or.inr

/-- Circuit elimination implies the existing circuit-free augmentation law. -/
theorem augment {I B : Set α} (hI : P.Indep I) (hn : ¬ Maximal P.Indep I)
    (hB : Maximal P.Indep B) : ∃ e ∈ B \ I, P.Indep (insert e I) := by
  classical
  obtain ⟨J, hJ, hIJ, hJsub⟩ := P.exists_maximal_extension hI hB
  have hnJI : ¬ J ⊆ I := fun h ↦ hn ((hIJ.antisymm h) ▸ hJ)
  obtain ⟨e, heJ, heI⟩ := not_subset.mp hnJI
  refine ⟨e, ⟨(hJsub heJ).resolve_left heI, heI⟩, ?_⟩
  exact P.indep_subset hJ.1 (insert_subset heJ hIJ)

/-- The reconstruction input is derived from the standard circuit axioms. -/
def toCircuit : CircuitPresentation α where
  ground := P.ground
  finite_ground := P.finite_ground
  IsCircuit := P.IsCircuit
  subset_ground := P.subset_ground
  nonempty := P.nonempty
  antichain := P.antichain
  augment := P.augment

noncomputable def matroid : _root_.Matroid α := P.toCircuit.matroid
instance : P.matroid.Finite := P.toCircuit.instFiniteMatroid
@[simp] theorem matroid_ground : P.matroid.E = P.ground := rfl
@[simp] theorem matroid_isCircuit (C : Set α) : P.matroid.IsCircuit C ↔ P.IsCircuit C :=
  P.toCircuit.matroid_isCircuit
@[simp] theorem matroid_indep (I : Set α) : P.matroid.Indep I ↔ P.Indep I := Iff.rfl

@[ext] theorem ext {Q : CircuitEliminationPresentation α}
    (hground : P.ground = Q.ground) (hcircuits : P.IsCircuit = Q.IsCircuit) : P = Q := by
  cases P
  cases Q
  cases hground
  cases hcircuits
  rfl

/-- Native finite matroids supply the standard circuit axioms. -/
def ofMatroid (M : _root_.Matroid α) [M.Finite] : CircuitEliminationPresentation α where
  ground := M.E
  finite_ground := M.ground_finite
  IsCircuit := M.IsCircuit
  subset_ground := fun h ↦ h.subset_ground
  nonempty := fun h ↦ h.nonempty
  antichain := fun hC hD h ↦ hC.eq_of_subset_isCircuit hD h
  eliminate := by
    intro C D e hC hD hne _
    obtain ⟨K, hsub, hK⟩ := hC.elimination hD hne e
    exact ⟨K, hK, hsub⟩

@[simp] theorem ofMatroid_toCircuit (M : _root_.Matroid α) [M.Finite] :
    (ofMatroid M).toCircuit = CircuitPresentation.ofMatroid M := rfl

@[simp] theorem ofMatroid_matroid (M : _root_.Matroid α) [M.Finite] :
    (ofMatroid M).matroid = M := CircuitPresentation.ofMatroid_matroid M

@[simp] theorem matroid_ofMatroid : ofMatroid P.matroid = P := by
  apply ext (ofMatroid P.matroid) (Q := P) rfl
  exact funext fun C ↦ propext (P.matroid_isCircuit C)

/-- Standard elimination and circuit-free augmentation give equivalent presentations. -/
noncomputable def circuitEquiv : CircuitEliminationPresentation α ≃ CircuitPresentation α where
  toFun := toCircuit
  invFun Q := ofMatroid Q.matroid
  left_inv := matroid_ofMatroid
  right_inv Q := by rw [ofMatroid_toCircuit, Q.matroid_ofMatroid]

noncomputable def relabel {β : Type*} (f : α ≃ β) : CircuitEliminationPresentation β :=
  ofMatroid (P.matroid.mapEquiv f)

@[simp] theorem relabel_matroid {β : Type*} (f : α ≃ β) :
    (P.relabel f).matroid = P.matroid.mapEquiv f := ofMatroid_matroid _

@[simp] theorem relabel_ground {β : Type*} (f : α ≃ β) :
    (P.relabel f).ground = f '' P.ground := rfl

@[simp] theorem relabel_circuit {β : Type*} (f : α ≃ β) (C : Set α) :
    (P.relabel f).IsCircuit (f '' C) ↔ P.IsCircuit C := by
  change (P.matroid.mapEquiv f).IsCircuit (f '' C) ↔ _
  rw [Applications.Matroid.relabel_circuit, P.matroid_isCircuit]

theorem circuit_relabel {β : Type*} (f : α ≃ β) (D : Set β) :
    (P.relabel f).IsCircuit D ↔ P.IsCircuit (f.symm '' D) := by
  simpa only [Equiv.image_symm_image] using P.relabel_circuit f (f.symm '' D)

@[simp] theorem relabel_refl : P.relabel (Equiv.refl α) = P := by
  apply ext (P.relabel (Equiv.refl α)) (Q := P)
  · simp
  · funext C
    apply propext
    simp [circuit_relabel]

theorem relabel_trans {β γ : Type*} (f : α ≃ β) (g : β ≃ γ) :
    (P.relabel f).relabel g = P.relabel (f.trans g) := by
  apply ext ((P.relabel f).relabel g) (Q := P.relabel (f.trans g))
  · simp [image_image]
  · funext C
    apply propext
    simp [circuit_relabel, image_image]

end CircuitEliminationPresentation

namespace FiniteMatroid
variable {α : Type*}

/-- Standard circuit axioms join all existing presentation routes. -/
noncomputable def circuitEliminationEquiv : FiniteMatroid α ≃ CircuitEliminationPresentation α :=
  circuitEquiv.trans CircuitEliminationPresentation.circuitEquiv.symm

end FiniteMatroid
end Applications.Matroid
