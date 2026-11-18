import Applications.Matroid.CircuitElimination
import Examples.MatroidPresentations

/-! # Direct circuit-elimination inputs

A single prescribed circuit gives loops, parallel elements and U₂,₃ without
assuming a matroid realization. The empty family gives the free matroid.
-/
set_option autoImplicit false
set_option warningAsError true

open Set Applications.Matroid
namespace Examples.CircuitElimination

/-- A single nonempty circuit inside a finite ground. -/
def singleCircuit {α : Type*} (E C : Set α) (hE : E.Finite)
    (hCE : C ⊆ E) (hC : C.Nonempty) : CircuitEliminationPresentation α where
  ground := E
  finite_ground := hE
  IsCircuit D := D = C
  subset_ground := fun h ↦ h ▸ hCE
  nonempty := fun h ↦ h ▸ hC
  antichain := fun hD hK _ ↦ hD.trans hK.symm
  eliminate := fun hD hK hne _ ↦ False.elim (hne (hD.trans hK.symm))

@[simp] theorem singleCircuit_indep {α : Type*} (E C : Set α) (hE : E.Finite)
    (hCE : C ⊆ E) (hC : C.Nonempty) (I : Set α) :
    (singleCircuit E C hE hCE hC).matroid.Indep I ↔ I ⊆ E ∧ ¬ C ⊆ I := by
  rw [CircuitEliminationPresentation.matroid_indep]
  change (I ⊆ E ∧ ∀ D ⊆ I, D ≠ C) ↔ I ⊆ E ∧ ¬ C ⊆ I
  constructor
  · rintro ⟨hI, h⟩
    exact ⟨hI, fun hc ↦ h C hc rfl⟩
  · rintro ⟨hI, h⟩
    exact ⟨hI, fun D hD heq ↦ h (heq ▸ hD)⟩

def emptyCircuits {α : Type*} (E : Set α) (hE : E.Finite) :
    CircuitEliminationPresentation α where
  ground := E
  finite_ground := hE
  IsCircuit _ := False
  subset_ground := False.elim
  nonempty := False.elim
  antichain := False.elim
  eliminate := False.elim

example {α : Type*} (I : Set α) :
    (emptyCircuits (∅ : Set α) finite_empty).matroid.Indep I ↔ I = ∅ := by
  rw [CircuitEliminationPresentation.matroid_indep]
  simp [CircuitEliminationPresentation.Indep, emptyCircuits]

/-- A singleton circuit is a loop, and an element outside the ground is not independent. -/
example : (singleCircuit ({2, 5} : Set ℕ) {2} (by simp) (by simp) (by simp)).matroid.IsCircuit {2} := by
  rw [CircuitEliminationPresentation.matroid_isCircuit]
  rfl

example : ¬ (singleCircuit ({2, 5} : Set ℕ) {2} (by simp) (by simp) (by simp)).matroid.Indep {9} := by
  rw [singleCircuit_indep]
  norm_num

example : (singleCircuit (univ : Set Bool) univ (toFinite _) Subset.rfl (by simp)).matroid.IsCircuit univ := by
  rw [CircuitEliminationPresentation.matroid_isCircuit]
  rfl

example (b : Bool) : (singleCircuit (univ : Set Bool) univ (toFinite _) Subset.rfl (by simp)).matroid.Indep {b} := by
  rw [singleCircuit_indep]
  refine ⟨subset_univ _, ?_⟩
  intro h
  have hn := h (mem_univ (!b))
  cases b <;> simp_all

/-- A three-element circuit recovers the existing uniform rank-two client. -/
theorem u23_recovered :
    (singleCircuit (univ : Set (Fin 3)) univ (toFinite _) Subset.rfl (by simp)).matroid =
      MatroidPresentations.u23 := by
  apply Matroid.ext_indep (M₁ := (singleCircuit (univ : Set (Fin 3)) univ
    (toFinite _) Subset.rfl (by simp)).matroid) (M₂ := MatroidPresentations.u23) rfl
  intro I _
  rw [singleCircuit_indep, MatroidPresentations.u23, MatroidPresentations.uniform_indep]
  simp only [subset_univ, true_and, univ_subset_iff]
  constructor
  · intro h
    have hn := ncard_lt_card h
    norm_num at hn
    omega
  · intro h heq
    subst I
    norm_num at h

example {α : Type*} (P : CircuitEliminationPresentation α) :
    (FiniteMatroid.closureEquiv.symm.trans FiniteMatroid.rankEquiv)
      ((FiniteMatroid.circuitEliminationEquiv.symm.trans FiniteMatroid.closureEquiv) P) =
    (FiniteMatroid.circuitEliminationEquiv.symm.trans FiniteMatroid.rankEquiv) P :=
  FiniteMatroid.route_agreement _ _ _ P

example {α : Type*} (P : CircuitEliminationPresentation α) :
    (FiniteMatroid.independenceEquiv.symm.trans FiniteMatroid.basisEquiv)
      ((FiniteMatroid.circuitEliminationEquiv.symm.trans FiniteMatroid.independenceEquiv) P) =
    (FiniteMatroid.circuitEliminationEquiv.symm.trans FiniteMatroid.basisEquiv) P :=
  FiniteMatroid.route_agreement _ _ _ P

example : ((singleCircuit ({2, 5} : Set ℕ) {2} (by simp) (by simp) (by simp)).relabel
    (Equiv.swap 2 9)).IsCircuit ((Equiv.swap 2 9) '' {2}) := by
  rw [CircuitEliminationPresentation.relabel_circuit]
  rfl

/-- The family {0,1}, {0,2} is an antichain of nonempty sets but cannot eliminate 0. -/
def badCircuit (C : Set (Fin 3)) : Prop := C = {0, 1} ∨ C = {0, 2}

theorem badCircuit_nonempty {C : Set (Fin 3)} (h : badCircuit C) : C.Nonempty := by
  rcases h with rfl | rfl <;> simp

theorem badCircuit_antichain {C D : Set (Fin 3)} (hC : badCircuit C)
    (hD : badCircuit D) (hsub : C ⊆ D) : C = D := by
  rcases hC with rfl | rfl <;> rcases hD with rfl | rfl
  · rfl
  · have h := hsub (show (1 : Fin 3) ∈ ({0, 1} : Set (Fin 3)) by simp)
    norm_num at h
  · have h := hsub (show (2 : Fin 3) ∈ ({0, 2} : Set (Fin 3)) by simp)
    norm_num at h
  · rfl

theorem badCircuit_not_eliminate :
    ¬ ∀ (C D : Set (Fin 3)) (e : Fin 3), badCircuit C → badCircuit D → C ≠ D →
      e ∈ C ∩ D → ∃ K, badCircuit K ∧ K ⊆ (C ∪ D) \ {e} := by
  intro h
  have hne : ({0, 1} : Set (Fin 3)) ≠ {0, 2} := by
    intro heq
    have := heq ▸ (show (1 : Fin 3) ∈ ({0, 1} : Set (Fin 3)) by simp)
    norm_num at this
  obtain ⟨K, hK, hsub⟩ := h {0, 1} {0, 2} 0 (Or.inl rfl) (Or.inr rfl) hne (by simp)
  have hzero : (0 : Fin 3) ∈ K := by rcases hK with rfl | rfl <;> simp
  simpa using hsub hzero

end Examples.CircuitElimination
