import Applications.Matroid.SubmodularRank
import Examples.MatroidPresentations

/-! # Direct submodular-rank inputs and recovery

Truncated cardinality supplies the axioms independently of any matroid. Recovery
then connects these inputs to the existing uniform, loop and presentation APIs.
-/
set_option autoImplicit false
set_option warningAsError true

open Set Applications.Matroid
namespace Examples.SubmodularRank

/-- Direct standard rank data on a finite ground inside an arbitrary ambient type. -/
noncomputable def uniformRank {α : Type*} (E : Set α) (hE : E.Finite) (k : ℕ) :
    SubmodularRankPresentation α where
  ground := E
  finite_ground := hE
  rank X := min k (X ∩ E).ncard
  empty := by simp
  inter_ground := fun X ↦ by simp [inter_assoc]
  mono := by
    intro X Y h
    exact min_le_min_left _ (ncard_le_ncard (inter_subset_inter_left E h)
      (hE.subset inter_subset_right))
  rank_le := fun _ ↦ min_le_right _ _
  submodular := by
    intro X Y
    have hi : (X ∩ E) ∩ (Y ∩ E) = (X ∩ Y) ∩ E := by
      ext a
      simp only [mem_inter_iff]
      tauto
    have hc := ncard_inter_add_ncard_union (X ∩ E) (Y ∩ E)
      (hE.subset inter_subset_right) (hE.subset inter_subset_right)
    have hx := ncard_le_ncard (inter_subset_left : (X ∩ E) ∩ (Y ∩ E) ⊆ X ∩ E)
      (hE.subset inter_subset_right)
    have hy := ncard_le_ncard (inter_subset_right : (X ∩ E) ∩ (Y ∩ E) ⊆ Y ∩ E)
      (hE.subset inter_subset_right)
    rw [hi, ← union_inter_distrib_right] at hc
    rw [hi] at hx hy
    omega

/-- Reconstructing the directly supplied rank agrees with the existing independent-set constructor. -/
theorem uniformRank_matroid {α : Type*} (E : Set α) (hE : E.Finite) (k : ℕ) :
    (uniformRank E hE k).matroid = MatroidPresentations.uniform E hE k := by
  apply Matroid.ext_indep (M₁ := (uniformRank E hE k).matroid)
    (M₂ := MatroidPresentations.uniform E hE k) rfl
  intro I hI
  change I ⊆ E at hI
  have hfin := hE.subset hI
  rw [Matroid.indep_iff_eRk_eq_encard_of_finite hfin,
    SubmodularRankPresentation.matroid_eRk, ← hfin.cast_ncard_eq,
    MatroidPresentations.uniform_indep]
  change (↑(min k (I ∩ E).ncard) : ℕ∞) = ↑I.ncard ↔ _
  rw [inter_eq_self_of_subset_left hI]
  simp [hI]

/-- A nontrivial direct input recovers the retained U₂,₃ client. -/
theorem u23_recovered : (uniformRank (univ : Set (Fin 3)) (toFinite _) 2).matroid =
    MatroidPresentations.u23 := uniformRank_matroid _ _ _

example : (uniformRank (univ : Set (Fin 3)) (toFinite _) 2).matroid.eRk {0, 1} = 2 := by
  rw [SubmodularRankPresentation.matroid_eRk]
  norm_num [uniformRank]

example : ¬ (uniformRank (univ : Set (Fin 3)) (toFinite _) 2).matroid.Indep univ := by
  rw [u23_recovered, MatroidPresentations.u23, MatroidPresentations.uniform_indep]
  simp [Set.ncard_univ]

/-- Empty ground is valid even when the ambient carrier is infinite. -/
example (X : Set ℕ) : (uniformRank ∅ finite_empty 3).matroid.eRk X = 0 := by
  rw [SubmodularRankPresentation.matroid_eRk]
  simp [uniformRank]

/-- Zero rank retains every labelled ground element as a loop. -/
theorem zero_loops {α : Type*} (E : Set α) (hE : E.Finite) :
    (uniformRank E hE 0).matroid = Matroid.loopyOn E := by
  apply Matroid.ext_indep (M₁ := (uniformRank E hE 0).matroid)
    (M₂ := Matroid.loopyOn E) rfl
  intro I hI
  change I ⊆ E at hI
  rw [uniformRank_matroid, MatroidPresentations.uniform_indep]
  simp [hI, ncard_eq_zero (hE.subset hI)]

/-- Two labelled nonloops in rank one form a circuit, retaining parallel multiplicity. -/
example : (uniformRank (univ : Set Bool) (toFinite _) 1).matroid.IsCircuit univ := by
  rw [Matroid.isCircuit_iff_dep_forall_sdiff_singleton_indep,
    Matroid.dep_iff, uniformRank_matroid]
  simp [MatroidPresentations.uniform_indep]
  exact Subset.rfl

/-- Outside-ground elements add no rank, also for an infinite ambient subset. -/
example : (uniformRank ({2, 5} : Set ℕ) (by simp) 2).matroid.eRk univ = 2 := by
  rw [SubmodularRankPresentation.matroid_eRk]
  norm_num [uniformRank]

example : (uniformRank ({2, 5} : Set ℕ) (by simp) 2).matroid.eRk {9} = 0 := by
  rw [SubmodularRankPresentation.matroid_eRk]
  norm_num [uniformRank, Set.ext_iff]

/-- Both presentation records survive a round trip. -/
example {α : Type*} (R : SubmodularRankPresentation α) :
    SubmodularRankPresentation.ofMatroid R.matroid = R := R.matroid_ofMatroid

example {α : Type*} (R : RankPresentation α) :
    (SubmodularRankPresentation.rankEquiv
      (SubmodularRankPresentation.rankEquiv.symm R)) = R :=
  SubmodularRankPresentation.rankEquiv.apply_symm_apply R

/-- The new presentation participates in all existing hub routes. -/
example {α : Type*} (R : SubmodularRankPresentation α) :
    (FiniteMatroid.circuitEquiv.symm.trans FiniteMatroid.closureEquiv)
      ((FiniteMatroid.submodularRankEquiv.symm.trans FiniteMatroid.circuitEquiv) R) =
    (FiniteMatroid.submodularRankEquiv.symm.trans FiniteMatroid.closureEquiv) R :=
  FiniteMatroid.route_agreement _ _ _ R

example {α : Type*} (R : SubmodularRankPresentation α) :
    (FiniteMatroid.independenceEquiv.symm.trans FiniteMatroid.basisEquiv)
      ((FiniteMatroid.submodularRankEquiv.symm.trans FiniteMatroid.independenceEquiv) R) =
    (FiniteMatroid.submodularRankEquiv.symm.trans FiniteMatroid.basisEquiv) R :=
  FiniteMatroid.route_agreement _ _ _ R

/-- Relabelling changes the actual labels while preserving ranks of all corresponding sets. -/
example : ((uniformRank ({2, 5} : Set ℕ) (by simp) 2).relabel (Equiv.swap 2 9)).rank
    ((Equiv.swap 2 9) '' {2}) = 1 := by
  rw [SubmodularRankPresentation.relabel_rank]
  norm_num [uniformRank]

/-- Two nonidentity relabellings preserve the same input rank in composition. -/
example : (((uniformRank ({2, 5} : Set ℕ) (by simp) 2).relabel (Equiv.swap 2 9)).relabel
    (Equiv.swap 9 12)).rank (((Equiv.swap 2 9).trans (Equiv.swap 9 12)) '' {2}) = 1 := by
  rw [SubmodularRankPresentation.relabel_trans, SubmodularRankPresentation.relabel_rank]
  norm_num [uniformRank]

/-- Monotonicity and cardinality bounds alone permit this invalid rank jump. -/
noncomputable def badRank (X : Set Bool) : ℕ := if X = univ then 2 else 0

theorem badRank_mono : Monotone badRank := by
  classical
  intro X Y h
  by_cases hx : X = univ
  · have hy : Y = univ := (subset_univ Y).antisymm (hx ▸ h)
    rw [hx, hy]
  · simp only [badRank, ite_eq_right hx, Nat.zero_le]

theorem badRank_le (X : Set Bool) : badRank X ≤ X.ncard := by
  classical
  dsimp only [badRank]
  split_ifs with hx
  · subst X
    simp
  · exact Nat.zero_le _

theorem badRank_not_submodular :
    ¬ ∀ X Y, badRank (X ∩ Y) + badRank (X ∪ Y) ≤ badRank X + badRank Y := by
  intro h
  have h' := h {false} {true}
  have hu : ({false} ∪ {true} : Set Bool) = univ := by
    ext x
    cases x <;> simp
  have hi : ({false} ∩ {true} : Set Bool) = ∅ := by
    ext x
    cases x <;> simp
  rw [hi, hu] at h'
  norm_num [badRank, Set.ext_iff, Bool.forall_bool] at h'

end Examples.SubmodularRank
