import Applications.Matroid.Geometric
import Examples.MatroidPresentations
import Mathlib.Tactic.FinCases

/-! Boolean and non-distributive geometric lattices, reconstruction of U₂,₃,
and preservation of ground membership in an ambient type. -/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.GeometricMatroids
open Set Applications.Matroid Examples.MatroidPresentations

/-- The Boolean lattice supplies the geometric axioms directly. -/
noncomputable def booleanFlats : Set (Fin 2) ≃o Flat (Geometric.matroid (Set (Fin 2))) :=
  Geometric.flatsIso _

example : IsSimple (Geometric.matroid (Set (Fin 2))) := inferInstance

example (X : Set (Geometric.Atom (Set (Fin 2)))) :
    (Geometric.matroid (Set (Fin 2))).closure X =
      Geometric.below _ (Geometric.joinAtoms _ X) := Geometric.closure_eq _ X

def booleanAtom (i : Fin 2) : Geometric.Atom (Set (Fin 2)) :=
  ⟨{i}, Set.isAtom_singleton i⟩

example : booleanAtom 1 ∉ (Geometric.matroid (Set (Fin 2))).closure {booleanAtom 0} := by
  rw [Geometric.closure_eq, Geometric.join_singleton]
  change ¬ ({1} : Set (Fin 2)) ⊆ {0}
  simp

example : (Geometric.matroid (Set (Fin 0))).E = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro p _
  have h : p.val = ⊥ := Subsingleton.elim _ _
  exact p.property.ne_bot h

private theorem pair_indep (i j : Fin 3) : u23.Indep {i, j} := by
  rw [u23, uniform_indep]
  refine ⟨subset_univ _, ?_⟩
  exact (ncard_insert_le i {j}).trans (by simp)

instance : IsSimple u23 where
  closure_empty := by
    ext x
    rw [u23.empty_indep.mem_closure_iff']
    simp only [mem_empty_iff_false, iff_false, not_and, not_forall, not_false_eq_true,
      insert_empty_eq]
    intro _
    simpa using pair_indep x x
  closure_singleton := by
    intro e _
    have he : u23.Indep {e} := by simpa using pair_indep e e
    ext x
    rw [he.mem_closure_iff']
    constructor
    · intro h; exact h.2 (pair_indep x e)
    · intro h; exact ⟨by trivial, fun _ ↦ h⟩

noncomputable def u23Flats : Flat u23 ≃o Flat (Geometric.matroid (Flat u23)) :=
  Geometric.flatsIso _

example : Flat.restore u23 = u23 := Flat.restore_eq _

/-- Reconstruction agrees with the existing rank-to-matroid route. -/
example : (RankPresentation.ofMatroid (Flat.restore u23)).matroid = u23 := by simp

/-- The flat consisting of one labelled element of U₂,₃. -/
noncomputable def u23Point (i : Fin 3) : Flat u23 := Flat.point _ ⟨i, by trivial⟩

private theorem pair_closure : u23.closure {1, 2} = univ := by
  ext x
  rw [(pair_indep 1 2).mem_closure_iff']
  change (x ∈ (univ : Set (Fin 3)) ∧
    (u23.Indep (insert x {1, 2}) → x ∈ ({1, 2} : Set (Fin 3)))) ↔ x ∈ univ
  fin_cases x <;> norm_num [u23, uniform_indep, Set.ncard_insert_of_notMem]

private theorem sup_points : u23Point 1 ⊔ u23Point 2 = ⊤ := by
  apply Flat.ext
  rw [Flat.sup_eq_span, Flat.carrier_span]
  change u23.closure ({1} ∪ {2}) = univ
  simpa only [singleton_union] using pair_closure

private theorem inf_points {i j : Fin 3} (h : i ≠ j) : u23Point i ⊓ u23Point j = ⊥ := by
  apply Flat.ext
  rw [Flat.carrier_inf, Flat.simple_carrier_bot]
  change ({i} : Set (Fin 3)) ∩ {j} = ∅
  simp [h]

/-- The flat lattice of U₂,₃ is geometric and fails distributivity. -/
theorem u23_nondistributive :
    u23Point 0 ⊓ (u23Point 1 ⊔ u23Point 2) ≠
      (u23Point 0 ⊓ u23Point 1) ⊔ (u23Point 0 ⊓ u23Point 2) := by
  rw [sup_points, inf_top_eq, inf_points (by decide : (0 : Fin 3) ≠ 1),
    inf_points (by decide : (0 : Fin 3) ≠ 2), bot_sup_eq]
  exact Flat.point_ne_bot _ _

example : IsAtomistic (Flat u23) := inferInstance
example : IsUpperModularLattice (Flat u23) := inferInstance
example : Finite (Flat u23) := inferInstance

/-- The reconstruction keeps the outside ambient elements outside the ground. -/
instance : IsSimple (Matroid.freeOn ({0} : Set (Fin 3))) where
  closure_empty := by simp
  closure_singleton := by
    intro e he
    simpa using inter_eq_self_of_subset_left (singleton_subset_iff.mpr he)

example : (Flat.restore (Matroid.freeOn ({0} : Set (Fin 3)))).E = {0} := by simp
example : ¬ (Flat.restore (Matroid.freeOn ({0} : Set (Fin 3)))).Indep {2} := by simp

/-- Non-simple controls from the presentation task remain available. -/
example : Nonempty (Flat (parallel : Matroid (Fin 1)) ≃o Flat (parallel : Matroid (Fin 2))) :=
  ⟨parallelFlatsIso⟩

example : Nonempty (Flat (Matroid.loopyOn (univ : Set (Fin 1))) ≃o
    Flat (Matroid.loopyOn (univ : Set (Fin 2)))) := ⟨loopFlatsIso _ _⟩

end Examples.GeometricMatroids
