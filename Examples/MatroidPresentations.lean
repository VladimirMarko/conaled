import Applications.Matroid.Flats
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Tactic.NormNum

/-! # Finite matroid presentation examples

Uniform independence, a one-edge graphic matroid, relabelling, and information
loss when the embedding of flats is forgotten.
-/
set_option autoImplicit false
set_option warningAsError true

open Set Applications.Matroid
namespace Examples.MatroidPresentations

/-- The uniform matroid of rank at most `k` on a finite labelled ground. -/
noncomputable def uniform {α : Type*} (E : Set α) (hE : E.Finite) (k : ℕ) : Matroid α :=
  (IndepMatroid.ofFinite hE (fun I ↦ I ⊆ E ∧ I.ncard ≤ k)
    (by simp)
    (fun _ _ h hsub ↦ ⟨hsub.trans h.1, (ncard_le_ncard hsub (hE.subset h.1)).trans h.2⟩)
    (by
      intro I J hI hJ hcard
      obtain ⟨e, heJ, heI⟩ := exists_mem_notMem_of_ncard_lt_ncard hcard (hE.subset hI.1)
      exact ⟨e, heJ, heI, insert_subset (hJ.1 heJ) hI.1,
        (ncard_insert_le e I).trans (by omega)⟩)
    (fun _ h ↦ h.1)).matroid

instance {α : Type*} (E : Set α) (hE : E.Finite) (k : ℕ) : (uniform E hE k).Finite := ⟨hE⟩

theorem uniform_indep {α : Type*} (E : Set α) (hE : E.Finite) (k : ℕ) (I : Set α) :
    (uniform E hE k).Indep I ↔ I ⊆ E ∧ I.ncard ≤ k := Iff.rfl

noncomputable def u23 : Matroid (Fin 3) := uniform univ (toFinite _) 2

example : u23.Indep ({0, 1} : Set (Fin 3)) := by
  rw [u23, uniform_indep]
  norm_num

example : ¬ u23.Indep univ := by
  rw [u23, uniform_indep]
  simp [Set.ncard_univ]

/-- The same native closure-exchange theorem is available through rank and circuits. -/
theorem rank_exchange {α : Type*} (R : RankPresentation α) {X : Set α} {x y : α}
    (h : x ∈ R.cl (insert y X) \ R.cl X) : y ∈ R.cl (insert x X) \ R.cl X := by
  simpa using R.matroid.closure_exchange (by simpa using h)

theorem circuit_exchange {α : Type*} (P : CircuitPresentation α) {X : Set α} {x y : α}
    (h : x ∈ P.matroid.closure (insert y X) \ P.matroid.closure X) :
    y ∈ P.matroid.closure (insert x X) \ P.matroid.closure X := P.matroid.closure_exchange h

example : (RankPresentation.ofMatroid
    (CircuitPresentation.ofMatroid u23).matroid).matroid = u23 := by simp

example (X : Set (Fin 3)) : (u23.mapEquiv (Equiv.swap 0 2)).eRk
    ((Equiv.swap 0 2) '' X) = u23.eRk X := relabel_rank _ _ _

/-- The complete graph on two vertices has one edge and no cycles. -/
def edgeGraph : SimpleGraph Bool := ⊤

noncomputable def edgeMatroid : Matroid (Sym2 Bool) := Matroid.freeOn edgeGraph.edgeSet

/-- Independence agrees with the graphic definition: selected edges form an acyclic graph. -/
theorem edge_graphic (I : Set (Sym2 Bool)) :
    edgeMatroid.Indep I ↔ I ⊆ edgeGraph.edgeSet ∧ (SimpleGraph.fromEdgeSet I).IsAcyclic := by
  have h : (SimpleGraph.fromEdgeSet I).IsAcyclic :=
    SimpleGraph.IsAcyclic.of_card_le_two (by simp)
  simp [edgeMatroid, h]

example : edgeMatroid.Indep {s(false, true)} := by
  rw [edge_graphic]
  exact ⟨by simp [edgeGraph], SimpleGraph.IsAcyclic.of_card_le_two (by simp)⟩

/-- Every all-loop matroid has a one-element abstract flat lattice, regardless of its ground. -/
noncomputable def loopFlatsIso {α β : Type*} (E : Set α) (D : Set β) :
    Flat (Matroid.loopyOn E) ≃o Flat (Matroid.loopyOn D) where
  toFun _ := ⊤
  invFun _ := ⊤
  left_inv F := by
    apply Flat.ext
    simpa using (Flat.carrier_isFlat (Matroid.loopyOn E) F).closure
  right_inv F := by
    apply Flat.ext
    simpa using (Flat.carrier_isFlat (Matroid.loopyOn D) F).closure
  map_rel_iff' := by
    intro F G
    have hF : F = ⊤ := by
      apply Flat.ext
      simpa using (Flat.carrier_isFlat (Matroid.loopyOn E) F).closure.symm
    have hG : G = ⊤ := by
      apply Flat.ext
      simpa using (Flat.carrier_isFlat (Matroid.loopyOn E) G).closure.symm
    simp [hF, hG]

/-- The abstract flat lattice cannot recover even the number of loops. -/
example : Nonempty (Flat (Matroid.loopyOn (univ : Set (Fin 1))) ≃o
    Flat (Matroid.loopyOn (univ : Set (Fin 2)))) := ⟨loopFlatsIso _ _⟩

example : ¬ Nonempty (Fin 1 ≃ Fin 2) := by
  rintro ⟨e⟩
  have h := Fintype.card_congr e
  norm_num at h

/-- All elements are parallel copies of the single free element. -/
noncomputable def parallel {α : Type*} : Matroid α :=
  (Matroid.freeOn (univ : Set Unit)).comap (fun _ : α ↦ ())

@[simp] theorem parallel_ground {α : Type*} : (parallel : Matroid α).E = univ := rfl

theorem parallel_closure {α : Type*} (X : Set α) :
    (parallel : Matroid α).closure X = {_e | X.Nonempty} := by
  classical
  ext e
  simp [parallel, Matroid.comap_closure_eq, Set.Nonempty]

/-- A parallel class has only the empty and whole-ground flats. -/
theorem parallel_flat {α : Type*} (F : Flat (parallel : Matroid α)) :
    Flat.carrier _ F = ∅ ∨ Flat.carrier _ F = univ := by
  have h := (Flat.carrier_isFlat _ F).closure
  rw [parallel_closure] at h
  by_cases hn : (Flat.carrier _ F).Nonempty
  · exact Or.inr (by simpa [hn] using h.symm)
  · exact Or.inl (by simpa [hn] using h.symm)

@[simp] theorem parallel_bot {γ : Type*} : Flat.carrier (parallel : Matroid γ) ⊥ = ∅ := by
  simp [parallel_closure]
@[simp] theorem parallel_top {γ : Type*} : Flat.carrier (parallel : Matroid γ) ⊤ = univ := rfl
theorem parallel_flat_cases {γ : Type*} (F : Flat (parallel : Matroid γ)) : F = ⊥ ∨ F = ⊤ := by
  rcases parallel_flat F with h | h
  · exact Or.inl (Flat.ext _ (by rw [h, parallel_bot]))
  · exact Or.inr (Flat.ext _ (by rw [h, parallel_top]))
theorem parallel_top_ne_bot {γ : Type*} [Nonempty γ] : (⊤ : Flat (parallel : Matroid γ)) ≠ ⊥ := by
  intro h
  have hc := congrArg (Flat.carrier _) h
  rw [parallel_bot, parallel_top] at hc
  exact Set.univ_nonempty.ne_empty hc

/-- Forgetting the embedding also loses parallel-class multiplicity. -/
noncomputable def parallelFlatsIso {α β : Type*} [Nonempty α] [Nonempty β] :
    Flat (parallel : Matroid α) ≃o Flat (parallel : Matroid β) := by
  classical
  let forward (F : Flat (parallel : Matroid α)) : Flat (parallel : Matroid β) :=
    if Flat.carrier _ F = ∅ then ⊥ else ⊤
  let backward (F : Flat (parallel : Matroid β)) : Flat (parallel : Matroid α) :=
    if Flat.carrier _ F = ∅ then ⊥ else ⊤
  exact {
    toFun := forward
    invFun := backward
    left_inv := fun F ↦ by
      rcases parallel_flat_cases F with rfl | rfl <;> simp [forward, backward, parallel_closure]
    right_inv := fun F ↦ by
      rcases parallel_flat_cases F with rfl | rfl <;> simp [forward, backward, parallel_closure]
    map_rel_iff' := by
      intro F G
      rcases parallel_flat_cases F with rfl | rfl <;>
        rcases parallel_flat_cases G with rfl | rfl <;> simp [forward, parallel_closure, parallel_top_ne_bot]
  }

example : (parallel : Matroid (Fin 2)).IsCircuit univ := by
  rw [Matroid.isCircuit_iff_dep_forall_sdiff_singleton_indep]
  simp [parallel, Matroid.dep_iff, Matroid.comap_indep_iff, Set.InjOn]

example : Nonempty (Flat (parallel : Matroid (Fin 1)) ≃o Flat (parallel : Matroid (Fin 2))) :=
  ⟨parallelFlatsIso⟩

/-- A rank presentation supplied directly, rather than read from a matroid. -/
def zeroRank : RankPresentation (Fin 2) where
  ground := univ
  finite_ground := toFinite _
  rank := fun _ ↦ 0
  empty := rfl
  inter_ground := fun _ ↦ rfl
  mono := fun _ _ _ ↦ le_rfl
  insert_le := fun _ _ ↦ by omega
  persist := fun _ _ ↦ rfl

example : zeroRank.matroid = Matroid.loopyOn univ := by
  apply Matroid.ext_closure
  intro X
  rw [zeroRank.matroid_closure, Matroid.loopyOn_closure_eq]
  ext e
  simp [RankPresentation.cl, zeroRank]

example (P : BasisPresentation (Fin 3)) :
    (FiniteMatroid.circuitEquiv.symm.trans FiniteMatroid.rankEquiv)
      ((FiniteMatroid.basisEquiv.symm.trans FiniteMatroid.circuitEquiv) P) =
    (FiniteMatroid.basisEquiv.symm.trans FiniteMatroid.rankEquiv) P :=
  FiniteMatroid.route_agreement _ _ _ P

example : (ClosurePresentation.ofMatroid
    (Matroid.freeOn ({0} : Set (Fin 3)))).cl {2} = {0} ∩ {2} := by
  simp [ClosurePresentation.ofMatroid, Set.inter_comm]

example : ¬ (IndependencePresentation.ofMatroid
    (Matroid.freeOn ({0} : Set (Fin 3)))).Indep {2} := by
  simp [IndependencePresentation.ofMatroid]

end Examples.MatroidPresentations
