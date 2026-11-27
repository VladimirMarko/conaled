import Applications.Orbifolds.LocalBranches
import Applications.Orbifolds.FiniteActionPresentation

/-! The branch sum has its inherited discrete-product smooth structure. -/
noncomputable section
open Set TopologicalSpace
open scoped Manifold ContDiff Orbifolds.FiniteActionPresentation
namespace Orbifolds.LocalBranches.Diagram

variable {EA EX EY HA HX HY A X Y : Type*}
  [NormedAddCommGroup EA] [NormedSpace ℝ EA]
  [NormedAddCommGroup EX] [NormedSpace ℝ EX]
  [TopologicalSpace HA] [TopologicalSpace HX]
  [TopologicalSpace A] [TopologicalSpace X] [TopologicalSpace Y]
  [ChartedSpace HA A] [ChartedSpace HX X]
  {IA : ModelWithCorners ℝ EA HA} {IX : ModelWithCorners ℝ EX HX}
  {s : A → X} {t : A → Y} {U : Opens X} {V : Opens Y} {J : Type*}
  (D : Diagram IA IX s t U V J)

/-- Relabel pieces without changing their source inverses or endpoint maps. -/
def reindex {K : Type*} (e : K ≃ J) : Diagram IA IX s t U V K where
  piece k := D.piece (e k)
  domain k := D.domain (e k)
  sourceEquiv k := D.sourceEquiv (e k)
  source_eq k := D.source_eq (e k)
  domain_le k := D.domain_le (e k)
  target_mem k := D.target_mem (e k)
  disjoint := fun _ _ h => D.disjoint (fun he => h (e.injective he))
  covers a := by
    rw [D.covers a]
    constructor
    · rintro ⟨j, hj⟩
      exact ⟨e.symm j, by simpa using hj⟩
    · rintro ⟨k, hk⟩
      exact ⟨e k, hk⟩

@[simp] theorem reindex_region {K : Type*} (e : K ≃ J) : (D.reindex e).region = D.region := rfl

@[simp] theorem reindex_assemble {K : Type*} (e : K ≃ J) (k : K)
    (x : D.domain (e k)) : (D.reindex e).assemble k x = D.assemble (e k) x := rfl

@[simp] theorem reindex_branch {K : Type*} (e : K ≃ J) (k : K)
    (x : D.domain (e k)) : (D.reindex e).branch k x = D.branch (e k) x := rfl

/-- The finite spelling is obtained by relabelling the derived index type. -/
def finDiagram [Fintype J] : Diagram IA IX s t U V (Fin (Fintype.card J)) :=
  D.reindex (Fintype.equivFin J).symm

section Sum
variable [TopologicalSpace J] [DiscreteTopology J]

/-- The actual open subset of the discrete product containing the branch domains. -/
def sumDomain : Opens (J × X) := ⟨{z | z.2 ∈ D.domain z.1}, by
  have he : {z : J × X | z.2 ∈ D.domain z.1} =
      ⋃ i, ({i} : Set J) ×ˢ (D.domain i : Set X) := by
    ext ⟨i,x⟩
    simp
  rw [he]
  exact isOpen_iUnion (fun i => (isOpen_discrete {i}).prod (D.domain i).isOpen)⟩

/-- The ordinary dependent sum and its discrete-product realization retain both coordinates. -/
def sumCoordinates : (Σ i, D.domain i) ≃ D.sumDomain where
  toFun z := ⟨(z.1, z.2.val), z.2.property⟩
  invFun z := ⟨z.val.1, ⟨z.val.2,z.property⟩⟩
  left_inv z := by cases z; rfl
  right_inv z := rfl

/-- The discrete-product topology is exactly the coproduct topology of the domains. -/
def sumHomeomorph : (Σ i, D.domain i) ≃ₜ D.sumDomain :=
  D.sumCoordinates.toHomeomorphOfContinuousOpen
    (continuous_sigma (fun i =>
      (continuous_const.prodMk continuous_subtype_val).subtype_mk _))
    (isOpenMap_sigma.mpr (fun i => by
      have h : IsOpenMap (fun x : D.domain i => (i,x.val)) := by
        intro W hW
        have he : (fun x : D.domain i => (i,x.val)) '' W =
            ({i} : Set J) ×ˢ (Subtype.val '' W) := by
          ext ⟨j,x⟩
          constructor
          · rintro ⟨a,ha,he⟩
            exact ⟨(congrArg Prod.fst he).symm,⟨a,ha,congrArg Prod.snd he⟩⟩
          · rintro ⟨hj,a,ha,hx⟩
            exact ⟨a,ha,Prod.ext hj.symm hx⟩
        rw [he]
        exact (isOpen_discrete {i}).prod ((D.domain i).isOpen.isOpenMap_subtype_val W hW)
      exact h.subtype_mk _))

/-- Each summand is included by its actual index and source coordinate. -/
def sumInclusion (i : J) (x : D.domain i) : D.sumDomain := ⟨(i,x.val),x.property⟩

theorem sumInclusion_smooth (i : J) :
    ContMDiff IX (FiniteActionPresentation.arrowModel IX) ∞ (D.sumInclusion i) := by
  apply (ContMDiff.subtypeVal_comp_iff D.sumDomain (D.sumInclusion i)).mp
  exact contMDiff_const.prodMk contMDiff_subtype_val

/-- The branch decomposition in the actual open discrete product. -/
def sumEquiv : D.region ≃ D.sumDomain := D.equiv.trans D.sumCoordinates

@[simp] theorem sumEquiv_index (a : D.region) : (D.sumEquiv a).val.1 = D.index a := rfl

@[simp] theorem sumEquiv_source (a : D.region) : (D.sumEquiv a).val.2 = s a.val :=
  D.source_eq _ _

@[simp] theorem sumEquiv_symm (z : D.sumDomain) :
    D.sumEquiv.symm z = D.assemble z.val.1 ⟨z.val.2,z.property⟩ := rfl

omit [TopologicalSpace J] [DiscreteTopology J] in
/-- The piece index is locally constant on the arrow region. -/
theorem index_eventually (a : D.region) :
    ∀ᶠ b in nhds a, D.index b = D.index a := by
  have h := ((D.piece (D.index a)).isOpen.preimage continuous_subtype_val).mem_nhds
    (D.mem_index a)
  filter_upwards [h] with b hb
  exact D.unique_piece (D.mem_index b) hb

omit [TopologicalSpace J] [DiscreteTopology J] in
/-- Smoothness of the actual source on its covered region follows from the branch charts. -/
theorem source_on_region_smooth : ContMDiff IA IX ∞ (fun a : D.region => s a.val) := by
  intro a
  apply contMDiffAt_subtype_iff.mpr
  apply (contMDiffAt_subtype_iff (U := D.piece (D.index a))
    (x := ⟨a.val,D.mem_index a⟩)).mp
  have he : (fun b : D.piece (D.index a) => s b.val) =
      fun b => (D.sourceEquiv (D.index a) b).val := by
    funext b
    exact (D.source_eq _ b).symm
  rw [he]
  exact (contMDiff_subtype_val.comp (D.sourceEquiv (D.index a)).contMDiff_toFun).contMDiffAt

theorem sumEquiv_smooth : ContMDiff IA (FiniteActionPresentation.arrowModel IX) ∞ D.sumEquiv := by
  apply (ContMDiff.subtypeVal_comp_iff D.sumDomain D.sumEquiv).mp
  intro a
  have hi : ContMDiffAt IA 𝓘(ℝ, Fin 0 → ℝ) ∞ D.index a :=
    contMDiffAt_const.congr_of_eventuallyEq (D.index_eventually a)
  have hs := hi.prodMk (D.source_on_region_smooth a)
  apply hs.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun b => Prod.ext rfl (D.sumEquiv_source b))

theorem sumEquiv_symm_smooth :
    ContMDiff (FiniteActionPresentation.arrowModel IX) IA ∞ D.sumEquiv.symm := by
  classical
  apply (ContMDiff.subtypeVal_comp_iff D.region D.sumEquiv.symm).mp
  intro z
  let i := z.val.1
  let g : X → A := fun x => if hx : x ∈ D.domain i then
    ((D.sourceEquiv i).symm ⟨x,hx⟩).val else (D.sumEquiv.symm z).val
  have hg : ContMDiffAt IX IA ∞ g z.val.2 := by
    apply (contMDiffAt_subtype_iff (U := D.domain i)
      (x := ⟨z.val.2,z.property⟩)).mp
    have he : (fun x : D.domain i => g x.val) =
        fun x => ((D.sourceEquiv i).symm x).val := by
      funext x
      simp [g, x.property]
    rw [he]
    exact (contMDiff_subtype_val.comp (D.sourceEquiv i).contMDiff_invFun).contMDiffAt
  have hs : ContMDiffAt (FiniteActionPresentation.arrowModel IX) IA ∞
      (fun w : D.sumDomain => g w.val.2) z :=
    hg.comp z (contMDiff_snd.comp contMDiff_subtype_val).contMDiffAt
  apply hs.congr_of_eventuallyEq
  have hi : ∀ᶠ w : D.sumDomain in nhds z, w.val.1 = i :=
    ((isOpen_discrete {i}).preimage (continuous_fst.comp continuous_subtype_val)).mem_nhds rfl
  filter_upwards [hi] with w hw
  change (D.assemble w.val.1 ⟨w.val.2,w.property⟩).val = g w.val.2
  have hx : w.val.2 ∈ D.domain i := hw ▸ w.property
  simp only [g, dite_eq_left hx, assemble]
  have transport (j k : J) (h : j = k) (x : X)
      (hj : x ∈ D.domain j) (hk : x ∈ D.domain k) :
      ((D.sourceEquiv j).symm ⟨x,hj⟩).val =
        ((D.sourceEquiv k).symm ⟨x,hk⟩).val := by
    subst k
    rfl
  exact transport _ _ hw _ _ _

/-- Smooth branch coordinates use the inherited product model, with both inverse laws. -/
def sumDiffeomorph : Diffeomorph IA (FiniteActionPresentation.arrowModel IX)
    D.region D.sumDomain ∞ where
  toEquiv := D.sumEquiv
  contMDiff_toFun := D.sumEquiv_smooth
  contMDiff_invFun := D.sumEquiv_symm_smooth

@[simp] theorem sumDiffeomorph_assemble (i : J) (x : D.domain i) :
    D.sumDiffeomorph (D.assemble i x) = D.sumInclusion i x := by
  change D.sumCoordinates (D.decompose (D.assemble i x)) = _
  rw [D.decompose_assemble]
  rfl

@[simp] theorem sumDiffeomorph_source (a : D.region) :
    (D.sumDiffeomorph a).val.2 = (D.source a).val := D.sumEquiv_source a

@[simp] theorem sumDiffeomorph_target (a : D.region) :
    D.branch (D.sumDiffeomorph a).val.1
      ⟨(D.sumDiffeomorph a).val.2,(D.sumDiffeomorph a).property⟩ = D.target a :=
  D.decompose_target a

@[simp] theorem sumDiffeomorph_symm_source (z : D.sumDomain) :
    D.source (D.sumDiffeomorph.symm z) = D.domainInclusion z.val.1 ⟨z.val.2,z.property⟩ :=
  D.source_assemble _ _

@[simp] theorem sumDiffeomorph_symm_target (z : D.sumDomain) :
    D.target (D.sumDiffeomorph.symm z) = D.branch z.val.1 ⟨z.val.2,z.property⟩ := rfl

end Sum
end Orbifolds.LocalBranches.Diagram
