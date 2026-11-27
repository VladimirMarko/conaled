import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Topology.OpenPartialHomeomorph.IsImage

/-! Finite smooth branch diagrams retain actual arrows and both endpoint maps. -/
noncomputable section
open Set TopologicalSpace
open scoped Manifold ContDiff
namespace Orbifolds.LocalBranches

variable {EA EX EY HA HX HY A X Y : Type*}
  [NormedAddCommGroup EA] [NormedSpace ℝ EA]
  [NormedAddCommGroup EX] [NormedSpace ℝ EX]
  [NormedAddCommGroup EY] [NormedSpace ℝ EY]
  [TopologicalSpace HA] [TopologicalSpace HX] [TopologicalSpace HY]
  [TopologicalSpace A] [TopologicalSpace X] [TopologicalSpace Y]
  [ChartedSpace HA A] [ChartedSpace HX X] [ChartedSpace HY Y]
  {IA : ModelWithCorners ℝ EA HA} {IX : ModelWithCorners ℝ EX HX}
  {IY : ModelWithCorners ℝ EY HY}

/-- Restrict a local smooth chart to an open subset of its source. -/
def restrictChart (q : PartialDiffeomorph IA IX A X ∞) (W : Opens A) :
    PartialDiffeomorph IA IX A X ∞ where
  __ := q.toOpenPartialHomeomorph.restrOpen W W.isOpen
  contMDiffOn_toFun := q.contMDiffOn_toFun.mono inter_subset_left
  contMDiffOn_invFun := q.contMDiffOn_invFun.mono inter_subset_left

/-- The actual map and inverse on the open source and target of a partial chart. -/
def chartDiffeomorph (q : PartialDiffeomorph IA IX A X ∞) :
    Diffeomorph IA IX (⟨q.source, q.open_source⟩ : Opens A)
      (⟨q.target, q.open_target⟩ : Opens X) ∞ where
  toFun a := ⟨q a, q.toPartialEquiv.map_source a.property⟩
  invFun x := ⟨q.invFun x, q.toPartialEquiv.map_target x.property⟩
  left_inv a := Subtype.ext (q.toPartialEquiv.left_inv a.property)
  right_inv x := Subtype.ext (q.toPartialEquiv.right_inv x.property)
  contMDiff_toFun := by
    apply (ContMDiff.subtypeVal_comp_iff _ _).mp
    intro a
    apply contMDiffAt_subtype_iff.mpr
    exact (q.contMDiffOn_toFun a a.property).contMDiffAt
      (q.open_source.mem_nhds a.property)
  contMDiff_invFun := by
    apply (ContMDiff.subtypeVal_comp_iff _ _).mp
    intro x
    apply contMDiffAt_subtype_iff.mpr
    exact (q.contMDiffOn_invFun x x.property).contMDiffAt
      (q.open_target.mem_nhds x.property)

/-- A diagram consists of open, disjoint pieces and actual source inverses.
Its construction from properness is supplied separately. -/
structure Diagram (IA : ModelWithCorners ℝ EA HA) (IX : ModelWithCorners ℝ EX HX)
    (s : A → X) (t : A → Y) (U : Opens X) (V : Opens Y) (J : Type*) where
  piece : J → Opens A
  domain : J → Opens X
  sourceEquiv : ∀ i, Diffeomorph IA IX (piece i) (domain i) ∞
  source_eq : ∀ i (a : piece i), (sourceEquiv i a).val = s a.val
  domain_le : ∀ i, domain i ≤ U
  target_mem : ∀ i (a : piece i), t a.val ∈ V
  disjoint : Pairwise (fun i j => Disjoint (piece i) (piece j))
  covers : ∀ a, (s a ∈ U ∧ t a ∈ V) ↔ ∃ i, a ∈ piece i

namespace Diagram
variable {s : A → X} {t : A → Y} {U : Opens X} {V : Opens Y} {J : Type*}
  (D : Diagram IA IX s t U V J)

/-- The whole arrow region, with its inherited open-submanifold structure. -/
def region : Opens A := ⟨{a | s a ∈ U ∧ t a ∈ V}, by
  have h : {a | s a ∈ U ∧ t a ∈ V} = ⋃ i, (D.piece i : Set A) := by
    ext a
    rw [mem_iUnion]
    exact D.covers a
  rw [h]
  exact isOpen_iUnion (fun i => (D.piece i).isOpen)⟩

@[simp] theorem mem_region (a : A) : a ∈ D.region ↔ s a ∈ U ∧ t a ∈ V := Iff.rfl

theorem piece_le_region (i : J) : D.piece i ≤ D.region := by
  intro a ha
  exact (D.covers a).mpr ⟨i, ha⟩

def source (a : D.region) : U := ⟨s a.val, a.property.1⟩
def target (a : D.region) : V := ⟨t a.val, a.property.2⟩
def domainInclusion (i : J) : D.domain i → U := Opens.inclusion (D.domain_le i)

/-- Actual inverse source branch, included into the full arrow region. -/
def assemble (i : J) (x : D.domain i) : D.region :=
  ⟨(D.sourceEquiv i).symm x, D.piece_le_region i ((D.sourceEquiv i).symm x).property⟩

def branch (i : J) (x : D.domain i) : V := D.target (D.assemble i x)

@[simp] theorem source_assemble (i : J) (x : D.domain i) :
    D.source (D.assemble i x) = D.domainInclusion i x := by
  apply Subtype.ext
  exact (D.source_eq i ((D.sourceEquiv i).symm x)).symm.trans
    (congrArg Subtype.val ((D.sourceEquiv i).apply_symm_apply x))

@[simp] theorem target_assemble (i : J) (x : D.domain i) :
    D.target (D.assemble i x) = D.branch i x := rfl

theorem assemble_smooth (i : J) : ContMDiff IX IA ∞ (D.assemble i) :=
  (contMDiff_inclusion (I := IA) (D.piece_le_region i)).comp
    (D.sourceEquiv i).contMDiff_invFun

theorem source_smooth (hs : ContMDiff IA IX ∞ s) : ContMDiff IA IX ∞ D.source := by
  apply (ContMDiff.subtypeVal_comp_iff _ _).mp
  exact hs.comp contMDiff_subtype_val

theorem target_smooth (ht : ContMDiff IA IY ∞ t) : ContMDiff IA IY ∞ D.target := by
  apply (ContMDiff.subtypeVal_comp_iff _ _).mp
  exact ht.comp contMDiff_subtype_val

theorem branch_smooth (ht : ContMDiff IA IY ∞ t) (i : J) :
    ContMDiff IX IY ∞ (D.branch i) :=
  (D.target_smooth ht).comp (D.assemble_smooth i)

theorem unique_piece {a : A} {i j : J} (hi : a ∈ D.piece i) (hj : a ∈ D.piece j) : i = j := by
  by_contra h
  exact Set.disjoint_left.mp (show Disjoint (D.piece i : Set A) (D.piece j : Set A) from
    (Opens.coe_disjoint.mpr (D.disjoint h))) hi hj

def index (a : D.region) : J := Classical.choose ((D.covers a.val).mp a.property)

theorem mem_index (a : D.region) : a.val ∈ D.piece (D.index a) :=
  Classical.choose_spec ((D.covers a.val).mp a.property)

def decompose (a : D.region) : Σ i, D.domain i :=
  ⟨D.index a, D.sourceEquiv (D.index a) ⟨a.val, D.mem_index a⟩⟩

theorem assemble_decompose (a : D.region) :
    D.assemble (D.decompose a).1 (D.decompose a).2 = a := by
  apply Subtype.ext
  change ((D.sourceEquiv (D.index a)).symm
    ((D.sourceEquiv (D.index a)) ⟨a.val, D.mem_index a⟩)).val = a.val
  exact congrArg Subtype.val ((D.sourceEquiv (D.index a)).symm_apply_apply _)

theorem assemble_injective : Function.Injective (fun z : Σ i, D.domain i =>
    D.assemble z.1 z.2) := by
  rintro ⟨i,x⟩ ⟨j,y⟩ h
  have hv := congrArg Subtype.val h
  have hij : i = j := D.unique_piece ((D.sourceEquiv i).symm x).property
    (hv.symm ▸ ((D.sourceEquiv j).symm y).property)
  subst j
  have hxy : x = y := (D.sourceEquiv i).symm.injective (Subtype.ext hv)
  subst y
  rfl

theorem decompose_assemble (i : J) (x : D.domain i) :
    D.decompose (D.assemble i x) = ⟨i,x⟩ :=
  D.assemble_injective (D.assemble_decompose _)

/-- This equivalence retains the branch index and the actual source coordinate. -/
def equiv : D.region ≃ Σ i, D.domain i where
  toFun := D.decompose
  invFun z := D.assemble z.1 z.2
  left_inv := D.assemble_decompose
  right_inv z := D.decompose_assemble z.1 z.2

@[simp] theorem equiv_symm_apply (i : J) (x : D.domain i) :
    D.equiv.symm ⟨i,x⟩ = D.assemble i x := rfl

theorem decompose_source (a : D.region) :
    D.domainInclusion (D.decompose a).1 (D.decompose a).2 = D.source a := by
  rw [← D.source_assemble, D.assemble_decompose]

theorem decompose_target (a : D.region) :
    D.branch (D.decompose a).1 (D.decompose a).2 = D.target a := by
  rw [← D.target_assemble, D.assemble_decompose]

end Diagram
end Orbifolds.LocalBranches
