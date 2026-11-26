import SquareKit.SmoothTorsorPoints
import SquareKit.SheafTorsorLabels
import SquareKit.SmoothOrdinaryQuotient
import Mathlib.Topology.FiberBundle.Basic

/-! Local sections of a smooth sheaf torsor as point-fiber pretrivializations. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SquareKit.SmoothTorsorReconstruction
open Topology CategoryTheory Opposite ManifoldRealization SmoothManifoldAction SmoothOpenSite EuclideanOpen
open scoped Manifold ContDiff
variable {n : ℕ} {G B : Type} [Group G] [TopologicalSpace B]
  [ChartedSpace (Space n) B] [IsManifold (modelWithCorners n) ∞ B]
variable (P : SheafTorsor.Torsor (locallyConstantGroup G) (object n B))
attribute [local instance] Classical.propDecidable

/-- A point in the source of a derived base chart has its actual chart coordinate. -/
def sectionInput (i : (sectionCharts P).Index) (b : B)
    (hb : b ∈ ((sectionCharts P).chart i).source) : Points ((sectionCharts P).charts.domain i) :=
  ⟨(sectionCharts P).chart i b, (chartDomain_locus ((sectionCharts P).chart i)).symm ▸
    ((sectionCharts P).chart i).map_source hb⟩

theorem sectionInput_projection (i : (sectionCharts P).Index) (b : B)
    (hb : b ∈ ((sectionCharts P).chart i).source) :
    (sectionPoint P i (sectionInput P i b hb)).proj = b := by
  rw [sectionPoint_projection]
  exact ((sectionCharts P).chart i).left_inv hb

/-- Extend a derived local section only as a set function outside its open domain.
No continuity or sheaf-section claim is made for those unused outside values. -/
def sectionValue (i : (sectionCharts P).Index) (b : B) : Fiber P b :=
  if hb : b ∈ ((sectionCharts P).chart i).source then
    cast (congrArg (Fiber P) (sectionInput_projection P i b hb))
      (sectionPoint P i (sectionInput P i b hb)).snd
  else Classical.choice (fiber_nonempty P b)

theorem sectionValue_spec (i : (sectionCharts P).Index) (b : B)
    (hb : b ∈ ((sectionCharts P).chart i).source) :
    (⟨b,sectionValue P i b⟩ : Total P) = sectionPoint P i (sectionInput P i b hb) := by
  rw [sectionValue, dite_eq_left hb]
  exact Bundle.TotalSpace.mk_cast (sectionInput_projection P i b hb) _

/-- The two set-theoretic inverse laws hold on every fiber; topology is derived later. -/
def productEquiv (s : ∀ b, Fiber P b) : Total P ≃ B × G where
  toFun z := (z.proj, (fiberEquiv P z.proj (s z.proj)).symm z.snd)
  invFun bg := ⟨bg.1, fiberEquiv P bg.1 (s bg.1) bg.2⟩
  left_inv z := by
    change (⟨z.proj, (fiberEquiv P z.proj (s z.proj))
      ((fiberEquiv P z.proj (s z.proj)).symm z.snd)⟩ : Total P) = z
    rw [Equiv.apply_symm_apply]
  right_inv bg := by
    change (bg.1, (fiberEquiv P bg.1 (s bg.1)).symm
      (fiberEquiv P bg.1 (s bg.1) bg.2)) = bg
    rw [Equiv.symm_apply_apply]

theorem fiberEquiv_apply (b : B) (p : Fiber P b) (g : G) : fiberEquiv P b p g = g • p := rfl
theorem productEquiv_change (s t : ∀ b, Fiber P b) (b : B) (g c : G)
    (h : c • s b = t b) :
    productEquiv P s ((productEquiv P t).symm (b,g)) = (b,g*c) := by
  refine Prod.ext ?_ ?_
  · rfl
  change (fiberEquiv P b (s b)).symm (fiberEquiv P b (t b) g) = g*c
  apply (fiberEquiv P b (s b)).injective
  rw [Equiv.apply_symm_apply, fiberEquiv_apply, fiberEquiv_apply, mul_smul, h]

def overlapBase (i j : (sectionCharts P).Index) :=
  embedding.map ((sectionAtlas P).left i j) ≫ (sectionAtlas P).chart i
def overlapSectionLeft (i j : (sectionCharts P).Index) :
    SplitSheaf.Tm (SheafTorsor.reindex P (overlapBase P i j)).family :=
  SplitSheaf.readTerm P.family
    (embedding.map ((sectionAtlas P).left i j) ≫ ChartFamily.TorsorAtlas.localLift .preferred P i)
    (by rw [Category.assoc, ChartFamily.TorsorAtlas.localLift_projection]; rfl)
def overlapSectionRight (i j : (sectionCharts P).Index) :
    SplitSheaf.Tm (SheafTorsor.reindex P (overlapBase P i j)).family :=
  SplitSheaf.readTerm P.family
    (embedding.map ((sectionAtlas P).right i j) ≫ ChartFamily.TorsorAtlas.localLift .preferred P j)
    (by rw [Category.assoc, ChartFamily.TorsorAtlas.localLift_projection];
        exact ((sectionAtlas P).square i j).w.symm)
def overlapLabel (i j : (sectionCharts P).Index) :
    embedding.obj ((sectionAtlas P).pair i j) ⟶ locallyConstantGroupSheaf G :=
  SheafTorsor.sectionDifference _ (overlapSectionLeft P i j) (overlapSectionRight P i j)

def transitionLabel (i j : (sectionCharts P).Index) :
    LocallyConstant (Points ((sectionAtlas P).pair i j)) G :=
  ordinaryHomLabelEquiv G _ (overlapLabel P i j)

def overlapInput (i j : (sectionCharts P).Index)
    (b : { b : B // b ∈ ((sectionCharts P).chart i).source ∩ ((sectionCharts P).chart j).source }) :
    Points ((sectionAtlas P).pair i j) :=
  ⟨((sectionCharts P).chart i) b.val, by
    apply mul_ne_zero
    · exact (sectionInput P i b.val b.property.1).property
    · apply (coordinateDefining_iff ((sectionCharts P).chart j) id continuous_id _).mpr
      exact ⟨((sectionCharts P).chart i).map_source b.property.1,
        by simpa only [id_eq, ((sectionCharts P).chart i).left_inv b.property.1] using b.property.2⟩⟩
theorem continuous_overlapInput (i j : (sectionCharts P).Index) :
    Continuous (overlapInput P i j) := by
  apply Continuous.subtype_mk
  exact (((sectionCharts P).chart i).continuousOn.comp_continuous continuous_subtype_val
    (fun b => b.property.1))

theorem overlapInput_left (i j : (sectionCharts P).Index)
    (b : { b : B // b ∈ ((sectionCharts P).chart i).source ∩ ((sectionCharts P).chart j).source }) :
    (show Map _ _ from (sectionAtlas P).left i j) (overlapInput P i j b) =
      sectionInput P i b.val b.property.1 := Subtype.ext rfl

theorem overlapInput_right (i j : (sectionCharts P).Index)
    (b : { b : B // b ∈ ((sectionCharts P).chart i).source ∩ ((sectionCharts P).chart j).source }) :
    (show Map _ _ from (sectionAtlas P).right i j) (overlapInput P i j b) =
      sectionInput P j b.val b.property.2 := by
  apply (chartPoint_isOpenEmbedding ((sectionCharts P).chart j)).injective
  exact ((sectionCharts P).agreement i j (overlapInput P i j b)).symm.trans
    ((((sectionCharts P).chart i).left_inv b.property.1).trans
      (((sectionCharts P).chart j).left_inv b.property.2).symm)

theorem transitionLabel_smul_sectionPoint (i j : (sectionCharts P).Index)
    (x : Points ((sectionAtlas P).pair i j)) :
    transitionLabel P i j x • sectionPoint P i ((show Map _ _ from (sectionAtlas P).left i j) x) =
      sectionPoint P j ((show Map _ _ from (sectionAtlas P).right i j) x) := by
  have h := sectionDifference_point_action P (overlapBase P i j)
    (overlapSectionLeft P i j) (overlapSectionRight P i j)
    (embedding.map ((sectionAtlas P).left i j) ≫ ChartFamily.TorsorAtlas.localLift .preferred P i)
    (embedding.map ((sectionAtlas P).right i j) ≫ ChartFamily.TorsorAtlas.localLift .preferred P j)
    (SplitSheaf.pair_read _ _ _) (SplitSheaf.pair_read _ _ _) (ordinaryPoint _ x)
    (transitionLabel P i j x) (SmoothOrdinaryQuotient.ordinaryHomLabelEquiv_point _ _ x)
  exact (congrArg (fun z : Total P => transitionLabel P i j x • z)
    (totalPointEquiv_symm_map_comp P ((sectionAtlas P).left i j) (ChartFamily.TorsorAtlas.localLift .preferred P i) x)).trans
    (h.trans (totalPointEquiv_symm_map_comp P ((sectionAtlas P).right i j)
      (ChartFamily.TorsorAtlas.localLift .preferred P j) x).symm)
theorem transitionLabel_smul_sectionValue (i j : (sectionCharts P).Index) (b : B)
    (hi : b ∈ ((sectionCharts P).chart i).source)
    (hj : b ∈ ((sectionCharts P).chart j).source)
    (x : Points ((sectionAtlas P).pair i j))
    (hxi : (show Map _ _ from (sectionAtlas P).left i j) x = sectionInput P i b hi)
    (hxj : (show Map _ _ from (sectionAtlas P).right i j) x = sectionInput P j b hj) :
    transitionLabel P i j x • sectionValue P i b = sectionValue P j b := by
  have hl := (sectionValue_spec P i b hi).trans (congrArg (sectionPoint P i) hxi.symm)
  have hr := (sectionValue_spec P j b hj).trans (congrArg (sectionPoint P j) hxj.symm)
  exact Bundle.TotalSpace.mk_inj.mp
    ((congrArg (fun z : Total P => transitionLabel P i j x • z) hl).trans
      ((transitionLabel_smul_sectionPoint P i j x).trans hr.symm))

theorem transitionLabel_sectionValue (i j : (sectionCharts P).Index) (b : B)
    (hi : b ∈ ((sectionCharts P).chart i).source)
    (hj : b ∈ ((sectionCharts P).chart j).source)
    (x : Points ((sectionAtlas P).pair i j))
    (hxi : (show Map _ _ from (sectionAtlas P).left i j) x = sectionInput P i b hi)
    (hxj : (show Map _ _ from (sectionAtlas P).right i j) x = sectionInput P j b hj) :
    transitionLabel P i j x = (fiberEquiv P b (sectionValue P i b)).symm (sectionValue P j b) :=
  (fiberEquiv P b (sectionValue P i b)).injective
    ((transitionLabel_smul_sectionValue P i j b hi hj x hxi hxj).trans
      ((fiberEquiv P b (sectionValue P i b)).apply_symm_apply (sectionValue P j b)).symm)

theorem transitionLabel_overlapInput_smul (i j : (sectionCharts P).Index)
    (b : { b : B // b ∈ ((sectionCharts P).chart i).source ∩ ((sectionCharts P).chart j).source }) :
    transitionLabel P i j (overlapInput P i j b) • sectionValue P i b.val = sectionValue P j b.val :=
  transitionLabel_smul_sectionValue P i j b.val b.property.1 b.property.2
    (overlapInput P i j b) (overlapInput_left P i j b) (overlapInput_right P i j b)


instance fiberTopology (b : B) : TopologicalSpace (Fiber P b) := ⊥
instance fiberDiscrete (b : B) : DiscreteTopology (Fiber P b) := ⟨rfl⟩

variable [TopologicalSpace G] [DiscreteTopology G]

def pretrivialization (i : (sectionCharts P).Index) :
    Bundle.Pretrivialization G (Bundle.TotalSpace.proj : Total P → B) where
  toFun := productEquiv P (sectionValue P i)
  invFun := (productEquiv P (sectionValue P i)).symm
  source := Bundle.TotalSpace.proj ⁻¹' ((sectionCharts P).chart i).source
  target := ((sectionCharts P).chart i).source ×ˢ Set.univ
  map_source' _ hz := ⟨hz, Set.mem_univ _⟩
  map_target' _ hbg := hbg.1
  left_inv' z _ := (productEquiv P (sectionValue P i)).left_inv z
  right_inv' bg _ := (productEquiv P (sectionValue P i)).right_inv bg
  open_target := ((sectionCharts P).chart i).open_source.prod isOpen_univ
  baseSet := ((sectionCharts P).chart i).source
  open_baseSet := ((sectionCharts P).chart i).open_source
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

def fiberHomeomorph (b : B) (p : Fiber P b) : G ≃ₜ Fiber P b where
  toEquiv := fiberEquiv P b p
  continuous_toFun := continuous_of_discreteTopology
  continuous_invFun := continuous_of_discreteTopology
theorem pretrivialization_inducing (i : (sectionCharts P).Index) (b : B) :
    IsInducing (pretrivialization P i ∘ Bundle.TotalSpace.mk b) := by
  exact (isInducing_prodMkRight b).comp (fiberHomeomorph P b (sectionValue P i b)).symm.isInducing

theorem continuous_pretrivialization_change (i j : (sectionCharts P).Index)
 :
    ContinuousOn (pretrivialization P i ∘ (pretrivialization P j).toPartialEquiv.symm)
      ((pretrivialization P j).target ∩ (pretrivialization P j).toPartialEquiv.symm ⁻¹'
        (pretrivialization P i).source) := by
  rw [(pretrivialization P i).target_inter_preimage_symm_source_eq]
  apply continuousOn_iff_continuous_domRestrict.mpr
  let S := (((sectionCharts P).chart i).source ∩ ((sectionCharts P).chart j).source) ×ˢ (Set.univ : Set G)
  have hc : Continuous (fun z : S => (⟨z.val.1,z.property.1⟩ :
      { b : B // b ∈ ((sectionCharts P).chart i).source ∩ ((sectionCharts P).chart j).source })) :=
    Continuous.subtype_mk continuous_subtype_val.fst _
  have hl := (transitionLabel P i j).continuous.comp ((continuous_overlapInput P i j).comp hc)
  have hh := continuous_subtype_val.fst.prodMk (continuous_subtype_val.snd.mul hl)
  apply hh.congr
  intro z
  exact (productEquiv_change P (sectionValue P i) (sectionValue P j) z.val.1 z.val.2
    (transitionLabel P i j (overlapInput P i j ⟨z.val.1,z.property.1⟩)) (transitionLabel_overlapInput_smul P i j _)).symm

def prebundle : FiberPrebundle G (Fiber P) where
  pretrivializationAtlas := Set.range (pretrivialization P)
  pretrivializationAt b := pretrivialization P ((sectionCharts P).covers b).choose
  mem_base_pretrivializationAt b := ((sectionCharts P).covers b).choose_spec
  pretrivialization_mem_atlas b := ⟨_,rfl⟩
  continuous_trivChange e he e' he' := by
    rcases he with ⟨i,rfl⟩
    rcases he' with ⟨j,rfl⟩
    exact continuous_pretrivialization_change P i j
  totalSpaceMk_isInducing b := pretrivialization_inducing P _ b

end SquareKit.SmoothTorsorReconstruction
