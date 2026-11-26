import Examples.SmoothBundleAtlas
import Examples.SmoothCechDescent
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Topology.Algebra.Module.Equiv.Pi
import Mathlib.RingTheory.RootsOfUnity.Complex

/-! A Hausdorff nontrivial smooth finite cover, derived recovery and no-section
controls. SquareBundle constructs the ordinary smooth sheets for the complex
covering; the C4 doubled-origin and S3 order controls remain separate. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace Examples.SmoothFiniteCover
open CategoryTheory SquareKit SquareKit.ManifoldRealization SquareKit.SmoothOpenSite
open scoped Manifold ContDiff

abbrev PuncturedPlane := {z : ℂ // z ≠ 0}

def square (z : PuncturedPlane) : PuncturedPlane := ⟨z.val ^ 2, pow_ne_zero 2 z.property⟩

theorem square_covering : IsCoveringMap square := isCoveringMap_npow 2 (by norm_num)

theorem square_surjective : Function.Surjective square := by
  intro y
  obtain ⟨z,hz⟩ := IsAlgClosed.exists_pow_nat_eq y.val (by decide : 0 < (2 : ℕ))
  have hn : z ≠ 0 := by intro h; subst z; simp at hz; exact y.property hz.symm
  exact ⟨⟨z,hn⟩,Subtype.ext hz⟩

theorem square_finite_fibers (y : PuncturedPlane) : Set.Finite (square ⁻¹' {y}) := by
  obtain ⟨z,hz⟩ := square_surjective y
  let nz : PuncturedPlane := ⟨-z.val, neg_ne_zero.mpr z.property⟩
  apply ((Set.finite_singleton nz).insert z).subset
  intro w hw
  have he : w.val ^ 2 = z.val ^ 2 := congrArg Subtype.val (hw.trans hz.symm)
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp he with h | h
  · exact Set.mem_insert_iff.mpr (Or.inl (Subtype.ext h))
  · exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr (Subtype.ext h)))

instance : PathConnectedSpace PuncturedPlane :=
  (unitsHomeomorphNeZero (G₀ := ℂ)).surjective.pathConnectedSpace
    (unitsHomeomorphNeZero (G₀ := ℂ)).continuous

/-- A continuous section of this connected Hausdorff two-sheeted cover cannot exist. -/
theorem square_no_continuous_section :
    ¬ ∃ s : PuncturedPlane → PuncturedPlane, Continuous s ∧ Function.RightInverse s square := by
  rintro ⟨s,hs,hr⟩
  have he : square ∘ s = id := funext hr
  have hopen := (square_covering.isLocalHomeomorph.isOpenEmbedding_of_comp
    (he.symm ▸ Topology.IsOpenEmbedding.id) hs).isOpen_range
  have hrange : Set.range s = {z | s (square z) = z} := by
    ext z
    constructor
    · rintro ⟨y,rfl⟩
      change s (square (s y)) = s y
      rw [hr y]
    · intro h
      exact ⟨square z,h⟩
  have hclosed : IsClosed (Set.range s) := by
    rw [hrange]
    exact isClosed_eq (hs.comp square_covering.continuous) continuous_id
  have huniv := (show IsClopen (Set.range s) from ⟨hclosed,hopen⟩).eq_univ
    ⟨s ⟨1,one_ne_zero⟩,Set.mem_range_self _⟩
  have hinj : Function.Injective square := by
    intro z w h
    have hz : s (square z) = z := (congrArg (fun t : Set PuncturedPlane => z ∈ t) hrange).mp (huniv.symm ▸ Set.mem_univ z)
    have hw : s (square w) = w := (congrArg (fun t : Set PuncturedPlane => w ∈ t) hrange).mp (huniv.symm ▸ Set.mem_univ w)
    exact hz.symm.trans ((congrArg s h).trans hw)
  have h := congrArg Subtype.val (hinj (a₁ := ⟨1,one_ne_zero⟩) (a₂ := ⟨-1,by simp⟩)
    (by apply Subtype.ext; norm_num [square]))
  norm_num at h

local instance : MulAction Orbifolds.QuarterTurn.C4 (Space 1) :=
  Examples.SmoothCechDescent.Clutching.trivialAction _

/-- The non-Hausdorff C4 example remains a separate no-section control. -/
theorem doubledOrigin_no_section :
    ¬ Nonempty (SplitSheaf.Tm
      (Examples.SmoothCechDescent.Clutching.quarterTurnDatum.interpreted
        (Examples.SmoothCechDescent.Clutching.smooth Orbifolds.QuarterTurn.C4)).torsor.family) :=
  Examples.SmoothCechDescent.Clutching.quarterTurn_no_section
end Examples.SmoothFiniteCover

namespace Examples.SmoothFiniteCover.C4Bundle
open CategoryTheory SquareKit SquareKit.ManifoldRealization SquareKit.SmoothOpenSite
open Orbifolds.QuarterTurn
open scoped Manifold ContDiff
local instance : TopologicalSpace C4 := ⊥
local instance : DiscreteTopology C4 := ⟨rfl⟩
local instance : ChartedSpace (Space 0) C4 := ChartedSpace.ofDiscreteTopology
local instance : ChartedSpace (Space 0) PUnit := ChartedSpace.ofDiscreteTopology
local instance : IsManifold (modelWithCorners 0) ∞ C4 := IsManifold.of_discreteTopology _
local instance : IsManifold (modelWithCorners 0) ∞ PUnit := IsManifold.of_discreteTopology _

def sheet (g : C4) : OpenPartialHomeomorph C4 PUnit where
  toFun _ := PUnit.unit
  invFun _ := g
  source := {g}
  target := Set.univ
  map_source' _ _ := Set.mem_univ _
  map_target' _ _ := Set.mem_singleton _
  left_inv' _ h := h.symm
  right_inv' _ _ := Subsingleton.elim _ _
  open_source := isOpen_discrete _
  open_target := isOpen_univ
  continuousOn_toFun := continuousOn_const
  continuousOn_invFun := continuousOn_const

/-- A nontrivial finite structure group exercises the ordinary sheet contract.
This bundle over a point is globally trivial; it is not the nontrivial-cover example. -/
def bundle : SmoothPrincipalBundle.Bundle (n := 0) (G := C4) (B := PUnit) (E := C4) where
  projection _ := PUnit.unit
  smooth_projection := contMDiff_const
  smooth_action _ := contMDiff_of_discreteTopology
  invariant _ _ := rfl
  triviality _ := ⟨{
    base := Set.univ
    isOpen_base := isOpen_univ
    sheet := sheet
    target _ := rfl
    projection _ _ _ := rfl
    smooth_inverse _ := contMDiff_const.contMDiffOn
    sheets e _ := ⟨e,rfl,fun _ h => h.symm⟩
    equivariant _ _ _ _ := rfl },Set.mem_univ _⟩

def totalComparison := bundle.totalSpaceIso
def recovered := bundle.quotientRecovery bundle.smooth_action id contMDiff_id (fun _ _ => rfl)
end Examples.SmoothFiniteCover.C4Bundle

namespace Examples.SmoothFiniteCover.DoubledOrigin
open CategoryTheory SquareKit SquareKit.ManifoldRealization SquareKit.SmoothOpenSite SquareKit.EuclideanOpen
open Orbifolds.QuarterTurn
open Examples.SmoothCechDescent.Clutching
local instance : MulAction C4 (Space 1) := trivialAction _
local instance : TopologicalSpace C4 := ⊥
local instance : DiscreteTopology C4 := ⟨rfl⟩

/-- Derive a new section atlas for each restriction of the nontrivial global torsor. -/
def localObject (i : Bool) := SheafActionQuotient.reindex (quarterTurnDatum.interpreted (smooth C4))
  (SmoothClutching.Represented.atlas.chart i)
def localAdmission (i : Bool) := SmoothCech.trivializedOnOpen (smooth C4) SmoothClutching.line (localObject i)
def localRecovery (i : Bool) := (localAdmission i).extractedRecovery

theorem no_global_section_despite_local_recovery :
    ¬ Nonempty (SplitSheaf.Tm (quarterTurnDatum.interpreted (smooth C4)).torsor.family) := quarterTurn_no_section
end Examples.SmoothFiniteCover.DoubledOrigin

namespace Examples.SmoothFiniteCover.Noncommuting
open CategoryTheory Opposite SquareKit SquareKit.ManifoldRealization SquareKit.SmoothOpenSite
open SquareKit.SmoothCech SquareKit.SmoothManifoldAction SquareKit.EuclideanOpen
open Examples.SmoothCechDescent.Clutching
open scoped Manifold ContDiff
abbrev S3 := Equiv.Perm (Fin 3)
local instance : TopologicalSpace S3 := ⊥
local instance : DiscreteTopology S3 := ⟨rfl⟩
local instance : MulAction S3 (Space 1) := trivialAction _

def base := ChartFamily.preferred (n := 1) (M := Space 1)
def zeroMap := (atlasIso base).inv ≫ ManifoldRealization.map (fun _ : Space 1 => (0 : Space 1))
  (show ContMDiff (modelWithCorners 1) (modelWithCorners 1) ∞ (fun _ : Space 1 => (0 : Space 1)) from contMDiff_const)
def quotient := SheafActionQuotient.chart (representation (smooth S3)).action zeroMap

def arrow (g : S3) : SheafActionQuotient.Arrow quotient quotient :=
  SheafActionQuotient.chartArrowOfRelation (constantSection _ g) zeroMap zeroMap (by
    ext U x
    change (representation (smooth S3)).act U ((constantLabel S3).app U g) _ = _
    rw [SmoothConstantAction.Representation.act_constant]
    change (ManifoldRealization.map id contMDiff_id).hom.app U _ = _
    rw [ManifoldRealization.map_id]
    rfl)

theorem arrow_comp (g h : S3) : (arrow g).comp (arrow h) = arrow (g * h) := by
  apply SheafActionQuotient.Arrow.ext
  apply SheafTorsor.Arrow.ext
  ext x p
  change (locallyConstantGroup S3).obj.obj x.obj at p
  change (p * (constantLabel S3).app x.obj g) * (constantLabel S3).app x.obj h =
    p * (constantLabel S3).app x.obj (g * h)
  rw [((constantLabel S3).app x.obj).hom.map_mul, mul_assoc]

def objects (_ : Fin 3) := quotient
def localArrows (i j : Fin 3) (g : S3) :=
  (jointArrowEquiv (smooth S3) base objects i j).symm (arrow g)

/-- The full derived-arrow equivalence preserves the independently computed order. -/
theorem local_order (g h : S3) :
    (localArrows 0 1 g).comp (localArrows 1 2 h) = localArrows 0 2 (g * h) := by
  apply (jointArrowEquiv (smooth S3) base objects 0 2).injective
  rw [joint_composition]
  simp only [localArrows, Equiv.apply_symm_apply]
  exact arrow_comp g h

theorem arrow_injective : Function.Injective arrow := by
  intro g h he
  have e := congrArg SheafActionQuotient.Arrow.torsorArrow he
  have e' := SheafTorsor.regularArrow_injective e
  let x := (atlasIso base).hom.hom.app (op (op (SmoothPresentationSite.free 0)))
    ((pointEquiv (d := 1) (M := Space 1)).symm 0)
  have hx := congrArg (fun k : base.realization ⟶ locallyConstantGroupSheaf S3 =>
    k.hom.app (op (op (SmoothPresentationSite.free 0))) x) e'
  exact constantLabel_injective S3 (SmoothPresentationSite.free 0)
    (𝟙 _) hx

/-- Reversing the noncommuting labels is rejected after passing through the new atlas. -/
theorem local_wrong_order :
    (localArrows 0 1 Examples.SmoothManifoldAction.g).comp
      (localArrows 1 2 Examples.SmoothManifoldAction.h) ≠
    localArrows 0 2 (Examples.SmoothManifoldAction.h * Examples.SmoothManifoldAction.g) := by
  rw [local_order]
  intro e
  have he := congrArg (jointArrowEquiv (smooth S3) base objects 0 2) e
  simp only [localArrows, Equiv.apply_symm_apply] at he
  have hp := congrArg (fun p : S3 => p 0) (arrow_injective he)
  norm_num [Examples.SmoothManifoldAction.g, Examples.SmoothManifoldAction.h,
    Equiv.Perm.mul_apply, Equiv.swap_apply_def] at hp

/-- Independent choices change actual local sections by an equivariant torsor arrow. -/
def shiftedSections (g : S3) : LocalSections (smooth S3) base quotient := fun i => {
  val x := ((arrow g).torsorArrow.reindex _).iso.hom.app x
    (selectedSections (smooth S3) base quotient i |>.val x)
  natural {x y} f := by
    rw [← NatTrans.naturality_apply]
    exact congrArg (((arrow g).torsorArrow.reindex _).iso.hom.app y)
      ((selectedSections (smooth S3) base quotient i).natural f) }

theorem shiftedSections_injective : Function.Injective shiftedSections := by
  intro g h hs
  let A := ChartFamily.TorsorAtlas.charts base quotient.torsor
  obtain ⟨i,hi⟩ := A.covers (0 : Space 1)
  let z : Points (chartDomain (A.chart i)) :=
    (chartTargetEquiv (A.chart i)).symm ⟨A.chart i 0, (A.chart i).map_source hi⟩
  let x := (embedding.obj (chartDomain (A.chart i))).obj.elementsMk
    (op (op (SmoothPresentationSite.free 0))) (ordinaryPoint _ z)
  have he := congrArg (fun s : LocalSections (smooth S3) base quotient => (s i).val x) hs
  change (show (locallyConstantGroup S3).obj.obj x.obj from
    (selectedSections (smooth S3) base quotient i).val x) * (constantLabel S3).app x.obj g =
    (show (locallyConstantGroup S3).obj.obj x.obj from
      (selectedSections (smooth S3) base quotient i).val x) * (constantLabel S3).app x.obj h at he
  exact constantLabel_injective S3 (SmoothPresentationSite.free 0) (𝟙 _) (mul_left_cancel he)

def changedSections := sectionsGauge (smooth S3) base quotient
  (shiftedSections Examples.SmoothManifoldAction.g) (shiftedSections Examples.SmoothManifoldAction.h)

theorem changed_recovery :
    (interpretedHomEquiv (smooth S3) _ _ changedSections).comp
      (sectionsCommonRight (smooth S3) base quotient
        (shiftedSections Examples.SmoothManifoldAction.h)).extractedRecovery =
    (sectionsCommonLeft (smooth S3) base quotient
      (shiftedSections Examples.SmoothManifoldAction.g)).extractedRecovery :=
  sectionsGauge_recovery (smooth S3) base quotient
  (shiftedSections Examples.SmoothManifoldAction.g) (shiftedSections Examples.SmoothManifoldAction.h)
end Examples.SmoothFiniteCover.Noncommuting

open scoped ContDiff
namespace Examples.SmoothFiniteCover.SlitRoots
noncomputable def root (z : ℂ) := Complex.exp (Complex.log z / 2)
theorem root_sq (z : ℂ) (hz : z ≠ 0) : root z ^ 2 = z := by
  rw [root, pow_two, ← Complex.exp_add]
  convert Complex.exp_log hz using 1; congr 1; ring

theorem root_smooth {z : ℂ} (hz : z ∈ Complex.slitPlane) : ContDiffAt ℝ ∞ root z := by
  exact (Complex.contDiff_exp.contDiffAt.comp z
    ((Complex.contDiffAt_log hz).div_const 2)).restrict_scalars ℝ

theorem slit_cover (z : ℂ) (hz : z ≠ 0) :
    z ∈ Complex.slitPlane ∨ -z ∈ Complex.slitPlane := by
  simp only [Complex.mem_slitPlane_iff, Complex.neg_re, Complex.neg_im]
  by_cases hi : z.im = 0
  · have hr : z.re ≠ 0 := by
      intro h
      apply hz
      apply Complex.ext <;> simp [h,hi]
    rcases lt_or_gt_of_ne hr with h | h
    · exact Or.inr (Or.inl (neg_pos.mpr h))
    · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr hi)

theorem opposite_root_sq (z : ℂ) (hz : z ≠ 0) :
    (Complex.I * root (-z)) ^ 2 = z := by
  rw [mul_pow, Complex.I_sq, root_sq (-z) (neg_ne_zero.mpr hz)]
  ring

theorem opposite_root_smooth {z : ℂ} (hz : -z ∈ Complex.slitPlane) :
    ContDiffAt ℝ ∞ (fun z => Complex.I * root (-z)) z :=
  contDiffAt_const.mul ((root_smooth hz).comp z contDiffAt_id.neg)
end Examples.SmoothFiniteCover.SlitRoots

open CategoryTheory Topology Set
open SquareKit SquareKit.ManifoldRealization
open scoped Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace Examples.SmoothFiniteCover.SquareBundle
abbrev E := Examples.SmoothFiniteCover.PuncturedPlane
instance : Nonempty E := ⟨⟨1,one_ne_zero⟩⟩
def coordEquiv : ℂ ≃L[ℝ] Space 2 :=
  Complex.equivRealProdCLM.trans (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm
def coord (z : E) : Space 2 := coordEquiv z.val
theorem coord_open : IsOpenEmbedding coord :=
  coordEquiv.toHomeomorph.isOpenEmbedding.comp
    (isOpen_ne : IsOpen {z : ℂ | z ≠ 0}).isOpenEmbedding_subtypeVal
local instance manifoldCharts : ChartedSpace (Space 2) E := coord_open.singletonChartedSpace
local instance manifoldSmooth : IsManifold (modelWithCorners 2) ∞ E := coord_open.isManifold_singleton

theorem coord_smooth : ContMDiff (modelWithCorners 2) (modelWithCorners 2) ∞ coord := contMDiff_isOpenEmbedding coord_open

theorem ambient_smooth (F : ℂ → ℂ) (hF : ContDiff ℝ ∞ F) (f : E → E)
    (he : ∀ z, (f z).val = F z.val) : ContMDiff (modelWithCorners 2) (modelWithCorners 2) ∞ f := by
  apply ContMDiff.of_comp_isOpenEmbedding coord_open
  have h : ContDiff ℝ ∞ (coordEquiv ∘ F ∘ coordEquiv.symm) :=
    coordEquiv.contDiff.comp (hF.comp coordEquiv.symm.contDiff)
  have hh := h.contMDiff.comp coord_smooth
  convert hh using 1
  funext z
  simp [coord, Function.comp_def, he]

theorem square_smooth : ContMDiff (modelWithCorners 2) (modelWithCorners 2) ∞ Examples.SmoothFiniteCover.square :=
  ambient_smooth (fun z => z^2) (contDiff_id.pow 2) _ (fun _ => rfl)
theorem ambient_smoothAt (F : ℂ → ℂ) (f : E → E)
    (he : ∀ z, (f z).val = F z.val) (z : E) (hF : ContDiffAt ℝ ∞ F z.val) :
    ContMDiffAt (modelWithCorners 2) (modelWithCorners 2) ∞ f z := by
  have hF' : ContDiffAt ℝ ∞ F (coordEquiv.symm (coord z)) := by simpa [coord] using hF
  have h : ContDiffAt ℝ ∞ (coordEquiv ∘ F ∘ coordEquiv.symm) (coord z) :=
    coordEquiv.contDiff.contDiffAt.comp _
      (hF'.comp _ coordEquiv.symm.contDiff.contDiffAt)
  have hh : ContMDiffAt (modelWithCorners 2) (modelWithCorners 2) ∞ (coord ∘ f) z := by
    convert h.contMDiffAt.comp z coord_smooth.contMDiffAt using 1
    funext y
    simp [coord, Function.comp_def, he]
  have hi := (contMDiffOn_isOpenEmbedding_symm (I := modelWithCorners 2) (n := ∞) coord_open).contMDiffAt
    (coord_open.isOpen_range.mem_nhds (Set.mem_range_self (f z)))
  apply (hi.comp z hh).congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun y => (coord_open.toOpenPartialHomeomorph_left_inv coord (x := f y)).symm)
/-- The finite two-element deck group, acting by complex multiplication. -/
abbrev G := rootsOfUnity 2 ℂ

theorem group_card : Nat.card G = 2 := Complex.card_rootsOfUnity 2

example : Finite G := inferInstance
example : T2Space E := inferInstance
local instance : TopologicalSpace G := ⊥
local instance : DiscreteTopology G := ⟨rfl⟩
local instance rootAction : MulAction G E where
  smul g z := ⟨(g.val : ℂ) * z.val, mul_ne_zero (Units.ne_zero _) z.property⟩
  one_smul z := by apply Subtype.ext; exact one_mul z.val
  mul_smul g h z := by apply Subtype.ext; exact mul_assoc _ _ _

theorem smul_val (g : G) (z : E) : (g • z).val = (g.val : ℂ) * z.val := rfl

theorem action_smooth (g : G) : ContMDiff (modelWithCorners 2) (modelWithCorners 2) ∞ (fun z : E => g • z) :=
  ambient_smooth (fun z => (g.val : ℂ) * z) (contDiff_const.mul contDiff_id) _ (fun _ => rfl)

theorem invariant (g : G) (z : E) : Examples.SmoothFiniteCover.square (g • z) =
    Examples.SmoothFiniteCover.square z := by
  apply Subtype.ext
  change ((g.val : ℂ) * z.val)^2 = z.val^2
  rw [mul_pow, (mem_rootsOfUnity' 2 g.val).mp g.property, one_mul]

theorem fiber_principal (z w : E) (h : Examples.SmoothFiniteCover.square z =
    Examples.SmoothFiniteCover.square w) : ∃! g : G, g • z = w := by
  have he : z.val^2 = w.val^2 := congrArg Subtype.val h
  let u : ℂˣ := Units.mk0 (w.val / z.val) (div_ne_zero w.property z.property)
  have hu : u ∈ rootsOfUnity 2 ℂ := by
    apply (mem_rootsOfUnity' 2 u).mpr
    change (w.val / z.val)^2 = 1
    rw [div_pow, ← he, div_self (pow_ne_zero _ z.property)]
  refine ⟨⟨u,hu⟩, ?_, ?_⟩
  · apply Subtype.ext
    exact div_mul_cancel₀ w.val z.property
  · intro g hg
    apply Subtype.ext
    apply Units.ext
    apply (mul_left_injective₀ z.property)
    have hv := congrArg Subtype.val hg
    exact hv.trans (div_mul_cancel₀ w.val z.property).symm
open Examples.SmoothFiniteCover
variable (V : Set E) (hV : IsOpen V) (s : E → E)
  (hs : ContMDiffOn (modelWithCorners 2) (modelWithCorners 2) ∞ s V)
  (hp : ∀ b ∈ V, square (s b) = b)

def branch (g : G) (b : V) : E := g • s b.val

include hp in
theorem branch_projection (g : G) (b : V) : square (branch V s g b) = b.val :=
  (invariant g (s b.val)).trans (hp b.val b.property)

include hV hs hp in
theorem branch_open (g : G) : IsOpenEmbedding (branch V s g) := by
  have he : square ∘ branch V s g = Subtype.val := funext (branch_projection V s hp g)
  apply square_covering.isLocalHomeomorph.isOpenEmbedding_of_comp (he.symm ▸ hV.isOpenEmbedding_subtypeVal)
  exact (action_smooth g).continuous.comp hs.continuousOn.domRestrict

def sheet (g : G) : OpenPartialHomeomorph E E where
  toFun := square
  invFun b := g • s b
  source := Set.range (branch V s g)
  target := V
  map_source' e he := by
    obtain ⟨b,rfl⟩ := he
    rw [branch_projection V s hp]
    exact b.property
  map_target' b hb := ⟨⟨b,hb⟩,rfl⟩
  left_inv' e he := by
    obtain ⟨b,rfl⟩ := he
    rw [branch_projection V s hp]
    rfl
  right_inv' b hb := (invariant g (s b)).trans (hp b hb)
  open_source := (branch_open V hV s hs hp g).isOpen_range
  open_target := hV
  continuousOn_toFun := square_covering.continuous.continuousOn
  continuousOn_invFun := (action_smooth g).continuous.comp_continuousOn hs.continuousOn

theorem sheet_source_iff (g : G) (e : E) (he : square e ∈ V) :
    e ∈ (sheet V hV s hs hp g).source ↔ g • s (square e) = e := by
  constructor
  · rintro ⟨b,rfl⟩
    rw [branch_projection V s hp]
    rfl
  · intro h
    exact ⟨⟨square e,he⟩,h⟩

def trivialization : SmoothPrincipalBundle.LocalTrivialization (n := 2) (G := G) square where
  base := V
  isOpen_base := hV
  sheet := sheet V hV s hs hp
  target _ := rfl
  projection _ _ _ := rfl
  smooth_inverse g := (action_smooth g).comp_contMDiffOn hs
  sheets e he := by
    obtain ⟨g,hg,hu⟩ := fiber_principal (s (square e)) e (hp (square e) he)
    exact ⟨g,(sheet_source_iff V hV s hs hp g e he).mpr hg,
      fun h hh => hu h ((sheet_source_iff V hV s hs hp h e he).mp hh)⟩
  equivariant g h b _ := mul_smul g h (s b)
open SlitRoots

def positiveRoot (b : E) : E := ⟨root b.val, Complex.exp_ne_zero _⟩
def negativeRoot (b : E) : E := ⟨Complex.I * root (-b.val),
  mul_ne_zero Complex.I_ne_zero (Complex.exp_ne_zero _)⟩

def positiveSlit : Set E := {b | b.val ∈ Complex.slitPlane}
def negativeSlit : Set E := {b | -b.val ∈ Complex.slitPlane}

theorem positiveSlit_open : IsOpen positiveSlit := Complex.isOpen_slitPlane.preimage continuous_subtype_val
theorem negativeSlit_open : IsOpen negativeSlit := Complex.isOpen_slitPlane.preimage continuous_subtype_val.neg

theorem positiveRoot_smooth : ContMDiffOn (modelWithCorners 2) (modelWithCorners 2) ∞ positiveRoot positiveSlit := by
  intro b hb
  exact (ambient_smoothAt root positiveRoot (fun _ => rfl) b (root_smooth hb)).contMDiffWithinAt

theorem negativeRoot_smooth : ContMDiffOn (modelWithCorners 2) (modelWithCorners 2) ∞ negativeRoot negativeSlit := by
  intro b hb
  exact (ambient_smoothAt (fun z => Complex.I * root (-z)) negativeRoot (fun _ => rfl) b
    (opposite_root_smooth hb)).contMDiffWithinAt

theorem positiveRoot_projection (b : E) (_ : b ∈ positiveSlit) : square (positiveRoot b) = b :=
  Subtype.ext (root_sq b.val b.property)

theorem negativeRoot_projection (b : E) (_ : b ∈ negativeSlit) : square (negativeRoot b) = b :=
  Subtype.ext (opposite_root_sq b.val b.property)

/-- Both slit neighborhoods supply equivariant smooth sheets for the square map. -/
def bundle : SmoothPrincipalBundle.Bundle (n := 2) (G := G) (B := E) (E := E) where
  projection := square
  smooth_projection := square_smooth
  smooth_action := action_smooth
  invariant := invariant
  triviality b := by
    rcases slit_cover b.val b.property with h | h
    · exact ⟨trivialization positiveSlit positiveSlit_open positiveRoot
        positiveRoot_smooth positiveRoot_projection,h⟩
    · exact ⟨trivialization negativeSlit negativeSlit_open negativeRoot
        negativeRoot_smooth negativeRoot_projection,h⟩

def totalComparison := bundle.totalSpaceIso
def recovered := bundle.quotientRecovery bundle.smooth_action id contMDiff_id (fun _ _ => rfl)
/-- A sheaf section would reconstruct a smooth, hence continuous, ordinary
section through the actual total-space and projection comparisons. -/
theorem no_sheaf_section : ¬ Nonempty (SplitSheaf.Tm bundle.descendedObject.torsor.family) := by
  rintro ⟨t⟩
  let k := (SplitSheaf.terms bundle.descendedObject.torsor.family) t
  let f : object 2 E ⟶ object 2 E := (atlasIso bundle.baseCharts).hom ≫ k.val ≫ bundle.totalSpaceIso.hom
  have hp : f ≫ ManifoldRealization.map square square_smooth = 𝟙 _ := by
    have hproj := bundle.totalSpaceIso_projection
    change bundle.totalSpaceIso.hom ≫ ManifoldRealization.map square square_smooth = _ at hproj
    dsimp only [f]
    rw [Category.assoc, Category.assoc, hproj, ← Category.assoc k.val,
      k.property, Category.id_comp, Iso.hom_inv_id]
  apply square_no_continuous_section
  refine ⟨ManifoldRealization.reconstruct f, (ManifoldRealization.reconstruct_smooth f).continuous, ?_⟩
  have h := congrArg ManifoldRealization.reconstruct hp
  rw [ManifoldRealization.reconstruct_comp, ManifoldRealization.reconstruct_map,
    ManifoldRealization.reconstruct_id] at h
  exact congrFun h
end Examples.SmoothFiniteCover.SquareBundle
