import SquareKit.SmoothManifoldActionComparison
import Examples.SmoothOrdinaryComparison
import Mathlib.Algebra.Group.PUnit
import Mathlib.Data.Fintype.Perm
import Mathlib.Topology.Instances.Real.Lemmas

/-! Controls for the complete manifold quotient-arrow comparison. -/
noncomputable section
open CategoryTheory
open scoped Manifold ContDiff Orbifolds.FiniteActionPresentation
namespace Examples.SmoothManifoldAction
open SquareKit.SmoothAlgebra
open SquareKit SquareKit.ManifoldRealization SquareKit.EuclideanOpen
open SquareKit.SmoothManifoldAction SquareKit.SmoothManifoldAction.External
open SquareKit.SmoothOpenSite SquareKit.SmoothOrdinaryQuotient

/-- The one-coordinate model is explicitly identified with the usual real line. -/
def lineCoordinates : Space 1 ≃L[ℝ] ℝ := ContinuousLinearEquiv.piUnique ℝ (fun _ : Fin 1 => ℝ)
example : ContMDiff (Model 1) 𝓘(ℝ, ℝ) ∞ lineCoordinates := lineCoordinates.contDiff.contMDiff
example : ContMDiff 𝓘(ℝ, ℝ) (Model 1) ∞ lineCoordinates.symm := lineCoordinates.symm.contDiff.contMDiff
example : NoncompactSpace (Space 1) := inferInstance

local instance trivial (G : Type) [Group G] : MulAction G (Space 1) where
  smul _ x := x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

def smooth (G : Type) [Group G] (g : G) : ContMDiff (Model 1) (Model 1) ∞
    (fun x : Space 1 => g • x) := contMDiff_id

def constant (U : Domain) (r : ℝ) : SmoothMap U 1 (Space 1) :=
  ⟨fun _ _ => r, contMDiff_const⟩

def family {G : Type} [Group G] [TopologicalSpace G] [DiscreteTopology G]
    (U : Domain) (g : LocallyConstant (Points U) G) : Family (G := G) U (constant U 0) (constant U 0) :=
  labelsEquiv _ _ ⟨g, fun _ => rfl⟩

def arrow {G : Type} [Group G] [TopologicalSpace G] [DiscreteTopology G]
    (U : Domain) (g : LocallyConstant (Points U) G) :
    ChartArrow (smooth G) (constant U 0) (constant U 0) :=
  (smoothChartEquiv (smooth G) _ _).symm (family U g)

theorem recovered_family {G : Type} [Group G] [TopologicalSpace G] [DiscreteTopology G]
    (U : Domain) (g : LocallyConstant (Points U) G) :
    smoothChartEquiv (smooth G) _ _ (arrow U g) = family U g :=
  (smoothChartEquiv (smooth G) _ _).apply_symm_apply _

/-- Trivial-group quotient arrows on the noncompact line retain the diagonal. -/
example : (smoothChartEquiv (smooth PUnit) _ _
    (arrow (full 1) (LocallyConstant.const _ (PUnit.unit : PUnit)))).val (realLinePoint 3) =
      (PUnit.unit, fun _ => (0 : ℝ)) := by
  rw [recovered_family]
  rfl

abbrev S3 := Equiv.Perm (Fin 3)
local instance : TopologicalSpace S3 := ⊥
local instance : DiscreteTopology S3 := ⟨rfl⟩
def g : S3 := Equiv.swap 0 1
def h : S3 := Equiv.swap 1 2
def cycle : S3 := h * g

theorem ineffective_distinct :
    arrow (full 1) (LocallyConstant.const _ g) ≠
      arrow (full 1) (LocallyConstant.const _ (1 : S3)) := by
  intro e
  have e' := congrArg (fun a => ((smoothChartEquiv (smooth S3) _ _ a).val (realLinePoint 0)).1 0) e
  simp only [recovered_family] at e'
  change (Equiv.swap (0 : Fin 3) 1) 0 = 0 at e'
  norm_num [Equiv.swap_apply_def] at e'

theorem noncommuting_order :
    let a := arrow (full 1) (LocallyConstant.const _ g)
    let b := arrow (full 1) (LocallyConstant.const _ h)
    ((smoothChartEquiv (smooth S3) _ _ (a.comp b)).val (realLinePoint 0)).1 = h * g ∧
    ((smoothChartEquiv (smooth S3) _ _ (a.comp b)).val (realLinePoint 0)).1 ≠ g * h := by
  dsimp only
  rw [smoothChartEquiv_comp, recovered_family, recovered_family]
  refine ⟨rfl, ?_⟩
  intro e
  have e' := congrArg (fun p : S3 => p 0) e
  change (h * g) 0 = (g * h) 0 at e'
  norm_num [g, h, Equiv.Perm.mul_apply, Equiv.swap_apply_def] at e'

theorem inverse_convention :
    ordinaryArrowLabel (arrow (full 1) (LocallyConstant.const _ cycle)) (realLinePoint 0) = cycle⁻¹ ∧
    ordinaryArrowLabel (arrow (full 1) (LocallyConstant.const _ cycle)) (realLinePoint 0) ≠ cycle := by
  have e := congrArg (fun a => (a.val (realLinePoint 0)).1)
    (recovered_family (full 1) (LocallyConstant.const _ cycle))
  change (ordinaryArrowLabel (arrow (full 1) (LocallyConstant.const _ cycle)) (realLinePoint 0))⁻¹ = cycle at e
  have he := congrArg Inv.inv e
  rw [inv_inv] at he
  refine ⟨he, ?_⟩
  rw [he]
  intro e'
  have e0 := congrArg (fun p : S3 => p 0) e'
  norm_num [cycle, g, h, mul_inv_rev, Equiv.Perm.mul_apply, Equiv.swap_apply_def] at e0

theorem disconnected :
    let a := arrow SmoothClutching.punctured (SmoothOrdinaryComparison.signLabel S3 cycle)
    ((smoothChartEquiv (smooth S3) _ _ a).val SmoothOrdinaryComparison.negativePoint).1 = 1 ∧
    ((smoothChartEquiv (smooth S3) _ _ a).val SmoothOrdinaryComparison.positivePoint).1 = cycle := by
  dsimp only
  rw [recovered_family]
  change (if (-1 : ℝ) < 0 then (1 : S3) else cycle) = 1 ∧
    (if (1 : ℝ) < 0 then (1 : S3) else cycle) = cycle
  norm_num

def shift (c : ℝ) : full 1 ⟶ full 1 where
  toFun x := ⟨fun i => x.val i + c, one_ne_zero⟩
  smooth i := (OpenFunctions.representative_iff _ (fun x => x i + c) (fun _ => rfl)).mpr
    (((contDiff_apply ℝ (fun _ : Fin 1 => ℝ) i).add contDiff_const).contDiffOn)

theorem two_restrictions : shift 1 ≠ 𝟙 (full 1) ∧ shift 2 ≠ 𝟙 (full 1) ∧
    restrictArrow (smooth S3)
      (restrictArrow (smooth S3) (arrow (full 1) (LocallyConstant.const _ cycle)) (shift 1)) (shift 2) =
    restrictArrow (smooth S3) (arrow (full 1) (LocallyConstant.const _ cycle)) (shift 2 ≫ shift 1) := by
  refine ⟨?_, ?_, restrictArrow_comp _ _ _ _⟩
  all_goals
    intro e
    have e' := congrArg (fun f : full 1 ⟶ full 1 => (show EuclideanOpen.Map _ _ from f) (realLinePoint 0) |>.val 0) e
    change (0 : ℝ) + _ = 0 at e'
    norm_num at e'

/-- A varying geometric endpoint checks the actual pulled-back arrow map. -/
def position : SmoothMap (full 1) 1 (Space 1) := ⟨Subtype.val, contMDiff_subtype_val⟩
def movingArrow : ChartArrow (smooth S3) position position :=
  (smoothChartEquiv (smooth S3) position position).symm
    (labelsEquiv position position ⟨LocallyConstant.const _ cycle, fun _ => rfl⟩)

theorem restricted_position :
    (smoothChartEquiv (smooth S3) _ _
      (restrictArrow (smooth S3) (restrictArrow (smooth S3) movingArrow (shift 1)) (shift 2))).val
        (realLinePoint 0) = (cycle, fun _ => (3 : ℝ)) := by
  rw [smoothChartEquiv_restrict, smoothChartEquiv_restrict]
  change ((smoothChartEquiv (smooth S3) position position) movingArrow).val _ = _
  unfold movingArrow
  rw [Equiv.apply_symm_apply]
  refine Prod.ext ?_ ?_
  · rfl
  funext i
  change (0 : ℝ) + 2 + 1 = 3
  norm_num

def emptyDomain : Domain := ⟨1, 0⟩
theorem empty_no_point (x : Points emptyDomain) : False := x.property rfl

/-- Even incompatible constant endpoints admit the unique empty-domain family. -/
def emptyFamily : Family (G := S3) emptyDomain (constant emptyDomain 0) (constant emptyDomain 1) :=
  ⟨fun x => False.elim (empty_no_point x), fun x => False.elim (empty_no_point x),
    fun x => False.elim (empty_no_point x), fun x => False.elim (empty_no_point x)⟩
example : smoothChartEquiv (smooth S3) _ _ ((smoothChartEquiv (smooth S3) _ _).symm emptyFamily) = emptyFamily :=
  smoothChartEquiv_right_inv _ _

/-- On the inhabited line the target certificate rejects those same endpoints. -/
theorem incompatible : IsEmpty (ChartArrow (smooth S3) (constant (full 1) 0) (constant (full 1) 1)) := by
  refine ⟨fun a => ?_⟩
  let f := smoothChartEquiv (smooth S3) _ _ a
  have hs := congrArg (fun y : Space 1 => y 0) (f.property.2.1 (realLinePoint 0))
  have ht := congrArg (fun y : Space 1 => y 0) (f.property.2.2 (realLinePoint 0))
  change ((f.val (realLinePoint 0)).2) 0 = 0 at hs
  change ((f.val (realLinePoint 0)).2) 0 = 1 at ht
  linarith

end Examples.SmoothManifoldAction
