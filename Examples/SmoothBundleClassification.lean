import SquareKit.SmoothBundleClassificationTargets
import Examples.SmoothBundlePullback
import Examples.SmoothBundleMorphisms
import Examples.SmoothTorsorReconstruction
import Examples.SmoothDoubleOriginManifold

/-! Classification consumers with automorphisms, nontrivial covers and
an actual non-Hausdorff ordinary base. -/
noncomputable section
set_option autoImplicit false
namespace Examples.SmoothBundleClassification
open CategoryTheory SquareKit SquareKit.ManifoldRealization SquareKit.SmoothPrincipalBundle
open scoped Manifold ContDiff

namespace Finite
open Orbifolds.QuarterTurn
local instance : TopologicalSpace C4 := ⊥
local instance : DiscreteTopology C4 := ⟨rfl⟩
local instance : ChartedSpace (Space 0) C4 := ChartedSpace.ofDiscreteTopology
local instance : ChartedSpace (Space 0) PUnit := ChartedSpace.ofDiscreteTopology
local instance : IsManifold (modelWithCorners 0) ∞ C4 := IsManifold.of_discreteTopology _
local instance : IsManifold (modelWithCorners 0) ∞ PUnit := IsManifold.of_discreteTopology _

def bundle : Ordinary 0 C4 PUnit := Ordinary.ofBundle SmoothFiniteCover.C4Bundle.bundle

def rotation (g : C4) : bundle ⟶ bundle := SmoothBundleMorphisms.rotation g

theorem realized_rotation_nonidentity {g : C4} (hg : g ≠ 1) :
    Ordinary.realization.map (rotation g) ≠ 𝟙 (Ordinary.realization.obj bundle) := by
  intro h
  apply SmoothBundleMorphisms.rotation_nonidentity hg
  exact Ordinary.realization.map_injective (h.trans (Ordinary.realization.map_id bundle).symm)

theorem rotation_composite (g h : C4) :
    Ordinary.realization.map (rotation g) ≫ Ordinary.realization.map (rotation h) =
      Ordinary.realization.map (rotation (g*h)) := by
  rw [← Functor.map_comp]
  exact congrArg Ordinary.realization.map (SmoothBundleMorphisms.rotation_comp g h)

theorem recovered_rotation (g : C4) :
    (Ordinary.unitComponent bundle).hom ≫
        Ordinary.reconstruction.map (Ordinary.realization.map (rotation g)) =
      rotation g ≫ (Ordinary.unitComponent bundle).hom :=
  (Ordinary.unit.hom.naturality (rotation g)).symm

local instance : MulAction C4 PUnit where
  smul _ _ := PUnit.unit
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

def ineffectiveTarget : Ordinary.WithTarget 0 0 C4 PUnit PUnit where
  ordinary := bundle
  target _ := PUnit.unit
  smooth := contMDiff_const
  equivariant _ _ := rfl

theorem ineffective_action (g : C4) :
    ContMDiff (modelWithCorners 0) (modelWithCorners 0) ∞ (fun x : PUnit => g • x) := contMDiff_const

def targetRotation (g : C4) : ineffectiveTarget ⟶ ineffectiveTarget where
  toMap := rotation g
  target _ := rfl

theorem ineffective_target_distinguishes {g : C4} (hg : g ≠ 1) :
    (Ordinary.WithTarget.realization ineffective_action).map (targetRotation g) ≠
      𝟙 ((Ordinary.WithTarget.realization ineffective_action).obj ineffectiveTarget) := by
  intro h
  have he := (Ordinary.WithTarget.realization ineffective_action).map_injective
    (h.trans ((Ordinary.WithTarget.realization ineffective_action).map_id ineffectiveTarget).symm)
  exact SmoothBundleMorphisms.rotation_nonidentity hg (congrArg TargetMap.toMap he)

theorem quarterTurn_ne_one : quarterTurn ≠ 1 := by
  intro h
  have he := congrArg (fun z : C4 => (z.val : ℂ)) h
  have hi := congrArg Complex.im he
  norm_num [quarterTurn] at hi

theorem concrete_nonidentity :
    (Ordinary.WithTarget.realization ineffective_action).map (targetRotation quarterTurn) ≠
      𝟙 ((Ordinary.WithTarget.realization ineffective_action).obj ineffectiveTarget) :=
  ineffective_target_distinguishes quarterTurn_ne_one

end Finite

namespace Square
open SmoothFiniteCover.SquareBundle
local instance : TopologicalSpace G := ⊥
local instance : DiscreteTopology G := ⟨rfl⟩
local instance : ChartedSpace (Space 2) E := manifoldCharts
local instance : IsManifold (modelWithCorners 2) ∞ E := manifoldSmooth
local instance : MulAction G E := rootAction

def ordinary : Ordinary 2 G E := Ordinary.ofBundle bundle
abbrev recovered := Ordinary.reconstructed (Ordinary.realization.obj ordinary)

theorem recovered_no_section :
    ¬ ∃ s : E → recovered.Total, Continuous s ∧ Function.RightInverse s recovered.bundle.projection := by
  rintro ⟨s, hs, hp⟩
  apply SmoothFiniteCover.square_no_continuous_section
  let a := (Ordinary.unitComponent ordinary).inv
  refine ⟨a.toFun ∘ s, a.smooth.continuous.comp hs, ?_⟩
  intro b
  exact (a.projection (s b)).trans (hp b)

theorem recovered_projection (x : E) :
    recovered.bundle.projection (Ordinary.unitDiffeomorph ordinary x) = SmoothFiniteCover.square x :=
  Ordinary.unit_projection ordinary x

theorem recovered_hausdorff : T2Space recovered.Total :=
  Ordinary.reconstructed_t2Space (Ordinary.realization.obj ordinary)

theorem secondCountableTopology_recovered : SecondCountableTopology recovered.Total :=
  Ordinary.reconstructed_secondCountableTopology (Ordinary.realization.obj ordinary)

/-- Recovery may be compared on any covering chart family of the nontrivial base. -/
theorem chart_comparison (A : ChartFamily 2 E) : type_of%
    (Ordinary.chartChoiceComparison_of_global A
      (Iso.refl (Ordinary.realization.obj ordinary))
      (Ordinary.recovery (Ordinary.realization.obj ordinary))) :=
  Ordinary.chartChoiceComparison_of_global A
    (Iso.refl (Ordinary.realization.obj ordinary))
    (Ordinary.recovery (Ordinary.realization.obj ordinary))

theorem bundle_chart_comparison : type_of% (chart_comparison bundle.baseCharts) :=
  chart_comparison bundle.baseCharts

end Square

namespace NonHausdorff
open SmoothDoubleOriginManifold
local instance : MulAction PUnit D where
  smul _ x := x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

def ordinary : Ordinary 1 PUnit D := Ordinary.ofBundle (identityBundle (G := PUnit) (B := D))
abbrev torsor := Ordinary.realization.obj ordinary
abbrev recovered := Ordinary.reconstructed torsor
local instance : MulAction PUnit recovered.Total := recovered.action

def comparison : D ≃ₘ⟮modelWithCorners 1, modelWithCorners 1⟯ recovered.Total := Ordinary.unitDiffeomorph ordinary

theorem recovered_not_t2 : ¬ T2Space recovered.Total := by
  intro h
  let := h
  exact not_t2Space comparison.symm.toHomeomorph.t2Space

theorem recovered_origins_distinct : comparison (origin false) ≠ comparison (origin true) :=
  fun h => origins_ne (comparison.injective h)

theorem recovered_projection (x : D) : recovered.bundle.projection (comparison x) = x :=
  Ordinary.unit_projection ordinary x

end NonHausdorff
namespace BaseChange
open SmoothBundleAtlas

def line : Ordinary 1 PUnit (Space 1) := Ordinary.ofBundle realLineBundle

theorem scale_two_ne_id : scale 2 ≠ id := by
  intro h
  have he := congrFun (congrFun h (fun _ => 1)) 0
  norm_num [scale] at he

theorem scale_three_ne_id : scale 3 ≠ id := by
  intro h
  have he := congrFun (congrFun h (fun _ => 1)) 0
  norm_num [scale] at he

def composite := Ordinary.pullbackCompositionComponent
  (scale 2) (scale_smooth 2) (scale 3) (scale_smooth 3) line

theorem composite_coordinates
    (z : (Ordinary.pulledBack (scale 3) (scale_smooth 3)
      (Ordinary.pulledBack (scale 2) (scale_smooth 2) line)).Total) :
    (composite.hom.toFun z).val = (z.val.1, z.val.2.val.2) := rfl

/-- This is equality of the complete comparison arrows after their base transport. -/
theorem composite_realization : type_of% (Ordinary.pullbackRealization_comp
    (scale 2) (scale_smooth 2) (scale 3) (scale_smooth 3) line) :=
  Ordinary.pullbackRealization_comp (scale 2) (scale_smooth 2) (scale 3) (scale_smooth 3) line

def dimensionChanging := Ordinary.pullbackRealization (G := PUnit)
  SmoothBundlePullback.coordinate SmoothBundlePullback.coordinate_smooth

def reconstructedDimensionChanging := Ordinary.reconstructionPullback (G := PUnit)
  SmoothBundlePullback.coordinate SmoothBundlePullback.coordinate_smooth

def nonlinear (x : Space 1) : Space 2 := fun i => if i = 0 then x 0 else (x 0)^2

theorem nonlinear_smooth : ContMDiff (modelWithCorners 1) (modelWithCorners 2) ∞ nonlinear := by
  apply ContDiff.contMDiff
  apply contDiff_pi.mpr
  intro i
  by_cases h : i = 0
  · simpa [nonlinear, h] using (contDiff_apply ℝ (fun _ : Fin 1 => ℝ) 0)
  · simpa [nonlinear, h] using (contDiff_apply ℝ (fun _ : Fin 1 => ℝ) 0).pow 2

def target : Ordinary.WithTarget 1 2 PUnit (Space 1) (Space 2) where
  ordinary := line
  target := nonlinear
  smooth := nonlinear_smooth
  equivariant _ _ := rfl

theorem target_action_smooth (g : PUnit) :
    ContMDiff (modelWithCorners 2) (modelWithCorners 2) ∞ (fun x : Space 2 => g • x) := contMDiff_id

abbrev quotient := (Ordinary.WithTarget.realization target_action_smooth).obj target
abbrev recoveredTarget := Ordinary.WithTarget.reconstructed target_action_smooth quotient
local instance : MulAction PUnit recoveredTarget.ordinary.Total := recoveredTarget.ordinary.action

theorem recovered_target_value (x : Space 1) :
    recoveredTarget.target (Ordinary.WithTarget.unitTotal target_action_smooth target x) =
      nonlinear x := Ordinary.WithTarget.unit_target target_action_smooth target x

theorem recovered_target_square :
    recoveredTarget.target (Ordinary.WithTarget.unitTotal target_action_smooth target (fun _ => 2)) 1 = 4 := by
  rw [recovered_target_value]
  norm_num [nonlinear]

theorem recovered_target_nonconstant :
    recoveredTarget.target (Ordinary.WithTarget.unitTotal target_action_smooth target (fun _ => 2)) ≠
      recoveredTarget.target (Ordinary.WithTarget.unitTotal target_action_smooth target (fun _ => 0)) := by
  intro h
  have he := congrFun h 1
  rw [recovered_target_value, recovered_target_value] at he
  norm_num [nonlinear] at he

/-- A full independent target comparison, usable before forming any associated quotient. -/
theorem target_composite : type_of% (Ordinary.WithTarget.pullbackRealization_comp target_action_smooth
    (scale 2) (scale_smooth 2) (scale 3) (scale_smooth 3) target) :=
  Ordinary.WithTarget.pullbackRealization_comp target_action_smooth
    (scale 2) (scale_smooth 2) (scale 3) (scale_smooth 3) target

def targetDimensionChanging := Ordinary.WithTarget.reconstructionPullbackComponent target_action_smooth
  SmoothBundlePullback.coordinate SmoothBundlePullback.coordinate_smooth quotient

end BaseChange

namespace EmptyBase
open Orbifolds.QuarterTurn
local instance : TopologicalSpace C4 := ⊥
local instance : DiscreteTopology C4 := ⟨rfl⟩
local instance : ChartedSpace (Space 0) Empty := ChartedSpace.ofDiscreteTopology
local instance : IsManifold (modelWithCorners 0) ∞ Empty := IsManifold.of_discreteTopology _
abbrev torsor := SmoothTorsorReconstruction.EmptyBase.torsor

def recovery : Ordinary.realization.obj (Ordinary.reconstructed torsor) ≅ torsor :=
  Ordinary.recovery torsor

theorem recovered_total_empty : IsEmpty (Ordinary.reconstructed torsor).Total :=
  ⟨fun z => z.proj.elim⟩
end EmptyBase
end Examples.SmoothBundleClassification
