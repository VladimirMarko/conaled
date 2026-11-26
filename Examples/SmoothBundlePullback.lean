import SquareKit.SmoothBundlePullbackTargets
import Examples.SmoothBundleAtlas
import Examples.SmoothFiniteCover

/-! Ordinary fiber products on noncompact bases and a nontrivial covering. -/
noncomputable section
namespace Examples.SmoothBundlePullback
open SquareKit SquareKit.ManifoldRealization SquareKit.SmoothPrincipalBundle
open Examples.SmoothBundleAtlas
open scoped Manifold ContDiff

local notation "P" => realLineBundle
local notation "f" => scale 2
local notation "g" => scale 3
local notation "hf" => ContMDiff.continuous (scale_smooth 2)
local notation "hg" => ContMDiff.continuous (scale_smooth 3)

local instance : ChartedSpace (Space 1) (Pullback P f) := Pullback.chartedSpace (m := 1) P f hf
local instance : IsManifold (modelWithCorners 1) ∞ (Pullback P f) := Pullback.isManifold (m := 1) P f hf

abbrev scaleTwoBundle := Pullback.bundle (m := 1) P f hf

theorem scaleTwoBundle_projection (z : Pullback P f) : scaleTwoBundle.projection z = z.val.1 := rfl

theorem scale_two_pullback_snd_smooth :
    ContMDiff (modelWithCorners 1) (modelWithCorners 1) ∞ (Pullback.snd P f) :=
  Pullback.smooth_snd P f hf (scale_smooth 2)

local instance : ChartedSpace (Space 1) (Pullback scaleTwoBundle g) :=
  Pullback.chartedSpace (m := 1) scaleTwoBundle g hg
local instance : ChartedSpace (Space 1) (Pullback P (f ∘ g)) :=
  Pullback.chartedSpace (m := 1) P (f ∘ g) ((hf).comp hg)

/-- Successive nonidentity base changes flatten the actual nested subtype. -/
def scaleComposite := Pullback.compositionMap (m := 1) (k := 1) P f hf g hg

theorem scaleComposite_coordinates (z : Pullback scaleTwoBundle g) :
    (scaleComposite.toFun z).val = (z.val.1, z.val.2.val.2) := rfl

theorem scaleComposite_inverse :
    scaleComposite.comp (Pullback.compositionInverseMap P f hf g hg) =
      Map.ident (Pullback.bundle (m := 1) scaleTwoBundle g hg) :=
  Pullback.compositionMap_inverse P f hf g hg

example (a : Map P P) :
    scaleComposite.comp (Pullback.map P (f ∘ g) ((hf).comp hg) a) =
      (Pullback.map scaleTwoBundle g hg (Pullback.map P f hf a)).comp scaleComposite :=
  Pullback.compositionMap_natural P f hf g hg a

example :
    letI := Pullback.chartedSpace (m := 1) P (id : Space 1 → Space 1) continuous_id
    (Pullback.identityInverseMap P).comp (Pullback.identityMap P) = Map.ident P :=
  Pullback.identityInverseMap_inverse P

/-- The new base dimension need not equal the old total-space dimension. -/
def coordinate (x : Space 2) : Space 1 := fun _ => x 0

theorem coordinate_smooth : ContMDiff (modelWithCorners 2) (modelWithCorners 1) ∞ coordinate := by
  apply ContDiff.contMDiff
  exact contDiff_pi.mpr fun _ => contDiff_apply ℝ (fun _ : Fin 2 => ℝ) 0

local instance : ChartedSpace (Space 2) (Pullback P coordinate) := Pullback.chartedSpace (m := 2) P coordinate coordinate_smooth.continuous
local instance : IsManifold (modelWithCorners 2) ∞ (Pullback P coordinate) := Pullback.isManifold (m := 2) P coordinate coordinate_smooth.continuous

def planeBundle := Pullback.bundle (m := 2) P coordinate coordinate_smooth.continuous

example : ContMDiff (modelWithCorners 2) (modelWithCorners 1) ∞ (Pullback.snd P coordinate) :=
  Pullback.smooth_snd P coordinate coordinate_smooth.continuous coordinate_smooth

/-- The actual dimension-changing pullback realizes to the sheaf universal property. -/
example : CategoryTheory.IsPullback
    (ManifoldRealization.map (Pullback.snd P coordinate)
      (Pullback.smooth_snd P coordinate coordinate_smooth.continuous coordinate_smooth))
    (ManifoldRealization.map (Pullback.fst P coordinate)
      (Pullback.smooth_fst P coordinate coordinate_smooth.continuous))
    (ManifoldRealization.map (P).projection (P).smooth_projection)
    (ManifoldRealization.map coordinate coordinate_smooth) :=
  Pullback.realization_isPullback P coordinate coordinate_smooth

attribute [local instance] Examples.SmoothFiniteCover.SquareBundle.manifoldCharts
  Examples.SmoothFiniteCover.SquareBundle.manifoldSmooth
local notation "S" => Examples.SmoothFiniteCover.SquareBundle.bundle
local notation "sq" => Examples.SmoothFiniteCover.square
local notation "hsq" => ContMDiff.continuous Examples.SmoothFiniteCover.SquareBundle.square_smooth
local instance : ChartedSpace (Space 2) (Pullback S sq) := Pullback.chartedSpace (m := 2) S sq hsq
local instance : IsManifold (modelWithCorners 2) ∞ (Pullback S sq) := Pullback.isManifold (m := 2) S sq hsq

/-- Pull back the square covering along its own nonidentity projection. -/
def squarePullback := Pullback.bundle (m := 2) S sq hsq

example (z : Pullback S sq) : sq z.val.1 = sq z.val.2 := z.property

example : ContMDiff (modelWithCorners 2) (modelWithCorners 2) ∞ (Pullback.snd S sq) :=
  Pullback.smooth_snd S sq hsq Examples.SmoothFiniteCover.SquareBundle.square_smooth

end Examples.SmoothBundlePullback

namespace Examples.SmoothBundlePullback.TargetControl
open SquareKit SquareKit.ManifoldRealization SquareKit.SmoothPrincipalBundle
open Examples.SmoothFiniteCover.SquareBundle
open scoped Manifold ContDiff
local instance : TopologicalSpace G := ⊥
local instance : DiscreteTopology G := ⟨rfl⟩
local instance : ChartedSpace (Space 2) E := manifoldCharts
local instance : IsManifold (modelWithCorners 2) ∞ E := manifoldSmooth
local instance : MulAction G E := rootAction
local instance : ChartedSpace (Space 0) PUnit := ChartedSpace.ofDiscreteTopology
local instance : IsManifold (modelWithCorners 0) ∞ PUnit := IsManifold.of_discreteTopology _
local instance : MulAction G PUnit where
  smul _ x := x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

def comparison := Pullback.quotientComparison (d := 0) (M := PUnit)
  bundle bundle.projection bundle.smooth_projection (fun _ => contMDiff_id)
  (fun _ => PUnit.unit) contMDiff_const (fun _ _ => rfl)

end Examples.SmoothBundlePullback.TargetControl

namespace Examples.SmoothBundleAtlas
open SquareKit SquareKit.SmoothPrincipalBundle.Pullback
/-- The exact categorical equality for two nonidentity real-line base changes. -/
theorem scale_composite_coherence :
    let := chartedSpace (m := 1) realLineBundle (scale 2) (scale_smooth 2).continuous
    let := isManifold (m := 1) realLineBundle (scale 2) (scale_smooth 2).continuous
    let := chartedSpace (m := 1) (bundle (m := 1) realLineBundle (scale 2) (scale_smooth 2).continuous) (scale 3) (scale_smooth 3).continuous
    let := isManifold (m := 1) (bundle (m := 1) realLineBundle (scale 2) (scale_smooth 2).continuous) (scale 3) (scale_smooth 3).continuous
    let := chartedSpace (m := 1) realLineBundle ((scale 2) ∘ (scale 3)) ((scale_smooth 2).comp (scale_smooth 3)).continuous
    let := isManifold (m := 1) realLineBundle ((scale 2) ∘ (scale 3)) ((scale_smooth 2).comp (scale_smooth 3)).continuous
    ((realizationComparison (bundle (m := 1) realLineBundle (scale 2) (scale_smooth 2).continuous) (scale 3) (scale_smooth 3)).comp
      ((realizationComparison realLineBundle (scale 2) (scale_smooth 2)).reindex (ManifoldRealization.map (scale 3) (scale_smooth 3)))).comp
      (SheafTorsor.reindexCompositeCongr realLineBundle.realizedTorsor
        (ManifoldRealization.map (scale 2) (scale_smooth 2)) (ManifoldRealization.map (scale 3) (scale_smooth 3))
        (ManifoldRealization.map ((scale 2) ∘ (scale 3)) ((scale_smooth 2).comp (scale_smooth 3)))
        (ManifoldRealization.map_comp (scale 3) (scale 2) (scale_smooth 3) (scale_smooth 2)).symm) =
    (compositionMap (m := 1) (k := 1) realLineBundle (scale 2) (scale_smooth 2).continuous (scale 3) (scale_smooth 3).continuous).realizedArrow.comp
      (realizationComparison realLineBundle ((scale 2) ∘ (scale 3)) ((scale_smooth 2).comp (scale_smooth 3))) := realizationComparison_comp realLineBundle
  (scale 2) (scale_smooth 2) (scale 3) (scale_smooth 3)
end Examples.SmoothBundleAtlas
