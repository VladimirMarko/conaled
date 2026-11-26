import SquareKit.SmoothBundleMapsRealization
import SquareKit.SmoothBundleRightAction
import SquareKit.SmoothBundleTargetMaps
import Examples.SmoothFiniteCover

/-! Ordinary bundle maps retain nonidentity automorphisms. -/
noncomputable section
namespace Examples.SmoothBundleMorphisms
open SquareKit SquareKit.ManifoldRealization SquareKit.SmoothPrincipalBundle
open Orbifolds.QuarterTurn
open scoped Manifold ContDiff
local instance : TopologicalSpace C4 := ⊥
local instance : DiscreteTopology C4 := ⟨rfl⟩
local instance : ChartedSpace (Space 0) C4 := ChartedSpace.ofDiscreteTopology
local instance : ChartedSpace (Space 0) PUnit := ChartedSpace.ofDiscreteTopology
local instance : IsManifold (modelWithCorners 0) ∞ C4 := IsManifold.of_discreteTopology _
local instance : IsManifold (modelWithCorners 0) ∞ PUnit := IsManifold.of_discreteTopology _

def rotation (g : C4) : Map SmoothFiniteCover.C4Bundle.bundle SmoothFiniteCover.C4Bundle.bundle where
  toFun e := e * g
  smooth := contMDiff_of_discreteTopology
  projection _ := rfl
  equivariant a e := mul_assoc a e g

theorem rotation_bijective (g : C4) : Function.Bijective (rotation g).toFun :=
  (rotation g).bijective

theorem rotation_nonidentity {g : C4} (hg : g ≠ 1) :
    rotation g ≠ Map.ident SmoothFiniteCover.C4Bundle.bundle := by
  intro h
  have he := congrArg (fun f => f.toFun 1) h
  exact hg (by simpa [rotation, Map.ident] using he)

theorem rotation_comp (g h : C4) : (rotation g).comp (rotation h) = rotation (g*h) := by
  apply Map.ext
  funext e
  exact mul_assoc e g h

theorem rotation_roundtrip (g : C4) :
    RealizedArrow.ordinaryMap (rotation g).realizedArrow = rotation g :=
  (rotation g).ordinary_realized

theorem rotation_smooth_inverse (g e : C4) :
    (rotation g).diffeomorph.symm ((rotation g).diffeomorph e) = e :=
  (rotation g).diffeomorph.left_inv e

end Examples.SmoothBundleMorphisms

namespace Examples.SmoothBundleMorphisms.RightConvention
open SquareKit SquareKit.ManifoldRealization SquareKit.SmoothPrincipalBundle MulOpposite
open scoped Manifold ContDiff
abbrev S3 := Equiv.Perm (Fin 3)
local instance : TopologicalSpace S3 := ⊥
local instance : DiscreteTopology S3 := ⟨rfl⟩
local instance : ChartedSpace (Space 0) S3 := ChartedSpace.ofDiscreteTopology
local instance : ChartedSpace (Space 0) PUnit := ChartedSpace.ofDiscreteTopology
local instance : IsManifold (modelWithCorners 0) ∞ S3 := IsManifold.of_discreteTopology _
local instance : IsManifold (modelWithCorners 0) ∞ PUnit := IsManifold.of_discreteTopology _

def sheet (g : S3ᵐᵒᵖ) : OpenPartialHomeomorph S3 PUnit where
  toFun _ := PUnit.unit
  invFun _ := g.unop
  source := {g.unop}
  target := Set.univ
  map_source' _ _ := Set.mem_univ _
  map_target' _ _ := Set.mem_singleton _
  left_inv' _ h := h.symm
  right_inv' _ _ := Subsingleton.elim _ _
  open_source := isOpen_discrete _
  open_target := isOpen_univ
  continuousOn_toFun := continuousOn_const
  continuousOn_invFun := continuousOn_const

def rightBundle : RightBundle (n := 0) (G := S3) (B := PUnit) (E := S3) where
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
    sheets e _ := ⟨op e,rfl,fun _ hg => unop_injective hg.symm⟩
    equivariant _ _ _ _ := rfl },Set.mem_univ _⟩

/-- Left translations are maps of the conventional regular right bundle. -/
def translation (g : S3) : Map rightBundle rightBundle where
  toFun e := g * e
  smooth := contMDiff_of_discreteTopology
  projection _ := rfl
  equivariant a e := (mul_assoc g e a.unop).symm

def convertedTranslation (g : S3) :=
  Map.changeGroupEquiv (MulEquiv.inv' S3) (translation g)

abbrev a : S3 := Equiv.swap 0 1
abbrev b : S3 := Equiv.swap 1 2

theorem inverse_action_order :
    @SMul.smul S3 S3 (inverseAction (G := S3) (E := S3)).toSMul (a*b) 1 = b*a := by
  rw [inverseAction_regular]
  simp [a, b, mul_inv_rev]

theorem inverse_action_not_wrong_order :
    @SMul.smul S3 S3 (inverseAction (G := S3) (E := S3)).toSMul (a*b) 1 ≠ a*b := by
  rw [inverse_action_order]
  intro h
  have he := congrArg (fun p : S3 => p 0) h
  norm_num [a,b,Equiv.Perm.mul_apply,Equiv.swap_apply_def] at he

theorem convertedTranslation_value (g e : S3) :
    letI := inverseAction (G := S3) (E := S3)
    (convertedTranslation g).toFun e = g*e := rfl

end Examples.SmoothBundleMorphisms.RightConvention

namespace Examples.SmoothBundleMorphisms.Targets
open SquareKit SquareKit.ManifoldRealization SquareKit.SmoothPrincipalBundle
open Orbifolds.QuarterTurn
open scoped Manifold ContDiff
local instance : TopologicalSpace C4 := ⊥
local instance : DiscreteTopology C4 := ⟨rfl⟩
local instance : ChartedSpace (Space 0) C4 := ChartedSpace.ofDiscreteTopology
local instance : ChartedSpace (Space 0) PUnit := ChartedSpace.ofDiscreteTopology
local instance : IsManifold (modelWithCorners 0) ∞ C4 := IsManifold.of_discreteTopology _
local instance : IsManifold (modelWithCorners 0) ∞ PUnit := IsManifold.of_discreteTopology _
local instance : MulAction C4 PUnit where
  smul _ x := x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

def rotation (g : C4) : TargetMap SmoothFiniteCover.C4Bundle.bundle
    SmoothFiniteCover.C4Bundle.bundle (fun _ => PUnit.unit) (fun _ => PUnit.unit) where
  toMap := SmoothBundleMorphisms.rotation g
  target _ := rfl

def comparison := targetMapEquiv (d := 0) (M := PUnit)
  (P := SmoothFiniteCover.C4Bundle.bundle) (Q := SmoothFiniteCover.C4Bundle.bundle)
  (F := fun _ => PUnit.unit) (F' := fun _ => PUnit.unit)
  (fun _ => contMDiff_id) contMDiff_const contMDiff_const
  (fun _ _ => rfl) (fun _ _ => rfl)

def arrow (g : C4) := comparison (rotation g)

theorem roundtrip (g : C4) : comparison.symm (arrow g) = rotation g :=
  comparison.symm_apply_apply _

theorem arrow_injective : Function.Injective arrow := by
  intro g h he
  have hf := comparison.injective he
  have hv := congrArg (fun f => f.toFun 1) hf
  simpa [rotation, SmoothBundleMorphisms.rotation] using hv

/-- The original selected chart presentation retains every ordinary automorphism. -/
def chartComparison := targetMapChartEquiv (d := 0) (M := PUnit)
  (P := SmoothFiniteCover.C4Bundle.bundle) (Q := SmoothFiniteCover.C4Bundle.bundle)
  (F := fun _ => PUnit.unit) (F' := fun _ => PUnit.unit)
  (fun _ => contMDiff_id) contMDiff_const contMDiff_const
  (fun _ _ => rfl) (fun _ _ => rfl) SmoothFiniteCover.C4Bundle.bundle.baseCharts

theorem chart_roundtrip (g : C4) :
    chartComparison.symm (chartComparison (rotation g)) = rotation g :=
  chartComparison.symm_apply_apply _

end Examples.SmoothBundleMorphisms.Targets

namespace Examples.SmoothBundleMorphisms.Square
open SquareKit SquareKit.ManifoldRealization SquareKit.SmoothPrincipalBundle
open SmoothFiniteCover.SquareBundle
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

/-- Deck transformations of the nontrivial Hausdorff square cover. -/
def deck (g : G) : TargetMap bundle bundle (fun _ => PUnit.unit) (fun _ => PUnit.unit) where
  toFun x := g • x
  smooth := action_smooth g
  projection := invariant g
  equivariant a x := by rw [smul_smul, smul_smul, mul_comm g a]
  target _ := rfl

/-- Here the total space has dimension two and the independent target has dimension zero. -/
def comparison := targetMapEquiv (d := 0) (M := PUnit) (P := bundle) (Q := bundle)
  (F := fun _ => PUnit.unit) (F' := fun _ => PUnit.unit)
  (fun _ => contMDiff_id) contMDiff_const contMDiff_const
  (fun _ _ => rfl) (fun _ _ => rfl)

def arrow (g : G) := comparison (deck g)

theorem roundtrip (g : G) : comparison.symm (arrow g) = deck g :=
  comparison.symm_apply_apply _

theorem arrow_injective : Function.Injective arrow := by
  intro g h he
  have hf := comparison.injective he
  exact bundle.action_free g h (⟨1, one_ne_zero⟩ : E)
    (congrArg (fun f => f.toFun (⟨1, one_ne_zero⟩ : E)) hf)

example : T2Space E := inferInstance

theorem no_section : ¬ Nonempty (SplitSheaf.Tm bundle.descendedObject.torsor.family) :=
  no_sheaf_section

end Examples.SmoothBundleMorphisms.Square

section DoubledOrigin
attribute [local instance] Examples.SmoothCechDescent.Clutching.trivialAction
local instance : TopologicalSpace Orbifolds.QuarterTurn.C4 := ⊥
local instance : DiscreteTopology Orbifolds.QuarterTurn.C4 := ⟨rfl⟩

/-- The earlier doubled-origin torsor still has no global section. -/
example : ¬ Nonempty (SquareKit.SplitSheaf.Tm
    (Examples.SmoothCechDescent.Clutching.quarterTurnDatum.interpreted
      (Examples.SmoothCechDescent.Clutching.smooth Orbifolds.QuarterTurn.C4)).torsor.family) :=
  Examples.SmoothCechDescent.Clutching.quarterTurn_no_section

end DoubledOrigin
