import SquareKit.SmoothTorsorReconstructionTargets
import SquareKit.SmoothTorsorReconstructionSeparation
import Examples.SmoothFiniteCover

/-! Reconstruction of the square-cover torsor, represented restrictions of the
doubled-origin torsor, and finite and empty boundary cases. -/
noncomputable section
set_option autoImplicit false
namespace Examples.SmoothTorsorReconstruction
open CategoryTheory SquareKit SquareKit.ManifoldRealization SquareKit.SmoothManifoldAction
open SquareKit.SmoothOpenSite SquareKit.SmoothTorsorReconstruction
open scoped Manifold ContDiff

namespace Square
open SmoothFiniteCover.SquareBundle
local instance : TopologicalSpace G := ⊥
local instance : DiscreteTopology G := ⟨rfl⟩
local instance : ChartedSpace (Space 2) E := manifoldCharts
local instance : IsManifold (modelWithCorners 2) ∞ E := manifoldSmooth
local instance : MulAction G E := rootAction

abbrev torsor := bundle.realizedTorsor
local instance : ChartedSpace (Space 2) (Total torsor) := chartedSpace torsor
local instance : IsManifold (modelWithCorners 2) ∞ (Total torsor) := isManifold torsor

/-- Recovery is an isomorphism on the full smooth site. -/
def totalRecovery : object 2 (Total torsor) ≅ SplitSheaf.extension torsor.family :=
  reconstructedTotalIso torsor

/-- Full faithfulness recovers the original nontrivial ordinary square cover. -/
def comparison : SmoothPrincipalBundle.Map (SquareKit.SmoothTorsorReconstruction.bundle torsor) bundle :=
  SmoothPrincipalBundle.mapEquiv.symm (reconstructedArrow torsor)

theorem comparison_realized : comparison.realizedArrow = reconstructedArrow torsor :=
  SmoothPrincipalBundle.mapEquiv.apply_symm_apply _

def recoveredDiffeomorph : Total torsor ≃ₘ⟮modelWithCorners 2, modelWithCorners 2⟯ E :=
  comparison.diffeomorph

theorem comparison_projection (z : Total torsor) :
    SmoothFiniteCover.square (comparison.toFun z) = z.proj :=
  comparison.projection z

theorem no_continuous_section :
    ¬ ∃ s : E → Total torsor, Continuous s ∧
      Function.RightInverse s (SquareKit.SmoothTorsorReconstruction.bundle torsor).projection := by
  rintro ⟨s, hs, hp⟩
  apply SmoothFiniteCover.square_no_continuous_section
  refine ⟨comparison.toFun ∘ s, comparison.smooth.continuous.comp hs, ?_⟩
  intro b
  exact (comparison.projection (s b)).trans (hp b)

theorem total_hausdorff : T2Space (Total torsor) :=
  total_t2Space torsor

theorem secondCountableTopology_total : SecondCountableTopology (Total torsor) :=
  total_secondCountableTopology torsor

theorem totalRecovery_equivariant (U : SmoothPresentationSite.Siteᵒᵖ)
    (g : (locallyConstantGroup G).obj.obj U) (z : (object 2 (Total torsor)).obj.obj U) :
    totalRecovery.hom.hom.app U
      ((representation (SquareKit.SmoothTorsorReconstruction.bundle torsor).smooth_action).act U g z) =
      torsor.toAction.totalAct U g (totalRecovery.hom.hom.app U z) :=
  reconstructedTotalIso_equivariant torsor U g z

local instance : ChartedSpace (Space 0) PUnit := ChartedSpace.ofDiscreteTopology
local instance : IsManifold (modelWithCorners 0) ∞ PUnit := IsManifold.of_discreteTopology _
local instance : MulAction G PUnit where
  smul _ x := x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

/-- The independent target has dimension zero while the square cover has dimension two. -/
def quotient := bundle.realizedQuotient (fun _ => contMDiff_id (I := modelWithCorners 0))
  (fun _ => PUnit.unit) contMDiff_const (fun _ _ => rfl)

local instance : ChartedSpace (Space 2) (Total quotient.torsor) := chartedSpace quotient.torsor
local instance : IsManifold (modelWithCorners 2) ∞ (Total quotient.torsor) := isManifold quotient.torsor

def targetRecovery := reconstructedQuotientArrow (fun _ => contMDiff_id (I := modelWithCorners 0)) quotient

theorem targetRecovery_map :
    ManifoldRealization.map
      (reconstructedTarget (fun _ => contMDiff_id (I := modelWithCorners 0)) quotient)
      (reconstructedTarget_smooth (fun _ => contMDiff_id (I := modelWithCorners 0)) quotient) =
    (reconstructedTotalIso quotient.torsor).hom ≫ quotient.totalMap :=
  reconstructedTarget_map _ _

end Square

namespace DoubledOrigin
open Orbifolds.QuarterTurn Examples.SmoothCechDescent.Clutching
local instance : MulAction C4 (Space 1) := trivialAction _
local instance : TopologicalSpace C4 := ⊥
local instance : DiscreteTopology C4 := ⟨rfl⟩

/-- Each represented line chart supplies a base to which reconstruction applies. -/
def chartTorsor (i : Bool) := SheafTorsor.reindex
  (SmoothFiniteCover.DoubledOrigin.localObject i).torsor
  (principalIso SmoothClutching.line).hom

local instance (i : Bool) : ChartedSpace (Space 1) (Total (chartTorsor i)) :=
  chartedSpace (chartTorsor i)
local instance (i : Bool) : IsManifold (modelWithCorners 1) ∞ (Total (chartTorsor i)) :=
  isManifold (chartTorsor i)

def chartRecovery (i : Bool) :
    object 1 (Total (chartTorsor i)) ≅ SplitSheaf.extension (chartTorsor i).family :=
  reconstructedTotalIso (chartTorsor i)

def chartArrow (i : Bool) :
    SheafTorsor.Arrow
      (SquareKit.SmoothTorsorReconstruction.bundle (chartTorsor i)).realizedTorsor (chartTorsor i) :=
  reconstructedArrow (chartTorsor i)

/-- Local reconstruction does not give the doubled-origin torsor a global section. -/
theorem no_global_section :
    ¬ Nonempty (SplitSheaf.Tm (quarterTurnDatum.interpreted (smooth C4)).torsor.family) :=
  quarterTurn_no_section

theorem overlap_not_constant (g : C4) :
    SmoothClutching.transition C4 quarterTurn ≠
      constantSection SmoothClutching.puncturedSheaf g :=
  SmoothClutching.transition_not_constant C4 quarterTurn
    SmoothQuarterTurnArcs.quarterTurn_ne_one g

end DoubledOrigin

namespace Finite
open Orbifolds.QuarterTurn
local instance : TopologicalSpace C4 := ⊥
local instance : DiscreteTopology C4 := ⟨rfl⟩
local instance : ChartedSpace (Space 0) C4 := ChartedSpace.ofDiscreteTopology
local instance : ChartedSpace (Space 0) PUnit := ChartedSpace.ofDiscreteTopology
local instance : IsManifold (modelWithCorners 0) ∞ C4 := IsManifold.of_discreteTopology _
local instance : IsManifold (modelWithCorners 0) ∞ PUnit := IsManifold.of_discreteTopology _

abbrev torsor := SmoothFiniteCover.C4Bundle.bundle.realizedTorsor
local instance : ChartedSpace (Space 0) (Total torsor) := chartedSpace torsor
local instance : IsManifold (modelWithCorners 0) ∞ (Total torsor) := isManifold torsor

def comparison : SmoothPrincipalBundle.Map
    (SquareKit.SmoothTorsorReconstruction.bundle torsor) SmoothFiniteCover.C4Bundle.bundle :=
  SmoothPrincipalBundle.mapEquiv.symm (reconstructedArrow torsor)

def totalRecovery : object 0 (Total torsor) ≅ SplitSheaf.extension torsor.family :=
  reconstructedTotalIso torsor

theorem total_card : Nat.card (Total torsor) = 4 :=
  (Nat.card_congr comparison.diffeomorph.toEquiv).trans card_C4

theorem secondCountableTopology_total : SecondCountableTopology (Total torsor) :=
  total_secondCountableTopology torsor

end Finite

namespace EmptyBase
open Orbifolds.QuarterTurn
local instance : TopologicalSpace C4 := ⊥
local instance : DiscreteTopology C4 := ⟨rfl⟩
local instance : ChartedSpace (Space 0) Empty := ChartedSpace.ofDiscreteTopology
local instance : IsManifold (modelWithCorners 0) ∞ Empty := IsManifold.of_discreteTopology _

def torsor := SheafTorsor.trivial (locallyConstantGroup C4) (object 0 Empty)
local instance : ChartedSpace (Space 0) (Total torsor) := chartedSpace torsor
local instance : IsManifold (modelWithCorners 0) ∞ (Total torsor) := isManifold torsor

theorem total_empty : IsEmpty (Total torsor) := ⟨fun z => z.proj.elim⟩

def totalRecovery : object 0 (Total torsor) ≅ SplitSheaf.extension torsor.family :=
  reconstructedTotalIso torsor

def recoveryArrow :
    SheafTorsor.Arrow (SquareKit.SmoothTorsorReconstruction.bundle torsor).realizedTorsor torsor :=
  reconstructedArrow torsor

theorem total_hausdorff : T2Space (Total torsor) :=
  total_t2Space torsor

theorem secondCountableTopology_total : SecondCountableTopology (Total torsor) :=
  total_secondCountableTopology torsor

end EmptyBase
end Examples.SmoothTorsorReconstruction
