import Examples.CubicalCocycleHigherAssignment
import Examples.FrozenMemoDisplayVariable
import Examples.CubicalFrozenMemo
import Examples.FrozenMemoPairReindex

/-! A complete assignment of the original frozen memo in the dependent cocycle model. -/
noncomputable section
namespace Examples.CubicalCocycleAssignment
open CategoryTheory SquareKit.Cubical SquareKit.Cubical.Presheaf
open SquareKit.Cubical.CategoryCocycles
open Examples.FrozenMemoStages

abbrev afterHomotopy := homotopyPoints cocycleStructuralModel cocycleBase cocycleRootedFamily
abbrev afterQ := qPoints cocycleStructuralModel cocycleBase cocycleRootedFamily

theorem q_at_assignment : reindex (qFamily cocycleStructuralModel cocycleBase cocycleRootedFamily).family assignHomotopy =
    firstIdentityFamily terminal.{0} :=
  normalizedIdentity_reindex afterHomotopy.family.family afterHomotopy.y.down afterHomotopy.z.down assignHomotopy

def assignedQ : Term (reindex (qFamily cocycleStructuralModel cocycleBase cocycleRootedFamily).family assignHomotopy) :=
  (normalizedIdentityRefl (zeroTerm terminal)).convert q_at_assignment.symm

def assignQ : terminal.{0} ⟶ afterQ.context := pair assignHomotopy assignedQ

abbrev firstPoint := Points.initial (M := cocycleStructuralModel) cocycleBase cocycleRootedFamily
abbrev twoPoints := firstPoint.addY

def fiberBaseMap : total afterQ.family.family ⟶ total cocycleBase.family :=
  (cocycleStructuralModel.lift afterHomotopy.family (cocycleStructuralModel.weaken afterHomotopy.context (qFamily cocycleStructuralModel cocycleBase cocycleRootedFamily))).down ≫
  (cocycleStructuralModel.lift parallelPoints.family (cocycleStructuralModel.weaken parallelPoints.context parallelPoints.identity)).down ≫
  (cocycleStructuralModel.lift onePath.family (cocycleStructuralModel.weaken onePath.context onePath.path)).down ≫
  (cocycleStructuralModel.lift points.family (cocycleStructuralModel.weaken points.context points.path)).down ≫
  (cocycleStructuralModel.lift twoPoints.family (cocycleStructuralModel.weaken twoPoints.context twoPoints.family)).down ≫
  (cocycleStructuralModel.lift firstPoint.family (cocycleStructuralModel.weaken firstPoint.context firstPoint.family)).down ≫
  (cocycleStructuralModel.lift cocycleBase (cocycleStructuralModel.weaken cocycleStructuralModel.empty cocycleBase)).down

def assignedFiberBaseMap : terminal.{0} ⟶ total cocycleBase.family :=
  assignQ ≫ (cocycleStructuralModel.sectionSub afterQ.family afterQ.x).down ≫ fiberBaseMap

theorem u_at_assignment : reindex (uFamily cocycleStructuralModel cocycleBase cocycleRootedFamily).family assignQ =
    firstIdentityFamily terminal.{0} := by
  exact normalizedIdentity_reindex
    (reindex cocycleBase.family (projection cocycleBase.family))
    ((zeroTerm terminal).reindex (projection cocycleBase.family))
    (generic cocycleBase.family) assignedFiberBaseMap

def assignedU : Term (reindex (uFamily cocycleStructuralModel cocycleBase cocycleRootedFamily).family assignQ) :=
  (normalizedIdentityRefl (zeroTerm terminal)).convert u_at_assignment.symm

def assignInput : terminal.{0} ⟶ inputContext cocycleStructuralModel cocycleBase cocycleRootedFamily := pair assignQ assignedU

/-- The semantic interpretation evaluates the actual source context and higher binder. -/
theorem sourceContext :
    type_of% (inputContext_eval cocycleModel cocycleBase cocycleRootedFamily) :=
  inputContext_eval cocycleModel cocycleBase cocycleRootedFamily

theorem sourceHomotopy :
    type_of% (selectedHomotopy_eval cocycleModel cocycleBase cocycleRootedFamily) :=
  selectedHomotopy_eval cocycleModel cocycleBase cocycleRootedFamily

/-- Both equations use the original frozen maps and retain their displayed variable. -/
def sourceSigmaHomotopy := sigmaHomotopy cocycleModel cocycleBase cocycleRootedFamily
def sourceTauHomotopy := tauHomotopy cocycleModel cocycleBase cocycleRootedFamily

/-- The generic client computes its selected certificate and dependent action using actual J. -/
def frozenClient := Examples.CubicalFrozenMemo.client cocycleBase cocycleRootedFamily
def frozenPair := Examples.CubicalFrozenMemo.selectedPair cocycleBase cocycleRootedFamily

end Examples.CubicalCocycleAssignment
