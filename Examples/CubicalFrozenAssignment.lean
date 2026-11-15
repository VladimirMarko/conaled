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

abbrev afterHomotopy := homotopyPoints CM cocycleBase cocycleRootedFamily
abbrev afterQ := qPoints CM cocycleBase cocycleRootedFamily

theorem q_at_assignment : reindex (qFamily CM cocycleBase cocycleRootedFamily).family assignHomotopy =
    FirstIdentityFamily terminal.{0} :=
  normalizedIdentity_reindex afterHomotopy.family.family afterHomotopy.y.down afterHomotopy.z.down assignHomotopy

def assignedQ : Term (reindex (qFamily CM cocycleBase cocycleRootedFamily).family assignHomotopy) :=
  (normalizedIdentityRefl (zeroTerm terminal)).convert q_at_assignment.symm

def assignQ : terminal.{0} ⟶ afterQ.context := pair assignHomotopy assignedQ

abbrev firstPoint := Points.initial (M := CM) cocycleBase cocycleRootedFamily
abbrev twoPoints := firstPoint.addY

def fiberBaseMap : total afterQ.family.family ⟶ total cocycleBase.family :=
  (CM.lift afterHomotopy.family (CM.weaken afterHomotopy.context (qFamily CM cocycleBase cocycleRootedFamily))).down ≫
  (CM.lift parallelPoints.family (CM.weaken parallelPoints.context parallelPoints.identity)).down ≫
  (CM.lift onePath.family (CM.weaken onePath.context onePath.path)).down ≫
  (CM.lift points.family (CM.weaken points.context points.path)).down ≫
  (CM.lift twoPoints.family (CM.weaken twoPoints.context twoPoints.family)).down ≫
  (CM.lift firstPoint.family (CM.weaken firstPoint.context firstPoint.family)).down ≫
  (CM.lift cocycleBase (CM.weaken CM.empty cocycleBase)).down

def assignedFiberBaseMap : terminal.{0} ⟶ total cocycleBase.family :=
  assignQ ≫ (CM.sectionSub afterQ.family afterQ.x).down ≫ fiberBaseMap

theorem u_at_assignment : reindex (uFamily CM cocycleBase cocycleRootedFamily).family assignQ =
    FirstIdentityFamily terminal.{0} := by
  exact normalizedIdentity_reindex
    (reindex cocycleBase.family (projection cocycleBase.family))
    ((zeroTerm terminal).reindex (projection cocycleBase.family))
    (generic cocycleBase.family) assignedFiberBaseMap

def assignedU : Term (reindex (uFamily CM cocycleBase cocycleRootedFamily).family assignQ) :=
  (normalizedIdentityRefl (zeroTerm terminal)).convert u_at_assignment.symm

def assignInput : terminal.{0} ⟶ inputContext CM cocycleBase cocycleRootedFamily := pair assignQ assignedU

/-- The semantic interpretation evaluates the actual source context and higher binder. -/
def sourceContext := inputContext_eval cocycleModel cocycleBase cocycleRootedFamily
def sourceHomotopy := selectedHomotopy_eval cocycleModel cocycleBase cocycleRootedFamily

/-- Both equations use the original frozen maps and retain their displayed variable. -/
def sourceSigmaHomotopy := sigmaHomotopy cocycleModel cocycleBase cocycleRootedFamily
def sourceTauHomotopy := tauHomotopy cocycleModel cocycleBase cocycleRootedFamily

/-- The generic client computes its selected certificate and dependent action using actual J. -/
def frozenClient := Examples.CubicalFrozenMemo.client cocycleBase cocycleRootedFamily
def frozenPair := Examples.CubicalFrozenMemo.selectedPair cocycleBase cocycleRootedFamily

end Examples.CubicalCocycleAssignment
