import SquareKit.Internal.Cubical.CocycleRootedFamily
import Examples.FrozenMemoStageEvaluation

/-! Assign the concrete cocycle point and reflexive paths to the original frozen display. -/
noncomputable section
namespace Examples.CubicalCocycleAssignment
open CategoryTheory SquareKit.Cubical SquareKit.Cubical.Presheaf
open SquareKit.Cubical.CategoryCocycles
open Examples.FrozenMemoStages

abbrev CM := cocycleModel.toStructuralModel
abbrev points := ((Points.initial (M := CM) cocycleBase cocycleRootedFamily).addY).addZ
abbrev onePath := points.addP
abbrev parallelPoints := onePath.addParallel

def assignX : terminal.{0} ⟶ total cocycleBase.family := pair (𝟙 _) (zeroTerm terminal)
def assignY : terminal.{0} ⟶ (Points.initial (M := CM) cocycleBase cocycleRootedFamily).addY.context :=
  pair assignX (zeroTerm terminal)
def assignZ : terminal.{0} ⟶ points.context := pair assignY (zeroTerm terminal)

theorem path_at_assignment : reindex points.path.family assignZ =
    normalizedIdentity (cocycleFamily terminal.{0}) (zeroTerm terminal) (zeroTerm terminal) :=
  normalizedIdentity_reindex points.family.family points.x.down points.y.down assignZ

def assignedPath : Term (reindex points.path.family assignZ) :=
  (normalizedIdentityRefl (zeroTerm terminal)).convert path_at_assignment.symm

def assignP : terminal.{0} ⟶ onePath.context := pair assignZ assignedPath

theorem parallel_path_at_assignment : reindex onePath.path.family assignP =
    normalizedIdentity (cocycleFamily terminal.{0}) (zeroTerm terminal) (zeroTerm terminal) :=
  normalizedIdentity_reindex onePath.family.family onePath.x.down onePath.y.down assignP

def assignedParallelPath : Term (reindex onePath.path.family assignP) :=
  (normalizedIdentityRefl (zeroTerm terminal)).convert parallel_path_at_assignment.symm

def assignParallel : terminal.{0} ⟶ parallelPoints.context := pair assignP assignedParallelPath

end Examples.CubicalCocycleAssignment
