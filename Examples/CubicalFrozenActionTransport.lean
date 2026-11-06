import Examples.CubicalFrozenActionInputs
import SquareKit.Internal.Cubical.CocycleComparisonValues

/-! The selected transport and beta are pulled back from the original frozen context. -/
noncomputable section
namespace Examples.CubicalFrozenActionInputs
set_option maxHeartbeats 800000
open CategoryTheory SquareKit.Cubical SquareKit.Cubical.Presheaf
open SquareKit.Cubical.CategoryCocycles
open Examples.CubicalCocycleAssignment Examples.FrozenOrdinaryAction

/-- The same selected family, exposing its raw functor without expanding the frozen context. -/
def assignedLoopFamily : LawfulFamily terminal.{0} :=
  ⟨⟨FirstIdentityFamily terminal, assignedType.filling⟩, assignedType.lawful⟩

theorem assignedLoopFamily_eq : assignedLoopFamily = assignedType := rfl

def assignedTransport : Term (reindex (FirstIdentityFamily terminal.{0}) (projection (FirstIdentityFamily terminal))) :=
  (reindexedTransport cocycleModel cocycleBase cocycleRootedFamily ⟨assignInput⟩).down

private def rawBeta (Base : LawfulFamily terminal.{0}) (Fiber : LawfulFamily (total Base.family))
    (F : LawfulFamily terminal.{0})
    (t : (Contextual.model Base Fiber).Section ((Contextual.model Base Fiber).extend terminal F)
      ((Contextual.model Base Fiber).subTy F ((Contextual.model Base Fiber).weaken terminal F)))
    (b : (Contextual.model Base Fiber).Section ((Contextual.model Base Fiber).extend terminal F)
      (SquareKit.Internal.DependentJudgments.Contextual.DerivedSemantics.EndomapBetaType (Contextual.model Base Fiber) F t)) :
    Term (normalizedIdentity (reindex F.family (projection F.family)) t.down (generic F.family)) := b.down

def assignedBeta : Term (normalizedIdentity (reindex (FirstIdentityFamily terminal.{0}) (projection (FirstIdentityFamily terminal)))
    assignedTransport (generic (FirstIdentityFamily terminal))) :=
  rawBeta cocycleBase cocycleRootedFamily assignedType
    (reindexedTransport cocycleModel cocycleBase cocycleRootedFamily ⟨assignInput⟩)
    (reindexedBeta cocycleModel cocycleBase cocycleRootedFamily ⟨assignInput⟩)

end Examples.CubicalFrozenActionInputs
