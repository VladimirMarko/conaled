import SquareKit.Internal.Cubical.CocycleOrdinaryAction
import SquareKit.Internal.Cubical.CocycleSourceConjugation

/-! Conjugation coherence for actual ordinary action with a selected endpoint comparison. -/
noncomputable section
namespace SquareKit.Cubical.CategoryCocycles
open CategoryTheory Presheaf Contextual
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable (Base : LawfulFamily terminal.{0}) (Fiber : LawfulFamily (total Base.family))
variable (F : Filling (FirstIdentityFamily terminal.{0})) (hF : F.Lawful)
variable (t : Term (reindex (FirstIdentityFamily terminal.{0}) (projection (FirstIdentityFamily terminal))))
variable (β : Term (normalizedIdentity (reindex (FirstIdentityFamily terminal.{0}) (projection (FirstIdentityFamily terminal)))
  t (generic (FirstIdentityFamily terminal))))
variable (h : Term (SecondIdentityFamily terminal.{0}))

def ordinaryConjugationCube := sourceConjugationCube β h
  (cocycleOrdinaryAction Base Fiber F hF t h) (cocycleOrdinaryBridge Base Fiber F hF t h)

theorem ordinaryConjugation_start : (ordinaryConjugationCube Base Fiber F hF t β h).pullback (Over.map (face3 1 false)) =
    sourceActionSquare (cocycleOrdinaryAction Base Fiber F hF t h) :=
  sourceConjugationCube_start β h (cocycleOrdinaryAction Base Fiber F hF t h) (cocycleOrdinaryBridge Base Fiber F hF t h)

theorem ordinaryConjugation_finish : (ordinaryConjugationCube Base Fiber F hF t β h).pullback (Over.map (face3 1 true)) =
    secondSquare h :=
  sourceConjugationCube_finish β h (cocycleOrdinaryAction Base Fiber F hF t h) (cocycleOrdinaryBridge Base Fiber F hF t h)

theorem ordinaryConjugation_root (e : Bool) : (ordinaryConjugationCube Base Fiber F hF t β h).pullback (Over.map (face3 0 e)) =
    comparisonRootSquare β :=
  sourceConjugationCube_root β h (cocycleOrdinaryAction Base Fiber F hF t h) (cocycleOrdinaryBridge Base Fiber F hF t h) e

theorem ordinaryConjugation_side (e : Bool) : (ordinaryConjugationCube Base Fiber F hF t β h).pullback (Over.map (face3 2 e)) =
    zeroCocycle (Over (⟨2⟩ : Cube)) :=
  sourceConjugationCube_side β h (cocycleOrdinaryAction Base Fiber F hF t h) (cocycleOrdinaryBridge Base Fiber F hF t h) e

include β in
theorem ordinaryConjugation_observation : observeSquare (sourceActionSquare (cocycleOrdinaryAction Base Fiber F hF t h)) =
    secondObservation h :=
  sourceActionSquare_observation β h (cocycleOrdinaryAction Base Fiber F hF t h) (cocycleOrdinaryBridge Base Fiber F hF t h)

end SquareKit.Cubical.CategoryCocycles
