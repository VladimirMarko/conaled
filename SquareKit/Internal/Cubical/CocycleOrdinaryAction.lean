import SquareKit.Internal.Cubical.OrdinaryEndomapBridge
import SquareKit.Internal.Cubical.CocycleActionBridgeValues

/-! Ordinary action and its typed comparison in the cocycle loop presentation. -/
noncomputable section
namespace SquareKit.Cubical.CategoryCocycles
open CategoryTheory Presheaf Contextual
open SquareKit.Internal.DependentJudgments.Contextual.DerivedSemantics
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable (Base : LawfulFamily terminal.{0}) (Fiber : LawfulFamily (total Base.family))
variable {Γ : Presheaf.Context.{0}} (F : Filling (FirstIdentityFamily Γ)) (hF : F.Lawful)

def actionLoopFamily : LawfulFamily Γ := ⟨⟨FirstIdentityFamily Γ, F⟩, hF⟩

variable (t : Term (reindex (FirstIdentityFamily Γ) (projection (FirstIdentityFamily Γ))))
  (h : Term (SecondIdentityFamily Γ))

def cocycleOrdinaryAction : Term (LoopSquareFamily (mappedPoint t)) :=
  ordinaryEndomapAction Base Fiber (actionLoopFamily F hF) t
    (FirstIdentityPoint Γ) (FirstIdentityPoint Γ) h

def cocycleOrdinaryBridge : Term (normalizedIdentity (LoopSquareFamily (mappedPoint t))
    (cocycleOrdinaryAction Base Fiber F hF t h) (mappedHigher t h)) :=
  ordinaryEndomapBridge Base Fiber (actionLoopFamily F hF) t
    (FirstIdentityPoint Γ) (FirstIdentityPoint Γ) h

theorem cocycleOrdinaryAction_heq : HEq (ULift.up.{1} (cocycleOrdinaryAction Base Fiber F hF t h))
    (ordinaryApValue (model Base Fiber) (actionLoopFamily F hF) (actionLoopFamily F hF)
      ⟨t⟩ ⟨FirstIdentityPoint Γ⟩ ⟨FirstIdentityPoint Γ⟩ ⟨h⟩) :=
  ordinaryEndomapAction_heq Base Fiber (actionLoopFamily F hF) t
    (FirstIdentityPoint Γ) (FirstIdentityPoint Γ) h

end SquareKit.Cubical.CategoryCocycles
