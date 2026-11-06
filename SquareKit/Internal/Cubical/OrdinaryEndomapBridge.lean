import SquareKit.Internal.Cubical.OrdinaryActionBridge
import SquareKit.Internal.Cubical.IdentityHomotopies

/-! Ordinary action for an endomap, in the section-map presentation used by beta. -/
noncomputable section
namespace SquareKit.Cubical.Contextual
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open CategoryTheory Presheaf
open SquareKit.Internal.DependentJudgments.Contextual.DerivedSemantics
universe u
variable (Base : LawfulFamily terminal.{u}) (Fiber : LawfulFamily (total Base.family))
variable {Γ : Presheaf.Context.{u}} (A : LawfulFamily Γ)
  (t : Term (reindex A.family (projection A.family))) (x y : Term A.family)
  (p : Term (normalizedIdentity A.family x y))

def ordinaryEndomapAction : Term (normalizedIdentity A.family (x.map (sectionMap t)) (y.map (sectionMap t))) :=
  ordinaryMappedAction Base Fiber A A t x y p

def ordinaryEndomapBridge : Term (normalizedIdentity
    (normalizedIdentity A.family (x.map (sectionMap t)) (y.map (sectionMap t)))
    (ordinaryEndomapAction Base Fiber A t x y p)
    (p.map (normalizedIdentityMap (sectionMap t) x y))) :=
  ordinaryMappedActionBridge Base Fiber A A t x y p

theorem ordinaryEndomapAction_heq : HEq (ULift.up.{u+1} (ordinaryEndomapAction Base Fiber A t x y p))
    (ordinaryApValue (model Base Fiber) A A ⟨t⟩ ⟨x⟩ ⟨y⟩ ⟨p⟩) :=
  ordinaryMappedAction_heq Base Fiber A A t x y p

end SquareKit.Cubical.Contextual
