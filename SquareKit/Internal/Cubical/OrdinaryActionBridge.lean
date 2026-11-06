import SquareKit.Internal.Cubical.ContextualPointwiseActionValue

/-! The selected source action and its whole pointwise marked-identity map are joined by an actual identity. -/
noncomputable section
namespace SquareKit.Cubical.Contextual
open CategoryTheory Presheaf SquareKit.Internal.PathTransport.Typed
open SquareKit.Internal.DependentJudgments.Contextual.DerivedSemantics
set_option backward.isDefEq.respectTransparency false
universe u
variable (Base : LawfulFamily terminal.{u}) (Fiber : LawfulFamily (total Base.family))
local notation "M" => model Base Fiber
variable {Γ : Presheaf.Context.{u}} (A C : LawfulFamily Γ)
  (t : Term (reindex C.family (projection A.family))) (x y : Term A.family)
  (p : Term (normalizedIdentity A.family x y))

theorem ordinaryActionFamily_eq :
    ((M).identity C (ordinaryApply M A C ⟨t⟩ ⟨x⟩) (ordinaryApply M A C ⟨t⟩ ⟨y⟩)).family =
    normalizedIdentity C.family (x.map (functionMap A C t)) (y.map (functionMap A C t)) :=
  congrArg₂ (normalizedIdentity C.family) (ordinaryApply_down Base Fiber A C t x)
    (ordinaryApply_down Base Fiber A C t y)

def ordinaryMappedAction : Term (normalizedIdentity C.family
    (x.map (functionMap A C t)) (y.map (functionMap A C t))) :=
  (ordinaryApValue M A C ⟨t⟩ ⟨x⟩ ⟨y⟩ ⟨p⟩).down.convert (ordinaryActionFamily_eq Base Fiber A C t x y)

private theorem action_lift_heq {X Y : Type u} {a : X} {b : Y} (h : HEq a b) :
    HEq (ULift.up.{u+1} a) (ULift.up.{u+1} b) := by cases h; rfl

theorem ordinaryMappedAction_heq : HEq (ULift.up.{u+1} (ordinaryMappedAction Base Fiber A C t x y p))
    (ordinaryApValue M A C ⟨t⟩ ⟨x⟩ ⟨y⟩ ⟨p⟩) :=
  action_lift_heq (Term.convert_heq _ _)

private theorem identity_congr {Γ : Presheaf.Context.{u}} {A B : Family Γ} (e : A = B)
    {a b : Term A} {c d : Term B} (ha : HEq a c) (hb : HEq b d) :
    normalizedIdentity A a b = normalizedIdentity B c d := by cases e; cases ha; cases hb; rfl

theorem ordinaryActionBridgeFamily_eq :
    ((M).identity ((M).identity C (ordinaryApply M A C ⟨t⟩ ⟨x⟩) (ordinaryApply M A C ⟨t⟩ ⟨y⟩))
      (ordinaryApValue M A C ⟨t⟩ ⟨x⟩ ⟨y⟩ ⟨p⟩) (pointwiseApValue Base Fiber A C t x y p)).family =
    normalizedIdentity (normalizedIdentity C.family (x.map (functionMap A C t)) (y.map (functionMap A C t)))
      (ordinaryMappedAction Base Fiber A C t x y p) (p.map (normalizedIdentityMap (functionMap A C t) x y)) :=
  identity_congr (ordinaryActionFamily_eq Base Fiber A C t x y)
    (Term.convert_heq _ _).symm (pointwiseApValue_map Base Fiber A C t x y p)

def ordinaryMappedActionBridge : Term
    (normalizedIdentity (normalizedIdentity C.family (x.map (functionMap A C t)) (y.map (functionMap A C t)))
      (ordinaryMappedAction Base Fiber A C t x y p) (p.map (normalizedIdentityMap (functionMap A C t) x y))) :=
  (ordinaryActionComparisonValue Base Fiber A C t x y p).down.convert
    (ordinaryActionBridgeFamily_eq Base Fiber A C t x y p)

end SquareKit.Cubical.Contextual
