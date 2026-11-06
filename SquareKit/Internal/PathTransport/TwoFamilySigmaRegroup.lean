import SquareKit.Internal.PathTransport.TwoFamilySigmaFamily
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000
universe u v w uΓ vΓ wΓ uB vB wB
variable {Γ : Type uΓ} [Bicategory.{wΓ,vΓ} Γ] [Bicategory.Strict Γ]
variable (F : Family.{uΓ,vΓ,wΓ,u,v,w} Γ)
variable (B : Family.{max uΓ u,max vΓ v,max wΓ w,uB,vB,wB} (Total F))
def sigmaRegroupObj (x : Total (sigmaFamily F B)) : Total B :=
  ⟨⟨x.base,x.fiber.base⟩,x.fiber.fiber⟩
def sigmaUngroupObj (x : Total B) : Total (sigmaFamily F B) :=
  ⟨x.base.base,⟨x.base.fiber,x.fiber⟩⟩
@[simp] theorem sigmaRegroupObj_ungroup (x : Total B) :
    sigmaRegroupObj F B (sigmaUngroupObj F B x) = x := rfl
@[simp] theorem sigmaUngroupObj_regroup (x : Total (sigmaFamily F B)) :
    sigmaUngroupObj F B (sigmaRegroupObj F B x) = x := rfl

def sigmaRegroupBase {x y : Total (sigmaFamily F B)} (p : x ⟶ y) :
    (sigmaRegroupObj F B x).base ⟶ (sigmaRegroupObj F B y).base :=
  ⟨p.base,p.fiber.base⟩

theorem sigmaRegroupBoundary {x y : Total (sigmaFamily F B)}
    (f : x.base ⟶ y.base) (u : (F.map f).obj x.fiber.base ⟶ y.fiber.base) :
    (B.map (show (sigmaRegroupObj F B x).base ⟶ (sigmaRegroupObj F B y).base from
      ⟨f,u⟩)).obj x.fiber.fiber =
      ((fiberRestriction F y.base B).map u).obj
        ((sigmaMap F B f).obj x.fiber).fiber := by
  have h := congrArg (fun H => H.obj x.fiber.fiber)
    (B.map_comp (cartesianLift F f x.fiber.base)
      ((fiberInclusion F y.base).map u))
  have e := cartesianLift_factorization F (x := (sigmaRegroupObj F B x).base)
    (y := (sigmaRegroupObj F B y).base) ⟨f,u⟩
  exact (congrArg (fun k => (B.map k).obj x.fiber.fiber) e).symm.trans h

def sigmaRegroupMap {x y : Total (sigmaFamily F B)} (p : x ⟶ y) :
    sigmaRegroupObj F B x ⟶ sigmaRegroupObj F B y :=
  ⟨sigmaRegroupBase F B p,eqToHom (sigmaRegroupBoundary F B p.base p.fiber.base) ≫ p.fiber.fiber⟩

def sigmaUngroupMap {x y : Total B} (p : x ⟶ y) :
    sigmaUngroupObj F B x ⟶ sigmaUngroupObj F B y :=
  ⟨p.base.base,⟨p.base.fiber,eqToHom (sigmaRegroupBoundary F B
    (x := sigmaUngroupObj F B x) (y := sigmaUngroupObj F B y)
    p.base.base p.base.fiber).symm ≫ p.fiber⟩⟩

@[simp] theorem sigmaRegroupMap_ungroup {x y : Total B} (p : x ⟶ y) :
    sigmaRegroupMap F B (sigmaUngroupMap F B p) = p := by
  rcases p with ⟨⟨f,u⟩,v⟩
  apply Pseudofunctor.CoGrothendieck.ext
  · rfl
  · simp [sigmaRegroupMap, sigmaUngroupMap]

@[simp] theorem sigmaUngroupMap_regroup {x y : Total (sigmaFamily F B)} (p : x ⟶ y) :
    sigmaUngroupMap F B (sigmaRegroupMap F B p) = p := by
  rcases p with ⟨f,⟨u,v⟩⟩
  apply Pseudofunctor.CoGrothendieck.ext
  · rfl
  · apply heq_of_eq
    apply Pseudofunctor.CoGrothendieck.ext
    · rfl
    · simp [sigmaRegroupMap, sigmaUngroupMap]


theorem sigmaRegroupMap_fiber_heq {x y : Total (sigmaFamily F B)} (p : x ⟶ y) :
    HEq (sigmaRegroupMap F B p).fiber p.fiber.fiber :=
  eqToHom_comp_heq _ _

theorem sigmaUngroupMap_fiber_heq {x y : Total B} (p : x ⟶ y) :
    HEq (sigmaUngroupMap F B p).fiber.fiber p.fiber :=
  eqToHom_comp_heq _ _

/-- Reassociation of dependent pair objects has an exact inverse. -/
def sigmaRegroupObjectEquiv : Total (sigmaFamily F B) ≃ Total B where
  toFun := sigmaRegroupObj F B
  invFun := sigmaUngroupObj F B
  left_inv := sigmaUngroupObj_regroup F B
  right_inv := sigmaRegroupObj_ungroup F B

/-- Reassociation of arrows retains both dependent arrow entries. -/
def sigmaRegroupArrowEquiv (x y : Total (sigmaFamily F B)) :
    (x ⟶ y) ≃ (sigmaRegroupObj F B x ⟶ sigmaRegroupObj F B y) where
  toFun := sigmaRegroupMap F B
  invFun := sigmaUngroupMap F B
  left_inv := sigmaUngroupMap_regroup F B
  right_inv := sigmaRegroupMap_ungroup F B

end SquareKit.Internal.PathTransport.TwoFamily
