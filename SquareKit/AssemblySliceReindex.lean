import SquareKit.AssemblySliceLift

/-! Explicit assembly pullback functors and their unit/composition isomorphisms.
All pullbacks use the constructed P1 limit cones. -/

universe u
namespace Realizability.Assembly

/-- Pull a commuting triangle back, using P1's universal mediator. -/
def pullbackMap {A A' B C : Assembly.{u}} (p : Hom A B) (q : Hom A' B)
    (f : Hom C B) (k : Hom A A') (hk : k.comp q = p) :
    Hom (pullback f p) (pullback f q) :=
  pullbackLift f q (pullbackFst f p) ((pullbackSnd f p).comp k) (Hom.ext fun d =>
    d.property.trans (congrArg (fun h => h.toFun d.val.2) hk).symm)

/-- The identity-base pullback has no extra data. -/
def pullbackIdentity {A B : Assembly.{u}} (p : Hom A B) : Hom (pullback (Hom.id B) p) A :=
  pullbackSnd (Hom.id B) p

def pullbackIdentityInv {A B : Assembly.{u}} (p : Hom A B) : Hom A (pullback (Hom.id B) p) :=
  pullbackLift _ _ p (Hom.id A) (Hom.ext fun _ => rfl)

theorem pullbackIdentity_inverse {A B : Assembly.{u}} (p : Hom A B) :
    (pullbackIdentity p).comp (pullbackIdentityInv p) = Hom.id (pullback (Hom.id B) p) := by
  apply Hom.ext
  intro d
  exact Subtype.ext (Prod.ext d.property.symm rfl)

theorem pullbackIdentityInv_inverse {A B : Assembly.{u}} (p : Hom A B) :
    (pullbackIdentityInv p).comp (pullbackIdentity p) = Hom.id A := Hom.ext fun _ => rfl

/-- Introduce the intermediate base coordinate in an iterated pullback. -/
def pullbackAssoc {A B C D : Assembly.{u}} (p : Hom A B) (f : Hom C B) (g : Hom D C) :
    Hom (pullback (g.comp f) p) (pullback g (pullbackFst f p)) :=
  pullbackLift g (pullbackFst f p) (pullbackFst (g.comp f) p)
    (pullbackLift f p ((pullbackFst (g.comp f) p).comp g) (pullbackSnd (g.comp f) p)
      (pullback_square (g.comp f) p)) (Hom.ext fun _ => rfl)

/-- Remove the redundant intermediate coordinate. -/
def pullbackUnassoc {A B C D : Assembly.{u}} (p : Hom A B) (f : Hom C B) (g : Hom D C) :
    Hom (pullback g (pullbackFst f p)) (pullback (g.comp f) p) :=
  pullbackLift (g.comp f) p (pullbackFst g (pullbackFst f p))
    ((pullbackSnd g (pullbackFst f p)).comp (pullbackSnd f p))
    (Hom.ext fun d => (congrArg f.toFun d.property).trans d.val.2.property)

theorem pullbackAssoc_unassoc {A B C D : Assembly.{u}}
    (p : Hom A B) (f : Hom C B) (g : Hom D C) :
    (pullbackAssoc p f g).comp (pullbackUnassoc p f g) = Hom.id (pullback (g.comp f) p) :=
  Hom.ext fun _ => rfl

theorem pullbackUnassoc_assoc {A B C D : Assembly.{u}}
    (p : Hom A B) (f : Hom C B) (g : Hom D C) :
    (pullbackUnassoc p f g).comp (pullbackAssoc p f g) = Hom.id (pullback g (pullbackFst f p)) := by
  apply Hom.ext
  intro d
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · exact Subtype.ext (Prod.ext d.property rfl)

open CategoryTheory

/-- Computed using the explicit assembly pullback, with Mathlib Over objects
and arrows. -/
def assemblyPullbackFunctor {B C : Assembly.{u}} (f : Hom C B) : Over B ⥤ Over C where
  obj X := Over.mk (pullbackFst f X.hom)
  map k := Over.homMk (pullbackMap _ _ f k.left (Over.w k)) (Hom.ext fun _ => rfl)
  map_id _ := Over.OverMorphism.ext (Hom.ext fun _ => rfl)
  map_comp _ _ := Over.OverMorphism.ext (Hom.ext fun _ => rfl)

end Realizability.Assembly
