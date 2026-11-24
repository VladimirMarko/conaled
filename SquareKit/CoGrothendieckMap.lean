import Mathlib.CategoryTheory.FiberedCategory.Grothendieck
import Mathlib.CategoryTheory.Bicategory.Modification.Pseudo

set_option autoImplicit false

/-! Total functors act on modifications, retaining their vertical components. -/
open CategoryTheory CategoryTheory.Functor Opposite Bicategory
open scoped Pseudofunctor.StrongTrans
namespace SquareKit.CoGrothendieckMap
open Pseudofunctor.CoGrothendieck
universe u v a b
variable {S : Type u} [Category.{v} S]
variable {F G : LocallyDiscrete Sᵒᵖ ⥤ᵖ Cat.{b,a}}
variable {α β : F ⟶ G}
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- Lift a modification using the target fibre inclusion, including its identity constraint. -/
def mapModification (m : α ⟶ β) : map α ⟶ map β where
  app x := (ι G x.base).map ((m.as.app ⟨op x.base⟩).toNatTrans.app x.fiber)
  naturality {x y} f := by
    apply Hom.ext _ _ (by simp)
    dsimp [Pseudofunctor.CoGrothendieck.map, ι]
    have hm := congrArg (fun k => k.toNatTrans.app y.fiber) (m.as.naturality f.base.op.toLoc)
    dsimp at hm
    simp [← Cat.Hom₂.comp_app, ← NatTrans.naturality_assoc,
      G.mapComp_id_left_inv_app, G.mapComp_id_right_inv_app,
      Strict.leftUnitor_eqToIso, Strict.rightUnitor_eqToIso,
      PrelaxFunctor.map₂_eqToHom]
    simp only [← Functor.map_comp_assoc,
      ← Cat.Hom.toNatIso_inv, ← Cat.Hom.toNatIso_hom, Iso.inv_hom_id_app]
    simp only [← Cat.Hom.toNatIso_hom] at hm
    rw [reassoc_of% hm]
    simp only [Functor.id_obj, Category.comp_id]

end SquareKit.CoGrothendieckMap
namespace SquareKit.CoGrothendieckMap
open Pseudofunctor.CoGrothendieck
universe u v a b
variable {S : Type u} [Category.{v} S]
variable (F G : LocallyDiscrete Sᵒᵖ ⥤ᵖ Cat.{b,a})
set_option backward.isDefEq.respectTransparency false

/-- CoGrothendieck total functors act functorially on all modifications. -/
def homFunctor : (F ⟶ G) ⥤ (Pseudofunctor.CoGrothendieck F ⥤ Pseudofunctor.CoGrothendieck G) where
  obj := Pseudofunctor.CoGrothendieck.map
  map := mapModification
  map_id α := by
    apply NatTrans.ext
    funext x
    exact (ι G x.base).map_id _
  map_comp m n := by
    apply NatTrans.ext
    funext x
    exact (ι G x.base).map_comp _ _
end SquareKit.CoGrothendieckMap

namespace SquareKit.CoGrothendieckMap
open Pseudofunctor.CoGrothendieck
universe u v a b
variable {S : Type u} [Category.{v} S]
variable {F G : LocallyDiscrete Sᵒᵖ ⥤ᵖ Cat.{b,a}}
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

@[simp] theorem mapModification_base {α β : F ⟶ G} (m : α ⟶ β)
    (x : Pseudofunctor.CoGrothendieck F) :
    ((mapModification m).app x).base = 𝟙 x.base := rfl

/-- Every total arrow factors through the canonical cartesian lift. -/
theorem vertical_cartesian {x y : Pseudofunctor.CoGrothendieck F} (f : x ⟶ y) :
    (ι F x.base).map f.fiber ≫ cartesianLift y.fiber f.base = f := by
  apply Hom.ext _ _ (by simp)
  dsimp [ι]
  simp [F.mapComp_id_right_inv_app, Strict.rightUnitor_eqToIso,
    PrelaxFunctor.map₂_eqToHom, ← Cat.Hom₂.comp_app]

/-- An invertible fibre component gives the cartesian universal property. -/
theorem cartesian_of_isIso_fiber {x y : Pseudofunctor.CoGrothendieck F}
    (f : x ⟶ y) [IsIso f.fiber] :
    (forget F).IsCartesian f.base f := by
  have hi : (forget F).IsHomLift (𝟙 x.base) ((ι F x.base).map f.fiber) :=
    CategoryTheory.Functor.IsHomLift.map (p := forget F) ((ι F x.base).map f.fiber)
  have hc : (forget F).IsCartesian f.base (cartesianLift y.fiber f.base) :=
    (isStronglyCartesian_homCartesianLift y.fiber f.base).isCartesian_of_isStronglyCartesian
  have : (forget F).IsHomLift (𝟙 x.base) ((ι F x.base).mapIso (asIso f.fiber)).hom := hi
  have h := CategoryTheory.Functor.IsCartesian.of_iso_comp (forget F) f.base
    (cartesianLift y.fiber f.base) ((ι F x.base).mapIso (asIso f.fiber))
  simpa only [Functor.mapIso_hom, asIso_hom, vertical_cartesian] using h

/-- A strong comparison sends each canonical cartesian lift to a cartesian arrow. -/
theorem map_cartesianLift (α : F ⟶ G) {R T : S} (a : F.obj ⟨op T⟩) (f : R ⟶ T) :
    (forget G).IsCartesian f ((Pseudofunctor.CoGrothendieck.map α).map (cartesianLift a f)) := by
  have : IsIso (((Pseudofunctor.CoGrothendieck.map α).map (cartesianLift a f)).fiber) := by
    change IsIso ((α.app ⟨op R⟩).toFunctor.map (𝟙 _) ≫
    (α.naturality f.op.toLoc).hom.toNatTrans.app a)
    rw [Functor.map_id, Category.id_comp]
    change IsIso ((Cat.Hom.toNatIso (α.naturality f.op.toLoc)).hom.app a)
    infer_instance
  exact cartesian_of_isIso_fiber (F := G) ((Pseudofunctor.CoGrothendieck.map α).map (cartesianLift a f))
end SquareKit.CoGrothendieckMap

namespace SquareKit.CoGrothendieckMap
open Pseudofunctor.CoGrothendieck CategoryTheory.Functor
universe u v a b
variable {S : Type u} [Category.{v} S]
variable {F G : LocallyDiscrete Sᵒᵖ ⥤ᵖ Cat.{b,a}}
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Strong naturality preserves arbitrary cartesian arrows, not only the selected lifts. -/
theorem map_cartesian (α : F ⟶ G) {x y : Pseudofunctor.CoGrothendieck F}
    (f : x ⟶ y) [(forget F).IsCartesian f.base f] :
    (forget G).IsCartesian f.base ((Pseudofunctor.CoGrothendieck.map α).map f) := by
  let T := Pseudofunctor.CoGrothendieck.map α
  have : (forget F).IsCartesian f.base (cartesianLift y.fiber f.base) :=
    (isStronglyCartesian_homCartesianLift y.fiber f.base).isCartesian_of_isStronglyCartesian
  let e := IsCartesian.domainUniqueUpToIso (forget F) f.base (cartesianLift y.fiber f.base) f
  have he : e.hom ≫ cartesianLift y.fiber f.base = f := IsCartesian.fac (forget F) f.base (cartesianLift y.fiber f.base) f
  have hb : e.hom.base = 𝟙 x.base := by
    simpa using (IsHomLift.fac' (forget F) (𝟙 x.base) e.hom)
  have : (forget G).IsHomLift (𝟙 x.base) (T.mapIso e).hom := by
    apply IsHomLift.of_fac _ _ _ rfl rfl
    simpa [T, Pseudofunctor.CoGrothendieck.map] using hb.symm
  have : (forget G).IsCartesian f.base (T.map (cartesianLift y.fiber f.base)) :=
    map_cartesianLift α y.fiber f.base
  have h := IsCartesian.of_iso_comp (forget G) f.base (T.map (cartesianLift y.fiber f.base))
    (T.mapIso e)
  simpa only [Functor.mapIso_hom, ← T.map_comp, he] using h
end SquareKit.CoGrothendieckMap

namespace SquareKit.CoGrothendieckMap
open Pseudofunctor.CoGrothendieck
universe u v a b
variable {S : Type u} [Category.{v} S]
variable {F : LocallyDiscrete Sᵒᵖ ⥤ᵖ Cat.{b,a}}
@[simp] theorem base_eqToHom {x y : Pseudofunctor.CoGrothendieck F} (h : x = y) :
    (eqToHom h).base = eqToHom (congrArg Pseudofunctor.CoGrothendieck.base h) := by
  subst h
  rfl
end SquareKit.CoGrothendieckMap
