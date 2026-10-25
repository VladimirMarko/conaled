import SquareKit.Internal.SierpinskiEquivalence
import SquareKit.Internal.GeometricCone

/-! Classification with a varying base leg retains the base transformation
alongside the generic-model map. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SquareKit.Internal.Sierpinski
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
universe v u vB uB
variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable {B : Type uB} [Category.{vB} B] [HasInitial B] [HasFiniteLimits B]
variable [HasStrictInitialObjects B]
variable {h h' : GeometricMorphism (Sheaf J (Type (max u v))) B}
variable {P Q : MonoOver (⊤_ (Sheaf J (Type (max u v))))}

/-- Transform both the base inverse image and the model carrier. -/
def classifiedTop (β : h ⟶ h') (q : P ⟶ Q) :
    (classified J h P).morphism ⟶ (classified J h' Q).morphism := by
  change h.inverseImage.mapArrow ⋙ ArrowPushout.interpretation P.obj.left ⟶
    h'.inverseImage.mapArrow ⋙ ArrowPushout.interpretation Q.obj.left
  exact whiskerRight ((Functor.mapArrowFunctor B (Sheaf J (Type (max u v)))).map β)
    (ArrowPushout.interpretation P.obj.left) ≫
    whiskerLeft h'.inverseImage.mapArrow (ArrowPushout.changeParameter P.obj.left q.hom.left)

omit [HasFiniteLimits B] [HasStrictInitialObjects B] in
/-- The resulting square retains the given, possibly noninvertible, base transformation. -/
theorem classifiedTop_over (β : h ⟶ h') (q : P ⟶ Q) :
    whiskerLeft (ArrowGeometry.projection B).inverseImage (classifiedTop J β q) ≫
      (classified J h' Q).comparison.hom = (classified J h P).comparison.hom ≫ β := by
  apply NatTrans.ext
  funext X
  apply pushout.hom_ext <;>
    simp [classifiedTop, classified, ArrowGeometry.projection, ArrowGeometry.diagonal,
      ArrowSheaf.ofSubterminal, ArrowSheaf.geometric, ArrowTransport.geometric,
      ArrowTransport.diagonalIso, ArrowPushout.interpretation, ArrowPushout.changeParameter,
      ArrowPushout.diagonalIso, ArrowPushout.diagonalObj, GeometricMorphism.comp,
      Category.assoc]
  ext U x
  rfl

universe vA uA
variable {A : Type uA} [Category.{vA} A]
variable (H : GeometricMorphism (Sheaf J (Type (max u v))) A ⥤
  GeometricMorphism (Sheaf J (Type (max u v))) B)

/-- Retain the varying base leg and its actual generic model. -/
def coneModels : GeometricMorphism.Cone H (ArrowGeometry.projection B) ⥤
    GeometricMorphism (Sheaf J (Type (max u v))) A ×
      MonoOver (⊤_ (Sheaf J (Type (max u v)))) where
  obj k := (k.base, interpretation.obj k.lift.morphism)
  map α := (α.base, interpretation.map α.top)
  map_id _ := rfl
  map_comp _ _ := rfl

instance : (coneModels J H).Faithful where
  map_injective {k l} α β e := by
    have eb : α.base = β.base := congrArg Prod.fst e
    apply GeometricMorphism.Cone.Hom.ext eb
    apply naturalTransformation_ext α.top β.top
    · intro X
      apply (cancel_mono (l.lift.comparison.hom.app X)).mp
      have ea := congrArg (fun η => η.app X) α.over
      have eb' := congrArg (fun η => η.app X) β.over
      rw [eb] at ea
      exact ea.trans eb'.symm
    · exact congrArg (fun f => f.hom.left) (congrArg Prod.snd e)

/-- Reconstruct a cone map from its base map and generic-model map. -/
def coneMap {k l : GeometricMorphism.Cone H (ArrowGeometry.projection B)}
    (β : k.base ⟶ l.base) (q : interpretation.obj k.lift.morphism ⟶
      interpretation.obj l.lift.morphism) : k ⟶ l where
  base := β
  top := (reconstructionIso J (H.obj k.base) k.lift).hom.transformation ≫
    classifiedTop J (H.map β) q ≫ (reconstructionIso J (H.obj l.base) l.lift).inv.transformation
  over := by
    change ((whiskerLeft (ArrowGeometry.projection B).inverseImage
      (reconstructionIso J (H.obj k.base) k.lift).hom.transformation ≫
      whiskerLeft (ArrowGeometry.projection B).inverseImage (classifiedTop J (H.map β) q)) ≫
      whiskerLeft (ArrowGeometry.projection B).inverseImage
        (reconstructionIso J (H.obj l.base) l.lift).inv.transformation) ≫
      l.lift.comparison.hom = _
    rw [Category.assoc, (reconstructionIso J (H.obj l.base) l.lift).inv.over,
      Category.assoc]
    dsimp only [classify, liftInterpretation, GeometricMorphism.Lift.forget, Functor.comp_obj]
    rw [classifiedTop_over, ← Category.assoc]
    have o := (reconstructionIso J (H.obj k.base) k.lift).hom.over
    dsimp only [classify, liftInterpretation, GeometricMorphism.Lift.forget, Functor.comp_obj] at o
    rw [o]

instance : (coneModels J H).Full where
  map_surjective {_k _l} f :=
    ⟨coneMap J H f.1 f.2, Prod.ext rfl (Subsingleton.elim _ _)⟩

instance : (coneModels J H).EssSurj where
  mem_essImage X := by
    let k : GeometricMorphism.Cone H (ArrowGeometry.projection B) :=
      ⟨X.1, classified J (H.obj X.1) X.2⟩
    let e := classifiedGenericIso J (H.obj X.1) X.2
    refine ⟨k, ⟨?_⟩⟩
    exact {
      hom := (𝟙 _, e.hom)
      inv := (𝟙 _, e.inv)
      hom_inv_id := Prod.ext (Category.id_comp _) e.hom_inv_id
      inv_hom_id := Prod.ext (Category.id_comp _) e.inv_hom_id }

instance : (coneModels J H).IsEquivalence where

/-- Varying-base cones are equivalent to base legs paired with actual subterminal models. -/
def coneEquivalence : GeometricMorphism.Cone H (ArrowGeometry.projection B) ≌
    GeometricMorphism (Sheaf J (Type (max u v))) A ×
      MonoOver (⊤_ (Sheaf J (Type (max u v)))) :=
  (coneModels J H).asEquivalence

end SquareKit.Internal.Sierpinski

