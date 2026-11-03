import SquareKit.Internal.SierpinskiVaryingBase

/-! The relative arrow classifier changes base by the pointwise geometric
morphism. Its universal property retains the full varying-base cone category. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SquareKit.Internal.Sierpinski
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
universe vG vD vB uG uD uB
variable {G : Type uG} {D : Type uD} {B : Type uB}
variable [Category.{vG} G] [Category.{vD} D] [Category.{vB} B]
variable [HasFiniteLimits G]
variable [HasInitial D] [HasFiniteLimits D] [HasStrictInitialObjects D]
variable [HasInitial B] [HasFiniteLimits B] [HasStrictInitialObjects B]
variable (b : GeometricMorphism D B)

/-- Postcompose a lift around the actual arrow base-change square. -/
def post {h : GeometricMorphism G D}
    (k : GeometricMorphism.Lift h (ArrowGeometry.projection D)) :
    GeometricMorphism.Lift (h.comp b) (ArrowGeometry.projection B) where
  morphism := k.morphism.comp (ArrowTransport.geometric b)
  comparison :=
    (Functor.associator (ArrowGeometry.diagonal B) b.inverseImage.mapArrow k.morphism.inverseImage).symm ≪≫
    isoWhiskerRight (ArrowTransport.diagonalIso b.inverseImage) k.morphism.inverseImage ≪≫
    Functor.associator b.inverseImage (ArrowGeometry.diagonal D) k.morphism.inverseImage ≪≫
    isoWhiskerLeft b.inverseImage k.comparison

/-- Both geometric legs and all their compatible transformations are retained. -/
def coneBaseChange :
    GeometricMorphism.Cone (𝟭 (GeometricMorphism G D)) (ArrowGeometry.projection D) ⥤
    GeometricMorphism.Cone (GeometricMorphism.postcompose (F := G) b) (ArrowGeometry.projection B) where
  obj k := ⟨k.base, post b k.lift⟩
  map {k l} α := {
    base := α.base
    top := whiskerLeft b.inverseImage.mapArrow α.top
    over := by
      apply NatTrans.ext
      funext X
      have ho := congrArg (fun η => η.app (b.inverseImage.obj X)) α.over
      dsimp [post, ArrowGeometry.projection, ArrowTransport.geometric,
        GeometricMorphism.comp, GeometricMorphism.postcompose]
      simp only [Category.id_comp, Category.assoc]
      rw [← α.top.naturality_assoc]
      exact congrArg (k.lift.morphism.inverseImage.map
        ((ArrowTransport.diagonalIso b.inverseImage).hom.app X) ≫ ·) ho }
  map_id _ := GeometricMorphism.Cone.Hom.ext rfl rfl
  map_comp _ _ := GeometricMorphism.Cone.Hom.ext rfl rfl

/-- The generic carrier is preserved by base change using initial/terminal comparisons. -/
def postGeneric {h : GeometricMorphism G D}
    (k : GeometricMorphism.Lift h (ArrowGeometry.projection D)) :
    interpretation.obj (post b k).morphism ≅ interpretation.obj k.morphism :=
  MonoOver.isoMk (k.morphism.inverseImage.mapIso (genericImageIso b)) (terminal.hom_ext _ _)

end SquareKit.Internal.Sierpinski

namespace SquareKit.Internal.Sierpinski
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
universe v u vD vB uD uB
variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable {D : Type uD} {B : Type uB} [Category.{vD} D] [Category.{vB} B]
variable [HasInitial D] [HasFiniteLimits D] [HasStrictInitialObjects D]
variable [HasInitial B] [HasFiniteLimits B] [HasStrictInitialObjects B]
variable (b : GeometricMorphism D B)

/-- Base change preserves the varying base leg and its model, naturally on both maps. -/
def coneBaseChangeModels :
    coneBaseChange (G := Sheaf J (Type (max u v))) b ⋙
      coneModels J (GeometricMorphism.postcompose b) ≅
    coneModels J (𝟭 (GeometricMorphism (Sheaf J (Type (max u v))) D)) :=
  NatIso.ofComponents (fun k => {
    hom := (𝟙 _, (postGeneric b k.lift).hom)
    inv := (𝟙 _, (postGeneric b k.lift).inv)
    hom_inv_id := Prod.ext (Category.id_comp _) (postGeneric b k.lift).hom_inv_id
    inv_hom_id := Prod.ext (Category.id_comp _) (postGeneric b k.lift).inv_hom_id }) (by
      intro k l α
      exact Prod.ext ((Category.comp_id _).trans (Category.id_comp _).symm) (Subsingleton.elim _ _))

instance : (coneBaseChange (G := Sheaf J (Type (max u v))) b).IsEquivalence := by
  let : (coneBaseChange (G := Sheaf J (Type (max u v))) b ⋙
      coneModels J (GeometricMorphism.postcompose b)).IsEquivalence :=
    Functor.isEquivalence_of_iso (coneBaseChangeModels J b).symm
  exact Functor.isEquivalence_of_comp_right _ (coneModels J (GeometricMorphism.postcompose b))

/-- The actual arrow base-change square is a pseudopullback on every represented sheaf source. -/
def pseudopullback :
    GeometricMorphism (Sheaf J (Type (max u v))) (Arrow D) ≌
    GeometricMorphism.Cone (GeometricMorphism.postcompose (F := Sheaf J (Type (max u v))) b) (ArrowGeometry.projection B) :=
  (GeometricMorphism.canonicalConeEquivalence (ArrowGeometry.projection D)).trans
    (coneBaseChange (G := Sheaf J (Type (max u v))) b).asEquivalence

end SquareKit.Internal.Sierpinski
