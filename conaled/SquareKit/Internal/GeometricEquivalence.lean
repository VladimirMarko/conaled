import SquareKit.Internal.GeometricSlice

/-! Equivalences of target categories transport full categories of geometric
morphisms. The construction retains all inverse-image transformations. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SquareKit.Internal.GeometricMorphism
open CategoryTheory CategoryTheory.Functor
universe v₁ v₂ v₃ u₁ u₂ u₃
variable {F : Type u₁} {B : Type u₂} {G : Type u₃}
variable [Category.{v₁} F] [Category.{v₂} B] [Category.{v₃} G]

/-- An inverse-image natural isomorphism is a geometric isomorphism. -/
def isoOfInverseImage {f g : GeometricMorphism F B} (e : f.inverseImage ≅ g.inverseImage) : f ≅ g where
  hom := e.hom
  inv := e.inv
  hom_inv_id := e.hom_inv_id
  inv_hom_id := e.inv_hom_id

/-- Equivalent targets have equivalent full geometric hom categories. -/
def postcomposeEquivalence (e : B ≌ F) : GeometricMorphism G F ≌ GeometricMorphism G B where
  functor := postcompose (ofEquivalence e)
  inverse := postcompose (ofEquivalence e.symm)
  unitIso := NatIso.ofComponents (fun k => isoOfInverseImage
    ((Functor.leftUnitor k.inverseImage).symm ≪≫ isoWhiskerRight e.counitIso.symm k.inverseImage ≪≫
      Functor.associator _ _ _)) (by
        intro k l α
        apply NatTrans.ext
        funext X
        change α.app X ≫ (𝟙 _ ≫ l.inverseImage.map (e.counitIso.inv.app X) ≫ 𝟙 _) =
          (𝟙 _ ≫ k.inverseImage.map (e.counitIso.inv.app X) ≫ 𝟙 _) ≫ α.app (e.functor.obj (e.inverse.obj X))
        simpa only [Category.id_comp, Category.comp_id, postcompose, whiskerLeft_app, Functor.id_obj, Functor.comp_obj] using (α.naturality (e.counitIso.inv.app X)).symm)
  counitIso := NatIso.ofComponents (fun k => isoOfInverseImage
    ((Functor.associator _ _ _).symm ≪≫ isoWhiskerRight e.unitIso.symm k.inverseImage ≪≫
      Functor.leftUnitor k.inverseImage)) (by
        intro k l α
        apply NatTrans.ext
        funext X
        change α.app (e.inverse.obj (e.functor.obj X)) ≫ (𝟙 _ ≫ l.inverseImage.map (e.unitIso.inv.app X) ≫ 𝟙 _) =
          (𝟙 _ ≫ k.inverseImage.map (e.unitIso.inv.app X) ≫ 𝟙 _) ≫ α.app X
        simpa only [Category.id_comp, Category.comp_id, postcompose, whiskerLeft_app, Functor.id_obj, Functor.comp_obj] using (α.naturality (e.unitIso.inv.app X)).symm)
  functor_unitIso_comp k := by
    apply NatTrans.ext
    funext X
    change (𝟙 _ ≫ k.inverseImage.map (e.counitIso.inv.app (e.functor.obj X)) ≫ 𝟙 _) ≫
      (𝟙 _ ≫ k.inverseImage.map (e.functor.map (e.unitIso.inv.app X)) ≫ 𝟙 _) = 𝟙 _
    simp only [Category.id_comp, Category.comp_id, ← k.inverseImage.map_comp]
    rw [e.counitInv_functor_comp]
    exact k.inverseImage.map_id _
end SquareKit.Internal.GeometricMorphism
