import SquareKit.Internal.PathTransport.StrictTwoTransformation

/-! The strict 2-category of strict 2-categories, strict higher functors and
strict natural transformations. Its fibers may have genuine 2-cells. -/
namespace SquareKit.Internal.PathTransport
open CategoryTheory Bicategory StrictTwoTransformation
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w

/-- A fixed universe of strict 2-categories; no elimination laws are fields. -/
structure StrictTwoCategory where
  carrier : Type u
  [bicategory : Bicategory.{w,v} carrier]
  [strict : Bicategory.Strict carrier]

attribute [instance] StrictTwoCategory.bicategory StrictTwoCategory.strict
instance : CoeSort (StrictTwoCategory.{u,v,w}) (Type u) := ⟨StrictTwoCategory.carrier⟩

namespace StrictTwoCategory
instance : CategoryStruct StrictTwoCategory.{u,v,w} where
  Hom A B := StrictPseudofunctor A B
  id A := StrictPseudofunctor.id A
  comp F G := F.comp G

instance homCategory (A B : StrictTwoCategory.{u,v,w}) : Category (A ⟶ B) :=
  inferInstanceAs (Category (StrictPseudofunctor A B))

private theorem assoc {A B C D : StrictTwoCategory.{u,v,w}}
    (F : A ⟶ B) (G : B ⟶ C) (H : C ⟶ D) : (F ≫ G) ≫ H = F ≫ G ≫ H :=
  functor_ext rfl

instance : Bicategory StrictTwoCategory.{u,v,w} where
  homCategory A B := inferInstanceAs (Category (StrictPseudofunctor A B))
  whiskerLeft F _ _ η := Trans.whiskerLeft F η
  whiskerRight η H := Trans.whiskerRight η H
  associator F G H := eqToIso (assoc F G H)
  leftUnitor F := eqToIso (functor_id_comp F)
  rightUnitor F := eqToIso (functor_comp_id F)
  whiskerLeft_id _ _ := by apply Trans.ext; intro a; rfl
  whiskerLeft_comp _ _ _ _ _ _ := by apply Trans.ext; intro a; rfl
  id_whiskerLeft η := by
    apply Trans.ext; intro a
    repeat rw [Trans.comp_app]
    simp only [eqToIso.hom, eqToIso.inv]
    dsimp only [Trans.whiskerLeft, Trans.whiskerRight]
    repeat rw [Trans.eqToHom_app]
    change η.app a = 𝟙 _ ≫ η.app a ≫ 𝟙 _
    simp
  comp_whiskerLeft F G _ _ η := by
    apply Trans.ext; intro a
    repeat rw [Trans.comp_app]
    simp only [eqToIso.hom, eqToIso.inv]
    dsimp only [Trans.whiskerLeft, Trans.whiskerRight]
    repeat rw [Trans.eqToHom_app]
    change η.app (G.obj (F.obj a)) = 𝟙 _ ≫ η.app (G.obj (F.obj a)) ≫ 𝟙 _
    simp
  id_whiskerRight F G := by
    apply Trans.ext; intro a
    exact G.map_id _
  comp_whiskerRight η θ H := by
    apply Trans.ext; intro a
    exact H.map_comp _ _
  whiskerRight_id η := by
    apply Trans.ext; intro a
    repeat rw [Trans.comp_app]
    simp only [eqToIso.hom, eqToIso.inv]
    dsimp only [Trans.whiskerLeft, Trans.whiskerRight]
    repeat rw [Trans.eqToHom_app]
    change η.app a = 𝟙 _ ≫ η.app a ≫ 𝟙 _
    simp
  whiskerRight_comp η G H := by
    apply Trans.ext; intro a
    repeat rw [Trans.comp_app]
    simp only [eqToIso.hom, eqToIso.inv]
    dsimp only [Trans.whiskerLeft, Trans.whiskerRight]
    repeat rw [Trans.eqToHom_app]
    change H.map (G.map (η.app a)) = 𝟙 _ ≫ H.map (G.map (η.app a)) ≫ 𝟙 _
    simp
  whisker_assoc F _ _ η H := by
    apply Trans.ext; intro a
    repeat rw [Trans.comp_app]
    simp only [eqToIso.hom, eqToIso.inv]
    dsimp only [Trans.whiskerLeft, Trans.whiskerRight]
    repeat rw [Trans.eqToHom_app]
    change H.map (η.app (F.obj a)) = 𝟙 _ ≫ H.map (η.app (F.obj a)) ≫ 𝟙 _
    simp
  whisker_exchange η θ := by
    apply Trans.ext; intro a
    exact (θ.naturality (η.app a)).symm
  pentagon F G H I := by
    apply Trans.ext; intro a
    repeat rw [Trans.comp_app]
    simp only [eqToIso.hom, eqToIso.inv]
    dsimp only [Trans.whiskerLeft, Trans.whiskerRight]
    repeat rw [Trans.eqToHom_app]
    change I.map (𝟙 (H.obj (G.obj (F.obj a)))) ≫ 𝟙 _ ≫ 𝟙 _ = 𝟙 _ ≫ 𝟙 _
    simp [I.map_id]
  triangle F G := by
    apply Trans.ext; intro a
    repeat rw [Trans.comp_app]
    simp only [eqToIso.hom, eqToIso.inv]
    dsimp only [Trans.whiskerLeft, Trans.whiskerRight]
    repeat rw [Trans.eqToHom_app]
    change 𝟙 _ ≫ 𝟙 _ = G.map (𝟙 (F.obj a))
    simp [G.map_id]

instance : Bicategory.Strict StrictTwoCategory.{u,v,w} where
  id_comp := functor_id_comp
  comp_id := functor_comp_id
  assoc := assoc
  leftUnitor_eqToIso _ := rfl
  rightUnitor_eqToIso _ := rfl
  associator_eqToIso _ _ _ := rfl

end StrictTwoCategory
end SquareKit.Internal.PathTransport
