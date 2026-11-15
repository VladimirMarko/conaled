import SquareKit.Internal.PathTransport.ComparisonComposition

/-! Strict reindexing squares retain the selected base and fiber arrows. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.GroupoidModel.Comparison
open CategoryTheory CategoryTheory.Functor
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u

theorem map_eq_pre {C D : Grpd.{u,u}} (B : D ⥤ Cat.{u,u})
    {R S : C ⥤ D} (h : R = S) :
    Grothendieck.map (eqToHom (congrArg (· ⋙ B) h)) ⋙ Grothendieck.pre B S =
      Grothendieck.pre B R := by
  subst S
  simp only [eqToHom_refl, Grothendieck.map_id_eq, Functor.id_comp]

theorem pre_totalMap {C D E F : Grpd.{u,u}}
    (R : C ⥤ D) (S : E ⥤ F) (f : C ⥤ E) (g : D ⥤ F)
    {A : D ⥤ Grpd.{u,u}} {B : F ⥤ Grpd.{u,u}} (α : A ⟶ g ⋙ B)
    (h : R ⋙ g = f ⋙ S) :
    Grothendieck.pre (A ⋙ Grpd.forgetToCat) R ⋙ totalMap g α =
      totalMap f (B := S ⋙ B) (whiskerLeft R α ≫ eqToHom (congrArg (· ⋙ B) h)) ⋙
        Grothendieck.pre (B ⋙ Grpd.forgetToCat) S := by
  unfold totalMap
  rw [whiskerRight_comp, Grothendieck.map_comp_eq]
  have hc : whiskerRight (eqToHom (congrArg (· ⋙ B) h)) Grpd.forgetToCat =
      eqToHom (congrArg (· ⋙ (B ⋙ Grpd.forgetToCat)) h) := by
    apply NatTrans.ext
    funext c
    simp only [whiskerRight_app, eqToHom_app, eqToHom_map]
  rw [hc]
  simp only [Functor.assoc, Grothendieck.pre_comp_map_assoc]
  change Grothendieck.map (whiskerLeft R (whiskerRight α Grpd.forgetToCat)) ⋙
    Grothendieck.pre (B ⋙ Grpd.forgetToCat) (R ⋙ g) =
    Grothendieck.map (whiskerLeft R (whiskerRight α Grpd.forgetToCat)) ⋙
      Grothendieck.map (eqToHom (congrArg (· ⋙ (B ⋙ Grpd.forgetToCat)) h)) ⋙
        Grothendieck.pre (B ⋙ Grpd.forgetToCat) (f ⋙ S)
  rw [map_eq_pre (B ⋙ Grpd.forgetToCat) h]

end SquareKit.Internal.PathTransport.GroupoidModel.Comparison

namespace SquareKit.Internal.PathTransport.GroupoidModel.Comparison
open CategoryTheory
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
theorem inclusion_pre {C D : Grpd.{u,u}} (B : D ⥤ Cat.{u,u}) (S : C ⥤ D) (c : C) :
    Grothendieck.ι (S ⋙ B) c ⋙ Grothendieck.pre B S = Grothendieck.ι B (S.obj c) := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro x y f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  apply Grothendieck.ext _ _ (S.map_id c)
  change eqToHom _ ≫ (eqToHom _ ≫ f) = eqToHom _ ≫ f
  rw [← Category.assoc, eqToHom_trans]
end SquareKit.Internal.PathTransport.GroupoidModel.Comparison
