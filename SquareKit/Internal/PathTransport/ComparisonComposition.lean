import SquareKit.Internal.PathTransport.GeneratedComparisonRestriction

/-! Composition laws for the comparison operations used by generated context
restriction. These equations retain whole functors and natural transformations. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.GroupoidModel.Comparison
open CategoryTheory CategoryTheory.Functor
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u

/-- The comprehension map associated to a base/family comparison. -/
def totalMap {C D : Grpd.{u,u}} (R : C ⥤ D)
    {A : C ⥤ Grpd.{u,u}} {B : D ⥤ Grpd.{u,u}} (α : A ⟶ R ⋙ B) :
    Extend A ⥤ Extend B :=
  Grothendieck.map (whiskerRight α Grpd.forgetToCat) ⋙
    Grothendieck.pre (B ⋙ Grpd.forgetToCat) R

theorem totalMap_extend {Γ : Context.{u}} (A : Family Γ) :
    totalMap Γ.map A.map = A.extend.map := rfl

theorem totalMap_id {C : Grpd.{u,u}} (A : C ⥤ Grpd.{u,u}) :
    totalMap (𝟭 C) (𝟙 A) = 𝟭 (Extend A) := by
  unfold totalMap
  rw [whiskerRight_id', Grothendieck.map_id_eq]
  rfl

theorem totalMap_comp {C D E : Grpd.{u,u}} (R : C ⥤ D) (S : D ⥤ E)
    {A : C ⥤ Grpd.{u,u}} {B : D ⥤ Grpd.{u,u}} {K : E ⥤ Grpd.{u,u}}
    (α : A ⟶ R ⋙ B) (β : B ⟶ S ⋙ K) :
    totalMap R α ⋙ totalMap S β = totalMap (R ⋙ S) (α ≫ whiskerLeft R β) := by
  unfold totalMap
  rw [whiskerRight_comp, Grothendieck.map_comp_eq]
  rfl

end SquareKit.Internal.PathTransport.GroupoidModel.Comparison
