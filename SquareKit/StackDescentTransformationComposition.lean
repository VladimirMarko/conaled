import SquareKit.StackDescentTransformation

/-! Transport along the vertical composite of strong transformations. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SquareKit.StackDescentTransformation
open CategoryTheory Opposite SquareKit.StackDescentTransformation
open scoped CategoryTheory.Pseudofunctor.StrongTrans
universe u v u₁ v₁
variable {C : Type u} [Category.{v} C]
variable {A B D : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v₁,u₁}}
variable (α : A ⟶ B) (β : B ⟶ D)
theorem mapHom_vcomp {X₁ X₂ Y : C} {M₁ : A.obj (.mk (op X₁))} {M₂ : A.obj (.mk (op X₂))}
    (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂)
    (h : (A.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (A.map f₂.op.toLoc).toFunctor.obj M₂) :
    mapHom (α ≫ β) f₁ f₂ h =
      mapHom β (M₁ := (component α X₁).obj M₁) (M₂ := (component α X₂).obj M₂)
        f₁ f₂ (mapHom α f₁ f₂ h) := by
  simp only [mapHom, comparison, component, Cat.Hom.toNatIso_inv, Cat.Hom.toNatIso_hom]
  simp [Functor.map_comp, Category.assoc, Cat.Hom.toNatTrans_comp,
    Cat.whiskerLeft_toNatTrans, Cat.whiskerRight_toNatTrans,
    Cat.associator_hom_toNatTrans, Cat.associator_inv_toNatTrans]
end SquareKit.StackDescentTransformation
