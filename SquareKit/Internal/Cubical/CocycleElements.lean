import SquareKit.Internal.Cubical.CocyclePresheaf

/-! Restrict global element-category cochains to a generalized cube. -/
namespace SquareKit.Cubical.CategoryCocycles
open CategoryTheory
universe u

/-- Every formal cube over a generalized element restricts that element. -/
def elementRestriction {Γ : Presheaf.Context.{u}} (x : Γ.Elements) :
    Over x.obj.unop ⥤ Γ.Elementsᵒᵖ where
  obj A := Opposite.op (Γ.elementsMk (Opposite.op A.left) (Γ.map A.hom.op x.val))
  map f := Quiver.Hom.op (Functor.Elements.homMk f.left.op (by
    change (Γ.map _ ≫ Γ.map f.left.op) x.val = Γ.map _ x.val
    rw [← Γ.map_comp]
    congr 2
    exact congrArg Γ.map (congrArg Quiver.Hom.op (Over.w f))))
  map_id A := by
    apply Quiver.Hom.unop_inj
    apply Functor.Elements.Hom.ext
    rfl
  map_comp f g := by
    apply Quiver.Hom.unop_inj
    apply Functor.Elements.Hom.ext
    rfl

private theorem elementOppHom_hext {Γ : Presheaf.Context.{u}}
    {x x' y y' : Γ.Elementsᵒᵖ} (hx : x = x') (hy : y = y')
    (f : x ⟶ y) (g : x' ⟶ y') (h : HEq f.unop.hom g.unop.hom) : HEq f g := by
  cases hx; cases hy
  apply heq_of_eq
  apply Quiver.Hom.unop_inj
  apply Functor.Elements.hom_ext
  exact eq_of_heq h

theorem elementRestriction_restriction {Γ : Presheaf.Context.{u}}
    {x y : Γ.Elements} (f : x ⟶ y) :
    Over.map f.hom.unop ⋙ elementRestriction x = elementRestriction y := by
  have ho : ∀ A : Over y.obj.unop,
      (Over.map f.hom.unop ⋙ elementRestriction x).obj A = (elementRestriction y).obj A := by
    intro A
    apply congrArg Opposite.op
    apply congrArg (Γ.elementsMk (Opposite.op A.left))
    exact (Γ.map_comp_apply f.hom A.hom.op x.val).trans
      (congrArg (Γ.map A.hom.op) f.map_val)
  apply Functor.hext ho
  intro A B g
  exact elementOppHom_hext (ho A) (ho B) _ _ HEq.rfl

/-- Context substitutions preserve restriction diagrams by equality. -/
theorem elementRestriction_substitution {Γ Δ : Presheaf.Context.{u}}
    (σ : Δ ⟶ Γ) (x : Δ.Elements) :
    elementRestriction x ⋙ σ.mapElements.op = elementRestriction (σ.mapElements.obj x) := by
  have ho : ∀ A : Over x.obj.unop,
      (elementRestriction x ⋙ σ.mapElements.op).obj A =
        (elementRestriction (σ.mapElements.obj x)).obj A := by
    intro A
    apply congrArg Opposite.op
    exact congrArg (Γ.elementsMk (Opposite.op A.left)) (σ.naturality_apply A.hom.op x.val)
  apply Functor.hext ho
  intro A B f
  exact elementOppHom_hext (ho A) (ho B) _ _ HEq.rfl

/-- Global closed cochains give strictly coherent slice cocycles. -/
def restrictCocycle {Γ : Presheaf.Context.{u}} (z : Cocycle2 Γ.Elementsᵒᵖ)
    (x : Γ.Elements) : Cocycle2 (Over x.obj.unop) := z.pullback (elementRestriction x)

theorem restrictCocycle_natural {Γ : Presheaf.Context.{u}} (z : Cocycle2 Γ.Elementsᵒᵖ)
    {x y : Γ.Elements} (f : x ⟶ y) :
    (restrictCocycle z x).pullback (Over.map f.hom.unop) = restrictCocycle z y := by
  unfold restrictCocycle
  rw [Cocycle2.pullback_comp,elementRestriction_restriction]

end SquareKit.Cubical.CategoryCocycles
