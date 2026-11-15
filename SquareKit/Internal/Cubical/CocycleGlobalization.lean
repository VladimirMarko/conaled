import SquareKit.Internal.Cubical.CocycleElements
import SquareKit.Internal.Cubical.CocycleEvaluation

/-! Closed cochains on generalized elements and maps to the cocycle presheaf. -/
namespace SquareKit.Cubical.CategoryCocycles
open CategoryTheory

/-- Restriction of one global cocycle defines a natural map of presheaves. -/
def globalToMap {Γ : Presheaf.Context.{0}} (z : Cocycle2 Γ.Elementsᵒᵖ) : Γ ⟶ cocycles where
  app I := TypeCat.ofHom (fun x => restrictCocycle z (Γ.elementsMk I x))
  naturality I J f := by
    apply ConcreteCategory.hom_ext
    intro x
    change restrictCocycle z (Γ.elementsMk J (Γ.map f x)) =
      (restrictCocycle z (Γ.elementsMk I x)).pullback (Over.map f.unop)
    exact (restrictCocycle_natural z
      (x := Γ.elementsMk I x) (y := Γ.elementsMk J (Γ.map f x))
      (Functor.Elements.homMk f rfl)).symm

def mapToCochain {Γ : Presheaf.Context.{0}} (v : Γ ⟶ cocycles) : Cochain2 Γ.Elementsᵒᵖ :=
  fun {X Y Z} f g => CubeCocycle.eval (v.app Z.unop.obj Z.unop.val)
    f.unop.hom.unop g.unop.hom.unop (𝟙 Z.unop.obj.unop)

theorem map_restriction {Γ : Presheaf.Context.{0}} (v : Γ ⟶ cocycles)
    {x y : Γ.Elements} (f : x ⟶ y) :
    (v.app x.obj x.val).pullback (Over.map f.hom.unop) = v.app y.obj y.val := by
  exact (v.naturality_apply f.hom x.val).symm.trans (congrArg (v.app y.obj) f.map_val)

/-- Naturality identifies the last face of each global cocycle equation. -/
def mapToGlobal {Γ : Presheaf.Context.{0}} (v : Γ ⟶ cocycles) : Cocycle2 Γ.Elementsᵒᵖ where
  cochain := mapToCochain v
  closed {W X Y Z} f g h := by
    let a := f.unop.hom.unop
    let b := g.unop.hom.unop
    let c := h.unop.hom.unop
    let z := v.app Z.unop.obj Z.unop.val
    have e := CubeCocycle.closed_eval z a b c (𝟙 Z.unop.obj.unop)
    have el := congrArg (fun q => CubeCocycle.eval q a b (𝟙 Y.unop.obj.unop))
      (map_restriction v h.unop)
    have el' := (CubeCocycle.pullback_eval z c a b (𝟙 Y.unop.obj.unop)).symm.trans el
    simp only [Category.id_comp] at el'
    change CubeCocycle.eval z b c (𝟙 _) - CubeCocycle.eval z (a ≫ b) c (𝟙 _) +
      CubeCocycle.eval z a (b ≫ c) (𝟙 _) -
      CubeCocycle.eval (v.app Y.unop.obj Y.unop.val) a b (𝟙 _) = 0
    rw [← el']
    simpa only [Category.comp_id] using e

end SquareKit.Cubical.CategoryCocycles
