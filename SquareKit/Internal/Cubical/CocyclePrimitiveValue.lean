import SquareKit.Internal.Cubical.CocycleBoxPrimitive

/-! A relative primitive depends on the selected cocycle at the fresh target cube. -/
namespace SquareKit.Cubical.CategoryCocycles
open CategoryTheory Presheaf Cube

def primitiveValue {I J : Cube} (f : I ⟶ J) (r : I ⟶ (⟨1⟩ : Cube))
    (s : J ⟶ (⟨1⟩ : Cube)) (z : CubeCocycle (extend J)) : ℤ :=
  z.eval (graph (Cube.endpoint I false)) (extensionMap f) (𝟙 _) -
    z.eval f (graph (Cube.endpoint J false)) (𝟙 _) -
    (z.eval (graph r) (extensionMap f) (𝟙 _) - z.eval f (graph s) (𝟙 _))

theorem boxPrimitive_value {Γ : Context.{0}} {φ : Cofibration Γ}
    (b : OpenBox (cocycleFamily (total (interval Γ))) φ)
    {X Y : (total (interval Γ)).Elementsᵒᵖ} (f : X ⟶ Y) (p : (tubeSieve φ).contains Y) :
    boxPrimitive b f p =
      primitiveValue f.unop.hom.unop X.unop.val.2.down Y.unop.val.2.down
        (b.tube.val (freshExtension (intervalBaseElement Y.unop)) (freshPreservesTube φ Y p)) -
      primitiveValue f.unop.hom.unop X.unop.val.2.down Y.unop.val.2.down
        (b.base.val (intervalBaseElement (freshExtension (intervalBaseElement Y.unop)))) := by
  let z := b.tube.val (freshExtension (intervalBaseElement Y.unop)) (freshPreservesTube φ Y p)
  let a := b.base.val (intervalBaseElement (freshExtension (intervalBaseElement Y.unop)))
  let g := f.unop.hom.unop
  let rz := X.unop.val.2.down
  let sz := Y.unop.val.2.down
  let z₁ := CubeCocycle.eval z (graph (Cube.endpoint X.unop.obj.unop false)) (extensionMap g) (𝟙 _)
  let z₂ := CubeCocycle.eval z g (graph (Cube.endpoint Y.unop.obj.unop false)) (𝟙 _)
  let z₃ := CubeCocycle.eval z (graph rz) (extensionMap g) (𝟙 _)
  let z₄ := CubeCocycle.eval z g (graph sz) (𝟙 _)
  let a₁ := CubeCocycle.eval a (graph (Cube.endpoint X.unop.obj.unop false)) (extensionMap g) (𝟙 _)
  let a₂ := CubeCocycle.eval a g (graph (Cube.endpoint Y.unop.obj.unop false)) (𝟙 _)
  let a₃ := CubeCocycle.eval a (graph rz) (extensionMap g) (𝟙 _)
  let a₄ := CubeCocycle.eval a g (graph sz) (𝟙 _)
  change ((z₁-a₁)-(z₂-a₂))-((z₃-a₃)-(z₄-a₄)) = (z₁-z₂-(z₃-z₄))-(a₁-a₂-(a₃-a₄))
  omega

end SquareKit.Cubical.CategoryCocycles
