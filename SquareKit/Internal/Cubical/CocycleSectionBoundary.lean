import SquareKit.Internal.Cubical.PartialCocycleSections

/-! Equality of cochains on a face recovers the selected partial section itself. -/
namespace SquareKit.Cubical.CategoryCocycles
open CategoryTheory Presheaf

theorem cocycleSection_partial {Γ : Context.{0}} {φ : Cofibration Γ}
    (z : Cocycle2 Γ.Elementsᵒᵖ) (t : PartialSection (cocycleFamily Γ) φ)
    (hz : ∀ {X Y Z : Γ.Elementsᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) (p : (faceSieve φ).contains Z),
      z.cochain f g = (partialSectionCocycle t).cochain f g p)
    (x : Γ.Elements) (p : φ.full x) : (cocycleSection z).val x = t.val x p := by
  apply Cocycle2.ext
  funext X Y Z f g
  let k : x ⟶ Γ.elementsMk (Opposite.op Z.left) (Γ.map Z.hom.op x.val) :=
    Functor.Elements.homMk Z.hom.op rfl
  let pZ := φ.full_natural k p
  have hh := hz ((elementRestriction x).map f) ((elementRestriction x).map g) pZ
  change z.cochain ((elementRestriction x).map f) ((elementRestriction x).map g) = _
  rw [hh]
  change CubeCocycle.eval (t.val _ pZ) f.left g.left (𝟙 Z.left) = (t.val x p).cochain f g
  have eh := t.property k p
  calc
    _ = CubeCocycle.eval ((t.val x p).pullback (Over.map Z.hom)) f.left g.left (𝟙 Z.left) :=
      congrArg (fun q => CubeCocycle.eval q f.left g.left (𝟙 Z.left)) eh.symm
    _ = CubeCocycle.eval (t.val x p) f.left g.left ((𝟙 Z.left) ≫ Z.hom) :=
      CubeCocycle.pullback_eval _ _ _ _ _
    _ = _ := by rw [Category.id_comp]; exact CubeCocycle.eval_arrows _ f g

end SquareKit.Cubical.CategoryCocycles
