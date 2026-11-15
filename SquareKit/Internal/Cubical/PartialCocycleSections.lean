import SquareKit.Internal.Cubical.CocycleFamily
import SquareKit.Internal.Cubical.PartialCocycles

/-! A partial section supplies a cocycle on the actual face sieve. -/
namespace SquareKit.Cubical.CategoryCocycles
open CategoryTheory Presheaf

def faceSieve {Γ : Context.{0}} (φ : Cofibration Γ) : SieveObjects Γ.Elementsᵒᵖ where
  contains X := φ.full X.unop
  downward f := φ.full_natural f.unop

def partialSectionCocycle {Γ : Context.{0}} {φ : Cofibration Γ}
    (t : PartialSection (cocycleFamily Γ) φ) : PartialCocycle2 (faceSieve φ) where
  cochain {X Y Z} f g p := CubeCocycle.eval (t.val Z.unop p)
    f.unop.hom.unop g.unop.hom.unop (𝟙 Z.unop.obj.unop)
  closed {W X Y Z} f g h p := by
    let a := f.unop.hom.unop
    let b := g.unop.hom.unop
    let c := h.unop.hom.unop
    let z := t.val Z.unop p
    have e := CubeCocycle.closed_eval z a b c (𝟙 Z.unop.obj.unop)
    have el := congrArg (fun q => CubeCocycle.eval q a b (𝟙 Y.unop.obj.unop))
      (t.property h.unop p)
    have el' := (CubeCocycle.pullback_eval z c a b (𝟙 Y.unop.obj.unop)).symm.trans el
    simp only [Category.id_comp] at el'
    change CubeCocycle.eval z b c (𝟙 _) - CubeCocycle.eval z (a ≫ b) c (𝟙 _) +
      CubeCocycle.eval z a (b ≫ c) (𝟙 _) -
      CubeCocycle.eval (t.val Y.unop _) a b (𝟙 _) = 0
    rw [← el']
    simpa only [Category.comp_id] using e

end SquareKit.Cubical.CategoryCocycles
