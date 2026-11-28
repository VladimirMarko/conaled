import SquareKit.SheafGroupoidBibundleInverse
import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic

/-! Double-opposite recovery and both actual tensor inverses. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SquareKit.SheafGroupoid.Bibundle
open CategoryTheory Opposite SquareKit SquareKit.SheafGroupoid
open SquareKit.SheafGroupoid.Bundle SquareKit.SheafGroupoid.Bibundle
open SquareKit.SheafGroupoid.Bibundle
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {G H : Operations J} [G.Laws] [H.Laws]
variable (P : Bibundle G H) (hP : LeftPrincipal P)

def doubleOppositeMap : opposite (opposite P hP) (opposite_leftPrincipal P hP) ⟶ P where
  hom := {
    app x := ↾id
    naturality := by intros; rfl }
  equivariant x m n g t := by
    change P.right.act x (Groupoid.inv (Groupoid.inv g)) t = P.right.act x g t
    simp
  left_equivariant g k t := by
    change P.left.act (Groupoid.inv (Groupoid.inv g)) k t = P.left.act g k t
    simp

def doubleOppositeIso : opposite (opposite P hP) (opposite_leftPrincipal P hP) ≅ P :=
  asIso (doubleOppositeMap P hP)

def oppositeEvaluationIso : tensor (opposite P hP) P ≅ identity H :=
  (asIso (SquareKit.SheafGroupoid.Bibundle.map (𝟙 (opposite P hP)) (doubleOppositeIso P hP).inv)) ≪≫
    evaluationIso (opposite P hP) (opposite_leftPrincipal P hP)

end SquareKit.SheafGroupoid.Bibundle
