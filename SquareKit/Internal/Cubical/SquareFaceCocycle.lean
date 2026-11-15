import SquareKit.Internal.Cubical.CategoryCocycles
import SquareKit.Internal.Cubical.PartialDimension
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.Data.Fintype.Prod

/-! An integer one-cocycle on the eight faces in a square boundary. -/
namespace SquareKit.Cubical.CategoryCocycles
open CategoryTheory

structure SquareFaceLabel where
  val : PartialDimension.Carrier × PartialDimension.Carrier
  boundary : val.1 ≠ none ∨ val.2 ≠ none
  deriving DecidableEq

instance : Fintype SquareFaceLabel := Fintype.ofEquiv
  {p : PartialDimension.Carrier × PartialDimension.Carrier // p.1 ≠ none ∨ p.2 ≠ none}
  ⟨(fun p => ⟨p.val,p.property⟩),(fun p => ⟨p.val,p.boundary⟩),(by intro p; rfl),(by intro p; rfl)⟩

private theorem refines_trans : ∀ a b c : PartialDimension.Carrier,
    PartialDimension.Refines a b → PartialDimension.Refines b c → PartialDimension.Refines a c := by decide

instance : Preorder SquareFaceLabel where
  le x y := PartialDimension.Refines y.val.1 x.val.1 ∧ PartialDimension.Refines y.val.2 x.val.2
  le_refl x := ⟨PartialDimension.refines_refl _,PartialDimension.refines_refl _⟩
  le_trans x y z h k := ⟨refines_trans _ _ _ k.1 h.1,refines_trans _ _ _ k.2 h.2⟩

instance (x y : SquareFaceLabel) : Decidable (x ≤ y) :=
  inferInstanceAs (Decidable (PartialDimension.Refines y.val.1 x.val.1 ∧ PartialDimension.Refines y.val.2 x.val.2))

def squareEdgeValue (x y : SquareFaceLabel) : ℤ :=
  if x.val = (some true,some true) ∧ y.val = (none,some true) then 1 else 0

def squareBoundaryCochain : Cochain1 SquareFaceLabel := fun {X Y} _ => squareEdgeValue X Y

private theorem squareEdgeValue_closed : ∀ x y z : SquareFaceLabel, x ≤ y → y ≤ z →
    squareEdgeValue y z - squareEdgeValue x z + squareEdgeValue x y = 0 := by decide

theorem squareBoundaryCochain_closed {X Y Z : SquareFaceLabel} (f : X ⟶ Y) (g : Y ⟶ Z) :
    δ1 squareBoundaryCochain f g = 0 := squareEdgeValue_closed X Y Z (leOfHom f) (leOfHom g)

def squareCorner (a b : Bool) : SquareFaceLabel := ⟨(some a,some b),Or.inl (by simp)⟩
def squareHorizontal (b : Bool) : SquareFaceLabel := ⟨(none,some b),Or.inr (by simp)⟩
def squareVertical (a : Bool) : SquareFaceLabel := ⟨(some a,none),Or.inl (by simp)⟩

/-- The oriented boundary sum is one, while every composable triangle has zero coboundary. -/
theorem squareBoundaryCochain_cycle :
    squareEdgeValue (squareCorner false false) (squareHorizontal false) -
    squareEdgeValue (squareCorner true false) (squareHorizontal false) +
    squareEdgeValue (squareCorner true false) (squareVertical true) -
    squareEdgeValue (squareCorner true true) (squareVertical true) +
    squareEdgeValue (squareCorner true true) (squareHorizontal true) -
    squareEdgeValue (squareCorner false true) (squareHorizontal true) +
    squareEdgeValue (squareCorner false true) (squareVertical false) -
    squareEdgeValue (squareCorner false false) (squareVertical false) = 1 := by decide

end SquareKit.Cubical.CategoryCocycles
