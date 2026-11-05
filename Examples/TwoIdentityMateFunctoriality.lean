import SquareKit.Internal.PathTransport.TwoIdentityMateFunctoriality
import SquareKit.DoubleDelooping
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.CategoryTheory.Bicategory.Product

/-! Inverse-mate laws retain integer cells, including through a nontrivial projection. -/
namespace Examples.TwoIdentityMateFunctoriality
open CategoryTheory Bicategory SquareKit
open SquareKit.Internal.PathTransport
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
abbrev B := DoubleDelooping.Space (Multiplicative ℤ)
abbrev point : B := DoubleDelooping.point _
abbrev arrow : point ⟶ point := DoubleDelooping.arrow _
local instance : IsGroupoid B where
  all_isIso f := by
    obtain ⟨g, h, k⟩ := DoubleDelooping.one_inverse (Multiplicative ℤ) f
    exact ⟨⟨g, h, k⟩⟩

private theorem integer_eqToHom {x y : B} {a b : x ⟶ y} (h : a = b) :
    eqToHom h = (1 : Multiplicative ℤ) := by
  cases a
  cases b
  rfl

private theorem integer_mate (n : ℤ) :
    TwoIdentityTransport.inverseMate (u := arrow) (u' := arrow) (h := arrow)
      (Multiplicative.ofAdd n) = Multiplicative.ofAdd (-n) := by
  simp [TwoIdentityTransport.inverseMate, ← Groupoid.inv_eq_inv]
  simp only [Bicategory.whiskerLeft, Bicategory.whiskerRight, Bicategory.associator,
    Iso.refl_hom, Iso.refl_inv, CategoryStruct.comp, CategoryStruct.id, Groupoid.inv,
    one_mul, mul_one]

/-- Postcomposition leaves the inverse integer cell, as the general mate law predicts. -/
theorem postcomposition_integer (n : ℤ) :
    TwoIdentityTransport.inverseMate (u := arrow ≫ arrow) (u' := arrow ≫ arrow)
      (h := arrow)
      ((Multiplicative.ofAdd n : arrow ⟶ arrow ≫ arrow) ▷ arrow ≫
        eqToHom (Category.assoc arrow arrow arrow)) = Multiplicative.ofAdd (-n) := by
  rw [TwoIdentityTransport.inverseMate_postcomp]
  rw [integer_mate]
  simp only [integer_eqToHom, Bicategory.whiskerLeft, CategoryStruct.comp,
    one_mul, mul_one]

local instance : IsLocallyGroupoid (B × B) := by
  intro x y
  change IsGroupoid ((x.1 ⟶ y.1) × (x.2 ⟶ y.2))
  infer_instance

abbrev pairPoint : B × B := (point, point)
abbrev pairArrow : pairPoint ⟶ pairPoint := (arrow, arrow)

/-- Projecting a pair of genuine cells retains the first inverse integer and
forgets only the explicitly projected second component. -/
theorem projection_integer (m n : ℤ) :
    TwoIdentityTransport.inverseMate
      (u := (Bicategory.Prod.fst B B).map pairArrow)
      (u' := (Bicategory.Prod.fst B B).map pairArrow)
      (h := (Bicategory.Prod.fst B B).map pairArrow)
      ((Bicategory.Prod.fst B B).map₂
        (show pairArrow ⟶ pairArrow ≫ pairArrow from
          (Multiplicative.ofAdd m, Multiplicative.ofAdd n)) ≫
        eqToHom ((Bicategory.Prod.fst B B).map_comp pairArrow pairArrow)) =
      Multiplicative.ofAdd (-m) := by
  rw [TwoIdentityTransport.inverseMate_map]
  simp only [integer_eqToHom, Bicategory.Prod.fst]
  simp [TwoIdentityTransport.inverseMate, ← Groupoid.inv_eq_inv,
    Bicategory.whiskerLeft, Bicategory.whiskerRight, CategoryStruct.comp,
    CategoryStruct.id, Groupoid.inv, one_mul, mul_one]

end Examples.TwoIdentityMateFunctoriality
