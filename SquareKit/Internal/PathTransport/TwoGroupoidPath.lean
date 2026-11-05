import SquareKit.DoubleDelooping
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.CategoryTheory.Bicategory.NaturalTransformation.Pseudo

/-!
The first higher dependent-extension discriminator from #322.
The path family over B²ℤ has integer arrows in its total space. Its
2-cells retain the base component, with boundary `a = b + m`.
This construction alone does not supply arbitrary families or contextual J.
-/
namespace SquareKit.Internal.PathTransport.TwoGroupoidPath
open CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

abbrev Base := DoubleDelooping.Space (Multiplicative ℤ)

/-- The path fiber is the one-object groupoid with integer arrows. -/
abbrev Fiber := SingleObj (Multiplicative ℤ)

/-- A base 2-cell acts by a natural transformation of the identity fiber functor. -/
def fiberAction (m : ℤ) : 𝟭 Fiber ⟶ 𝟭 Fiber where
  app _ := Multiplicative.ofAdd m
  naturality := by
    intro x y f
    change Multiplicative.ofAdd m * (show Multiplicative ℤ from f) =
      (show Multiplicative ℤ from f) * Multiplicative.ofAdd m
    exact mul_comm _ _

theorem fiberAction_zero : fiberAction 0 = 𝟙 (𝟭 Fiber) := by
  ext
  rfl

theorem fiberAction_add (m n : ℤ) : fiberAction (m + n) = fiberAction m ≫ fiberAction n := by
  ext
  change m + n = n + m
  omega

/-- Arrows in the total path family. -/
abbrev Arrow := ℤ

/-- The base 2-cell is data; the fiber boundary is an equality because this
particular path fiber is locally discrete. -/
structure Cell (a b : Arrow) where
  base : ℤ
  boundary : (a : ℤ) = b + base

/-- The cell boundary agrees with the actual fiber natural transformation,
including its base component and the order of fiber composition. -/
theorem Cell.fiber_boundary {a b : Arrow} (p : Cell a b) :
    Multiplicative.ofAdd a =
      (fiberAction p.base).app (SingleObj.star (Multiplicative ℤ)) ≫
        (show SingleObj.star (Multiplicative ℤ) ⟶ SingleObj.star (Multiplicative ℤ) from
          Multiplicative.ofAdd b) :=
  p.boundary

theorem Cell.base_eq {a b : Arrow} (p : Cell a b) : p.base = a - b := by
  have := p.boundary
  simp only [Arrow] at *; omega

instance (a b : Arrow) : Subsingleton (Cell a b) where
  allEq p q := by
    have h : p.base = q.base := p.base_eq.trans q.base_eq.symm
    cases p; cases q; cases h; rfl

/-- The unique coherent comparison retains the forced integer base component. -/
def comparison (a b : Arrow) : Cell a b := ⟨a - b, by simp only [Arrow] at *; omega⟩

scoped instance : Groupoid Arrow where
  Hom := Cell
  id a := ⟨0, by simp only [Arrow] at *; omega⟩
  comp p q := ⟨p.base + q.base, by have := p.boundary; have := q.boundary; simp only [Arrow] at *; omega⟩
  inv p := ⟨-p.base, by have := p.boundary; simp only [Arrow] at *; omega⟩
  id_comp _ := Subsingleton.elim _ _
  comp_id _ := Subsingleton.elim _ _
  assoc _ _ _ := Subsingleton.elim _ _
  inv_comp _ := Subsingleton.elim _ _
  comp_inv _ := Subsingleton.elim _ _

scoped instance (a b : Arrow) : Subsingleton (a ⟶ b) :=
  inferInstanceAs (Subsingleton (Cell a b))

/-- The one object of the total path family. -/
def Total := Unit

def point : Total := ()

instance : Bicategory Total where
  Hom _ _ := Arrow
  homCategory _ _ := inferInstanceAs (Category Arrow)
  id _ := (0 : ℤ)
  comp a b := (a : ℤ) + b
  whiskerLeft a _ _ p := ⟨p.base, by have := p.boundary; simp only [Arrow] at *; omega⟩
  whiskerRight p a := ⟨p.base, by have := p.boundary; simp only [Arrow] at *; omega⟩
  associator a b c := ⟨comparison _ _, comparison _ _, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  leftUnitor a := ⟨comparison _ _, comparison _ _, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  rightUnitor a := ⟨comparison _ _, comparison _ _, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  whiskerLeft_id := by intros; exact Subsingleton.elim _ _
  whiskerLeft_comp := by intros; exact Subsingleton.elim _ _
  id_whiskerLeft := by intros; exact Subsingleton.elim _ _
  comp_whiskerLeft := by intros; exact Subsingleton.elim _ _
  id_whiskerRight := by intros; exact Subsingleton.elim _ _
  comp_whiskerRight := by intros; exact Subsingleton.elim _ _
  whiskerRight_id := by intros; exact Subsingleton.elim _ _
  whiskerRight_comp := by intros; exact Subsingleton.elim _ _
  whisker_assoc := by intros; exact Subsingleton.elim _ _
  whisker_exchange := by intros; exact Subsingleton.elim _ _
  pentagon := by intros; exact Subsingleton.elim _ _
  triangle := by intros; exact Subsingleton.elim _ _

instance : Bicategory.Strict Total where
  id_comp _ := Int.zero_add _
  comp_id _ := Int.add_zero _
  assoc _ _ _ := Int.add_assoc _ _ _
  leftUnitor_eqToIso _ := by apply Iso.ext; exact @Subsingleton.elim (Cell _ _) _ _ _
  rightUnitor_eqToIso _ := by apply Iso.ext; exact @Subsingleton.elim (Cell _ _) _ _ _
  associator_eqToIso _ _ _ := by apply Iso.ext; exact @Subsingleton.elim (Cell _ _) _ _ _

instance {x y : Total} (a b : x ⟶ y) : Subsingleton (a ⟶ b) :=
  inferInstanceAs (Subsingleton (Cell a b))

/-- Constant endofunctor at the sole object, sending every arrow to zero. -/
def constant : Pseudofunctor Total Total where
  obj _ := ()
  map _ := (0 : ℤ)
  map₂ _ := comparison _ _
  map₂_id := by intros; exact Subsingleton.elim _ _
  map₂_comp := by intros; exact Subsingleton.elim _ _
  mapId _ := Iso.refl _
  mapComp _ _ := Iso.refl _
  map₂_whisker_left := by intros; exact Subsingleton.elim _ _
  map₂_whisker_right := by intros; exact Subsingleton.elim _ _
  map₂_associator := by intros; exact Subsingleton.elim _ _
  map₂_left_unitor := by intros; exact Subsingleton.elim _ _
  map₂_right_unitor := by intros; exact Subsingleton.elim _ _

/-- The canonical contraction is an actual strong transformation. All its
naturality, unit and composition pastings are equalities of total 2-cells. -/
def coherentContraction : Pseudofunctor.StrongTrans (Pseudofunctor.id Total) constant where
  app _ := (0 : ℤ)
  naturality _ := ⟨comparison _ _, comparison _ _, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  naturality_naturality := by intros; exact Subsingleton.elim _ _
  naturality_id := by intros; exact Subsingleton.elim _ _
  naturality_comp := by intros; exact Subsingleton.elim _ _

theorem coherentContraction_base (a : Arrow) :
    ((coherentContraction.naturality (show point ⟶ point from a)).hom :
      Cell (a + 0) (0 + 0)).base = a := by
  change a + 0 - (0 + 0) = a
  simp only [Arrow] at *
  omega

/-- Every total 1-arrow has a strict inverse. -/
theorem arrow_inverse (a : Arrow) :
    (a : ℤ) + -a = 0 ∧ -a + a = 0 := by simp only [Arrow] at *; omega

/-- Pseudonaturality comparison for contraction with identity component zero.
Its orientation is from the identity functor's arrow to the constant arrow. -/
def contraction (a : Arrow) : Cell a 0 := comparison a 0

theorem contraction_base (a : Arrow) : (contraction a).base = a := by
  change a - 0 = a
  simp only [Arrow] at *; omega

/-- The unit coherence is equality of actual 2-cells. -/
theorem contraction_unit : contraction 0 = 𝟙 (0 : Arrow) := Subsingleton.elim _ _

/-- Composition coherence retains the sum of both base components. -/
theorem contraction_composition (a b : Arrow) :
    (contraction ((a : ℤ) + b)).base = (contraction a).base + (contraction b).base := by
  simp only [contraction_base]

/-- Naturality against a total 2-cell is its boundary equation. -/
theorem contraction_naturality {a b : Arrow} (p : Cell a b) :
    (contraction a).base = (contraction b).base + p.base := by
  simpa only [contraction_base] using p.boundary

/-- A strict natural contraction would impose an impossible arrow equality. -/
theorem no_strict_contraction : ¬ ∃ c : ℤ, ∀ a : ℤ, c = a + c := by
  rintro ⟨c, h⟩
  have := h 1
  omega

/-- Erasing the base component discards the comparison needed at arrow one. -/
theorem comparison_one_not_zero : (comparison 1 0).base ≠ 0 := by decide

end SquareKit.Internal.PathTransport.TwoGroupoidPath
