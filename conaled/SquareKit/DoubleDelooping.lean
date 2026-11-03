import Mathlib.CategoryTheory.Bicategory.Strict.Basic
import Mathlib.CategoryTheory.SingleObj

/-! Double delooping of an abelian group, using Mathlib's bicategory interface.
The unique object and 1-arrow carry group elements as 2-automorphisms.
Commutativity supplies interchange; it is not needed for the hom-groupoid. -/
namespace SquareKit.DoubleDelooping
open CategoryTheory
universe u

/-- A separate object type prevents competing bicategory instances on Unit. -/
def Space (_A : Type u) := Unit

instance (A : Type u) : Unique (Space A) := inferInstanceAs (Unique Unit)

variable (A : Type u) [CommGroup A]

instance : Bicategory (Space A) where
  Hom _ _ := SingleObj A
  id _ := SingleObj.star A
  comp _ _ := SingleObj.star A
  whiskerLeft _ _ _ η := η
  whiskerRight η _ := η
  associator _ _ _ := Iso.refl _
  leftUnitor _ := { hom := 1, inv := 1, hom_inv_id := one_mul (1 : A), inv_hom_id := one_mul (1 : A) }
  rightUnitor _ := { hom := 1, inv := 1, hom_inv_id := one_mul (1 : A), inv_hom_id := one_mul (1 : A) }
  whiskerLeft_id _ _ := rfl
  whiskerLeft_comp := by intros; rfl
  id_whiskerLeft := by intros; simp [SingleObj.comp_as_mul]
  comp_whiskerLeft := by intros; simp [SingleObj.comp_as_mul, SingleObj.id_as_one]
  id_whiskerRight _ _ := rfl
  comp_whiskerRight _ _ _ := rfl
  whiskerRight_id := by intros; simp [SingleObj.comp_as_mul]
  whiskerRight_comp := by intros; simp [SingleObj.comp_as_mul, SingleObj.id_as_one]
  whisker_assoc := by intros; simp [SingleObj.comp_as_mul, SingleObj.id_as_one]
  whisker_exchange := by intros; exact mul_comm _ _
  pentagon := by intros; simp [SingleObj.comp_as_mul, SingleObj.id_as_one]
  triangle := by intros; change (1 : A) * 1 = 1; simp

instance : Bicategory.Strict (Space A) where
  id_comp f := by cases f; rfl
  comp_id f := by cases f; rfl
  assoc _ _ _ := rfl
  leftUnitor_eqToIso f := by cases f; rfl
  rightUnitor_eqToIso f := by cases f; rfl
  associator_eqToIso _ _ _ := rfl

/-- Every hom-category is a groupoid; all 2-arrows are invertible. -/
instance (x y : Space A) : Groupoid (x ⟶ y) :=
  inferInstanceAs (Groupoid (SingleObj A))

def point : Space A := ()
abbrev arrow : point A ⟶ point A := SingleObj.star A
abbrev Cell := arrow A ⟶ arrow A

/-- Vertical composition comes from the hom-category. -/
def vertical (p q : Cell A) : Cell A := p ≫ q

/-- Horizontal composition is whiskering followed by vertical composition. -/
def horizontal (p q : Cell A) : Cell A :=
  Bicategory.whiskerRight p (arrow A) ≫ Bicategory.whiskerLeft (arrow A) q

theorem vertical_mul (p q : Cell A) : vertical A p q = q * p := rfl
theorem horizontal_mul (p q : Cell A) : horizontal A p q = q * p := rfl

theorem interchange (p q r s : Cell A) :
    vertical A (horizontal A p q) (horizontal A r s) =
      horizontal A (vertical A p r) (vertical A q s) := by
  change (s * r) * (q * p) = (s * q) * (r * p)
  ac_rfl

theorem vertical_inverse (p : Cell A) : vertical A p p⁻¹ = 1 := inv_mul_cancel p
theorem horizontal_inverse (p : Cell A) : horizontal A p p⁻¹ = 1 := inv_mul_cancel p

/-- Every 1-arrow has a strict two-sided inverse. -/
theorem one_inverse {x y : Space A} (f : x ⟶ y) :
    ∃ g : y ⟶ x, f ≫ g = 𝟙 x ∧ g ≫ f = 𝟙 y :=
  ⟨SingleObj.star A, rfl, rfl⟩

/-- The sole 1-arrow is also strictly invertible. -/
theorem arrow_inverse : arrow A ≫ arrow A = 𝟙 (point A) := rfl
end SquareKit.DoubleDelooping

namespace SquareKit.DoubleDelooping
open CategoryTheory
universe u v
variable {A : Type u} {B : Type v} [CommGroup A] [CommGroup B]

/-- A homomorphism preserves both 2-cell compositions without any extra law. -/
theorem map_vertical (f : A →* B) (p q : Cell A) :
    f (vertical A p q) = vertical B (f p) (f q) := f.map_mul q p

theorem map_horizontal (f : A →* B) (p q : Cell A) :
    f (horizontal A p q) = horizontal B (f p) (f q) := f.map_mul q p
end SquareKit.DoubleDelooping
