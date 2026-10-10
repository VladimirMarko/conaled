import Mathlib.Algebra.Tropical.Basic
import Mathlib.Algebra.Ring.Prod
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# The interval semiring for setup and hold timing

Lower bounds use max-plus, upper bounds use min-plus.  The infinite lower
bound is represented by `WithTop` of the order dual, so both factors use
Mathlib's proved tropical commutative-semiring construction.

An interval is a pair of bounds, with no nonemptiness invariant.  Its
addition is intersection and its multiplication is endpoint addition.
Endpoint addition is NOT claimed to model Minkowski sum after quotienting
all inverted intervals to the empty set; `empty_product_counterexample`
below records why that quotient would be unsound.
-/

namespace Applications.Timing

abbrev Time := ℚ
abbrev Lower := Tropical (WithTop (OrderDual Time))
abbrev Upper := Tropical (WithTop Time)
abbrev Interval := Lower × Upper

example : CommSemiring Interval := inferInstance

namespace Interval

def finite (lo hi : Time) : Interval :=
  (Tropical.trop ((OrderDual.toDual lo : OrderDual Time) : WithTop (OrderDual Time)),
   Tropical.trop (hi : WithTop Time))

def point (d : Time) : Interval := finite d d

def Contains (I : Interval) (t : Time) : Prop :=
  ((OrderDual.toDual t : OrderDual Time) : WithTop (OrderDual Time)) ≤ Tropical.untrop I.1 ∧
  (t : WithTop Time) ≤ Tropical.untrop I.2

instance (I : Interval) (t : Time) : Decidable (I.Contains t) :=
  inferInstanceAs (Decidable (_ ∧ _))

@[simp] theorem contains_finite (lo hi t : Time) :
    (finite lo hi).Contains t ↔ lo ≤ t ∧ t ≤ hi := by
  simp [Contains, finite]

@[simp] theorem contains_zero (t : Time) : (0 : Interval).Contains t := by
  simp [Contains]

@[simp] theorem contains_add (I J : Interval) (t : Time) :
    (I + J).Contains t ↔ I.Contains t ∧ J.Contains t := by
  simp only [Contains, Prod.fst_add, Prod.snd_add, Tropical.untrop_add, le_min_iff]
  tauto

private theorem coe_le_shift {A : Type*} [AddCommGroup A] [LinearOrder A] [IsOrderedAddMonoid A]
    (a b : A) (c : WithTop A) :
    (a : WithTop A) ≤ (b : WithTop A) + c ↔ ((a - b : A) : WithTop A) ≤ c := by
  induction c using WithTop.recTopCoe with
  | top => simp
  | coe c =>
    simp only [← WithTop.coe_add, WithTop.coe_le_coe]
    exact sub_le_iff_le_add'.symm

@[simp] theorem contains_shift (d : Time) (I : Interval) (t : Time) :
    (point d * I).Contains t ↔ I.Contains (t - d) := by
  simp only [Contains, Prod.fst_mul, Prod.snd_mul, point, finite, Tropical.untrop_mul,
    Tropical.untrop_trop, coe_le_shift]
  rfl

@[simp] theorem finite_mul (a b c d : Time) :
    finite a b * finite c d = finite (a + c) (b + d) := by
  apply Prod.ext
  · apply Tropical.untrop_injective
    simp [finite, ← WithTop.coe_add]
  · apply Tropical.untrop_injective
    simp [finite, ← WithTop.coe_add]

@[simp] theorem point_mul (a b : Time) : point a * point b = point (a + b) :=
  finite_mul a a b b

@[simp] theorem point_zero : point 0 = (1 : Interval) := by
  apply Prod.ext <;> apply Tropical.untrop_injective <;> simp [point, finite]

theorem finite_add (a b c d : Time) :
    finite a b + finite c d = finite (max a c) (min b d) := by
  apply Prod.ext
  · apply Tropical.untrop_injective
    simp [finite, ← WithTop.coe_min]
  · apply Tropical.untrop_injective
    simp [finite, ← WithTop.coe_min]

theorem empty_of_inverted {lo hi : Time} (h : hi < lo) :
    ∀ t, ¬ (finite lo hi).Contains t := by
  intro t ht
  rw [contains_finite] at ht
  exact (not_le_of_gt h) (ht.1.trans ht.2)

/-- A retained negative width can be repaired by an input stability width. -/
theorem empty_product_counterexample :
    (∀ t, ¬ (finite 1 0).Contains t) ∧
      (finite 1 0 * finite 0 2).Contains 1 := by
  constructor
  · exact empty_of_inverted (by norm_num)
  · simp

/-- The full semiring laws are inherited, rather than postulated anew. -/
theorem mul_distributes (I J K : Interval) : I * (J + K) = I * J + I * K :=
  mul_add I J K

theorem add_idempotent (I : Interval) : I + I = I := by
  apply Prod.ext <;> apply Tropical.untrop_injective <;> simp

end Interval
end Applications.Timing
