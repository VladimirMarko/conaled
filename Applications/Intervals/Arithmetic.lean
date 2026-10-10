import SquareKit.FirstOrder
import SquareKit.Arithmetic
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Rational interval analysis with a relational compiler theorem

The implementation uses the four endpoint products, exactly and without
floating-point rounding. Its theorem is enclosure, never equality with an
image set. No well-formedness assumption is needed: a reversed interval has
no related point. The dependency-loss example is itself proved in Lean.
-/
namespace IntervalAnalysis

structure Interval where
  lo : ℚ
  hi : ℚ
  deriving DecidableEq, Repr

def Contains (I : Interval) (x : ℚ) : Prop := I.lo ≤ x ∧ x ≤ I.hi

def singleton (x : ℚ) : Interval := ⟨x, x⟩
def add (I J : Interval) : Interval := ⟨I.lo + J.lo, I.hi + J.hi⟩
def neg (I : Interval) : Interval := ⟨-I.hi, -I.lo⟩
def mul (I J : Interval) : Interval :=
  ⟨min (min (I.lo * J.lo) (I.lo * J.hi)) (min (I.hi * J.lo) (I.hi * J.hi)),
   max (max (I.lo * J.lo) (I.lo * J.hi)) (max (I.hi * J.lo) (I.hi * J.hi))⟩

theorem singleton_contains (x : ℚ) : Contains (singleton x) x := ⟨le_rfl, le_rfl⟩

theorem add_contains {I J : Interval} {x y : ℚ} (hx : Contains I x) (hy : Contains J y) :
    Contains (add I J) (x + y) := ⟨add_le_add hx.1 hy.1, add_le_add hx.2 hy.2⟩

theorem neg_contains {I : Interval} {x : ℚ} (hx : Contains I x) :
    Contains (neg I) (-x) := ⟨neg_le_neg hx.2, neg_le_neg hx.1⟩

private theorem mul_bounds {l h x : ℚ} (hx : l ≤ x ∧ x ≤ h) (y : ℚ) :
    min (l * y) (h * y) ≤ x * y ∧ x * y ≤ max (l * y) (h * y) := by
  by_cases hy : 0 ≤ y
  · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_right hx.1 hy),
      (mul_le_mul_of_nonneg_right hx.2 hy).trans (le_max_right _ _)⟩
  · have hy' : y ≤ 0 := le_of_not_ge hy
    exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_right hx.2 hy'),
      (mul_le_mul_of_nonpos_right hx.1 hy').trans (le_max_left _ _)⟩

theorem mul_contains {I J : Interval} {x y : ℚ} (hx : Contains I x) (hy : Contains J y) :
    Contains (mul I J) (x * y) := by
  have hxy := mul_bounds hx y
  have hl : min (I.lo * J.lo) (I.lo * J.hi) ≤ I.lo * y ∧
      I.lo * y ≤ max (I.lo * J.lo) (I.lo * J.hi) := by
    simpa only [mul_comm] using mul_bounds hy I.lo
  have hh : min (I.hi * J.lo) (I.hi * J.hi) ≤ I.hi * y ∧
      I.hi * y ≤ max (I.hi * J.lo) (I.hi * J.hi) := by
    simpa only [mul_comm] using mul_bounds hy I.hi
  constructor
  · exact (le_min ((min_le_left _ _).trans hl.1)
        ((min_le_right _ _).trans hh.1)).trans hxy.1
  · exact hxy.2.trans (max_le (hl.2.trans (le_max_left _ _))
        (hh.2.trans (le_max_right _ _)))

@[reducible] def representation : Relational.RelRep := ⟨Interval, ℚ, Contains⟩

def addSquare : Relational.RelSquare (Relational.product representation representation) representation :=
  ⟨fun p => add p.1 p.2, fun p => p.1 + p.2, fun h => add_contains h.1 h.2⟩

def mulSquare : Relational.RelSquare (Relational.product representation representation) representation :=
  ⟨fun p => mul p.1 p.2, fun p => p.1 * p.2, fun h => mul_contains h.1 h.2⟩

def negSquare : Relational.RelSquare representation representation :=
  ⟨neg, Neg.neg, neg_contains⟩

def primitives : FirstOrderRelations.Primitives representation Arithmetic.Prim
    (@Arithmetic.meaning ℚ _) where
  impl := fun {a b} p => match p with
    | .literal n => fun _ => singleton n
    | .add => fun p => add p.1 p.2
    | .mul => fun p => mul p.1 p.2
    | .neg => fun x => neg x
  correct := by
    intro a b p r s h
    cases p with
    | literal n => exact singleton_contains n
    | add => exact add_contains h.1 h.2
    | mul => exact mul_contains h.1 h.2
    | neg => exact neg_contains h

def compile {Γ a} (t : FirstOrderCompiler.Term Arithmetic.Prim Γ a) :=
  FirstOrderRelations.compileRelation representation primitives t

theorem compile_contains {Γ a} (t : FirstOrderCompiler.Term Arithmetic.Prim Γ a)
    {box : (FirstOrderRelations.encoding representation (FirstOrderCompiler.context Γ)).R}
    {ρ : FirstOrderCompiler.Val ℚ (FirstOrderCompiler.context Γ)}
    (h : (FirstOrderRelations.encoding representation (FirstOrderCompiler.context Γ)).Rel box ρ) :
    (FirstOrderRelations.encoding representation a).Rel ((compile t).impl box)
      (FirstOrderCompiler.eval Arithmetic.meaning t ρ) :=
  FirstOrderRelations.compile_preserves representation primitives t h

/-- A single shared source term can be enclosed after arbitrary compilation. -/
theorem shared_contains (I J : Interval) (x y : ℚ) (hx : Contains I x) (hy : Contains J y) :
    Contains ((compile Arithmetic.shared).impl ((), (I, J))) ((x*y)*(x*y)+x) :=
  compile_contains Arithmetic.shared (box := ((), (I, J))) (ρ := ((), (x, y)))
    ⟨True.intro, hx, hy⟩

def unitBox : Interval := ⟨-1, 1⟩

theorem point_cancellation (x : ℚ) : x + -x = 0 := add_neg_cancel x

theorem interval_cancellation_is_wider :
    add unitBox (neg unitBox) = ⟨-2, 2⟩ ∧
    add unitBox (neg unitBox) ≠ singleton 0 := by
  constructor
  · norm_num [add, unitBox, neg]
  · intro h
    have hl := congrArg Interval.lo h
    norm_num [add, unitBox, neg, singleton] at hl

/-- Function relations still support application without choosing a point from a box. -/
def applySquare : Relational.RelSquare
    (Relational.product (Relational.exponential representation representation) representation)
    representation := Relational.evaluation _ _

end IntervalAnalysis
