import SquareKit.NonnegativeArithmetic
import Applications.Intervals.Arithmetic
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Rat.Cast.Order

/-!
# Real-point enclosure by the existing rational interval operations

The endpoints and operations are the existing rational ones. The relation here
observes real points, so it also applies to irrational values. Arbitrary related
intervals may have negative endpoints; no endpoint-sign invariant is assumed.
-/

namespace IntervalAnalysis.Exact

def ContainsReal (I : Interval) (x : ℝ) : Prop :=
  (I.lo : ℝ) ≤ x ∧ x ≤ (I.hi : ℝ)

theorem containsReal_rat_iff {I : Interval} {x : ℚ} :
    ContainsReal I (x : ℝ) ↔ IntervalAnalysis.Contains I x := by
  simp only [ContainsReal, IntervalAnalysis.Contains, Rat.cast_le]

theorem singleton_containsReal (x : ℚ) :
    ContainsReal (IntervalAnalysis.singleton x) (x : ℝ) :=
  ⟨le_rfl, le_rfl⟩

theorem add_containsReal {I J : Interval} {x y : ℝ}
    (hx : ContainsReal I x) (hy : ContainsReal J y) :
    ContainsReal (IntervalAnalysis.add I J) (x + y) := by
  change (((I.lo + J.lo : ℚ) : ℝ) ≤ x + y) ∧
    (x + y ≤ ((I.hi + J.hi : ℚ) : ℝ))
  simpa only [Rat.cast_add] using
    And.intro (add_le_add hx.1 hy.1) (add_le_add hx.2 hy.2)

private theorem real_mul_bounds {l h x : ℝ} (hx : l ≤ x ∧ x ≤ h) (y : ℝ) :
    min (l * y) (h * y) ≤ x * y ∧ x * y ≤ max (l * y) (h * y) := by
  by_cases hy : 0 ≤ y
  · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_right hx.1 hy),
      (mul_le_mul_of_nonneg_right hx.2 hy).trans (le_max_right _ _)⟩
  · have hy' : y ≤ 0 := le_of_not_ge hy
    exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_right hx.2 hy'),
      (mul_le_mul_of_nonpos_right hx.1 hy').trans (le_max_left _ _)⟩

theorem mul_containsReal {I J : Interval} {x y : ℝ}
    (hx : ContainsReal I x) (hy : ContainsReal J y) :
    ContainsReal (IntervalAnalysis.mul I J) (x * y) := by
  have hxy := real_mul_bounds hx y
  have hl : min ((I.lo : ℝ) * J.lo) ((I.lo : ℝ) * J.hi) ≤ (I.lo : ℝ) * y ∧
      (I.lo : ℝ) * y ≤ max ((I.lo : ℝ) * J.lo) ((I.lo : ℝ) * J.hi) := by
    simpa only [mul_comm] using real_mul_bounds hy (I.lo : ℝ)
  have hh : min ((I.hi : ℝ) * J.lo) ((I.hi : ℝ) * J.hi) ≤ (I.hi : ℝ) * y ∧
      (I.hi : ℝ) * y ≤ max ((I.hi : ℝ) * J.lo) ((I.hi : ℝ) * J.hi) := by
    simpa only [mul_comm] using real_mul_bounds hy (I.hi : ℝ)
  simp only [ContainsReal, IntervalAnalysis.mul, Rat.cast_min, Rat.cast_max, Rat.cast_mul]
  constructor
  · exact (le_min ((min_le_left _ _).trans hl.1)
        ((min_le_right _ _).trans hh.1)).trans hxy.1
  · exact hxy.2.trans (max_le (hl.2.trans (le_max_left _ _))
        (hh.2.trans (le_max_right _ _)))

end IntervalAnalysis.Exact
/-! Optional intervals preserve exact validity and use the existing rational operations. -/

namespace IntervalAnalysis.Exact
open FirstOrderCompiler
open SquareKit.NonnegativeArithmetic (Value Prim valueMeaning strictAdd strictMul)
open scoped NNReal

/-- Optional rational boxes preserve exactly the validity of a partial value.
For finite values the contract is enclosure, without raw lower attainment. -/
def Rel : Option Interval → Value → Prop
  | none, none => True
  | some I, some x => ContainsReal I (x : ℝ)
  | _, _ => False

@[simp] theorem rel_none_iff (v : SquareKit.NonnegativeArithmetic.Value) :
    Rel none v ↔ v = ⊥ := by
  cases v with
  | none => exact ⟨fun _ => rfl, fun _ => True.intro⟩
  | some v => exact ⟨False.elim, fun h => WithBot.coe_ne_bot h⟩

@[simp] theorem rel_bot_iff (I : Option Interval) : Rel I ⊥ ↔ I = none := by
  cases I <;> simp [Rel]

@[simp] theorem rel_some_coe_iff (I : Interval) (x : ℝ≥0) :
    Rel (some I) (x : Value) ↔ ContainsReal I (x : ℝ) := Iff.rfl

abbrev representation : Relational.RelRep :=
  ⟨Option Interval, Value, Rel⟩

theorem rel_add {I J : Option Interval} {x y : Value}
    (hx : Rel I x) (hy : Rel J y) :
    Rel (Option.map₂ IntervalAnalysis.add I J) (strictAdd x y) := by
  cases x with
  | none =>
      have hI : I = none := (rel_bot_iff I).mp hx
      subst I
      exact True.intro
  | some x =>
      cases I with
      | none => exact False.elim hx
      | some I =>
          cases y with
          | none =>
              have hJ : J = none := (rel_bot_iff J).mp hy
              subst J
              exact True.intro
          | some y =>
              cases J with
              | none => exact False.elim hy
              | some J =>
                  change ContainsReal (IntervalAnalysis.add I J) ((x + y : ℝ≥0) : ℝ)
                  simpa only [NNReal.coe_add] using add_containsReal hx hy

theorem rel_mul {I J : Option Interval} {x y : Value}
    (hx : Rel I x) (hy : Rel J y) :
    Rel (Option.map₂ IntervalAnalysis.mul I J) (strictMul x y) := by
  cases x with
  | none =>
      have hI : I = none := (rel_bot_iff I).mp hx
      subst I
      exact True.intro
  | some x =>
      cases I with
      | none => exact False.elim hx
      | some I =>
          cases y with
          | none =>
              have hJ : J = none := (rel_bot_iff J).mp hy
              subst J
              exact True.intro
          | some y =>
              cases J with
              | none => exact False.elim hy
              | some J =>
                  change ContainsReal (IntervalAnalysis.mul I J) ((x * y : ℝ≥0) : ℝ)
                  simpa only [NNReal.coe_mul] using mul_containsReal hx hy

def rationalInterval (r : ℚ) : Option Interval :=
  if 0 ≤ r then some (IntervalAnalysis.singleton r) else none

def logarithmInterval (q n : ℕ) : Option Interval :=
  if n = 0 then none else
    some ⟨(Nat.log2 (n ^ q) : ℚ) / (q : ℚ),
      ((Nat.log2 (n ^ q) + 1 : ℕ) : ℚ) / (q : ℚ)⟩

def squareRootInterval (q n : ℕ) : Option Interval :=
  some ⟨(Nat.sqrt (n * q * q) : ℚ) / (q : ℚ),
    ((Nat.sqrt (n * q * q) + 1 : ℕ) : ℚ) / (q : ℚ)⟩

def exponentiatedLogarithmInterval (q n : ℕ) : Option Interval :=
  if n = 0 then none else
    some ⟨((n * q - 1 : ℕ) : ℚ) / (q : ℚ), (n : ℚ)⟩

/-- Actual rational implementation of the common six primitive families.
Its relation certificate will be supplied for positive q from the shared
atom correspondence and attained precision bounds. -/
def intervalPrimitive (q : ℕ) : {a b : Ty} → Prim a b →
    (FirstOrderRelations.encoding representation a).R →
    (FirstOrderRelations.encoding representation b).R
  | _, _, .rational r, _ => rationalInterval r
  | _, _, .logarithm n, _ => logarithmInterval q n
  | _, _, .squareRoot n, _ => squareRootInterval q n
  | _, _, .exponentiatedLogarithm n, _ => exponentiatedLogarithmInterval q n
  | _, _, .add, x => Option.map₂ IntervalAnalysis.add x.1 x.2
  | _, _, .mul, x => Option.map₂ IntervalAnalysis.mul x.1 x.2

end IntervalAnalysis.Exact
/-! Atom certificates and real-point enclosure through the existing typed compiler. -/

namespace IntervalAnalysis.Exact
open FirstOrderCompiler
open SquareKit.NonnegativeArithmetic
  (Value Prim valueMeaning RawBounds rationalValue logarithmValue squareRootValue
   exponentiatedLogarithmValue logApprox rootApprox expLogApprox)
open scoped NNReal

/-- Actual attained raw bounds give an enclosing optional interval.
This does not assert attainment for arbitrary related input boxes. -/
theorem rel_some_of_rawBounds {A : Set ℚ} {v : Value} {lo hi : ℚ}
    (h : SquareKit.NonnegativeArithmetic.Rel A v) (hb : RawBounds A lo hi) :
    Rel (some ⟨lo, hi⟩) v := by
  obtain ⟨x, rfl, hlo, hhi⟩ := SquareKit.NonnegativeArithmetic.rel_bounds_real h hb
  exact ⟨hlo, hhi⟩

theorem rationalInterval_related (r : ℚ) :
    Rel (rationalInterval r) (rationalValue r) := by
  by_cases hr : 0 ≤ r
  · simp only [rationalInterval, ite_eq_left hr]
    apply rel_some_of_rawBounds (SquareKit.NonnegativeArithmetic.rel_rational r)
    exact ⟨⟨hr, le_rfl⟩, fun _ hx => hx.2⟩
  · simp [rationalInterval, rationalValue, hr, Rel]

theorem logarithmInterval_related (q n : ℕ) (hq : 0 < q) :
    Rel (logarithmInterval q n) (logarithmValue n) := by
  by_cases hn : n = 0
  · subst n
    simp [logarithmInterval, logarithmValue, Rel]
  · have hn' : 1 ≤ n := Nat.pos_of_ne_zero hn
    simp only [logarithmInterval, ite_eq_right hn]
    exact rel_some_of_rawBounds (SquareKit.NonnegativeArithmetic.rel_logarithm n)
      (SquareKit.NonnegativeArithmetic.logApprox_precision_bounds n q hn' hq)

theorem squareRootInterval_related (q n : ℕ) (hq : 0 < q) :
    Rel (squareRootInterval q n) (squareRootValue n) :=
  rel_some_of_rawBounds (SquareKit.NonnegativeArithmetic.rel_squareRoot n)
    (SquareKit.NonnegativeArithmetic.rootApprox_precision_bounds n q hq)

theorem exponentiatedLogarithmInterval_related (q n : ℕ) (hq : 0 < q) :
    Rel (exponentiatedLogarithmInterval q n) (exponentiatedLogarithmValue n) := by
  by_cases hn : n = 0
  · subst n
    simp [exponentiatedLogarithmInterval, exponentiatedLogarithmValue, Rel]
  · have hn' : 0 < n := Nat.pos_of_ne_zero hn
    have hprod : 0 < n * q := Nat.mul_pos hn' hq
    have hnum : n * q - 1 < n * q := Nat.sub_lt hprod (by decide)
    simp only [exponentiatedLogarithmInterval, ite_eq_right hn]
    apply rel_some_of_rawBounds
      (SquareKit.NonnegativeArithmetic.rel_exponentiatedLogarithm n)
    exact ⟨SquareKit.NonnegativeArithmetic.expLogApprox_fraction_lt n (n * q - 1) q hq hnum,
      fun _ ha => SquareKit.NonnegativeArithmetic.expLogApprox_upper n ha⟩

def primitives (q : ℕ) (hq : 0 < q) :
    FirstOrderRelations.Primitives representation Prim valueMeaning where
  impl := intervalPrimitive q
  correct := by
    intro a b p r s h
    cases p with
    | rational c => exact rationalInterval_related c
    | logarithm n => exact logarithmInterval_related q n hq
    | squareRoot n => exact squareRootInterval_related q n hq
    | exponentiatedLogarithm n => exact exponentiatedLogarithmInterval_related q n hq
    | add => exact rel_add h.1 h.2
    | mul => exact rel_mul h.1 h.2

noncomputable def compile (q : ℕ) (hq : 0 < q) {Γ : Ctx} {a : Ty}
    (t : Term Prim Γ a) :=
  FirstOrderRelations.compileRelation representation (primitives q hq) t

/-- Existing relational compilation relates the actual interval implementation
to the common partial-value semantics for every typed term and environment. -/
theorem compile_contains (q : ℕ) (hq : 0 < q) {Γ : Ctx} {a : Ty}
    (t : Term Prim Γ a)
    {box : (FirstOrderRelations.encoding representation (context Γ)).R}
    {ρ : Val Value (context Γ)}
    (h : (FirstOrderRelations.encoding representation (context Γ)).Rel box ρ) :
    (FirstOrderRelations.encoding representation a).Rel ((compile q hq t).impl box)
      (FirstOrderCompiler.eval valueMeaning t ρ) :=
  FirstOrderRelations.compile_preserves representation (primitives q hq) t h

@[simp] theorem compile_rational (q : ℕ) (hq : 0 < q) {Γ : Ctx} (r : ℚ)
    (box : (FirstOrderRelations.encoding representation (context Γ)).R) :
    ((compile q hq (SquareKit.NonnegativeArithmetic.rational (Γ := Γ) r)).impl box) =
      rationalInterval r := rfl

@[simp] theorem compile_logarithm (q : ℕ) (hq : 0 < q) {Γ : Ctx} (n : ℕ)
    (box : (FirstOrderRelations.encoding representation (context Γ)).R) :
    ((compile q hq (SquareKit.NonnegativeArithmetic.logarithm (Γ := Γ) n)).impl box) =
      logarithmInterval q n := rfl

@[simp] theorem compile_squareRoot (q : ℕ) (hq : 0 < q) {Γ : Ctx} (n : ℕ)
    (box : (FirstOrderRelations.encoding representation (context Γ)).R) :
    ((compile q hq (SquareKit.NonnegativeArithmetic.squareRoot (Γ := Γ) n)).impl box) =
      squareRootInterval q n := rfl

@[simp] theorem compile_exponentiatedLogarithm (q : ℕ) (hq : 0 < q) {Γ : Ctx} (n : ℕ)
    (box : (FirstOrderRelations.encoding representation (context Γ)).R) :
    ((compile q hq
      (SquareKit.NonnegativeArithmetic.exponentiatedLogarithm (Γ := Γ) n)).impl box) =
      exponentiatedLogarithmInterval q n := rfl

@[simp] theorem compile_add (q : ℕ) (hq : 0 < q) {Γ : Ctx}
    (e f : Term Prim Γ .base)
    (box : (FirstOrderRelations.encoding representation (context Γ)).R) :
    ((compile q hq (SquareKit.NonnegativeArithmetic.add e f)).impl box) =
      Option.map₂ IntervalAnalysis.add ((compile q hq e).impl box)
        ((compile q hq f).impl box) := rfl

@[simp] theorem compile_mul (q : ℕ) (hq : 0 < q) {Γ : Ctx}
    (e f : Term Prim Γ .base)
    (box : (FirstOrderRelations.encoding representation (context Γ)).R) :
    ((compile q hq (SquareKit.NonnegativeArithmetic.mul e f)).impl box) =
      Option.map₂ IntervalAnalysis.mul ((compile q hq e).impl box)
        ((compile q hq f).impl box) := rfl

@[simp] theorem compile_letE (q : ℕ) (hq : 0 < q) {Γ : Ctx} {a b : Ty}
    (e : Term Prim Γ a) (body : Term Prim (a :: Γ) b)
    (box : (FirstOrderRelations.encoding representation (context Γ)).R) :
    ((compile q hq (.letE e body)).impl box) =
      (compile q hq body).impl (box, (compile q hq e).impl box) := rfl

end IntervalAnalysis.Exact
