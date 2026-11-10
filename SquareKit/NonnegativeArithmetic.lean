import Mathlib.Order.Bounds.Basic
import Mathlib.Algebra.Order.Group.Pointwise.Bounds
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.NumberTheory.Real.Irrational
import SquareKit.FirstOrder
import SquareKit.DiscreteScales
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Topology.Instances.Rat
import Mathlib.Order.UpperLower.Closure
import Mathlib.Order.WithBot

/-!
# Strict nonnegative arithmetic through the existing typed compiler

Raw rational observations retain finite natural witnesses. Values use the
existing ordered type WithBot NNReal; explicit strict operations preserve
invalidity even when the other operand is valid zero. Ordinary rational closure
and actual lower attainment are separate contracts.
-/

open scoped NNReal

namespace SquareKit.NonnegativeArithmetic
open FirstOrderCompiler

noncomputable section

abbrev Value := WithBot ℝ≥0

def logApprox (n : ℕ) : Set ℚ :=
  {a | ∃ p q : ℕ, 0 < q ∧ a = (p : ℚ) / (q : ℚ) ∧ 2 ^ p ≤ n ^ q}

def rootApprox (n : ℕ) : Set ℚ :=
  {a | ∃ p q : ℕ, 0 < q ∧ a = (p : ℚ) / (q : ℚ) ∧ p * p ≤ n * q * q}

def expLogApprox (n : ℕ) : Set ℚ :=
  {a | ∃ p q r s : ℕ, 0 < q ∧ 0 < s ∧ a = (r : ℚ) / (s : ℚ) ∧
    2 ^ p ≤ n ^ q ∧ r ^ q ≤ 2 ^ p * s ^ q}

def closedSection (A : Set ℚ) : Set ℚ :=
  closure (lowerClosure A : Set ℚ)

def RawBounds (A : Set ℚ) (lo hi : ℚ) : Prop :=
  lo ∈ A ∧ A ⊆ Set.Iic hi

def Rel (A : Set ℚ) : Value → Prop
  | none => A = ∅
  | some v => (∀ q ∈ A, 0 ≤ q) ∧
      ∀ q : ℚ, q ∈ closedSection A ↔ (q : ℝ) ≤ (v : ℝ)

def strictAdd (v w : Value) : Value :=
  WithBot.map₂ (fun x y : ℝ≥0 => x + y) v w

def strictMul (v w : Value) : Value :=
  WithBot.map₂ (fun x y : ℝ≥0 => x * y) v w

def rationalValue (r : ℚ) : Value :=
  if 0 ≤ r then (Real.toNNReal (r : ℝ) : Value) else ⊥

def logarithmValue (n : ℕ) : Value :=
  if n = 0 then ⊥ else (Real.toNNReal (Real.logb 2 (n : ℝ)) : Value)

def squareRootValue (n : ℕ) : Value :=
  (NNReal.sqrt (n : ℝ≥0) : Value)

def exponentiatedLogarithmValue (n : ℕ) : Value :=
  if n = 0 then ⊥ else ((n : ℝ≥0) : Value)

inductive Prim : Ty → Ty → Type
  | rational : ℚ → Prim .unit .base
  | logarithm : ℕ → Prim .unit .base
  | squareRoot : ℕ → Prim .unit .base
  | exponentiatedLogarithm : ℕ → Prim .unit .base
  | add : Prim (.prod .base .base) .base
  | mul : Prim (.prod .base .base) .base

def valueMeaning : {a b : Ty} → Prim a b → Val Value a → Val Value b
  | _, _, .rational r, _ => rationalValue r
  | _, _, .logarithm n, _ => logarithmValue n
  | _, _, .squareRoot n, _ => squareRootValue n
  | _, _, .exponentiatedLogarithm n, _ => exponentiatedLogarithmValue n
  | _, _, .add, x => strictAdd x.1 x.2
  | _, _, .mul, x => strictMul x.1 x.2

abbrev representation : Relational.RelRep :=
  ⟨Set ℚ, Value, Rel⟩

def rawPrimitive : {a b : Ty} → Prim a b →
    (FirstOrderRelations.encoding representation a).R →
    (FirstOrderRelations.encoding representation b).R
  | _, _, .rational r, _ => Set.Icc 0 r
  | _, _, .logarithm n, _ => logApprox n
  | _, _, .squareRoot n, _ => rootApprox n
  | _, _, .exponentiatedLogarithm n, _ => expLogApprox n
  | _, _, .add, x => Set.image2 (· + ·) x.1 x.2
  | _, _, .mul, x => Set.image2 (· * ·) x.1 x.2

def rational {Γ : Ctx} (r : ℚ) : Term Prim Γ .base :=
  .prim (.rational r) .unit

def logarithm {Γ : Ctx} (n : ℕ) : Term Prim Γ .base :=
  .prim (.logarithm n) .unit

def squareRoot {Γ : Ctx} (n : ℕ) : Term Prim Γ .base :=
  .prim (.squareRoot n) .unit

def exponentiatedLogarithm {Γ : Ctx} (n : ℕ) : Term Prim Γ .base :=
  .prim (.exponentiatedLogarithm n) .unit

def add {Γ : Ctx} (e f : Term Prim Γ .base) : Term Prim Γ .base :=
  .prim .add (.pair e f)

def mul {Γ : Ctx} (e f : Term Prim Γ .base) : Term Prim Γ .base :=
  .prim .mul (.pair e f)

def scale {Γ : Ctx} (k : ℕ) (e : Term Prim Γ .base) : Term Prim Γ .base :=
  mul (rational (k : ℚ)) e

abbrev ClosedTerm := Term Prim [] .base

def valueTerm {Γ : Ctx} {a : Ty} (t : Term Prim Γ a) :
    Val Value (context Γ) → Val Value a :=
  FirstOrderCompiler.eval valueMeaning t

def value (t : ClosedTerm) : Value := valueTerm t ()

end
end SquareKit.NonnegativeArithmetic
/-! Finite natural witnesses for the raw atom sets. -/

set_option autoImplicit false
set_option warningAsError true

namespace SquareKit.NonnegativeArithmetic

/-- Ordinary rational division is nonnegative for natural inputs, including q = 0. -/
theorem nat_fraction_nonneg (p q : ℕ) : 0 ≤ (p : ℚ) / (q : ℚ) :=
  div_nonneg (Nat.cast_nonneg p) (Nat.cast_nonneg q)

/-- Cross multiplication retains both strictly positive denominator premises. -/
theorem nat_fraction_le_iff (p q r s : ℕ) (hq : 0 < q) (hs : 0 < s) :
    (p : ℚ) / (q : ℚ) ≤ (r : ℚ) / (s : ℚ) ↔ p * s ≤ r * q := by
  rw [div_le_div_iff₀ (show (0 : ℚ) < q by exact_mod_cast hq)
    (show (0 : ℚ) < s by exact_mod_cast hs)]
  norm_cast

theorem nat_fraction_one (p : ℕ) : (p : ℚ) / (1 : ℚ) = (p : ℚ) := div_one _

/-- This identity also holds at denominator zero, without a positivity assumption. -/
theorem nat_fraction_successor (p q : ℕ) :
    ((p + 1 : ℕ) : ℚ) / (q : ℚ) = (p : ℚ) / (q : ℚ) + 1 / (q : ℚ) := by
  rw [Nat.cast_add, Nat.cast_one, add_div]

/-- Every nonnegative rational admits natural numerator and positive denominator. -/
theorem exists_nat_fraction (a : ℚ) (ha : 0 ≤ a) :
    ∃ p q : ℕ, 0 < q ∧ a = (p : ℚ) / (q : ℚ) := by
  refine ⟨a.num.natAbs, a.den, a.den_pos, ?_⟩
  have hnum : (a.num.natAbs : ℤ) = a.num :=
    Int.natAbs_of_nonneg (Rat.num_nonneg.mpr ha)
  have hnum' : (a.num.natAbs : ℚ) = (a.num : ℚ) := by
    simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z : ℚ)) hnum
  rw [hnum']
  exact a.num_div_den.symm

/-- Finite representation invariance does not require the logarithm input to be positive. -/
theorem log_fraction_invariant (n p q r s : ℕ) (hq : 0 < q) (hs : 0 < s)
    (he : p * s = r * q) : 2 ^ p ≤ n ^ q ↔ 2 ^ r ≤ n ^ s := by
  constructor
  · intro h
    have hp := Nat.pow_le_pow_left h s
    rw [← Nat.pow_mul, ← Nat.pow_mul, he, Nat.mul_comm q s,
      Nat.pow_mul 2 r q, Nat.pow_mul n s q] at hp
    exact (Nat.pow_le_pow_iff_left (by omega : q ≠ 0)).mp hp
  · intro h
    have hp := Nat.pow_le_pow_left h q
    rw [← Nat.pow_mul, ← Nat.pow_mul, ← he, Nat.mul_comm s q,
      Nat.pow_mul 2 p s, Nat.pow_mul n q s] at hp
    exact (Nat.pow_le_pow_iff_left (by omega : s ≠ 0)).mp hp

theorem root_fraction_invariant (n p q r s : ℕ) (hq : 0 < q) (hs : 0 < s)
    (he : p * s = r * q) : p * p ≤ n * q * q ↔ r * r ≤ n * s * s := by
  constructor
  · intro h
    have hm := Nat.mul_le_mul_right (s * s) h
    have he2 := congrArg (fun x : ℕ => x * x) he
    have hx : (r * r) * (q * q) ≤ (n * s * s) * (q * q) := by nlinarith
    exact Nat.le_of_mul_le_mul_right hx (Nat.mul_pos hq hq)
  · intro h
    have hm := Nat.mul_le_mul_right (q * q) h
    have he2 := congrArg (fun x : ℕ => x * x) he
    have hx : (p * p) * (s * s) ≤ (n * q * q) * (s * s) := by nlinarith
    exact Nat.le_of_mul_le_mul_right hx (Nat.mul_pos hs hs)

theorem logApprox_nonneg {n : ℕ} {a : ℚ} (ha : a ∈ logApprox n) : 0 ≤ a := by
  rcases ha with ⟨p, q, _, rfl, _⟩
  exact nat_fraction_nonneg p q

theorem rootApprox_nonneg {n : ℕ} {a : ℚ} (ha : a ∈ rootApprox n) : 0 ≤ a := by
  rcases ha with ⟨p, q, _, rfl, _⟩
  exact nat_fraction_nonneg p q

theorem expLogApprox_nonneg {n : ℕ} {a : ℚ} (ha : a ∈ expLogApprox n) : 0 ≤ a := by
  rcases ha with ⟨_, _, r, s, _, _, rfl, _, _⟩
  exact nat_fraction_nonneg r s

@[simp] theorem logApprox_zero : logApprox 0 = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro a ⟨p, q, hq, _, hp⟩
  have hp0 : 0 < 2 ^ p := Nat.two_pow_pos p
  rw [zero_pow (Nat.ne_of_gt hq)] at hp
  omega

@[simp] theorem expLogApprox_zero : expLogApprox 0 = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro a ⟨p, q, _, _, hq, _, _, hp, _⟩
  have hp0 : 0 < 2 ^ p := Nat.two_pow_pos p
  rw [zero_pow (Nat.ne_of_gt hq)] at hp
  omega

@[simp] theorem rootApprox_zero : rootApprox 0 = {0} := by
  ext a
  constructor
  · rintro ⟨p, q, _, ha, hp⟩
    have hp0 : p = 0 := by nlinarith
    simp only [hp0, Nat.cast_zero, zero_div] at ha
    exact Set.mem_singleton_iff.mpr ha
  · intro ha
    have ha0 : a = 0 := Set.mem_singleton_iff.mp ha
    subst a
    exact ⟨0, 1, by decide, by simp, by simp⟩

/-- A supplied finite upper-power witness bounds every raw log approximant. -/
theorem logApprox_upper (n p q : ℕ) (hq : 0 < q) (hbound : n ^ q ≤ 2 ^ p)
    {a : ℚ} (ha : a ∈ logApprox n) : a ≤ (p : ℚ) / (q : ℚ) := by
  rcases ha with ⟨r, s, hs, rfl, hr⟩
  apply (nat_fraction_le_iff r s p q hs hq).mpr
  have hl := Nat.pow_le_pow_left hr q
  have hu := Nat.pow_le_pow_left hbound s
  have he : (n ^ s) ^ q = (n ^ q) ^ s := by
    rw [← Nat.pow_mul, ← Nat.pow_mul, Nat.mul_comm s q]
  rw [he] at hl
  have hm := Nat.le_trans hl hu
  rw [← Nat.pow_mul, ← Nat.pow_mul] at hm
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hm

/-- A supplied finite upper-square witness bounds every raw root approximant. -/
theorem rootApprox_upper (n p q : ℕ) (hq : 0 < q) (hbound : n * q * q ≤ p * p)
    {a : ℚ} (ha : a ∈ rootApprox n) : a ≤ (p : ℚ) / (q : ℚ) := by
  rcases ha with ⟨r, s, hs, rfl, hr⟩
  apply (nat_fraction_le_iff r s p q hs hq).mpr
  have hl := Nat.mul_le_mul_right (q * q) hr
  have hu := Nat.mul_le_mul_right (s * s) hbound
  have hsq : (r * q) * (r * q) ≤ (p * s) * (p * s) := by nlinarith
  by_cases h : r * q ≤ p * s
  · exact h
  · have hlt : p * s < r * q := by omega
    have hc := Nat.mul_self_lt_mul_self hlt
    omega

theorem logApprox_floor (n : ℕ) (hn : 1 ≤ n) : (n.log2 : ℚ) ∈ logApprox n := by
  refine ⟨n.log2, 1, by decide, by simp, ?_⟩
  simpa using Nat.log2_self_le (by omega : n ≠ 0)

theorem rootApprox_floor (n : ℕ) : (n.sqrt : ℚ) ∈ rootApprox n := by
  refine ⟨n.sqrt, 1, by decide, by simp, ?_⟩
  simpa using Nat.sqrt_le n

theorem logApprox_floor_upper (n : ℕ) {a : ℚ} (ha : a ∈ logApprox n) :
    a ≤ (n.log2 : ℚ) + 1 := by
  have hb : n ^ 1 ≤ 2 ^ (n.log2 + 1) := by
    simpa using (Nat.lt_log2_self (n := n)).le
  simpa only [Nat.cast_add, Nat.cast_one, div_one] using
    logApprox_upper n (n.log2 + 1) 1 (by decide) hb ha

theorem rootApprox_floor_upper (n : ℕ) {a : ℚ} (ha : a ∈ rootApprox n) :
    a ≤ (n.sqrt : ℚ) + 1 := by
  have hb : n * 1 * 1 ≤ (n.sqrt + 1) * (n.sqrt + 1) := by
    simpa using (Nat.lt_succ_sqrt n).le
  simpa only [Nat.cast_add, Nat.cast_one, div_one] using
    rootApprox_upper n (n.sqrt + 1) 1 (by decide) hb ha

theorem logApprox_power_upper (k : ℕ) {a : ℚ} (ha : a ∈ logApprox (2 ^ k)) :
    a ≤ (k : ℚ) := by
  simpa only [Nat.cast_one, div_one] using
    logApprox_upper (2 ^ k) k 1 (by decide) (by simp) ha

theorem rootApprox_square_upper (k : ℕ) {a : ℚ} (ha : a ∈ rootApprox (k * k)) :
    a ≤ (k : ℚ) := by
  simpa only [Nat.cast_one, div_one] using
    rootApprox_upper (k * k) k 1 (by decide) (by simp) ha

end SquareKit.NonnegativeArithmetic
/-! Exact real characterizations of the retained natural-fraction atom sets. -/

set_option autoImplicit false
set_option warningAsError true

namespace SquareKit.NonnegativeArithmetic

/-- A rational natural fraction is below the exact base-two logarithm precisely
when its finite integer power test holds. -/
theorem nat_fraction_le_logb_iff (n p q : ℕ) (hn : 1 ≤ n) (hq : 0 < q) :
    (((p : ℚ) / (q : ℚ) : ℚ) : ℝ) ≤ Real.logb 2 (n : ℝ) ↔
      2 ^ p ≤ n ^ q := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have htwo : (1 : ℝ) < 2 := by norm_num
  have hlog := Real.logb_le_logb htwo
    (pow_pos (show (0 : ℝ) < 2 by norm_num) p) (pow_pos hnR q)
  have hlog' : (p : ℝ) ≤ (q : ℝ) * Real.logb 2 (n : ℝ) ↔
      (2 : ℝ) ^ p ≤ (n : ℝ) ^ q := by
    simpa only [Real.logb_pow, Real.logb_self_eq_one htwo, mul_one] using hlog
  simp only [Rat.cast_div, Rat.cast_natCast]
  rw [div_le_iff₀ hqR, mul_comm]
  exact hlog'.trans (by norm_cast)

/-- The exact root comparison retains all natural radicands, including zero. -/
theorem nat_fraction_le_sqrt_iff (n p q : ℕ) (hq : 0 < q) :
    (((p : ℚ) / (q : ℚ) : ℚ) : ℝ) ≤ Real.sqrt (n : ℝ) ↔
      p * p ≤ n * q * q := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  simp only [Rat.cast_div, Rat.cast_natCast]
  rw [Real.le_sqrt
    (div_nonneg (Nat.cast_nonneg p) (Nat.cast_nonneg q)) (Nat.cast_nonneg n),
    div_pow, div_le_iff₀ (pow_pos hqR 2)]
  norm_cast
  simp only [pow_two, mul_assoc]

/-- Raw log observations are exactly the nonnegative rational observations below
the standard real logarithm, on the source's positive domain. -/
theorem mem_logApprox_iff (n : ℕ) (hn : 1 ≤ n) (a : ℚ) :
    a ∈ logApprox n ↔ 0 ≤ a ∧ (a : ℝ) ≤ Real.logb 2 (n : ℝ) := by
  constructor
  · rintro ⟨p, q, hq, rfl, hp⟩
    exact ⟨nat_fraction_nonneg p q, (nat_fraction_le_logb_iff n p q hn hq).mpr hp⟩
  · rintro ⟨ha0, ha⟩
    rcases exists_nat_fraction a ha0 with ⟨p, q, hq, rfl⟩
    exact ⟨p, q, hq, rfl, (nat_fraction_le_logb_iff n p q hn hq).mp ha⟩

/-- Every nonnegative rational query is covered; no chosen fraction presentation
or positive-radicand restriction remains in this public characterization. -/
theorem mem_rootApprox_iff (n : ℕ) (a : ℚ) :
    a ∈ rootApprox n ↔ 0 ≤ a ∧ (a : ℝ) ≤ Real.sqrt (n : ℝ) := by
  constructor
  · rintro ⟨p, q, hq, rfl, hp⟩
    exact ⟨nat_fraction_nonneg p q, (nat_fraction_le_sqrt_iff n p q hq).mpr hp⟩
  · rintro ⟨ha0, ha⟩
    rcases exists_nat_fraction a ha0 with ⟨p, q, hq, rfl⟩
    exact ⟨p, q, hq, rfl, (nat_fraction_le_sqrt_iff n p q hq).mp ha⟩

/-- The usual real inverse identity is used only on the source's valid domain. -/
theorem expLog_rpow_identity (n : ℕ) (hn : 1 ≤ n) :
    (2 : ℝ) ^ Real.logb 2 (n : ℝ) = (n : ℝ) := by
  exact Real.rpow_logb (by norm_num : (0 : ℝ) < 2)
    (by norm_num : (2 : ℝ) ≠ 1)
    (by exact_mod_cast (show 0 < n by omega))

end SquareKit.NonnegativeArithmetic
/-! Finite ExpLog witnesses, strict rational cofinality and exact upper bounds. -/

set_option autoImplicit false
set_option warningAsError true

namespace SquareKit.NonnegativeArithmetic

/-- A native specialization of the standard denominator-free Bernoulli bound. -/
theorem bernoulli_integer (a k : ℕ) : a ^ k * (a + k) ≤ a * (a + 1) ^ k := by
  cases k with
  | zero => simp
  | succ k =>
    have hb := pow_add_mul_le_add_pow (a := a) (b := 1)
      (Nat.zero_le a) (Nat.zero_le (2 * a + 1)) (k + 1)
    simp only [Nat.add_sub_cancel, Nat.cast_id, mul_one] at hb
    change a ^ (k + 1) * (a + (k + 1)) ≤ a * (a + 1) ^ (k + 1)
    calc
      a ^ (k + 1) * (a + (k + 1)) =
          a * (a ^ (k + 1) + (k + 1) * a ^ k) := by
        simp only [pow_succ]
        ring
      _ ≤ a * (a + 1) ^ (k + 1) := Nat.mul_le_mul_left a hb

theorem doubled_power_le_successor_power (a : ℕ) (ha : 0 < a) :
    2 * a ^ a ≤ (a + 1) ^ a := by
  have hb := bernoulli_integer a a
  apply Nat.le_of_mul_le_mul_left (c := a)
  · nlinarith
  · exact ha

/-- Every raw four-witness ExpLog approximation has the finite upper bound n. -/
theorem expLogApprox_upper (n : ℕ) {a : ℚ} (ha : a ∈ expLogApprox n) :
    a ≤ (n : ℚ) := by
  rcases ha with ⟨p, q, r, s, hq, hs, rfl, hp, hr⟩
  have hm := Nat.mul_le_mul_right (s ^ q) hp
  have hx : r ^ q ≤ (n * s) ^ q := by
    simpa only [Nat.mul_pow] using Nat.le_trans hr hm
  have hd := (Nat.pow_le_pow_iff_left (by omega : q ≠ 0)).mp hx
  have hfrac := (nat_fraction_le_iff r s n 1 hs (by decide)).mpr
    (by simpa only [mul_one] using hd)
  simpa only [Nat.cast_one, div_one] using hfrac

/-- Every strict rational natural-fraction lower bound is an actual raw member.
The positive-numerator construction uses symbolic p = log2(n^r), q = r. -/
theorem expLogApprox_fraction_lt (n r s : ℕ) (hs : 0 < s) (hr : r < n * s) :
    (r : ℚ) / (s : ℚ) ∈ expLogApprox n := by
  have hn : 0 < n := by
    by_contra h
    have hn0 : n = 0 := by omega
    simp only [hn0, zero_mul] at hr
    omega
  by_cases hr0 : r = 0
  · subst r
    refine ⟨0, 1, 0, s, by decide, hs, rfl, ?_, ?_⟩
    · simpa using (show 1 ≤ n by omega)
    · simp
  · have hrp : 0 < r := by omega
    have hb := doubled_power_le_successor_power r hrp
    have hm := Nat.pow_le_pow_left (show r + 1 ≤ n * s by omega) r
    have hpow : n ^ r < 2 * 2 ^ (n ^ r).log2 := by
      have h := Nat.lt_log2_self (n := n ^ r)
      rw [Nat.pow_succ] at h
      nlinarith
    have hmult := Nat.mul_lt_mul_of_pos_right hpow (Nat.pow_pos (n := r) hs)
    have hh : r ^ r ≤ 2 ^ (n ^ r).log2 * s ^ r := by
      rw [Nat.mul_pow] at hm
      have hle : 2 * r ^ r ≤ 2 * (2 ^ (n ^ r).log2 * s ^ r) := by nlinarith
      exact Nat.le_of_mul_le_mul_left hle (by decide)
    exact ⟨(n ^ r).log2, r, r, s, hrp, hs, rfl,
      Nat.log2_self_le (Nat.ne_of_gt (Nat.pow_pos hn)), hh⟩

/-- The strict-lower inclusion holds for every rational query; no particular
fraction representation remains in the public statement. -/
theorem expLogApprox_of_nonneg_lt (n : ℕ) {a : ℚ} (ha0 : 0 ≤ a)
    (ha : a < (n : ℚ)) : a ∈ expLogApprox n := by
  rcases exists_nat_fraction a ha0 with ⟨r, s, hs, rfl⟩
  have hsQ : (0 : ℚ) < s := by exact_mod_cast hs
  have hrQ : (r : ℚ) < (n : ℚ) * (s : ℚ) := (div_lt_iff₀ hsQ).mp ha
  have hr : r < n * s := by exact_mod_cast hrQ
  exact expLogApprox_fraction_lt n r s hs hr

end SquareKit.NonnegativeArithmetic
/-! Attained rational bounds and the specified finite-precision endpoints. -/

set_option autoImplicit false
set_option warningAsError true

namespace SquareKit.NonnegativeArithmetic

theorem rawBounds_rational (r : ℚ) (hr : 0 ≤ r) : RawBounds (Set.Icc 0 r) r r :=
  ⟨⟨hr, le_rfl⟩, fun _ hx => hx.2⟩

theorem rawBounds_log (n : ℕ) (hn : 1 ≤ n) :
    RawBounds (logApprox n) (n.log2 : ℚ) ((n.log2 : ℚ) + 1) :=
  ⟨logApprox_floor n hn, fun _ ha => logApprox_floor_upper n ha⟩

theorem rawBounds_root (n : ℕ) :
    RawBounds (rootApprox n) (n.sqrt : ℚ) ((n.sqrt : ℚ) + 1) :=
  ⟨rootApprox_floor n, fun _ ha => rootApprox_floor_upper n ha⟩

theorem rawBounds_log_power (k : ℕ) :
    RawBounds (logApprox (2 ^ k)) (k : ℚ) (k : ℚ) := by
  refine ⟨?_, fun _ ha => logApprox_power_upper k ha⟩
  exact ⟨k, 1, by decide, by simp, by simp⟩

theorem rawBounds_root_square (k : ℕ) :
    RawBounds (rootApprox (k * k)) (k : ℚ) (k : ℚ) := by
  refine ⟨?_, fun _ ha => rootApprox_square_upper k ha⟩
  exact ⟨k, 1, by decide, by simp, by simp⟩

/-- Set-image addition retains the actual lower members from both operands. -/
theorem rawBounds_image2_add {A B : Set ℚ} {a b c d : ℚ}
    (hA : RawBounds A a b) (hB : RawBounds B c d) :
    RawBounds (Set.image2 (· + ·) A B) (a + c) (b + d) := by
  refine ⟨Set.mem_image2_of_mem hA.1 hB.1, ?_⟩
  rintro _ ⟨x, hx, y, hy, rfl⟩
  exact add_le_add (show x ≤ b from hA.2 hx) (show y ≤ d from hB.2 hy)

/-- The reusable set statement exposes its sign requirements. Native-term
specialization later supplies them from the proved raw-member invariant. -/
theorem rawBounds_image2_mul {A B : Set ℚ} {a b c d : ℚ}
    (hA0 : ∀ x ∈ A, 0 ≤ x) (hB0 : ∀ y ∈ B, 0 ≤ y)
    (hA : RawBounds A a b) (hB : RawBounds B c d) :
    RawBounds (Set.image2 (· * ·) A B) (a * c) (b * d) := by
  refine ⟨Set.mem_image2_of_mem hA.1 hB.1, ?_⟩
  rintro _ ⟨x, hx, y, hy, rfl⟩
  have hb0 : 0 ≤ b := (hA0 a hA.1).trans (hA.2 hA.1)
  exact mul_le_mul (hA.2 hx) (hB.2 hy) (hB0 y hy) hb0

theorem rawBounds_expLog (n : ℕ) (hn : 1 ≤ n) :
    RawBounds (expLogApprox n) 0 (n : ℚ) := by
  refine ⟨expLogApprox_of_nonneg_lt n (le_refl 0) ?_, fun _ ha => expLogApprox_upper n ha⟩
  exact_mod_cast (show 0 < n by omega)

/-- The lower precision endpoint is a raw approximation, rather than merely a
member of the closed section. -/
theorem logApprox_precision_bounds (n q : ℕ) (hn : 1 ≤ n) (hq : 0 < q) :
    RawBounds (logApprox n)
      (((n ^ q).log2 : ℚ) / (q : ℚ))
      ((((n ^ q).log2 + 1 : ℕ) : ℚ) / (q : ℚ)) := by
  have hnq : n ^ q ≠ 0 := Nat.ne_of_gt (Nat.pow_pos (show 0 < n by omega))
  refine ⟨⟨(n ^ q).log2, q, hq, rfl, Nat.log2_self_le hnq⟩, ?_⟩
  intro a ha
  exact logApprox_upper n ((n ^ q).log2 + 1) q hq
    (Nat.lt_log2_self (n := n ^ q)).le ha

theorem rootApprox_precision_bounds (n q : ℕ) (hq : 0 < q) :
    RawBounds (rootApprox n)
      (((n * q * q).sqrt : ℚ) / (q : ℚ))
      ((((n * q * q).sqrt + 1 : ℕ) : ℚ) / (q : ℚ)) := by
  refine ⟨⟨(n * q * q).sqrt, q, hq, rfl, Nat.sqrt_le _⟩, ?_⟩
  intro a ha
  exact rootApprox_upper n ((n * q * q).sqrt + 1) q hq
    (Nat.lt_succ_sqrt (n * q * q)).le ha

/-- The prescribed adjacent fraction endpoints have exactly the displayed width. -/
theorem nat_fraction_width (p q : ℕ) :
    (((p + 1 : ℕ) : ℚ) / (q : ℚ)) - (p : ℚ) / (q : ℚ) = 1 / (q : ℚ) := by
  rw [nat_fraction_successor]
  ring

theorem reciprocal_arbitrarily_small (ε : ℚ) (hε : 0 < ε) :
    ∃ q : ℕ, 0 < q ∧ 1 / (q : ℚ) < ε := by
  obtain ⟨q, hq⟩ := exists_nat_one_div_lt hε
  refine ⟨q + 1, Nat.succ_pos q, ?_⟩
  simpa only [Nat.cast_add, Nat.cast_one] using hq

theorem logApprox_arbitrary_precision (n : ℕ) (hn : 1 ≤ n) (ε : ℚ) (hε : 0 < ε) :
    ∃ lo hi : ℚ, RawBounds (logApprox n) lo hi ∧ hi < lo + ε := by
  obtain ⟨q, hq, hsmall⟩ := reciprocal_arbitrarily_small ε hε
  refine ⟨((n ^ q).log2 : ℚ) / (q : ℚ),
    (((n ^ q).log2 + 1 : ℕ) : ℚ) / (q : ℚ), logApprox_precision_bounds n q hn hq, ?_⟩
  rw [nat_fraction_successor]
  linarith

theorem rootApprox_arbitrary_precision (n : ℕ) (ε : ℚ) (hε : 0 < ε) :
    ∃ lo hi : ℚ, RawBounds (rootApprox n) lo hi ∧ hi < lo + ε := by
  obtain ⟨q, hq, hsmall⟩ := reciprocal_arbitrarily_small ε hε
  refine ⟨((n * q * q).sqrt : ℚ) / (q : ℚ),
    (((n * q * q).sqrt + 1 : ℕ) : ℚ) / (q : ℚ), rootApprox_precision_bounds n q hq, ?_⟩
  rw [nat_fraction_successor]
  linarith

end SquareKit.NonnegativeArithmetic
/-! Ordinary rational closure, positive-rational tolerance and real least upper bounds. -/

namespace SquareKit.NonnegativeArithmetic
open scoped NNReal

noncomputable section

/-- Ordinary rational closure has the source's positive-rational tolerance test.
The set is arbitrary: neither boundedness nor nonemptiness is assumed. -/
theorem mem_closedSection_iff (A : Set ℚ) (x : ℚ) :
    x ∈ closedSection A ↔
      ∀ ε : ℚ, 0 < ε → ∃ b ∈ A, x ≤ b + ε := by
  change x ∈ closure (lowerClosure A : Set ℚ) ↔ _
  rw [Metric.mem_closure_iff]
  constructor
  · intro h ε hε
    have hεR : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
    obtain ⟨c, hc, hdist⟩ := h (ε : ℝ) hεR
    obtain ⟨b, hb, hcb⟩ := mem_lowerClosure.mp hc
    have hxcR : (x : ℝ) - (c : ℝ) < (ε : ℝ) :=
      (le_abs_self _).trans_lt (by simpa only [Rat.dist_eq] using hdist)
    have hxc : x - c < ε := by exact_mod_cast hxcR
    exact ⟨b, hb, by linarith⟩
  · intro h δ hδ
    obtain ⟨ε, hε, hεδ⟩ := exists_pos_rat_lt hδ
    obtain ⟨b, hb, hxb⟩ := h ε hε
    refine ⟨x - ε, mem_lowerClosure.mpr ⟨b, hb, by linarith⟩, ?_⟩
    have hεR : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
    simpa only [Rat.dist_eq, Rat.cast_sub, sub_sub_cancel, abs_of_pos hεR] using hεδ

/-- Every raw observation is a closed lower observation. -/
theorem subset_closedSection (A : Set ℚ) : A ⊆ closedSection A := by
  intro x hx
  exact subset_closure (subset_lowerClosure hx)

/-- A raw upper witness also supplies every smaller rational observation. -/
theorem mem_closedSection_of_le {A : Set ℚ} {x b : ℚ}
    (hb : b ∈ A) (hxb : x ≤ b) : x ∈ closedSection A := by
  exact subset_closure (mem_lowerClosure.mpr ⟨b, hb, hxb⟩)

@[simp] theorem closedSection_empty : closedSection (∅ : Set ℚ) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨b, hb, _⟩ := (mem_closedSection_iff ∅ x).mp hx 1 (by norm_num)
  exact hb

/-- Closing below does not turn an invalid empty raw set into a finite zero. -/
theorem closedSection_eq_empty_iff (A : Set ℚ) :
    closedSection A = ∅ ↔ A = ∅ := by
  constructor
  · intro h
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hmem := subset_closedSection A hx
    rw [h] at hmem
    exact hmem
  · rintro rfl
    exact closedSection_empty

/-- Raw observations dominated by actual target observations induce inclusion. -/
theorem closedSection_mono_of_dominates {A B : Set ℚ}
    (h : ∀ a ∈ A, ∃ b ∈ B, a ≤ b) :
    closedSection A ⊆ closedSection B := by
  intro x hx
  apply (mem_closedSection_iff B x).mpr
  intro ε hε
  obtain ⟨a, ha, hxa⟩ := (mem_closedSection_iff A x).mp hx ε hε
  obtain ⟨b, hb, hab⟩ := h a ha
  exact ⟨b, hb, by linarith⟩

/-- A real upper bound of raw observations bounds their ordinary rational closure. -/
theorem closedSection_le_real {A : Set ℚ} {v : ℝ}
    (hA : ∀ q ∈ A, (q : ℝ) ≤ v) {q : ℚ}
    (hq : q ∈ closedSection A) : (q : ℝ) ≤ v := by
  by_contra hnot
  have hgap : 0 < (q : ℝ) - v := sub_pos.mpr (lt_of_not_ge hnot)
  obtain ⟨ε, hε, hεgap⟩ := exists_pos_rat_lt hgap
  obtain ⟨b, hb, hqb⟩ := (mem_closedSection_iff A q).mp hq ε hε
  have hqbR : (q : ℝ) ≤ (b : ℝ) + (ε : ℝ) := by exact_mod_cast hqb
  have hbR := hA b hb
  linarith

/-- A finite real LUB is equivalent to the complete rational observation cut.
The image lives in ℝ, so the empty raw set has no finite LUB. -/
theorem isLUB_realCast_iff (A : Set ℚ) (v : ℝ) :
    IsLUB (((↑) : ℚ → ℝ) '' A) v ↔
      ∀ q : ℚ, q ∈ closedSection A ↔ (q : ℝ) ≤ v := by
  constructor
  · intro h q
    constructor
    · exact closedSection_le_real (fun a ha => h.1 ⟨a, ha, rfl⟩)
    · intro hq
      apply (mem_closedSection_iff A q).mpr
      intro ε hε
      have hεR : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
      have hlt : (q : ℝ) - (ε : ℝ) < v := by linarith
      obtain ⟨b, hb, hqb⟩ := (lt_isLUB_iff h).mp hlt
      obtain ⟨a, ha, rfl⟩ := hb
      refine ⟨a, ha, ?_⟩
      have hqR : (q : ℝ) ≤ (a : ℝ) + (ε : ℝ) := by linarith
      exact_mod_cast hqR
  · intro h
    constructor
    · rintro _ ⟨q, hq, rfl⟩
      exact (h q).mp (subset_closedSection A hq)
    · intro b hb
      apply le_of_forall_rat_lt_imp_le
      intro q hq
      exact closedSection_le_real (fun a ha => hb ⟨a, ha, rfl⟩)
        ((h q).mpr hq.le)

/-- Internal finite-branch characterization; the public relation is unchanged. -/
theorem rel_coe_iff_isLUB (A : Set ℚ) (v : ℝ≥0) :
    Rel A (v : Value) ↔ (∀ q ∈ A, 0 ≤ q) ∧
      IsLUB (((↑) : ℚ → ℝ) '' A) (v : ℝ) := by
  change ((∀ q ∈ A, 0 ≤ q) ∧
    ∀ q : ℚ, q ∈ closedSection A ↔ (q : ℝ) ≤ (v : ℝ)) ↔ _
  exact and_congr Iff.rfl (isLUB_realCast_iff A (v : ℝ)).symm

/-- A raw member is nonnegative even when the related value is not assumed valid. -/
theorem rel_nonneg {A : Set ℚ} {v : Value} (h : Rel A v)
    {q : ℚ} (hq : q ∈ A) : 0 ≤ q := by
  cases v with
  | none =>
    change A = ∅ at h
    have hempty : q ∈ (∅ : Set ℚ) := h ▸ hq
    exact False.elim hempty
  | some v => exact h.1 q hq

/-- An attained lower raw bound rules out bottom and gives a real enclosure. -/
theorem rel_bounds_real {A : Set ℚ} {v : Value} {lo hi : ℚ}
    (h : Rel A v) (hb : RawBounds A lo hi) :
    ∃ x : ℝ≥0, v = (x : Value) ∧
      (lo : ℝ) ≤ (x : ℝ) ∧ (x : ℝ) ≤ (hi : ℝ) := by
  cases v with
  | none =>
    change A = ∅ at h
    have hempty : lo ∈ (∅ : Set ℚ) := h ▸ hb.1
    exact False.elim hempty
  | some v =>
    refine ⟨v, rfl, (h.2 lo).mp (subset_closedSection A hb.1), ?_⟩
    have hLUB := (rel_coe_iff_isLUB A v).mp h
    apply hLUB.2.2
    rintro _ ⟨q, hq, rfl⟩
    have hqhi : q ≤ hi := hb.2 hq
    exact_mod_cast hqhi

/-- A singleton's closed lower observations include every smaller rational. -/
theorem mem_closedSection_singleton (r x : ℚ) :
    x ∈ closedSection ({r} : Set ℚ) ↔ x ≤ r := by
  have h : IsLUB (((↑) : ℚ → ℝ) '' ({r} : Set ℚ)) (r : ℝ) := by
    simpa only [Set.image_singleton] using (isLUB_singleton : IsLUB ({(r : ℝ)} : Set ℝ) (r : ℝ))
  exact ((isLUB_realCast_iff ({r} : Set ℚ) (r : ℝ)).mp h x).trans Rat.cast_le

/-- The negative query -2 distinguishes a valid zero section from emptiness. -/
theorem negative_query_zero_section : (-2 : ℚ) ∈ closedSection ({0} : Set ℚ) := by
  exact (mem_closedSection_singleton 0 (-2)).mpr (by norm_num)

theorem negative_query_empty_section : (-2 : ℚ) ∉ closedSection (∅ : Set ℚ) := by
  rw [closedSection_empty]
  exact Set.notMem_empty (-2)

end
end SquareKit.NonnegativeArithmetic
/-! Strict arithmetic preserves the raw-set relation, including valid zero and invalid operands. -/

namespace SquareKit.NonnegativeArithmetic

noncomputable section
open scoped Pointwise

theorem realCast_image2_add (A B : Set ℚ) :
    (((↑) : ℚ → ℝ) '' Set.image2 (fun x y : ℚ => x + y) A B) =
      Set.image2 (fun x y : ℝ => x + y)
        (((↑) : ℚ → ℝ) '' A) (((↑) : ℚ → ℝ) '' B) := by
  apply Set.image_image2_distrib
  intro a b
  exact Rat.cast_add a b

theorem realCast_image2_mul (A B : Set ℚ) :
    (((↑) : ℚ → ℝ) '' Set.image2 (fun x y : ℚ => x * y) A B) =
      Set.image2 (fun x y : ℝ => x * y)
        (((↑) : ℚ → ℝ) '' A) (((↑) : ℚ → ℝ) '' B) := by
  apply Set.image_image2_distrib
  intro a b
  exact Rat.cast_mul a b

/-- Two unary monotone scaling LUBs give the binary product LUB, including zero.
Only nonnegativity of the first upper endpoint and the second set is needed. -/
theorem isLUB_image2_mul_nonneg {A B : Set ℝ} {v w : ℝ}
    (hA : IsLUB A v) (hB : IsLUB B w)
    (hv : 0 ≤ v) (hB0 : ∀ b ∈ B, 0 ≤ b) :
    IsLUB (Set.image2 (fun x y : ℝ => x * y) A B) (v * w) := by
  constructor
  · rintro _ ⟨a, ha, b, hb, rfl⟩
    exact mul_le_mul (hA.1 ha) (hB.1 hb) (hB0 b hb) hv
  · intro z hz
    apply (hB.mul_left hv).2
    rintro _ ⟨b, hb, rfl⟩
    apply (hA.mul_right (hB0 b hb)).2
    rintro _ ⟨a, ha, rfl⟩
    exact hz ⟨a, ha, b, hb, rfl⟩

/-- The raw sum represents exactly the explicitly strict partial sum. -/
theorem rel_image2_add {A B : Set ℚ} {v w : Value}
    (hA : Rel A v) (hB : Rel B w) :
    Rel (Set.image2 (fun x y : ℚ => x + y) A B) (strictAdd v w) := by
  cases v with
  | none =>
    change A = ∅ at hA
    change Set.image2 (fun x y : ℚ => x + y) A B = ∅
    rw [hA, Set.image2_empty_left]
  | some v =>
    cases w with
    | none =>
      change B = ∅ at hB
      change Set.image2 (fun x y : ℚ => x + y) A B = ∅
      rw [hB, Set.image2_empty_right]
    | some w =>
      change Rel (Set.image2 (fun x y : ℚ => x + y) A B) ((v + w : ℝ≥0) : Value)
      obtain ⟨hA0, hALUB⟩ := (rel_coe_iff_isLUB A v).mp hA
      obtain ⟨hB0, hBLUB⟩ := (rel_coe_iff_isLUB B w).mp hB
      apply (rel_coe_iff_isLUB _ _).mpr
      constructor
      · rintro _ ⟨a, ha, b, hb, rfl⟩
        exact add_nonneg (hA0 a ha) (hB0 b hb)
      · rw [realCast_image2_add]
        change IsLUB (Set.image2 (fun x y : ℝ => x + y)
          (((↑) : ℚ → ℝ) '' A) (((↑) : ℚ → ℝ) '' B)) ((v : ℝ) + (w : ℝ))
        simpa only [Set.image2_add] using hALUB.add hBLUB

/-- The raw product represents exactly the explicitly strict partial product.
Empty raw operands remain empty even when the other value is finite zero. -/
theorem rel_image2_mul {A B : Set ℚ} {v w : Value}
    (hA : Rel A v) (hB : Rel B w) :
    Rel (Set.image2 (fun x y : ℚ => x * y) A B) (strictMul v w) := by
  cases v with
  | none =>
    change A = ∅ at hA
    change Set.image2 (fun x y : ℚ => x * y) A B = ∅
    rw [hA, Set.image2_empty_left]
  | some v =>
    cases w with
    | none =>
      change B = ∅ at hB
      change Set.image2 (fun x y : ℚ => x * y) A B = ∅
      rw [hB, Set.image2_empty_right]
    | some w =>
      change Rel (Set.image2 (fun x y : ℚ => x * y) A B) ((v * w : ℝ≥0) : Value)
      obtain ⟨hA0, hALUB⟩ := (rel_coe_iff_isLUB A v).mp hA
      obtain ⟨hB0, hBLUB⟩ := (rel_coe_iff_isLUB B w).mp hB
      apply (rel_coe_iff_isLUB _ _).mpr
      constructor
      · rintro _ ⟨a, ha, b, hb, rfl⟩
        exact mul_nonneg (hA0 a ha) (hB0 b hb)
      · rw [realCast_image2_mul]
        change IsLUB (Set.image2 (fun x y : ℝ => x * y)
          (((↑) : ℚ → ℝ) '' A) (((↑) : ℚ → ℝ) '' B)) ((v : ℝ) * (w : ℝ))
        apply isLUB_image2_mul_nonneg hALUB hBLUB v.property
        rintro _ ⟨q, hq, rfl⟩
        exact_mod_cast hB0 q hq

theorem strictAdd_eq_bot_iff (v w : Value) :
    strictAdd v w = ⊥ ↔ v = ⊥ ∨ w = ⊥ :=
  WithBot.map₂_eq_bot_iff

theorem strictMul_eq_bot_iff (v w : Value) :
    strictMul v w = ⊥ ↔ v = ⊥ ∨ w = ⊥ :=
  WithBot.map₂_eq_bot_iff

/-- Source multiplication preserves invalidity on either side of finite zero. -/
theorem strictMul_zero_bot : strictMul ((0 : ℝ≥0) : Value) ⊥ = ⊥ := rfl

theorem strictMul_bot_zero : strictMul ⊥ ((0 : ℝ≥0) : Value) = ⊥ := rfl

/-- Finite zero times a finite value remains the distinct finite zero. -/
theorem strictMul_zero_finite (v : ℝ≥0) :
    strictMul ((0 : ℝ≥0) : Value) (v : Value) = ((0 : ℝ≥0) : Value) := by
  change ((0 * v : ℝ≥0) : Value) = ((0 : ℝ≥0) : Value)
  rw [zero_mul]

end
end SquareKit.NonnegativeArithmetic
/-! Consequences of attained raw bounds for the ordinary closed lower section. -/

set_option autoImplicit false
set_option warningAsError true

namespace SquareKit.NonnegativeArithmetic

theorem rawBounds_closedSection_le {A : Set ℚ} {lo hi x : ℚ}
    (hA : RawBounds A lo hi) (hx : x ∈ closedSection A) : x ≤ hi := by
  have hR : (x : ℝ) ≤ (hi : ℝ) := closedSection_le_real
    (fun q hq => by
      have hqhi : q ≤ hi := hA.2 hq
      exact_mod_cast hqhi) hx
  exact_mod_cast hR

theorem rawBounds_closedSection_exact {A : Set ℚ} {r : ℚ}
    (hA : RawBounds A r r) (x : ℚ) : x ∈ closedSection A ↔ x ≤ r := by
  constructor
  · exact rawBounds_closedSection_le hA
  · exact mem_closedSection_of_le hA.1

theorem rawBounds_closedSection_mono {A B : Set ℚ} {a b c d : ℚ}
    (hA : RawBounds A a b) (hB : RawBounds B c d) (hbc : b ≤ c) :
    closedSection A ⊆ closedSection B := by
  apply closedSection_mono_of_dominates
  intro x hx
  exact ⟨c, hB.1, (hA.2 hx).trans hbc⟩

end SquareKit.NonnegativeArithmetic
/-! Atom relation certificates for every original rational or natural input. -/

namespace SquareKit.NonnegativeArithmetic
open scoped NNReal

noncomputable section

/-- An attained zero, a finite upper bound, and every strict nonnegative lower
observation establish the exact finite relation without asserting endpoint attainment. -/
theorem rel_of_nonneg_cofinal {A : Set ℚ} {v : ℝ≥0}
    (hA0 : ∀ q ∈ A, 0 ≤ q) (hzero : (0 : ℚ) ∈ A)
    (hupper : ∀ q ∈ A, (q : ℝ) ≤ (v : ℝ))
    (hcofinal : ∀ q : ℚ, 0 ≤ q → (q : ℝ) < (v : ℝ) → q ∈ A) :
    Rel A (v : Value) := by
  apply (rel_coe_iff_isLUB A v).mpr
  refine ⟨hA0, ?_⟩
  constructor
  · rintro _ ⟨q, hq, rfl⟩
    exact hupper q hq
  · intro z hz
    by_contra hnot
    have hzv : z < (v : ℝ) := lt_of_not_ge hnot
    by_cases hz0 : z < 0
    · have h0z : (0 : ℝ) ≤ z := hz ⟨0, hzero, by simp⟩
      exact (not_lt_of_ge h0z) hz0
    · obtain ⟨q, hzq, hqv⟩ := exists_rat_btwn hzv
      have hq0R : (0 : ℝ) ≤ (q : ℝ) := (le_of_not_gt hz0).trans hzq.le
      have hq0 : (0 : ℚ) ≤ q := by exact_mod_cast hq0R
      have hqz : (q : ℝ) ≤ z := hz ⟨q, hcofinal q hq0 hqv, rfl⟩
      exact (not_lt_of_ge hqz) hzq

/-- Exact nonnegative rational lower cuts supply the finite atom contract. -/
theorem rel_of_mem_iff {A : Set ℚ} {v : ℝ≥0}
    (h : ∀ q : ℚ, q ∈ A ↔ 0 ≤ q ∧ (q : ℝ) ≤ (v : ℝ)) :
    Rel A (v : Value) := by
  apply rel_of_nonneg_cofinal
  · intro q hq
    exact ((h q).mp hq).1
  · exact (h 0).mpr ⟨le_rfl, by simpa only [Rat.cast_zero] using NNReal.coe_nonneg v⟩
  · intro q hq
    exact ((h q).mp hq).2
  · intro q hq0 hqv
    exact (h q).mpr ⟨hq0, hqv.le⟩

/-- Negative rational atoms are invalid; nonnegative atoms retain their exact cast. -/
theorem rel_rational (r : ℚ) : Rel (Set.Icc 0 r) (rationalValue r) := by
  by_cases hr : 0 ≤ r
  · rw [rationalValue, ite_eq_left hr]
    have hrR : (0 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    apply rel_of_mem_iff
    intro q
    simp only [Set.mem_Icc, Real.coe_toNNReal _ hrR, Rat.cast_le]
  · rw [rationalValue, ite_eq_right hr]
    change Set.Icc (0 : ℚ) r = ∅
    exact Set.Icc_eq_empty_of_lt (lt_of_not_ge hr)

/-- The log certificate includes the invalid zero input and the valid log-one zero. -/
theorem rel_logarithm (n : ℕ) : Rel (logApprox n) (logarithmValue n) := by
  by_cases hn : n = 0
  · subst n
    simp [logarithmValue, Rel]
  · have hn1 : 1 ≤ n := by omega
    have hlog : 0 ≤ Real.logb 2 (n : ℝ) :=
      Real.logb_nonneg (by norm_num : (1 : ℝ) < 2) (by exact_mod_cast hn1)
    rw [logarithmValue, ite_eq_right hn]
    apply rel_of_mem_iff
    intro q
    rw [Real.coe_toNNReal _ hlog]
    exact mem_logApprox_iff n hn1 q

/-- Square root is valid for every natural input, including zero. -/
theorem rel_squareRoot (n : ℕ) : Rel (rootApprox n) (squareRootValue n) := by
  unfold squareRootValue
  apply rel_of_mem_iff
  intro q
  simpa only [Real.coe_sqrt, NNReal.coe_natCast] using mem_rootApprox_iff n q

/-- ExpLog's cofinal raw observations represent n on the positive domain.
The proof does not identify the raw set with an interval or attain its endpoint. -/
theorem rel_exponentiatedLogarithm (n : ℕ) :
    Rel (expLogApprox n) (exponentiatedLogarithmValue n) := by
  by_cases hn : n = 0
  · subst n
    simp [exponentiatedLogarithmValue, Rel]
  · rw [exponentiatedLogarithmValue, ite_eq_right hn]
    apply rel_of_nonneg_cofinal
    · intro q hq
      exact expLogApprox_nonneg hq
    · apply expLogApprox_of_nonneg_lt n (by norm_num)
      exact_mod_cast (show 0 < n by omega)
    · intro q hq
      have hqn := expLogApprox_upper n hq
      rw [NNReal.coe_natCast]
      exact_mod_cast hqn
    · intro q hq0 hqn
      apply expLogApprox_of_nonneg_lt n hq0
      rw [NNReal.coe_natCast] at hqn
      exact_mod_cast hqn

end
end SquareKit.NonnegativeArithmetic
/-! The relational primitive instance and equations of the existing typed compiler. -/

set_option autoImplicit false
set_option warningAsError true

namespace SquareKit.NonnegativeArithmetic
open FirstOrderCompiler
open scoped NNReal

noncomputable section

/-- The six actual raw operations preserve the shared relation. -/
def rawPrimitives :
    FirstOrderRelations.Primitives representation Prim valueMeaning where
  impl := rawPrimitive
  correct := by
    intro a b p r s h
    cases p with
    | rational q => exact rel_rational q
    | logarithm n => exact rel_logarithm n
    | squareRoot n => exact rel_squareRoot n
    | exponentiatedLogarithm n => exact rel_exponentiatedLogarithm n
    | add => exact rel_image2_add h.1 h.2
    | mul => exact rel_image2_mul h.1 h.2

/-- Raw observations are the implementation of the existing typed compiler. -/
def rawTerm {Γ : Ctx} {a : Ty} (t : Term Prim Γ a) :
    (FirstOrderRelations.encoding representation (context Γ)).R →
    (FirstOrderRelations.encoding representation a).R :=
  (FirstOrderCompiler.compile
    (FirstOrderRelations.target representation rawPrimitives) t).impl

/-- Every typed term preserves every related environment, including products,
projections and let-bound values that the body may discard. -/
theorem rawTerm_related {Γ : Ctx} {a : Ty} (t : Term Prim Γ a)
    {r : (FirstOrderRelations.encoding representation (context Γ)).R}
    {s : Val Value (context Γ)}
    (h : (FirstOrderRelations.encoding representation (context Γ)).Rel r s) :
    (FirstOrderRelations.encoding representation a).Rel (rawTerm t r) (valueTerm t s) :=
  FirstOrderRelations.compile_preserves representation rawPrimitives t h

/-- Ground raw members are nonnegative under the same related-environment
premise as compiler preservation; no condition is imposed on unused subterms. -/
theorem rawTerm_nonneg {Γ : Ctx} (t : Term Prim Γ .base)
    {r : (FirstOrderRelations.encoding representation (context Γ)).R}
    {s : Val Value (context Γ)}
    (h : (FirstOrderRelations.encoding representation (context Γ)).Rel r s)
    {q : ℚ} (hq : (rawTerm t r : Set ℚ) q) : 0 ≤ q :=
  rel_nonneg (rawTerm_related t h) hq

@[simp] theorem rawTerm_rational {Γ : Ctx} (r : ℚ)
    (ρ : (FirstOrderRelations.encoding representation (context Γ)).R) :
    rawTerm (rational r) ρ = Set.Icc 0 r := rfl

@[simp] theorem rawTerm_logarithm {Γ : Ctx} (n : ℕ)
    (ρ : (FirstOrderRelations.encoding representation (context Γ)).R) :
    rawTerm (logarithm n) ρ = logApprox n := rfl

@[simp] theorem rawTerm_squareRoot {Γ : Ctx} (n : ℕ)
    (ρ : (FirstOrderRelations.encoding representation (context Γ)).R) :
    rawTerm (squareRoot n) ρ = rootApprox n := rfl

@[simp] theorem rawTerm_exponentiatedLogarithm {Γ : Ctx} (n : ℕ)
    (ρ : (FirstOrderRelations.encoding representation (context Γ)).R) :
    rawTerm (exponentiatedLogarithm n) ρ = expLogApprox n := rfl

@[simp] theorem rawTerm_add {Γ : Ctx} (e f : Term Prim Γ .base)
    (ρ : (FirstOrderRelations.encoding representation (context Γ)).R) :
    rawTerm (add e f) ρ = Set.image2 (· + ·) (rawTerm e ρ) (rawTerm f ρ) := rfl

@[simp] theorem rawTerm_mul {Γ : Ctx} (e f : Term Prim Γ .base)
    (ρ : (FirstOrderRelations.encoding representation (context Γ)).R) :
    rawTerm (mul e f) ρ = Set.image2 (· * ·) (rawTerm e ρ) (rawTerm f ρ) := rfl

@[simp] theorem rawTerm_letE {Γ : Ctx} {a b : Ty}
    (t : Term Prim Γ a) (u : Term Prim (a :: Γ) b)
    (ρ : (FirstOrderRelations.encoding representation (context Γ)).R) :
    rawTerm (.letE t u) ρ = rawTerm u (ρ, rawTerm t ρ) := rfl

@[simp] theorem valueTerm_rational {Γ : Ctx} (r : ℚ)
    (ρ : Val Value (context Γ)) :
    valueTerm (rational r) ρ = rationalValue r := rfl

@[simp] theorem valueTerm_logarithm {Γ : Ctx} (n : ℕ)
    (ρ : Val Value (context Γ)) :
    valueTerm (logarithm n) ρ = logarithmValue n := rfl

@[simp] theorem valueTerm_squareRoot {Γ : Ctx} (n : ℕ)
    (ρ : Val Value (context Γ)) :
    valueTerm (squareRoot n) ρ = squareRootValue n := rfl

@[simp] theorem valueTerm_exponentiatedLogarithm {Γ : Ctx} (n : ℕ)
    (ρ : Val Value (context Γ)) :
    valueTerm (exponentiatedLogarithm n) ρ = exponentiatedLogarithmValue n := rfl

@[simp] theorem valueTerm_add {Γ : Ctx} (e f : Term Prim Γ .base)
    (ρ : Val Value (context Γ)) :
    valueTerm (add e f) ρ = strictAdd (valueTerm e ρ) (valueTerm f ρ) := rfl

@[simp] theorem valueTerm_mul {Γ : Ctx} (e f : Term Prim Γ .base)
    (ρ : Val Value (context Γ)) :
    valueTerm (mul e f) ρ = strictMul (valueTerm e ρ) (valueTerm f ρ) := rfl

@[simp] theorem valueTerm_letE {Γ : Ctx} {a b : Ty}
    (t : Term Prim Γ a) (u : Term Prim (a :: Γ) b)
    (ρ : Val Value (context Γ)) :
    valueTerm (.letE t u) ρ = valueTerm u (ρ, valueTerm t ρ) := rfl

def raw (e : ClosedTerm) : Set ℚ := rawTerm e ()

def sectionOf (e : ClosedTerm) : Set ℚ := closedSection (raw e)

def Bounded (e : ClosedTerm) (lo hi : ℚ) : Prop := RawBounds (raw e) lo hi

theorem raw_related (e : ClosedTerm) : Rel (raw e) (value e) :=
  rawTerm_related e (r := ()) (s := ()) True.intro

theorem raw_nonneg (e : ClosedTerm) {q : ℚ} (hq : q ∈ raw e) : 0 ≤ q :=
  rel_nonneg (raw_related e) hq

@[simp] theorem raw_rational (r : ℚ) : raw (rational r) = Set.Icc 0 r := rfl
@[simp] theorem raw_logarithm (n : ℕ) : raw (logarithm n) = logApprox n := rfl
@[simp] theorem raw_squareRoot (n : ℕ) : raw (squareRoot n) = rootApprox n := rfl
@[simp] theorem raw_exponentiatedLogarithm (n : ℕ) :
    raw (exponentiatedLogarithm n) = expLogApprox n := rfl
@[simp] theorem raw_add (e f : ClosedTerm) :
    raw (add e f) = Set.image2 (· + ·) (raw e) (raw f) := rfl
@[simp] theorem raw_mul (e f : ClosedTerm) :
    raw (mul e f) = Set.image2 (· * ·) (raw e) (raw f) := rfl
@[simp] theorem raw_scale (k : ℕ) (e : ClosedTerm) :
    raw (scale k e) = Set.image2 (· * ·) (Set.Icc 0 (k : ℚ)) (raw e) := rfl

@[simp] theorem value_rational (r : ℚ) : value (rational r) = rationalValue r := rfl
@[simp] theorem value_logarithm (n : ℕ) : value (logarithm n) = logarithmValue n := rfl
@[simp] theorem value_squareRoot (n : ℕ) : value (squareRoot n) = squareRootValue n := rfl
@[simp] theorem value_exponentiatedLogarithm (n : ℕ) :
    value (exponentiatedLogarithm n) = exponentiatedLogarithmValue n := rfl
@[simp] theorem value_add (e f : ClosedTerm) :
    value (add e f) = strictAdd (value e) (value f) := rfl
@[simp] theorem value_mul (e f : ClosedTerm) :
    value (mul e f) = strictMul (value e) (value f) := rfl

end
end SquareKit.NonnegativeArithmetic
/-! Exact observations, validity and the existing value order for all rational queries. -/

set_option autoImplicit false
set_option warningAsError true

namespace SquareKit.NonnegativeArithmetic
open scoped NNReal

noncomputable section

/-- A finite related value has a genuine raw member, even when its endpoint
itself is not a raw observation. -/
theorem rel_coe_nonempty {A : Set ℚ} {v : ℝ≥0} (h : Rel A (v : Value)) :
    A.Nonempty := by
  obtain ⟨_, q, hq, _⟩ := ((rel_coe_iff_isLUB A v).mp h).2.nonempty
  exact ⟨q, hq⟩

theorem rel_value_eq_bot_iff {A : Set ℚ} {v : Value} (h : Rel A v) :
    v = ⊥ ↔ A = ∅ := by
  cases v with
  | none =>
    change A = ∅ at h
    exact ⟨fun _ => h, fun _ => rfl⟩
  | some v =>
    constructor
    · intro hv
      exact False.elim (WithBot.coe_ne_bot hv)
    · intro hempty
      obtain ⟨q, hq⟩ := rel_coe_nonempty h
      rw [hempty] at hq
      exact False.elim hq

/-- The public cut observation is an existential finite value, so invalidity
does not acquire any rational observation through a default-zero convention. -/
theorem rel_mem_closedSection_iff {A : Set ℚ} {v : Value}
    (h : Rel A v) (q : ℚ) :
    q ∈ closedSection A ↔
      ∃ x : ℝ≥0, v = (x : Value) ∧ (q : ℝ) ≤ (x : ℝ) := by
  cases v with
  | none =>
    change A = ∅ at h
    rw [h, closedSection_empty]
    constructor
    · intro hq
      exact False.elim hq
    · rintro ⟨x, hx, _⟩
      exact False.elim (WithBot.bot_ne_coe hx)
  | some v =>
    constructor
    · intro hq
      exact ⟨v, rfl, (h.2 q).mp hq⟩
    · rintro ⟨x, hx, hq⟩
      have hvx : v = x := WithBot.coe_injective hx
      subst x
      exact (h.2 q).mpr hq

/-- Inclusion of exact rational observation cuts is precisely the existing
WithBot order, including both mixed-validity cases. -/
theorem rel_closedSection_subset_iff {A B : Set ℚ} {v w : Value}
    (hA : Rel A v) (hB : Rel B w) :
    closedSection A ⊆ closedSection B ↔ v ≤ w := by
  cases v with
  | none =>
    change A = ∅ at hA
    rw [hA, closedSection_empty]
    exact ⟨fun _ => bot_le, fun _ => Set.empty_subset _⟩
  | some v =>
    cases w with
    | none =>
      change B = ∅ at hB
      rw [hB, closedSection_empty]
      constructor
      · intro hsub
        have hzero : (0 : ℚ) ∈ closedSection A :=
          (hA.2 0).mpr (by simpa only [Rat.cast_zero] using NNReal.coe_nonneg v)
        exact False.elim (hsub hzero)
      · intro hle
        exact False.elim ((WithBot.not_coe_le_bot v) hle)
    | some w =>
      constructor
      · intro hsub
        apply WithBot.coe_le_coe.mpr
        apply NNReal.coe_le_coe.mp
        apply le_of_forall_rat_lt_imp_le
        intro q hq
        exact (hB.2 q).mp (hsub ((hA.2 q).mpr hq.le))
      · intro hle q hq
        have hvw : (v : ℝ) ≤ (w : ℝ) :=
          NNReal.coe_le_coe.mpr (WithBot.coe_le_coe.mp hle)
        exact (hB.2 q).mpr (((hA.2 q).mp hq).trans hvw)

theorem value_eq_bot_iff (e : ClosedTerm) : value e = ⊥ ↔ raw e = ∅ :=
  rel_value_eq_bot_iff (raw_related e)

theorem value_eq_bot_iff_sectionOf_empty (e : ClosedTerm) :
    value e = ⊥ ↔ sectionOf e = ∅ :=
  (value_eq_bot_iff e).trans (closedSection_eq_empty_iff (raw e)).symm

theorem mem_sectionOf_iff (e : ClosedTerm) (q : ℚ) :
    q ∈ sectionOf e ↔
      ∃ x : ℝ≥0, value e = (x : Value) ∧ (q : ℝ) ≤ (x : ℝ) :=
  rel_mem_closedSection_iff (raw_related e) q

theorem sectionOf_subset_iff (e f : ClosedTerm) :
    sectionOf e ⊆ sectionOf f ↔ value e ≤ value f :=
  rel_closedSection_subset_iff (raw_related e) (raw_related f)

/-- The source approximation-to-section theorem uses ordinary set inclusion. -/
theorem raw_subset_sectionOf (e : ClosedTerm) : raw e ⊆ sectionOf e :=
  subset_closedSection (raw e)

/-- Every rational query is admitted, including negative queries. -/
theorem rational_section_iff (r x : ℚ) (hr : 0 ≤ r) :
    x ∈ sectionOf (rational r) ↔ x ≤ r := by
  have hrR : (0 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hrel : Rel (Set.Icc 0 r) (Real.toNNReal (r : ℝ) : Value) := by
    simpa only [rationalValue, ite_eq_left hr] using rel_rational r
  simpa only [sectionOf, raw_rational, Real.coe_toNNReal _ hrR, Rat.cast_le]
    using hrel.2 x

theorem le_of_approximants {e f : ClosedTerm}
    (h : ∀ a ∈ raw e, ∃ b ∈ raw f, a ≤ b) :
    sectionOf e ⊆ sectionOf f :=
  closedSection_mono_of_dominates h

@[simp] theorem rationalValue_natCast (k : ℕ) :
    rationalValue (k : ℚ) = ((k : ℝ≥0) : Value) := by
  rw [rationalValue, ite_eq_left (Nat.cast_nonneg k), Rat.cast_natCast,
    Real.toNNReal_natCast]

/-- Natural scaling maps finite values and retains bottom even when k = 0. -/
theorem value_scale (k : ℕ) (e : ClosedTerm) :
    value (scale k e) =
      WithBot.map (fun x : ℝ≥0 => (k : ℝ≥0) * x) (value e) := by
  change strictMul (rationalValue (k : ℚ)) (value e) = _
  rw [rationalValue_natCast, strictMul, WithBot.map₂_coe_left]

theorem value_scale_eq_bot_iff (k : ℕ) (e : ClosedTerm) :
    value (scale k e) = ⊥ ↔ value e = ⊥ := by
  rw [value_scale, WithBot.map_eq_bot_iff]

end
end SquareKit.NonnegativeArithmetic
/-! Attained bounds and section consequences through the relational compiler. -/

set_option autoImplicit false
set_option warningAsError true

namespace SquareKit.NonnegativeArithmetic
open scoped NNReal

theorem bounded_rational (r : ℚ) (hr : 0 ≤ r) : Bounded (rational r) r r := by
  simpa only [Bounded, raw_rational] using rawBounds_rational r hr

theorem bounded_log (n : ℕ) (hn : 1 ≤ n) :
    Bounded (logarithm n) (n.log2 : ℚ) ((n.log2 : ℚ) + 1) := by
  simpa only [Bounded, raw_logarithm] using rawBounds_log n hn

theorem bounded_root (n : ℕ) :
    Bounded (squareRoot n) (n.sqrt : ℚ) ((n.sqrt : ℚ) + 1) := by
  simpa only [Bounded, raw_squareRoot] using rawBounds_root n

theorem bounded_log_power (k : ℕ) : Bounded (logarithm (2 ^ k)) (k : ℚ) (k : ℚ) := by
  simpa only [Bounded, raw_logarithm] using rawBounds_log_power k

theorem bounded_root_square (k : ℕ) : Bounded (squareRoot (k * k)) (k : ℚ) (k : ℚ) := by
  simpa only [Bounded, raw_squareRoot] using rawBounds_root_square k

theorem bounded_add {e f : ClosedTerm} {a b c d : ℚ}
    (he : Bounded e a b) (hf : Bounded f c d) :
    Bounded (add e f) (a + c) (b + d) := by
  simpa only [Bounded, raw_add] using rawBounds_image2_add he hf

/-- Source multiplication needs no extra sign premise: raw-member nonnegativity
comes from the already proved generic compiler interpretation. -/
theorem bounded_mul {e f : ClosedTerm} {a b c d : ℚ}
    (he : Bounded e a b) (hf : Bounded f c d) :
    Bounded (mul e f) (a * c) (b * d) := by
  have hset := rawBounds_image2_mul
    (fun x hx => raw_nonneg e hx) (fun y hy => raw_nonneg f hy) he hf
  simpa only [Bounded, raw_mul] using hset

/-- Zero scaling is covered under the source's actual bounded-operand premise. -/
theorem bounded_scale (k : ℕ) {e : ClosedTerm} {a b : ℚ} (he : Bounded e a b) :
    Bounded (scale k e) ((k : ℚ) * a) ((k : ℚ) * b) := by
  exact bounded_mul (bounded_rational (k : ℚ) (Nat.cast_nonneg k)) he

theorem le_of_bounds {e f : ClosedTerm} {a b c d : ℚ}
    (he : Bounded e a b) (hf : Bounded f c d) (hbc : b ≤ c) :
    sectionOf e ⊆ sectionOf f :=
  rawBounds_closedSection_mono he hf hbc

theorem section_le_upper {e : ClosedTerm} {lo hi x : ℚ}
    (he : Bounded e lo hi) (hx : x ∈ sectionOf e) : x ≤ hi :=
  rawBounds_closedSection_le he hx

theorem section_of_exact_bounds {e : ClosedTerm} {r : ℚ}
    (he : Bounded e r r) (x : ℚ) : x ∈ sectionOf e ↔ x ≤ r :=
  rawBounds_closedSection_exact he x

theorem bounded_expLog (n : ℕ) (hn : 1 ≤ n) :
    Bounded (exponentiatedLogarithm n) 0 (n : ℚ) := by
  simpa only [Bounded, raw_exponentiatedLogarithm] using rawBounds_expLog n hn

theorem log_bounded_precision (n q : ℕ) (hn : 1 ≤ n) (hq : 0 < q) :
    Bounded (logarithm n)
      (((n ^ q).log2 : ℚ) / (q : ℚ))
      ((((n ^ q).log2 + 1 : ℕ) : ℚ) / (q : ℚ)) := by
  simpa only [Bounded, raw_logarithm] using logApprox_precision_bounds n q hn hq

theorem root_bounded_precision (n q : ℕ) (hq : 0 < q) :
    Bounded (squareRoot n)
      (((n * q * q).sqrt : ℚ) / (q : ℚ))
      ((((n * q * q).sqrt + 1 : ℕ) : ℚ) / (q : ℚ)) := by
  simpa only [Bounded, raw_squareRoot] using rootApprox_precision_bounds n q hq

/-- The closed threshold is the exact finite power test, rather than a floor test. -/
theorem logarithm_section_fraction_iff (n p q : ℕ) (hn : 1 ≤ n) (hq : 0 < q) :
    (p : ℚ) / (q : ℚ) ∈ sectionOf (logarithm n) ↔ 2 ^ p ≤ n ^ q := by
  have hn0 : n ≠ 0 := by omega
  have hlog0 : 0 ≤ Real.logb 2 (n : ℝ) :=
    Real.logb_nonneg (by norm_num : (1 : ℝ) < 2) (by exact_mod_cast hn)
  have hrel : Rel (logApprox n) (Real.toNNReal (Real.logb 2 (n : ℝ)) : Value) := by
    simpa only [logarithmValue, ite_eq_right hn0] using rel_logarithm n
  have hcut : (p : ℚ) / (q : ℚ) ∈ closedSection (logApprox n) ↔
      (((p : ℚ) / (q : ℚ) : ℚ) : ℝ) ≤ Real.logb 2 (n : ℝ) := by
    simpa only [Real.coe_toNNReal _ hlog0] using hrel.2 ((p : ℚ) / (q : ℚ))
  simpa only [sectionOf, raw_logarithm] using
    hcut.trans (nat_fraction_le_logb_iff n p q hn hq)

theorem squareRoot_section_fraction_iff (n p q : ℕ) (hq : 0 < q) :
    (p : ℚ) / (q : ℚ) ∈ sectionOf (squareRoot n) ↔ p * p ≤ n * q * q := by
  have hrel : Rel (rootApprox n) (NNReal.sqrt (n : ℝ≥0) : Value) := rel_squareRoot n
  have hcut : (p : ℚ) / (q : ℚ) ∈ closedSection (rootApprox n) ↔
      (((p : ℚ) / (q : ℚ) : ℚ) : ℝ) ≤ Real.sqrt (n : ℝ) := by
    simpa only [Real.coe_sqrt, NNReal.coe_natCast] using hrel.2 ((p : ℚ) / (q : ℚ))
  simpa only [sectionOf, raw_squareRoot] using
    hcut.trans (nat_fraction_le_sqrt_iff n p q hq)

/-- Every rational query is included, including negative queries and the closed
upper endpoint, even when that endpoint is not a raw approximation. -/
theorem exponentiatedLogarithm_section_iff (n : ℕ) (hn : 1 ≤ n) (x : ℚ) :
    x ∈ sectionOf (exponentiatedLogarithm n) ↔ x ≤ (n : ℚ) := by
  have hn0 : n ≠ 0 := by omega
  have hrel : Rel (expLogApprox n) ((n : ℝ≥0) : Value) := by
    simpa only [exponentiatedLogarithmValue, ite_eq_right hn0] using rel_exponentiatedLogarithm n
  simpa only [sectionOf, raw_exponentiatedLogarithm, NNReal.coe_natCast,
    Rat.cast_le_natCast] using hrel.2 x

theorem logarithm_arbitrary_precision (n : ℕ) (hn : 1 ≤ n) (ε : ℚ) (hε : 0 < ε) :
    ∃ lo hi : ℚ, Bounded (logarithm n) lo hi ∧ hi < lo + ε := by
  simpa only [Bounded, raw_logarithm] using logApprox_arbitrary_precision n hn ε hε

theorem squareRoot_arbitrary_precision (n : ℕ) (ε : ℚ) (hε : 0 < ε) :
    ∃ lo hi : ℚ, Bounded (squareRoot n) lo hi ∧ hi < lo + ε := by
  simpa only [Bounded, raw_squareRoot] using rootApprox_arbitrary_precision n ε hε

end SquareKit.NonnegativeArithmetic
/-! Raw endpoint distinctions for exact square-root and ExpLog clients. -/

set_option autoImplicit false
set_option warningAsError true

namespace SquareKit.NonnegativeArithmetic

/-- An ExpLog3 endpoint witness would force a positive power of three to be
a power of two. Cancellation keeps every denominator symbolic. -/
theorem expLogApprox_three_not_mem : (3 : ℚ) ∉ expLogApprox 3 := by
  rintro ⟨p, q, r, s, hq, hs, hfrac, hp, hr⟩
  have hsQ : (0 : ℚ) < s := by exact_mod_cast hs
  have hrsQ : (r : ℚ) = 3 * (s : ℚ) :=
    (div_eq_iff (ne_of_gt hsQ)).mp hfrac.symm
  have hrs : r = 3 * s := by exact_mod_cast hrsQ
  subst r
  have hrev : 3 ^ q ≤ 2 ^ p := Nat.le_of_mul_le_mul_right
    (by simpa only [Nat.mul_pow] using hr) (Nat.pow_pos (n := q) hs)
  have hpow : 3 ^ q = 2 ^ p := le_antisymm hrev hp
  have hthree : (3 : ℕ) ∣ 2 ^ p := by
    rw [← hpow]
    exact dvd_pow_self 3 (Nat.ne_of_gt hq)
  exact (by decide : ¬ ((3 : ℕ) ∣ 2)) (Nat.prime_three.dvd_of_dvd_pow hthree)

/-- ExpLog does attain some integer endpoints; it is not a strict interval. -/
theorem expLogApprox_four_mem : (4 : ℚ) ∈ expLogApprox 4 := by
  exact ⟨2, 1, 4, 1, by decide, by decide, by norm_num, by decide, by decide⟩

/-- Irrational roots have no rational raw member at their real endpoint. -/
theorem rootApprox_lt_sqrt_of_irrational {n : ℕ}
    (hn : Irrational (Real.sqrt (n : ℝ))) {a : ℚ} (ha : a ∈ rootApprox n) :
    (a : ℝ) < Real.sqrt (n : ℝ) :=
  lt_of_le_of_ne ((mem_rootApprox_iff n a).mp ha).2 (hn.ne_rat a).symm

/-- The exact real product is two, but no pair of raw root-two approximants
has rational product two. -/
theorem rootApprox_two_product_not_two :
    (2 : ℚ) ∉ Set.image2 (· * ·) (rootApprox 2) (rootApprox 2) := by
  rintro ⟨a, ha, b, hb, hab⟩
  have ha0 : (0 : ℝ) ≤ (a : ℝ) := by exact_mod_cast rootApprox_nonneg ha
  have haLt : (a : ℝ) < Real.sqrt (2 : ℝ) :=
    rootApprox_lt_sqrt_of_irrational irrational_sqrt_two ha
  have hbLe : (b : ℝ) ≤ Real.sqrt (2 : ℝ) := ((mem_rootApprox_iff 2 b).mp hb).2
  have hsPos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsmall : (a : ℝ) * (b : ℝ) < 2 := by
    calc
      (a : ℝ) * (b : ℝ) ≤ (a : ℝ) * Real.sqrt 2 :=
        mul_le_mul_of_nonneg_left hbLe ha0
      _ < Real.sqrt 2 * Real.sqrt 2 := mul_lt_mul_of_pos_right haLt hsPos
      _ = 2 := Real.mul_self_sqrt (by norm_num)
  have hprod : (a : ℝ) * (b : ℝ) = 2 := by exact_mod_cast hab
  linarith

end SquareKit.NonnegativeArithmetic
