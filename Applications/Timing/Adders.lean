import Applications.Circuits.Correctness
import Mathlib.Tactic.FinCases

/-!
# Adders, calculated timing matrices, and a reconvergent-path hazard

The gate delays and input order reproduce the examples in Elliott's
*Timely Computation*.  The full adder is also obtained from a source term
with two let bindings; its complete analog, value, and timing interpretations
agree with the explicitly factored circuit.
-/

namespace Applications.Timing.Adders

open FirstOrderCompiler Applications.Circuits
open scoped Matrix

abbrev Bits : Ty := .prod .base .base
abbrev Triple : Ty := .prod Bits .base

def halfAdder : Circuit Bits Bits := .pair Circuit.xor Circuit.and

/-- First combine `b,c`, then combine `a` with their sum, then merge carries. -/
def fullAdder : Circuit Triple Bits :=
  let firstHA : Circuit Triple Bits :=
    .compose halfAdder (.pair (.compose .second .first) .second)
  let secondHA : Circuit Triple Bits :=
    .compose halfAdder (.pair (.compose .first .first) (.compose .first firstHA))
  .pair (.compose .first secondHA)
    (.compose Circuit.or (.pair (.compose .second secondHA) (.compose .second firstHA)))

def halfAdderTerm (input : Term Gate Γ Bits) : Term Gate Γ Bits :=
  .pair (.prim (.xor (1 / 4) (1 / 4)) input)
    (.prim (.not (1 / 10)) (.prim (.nand (1 / 5) (1 / 5)) input))

/-- A genuine first-order source program, preserving two let-bound results. -/
def fullAdderTerm : Term Gate [Triple] Bits :=
  .letE (halfAdderTerm (.pair (.snd (.fst (.var .here))) (.snd (.var .here))))
    (.letE (halfAdderTerm (.pair (.fst (.fst (.var (.there .here)))) (.fst (.var .here))))
      (.pair (.fst (.var .here))
        (.prim (.not (1 / 10))
          (.prim (.nor (1 / 5) (1 / 5))
            (.pair (.snd (.var .here)) (.snd (.var (.there .here))))))))

def compiledFullAdder : Circuit Triple Bits :=
  .compose (compile Circuit.target fullAdderTerm) (.pair .terminate .identity)

/-- The source compiler agrees on all three interpretations, including timing. -/
theorem compiled_fullAdder : compiledFullAdder.digital = fullAdder.digital := by
  apply Digital.ext <;> intro x <;> rfl

theorem halfAdder_value (a b : Bool) :
    halfAdder.digital.value (a, b) = (Bool.xor a b, a && b) := by
  cases a <;> cases b <;> rfl

theorem halfAdder_addition (a b : Bool) :
    let r := halfAdder.digital.value (a, b)
    r.1.toNat + 2 * r.2.toNat = a.toNat + b.toNat := by
  cases a <;> cases b <;> rfl

theorem fullAdder_addition (a b c : Bool) :
    let r := fullAdder.digital.value ((a, b), c)
    r.1.toNat + 2 * r.2.toNat = a.toNat + b.toNat + c.toNat := by
  cases a <;> cases b <;> cases c <;> rfl

theorem source_addition (a b c : Bool) :
    let r := eval Gate.meaning fullAdderTerm ((), ((a, b), c))
    r.1.toNat + 2 * r.2.toNat = a.toNat + b.toNat + c.toNat := by
  cases a <;> cases b <;> cases c <;> rfl

def sumPort : Port Bits := .inl 0
def carryPort : Port Bits := .inr 0
def inputA : Port Triple := .inl (.inl 0)
def inputB : Port Triple := .inl (.inr 0)
def inputC : Port Triple := .inr 0

/-- The locally calculated timing expression, before collecting path delays. -/
def halfAdderTiming (τ : Times Bits) : Times Bits :=
  Sum.elim
    (fun _ => Interval.point (1 / 4) * τ (.inl 0) + Interval.point (1 / 4) * τ (.inr 0))
    (fun _ => Interval.point (1 / 10) *
      (Interval.point (1 / 5) * τ (.inl 0) + Interval.point (1 / 5) * τ (.inr 0)))

theorem halfAdder_timing (τ : Times Bits) : halfAdder.digital.timing τ = halfAdderTiming τ := rfl

def fullAdderTiming (τ : Times Triple) : Times Bits :=
  let firstSum := Interval.point (1 / 4) * τ inputB + Interval.point (1 / 4) * τ inputC
  let firstCarry := Interval.point (1 / 10) *
    (Interval.point (1 / 5) * τ inputB + Interval.point (1 / 5) * τ inputC)
  let secondCarry := Interval.point (1 / 10) *
    (Interval.point (1 / 5) * τ inputA + Interval.point (1 / 5) * firstSum)
  Sum.elim
    (fun _ => Interval.point (1 / 4) * τ inputA + Interval.point (1 / 4) * firstSum)
    (fun _ => Interval.point (1 / 10) *
      (Interval.point (1 / 5) * secondCarry + Interval.point (1 / 5) * firstCarry))

theorem fullAdder_timing (τ : Times Triple) : fullAdder.digital.timing τ = fullAdderTiming τ := rfl

/-- Row order is sum, carry; both input columns are equal. -/
def halfAdderMatrix : Matrix (Port Bits) (Port Bits) Interval :=
  Sum.elim (fun _ _ => Interval.point (1 / 4)) (fun _ _ => Interval.point (3 / 10))

/-- The carry entries for `b,c` retain the negative width `3/5 - 17/20`. -/
def fullAdderMatrix : Matrix (Port Bits) (Port Triple) Interval :=
  Sum.elim
    (fun _ => Sum.elim
      (Sum.elim (fun _ => Interval.point (1 / 4)) (fun _ => Interval.point (1 / 2)))
      (fun _ => Interval.point (1 / 2)))
    (fun _ => Sum.elim
      (Sum.elim (fun _ => Interval.point (3 / 5))
        (fun _ => Interval.finite (17 / 20) (3 / 5)))
      (fun _ => Interval.finite (17 / 20) (3 / 5)))

theorem halfAdder_matrix : halfAdder.digital.matrix = halfAdderMatrix := by
  funext out inp
  rcases out with out | out <;> rcases inp with inp | inp <;>
    fin_cases out <;> fin_cases inp
  all_goals
    simp only [Digital.matrix, LinearMap.toMatrix'_apply]
    rw [halfAdder_timing]
    simp [halfAdderTiming, halfAdderMatrix] <;> norm_num

theorem fullAdder_matrix : fullAdder.digital.matrix = fullAdderMatrix := by
  funext out inp
  rcases out with out | out <;> fin_cases out <;>
    rcases inp with (inp | inp) | inp <;> fin_cases inp
  all_goals
    simp only [Digital.matrix, LinearMap.toMatrix'_apply]
    rw [fullAdder_timing]
    simp [fullAdderTiming, fullAdderMatrix, inputA, inputB, inputC,
      mul_add, ← mul_assoc] <;> norm_num [Interval.point, Interval.finite_add]

theorem compiledFullAdder_matrix : compiledFullAdder.digital.matrix = fullAdderMatrix := by
  rw [compiled_fullAdder, fullAdder_matrix]

/-- Matrix-calculated output intervals carry a proof valid at every enclosed time. -/
theorem fullAdder_stable {s τ v} (h : Stable Triple s τ v) :
    Stable Bits (fullAdder.digital.analog s) (fullAdderMatrix *ᵥ τ)
      (fullAdder.digital.value v) := by
  rw [← fullAdder_matrix]
  exact fullAdder.digital.matrix_stable h

/-- A falling input with both other inputs true has logically constant carry. -/
def hazardInput : Val Signal Triple := ((fun _ => true, fun t => decide (t < 0)), fun _ => true)

theorem hazard_expected_carry (b : Bool) :
    (fullAdder.digital.value ((true, b), true)).2 = true := by
  cases b <;> rfl

/-- The actual gate model drops the carry at a time between the path delays. -/
theorem hazard_at_seven_tenths :
    (fullAdder.digital.analog hazardInput).2 (7 / 10) = false := by
  norm_num [fullAdder, halfAdder, hazardInput,
    Circuit.xor, Circuit.and, Circuit.nand, Circuit.not, Circuit.or, Circuit.nor,
    Gate.digital, Digital.binary, Digital.unary]

theorem hazard_before_and_after :
    (fullAdder.digital.analog hazardInput).2 0 = true ∧
      (fullAdder.digital.analog hazardInput).2 1 = true := by
  norm_num [fullAdder, halfAdder, hazardInput,
    Circuit.xor, Circuit.and, Circuit.nand, Circuit.not, Circuit.or, Circuit.nor,
    Gate.digital, Digital.binary, Digital.unary]

/-- Retained setup/hold bounds demand at least a quarter-unit input width. -/
theorem carry_path_nonempty_iff (lo hi : Time) :
    (∃ t, (Interval.finite (17 / 20) (3 / 5) * Interval.finite lo hi).Contains t) ↔
      1 / 4 ≤ hi - lo := by
  rw [Interval.finite_mul]
  simp only [Interval.contains_finite]
  constructor
  · rintro ⟨t, hlo, hhi⟩
    linarith
  · intro h
    refine ⟨17 / 20 + lo, le_rfl, ?_⟩
    linarith

/-- The inverted coefficient is not discarded: a wide input yields a useful interval. -/
theorem repaired_carry_path :
    Interval.finite (17 / 20) (3 / 5) * Interval.finite 0 1 =
      Interval.finite (17 / 20) (8 / 5) := by
  rw [Interval.finite_mul]
  norm_num

end Applications.Timing.Adders
