import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Complex.Order
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

/-! Finite density matrices, effects, and complete measurements. -/

namespace QuantumSemantics

open Matrix
open scoped BigOperators ComplexOrder

variable {n : Type} [Fintype n] [DecidableEq n]

abbrev Operator (n : Type) := Matrix n n ℂ

/-- Subnormalized density operator. Real-trace nonnegativity follows from positivity. -/
def IsState (ρ : Operator n) : Prop := ρ.PosSemidef ∧ ρ.trace.re ≤ 1

/-- An effect is a positive operator bounded above by the identity. -/
def IsEffect (A : Operator n) : Prop := A.PosSemidef ∧ (1 - A).PosSemidef

/-- Both adjoint inverse equations are explicit. -/
structure Gate (n : Type) [Fintype n] [DecidableEq n] where
  matrix : Operator n
  adjoint_mul : matrixᴴ * matrix = 1
  mul_adjoint : matrix * matrixᴴ = 1

/-- No outcome probabilities are divided out. Completeness is an operator equation. -/
structure Measurement (n : Type) [Fintype n] [DecidableEq n] (k : Nat) where
  kraus : Fin k → Operator n
  complete : ∑ i, (kraus i)ᴴ * kraus i = 1

def conjugate (M ρ : Operator n) : Operator n := M * ρ * Mᴴ

def expectation (A ρ : Operator n) : ℝ := (A * ρ).trace.re

omit [DecidableEq n] in
lemma trace_re_nonneg {ρ : Operator n} (h : ρ.PosSemidef) : 0 ≤ ρ.trace.re :=
  (Complex.nonneg_iff.mp h.trace_nonneg).1

omit [DecidableEq n] in
lemma trace_im_zero {ρ : Operator n} (h : ρ.PosSemidef) : ρ.trace.im = 0 :=
  (Complex.nonneg_iff.mp h.trace_nonneg).2.symm

omit [DecidableEq n] in
lemma expectation_real {A ρ : Operator n} (hA : A.IsHermitian) (hρ : ρ.IsHermitian) :
    (A * ρ).trace.im = 0 := by
  have hc : star (A * ρ).trace = (A * ρ).trace := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hA.eq, hρ.eq,
      Matrix.trace_mul_comm]
  have hi := congrArg Complex.im hc
  simp only [Complex.star_def, Complex.conj_im] at hi
  linarith

omit [DecidableEq n] in
lemma conjugate_pos {ρ : Operator n} (h : ρ.PosSemidef) (M : Operator n) :
    (conjugate M ρ).PosSemidef := h.mul_mul_conjTranspose_same M

omit [DecidableEq n] in
lemma trace_conjugate (M ρ : Operator n) :
    (conjugate M ρ).trace = ((Mᴴ * M) * ρ).trace := by
  exact Matrix.trace_mul_cycle M ρ Mᴴ

lemma trace_gate (U : Gate n) (ρ : Operator n) : (conjugate U.matrix ρ).trace = ρ.trace := by
  rw [trace_conjugate, U.adjoint_mul, Matrix.one_mul]

lemma gate_state (U : Gate n) {ρ : Operator n} (hρ : IsState ρ) :
    IsState (conjugate U.matrix ρ) :=
  ⟨conjugate_pos hρ.1 _, by simpa [trace_gate] using hρ.2⟩

lemma trace_sum_conjugate {k : Nat} (M : Measurement n k) (ρ : Operator n) :
    (∑ i, conjugate (M.kraus i) ρ).trace = ρ.trace := by
  simp only [Matrix.trace_sum, trace_conjugate]
  rw [← Matrix.trace_sum, ← Matrix.sum_mul, M.complete, Matrix.one_mul]

lemma branch_trace_sum {k : Nat} (M : Measurement n k) (ρ : Operator n) :
    ∑ i, (conjugate (M.kraus i) ρ).trace.re = ρ.trace.re := by
  simpa using congrArg Complex.re (trace_sum_conjugate M ρ)

/-- Actual unnormalized outcomes are admitted states, including probability-zero branches. -/
lemma branch_state {k : Nat} (M : Measurement n k) {ρ : Operator n}
    (hρ : IsState ρ) (i : Fin k) : IsState (conjugate (M.kraus i) ρ) := by
  refine ⟨conjugate_pos hρ.1 _, ?_⟩
  calc
    (conjugate (M.kraus i) ρ).trace.re ≤
        ∑ j, (conjugate (M.kraus j) ρ).trace.re :=
      Finset.single_le_sum (fun j _ => trace_re_nonneg (conjugate_pos hρ.1 _)) (Finset.mem_univ i)
    _ = ρ.trace.re := branch_trace_sum M ρ
    _ ≤ 1 := hρ.2

omit [DecidableEq n] in
/-- Cyclic trace supplies the precondition/branch expectation equation. -/
lemma expectation_conjugate (M A ρ : Operator n) :
    expectation (Mᴴ * A * M) ρ = expectation A (conjugate M ρ) := by
  unfold expectation conjugate
  congr 1
  calc
    (Mᴴ * A * M * ρ).trace = (Mᴴ * (A * M * ρ)).trace := by simp only [Matrix.mul_assoc]
    _ = (A * M * ρ * Mᴴ).trace := Matrix.trace_mul_comm _ _
    _ = (A * (M * ρ * Mᴴ)).trace := by simp only [Matrix.mul_assoc]

lemma effect_unitary (U : Gate n) {A : Operator n} (hA : IsEffect A) :
    IsEffect (U.matrixᴴ * A * U.matrix) := by
  refine ⟨hA.1.conjTranspose_mul_mul_same _, ?_⟩
  have h := hA.2.conjTranspose_mul_mul_same U.matrix
  simpa [Matrix.mul_sub, Matrix.sub_mul, U.adjoint_mul] using h

/-- The finite measurement precondition is itself an effect. -/
lemma effect_measurement {k : Nat} (M : Measurement n k) (A : Fin k → Operator n)
    (hA : ∀ i, IsEffect (A i)) : IsEffect (∑ i, (M.kraus i)ᴴ * A i * M.kraus i) := by
  constructor
  · exact Matrix.posSemidef_sum _ fun i _ => (hA i).1.conjTranspose_mul_mul_same _
  · have h : (∑ i, (M.kraus i)ᴴ * (1 - A i) * M.kraus i).PosSemidef :=
      Matrix.posSemidef_sum _ fun i _ => (hA i).2.conjTranspose_mul_mul_same _
    simpa [Matrix.mul_sub, Matrix.sub_mul, Finset.sum_sub_distrib, M.complete] using h

end QuantumSemantics
