import Applications.QuantumSemantics.Core
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Nonempty, normalized qubit states and actual complete measurements. -/

namespace QuantumSemantics.Qubit

open Matrix
open scoped ComplexOrder BigOperators

abbrev Q := Operator (Fin 2)

def p0 : Q := !![1, 0; 0, 0]
def p1 : Q := !![0, 0; 0, 1]
def x : Q := !![0, 1; 1, 0]
noncomputable def amplitude : ℝ := Real.sqrt (1 / 2)
noncomputable def hadamard : Q := !![(amplitude : ℂ), amplitude; amplitude, -(amplitude : ℂ)]
noncomputable def plus : Q := !![1 / 2, 1 / 2; 1 / 2, 1 / 2]
noncomputable def mixed : Q := !![1 / 2, 0; 0, 1 / 2]

lemma amplitude_sq : amplitude * amplitude = 1 / 2 := Real.mul_self_sqrt (by norm_num)

lemma amplitude_complex_sq : (amplitude : ℂ) * amplitude = 1 / 2 := by
  rw [← Complex.ofReal_mul, amplitude_sq]
  norm_num

@[simp] lemma p0_adjoint : p0ᴴ = p0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [p0, Matrix.conjTranspose_apply]

@[simp] lemma p1_adjoint : p1ᴴ = p1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [p1, Matrix.conjTranspose_apply]

@[simp] lemma p0_square : p0 * p0 = p0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [p0, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] lemma p1_square : p1 * p1 = p1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [p1, Matrix.mul_apply, Fin.sum_univ_two]

lemma projectors_complete : p0 + p1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [p0, p1]

lemma p0_positive : p0.PosSemidef := by
  simpa using Matrix.posSemidef_conjTranspose_mul_self p0

lemma p1_positive : p1.PosSemidef := by
  simpa using Matrix.posSemidef_conjTranspose_mul_self p1

lemma p0_effect : IsEffect p0 := by
  refine ⟨p0_positive, ?_⟩
  have he : 1 - p0 = p1 := by rw [← projectors_complete]; abel
  rw [he]
  exact p1_positive

lemma p1_effect : IsEffect p1 := by
  refine ⟨p1_positive, ?_⟩
  have he : 1 - p1 = p0 := by rw [← projectors_complete]; abel
  rw [he]
  exact p0_positive

@[simp] lemma p0_trace : p0.trace = 1 := by simp [p0, Matrix.trace, Fin.sum_univ_two]
@[simp] lemma p1_trace : p1.trace = 1 := by simp [p1, Matrix.trace, Fin.sum_univ_two]

lemma p0_state : IsState p0 := ⟨p0_positive, by simp⟩
lemma p1_state : IsState p1 := ⟨p1_positive, by simp⟩

@[simp] lemma x_adjoint : xᴴ = x := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [x, Matrix.conjTranspose_apply]

@[simp] lemma x_square : x * x = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [x, Matrix.mul_apply, Fin.sum_univ_two]

def bitFlip : Gate (Fin 2) := ⟨x, by simp, by simp⟩

@[simp] lemma hadamard_adjoint : hadamardᴴ = hadamard := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hadamard, Matrix.conjTranspose_apply]

@[simp] lemma hadamard_square : hadamard * hadamard = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [hadamard, Matrix.mul_apply, Fin.sum_univ_two, amplitude_complex_sq]

noncomputable def hadamardGate : Gate (Fin 2) := ⟨hadamard, by simp, by simp⟩

lemma hadamard_p0 : conjugate hadamard p0 = plus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [conjugate, hadamard, p0, plus, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.conjTranspose_apply, amplitude_complex_sq]

lemma plus_state : IsState plus := by
  rw [← hadamard_p0]
  exact gate_state hadamardGate p0_state

lemma plus_effect : IsEffect plus := by
  have h := effect_unitary hadamardGate p0_effect
  simpa [hadamardGate, ← hadamard_p0, conjugate] using h

lemma mixed_eq : mixed = (1 / 2 : ℝ) • (p0 + p1) := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [mixed, p0, p1, Matrix.smul_apply]

lemma mixed_state : IsState mixed := by
  refine ⟨?_, ?_⟩
  · rw [mixed_eq]
    exact (p0_positive.add p1_positive).smul (by norm_num : (0 : ℝ) ≤ 1 / 2)
  · norm_num [mixed, Matrix.trace, Fin.sum_univ_two]

/-- The finite outcome label remains classical data; branches carry quantum states. -/
def zMeasurement : Measurement (Fin 2) 2 where
  kraus := ![p0, p1]
  complete := by simpa [Fin.sum_univ_two] using projectors_complete

lemma z_branch_zero (ρ : Q) : conjugate (zMeasurement.kraus 0) ρ = (ρ 0 0) • p0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [zMeasurement, conjugate, p0, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]

lemma z_branch_one (ρ : Q) : conjugate (zMeasurement.kraus 1) ρ = (ρ 1 1) • p1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [zMeasurement, conjugate, p1, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]

lemma z_plus_probabilities (i : Fin 2) :
    (conjugate (zMeasurement.kraus i) plus).trace.re = 1 / 2 := by
  fin_cases i <;> simp [z_branch_zero, z_branch_one, plus, Matrix.trace_smul]

lemma z_mixed_probabilities (i : Fin 2) :
    (conjugate (zMeasurement.kraus i) mixed).trace.re = 1 / 2 := by
  fin_cases i <;> simp [z_branch_zero, z_branch_one, mixed, Matrix.trace_smul]

lemma equal_z_statistics (i : Fin 2) :
    (conjugate (zMeasurement.kraus i) plus).trace.re =
      (conjugate (zMeasurement.kraus i) mixed).trace.re := by
  rw [z_plus_probabilities, z_mixed_probabilities]

lemma plus_ne_mixed : plus ≠ mixed := by
  intro h
  have he := congrArg (fun A : Q => A 0 1) h
  norm_num [plus, mixed] at he

lemma plus_observation : expectation plus plus = 1 := by
  norm_num [expectation, plus, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two]

lemma mixed_observation : expectation plus mixed = 1 / 2 := by
  norm_num [expectation, plus, mixed, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two]

/-- Equal Z distributions do not preserve this other admitted effect. -/
lemma observation_separator : expectation plus plus ≠ expectation plus mixed := by
  rw [plus_observation, mixed_observation]
  norm_num

lemma incomplete_projector : p0ᴴ * p0 ≠ (1 : Q) := by
  simp only [p0_adjoint, p0_square]
  intro h
  have he := congrArg (fun A : Q => A 1 1) h
  simp [p0] at he

end QuantumSemantics.Qubit
