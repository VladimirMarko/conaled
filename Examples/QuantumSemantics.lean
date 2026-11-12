import Applications.QuantumSemantics.Qubit
import Applications.QuantumSemantics.Rules
import Applications.QuantumSemantics.Permutations

/-! Measurement with classical feedback, rule-derived verification, and observation limits. -/

namespace Examples.QuantumSemantics

open _root_.QuantumSemantics
open _root_.QuantumSemantics.Qubit
open Matrix
open scoped BigOperators ComplexOrder

/-- The bit flip agrees with the existing coherent permutation backend. -/
theorem bitFlip_coordinates :
    (permutationGate (Equiv.swap (0 : Fin 2) 1)).matrix = x := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [permutationGate, Uncomputation.coordinates_entry, x]

def zeroEffect : Effect (Fin 2) := ⟨p0, p0_effect⟩

def oneEffect : Effect (Fin 2) := ⟨1, Matrix.PosSemidef.one, by simp; exact .zero⟩

def feedback : Fin 2 → Program (Fin 2) := ![.skip, .unitary bitFlip]

def reset : Program (Fin 2) := .measure zMeasurement feedback

def branchPre : Fin 2 → Effect (Fin 2) := ![zeroEffect, unitaryPre bitFlip zeroEffect]

lemma reset_pre : (measurementPre zMeasurement branchPre).matrix = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [measurementPre, zMeasurement, branchPre, unitaryPre, zeroEffect, bitFlip,
      p0, p1, x, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply]

/-- R.IF combines the skip and unitary proofs; it does not assume the reset postcondition. -/
theorem reset_sound : Valid oneEffect reset zeroEffect := by
  have hb (i : Fin 2) : Valid (branchPre i) (feedback i) zeroEffect := by
    fin_cases i
    · exact skip_sound zeroEffect
    · exact unitary_sound bitFlip zeroEffect
  have hr := measurement_sound zMeasurement feedback branchPre zeroEffect hb
  intro ρ hρ
  have h := hr ρ hρ
  simpa only [reset_pre, oneEffect, reset] using h

/-- Independently specified reset channel, proved for every input matrix. -/
theorem reset_denote (ρ : Q) : denote reset ρ = ρ.trace • p0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [reset, feedback, denote, zMeasurement, bitFlip, conjugate, p0, p1, x,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct, Matrix.trace]

/-- A normalized admitted input is reset to the zero state. -/
theorem reset_normalized {ρ : Q} (_hρ : IsState ρ) (htrace : ρ.trace = 1) :
    denote reset ρ = p0 := by
  rw [reset_denote, htrace, one_smul]

noncomputable def prepareAndReset : Program (Fin 2) := .seq (.unitary hadamardGate) reset

lemma gate_one_sound (U : Gate (Fin 2)) : Valid oneEffect (.unitary U) oneEffect := by
  have h := unitary_sound U oneEffect
  simpa [Valid, unitaryPre, oneEffect, U.adjoint_mul] using h

/-- R.SC composes actual preparation with the measurement/control rule proof. -/
theorem prepareAndReset_sound : Valid oneEffect prepareAndReset zeroEffect :=
  sequence_sound (gate_one_sound hadamardGate) reset_sound

/-- Partial correctness agrees here because the actual finite semantics preserves trace. -/
theorem prepareAndReset_partial : PartialValid oneEffect prepareAndReset zeroEffect :=
  (partial_iff_total _ _ _).mpr prepareAndReset_sound

theorem prepareAndReset_output : denote prepareAndReset p0 = p0 := by
  change denote reset (conjugate hadamard p0) = p0
  rw [hadamard_p0, reset_denote]
  have ht : plus.trace = 1 := by
    rw [← hadamard_p0]
    exact (trace_gate hadamardGate p0).trans p0_trace
  rw [ht, one_smul]

/-- Outcome weights remain observable after the feedback continuation. -/
theorem feedback_half (i : Fin 2) :
    (instrument zMeasurement feedback (conjugate hadamard p0) i).trace.re = 1 / 2 := by
  rw [instrument_probability, hadamard_p0]
  exact z_plus_probabilities i

/-- Each unnormalized feedback branch is half of the zero-state density matrix. -/
theorem feedback_branch (i : Fin 2) :
    instrument zMeasurement feedback (conjugate hadamard p0) i = (1 / 2 : ℂ) • p0 := by
  rw [hadamard_p0]
  fin_cases i <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    norm_num [instrument, feedback, denote, zMeasurement, bitFlip, conjugate, p0, p1,
      plus, x, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]

/-- This control error keeps the one branch instead of resetting it. -/
def wrongFeedback : Program (Fin 2) := .measure zMeasurement (fun _ => .skip)

lemma wrongFeedback_p1 : denote wrongFeedback p1 = p1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [wrongFeedback, denote, zMeasurement, conjugate, p0, p1,
      Fin.sum_univ_two, Matrix.vecMul, dotProduct]

theorem wrongFeedback_rejected : ¬ Valid oneEffect wrongFeedback zeroEffect := by
  intro h
  have bad := h p1 p1_state
  rw [wrongFeedback_p1] at bad
  norm_num [oneEffect, zeroEffect, expectation, p0, p1, Matrix.trace, Matrix.mul_apply,
    Fin.sum_univ_two] at bad

/-- The separator retains positive states and an actual positive bounded observation. -/
theorem admitted_observation_separator :
    IsState plus ∧ IsState mixed ∧ IsEffect plus ∧
      (∀ i, (conjugate (zMeasurement.kraus i) plus).trace.re =
        (conjugate (zMeasurement.kraus i) mixed).trace.re) ∧
      plus ≠ mixed ∧ expectation plus plus ≠ expectation plus mixed :=
  ⟨plus_state, mixed_state, plus_effect, equal_z_statistics, plus_ne_mixed, observation_separator⟩

/-- A one-projector family cannot satisfy the completeness contract. -/
theorem no_single_projector_measurement :
    ¬ ∃ M : Measurement (Fin 2) 1, M.kraus 0 = p0 := by
  rintro ⟨M, h⟩
  have hm := M.complete
  simp only [Fin.sum_univ_one, h] at hm
  exact incomplete_projector hm

end Examples.QuantumSemantics
