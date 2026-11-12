import Applications.QuantumSemantics.Program

/-! Full-register specializations of CoqQ's unitary, conditional and sequencing rules. -/

namespace QuantumSemantics

open Matrix
open scoped BigOperators ComplexOrder

variable {n : Type} [Fintype n] [DecidableEq n]

/-- Assertions carry their actual positivity and upper-bound proofs. -/
structure Effect (n : Type) [Fintype n] [DecidableEq n] where
  matrix : Operator n
  valid : IsEffect matrix

def Valid (A : Effect n) (c : Program n) (B : Effect n) : Prop :=
  ∀ ρ, IsState ρ → expectation A.matrix ρ ≤ expectation B.matrix (denote c ρ)

/-- The source partial-correctness trace-loss term is retained explicitly. -/
def PartialValid (A : Effect n) (c : Program n) (B : Effect n) : Prop :=
  ∀ ρ, IsState ρ → expectation A.matrix ρ ≤
    expectation B.matrix (denote c ρ) + (ρ.trace.re - (denote c ρ).trace.re)

theorem partial_iff_total (A : Effect n) (c : Program n) (B : Effect n) :
    PartialValid A c B ↔ Valid A c B := by
  simp only [PartialValid, Valid, denote_trace, sub_self, add_zero]

def unitaryPre (U : Gate n) (B : Effect n) : Effect n :=
  ⟨U.matrixᴴ * B.matrix * U.matrix, effect_unitary U B.valid⟩

def measurementPre {k : Nat} (M : Measurement n k) (A : Fin k → Effect n) : Effect n :=
  ⟨∑ i, (M.kraus i)ᴴ * (A i).matrix * M.kraus i,
    effect_measurement M (fun i => (A i).matrix) (fun i => (A i).valid)⟩

theorem skip_sound (A : Effect n) : Valid A .skip A := fun _ _ => le_rfl

/-- CoqQ Ax.UT specialized to the full register. -/
theorem unitary_sound (U : Gate n) (B : Effect n) : Valid (unitaryPre U B) (.unitary U) B := by
  intro ρ _
  exact le_of_eq (expectation_conjugate U.matrix B.matrix ρ)

/-- CoqQ R.SC: the intermediate denotation is an admitted state by a separate theorem. -/
theorem sequence_sound {A B C : Effect n} {c d : Program n}
    (h₁ : Valid A c B) (h₂ : Valid B d C) : Valid A (.seq c d) C := by
  intro ρ hρ
  exact le_trans (h₁ ρ hρ) (h₂ (denote c ρ) (denote_state c hρ))

omit [DecidableEq n] in
lemma expectation_sum_left {k : Nat} (A : Fin k → Operator n) (ρ : Operator n) :
    expectation (∑ i, A i) ρ = ∑ i, expectation (A i) ρ := by
  simp [expectation, Matrix.sum_mul, Matrix.trace_sum]

omit [DecidableEq n] in
lemma expectation_sum_right {k : Nat} (A : Operator n) (ρ : Fin k → Operator n) :
    expectation A (∑ i, ρ i) = ∑ i, expectation A (ρ i) := by
  simp [expectation, Matrix.mul_sum, Matrix.trace_sum]

/-- CoqQ R.IF: sound for actual unnormalized measurement branches, including zero probability. -/
theorem measurement_sound {k : Nat} (M : Measurement n k) (c : Fin k → Program n)
    (A : Fin k → Effect n) (B : Effect n) (h : ∀ i, Valid (A i) (c i) B) :
    Valid (measurementPre M A) (.measure M c) B := by
  intro ρ hρ
  change expectation (∑ i, (M.kraus i)ᴴ * (A i).matrix * M.kraus i) ρ ≤
    expectation B.matrix (∑ i, denote (c i) (conjugate (M.kraus i) ρ))
  rw [expectation_sum_left, expectation_sum_right]
  apply Finset.sum_le_sum
  intro i _
  rw [expectation_conjugate]
  exact h i _ (branch_state M hρ i)

/-- A precise compositional precondition for this finite syntax. -/
def pre : Program n → Effect n → Effect n
  | .skip, B => B
  | .unitary U, B => unitaryPre U B
  | .seq c d, B => pre c (pre d B)
  | .measure M c, B => measurementPre M (fun i => pre (c i) B)

/-- Generated proofs use the independently proved source rules. -/
theorem pre_sound (c : Program n) (B : Effect n) : Valid (pre c B) c B := by
  induction c generalizing B with
  | skip => exact skip_sound B
  | unitary U => exact unitary_sound U B
  | seq c d hc hd => exact sequence_sound (hc _) (hd B)
  | measure M c ih => exact measurement_sound M c _ B (fun i => ih i B)

/-- Equality for this loop-free precondition does not assert a full-qwhile completeness theorem. -/
theorem pre_expectation (c : Program n) (B : Effect n) (ρ : Operator n) :
    expectation (pre c B).matrix ρ = expectation B.matrix (denote c ρ) := by
  induction c generalizing B ρ with
  | skip => rfl
  | unitary U => exact expectation_conjugate _ _ _
  | seq c d hc hd => exact (hc _ _).trans (hd _ _)
  | measure M c ih =>
    change expectation (∑ i, (M.kraus i)ᴴ * (pre (c i) B).matrix * M.kraus i) ρ =
      expectation B.matrix (∑ i, denote (c i) (conjugate (M.kraus i) ρ))
    rw [expectation_sum_left, expectation_sum_right]
    apply Finset.sum_congr rfl
    intro i _
    rw [expectation_conjugate, ih]

end QuantumSemantics
