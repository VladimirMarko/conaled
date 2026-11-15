import Applications.QuantumSemantics.Core

/-! Loop-free quantum programs and their independently defined density-operator denotation. -/

namespace QuantumSemantics

open Matrix
open scoped BigOperators ComplexOrder

variable {n : Type} [Fintype n] [DecidableEq n]

inductive Program (n : Type) [Fintype n] [DecidableEq n] where
  | skip
  | unitary : Gate n → Program n
  | seq : Program n → Program n → Program n
  | measure {k : Nat} : Measurement n k → (Fin k → Program n) → Program n

/-- Classical outcomes select continuations; the unconditioned result sums their states. -/
def denote : Program n → Operator n → Operator n
  | .skip, ρ => ρ
  | .unitary U, ρ => conjugate U.matrix ρ
  | .seq c d, ρ => denote d (denote c ρ)
  | .measure M c, ρ => ∑ i, denote (c i) (conjugate (M.kraus i) ρ)

/-- The instrument retains the outcome label and unnormalized branch state. -/
def instrument {k : Nat} (M : Measurement n k) (c : Fin k → Program n)
    (ρ : Operator n) (i : Fin k) : Operator n := denote (c i) (conjugate (M.kraus i) ρ)

theorem denote_positive (c : Program n) {ρ : Operator n} (hρ : ρ.PosSemidef) :
    (denote c ρ).PosSemidef := by
  induction c generalizing ρ with
  | skip => exact hρ
  | unitary U => exact conjugate_pos hρ _
  | seq c d hc hd => exact hd (hc hρ)
  | measure M c ih =>
    exact Matrix.posSemidef_sum _ fun i _ => ih i (conjugate_pos hρ _)

/-- Trace preservation is proved from unitary equations and measurement completeness. -/
theorem denote_trace (c : Program n) (ρ : Operator n) : (denote c ρ).trace = ρ.trace := by
  induction c generalizing ρ with
  | skip => rfl
  | unitary U => exact trace_gate U ρ
  | seq c d hc hd => exact (hd _).trans (hc ρ)
  | measure M c ih =>
    simp only [denote, Matrix.trace_sum, ih]
    simpa only [Matrix.trace_sum] using trace_sum_conjugate M ρ

theorem denote_state (c : Program n) {ρ : Operator n} (hρ : IsState ρ) : IsState (denote c ρ) :=
  ⟨denote_positive c hρ.1, by simpa only [denote_trace] using hρ.2⟩

theorem instrument_state {k : Nat} (M : Measurement n k) (c : Fin k → Program n)
    {ρ : Operator n} (hρ : IsState ρ) (i : Fin k) : IsState (instrument M c ρ i) :=
  denote_state _ (branch_state M hρ i)

theorem instrument_probability {k : Nat} (M : Measurement n k) (c : Fin k → Program n)
    (ρ : Operator n) (i : Fin k) :
    (instrument M c ρ i).trace = (conjugate (M.kraus i) ρ).trace := denote_trace _ _

/-- Linear combination laws concern denotations, not copying of unknown states. -/
theorem denote_add (c : Program n) (ρ σ : Operator n) :
    denote c (ρ + σ) = denote c ρ + denote c σ := by
  induction c generalizing ρ σ with
  | skip => rfl
  | unitary U => simp [denote, conjugate, Matrix.mul_add, Matrix.add_mul]
  | seq c d hc hd => simp only [denote, hc, hd]
  | measure M c ih => simp [denote, conjugate, Matrix.mul_add, Matrix.add_mul, ih,
      Finset.sum_add_distrib]

theorem denote_smul (c : Program n) (a : ℂ) (ρ : Operator n) :
    denote c (a • ρ) = a • denote c ρ := by
  induction c generalizing ρ with
  | skip => rfl
  | unitary U => simp [denote, conjugate]
  | seq c d hc hd => simp only [denote, hc, hd]
  | measure M c ih => simp [denote, conjugate, ih,
      Finset.smul_sum]

end QuantumSemantics
