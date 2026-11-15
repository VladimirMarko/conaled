import Applications.OracleComputation.Compilation
import Applications.OracleComputation.Separation

/-! Bounded observations and the distinction between pointwise witnesses and effective selection. -/

namespace OracleComputation

/-- `none` means unknown at this bound. The bound is Mathlib's numeric/recursion bound,
not a count of abstract-machine steps. -/
abbrev observe (k : Nat) (c : Nat.Partrec.Code) (n : Nat) : Option Nat := c.evaln k n

theorem observe_sound {k n v : Nat} {c : Nat.Partrec.Code}
    (h : observe k c n = some v) : v ∈ c.eval n :=
  Nat.Partrec.Code.evaln_sound h

theorem observe_mono {k l n v : Nat} {c : Nat.Partrec.Code}
    (hkl : k ≤ l) (h : observe k c n = some v) : observe l c n = some v :=
  Nat.Partrec.Code.evaln_mono hkl h

theorem observe_complete (c : Nat.Partrec.Code) (n v : Nat) :
    v ∈ c.eval n ↔ ∃ k, observe k c n = some v := Nat.Partrec.Code.evaln_complete

theorem observe_primrec : Primrec fun a : (Nat × Nat.Partrec.Code) × Nat =>
    observe a.1.1 a.1.2 a.2 := Nat.Partrec.Code.primrec_evaln

theorem observe_divergent {c : Nat.Partrec.Code} {n : Nat} (h : ¬ (c.eval n).Dom)
    (k : Nat) : observe k c n = none := by
  cases he : observe k c n with
  | none => rfl
  | some v => exact False.elim (h (observe_sound he).1)

/-- A result at input zero certifies the positive answer, not its converse at a fixed bound. -/
theorem observe_halting {k v : Nat} {c : Nat.Partrec.Code}
    (h : observe k c 0 = some v) : haltingAnswer (Encodable.encode c) = 1 :=
  (haltingAnswer_one_iff c).mpr (observe_sound h).1

/-- Forget the observed output value but retain positive termination evidence. -/
def observeAnswer (k index : Nat) : Option Nat :=
  (observe k (Denumerable.ofNat Nat.Partrec.Code index) 0).map (fun _ => 1)

/-- Unknown imposes no answer constraint; observed answers must agree. -/
def AnswerObservation (result : Option Nat) (answer : Nat) : Prop :=
  ∀ v, result = some v → v = answer

theorem observeAnswer_sound (k index : Nat) :
    AnswerObservation (observeAnswer k index) (haltingAnswer index) := by
  intro v hv
  obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp hv
  have h := observe_halting hw
  simpa using h.symm

/-- Every individual correct answer has a constant program. This is not effective selection. -/
theorem answer_code_exists (n : Nat) : ∃ q : Nat.Partrec.Code,
    ∀ m, q.eval m = Part.some (haltingAnswer n) :=
  ⟨Nat.Partrec.Code.const (haltingAnswer n), Nat.Partrec.Code.eval_const _⟩

/-- A uniformly computable selection of even input-zero-correct programs would decide halting. -/
theorem no_computable_answer_selector (select : Nat → Nat.Partrec.Code)
    (hselect : Computable select)
    (correct : ∀ n, (select n).eval 0 = Part.some (haltingAnswer n)) : False := by
  have h : Partrec (fun n => (select n).eval 0) :=
    Nat.Partrec.Code.eval_part.comp hselect (Computable.const 0)
  apply haltingOracle_not_partrec
  exact Partrec.nat_iff.mp (h.of_eq correct)

/-- When the answer is already supplied, the constant-program constructor is effective. -/
theorem supplied_answer_constructor : Primrec Nat.Partrec.Code.const :=
  Nat.Partrec.Code.primrec_const

end OracleComputation
