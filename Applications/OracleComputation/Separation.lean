import Applications.OracleComputation.Coding
import Mathlib.Computability.Halting

/-! Ordinary halting answers and the strictly unresolved relative self-halting problem. -/

namespace OracleComputation

/-- Halting is defined by actual partial evaluation, including self-application of code indices. -/
def SelfHalts (oracle : Nat →. Nat) (n : Nat) : Prop :=
  (eval oracle (ofIndex n) n).Dom

/-- No total relative computation decides self-halting, with zero meaning nontermination. -/
theorem no_relative_halting_decider (oracle : Nat →. Nat) (d : Nat → Nat)
    (hd : Nat.RecursiveIn {oracle} (fun n => Part.some (d n)))
    (correct : ∀ n, d n = 0 ↔ ¬ SelfHalts oracle n) : False := by
  obtain ⟨c, hc⟩ := recursiveIn_iff_exists_code.mp hd
  let p := Code.rfind (.comp c .left)
  have hp (n : Nat) : (eval oracle p n).Dom ↔ d n = 0 := by
    simpa [p, eval, hc] using search_constant_dom d n
  have hk : SelfHalts oracle (index p) ↔ d (index p) = 0 := by
    simpa [SelfHalts] using hp (index p)
  have impossible := hk.trans (correct (index p))
  exact not_iff_self impossible.symm

/-- A total mathematical specification, with no claim of a relative executor. -/
noncomputable def jump (oracle : Nat →. Nat) (n : Nat) : Nat := by
  classical
  exact if SelfHalts oracle n then 1 else 0

@[simp] theorem jump_zero_iff (oracle : Nat →. Nat) (n : Nat) :
    jump oracle n = 0 ↔ ¬ SelfHalts oracle n := by
  classical
  simp [jump]

theorem jump_not_recursiveIn (oracle : Nat →. Nat) :
    ¬ Nat.RecursiveIn {oracle} (fun n => Part.some (jump oracle n)) := by
  intro h
  exact no_relative_halting_decider oracle (jump oracle) h (jump_zero_iff oracle)

/-- The ordinary property is independent of the oracle-language enumeration. -/
def OrdinaryHalts (c : Nat.Partrec.Code) : Prop := (Nat.Partrec.Code.eval c 0).Dom

/-- Answers ordinary halting at input zero for the standard Mathlib enumeration. -/
noncomputable def haltingAnswer (n : Nat) : Nat := by
  classical
  exact if OrdinaryHalts (Denumerable.ofNat Nat.Partrec.Code n) then 1 else 0

noncomputable def haltingOracle : Nat →. Nat := fun n => Part.some (haltingAnswer n)

@[simp] theorem haltingAnswer_one_iff (c : Nat.Partrec.Code) :
    haltingAnswer (Encodable.encode c) = 1 ↔ OrdinaryHalts c := by
  classical
  simp [haltingAnswer]

theorem haltingAnswer_boolean (n : Nat) : haltingAnswer n = 0 ∨ haltingAnswer n = 1 := by
  classical
  simp only [haltingAnswer]
  split <;> simp

theorem haltingOracle_total (n : Nat) : (haltingOracle n).Dom := trivial

/-- This separation reuses actual ordinary-program undecidability, not an assumed oracle property. -/
theorem haltingOracle_not_partrec : ¬ Nat.Partrec haltingOracle := by
  intro h
  have hc : Computable haltingAnswer := Partrec.nat_iff.mpr h
  have hp : ComputablePred (fun c : Nat.Partrec.Code =>
      haltingAnswer (Encodable.encode c) = 1) := by
    exact (Primrec.eq.decide.to_comp.comp
      (hc.comp Computable.encode) (Computable.const 1)).computablePred
  exact ComputablePred.halting_problem 0 (hp.of_eq haltingAnswer_one_iff)

/-- The query is a genuine additional capability over ordinary partial computation. -/
theorem halting_query_relative : Nat.RecursiveIn {haltingOracle} (eval haltingOracle .query) :=
  eval_recursiveIn _ _

theorem halting_query_not_ordinary : ¬ Nat.Partrec (eval haltingOracle .query) :=
  haltingOracle_not_partrec

/-- The concrete enlarged class still cannot answer its own self-halting problem. -/
theorem haltingOracle_cannot_solve_own_jump :
    ¬ Nat.RecursiveIn {haltingOracle} (fun n => Part.some (jump haltingOracle n)) :=
  jump_not_recursiveIn haltingOracle

end OracleComputation
