import Applications.OracleComputation.Compilation
import Applications.OracleComputation.Separation

/-! Public clients exercise adequate oracle computation, realizations and both separations. -/

namespace Examples.OracleComputation

open _root_.OracleComputation

/-- An actual ordinary program implements the selected oracle. -/
def plusTwo : Nat.Partrec.Code := .comp .succ .succ

@[simp] theorem plusTwo_eval (n : Nat) : plusTwo.eval n = Part.some (n + 2) := by
  change Part.bind (Part.some (n + 1)) (fun x => Part.some (x + 1)) = _
  rw [Part.bind_some]

/-- Search for the first zero, then use the supplied oracle twice. -/
def program : Code := .comp .query (.comp .query (.rfind .zero))

theorem zero_search (oracle : Nat →. Nat) (n : Nat) :
    eval oracle (.rfind .zero) n = Part.some 0 := by
  apply Part.eq_some_iff.mpr
  exact Nat.mem_rfind.mpr (by simp [eval])

/-- Two increments of two after the zero search give four for every input. -/
theorem program_value (n : Nat) : eval plusTwo.eval program n = Part.some 4 := by
  change (eval plusTwo.eval (.rfind .zero) n >>= plusTwo.eval) >>= plusTwo.eval = _
  rw [zero_search]
  change Part.bind (Part.bind (Part.some 0) (fun x => plusTwo.eval x))
    (fun x => plusTwo.eval x) = _
  rw [Part.bind_some, plusTwo_eval, Part.bind_some, plusTwo_eval]

theorem program_artifact : emit program = [4, 4, 0, 8, 6, 6] := rfl

/-- The nontrivial emitted instruction sequence uses the general compiler theorem. -/
theorem compiled_program :
    artifact plusTwo.eval [4, 4, 0, 8, 6, 6] = some (fun _ => Part.some 4) := by
  rw [← program_artifact, artifact_emit]
  congr 1
  funext n
  exact program_value n

/-- Ordinary execution is backed by a chosen program, not by a claimed executable oracle. -/
theorem ordinary_program (n : Nat) :
    Nat.Partrec.Code.eval (toOrdinary plusTwo program) n = Part.some 4 := by
  rw [toOrdinary_correct]
  exact program_value n

/-- Code generation and syntax validation are effective even for an unavailable oracle. -/
theorem query_instruction : emit .query = [4] := rfl

theorem malformed_underflow : parse [6] = none := rfl

theorem malformed_tag : parse [9] = none := rfl

theorem extra_stack : parse [0, 1] = none := rfl

theorem semantic_underflow (oracle : Nat →. Nat) : artifact oracle [6] = none := rfl

/-- A genuine divergent source program, independent of the chosen oracle. -/
def diverge : Code := .rfind (.comp .succ .zero)

theorem diverge_never (oracle : Nat →. Nat) (n : Nat) : ¬ (eval oracle diverge n).Dom := by
  simpa [diverge, eval] using search_constant_dom (fun _ => 1) n

/-- An explicit standard Code, not a hypothetical counterexample. -/
def ordinaryDiverge : Nat.Partrec.Code := toOrdinary .zero diverge

theorem ordinaryDiverge_never (n : Nat) : ¬ (ordinaryDiverge.eval n).Dom := by
  rw [ordinaryDiverge, toOrdinary_correct]
  exact diverge_never _ _

theorem halting_positive :
    haltingAnswer (Encodable.encode Nat.Partrec.Code.zero) = 1 :=
  (haltingAnswer_one_iff _).mpr trivial

theorem halting_negative : haltingAnswer (Encodable.encode ordinaryDiverge) = 0 := by
  classical
  simp [haltingAnswer, OrdinaryHalts, ordinaryDiverge_never]

/-- The same one-instruction artifact has a valid mathematical interpretation here. -/
theorem halting_artifact : artifact haltingOracle (emit .query) = some haltingOracle :=
  artifact_emit _ _

/-- No ordinary program realizes that interpreted query on all inputs. -/
theorem no_ordinary_halting_realizer (q : Nat.Partrec.Code) : q.eval ≠ haltingOracle := by
  intro h
  apply haltingOracle_not_partrec
  exact Nat.Partrec.Code.exists_code.mpr ⟨q, h⟩

/-- Ordinary halting capability does not provide self-halting for the enlarged class. -/
theorem relative_separation :
    ¬ Nat.RecursiveIn {haltingOracle} (fun n => Part.some (jump haltingOracle n)) :=
  haltingOracle_cannot_solve_own_jump

/-- A total oracle does not make minimization total. -/
theorem total_query_divergent_search (n : Nat) :
    ¬ (eval (fun _ => Part.some 1) (.rfind .query) n).Dom := by
  simpa [eval] using search_constant_dom (fun _ => 1) n

theorem alternate_query_terminates (n : Nat) :
    (eval (fun _ => Part.some 0) (.rfind .query) n).Dom := by
  simpa [eval] using (search_constant_dom (fun _ => 0) n).mpr rfl

/-- Omitting an oracle-equality premise would falsely preserve results. -/
theorem query_answer_changes :
    eval (fun _ => Part.some 0) .query 7 ≠ eval (fun _ => Part.some 1) .query 7 := by
  simp [eval]

/-- Two actual macro substitutions compose without assuming a universal interface. -/
theorem two_realizations (oracle : Nat →. Nat) (r q c : Code) :
    eval oracle (substitute r (substitute q c)) =
      eval (eval (eval oracle r) q) c := by
  rw [eval_substitute, eval_substitute]

/-- The relative obstruction also has an ordinary, computable-oracle instance. -/
theorem computable_oracle_jump :
    ¬ Nat.RecursiveIn {plusTwo.eval} (fun n => Part.some (jump plusTwo.eval n)) :=
  jump_not_recursiveIn _

end Examples.OracleComputation
