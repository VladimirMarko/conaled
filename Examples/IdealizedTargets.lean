import Applications.OracleComputation.Observation
import Applications.Intervals.Observation
import Examples.OracleComputation

/-! Mathematical, symbolic, effective, and partial observations with distinct admission premises. -/

namespace Examples.IdealizedTargets

open _root_.OracleComputation

/-- The same source syntax permits different independently justified query interpretations. -/
def answerThenSucc : Code := .comp .succ .query

theorem ideal_meaning (n : Nat) :
    eval haltingOracle answerThenSucc n = Part.some (haltingAnswer n + 1) := by
  simp [answerThenSucc, eval, haltingOracle]

theorem mathematical_interpretation :
    interpret (semanticAlgebra haltingOracle) answerThenSucc =
      fun n => Part.some (haltingAnswer n + 1) := by
  rw [interpret_semantics]
  funext n
  exact ideal_meaning n

theorem finite_artifact : emit answerThenSucc = [1, 4, 6] := rfl

theorem symbolic_preservation : artifact haltingOracle [1, 4, 6] =
    some (fun n => Part.some (haltingAnswer n + 1)) := by
  rw [← finite_artifact, artifact_emit]
  congr 1
  funext n
  exact ideal_meaning n

/-- Any supplied mathematical function can interpret the query; no executor is inferred. -/
theorem arbitrary_function_interpretation (f : Nat → Nat) :
    artifact (fun n => Part.some (f n)) (emit answerThenSucc) =
      some (fun n => Part.some (f n + 1)) := by
  erw [artifact_emit]
  congr 1
  funext n
  simp [answerThenSucc, eval]

/-- The ordinary route receives an actual implementing query program. -/
def effectiveProgram : Nat.Partrec.Code := toOrdinary .succ answerThenSucc

theorem effective_preservation (n : Nat) : effectiveProgram.eval n = Part.some (n + 2) := by
  rw [effectiveProgram, toOrdinary_correct]
  simp [answerThenSucc, eval, Nat.Partrec.Code.eval]

theorem query_realization_rejected (q : Nat.Partrec.Code) : q.eval ≠ haltingOracle :=
  Examples.OracleComputation.no_ordinary_halting_realizer q

/-- Concrete realization substitution composes under its actual interpretation. -/
theorem two_substitutions (oracle : Nat →. Nat) (r q : Code) :
    eval oracle (substitute r (substitute q answerThenSucc)) =
      eval (eval (eval oracle r) q) answerThenSucc := by
  rw [eval_substitute, eval_substitute]

theorem no_bound_no_result : observe 0 .zero 0 = none := by simp [observe, Nat.Partrec.Code.evaln]

theorem zero_observed : observe 1 .zero 0 = some 0 := by simp [observe, Nat.Partrec.Code.evaln]

/-- This terminating program is unknown at bound1 because its intermediate input exceeds it. -/
theorem insufficient_bound : observe 1 effectiveProgram 0 = none := by
  simp [observe, effectiveProgram, toOrdinary, answerThenSucc, Nat.Partrec.Code.evaln]

theorem sufficient_bound : observe 2 effectiveProgram 0 = some 2 := by
  simp [observe, effectiveProgram, toOrdinary, answerThenSucc, Nat.Partrec.Code.evaln]

theorem unknown_is_not_divergence : observe 1 effectiveProgram 0 = none ∧
    (effectiveProgram.eval 0).Dom := by
  refine ⟨insufficient_bound, ?_⟩
  rw [effective_preservation]
  trivial

theorem observed_ideal_answer : haltingAnswer (Encodable.encode effectiveProgram) = 1 :=
  observe_halting sufficient_bound

theorem divergence_stays_unknown (k : Nat) :
    observe k Examples.OracleComputation.ordinaryDiverge 0 = none :=
  observe_divergent (Examples.OracleComputation.ordinaryDiverge_never 0) k

/-- Pointwise existence does not supply a computable program-producing converter. -/
theorem extraction_separator :
    (∀ n, ∃ q : Nat.Partrec.Code, ∀ m, q.eval m = Part.some (haltingAnswer n)) ∧
      ¬ ∃ select : Nat → Nat.Partrec.Code, Computable select ∧
        ∀ n, (select n).eval 0 = Part.some (haltingAnswer n) := by
  refine ⟨answer_code_exists, ?_⟩
  rintro ⟨select, hs, hc⟩
  exact no_computable_answer_selector select hs hc

open IntervalAnalysis

/-- Exact rational constants remain executable without an ideal-real oracle. -/
theorem singleton_zero_observed : observeZero (singleton 0) = some true := by
  norm_num [observeZero, IntervalAnalysis.singleton]

theorem singleton_one_observed : observeZero (singleton 1) = some false := by
  norm_num [observeZero, IntervalAnalysis.singleton]

theorem ambiguous_box : observeZero unitBox = none ∧
    Exact.ContainsReal unitBox 0 ∧ Exact.ContainsReal unitBox 1 := by
  norm_num [observeZero, unitBox, Exact.ContainsReal]

/-- Compose real-point enclosure with a justified exact observation. -/
theorem real_sum_observation {x y : ℝ}
    (hx : Exact.ContainsReal (singleton 1) x)
    (hy : Exact.ContainsReal (singleton 2) y) : x + y ≠ 0 := by
  have ho : observeZero (add (singleton 1) (singleton 2)) = some false := by
    norm_num [observeZero, add, IntervalAnalysis.singleton]
  simpa using observeZero_add hx hy ho

/-- The existing typed compiler computes the enclosure; the source value is independently five. -/
def compiledBox : Interval :=
  (IntervalAnalysis.compile Arithmetic.shared).impl ((), (singleton 1, singleton 2))

theorem compiled_box : compiledBox = singleton 5 := by
  norm_num [compiledBox, IntervalAnalysis.compile, FirstOrderRelations.compileRelation,
    Arithmetic.shared, Arithmetic.x, Arithmetic.y, FirstOrderCompiler.compile,
    FirstOrderCompiler.compileVar, FirstOrderRelations.target, Relational.compose,
    primitives, IntervalAnalysis.singleton, add, mul]
  simp only [FirstOrderRelations.target, Relational.compose]
  norm_num [primitives, IntervalAnalysis.singleton, add, mul, Function.comp_def]
  dsimp [Function.comp_def, FirstOrderRelations.object, FirstOrderRelations.encoding,
    FirstOrderCompiler.context]
  norm_num

theorem compiled_contains : Contains compiledBox 5 := by
  have h := shared_contains (singleton 1) (singleton 2) 1 2
    (singleton_contains 1) (singleton_contains 2)
  norm_num at h
  exact h

theorem compiled_real_contains : Exact.ContainsReal compiledBox (5 : ℝ) :=
  (Exact.containsReal_rat_iff).mpr compiled_contains

theorem compiled_observation : observeZero compiledBox = some false := by
  rw [compiled_box]
  norm_num [observeZero, IntervalAnalysis.singleton]

/-- The compiled enclosure and observation laws jointly justify the exact source observation. -/
theorem compiled_source_nonzero : (5 : ℝ) ≠ 0 := by
  exact (observeZero_sound compiled_real_contains compiled_observation).not.mp Bool.false_ne_true

/-- Exact point cancellation is compatible with an inconclusive enclosure observation. -/
theorem dependency_loss : (∀ x : ℚ, x + -x = 0) ∧
    add unitBox (neg unitBox) = ⟨-2, 2⟩ ∧
    observeZero (add unitBox (neg unitBox)) = none := by
  refine ⟨point_cancellation, interval_cancellation_is_wider.1, ?_⟩
  rw [interval_cancellation_is_wider.1]
  norm_num [observeZero]

theorem exact_decoder_rejected : ¬ ∃ d : Interval → Bool,
    ∀ I x, Exact.ContainsReal I x → (d I = true ↔ x = 0) := no_exact_zero_decoder

end Examples.IdealizedTargets
