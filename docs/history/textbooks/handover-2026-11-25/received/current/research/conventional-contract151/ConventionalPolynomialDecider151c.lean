import Applications.Resources.TuringSimulation.PolynomialDeciderPrintMove
import NaturalPolynomialNormalForm149

set_option autoImplicit false
set_option warningAsError true

/-!
# Finite-input conventional polynomial deciders

UNCOMPILED research draft150. The input alphabet, finite machine, literal
per-letter initialization and exponent precede every input word. Transitions
are the existing actual combined write-and-move operations. None is permitted
exactly at the two terminal controls. The native constructor below supplies
the run field from the existing actual simulation theorem.

This smaller contract intentionally forgets the native simulation witness and
the particular final tape. Concrete refinement theorems retain those data;
there is no inverse reconstruction or executable numeric-table claim.
-/

namespace Resources.TuringSimulation.ConventionalPolynomialDraft150

open Function Turing

/-- One fixed finite combined-transition machine, with a fixed power allowance
and actual execution for every literal word over its finite input alphabet. -/
structure PolynomialDecider (Input : Type) (f : List Input → Bool) where
  inputFintype : Fintype Input
  Alphabet : Type
  Control : Type
  alphabetFintype : Fintype Alphabet
  controlFintype : Fintype Control
  blank : Alphabet
  start : Control
  accept : Control
  reject : Control
  start_ne_accept : start ≠ accept
  start_ne_reject : start ≠ reject
  accept_ne_reject : accept ≠ reject
  letter : Input ↪ Alphabet
  letter_ne_blank : ∀ a, letter a ≠ blank
  machine : PrintMove.Machine Alphabet Control
  machine_eq_none_iff : ∀ (q : Control) (a : Alphabet),
    machine q a = none ↔ q = accept ∨ q = reject
  exponent : Nat
  run :
    letI : Inhabited Alphabet := ⟨blank⟩
    ∀ raw : List Input, ∃ finish : PrintMove.Cfg Alphabet Control,
      Nonempty (StateTransition.EvalsToInTime (PrintMove.step machine)
        (PrintMove.init start (raw.map letter)) (some finish)
        (raw.length ^ exponent + exponent)) ∧
      finish.q = if f raw then accept else reject

private theorem iterate_bind_none {σ : Type*} (f : σ → Option σ) (n : Nat) :
    (flip Bind.bind f)^[n] (none : Option σ) = none := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      rfl

/-- Connect the count-carrying finite witness to Mathlib's actual reachability
relation; no terminal correctness assumption is hidden in this conversion. -/
theorem reaches_of_finite_run {σ : Type*} {f : σ → Option σ} {a b : σ}
    (run : StateTransition.EvalsTo f a (some b)) : StateTransition.Reaches f a b := by
  have finite : ∀ (n : Nat) (start : σ),
      (flip Bind.bind f)^[n] (some start) = some b → StateTransition.Reaches f start b := by
    intro n
    induction n with
    | zero =>
        intro start reached
        have same : start = b := Option.some.inj reached
        subst start
        exact Relation.ReflTransGen.refl
    | succ n ih =>
        intro start reached
        rw [Function.iterate_succ_apply] at reached
        change (flip Bind.bind f)^[n] (f start) = some b at reached
        cases selected : f start with
        | none =>
            rw [selected, iterate_bind_none] at reached
            cases reached
        | some next =>
            rw [selected] at reached
            exact Relation.ReflTransGen.head selected (ih next reached)
  exact finite run.steps a run.evals_in_steps

namespace PolynomialDecider

variable {Input : Type} {f : List Input → Bool} (d : PolynomialDecider Input f)

/-- Every active control has a real action on every work symbol. -/
theorem transition_some_of_nonterminal (q : d.Control) (a : d.Alphabet)
    (notAccept : q ≠ d.accept) (notReject : q ≠ d.reject) :
    ∃ action, d.machine q a = some action := by
  cases selected : d.machine q a with
  | none =>
      rcases (d.machine_eq_none_iff q a).1 selected with accepted | rejected
      · exact False.elim (notAccept accepted)
      · exact False.elim (notReject rejected)
  | some action => exact ⟨action, rfl⟩

theorem literal_input_length (raw : List Input) :
    (raw.map d.letter).length = raw.length := by simp only [List.length_map]

/-- Stopping is an actual machine fact, derived from the exact terminal domain. -/
theorem step_eq_none_iff :
    letI : Inhabited d.Alphabet := ⟨d.blank⟩
    ∀ c : PrintMove.Cfg d.Alphabet d.Control,
      PrintMove.step d.machine c = none ↔ c.q = d.accept ∨ c.q = d.reject := by
  let : Inhabited d.Alphabet := ⟨d.blank⟩
  intro c
  simpa only [PrintMove.step, Option.map_eq_none_iff] using
    d.machine_eq_none_iff c.q c.Tape.head

/-- The same concrete bounded run has the claimed answer and is stopped. -/
theorem run_and_stopped :
    letI : Inhabited d.Alphabet := ⟨d.blank⟩
    ∀ raw : List Input, ∃ finish : PrintMove.Cfg d.Alphabet d.Control,
      Nonempty (StateTransition.EvalsToInTime (PrintMove.step d.machine)
        (PrintMove.init d.start (raw.map d.letter)) (some finish)
        (raw.length ^ d.exponent + d.exponent)) ∧
      PrintMove.step d.machine finish = none ∧
      finish.q = if f raw then d.accept else d.reject := by
  let : Inhabited d.Alphabet := ⟨d.blank⟩
  intro raw
  obtain ⟨finish, run, answer⟩ := d.run raw
  refine ⟨finish, run, (d.step_eq_none_iff finish).2 ?_, answer⟩
  cases selected : f raw with
  | false => exact Or.inr (by simpa [selected] using answer)
  | true => exact Or.inl (by simpa [selected] using answer)

/-- Acceptance is membership in actual terminal evaluation, rather than a
renamed Boolean specification or a caller-supplied complexity predicate. -/
def Accepts (raw : List Input) : Prop :=
  letI : Inhabited d.Alphabet := ⟨d.blank⟩
  ∃ finish : PrintMove.Cfg d.Alphabet d.Control,
    finish ∈ StateTransition.eval (PrintMove.step d.machine)
      (PrintMove.init d.start (raw.map d.letter)) ∧ finish.q = d.accept

/-- Deterministic terminal uniqueness connects the actual language to the
specified Boolean function. The forward implication excludes spurious runs. -/
theorem accepts_iff (raw : List Input) : d.Accepts raw ↔ f raw = true := by
  let : Inhabited d.Alphabet := ⟨d.blank⟩
  obtain ⟨finish, ⟨run⟩, stopped, answer⟩ := d.run_and_stopped raw
  have evaluated : finish ∈ StateTransition.eval (PrintMove.step d.machine)
      (PrintMove.init d.start (raw.map d.letter)) :=
    StateTransition.mem_eval.2 ⟨reaches_of_finite_run run.toEvalsTo, stopped⟩
  constructor
  · rintro ⟨other, evaluatedOther, accepted⟩
    have same : other = finish := Part.mem_unique evaluatedOther evaluated
    subst other
    cases selected : f raw with
    | false =>
        have rejected : finish.q = d.reject := by
          simpa [selected] using answer
        exact False.elim (d.accept_ne_reject (accepted.symm.trans rejected))
    | true => rfl
  · intro positive
    exact ⟨finish, evaluated, by simpa [positive] using answer⟩

/-- The zero-size input is handled with the same fixed exponent. -/
theorem empty_run :
    letI : Inhabited d.Alphabet := ⟨d.blank⟩
    ∃ finish : PrintMove.Cfg d.Alphabet d.Control,
      Nonempty (StateTransition.EvalsToInTime (PrintMove.step d.machine)
        (PrintMove.init d.start []) (some finish) (0 ^ d.exponent + d.exponent)) ∧
      PrintMove.step d.machine finish = none ∧
      finish.q = if f [] then d.accept else d.reject :=
  d.run_and_stopped []

end PolynomialDecider

/-- Reuse the existing Boolean-input API. The exponent is fixed from its
checked `2*p+1` polynomial; only the actual target allowance is widened. -/
noncomputable def ofNative {f : List Bool → Bool}
    (d : PolynomialBooleanDecider f) [DecidableEq d.Alphabet] : PolynomialDecider Bool f where
  inputFintype := inferInstance
  Alphabet := d.Alphabet
  Control := PrintMove.Control d.Control
  alphabetFintype := d.alphabetFintype
  controlFintype := d.printMoveControlFintype
  blank := d.blank
  start := .normal d.start
  accept := .accept
  reject := .reject
  start_ne_accept := PrintMove.normal_ne_accept d.start
  start_ne_reject := PrintMove.normal_ne_reject d.start
  accept_ne_reject := PrintMove.accept_ne_reject
  letter := d.bit
  letter_ne_blank := d.bit_ne_blank
  machine := d.printMoveMachine
  machine_eq_none_iff := by
    let : Inhabited d.Control := ⟨d.start⟩
    exact PrintMove.adapter_eq_none_iff d.machine (d.bit true)
  exponent := Resources.PolynomialTime.NormalFormDraft148.exponent d.printMoveTime
  run := by
    let : Inhabited d.Alphabet := ⟨d.blank⟩
    let : Inhabited d.Control := ⟨d.start⟩
    intro raw
    obtain ⟨finish, _source, _stopped, _output, target, _exact, _relative, _halted⟩ :=
      d.printMove_run raw
    let widened : StateTransition.EvalsToInTime (PrintMove.step d.printMoveMachine)
        (PrintMove.init (.normal d.start) (raw.map d.bit))
        (some (PrintMove.decidedCfg (f raw) finish.Tape))
        (raw.length ^ Resources.PolynomialTime.NormalFormDraft148.exponent d.printMoveTime +
          Resources.PolynomialTime.NormalFormDraft148.exponent d.printMoveTime) :=
      { toEvalsTo := target.toEvalsTo
        steps_le_m := target.steps_le_m.trans
          (Resources.PolynomialTime.NormalFormDraft148.eval_le_power_add_exponent
            d.printMoveTime raw.length) }
    refine ⟨PrintMove.decidedCfg (f raw) finish.Tape, ⟨widened⟩, ?_⟩
    cases f raw <;> rfl

/-- The generic API consumes the existing native construction without replacing
its machine or input representation. -/
theorem ofNative_accepts_iff {f : List Bool → Bool}
    (d : PolynomialBooleanDecider f) [DecidableEq d.Alphabet] (raw : List Bool) :
    (ofNative d).Accepts raw ↔ f raw = true :=
  (ofNative d).accepts_iff raw

end Resources.TuringSimulation.ConventionalPolynomialDraft150
