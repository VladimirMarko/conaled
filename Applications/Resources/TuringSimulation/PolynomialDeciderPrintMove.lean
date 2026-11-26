import Applications.Resources.TuringSimulation.PolynomialDecider
import Applications.Resources.TuringSimulation.PrintMove

set_option autoImplicit false
set_option warningAsError true

/-!
# Print-and-move realization of native polynomial Boolean deciders

The construction fixes finite target control before the input, preserving the
native decider's blank, supplied start and injective nonblank Boolean letters.
Its time polynomial evaluates to `2 * d.time.eval N + 1`. The run theorem
retains actual native and target witnesses and the complete final tape; the
space theorem observes every target prefix on the literal input length.

`printMoveMachine` uses supplied decidable alphabet equality. The classical variant
provides a noncomputable finite machine from the same native contract.
-/

namespace Resources.TuringSimulation.PolynomialBooleanDecider

open Function Turing

variable {f : List Bool → Bool} (d : PolynomialBooleanDecider f)

/-- The actual finite target control, chosen before any input. -/
@[instance_reducible] def printMoveControlFintype :
    Fintype (PrintMove.Control d.Control) := by
  let : Fintype d.Control := d.controlFintype
  infer_instance

/-- The two actual input letters as a finite subset of the unchanged work
alphabet. Mapping the embedding needs no whole-word conversion or decoder. -/
def printMoveInputAlphabet : Finset d.Alphabet :=
  (Finset.univ : Finset Bool).map d.bit

theorem printMoveInputAlphabet_card : (printMoveInputAlphabet d).card = 2 := by
  simp only [printMoveInputAlphabet, Finset.card_map, Finset.card_univ, Fintype.card_bool]

theorem blank_not_mem_printMoveInputAlphabet : d.blank ∉ printMoveInputAlphabet d := by
  intro h
  rcases Finset.mem_map.mp h with ⟨b, _hb, heq⟩
  exact d.bit_ne_blank b heq

/-- The new fixed polynomial pays for real combined actions and the final
decision. In particular, its constant term includes the decision transition. -/
noncomputable def printMoveTime : Polynomial ℕ := Polynomial.C 2 * d.time + Polynomial.C 1

theorem printMoveTime_eval (n : ℕ) :
    (printMoveTime d).eval n = 2 * d.time.eval n + 1 := by
  simp only [printMoveTime, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]

section SuppliedEquality

variable [DecidableEq d.Alphabet]

/-- An actual combined transition definition, using the supplied native
machine and fixed true letter. Equality is explicit; no runtime table is
exported merely from the Fintype fields of the native contract. -/
def printMoveMachine : PrintMove.Machine d.Alphabet (PrintMove.Control d.Control) := by
  let : Inhabited d.Control := ⟨d.start⟩
  exact PrintMove.adapter d.machine (d.bit true)

/-- Preserve the actual native witness and output evidence while constructing
the paid conventional run on the literal per-letter initialized input. The
target's complete tape is the native endpoint tape moved right. -/
theorem printMoveMachine_run :
    letI : Inhabited d.Alphabet := ⟨d.blank⟩
    letI : Inhabited d.Control := ⟨d.start⟩
    ∀ raw : List Bool, ∃ finish : TM0.Cfg d.Alphabet d.Control,
      ∃ source : StateTransition.EvalsToInTime (TM0.step d.machine)
          (TM0.init (raw.map d.bit)) (some finish) (d.time.eval raw.length),
        TM0.step d.machine finish = none ∧ finish.Tape.head = d.bit (f raw) ∧
        ∃ target : StateTransition.EvalsToInTime (PrintMove.step (printMoveMachine d))
            (PrintMove.init (.normal d.start) (raw.map d.bit))
            (some (PrintMove.decidedCfg (f raw) finish.Tape)) ((printMoveTime d).eval raw.length),
          target.steps = PrintMove.simulationTime d.machine
            (TM0.init (raw.map d.bit)) source.steps + 1 ∧
          target.steps ≤ 2 * source.steps + 1 ∧
          PrintMove.step (printMoveMachine d) (PrintMove.decidedCfg (f raw) finish.Tape) = none := by
  let : Inhabited d.Alphabet := ⟨d.blank⟩
  let : Inhabited d.Control := ⟨d.start⟩
  intro raw
  obtain ⟨finish, ⟨source⟩, stopped, output⟩ := d.run raw
  obtain ⟨target, hcount, hbound, hhalt⟩ :=
    PrintMove.decide_of_native_run d.machine d.bit (TM0.init (raw.map d.bit)) finish
      (f raw) (d.time.eval raw.length) source stopped output
  let transported : StateTransition.EvalsToInTime (PrintMove.step (printMoveMachine d))
      (PrintMove.init (.normal d.start) (raw.map d.bit))
      (some (PrintMove.decidedCfg (f raw) finish.Tape)) ((printMoveTime d).eval raw.length) :=
    { toEvalsTo := target.toEvalsTo
      steps_le_m := by
        rw [printMoveTime_eval]
        exact target.steps_le_m }
  exact ⟨finish, source, stopped, output, transported, hcount, hbound, hhalt⟩

/-- The head positions of every actual combined prefix are counted, including
the temporary stationary-write excursions and the final decision movement. -/
theorem printMoveMachine_run_with_space :
    letI : Inhabited d.Alphabet := ⟨d.blank⟩
    letI : Inhabited d.Control := ⟨d.start⟩
    ∀ raw : List Bool, ∃ finish : TM0.Cfg d.Alphabet d.Control,
      TM0.step d.machine finish = none ∧ finish.Tape.head = d.bit (f raw) ∧
      ∃ target : StateTransition.EvalsToInTime (PrintMove.step (printMoveMachine d))
          (PrintMove.init (.normal d.start) (raw.map d.bit))
          (some (PrintMove.decidedCfg (f raw) finish.Tape)) ((printMoveTime d).eval raw.length),
        ∀ i ≤ target.steps,
          (PrintMove.Trace.visitedInterval (printMoveMachine d)
            (PrintMove.init (.normal d.start) (raw.map d.bit)) 0 raw.length i).card ≤
            max raw.length 1 + (2 * d.time.eval raw.length + 1) := by
  let : Inhabited d.Alphabet := ⟨d.blank⟩
  let : Inhabited d.Control := ⟨d.start⟩
  intro raw
  obtain ⟨finish, _source, stopped, output, target, _hcount, _hbound, _hhalt⟩ := printMoveMachine_run d raw
  refine ⟨finish, stopped, output, target, ?_⟩
  have hspace := (PrintMove.Trace.interval_le_of_run (printMoveMachine d)
    (PrintMove.init (.normal d.start) (raw.map d.bit))
    (some (PrintMove.decidedCfg (f raw) finish.Tape)) ((printMoveTime d).eval raw.length)
    target 0 (raw.map d.bit).length).2
  simpa only [List.length_map, printMoveTime_eval] using hspace

end SuppliedEquality

/-- Finite-machine existence when the native package did not carry executable
equality. This fixes classical equality before the input quantifier. It is
explicitly noncomputable and does not export an enumerated transition table. -/
noncomputable def classicalPrintMoveMachine :
    PrintMove.Machine d.Alphabet (PrintMove.Control d.Control) := by
  classical
  exact printMoveMachine d

/-- Unconditional existence consumer of the existing native decider package.
The computationally explicit supplied-equality route above remains separate. -/
theorem classicalPrintMoveMachine_run :
    letI : Inhabited d.Alphabet := ⟨d.blank⟩
    letI : Inhabited d.Control := ⟨d.start⟩
    ∀ raw : List Bool, ∃ finish : TM0.Cfg d.Alphabet d.Control,
      TM0.step d.machine finish = none ∧ finish.Tape.head = d.bit (f raw) ∧
      Nonempty (StateTransition.EvalsToInTime (PrintMove.step (classicalPrintMoveMachine d))
        (PrintMove.init (.normal d.start) (raw.map d.bit))
        (some (PrintMove.decidedCfg (f raw) finish.Tape)) ((printMoveTime d).eval raw.length)) := by
  classical
  let : Inhabited d.Alphabet := ⟨d.blank⟩
  let : Inhabited d.Control := ⟨d.start⟩
  intro raw
  obtain ⟨finish, _source, stopped, output, target, _hcount, _hbound, _hhalt⟩ := printMoveMachine_run d raw
  exact ⟨finish, stopped, output, ⟨target⟩⟩

end Resources.TuringSimulation.PolynomialBooleanDecider
