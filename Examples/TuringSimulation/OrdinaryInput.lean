import Applications.Resources.TuringSimulation.MarkedInput
import Applications.Resources.TuringSimulation.PolynomialDecider

set_option autoImplicit false
set_option warningAsError true

namespace Examples.TuringSimulation.OrdinaryInput

open Function Turing
open Resources.TuringSimulation

abbrev Letters := TM2to1.Γ' Bool (fun _ => Bool)

def haltSource : @TM0.Machine Letters Bool ⟨true⟩ := fun _ _ => none

def emit (a : Letters) : Letters := MarkedInput.symbol false ((a.2 true).getD false)

def marked (b : Bool) : Letters := (true, (MarkedInput.symbol false b).2)

theorem empty_prelude_is_one_actual_write :
    letI : Inhabited Bool := ⟨true⟩
    (flip Bind.bind (TM0.step (MarkedInput.machine false haltSource emit)))^[1]
      (some (TM0.init (MarkedInput.input false ([] : List Bool)))) =
      some ⟨.run true, Tape.mk (true, fun _ => none) ∅ ∅⟩ := by
  let : Inhabited Bool := ⟨true⟩
  exact MarkedInput.prelude_exact false haltSource emit []

theorem false_prelude_costs_three_and_keeps_present_false :
    letI : Inhabited Bool := ⟨true⟩
    (flip Bind.bind (TM0.step (MarkedInput.machine false haltSource emit)))^[3]
      (some (TM0.init (MarkedInput.input false [false]))) =
      some ⟨.run true, Tape.mk (marked false) ∅ ∅⟩ := by
  let : Inhabited Bool := ⟨true⟩
  exact MarkedInput.prelude_exact false haltSource emit [false]

theorem true_prelude_costs_three :
    letI : Inhabited Bool := ⟨true⟩
    (flip Bind.bind (TM0.step (MarkedInput.machine false haltSource emit)))^[3]
      (some (TM0.init (MarkedInput.input false [true]))) =
      some ⟨.run true, Tape.mk (marked true) ∅ ∅⟩ := by
  let : Inhabited Bool := ⟨true⟩
  exact MarkedInput.prelude_exact false haltSource emit [true]

theorem false_true_prelude_exposes_the_reflected_orientation :
    letI : Inhabited Bool := ⟨true⟩
    (flip Bind.bind (TM0.step (MarkedInput.machine false haltSource emit)))^[4]
      (some (TM0.init (MarkedInput.input false [false, true]))) =
      some ⟨.run true,
        Tape.mk (marked true) (ListBlank.mk [MarkedInput.symbol false false]) ∅⟩ := by
  let : Inhabited Bool := ⟨true⟩
  exact MarkedInput.prelude_exact false haltSource emit [false, true]

theorem true_false_prelude_is_a_different_complete_tape :
    letI : Inhabited Bool := ⟨true⟩
    (flip Bind.bind (TM0.step (MarkedInput.machine false haltSource emit)))^[4]
      (some (TM0.init (MarkedInput.input false [true, false]))) =
      some ⟨.run true,
        Tape.mk (marked false) (ListBlank.mk [MarkedInput.symbol false true]) ∅⟩ := by
  let : Inhabited Bool := ⟨true⟩
  exact MarkedInput.prelude_exact false haltSource emit [true, false]

theorem repeated_false_does_not_terminate_the_scan :
    letI : Inhabited Bool := ⟨true⟩
    (flip Bind.bind (TM0.step (MarkedInput.machine false haltSource emit)))^[4]
      (some (TM0.init (MarkedInput.input false [false, false]))) =
      some ⟨.run true,
        Tape.mk (marked false) (ListBlank.mk [MarkedInput.symbol false false]) ∅⟩ := by
  let : Inhabited Bool := ⟨true⟩
  exact MarkedInput.prelude_exact false haltSource emit [false, false]

theorem length_three_prelude_has_nearest_first_left_order :
    letI : Inhabited Bool := ⟨true⟩
    (flip Bind.bind (TM0.step (MarkedInput.machine false haltSource emit)))^[5]
      (some (TM0.init (MarkedInput.input false [true, false, false]))) =
      some ⟨.run true,
        Tape.mk (marked false)
          (ListBlank.mk [MarkedInput.symbol false false, MarkedInput.symbol false true]) ∅⟩ := by
  let : Inhabited Bool := ⟨true⟩
  exact MarkedInput.prelude_exact false haltSource emit [true, false, false]

theorem ordinary_false_is_not_the_blank :
    (MarkedInput.symbol false false : Letters) ≠ default :=
  MarkedInput.symbol_ne_blank (Γ := fun _ : Bool => Bool) false false

theorem empty_and_false_have_distinct_complete_native_input_tapes :
    (Tape.mk₁ (MarkedInput.input false ([] : List Bool)) : Tape Letters) ≠
      Tape.mk₁ (MarkedInput.input false [false]) := by
  intro same
  have observed := congrArg (fun T : Tape Letters => T.head.2 false) same
  change none = some false at observed
  cases observed

theorem ordinary_false_and_true_are_distinct :
    (MarkedInput.symbol false false : Letters) ≠ MarkedInput.symbol false true := by
  intro same
  have impossible := MarkedInput.symbol_injective false same
  cases impossible

theorem input_and_fuel_are_distinct : (false : Bool) ≠ true := by decide

theorem output_write_and_following_none (answer : Bool) :
    letI : Inhabited Bool := ⟨true⟩
    let a : Letters := (true, Function.update (fun _ => none) true (some answer))
    TM0.step (MarkedInput.machine false haltSource emit)
        ⟨.run true, Tape.mk₁ [a]⟩ =
      some ⟨.done, Tape.mk₁ [MarkedInput.symbol false answer]⟩ ∧
    TM0.step (MarkedInput.machine false haltSource emit)
        ⟨.done, Tape.mk₁ [MarkedInput.symbol false answer]⟩ = none := by
  let : Inhabited Bool := ⟨true⟩
  dsimp only
  constructor
  · exact MarkedInput.emit_singleton_step false haltSource emit true
      (true, Function.update (fun _ => none) true (some answer)) rfl
  · exact MarkedInput.done_step false haltSource emit _

end Examples.TuringSimulation.OrdinaryInput

namespace Examples.TuringSimulation.PolynomialDecider

open Function Turing
open Resources.TuringSimulation

/-- A fixed one-write decider; the supplied starting state is true, whereas
the ambient Boolean default is false and would already be stopped. -/
def constantMachine (answer : Bool) : @TM0.Machine (Option Bool) Bool ⟨true⟩
  | true, _ => some (false, .write (some answer))
  | false, _ => none

def constantRun (answer : Bool) (raw : List Bool) :
    letI : Inhabited Bool := ⟨true⟩
    StateTransition.EvalsTo (TM0.step (constantMachine answer))
      (TM0.init (raw.map some))
      (some ⟨false, (Tape.mk₁ (raw.map some)).write (some answer)⟩) := by
  let : Inhabited Bool := ⟨true⟩
  exact { steps := 1, evals_in_steps := rfl }

theorem constantRun_steps (answer : Bool) (raw : List Bool) :
    (constantRun answer raw).steps = 1 := rfl

noncomputable def constantDecider (answer : Bool) :
    PolynomialBooleanDecider (fun _ => answer) where
  Alphabet := Option Bool
  Control := Bool
  alphabetFintype := inferInstance
  controlFintype := inferInstance
  blank := none
  start := true
  bit := ⟨some, by intro a b h; exact Option.some.inj h⟩
  bit_ne_blank := by intro b h; cases h
  machine := constantMachine answer
  time := Polynomial.C 1
  run := by
    intro raw
    refine ⟨⟨false, (Tape.mk₁ (raw.map some)).write (some answer)⟩, ⟨?_⟩, rfl, ?_⟩
    · exact
        { toEvalsTo := constantRun answer raw
          steps_le_m := by simp only [constantRun_steps, Polynomial.eval_C, le_refl] }
    · rfl

theorem constantDecider_uses_true_start (answer : Bool) :
    (constantDecider answer).start = true := rfl

theorem empty_and_present_false_inputs_differ (answer : Bool) :
    ([] : List Bool).map (constantDecider answer).bit ≠
      [false].map (constantDecider answer).bit := by
  intro h
  cases h

theorem present_false_output_is_not_blank :
    (constantDecider false).bit false ≠ (constantDecider false).blank :=
  (constantDecider false).false_ne_blank

end Examples.TuringSimulation.PolynomialDecider
