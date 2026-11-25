import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Fixed finite native polynomial Boolean deciders

The contract records finite carriers, supplied blank and start, an injective nonblank input alphabet, and actual bounded native execution. Its terminal observation pays one additional transition.
-/

set_option autoImplicit false
set_option warningAsError true


namespace Resources.TuringSimulation

open Function Turing

/-- One fixed finite native machine deciding a total Boolean function in a
fixed natural-coefficient polynomial number of primitive transitions. -/
structure PolynomialBooleanDecider (f : List Bool → Bool) where
  Alphabet : Type
  Control : Type
  alphabetFintype : Fintype Alphabet
  controlFintype : Fintype Control
  blank : Alphabet
  start : Control
  bit : Bool ↪ Alphabet
  bit_ne_blank : ∀ b, bit b ≠ blank
  machine : @TM0.Machine Alphabet Control ⟨start⟩
  time : Polynomial ℕ
  run :
    letI : Inhabited Alphabet := ⟨blank⟩
    letI : Inhabited Control := ⟨start⟩
    ∀ raw : List Bool, ∃ finish : TM0.Cfg Alphabet Control,
      Nonempty (StateTransition.EvalsToInTime (TM0.step machine)
        (TM0.init (raw.map bit)) (some finish) (time.eval raw.length)) ∧
      TM0.step machine finish = none ∧ finish.Tape.head = bit (f raw)

namespace PolynomialBooleanDecider

variable {f : List Bool → Bool} (d : PolynomialBooleanDecider f)

/-- Both input letters are present symbols, even when the Boolean is false. -/
theorem false_ne_blank : d.bit false ≠ d.blank := d.bit_ne_blank false

theorem true_ne_false : d.bit true ≠ d.bit false := by
  intro h
  have impossible : true = false := d.bit.injective h
  cases impossible

/-- The actual bounded live run is retained while the distinct outer-none
observation is obtained by one more native transition. -/
theorem run_and_outer_none :
    letI : Inhabited d.Alphabet := ⟨d.blank⟩
    letI : Inhabited d.Control := ⟨d.start⟩
    ∀ raw : List Bool, ∃ finish : TM0.Cfg d.Alphabet d.Control,
      Nonempty (StateTransition.EvalsToInTime (TM0.step d.machine)
        (TM0.init (raw.map d.bit)) (some finish) (d.time.eval raw.length)) ∧
      TM0.step d.machine finish = none ∧ finish.Tape.head = d.bit (f raw) ∧
      Nonempty (StateTransition.EvalsToInTime (TM0.step d.machine)
        (TM0.init (raw.map d.bit)) none (d.time.eval raw.length + 1)) := by
  let : Inhabited d.Alphabet := ⟨d.blank⟩
  let : Inhabited d.Control := ⟨d.start⟩
  intro raw
  obtain ⟨finish, ⟨live⟩, stopped, answer⟩ := d.run raw
  let terminal : StateTransition.EvalsTo (TM0.step d.machine) finish none :=
    { steps := 1
      evals_in_steps := by
        change TM0.step d.machine finish = none
        exact stopped }
  refine ⟨finish, ⟨live⟩, stopped, answer, ⟨?_⟩⟩
  exact
    { toEvalsTo := StateTransition.EvalsTo.trans (TM0.step d.machine) _ _ _
        live.toEvalsTo terminal
      steps_le_m := by
        change 1 + live.steps ≤ d.time.eval raw.length + 1
        rw [Nat.add_comm 1 live.steps]
        exact Nat.add_le_add_right live.steps_le_m 1 }

end PolynomialBooleanDecider

end Resources.TuringSimulation
