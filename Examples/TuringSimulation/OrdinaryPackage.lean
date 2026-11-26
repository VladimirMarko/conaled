import Applications.Resources.TuringSimulation.OrdinaryPackage
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Prod

set_option autoImplicit false
set_option warningAsError true

namespace Examples.TuringSimulation.OrdinaryPackageCases

open Function Turing
open Resources.TuringSimulation
open Resources.TuringSimulation.StackToTape

def FixtureAlphabet : Bool → Type
  | false => Option Bool
  | true => Bool

instance fixtureAlphabetFintype (k : Bool) : Fintype (FixtureAlphabet k) := by
  cases k with
  | false => exact (inferInstance : Fintype (Option Bool))
  | true => exact (inferInstance : Fintype Bool)

def fixture : FinTM2 where
  K := Bool
  k₀ := false
  k₁ := true
  Γ := FixtureAlphabet
  Λ := Bool
  main := true
  σ := Bool
  initialState := true
  m _ := .halt

def outputLetter : Bool → Option Bool := some

def cell (a : Option Bool) : OrdinaryPackage.Alphabet fixture :=
  MarkedInput.symbol (Γ := fixture.Γ) fixture.k₀ a

def nativeInput (raw : List (Option Bool)) : List (OrdinaryPackage.Alphabet fixture) :=
  raw.map cell

def fixtureMachine : @TM0.Machine (OrdinaryPackage.Alphabet fixture) (OrdinaryPackage.Control fixture)
    (OrdinaryPackage.controlInhabited fixture) :=
  OrdinaryPackage.machine fixture outputLetter true

theorem stores_are_distinct : fixture.k₀ ≠ fixture.k₁ := by
  intro impossible
  cases impossible

theorem alphabet_is_finite : Nonempty (Fintype (OrdinaryPackage.Alphabet fixture)) := by
  let : ∀ k : fixture.K, Fintype (fixture.Γ k) := fixtureAlphabetFintype
  exact ⟨OrdinaryPackage.alphabetFintype fixture⟩

theorem working_alphabet_has_twenty_four_symbols :
    letI : ∀ k : fixture.K, Fintype (fixture.Γ k) := fixtureAlphabetFintype
    letI : Fintype (OrdinaryPackage.Alphabet fixture) := OrdinaryPackage.alphabetFintype fixture
    Fintype.card (OrdinaryPackage.Alphabet fixture) = 24 := by
  let : ∀ k : Bool, Fintype (FixtureAlphabet k) := fixtureAlphabetFintype
  change Fintype.card (Bool × ((k : Bool) → Option (FixtureAlphabet k))) = 24
  rw [Fintype.card_prod, Fintype.card_pi,
    Fintype.prod_bool (fun k : Bool => Fintype.card (Option (FixtureAlphabet k)))]
  change Fintype.card Bool * (Fintype.card (Option Bool) *
    Fintype.card (Option (Option Bool))) = 24
  simp only [Fintype.card_option, Fintype.card_bool]

theorem wrapper_control_is_finite : Nonempty (Fintype (OrdinaryPackage.Control fixture)) :=
  ⟨OrdinaryPackage.controlFintype fixture⟩

theorem supplied_main_is_true : fixture.main = true := rfl

theorem supplied_register_is_true : (OrdinaryPackage.sourceDefault fixture).val.2 = true := rfl

theorem supplied_source_control :
    (OrdinaryPackage.sourceDefault fixture).val =
      (some ((TM2to1.tr fixture.m) (.normal true)), true) := rfl

theorem wrapper_starts_at_prelude :
    (OrdinaryPackage.controlInhabited fixture).default =
      (MarkedInput.Control.start : OrdinaryPackage.Control fixture) := rfl

theorem designated_input_preserves_length (raw : List (Option Bool)) :
    (nativeInput raw).length = raw.length := by
  simp only [nativeInput, List.length_map]

theorem delimiter_cell_is_present : (cell none).2 fixture.k₀ = some none :=
  MarkedInput.symbol_selected (Γ := fixture.Γ) fixture.k₀ none

theorem false_cell_is_present : (cell (some false)).2 fixture.k₀ = some (some false) :=
  MarkedInput.symbol_selected (Γ := fixture.Γ) fixture.k₀ (some false)

theorem true_cell_is_present : (cell (some true)).2 fixture.k₀ = some (some true) :=
  MarkedInput.symbol_selected (Γ := fixture.Γ) fixture.k₀ (some true)

theorem delimiter_cell_ne_blank : cell none ≠ (default : OrdinaryPackage.Alphabet fixture) :=
  MarkedInput.symbol_ne_blank (Γ := fixture.Γ) fixture.k₀ none

theorem false_cell_ne_blank : cell (some false) ≠ (default : OrdinaryPackage.Alphabet fixture) :=
  MarkedInput.symbol_ne_blank (Γ := fixture.Γ) fixture.k₀ (some false)

theorem delimiter_cell_ne_false : cell none ≠ cell (some false) := by
  intro same
  have impossible : (none : Option Bool) = some false :=
    MarkedInput.symbol_injective (Γ := fixture.Γ) fixture.k₀ same
  cases impossible

theorem empty_input_ne_delimiter : nativeInput [] ≠ nativeInput [none] := by
  intro impossible
  cases impossible

theorem empty_prelude_one_step :
    (flip Bind.bind (TM0.step fixtureMachine))^[1] (some (TM0.init (nativeInput []))) =
      some ⟨.run (OrdinaryPackage.sourceDefault fixture),
        Tape.mk (true, fun _ => none) ∅ ∅⟩ :=
  OrdinaryPackage.prelude_exact fixture outputLetter true []

private theorem singleton_prelude_three_steps (a : Option Bool) :
    (flip Bind.bind (TM0.step fixtureMachine))^[3] (some (TM0.init (nativeInput [a]))) =
      some ⟨.run (OrdinaryPackage.sourceDefault fixture), Tape.mk (true, (cell a).2) ∅ ∅⟩ := by
  have boundary : TapeReflection.tape
      (Tape.mk₁ (TM2to1.trInit (Γ := fixture.Γ) fixture.k₀ [a])) =
        Tape.mk (true, (cell a).2) ∅ ∅ := rfl
  exact (OrdinaryPackage.prelude_exact fixture outputLetter true [a]).trans
    (congrArg
      (fun T : Tape (OrdinaryPackage.Alphabet fixture) =>
        (some ⟨.run (OrdinaryPackage.sourceDefault fixture), T⟩ :
          Option (TM0.Cfg (OrdinaryPackage.Alphabet fixture) (OrdinaryPackage.Control fixture))))
      boundary)

theorem delimiter_prelude_three_steps :
    (flip Bind.bind (TM0.step fixtureMachine))^[3] (some (TM0.init (nativeInput [none]))) =
      some ⟨.run (OrdinaryPackage.sourceDefault fixture), Tape.mk (true, (cell none).2) ∅ ∅⟩ :=
  singleton_prelude_three_steps none

theorem present_false_prelude_three_steps :
    (flip Bind.bind (TM0.step fixtureMachine))^[3] (some (TM0.init (nativeInput [some false]))) =
      some ⟨.run (OrdinaryPackage.sourceDefault fixture),
        Tape.mk (true, (cell (some false)).2) ∅ ∅⟩ :=
  singleton_prelude_three_steps (some false)

theorem present_true_prelude_three_steps :
    (flip Bind.bind (TM0.step fixtureMachine))^[3] (some (TM0.init (nativeInput [some true]))) =
      some ⟨.run (OrdinaryPackage.sourceDefault fixture),
        Tape.mk (true, (cell (some true)).2) ∅ ∅⟩ :=
  singleton_prelude_three_steps (some true)

/-- The left list is nearest first. The final input letter is marked, and
the two preceding letters remain in their actual reversed physical order. -/
theorem orientation_prelude_five_steps :
    (flip Bind.bind (TM0.step fixtureMachine))^[5]
      (some (TM0.init (nativeInput [some false, none, some true]))) =
      some ⟨.run (OrdinaryPackage.sourceDefault fixture),
        Tape.mk (true, (cell (some true)).2)
          (ListBlank.mk [cell none, cell (some false)]) ∅⟩ := by
  have boundary : TapeReflection.tape
      (Tape.mk₁ (TM2to1.trInit (Γ := fixture.Γ) fixture.k₀ [some false, none, some true])) =
        Tape.mk (true, (cell (some true)).2)
          (ListBlank.mk [cell none, cell (some false)]) ∅ := rfl
  exact (OrdinaryPackage.prelude_exact fixture outputLetter true
    [some false, none, some true]).trans
      (congrArg
        (fun T : Tape (OrdinaryPackage.Alphabet fixture) =>
          (some ⟨.run (OrdinaryPackage.sourceDefault fixture), T⟩ :
            Option (TM0.Cfg (OrdinaryPackage.Alphabet fixture) (OrdinaryPackage.Control fixture))))
        boundary)

theorem false_halt_has_empty_input_track :
    SingletonOutput.haltRow fixture false fixture.k₀ = none :=
  OrdinaryPackage.haltRow_input fixture false stores_are_distinct

theorem false_halt_has_present_output_track :
    SingletonOutput.haltRow fixture false fixture.k₁ = some false :=
  OrdinaryPackage.haltRow_output fixture false

theorem false_output_ignores_true_fallback :
    OrdinaryPackage.emitter fixture outputLetter true
        (true, SingletonOutput.haltRow fixture false) = cell (some false) :=
  OrdinaryPackage.emitter_halt_row fixture outputLetter true false

theorem true_output_ignores_false_fallback :
    OrdinaryPackage.emitter fixture outputLetter false
        (true, SingletonOutput.haltRow fixture true) = cell (some true) :=
  OrdinaryPackage.emitter_halt_row fixture outputLetter false true

/-- This is a function-totality case, not a claim that blank is a valid
singleton source output. -/
theorem blank_cell_uses_total_fallback :
    OrdinaryPackage.emitter fixture outputLetter true
        (default : OrdinaryPackage.Alphabet fixture) = cell (some true) := rfl

noncomputable def haltedControl : Package.Control fixture :=
  ⟨(none, true), SingletonOutput.package_halt_supported fixture true⟩

private theorem native_output_one_step (fallback answer : Bool) :
    TM0.step (OrdinaryPackage.machine fixture outputLetter fallback)
      ⟨.run haltedControl, Tape.mk₁ [(true, SingletonOutput.haltRow fixture answer)]⟩ =
      some ⟨.done, Tape.mk₁ [cell (some answer)]⟩ := by
  let : Inhabited (Package.Control fixture) := Package.controlInhabited fixture
  have actual := MarkedInput.emit_singleton_step (Γ := fixture.Γ) fixture.k₀
    (Package.closedMachine fixture) (OrdinaryPackage.emitter fixture outputLetter fallback)
    haltedControl (true, SingletonOutput.haltRow fixture answer) (by rfl)
  exact actual.trans
    (congrArg
      (fun a : OrdinaryPackage.Alphabet fixture =>
        (some ⟨MarkedInput.Control.done, Tape.mk₁ [a]⟩ :
          Option (TM0.Cfg (OrdinaryPackage.Alphabet fixture) (OrdinaryPackage.Control fixture))))
      (OrdinaryPackage.emitter_halt_row fixture outputLetter fallback answer))

theorem false_output_one_step :
    TM0.step fixtureMachine
      ⟨.run haltedControl, Tape.mk₁ [(true, SingletonOutput.haltRow fixture false)]⟩ =
      some ⟨.done, Tape.mk₁ [cell (some false)]⟩ :=
  native_output_one_step true false

theorem true_output_one_step :
    TM0.step (OrdinaryPackage.machine fixture outputLetter false)
      ⟨.run haltedControl, Tape.mk₁ [(true, SingletonOutput.haltRow fixture true)]⟩ =
      some ⟨.done, Tape.mk₁ [cell (some true)]⟩ :=
  native_output_one_step false true

theorem false_output_next_step_is_none :
    TM0.step fixtureMachine ⟨.done, Tape.mk₁ [cell (some false)]⟩ = none := rfl

theorem false_output_outer_none_at_two :
    (flip Bind.bind (TM0.step fixtureMachine))^[2]
      (some ⟨.run haltedControl, Tape.mk₁ [(true, SingletonOutput.haltRow fixture false)]⟩) =
      none := by
  change Bind.bind
    (TM0.step fixtureMachine ⟨.run haltedControl, Tape.mk₁ [(true, SingletonOutput.haltRow fixture false)]⟩)
    (TM0.step fixtureMachine) = none
  rw [false_output_one_step]
  rfl

/-- These literals test the count formula on a retained count of 7, rather
than replacing that count by its allowance 10. They do not assert a fixture
source run from input to output. -/
theorem stored_count_literals :
    1 + (7 + MarkedInput.preludeSteps ([] : List (Option Bool))) = 9 ∧
      1 + (7 + MarkedInput.preludeSteps [some false]) = 11 ∧
      1 + (7 + MarkedInput.preludeSteps [some false, none, some true]) = 13 :=
  ⟨rfl, rfl, rfl⟩

theorem bound_literals :
    MarkedInput.preludeSteps ([] : List (Option Bool)) + 10 + 1 = 12 ∧
      MarkedInput.preludeSteps [some false] + 10 + 1 = 14 ∧
      MarkedInput.preludeSteps [some false, none, some true] + 10 + 1 = 16 :=
  ⟨rfl, rfl, rfl⟩

theorem distinct_outer_none_literals :
    1 + 9 = 10 ∧ 1 + 11 = 12 ∧ 1 + 13 = 14 ∧
      MarkedInput.preludeSteps ([] : List (Option Bool)) + 10 + 2 = 13 ∧
      MarkedInput.preludeSteps [some false] + 10 + 2 = 15 ∧
      MarkedInput.preludeSteps [some false, none, some true] + 10 + 2 = 17 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end Examples.TuringSimulation.OrdinaryPackageCases
