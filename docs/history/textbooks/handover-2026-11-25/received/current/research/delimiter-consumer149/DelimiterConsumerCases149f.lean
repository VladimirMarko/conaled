import DelimiterPreludeExamples144c
import DelimiterNativeConsumer148

set_option autoImplicit false
set_option warningAsError true

/-!
# Preexisting delimiter fixtures consuming the new bridge

UNCOMPILED implementation examples. Each first conjunct is the unchanged fixed
prelude clock and complete old initializer. Each second conjunct consumes the
new actual ordinary execution theorem and retains its whole output tape.
No sharp peak or exact primitive count is inferred from a source clock.
-/

namespace Examples.DelimiterConsumer148

open Turing
open Resources.TuringSimulation
open Resources.RotationCertificate
open Resources.RotationCertificate.DelimiterPreludeDraft
open Resources.RotationCertificate.DelimiterPreludeDraft.NativeConsumer148

/-- Transport only the small literal-list and length equalities. The execution
proposition stays an opaque parameter of this proof. -/
private theorem transport_literal_case (P : Raw → ℕ → Prop)
    (raw shown : Raw) (n : ℕ) (hraw : raw = shown) (hlen : raw.length = n)
    (run : P raw raw.length) : P shown n := by
  cases hraw
  cases hlen
  exact run

theorem empty_missing_bridge :
    next^[2] (some (initList (machine false) [])) =
        some (initList (oldMachine false) []) ∧
      Nonempty (StateTransition.EvalsToInTime (TM0.step (ordinaryMachine false))
        (TM0.init (ordinaryInput false [])) (some (ordinaryOutput false false))
        (MarkedInput.preludeSteps ([] : Raw) +
          encodedPrimitiveTimeBound (actionMaximum (R := Bool)) 0 + 1)) := by
  constructor
  · exact Examples.DelimiterPreludeResearch.empty_missing_handoff
  · have run := ordinary_malformed (R := Bool) false ([] : Raw) rfl
    simpa only [List.length_nil] using run

theorem delimiter_only_bridge :
    next^[4] (some (initList (machine false) [none])) =
        some (initList (oldMachine false) [true]) ∧
      Nonempty (StateTransition.EvalsToInTime (TM0.step (ordinaryMachine false))
        (TM0.init (ordinaryInput false [none]))
        (some (ordinaryOutput false ((verifyBitsRun [] []).1)))
        (MarkedInput.preludeSteps ([none] : Raw) +
          encodedPrimitiveTimeBound (actionMaximum (R := Bool)) 1 + 1)) := by
  constructor
  · exact Examples.DelimiterPreludeResearch.delimiter_only_handoff
  · have run := ordinary_literal_pair (R := Bool) false [] []
    exact transport_literal_case
      (fun raw n => Nonempty (StateTransition.EvalsToInTime
        (TM0.step (ordinaryMachine false))
        (TM0.init (ordinaryInput false raw))
        (some (ordinaryOutput false ((verifyBitsRun [] []).1)))
        (MarkedInput.preludeSteps raw +
          encodedPrimitiveTimeBound (actionMaximum (R := Bool)) n + 1)))
      (literalPair [] []) [none] 1 rfl rfl run

theorem missing_false_bridge :
    next^[5] (some (initList (machine false) [some false])) =
        some (initList (oldMachine false) []) ∧
      Nonempty (StateTransition.EvalsToInTime (TM0.step (ordinaryMachine false))
        (TM0.init (ordinaryInput false [some false])) (some (ordinaryOutput false false))
        (MarkedInput.preludeSteps ([some false] : Raw) +
          encodedPrimitiveTimeBound (actionMaximum (R := Bool)) 1 + 1)) := by
  constructor
  · exact Examples.DelimiterPreludeResearch.missing_false_handoff
  · have run := ordinary_malformed (R := Bool) false ([some false] : Raw) rfl
    exact transport_literal_case
      (fun raw n => Nonempty (StateTransition.EvalsToInTime
        (TM0.step (ordinaryMachine false))
        (TM0.init (ordinaryInput false raw))
        (some (ordinaryOutput false false))
        (MarkedInput.preludeSteps raw +
          encodedPrimitiveTimeBound (actionMaximum (R := Bool)) n + 1)))
      [some false] [some false] 1 rfl rfl run

theorem mixed_valid_true_bridge :
    next^[14]
        (some (initList (machine true) [some true, some false, none, some false, some true])) =
        some (initList (oldMachine true) [false, true, false, false, true, false, true]) ∧
      Nonempty (StateTransition.EvalsToInTime (TM0.step (ordinaryMachine true))
        (TM0.init (ordinaryInput true [some true, some false, none, some false, some true]))
        (some (ordinaryOutput true ((verifyBitsRun [true, false] [false, true]).1)))
        (MarkedInput.preludeSteps ([some true, some false, none, some false, some true] : Raw) +
          encodedPrimitiveTimeBound (actionMaximum (R := Bool)) 5 + 1)) := by
  constructor
  · exact Examples.DelimiterPreludeResearch.mixed_valid_initial_true_handoff
  · have run := ordinary_literal_pair (R := Bool) true [true, false] [false, true]
    exact transport_literal_case
      (fun raw n => Nonempty (StateTransition.EvalsToInTime
        (TM0.step (ordinaryMachine true))
        (TM0.init (ordinaryInput true raw))
        (some (ordinaryOutput true ((verifyBitsRun [true, false] [false, true]).1)))
        (MarkedInput.preludeSteps raw +
          encodedPrimitiveTimeBound (actionMaximum (R := Bool)) n + 1)))
      (literalPair [true, false] [false, true]) [some true, some false, none, some false, some true] 5 rfl rfl run

theorem repeated_mixed_true_bridge :
    next^[11] (some (initList (machine true) [some true, none, some false, none, some true])) =
        some (initList (oldMachine true) []) ∧
      Nonempty (StateTransition.EvalsToInTime (TM0.step (ordinaryMachine true))
        (TM0.init (ordinaryInput true [some true, none, some false, none, some true]))
        (some (ordinaryOutput true false))
        (MarkedInput.preludeSteps ([some true, none, some false, none, some true] : Raw) +
          encodedPrimitiveTimeBound (actionMaximum (R := Bool)) 5 + 1)) := by
  constructor
  · exact Examples.DelimiterPreludeResearch.repeated_mixed_initial_true_handoff
  · have run := ordinary_malformed (R := Bool) true ([some true, none, some false, none, some true] : Raw) rfl
    exact transport_literal_case
      (fun raw n => Nonempty (StateTransition.EvalsToInTime
        (TM0.step (ordinaryMachine true))
        (TM0.init (ordinaryInput true raw))
        (some (ordinaryOutput true false))
        (MarkedInput.preludeSteps raw +
          encodedPrimitiveTimeBound (actionMaximum (R := Bool)) n + 1)))
      [some true, none, some false, none, some true] [some true, none, some false, none, some true] 5 rfl rfl run

theorem repeated_tail_delimiter_bridge :
    next^[9] (some (initList (machine false) [none, some true, none, none, some false])) =
        some (initList (oldMachine false) []) ∧
      Nonempty (StateTransition.EvalsToInTime (TM0.step (ordinaryMachine false))
        (TM0.init (ordinaryInput false [none, some true, none, none, some false]))
        (some (ordinaryOutput false false))
        (MarkedInput.preludeSteps ([none, some true, none, none, some false] : Raw) +
          encodedPrimitiveTimeBound (actionMaximum (R := Bool)) 5 + 1)) := by
  constructor
  · exact Examples.DelimiterPreludeResearch.repeated_tail_has_delimiter_handoff
  · have run := ordinary_malformed (R := Bool) false ([none, some true, none, none, some false] : Raw) rfl
    exact transport_literal_case
      (fun raw n => Nonempty (StateTransition.EvalsToInTime
        (TM0.step (ordinaryMachine false))
        (TM0.init (ordinaryInput false raw))
        (some (ordinaryOutput false false))
        (MarkedInput.preludeSteps raw +
          encodedPrimitiveTimeBound (actionMaximum (R := Bool)) n + 1)))
      [none, some true, none, none, some false] [none, some true, none, none, some false] 5 rfl rfl run

theorem delimiter_false_and_blank_distinct :
    inputLetter true none ≠ inputLetter true (some false) ∧
      inputLetter true none ≠ (default : Alphabet true) ∧
      inputLetter true (some false) ≠ (default : Alphabet true) :=
  ⟨delimiter_ne_false true, input_ne_blank true none, input_ne_blank true (some false)⟩

end Examples.DelimiterConsumer148
