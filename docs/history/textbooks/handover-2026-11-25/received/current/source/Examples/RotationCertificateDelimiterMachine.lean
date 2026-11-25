import Applications.Resources.RotationCertificate.DelimiterMachine
import Applications.Resources.RotationCertificate.DelimiterTapeMachine
import Applications.Resources.RotationCertificate.DelimiterExecution

set_option autoImplicit false
set_option warningAsError true

/-!
# Connected delimiter and execution examples

The complete source fixtures, native bridge clocks, symbol separation
and arbitrary-raw parser clients retain their literal inputs.
-/

/- Complete preserved component: delimiter_examples. -/
section

namespace Examples.RotationCertificateDelimiterMachine.Prelude

open Resources.RotationCertificate.DelimiterMachine

theorem empty_missing_handoff :
    next^[2]
      (some (Turing.initList (machine false) [])) =
      some (Turing.initList (oldMachine false) []) := by
  have transport := congrArg (fun c : Cfg Bool => next^[2] (some c))
    (machine_initList_eq false [])
  have executed : next^[2]
      (some (state .prefix false none [] [] [])) =
      some (Turing.initList (oldMachine false) []) := by
    simp only [Function.iterate_succ_apply, next_some,
      step_prefix_empty, step_drainWork_empty]
    rfl
  exact transport.trans executed

theorem delimiter_only_handoff :
    next^[4]
      (some (Turing.initList (machine false) [none])) =
      some (Turing.initList (oldMachine false) [true]) := by
  have transport := congrArg (fun c : Cfg Bool => next^[4] (some c))
    (machine_initList_eq false [none])
  have executed : next^[4]
      (some (state .prefix false none [none] [] [])) =
      some (Turing.initList (oldMachine false) [true]) := by
    simp only [Function.iterate_succ_apply, next_some,
      step_prefix_delimiter, step_certificate_empty, step_reverse_bit, step_reverse_empty]
    rfl
  exact transport.trans executed

theorem prefix_false_handoff :
    next^[7]
      (some (Turing.initList (machine false) [some false, none])) =
      some (Turing.initList (oldMachine false) [false, false, true]) := by
  have transport := congrArg (fun c : Cfg Bool => next^[7] (some c))
    (machine_initList_eq false [some false, none])
  have executed : next^[7]
      (some (state .prefix false none [some false, none] [] [])) =
      some (Turing.initList (oldMachine false) [false, false, true]) := by
    simp only [Function.iterate_succ_apply, next_some,
      step_prefix_bit, step_prefix_delimiter, step_certificate_empty, step_reverse_bit, step_reverse_empty]
    rfl
  exact transport.trans executed

theorem prefix_true_handoff :
    next^[7]
      (some (Turing.initList (machine false) [some true, none])) =
      some (Turing.initList (oldMachine false) [false, true, true]) := by
  have transport := congrArg (fun c : Cfg Bool => next^[7] (some c))
    (machine_initList_eq false [some true, none])
  have executed : next^[7]
      (some (state .prefix false none [some true, none] [] [])) =
      some (Turing.initList (oldMachine false) [false, true, true]) := by
    simp only [Function.iterate_succ_apply, next_some,
      step_prefix_bit, step_prefix_delimiter, step_certificate_empty, step_reverse_bit, step_reverse_empty]
    rfl
  exact transport.trans executed

theorem certificate_false_handoff :
    next^[6]
      (some (Turing.initList (machine false) [none, some false])) =
      some (Turing.initList (oldMachine false) [true, false]) := by
  have transport := congrArg (fun c : Cfg Bool => next^[6] (some c))
    (machine_initList_eq false [none, some false])
  have executed : next^[6]
      (some (state .prefix false none [none, some false] [] [])) =
      some (Turing.initList (oldMachine false) [true, false]) := by
    simp only [Function.iterate_succ_apply, next_some,
      step_prefix_delimiter, step_certificate_bit, step_certificate_empty, step_reverse_bit, step_reverse_empty]
    rfl
  exact transport.trans executed

theorem certificate_true_handoff :
    next^[6]
      (some (Turing.initList (machine false) [none, some true])) =
      some (Turing.initList (oldMachine false) [true, true]) := by
  have transport := congrArg (fun c : Cfg Bool => next^[6] (some c))
    (machine_initList_eq false [none, some true])
  have executed : next^[6]
      (some (state .prefix false none [none, some true] [] [])) =
      some (Turing.initList (oldMachine false) [true, true]) := by
    simp only [Function.iterate_succ_apply, next_some,
      step_prefix_delimiter, step_certificate_bit, step_certificate_empty, step_reverse_bit, step_reverse_empty]
    rfl
  exact transport.trans executed

theorem two_certificate_bits_handoff :
    next^[8]
      (some (Turing.initList (machine false) [none, some false, some true])) =
      some (Turing.initList (oldMachine false) [true, false, true]) := by
  have transport := congrArg (fun c : Cfg Bool => next^[8] (some c))
    (machine_initList_eq false [none, some false, some true])
  have executed : next^[8]
      (some (state .prefix false none [none, some false, some true] [] [])) =
      some (Turing.initList (oldMachine false) [true, false, true]) := by
    simp only [Function.iterate_succ_apply, next_some,
      step_prefix_delimiter, step_certificate_bit, step_certificate_empty, step_reverse_bit, step_reverse_empty]
    rfl
  exact transport.trans executed

theorem mixed_valid_handoff :
    next^[14]
      (some (Turing.initList (machine false) [some true, some false, none, some false, some true])) =
      some (Turing.initList (oldMachine false) [false, true, false, false, true, false, true]) := by
  have transport := congrArg (fun c : Cfg Bool => next^[14] (some c))
    (machine_initList_eq false [some true, some false, none, some false, some true])
  have executed : next^[14]
      (some (state .prefix false none [some true, some false, none, some false, some true] [] [])) =
      some (Turing.initList (oldMachine false) [false, true, false, false, true, false, true]) := by
    simp only [Function.iterate_succ_apply, next_some,
      step_prefix_bit, step_prefix_delimiter, step_certificate_bit, step_certificate_empty, step_reverse_bit, step_reverse_empty]
    rfl
  exact transport.trans executed

theorem missing_false_handoff :
    next^[5]
      (some (Turing.initList (machine false) [some false])) =
      some (Turing.initList (oldMachine false) []) := by
  have transport := congrArg (fun c : Cfg Bool => next^[5] (some c))
    (machine_initList_eq false [some false])
  have executed : next^[5]
      (some (state .prefix false none [some false] [] [])) =
      some (Turing.initList (oldMachine false) []) := by
    simp only [Function.iterate_succ_apply, next_some,
      step_prefix_bit, step_prefix_empty, step_drainWork_bit, step_drainWork_empty]
    rfl
  exact transport.trans executed

theorem missing_true_handoff :
    next^[5]
      (some (Turing.initList (machine false) [some true])) =
      some (Turing.initList (oldMachine false) []) := by
  have transport := congrArg (fun c : Cfg Bool => next^[5] (some c))
    (machine_initList_eq false [some true])
  have executed : next^[5]
      (some (state .prefix false none [some true] [] [])) =
      some (Turing.initList (oldMachine false) []) := by
    simp only [Function.iterate_succ_apply, next_some,
      step_prefix_bit, step_prefix_empty, step_drainWork_bit, step_drainWork_empty]
    rfl
  exact transport.trans executed

theorem missing_mixed_handoff :
    next^[8]
      (some (Turing.initList (machine false) [some true, some false])) =
      some (Turing.initList (oldMachine false) []) := by
  have transport := congrArg (fun c : Cfg Bool => next^[8] (some c))
    (machine_initList_eq false [some true, some false])
  have executed : next^[8]
      (some (state .prefix false none [some true, some false] [] [])) =
      some (Turing.initList (oldMachine false) []) := by
    simp only [Function.iterate_succ_apply, next_some,
      step_prefix_bit, step_prefix_empty, step_drainWork_bit, step_drainWork_empty]
    rfl
  exact transport.trans executed

theorem repeated_empty_handoff :
    next^[5]
      (some (Turing.initList (machine false) [none, none])) =
      some (Turing.initList (oldMachine false) []) := by
  have transport := congrArg (fun c : Cfg Bool => next^[5] (some c))
    (machine_initList_eq false [none, none])
  have executed : next^[5]
      (some (state .prefix false none [none, none] [] [])) =
      some (Turing.initList (oldMachine false) []) := by
    simp only [Function.iterate_succ_apply, next_some,
      step_prefix_delimiter, step_certificate_delimiter, step_drainInput_empty, step_drainWork_bit, step_drainWork_empty]
    rfl
  exact transport.trans executed

theorem repeated_tail_handoff :
    next^[6]
      (some (Turing.initList (machine false) [none, none, some false])) =
      some (Turing.initList (oldMachine false) []) := by
  have transport := congrArg (fun c : Cfg Bool => next^[6] (some c))
    (machine_initList_eq false [none, none, some false])
  have executed : next^[6]
      (some (state .prefix false none [none, none, some false] [] [])) =
      some (Turing.initList (oldMachine false) []) := by
    simp only [Function.iterate_succ_apply, next_some,
      step_prefix_delimiter, step_certificate_delimiter, step_drainInput_cons, step_drainInput_empty, step_drainWork_bit, step_drainWork_empty]
    rfl
  exact transport.trans executed

theorem repeated_mixed_handoff :
    next^[11]
      (some (Turing.initList (machine false) [some true, none, some false, none, some true])) =
      some (Turing.initList (oldMachine false) []) := by
  have transport := congrArg (fun c : Cfg Bool => next^[11] (some c))
    (machine_initList_eq false [some true, none, some false, none, some true])
  have executed : next^[11]
      (some (state .prefix false none [some true, none, some false, none, some true] [] [])) =
      some (Turing.initList (oldMachine false) []) := by
    simp only [Function.iterate_succ_apply, next_some,
      step_prefix_bit, step_prefix_delimiter, step_certificate_bit, step_certificate_delimiter, step_drainInput_cons, step_drainInput_empty, step_drainWork_bit, step_drainWork_empty]
    rfl
  exact transport.trans executed

theorem repeated_tail_has_delimiter_handoff :
    next^[9]
      (some (Turing.initList (machine false) [none, some true, none, none, some false])) =
      some (Turing.initList (oldMachine false) []) := by
  have transport := congrArg (fun c : Cfg Bool => next^[9] (some c))
    (machine_initList_eq false [none, some true, none, none, some false])
  have executed : next^[9]
      (some (state .prefix false none [none, some true, none, none, some false] [] [])) =
      some (Turing.initList (oldMachine false) []) := by
    simp only [Function.iterate_succ_apply, next_some,
      step_prefix_delimiter, step_certificate_bit, step_certificate_delimiter, step_drainInput_cons, step_drainInput_empty, step_drainWork_bit, step_drainWork_empty]
    rfl
  exact transport.trans executed

theorem mixed_valid_initial_true_handoff :
    next^[14]
      (some (Turing.initList (machine true) [some true, some false, none, some false, some true])) =
      some (Turing.initList (oldMachine true) [false, true, false, false, true, false, true]) := by
  have transport := congrArg (fun c : Cfg Bool => next^[14] (some c))
    (machine_initList_eq true [some true, some false, none, some false, some true])
  have executed : next^[14]
      (some (state .prefix true none [some true, some false, none, some false, some true] [] [])) =
      some (Turing.initList (oldMachine true) [false, true, false, false, true, false, true]) := by
    simp only [Function.iterate_succ_apply, next_some,
      step_prefix_bit, step_prefix_delimiter, step_certificate_bit, step_certificate_empty, step_reverse_bit, step_reverse_empty]
    rfl
  exact transport.trans executed

theorem repeated_mixed_initial_true_handoff :
    next^[11]
      (some (Turing.initList (machine true) [some true, none, some false, none, some true])) =
      some (Turing.initList (oldMachine true) []) := by
  have transport := congrArg (fun c : Cfg Bool => next^[11] (some c))
    (machine_initList_eq true [some true, none, some false, none, some true])
  have executed : next^[11]
      (some (state .prefix true none [some true, none, some false, none, some true] [] [])) =
      some (Turing.initList (oldMachine true) []) := by
    simp only [Function.iterate_succ_apply, next_some,
      step_prefix_bit, step_prefix_delimiter, step_certificate_bit, step_certificate_delimiter, step_drainInput_cons, step_drainInput_empty, step_drainWork_bit, step_drainWork_empty]
    rfl
  exact transport.trans executed

theorem empty_is_missing : splitLiteral [] = none := rfl

theorem delimiter_alone_is_valid : splitLiteral [none] = some ([], []) := rfl

theorem repeated_delimiter_is_invalid : splitLiteral [none, none] = none := rfl

theorem delimiter_tail_is_fully_rejected :
    splitLiteral [none, some true, none, none, some false] = none := rfl

end Examples.RotationCertificateDelimiterMachine.Prelude

end

/- Complete preserved component: bridge_examples. -/
section

namespace Examples.RotationCertificateDelimiterMachine.Native

open Turing
open Resources.TuringSimulation
open Resources.RotationCertificate
open Resources.RotationCertificate.DelimiterMachine
open Resources.RotationCertificate.DelimiterMachine.Native

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
  · exact Examples.RotationCertificateDelimiterMachine.Prelude.empty_missing_handoff
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
  · exact Examples.RotationCertificateDelimiterMachine.Prelude.delimiter_only_handoff
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
  · exact Examples.RotationCertificateDelimiterMachine.Prelude.missing_false_handoff
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
  · exact Examples.RotationCertificateDelimiterMachine.Prelude.mixed_valid_initial_true_handoff
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
  · exact Examples.RotationCertificateDelimiterMachine.Prelude.repeated_mixed_initial_true_handoff
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
  · exact Examples.RotationCertificateDelimiterMachine.Prelude.repeated_tail_has_delimiter_handoff
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

end Examples.RotationCertificateDelimiterMachine.Native

end

/- Complete preserved component: checking_examples. -/
section

namespace Examples.RotationCertificateDelimiterMachine.Checking

open Resources.BinaryCounter (Bits)
open Resources.RotationCertificate
open Resources.RotationCertificate.DelimiterMachine

/-- The existing converse applies to arbitrary raw words. -/
example (raw : Raw) (input cert : Bits) :
    splitLiteral raw = some (input, cert) ↔ raw = literalPair input cert :=
  Execution.splitLiteral_iff raw input cert

/-- This is already the exact arbitrary-raw checking-relation theorem. -/
example (raw : Raw) :
    verifyDelimited raw = true ↔
      ∃ input cert : Bits,
        raw = literalPair input cert ∧ (verifyBitsRun input cert).1 = true :=
  Execution.verifyDelimited_accept_iff raw

/-- Parser failure forces rejection without inspecting a Boolean verifier. -/
example (raw : Raw) (malformed : splitLiteral raw = none) :
    verifyDelimited raw = false := by
  simp only [verifyDelimited, malformed]

theorem empty_missing_rejects :
    splitLiteral ([] : Raw) = none ∧ verifyDelimited [] = false :=
  ⟨rfl, rfl⟩

theorem present_false_missing_rejects :
    splitLiteral [some false] = none ∧ verifyDelimited [some false] = false :=
  ⟨rfl, rfl⟩

theorem delimiter_only_parses :
    splitLiteral [none] = some ([], []) := rfl

theorem empty_input_false_certificate_parses :
    splitLiteral [none, some false] = some ([], [false]) := rfl

theorem false_input_empty_certificate_parses :
    splitLiteral [some false, none] = some ([false], []) := rfl

theorem mixed_order_parses :
    splitLiteral [some true, some false, none, some false, some true] =
      some ([true, false], [false, true]) := rfl

/-- The mixed fixture preserves the actual checker result, without guessing it. -/
theorem mixed_pair_checker :
    verifyDelimited [some true, some false, none, some false, some true] =
      (verifyBitsRun [true, false] [false, true]).1 :=
  verifyDelimited_pair [true, false] [false, true]

theorem two_delimiters_reject :
    splitLiteral [none, none] = none ∧ verifyDelimited [none, none] = false :=
  ⟨rfl, rfl⟩

theorem repeated_with_more_tail_rejects :
    splitLiteral [some false, none, some true, none, some false, none] = none ∧
      verifyDelimited [some false, none, some true, none, some false, none] = false :=
  ⟨rfl, rfl⟩

end Examples.RotationCertificateDelimiterMachine.Checking

end
