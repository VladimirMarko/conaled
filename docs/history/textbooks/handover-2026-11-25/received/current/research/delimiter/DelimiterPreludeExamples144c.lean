import DelimiterPrelude144b

/-!
UNCOMPILED general-repair2 connected cases. The seventeen statements, literal inputs,
clocks and complete old-initializer endpoints are unchanged. Proofs explicitly
transport the initializer through a Cfg Bool function and then use typed
next_some plus only the actual branch lemmas needed by each frozen case.
The residual zero iteration is closed by definitional equality; its unused
simp argument from the actual failed attempt is removed.
No compiler, error-limit, linter, resource or source-semantics setting changes.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Examples.DelimiterPreludeResearch

open Resources.RotationCertificate.DelimiterPreludeDraft

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

end Examples.DelimiterPreludeResearch
