import Applications.Resources.RotationCertificate.FuelDispatchMachine
import Applications.Resources.RotationCertificate.BinaryVerifier
import Examples.RotationCertificateVerification

/-!
# Actual fuel-machine handoffs in the rotation verifier

These clients preserve literal fuel width, the higher unvisited suffix, the
represented borrowed prefix, finite caller state and unrelated stack contents.
They distinguish live handoffs from caller execution and source-event work from
actual TM2 transitions. Complete certificate-bit decoding remains before the
decoded-word fuel gate. The parser, rotation and equality continuations are not
implemented by these examples.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.RotationCertificateFuelMachine
open Trees Trees.Rotations Resources
open Resources.BinaryCounter
open Resources.RotationCertificate
open RotationDistanceExample (empty singleton leftTwo rightTwo rootRight)

namespace Core
open FixedWidthMachine

section Context
variable {K Λ R : Type} [DecidableEq K]
variable {Γ : K → Type}
variable (caller : External Λ → Statement Γ Λ R)
variable (regs : Registers R) (ctx : ∀ k, List (Γ k))

/-! General clients retain the exact returned word and every arbitrary store. -/

theorem first_true_preserves_arbitrary_higher_bits
    [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)] (zeros : Nat) (higher : Bits) :
    (next caller)^[2 * zeros + 2]
        (some (cfg (some (phaseLabel .borrow)) regs
          (List.replicate zeros false ++ true :: higher) [] ctx)) =
      some (cfg (some (resultLabel .positive)) (reset regs)
        (List.replicate zeros true ++ false :: higher) [] ctx) := by
  apply borrow_run_first_true

theorem zero_restores_its_supplied_width
    [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)] (width : Nat) :
    (next caller)^[2 * width + 2]
        (some (cfg (some (phaseLabel .borrow)) regs
          (List.replicate width false) [] ctx)) =
      some (cfg (some (resultLabel .zero)) (reset regs)
        (List.replicate width false) [] ctx) := by
  apply borrow_run_replicate_false

theorem literal_zero_widths_remain_distinct
    [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)] :
    (next caller)^[2]
        (some (cfg (some (phaseLabel .borrow)) regs [] [] ctx)) =
        some (cfg (some (resultLabel .zero)) (reset regs) [] [] ctx) ∧
      (next caller)^[4]
        (some (cfg (some (phaseLabel .borrow)) regs [false] [] ctx)) =
        some (cfg (some (resultLabel .zero)) (reset regs) [false] [] ctx) ∧
      (next caller)^[6]
        (some (cfg (some (phaseLabel .borrow)) regs [false, false] [] ctx)) =
        some (cfg (some (resultLabel .zero)) (reset regs) [false, false] [] ctx) :=
  ⟨zero_restores_its_supplied_width caller regs ctx 0,
    zero_restores_its_supplied_width caller regs ctx 1,
    zero_restores_its_supplied_width caller regs ctx 2⟩

theorem one_and_high_zero_one_keep_different_widths
    [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)] :
    value [true] = value [true, false, false] ∧
      (next caller)^[2]
        (some (cfg (some (phaseLabel .borrow)) regs [true] [] ctx)) =
        some (cfg (some (resultLabel .positive)) (reset regs) [false] [] ctx) ∧
      (next caller)^[2]
        (some (cfg (some (phaseLabel .borrow)) regs [true, false, false] [] ctx)) =
        some (cfg (some (resultLabel .positive)) (reset regs)
          [false, false, false] [] ctx) :=
  ⟨rfl, first_true_preserves_arbitrary_higher_bits caller regs ctx 0 [],
    first_true_preserves_arbitrary_higher_bits caller regs ctx 0 [false, false]⟩

theorem two_and_four_borrow_before_the_first_true
    [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)] :
    (next caller)^[4]
        (some (cfg (some (phaseLabel .borrow)) regs [false, true] [] ctx)) =
        some (cfg (some (resultLabel .positive)) (reset regs) [true, false] [] ctx) ∧
      (next caller)^[6]
        (some (cfg (some (phaseLabel .borrow)) regs [false, false, true] [] ctx)) =
        some (cfg (some (resultLabel .positive)) (reset regs)
          [true, true, false] [] ctx) :=
  ⟨first_true_preserves_arbitrary_higher_bits caller regs ctx 1 [],
    first_true_preserves_arbitrary_higher_bits caller regs ctx 2 []⟩

theorem twenty_to_nineteen_preserves_nonpalindromic_high_bits
    [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)] :
    value [false, false, true, false, true, false, false] = 20 ∧
      value [true, true, false, false, true, false, false] = 19 ∧
      (next caller)^[6]
        (some (cfg (some (phaseLabel .borrow)) regs
          [false, false, true, false, true, false, false] [] ctx)) =
        some (cfg (some (resultLabel .positive)) (reset regs)
          [true, true, false, false, true, false, false] [] ctx) :=
  ⟨rfl, rfl,
    first_true_preserves_arbitrary_higher_bits caller regs ctx 2
      [false, true, false, false]⟩

theorem later_failure_observes_the_retained_high_zeros
    [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)] :
    (next caller)^[4]
        (some (cfg (some (phaseLabel .borrow)) regs [false] [] ctx)) =
        some (cfg (some (resultLabel .zero)) (reset regs) [false] [] ctx) ∧
      (next caller)^[8]
        (some (cfg (some (phaseLabel .borrow)) regs [false, false, false] [] ctx)) =
        some (cfg (some (resultLabel .zero)) (reset regs)
          [false, false, false] [] ctx) :=
  ⟨zero_restores_its_supplied_width caller regs ctx 1,
    zero_restores_its_supplied_width caller regs ctx 3⟩

theorem actual_returned_word_has_the_source_width_and_value
    [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)] (fuel returned : Bits)
    (ran : (decFixedRun fuel).1 = some returned) :
    (next caller)^[runSteps fuel]
        (some (cfg (some (phaseLabel .borrow)) regs fuel [] ctx)) =
        some (cfg (some (resultLabel .positive)) (reset regs) returned [] ctx) ∧
      returned.length = fuel.length ∧ value fuel = value returned + 1 := by
  refine ⟨?_, decFixedRun_some_spec ran⟩
  apply borrow_run_of_some
  exact ran

/-! Existing scratch represents already borrowed zeros; it is not disposable data. -/

theorem restore_true_prepends_to_arbitrary_existing_fuel
    [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)] (raw : Bits) (borrowed : List Unit) :
    (next caller)^[borrowed.length + 1]
        (some (cfg (some (phaseLabel .restoreTrue)) regs raw borrowed ctx)) =
      some (cfg (some (resultLabel .positive)) (reset regs)
        (List.replicate borrowed.length true ++ raw) [] ctx) := by
  apply restoreTrue_iterate

theorem restore_false_prepends_to_arbitrary_existing_fuel
    [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)] (raw : Bits) (borrowed : List Unit) :
    (next caller)^[borrowed.length + 1]
        (some (cfg (some (phaseLabel .restoreFalse)) regs raw borrowed ctx)) =
      some (cfg (some (resultLabel .zero)) (reset regs)
        (List.replicate borrowed.length false ++ raw) [] ctx) := by
  apply restoreFalse_iterate

theorem arbitrary_scratch_records_the_logical_low_zero_prefix
    [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
    (raw : Bits) (borrowed : List Unit) :
    (next caller)^[runSteps raw + borrowed.length]
        (some (cfg (some (phaseLabel .borrow)) regs raw borrowed ctx)) =
      some (cfg
        (some (resultLabel (predSpec (List.replicate borrowed.length false ++ raw)).1))
        (reset regs) (predSpec (List.replicate borrowed.length false ++ raw)).2 [] ctx) := by
  apply borrow_iterate

theorem existing_tokens_count_only_the_remaining_restore_work
    [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
    (zeros width : Nat) (higher : Bits) (borrowed : List Unit) :
    (next caller)^[2 * zeros + borrowed.length + 2]
        (some (cfg (some (phaseLabel .borrow)) regs
          (List.replicate zeros false ++ true :: higher) borrowed ctx)) =
        some (cfg (some (resultLabel .positive)) (reset regs)
          (List.replicate (borrowed.length + zeros) true ++ false :: higher) [] ctx) ∧
      (next caller)^[2 * width + borrowed.length + 2]
        (some (cfg (some (phaseLabel .borrow)) regs
          (List.replicate width false) borrowed ctx)) =
        some (cfg (some (resultLabel .zero)) (reset regs)
          (List.replicate (borrowed.length + width) false) [] ctx) :=
  ⟨borrow_first_true_iterate caller zeros higher borrowed regs ctx,
    borrow_zero_iterate caller width borrowed regs ctx⟩

theorem one_pending_token_cannot_be_ignored
    [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)] :
    (next caller)^[3]
        (some (cfg (some (phaseLabel .borrow)) regs [true] [()] ctx)) =
        some (cfg (some (resultLabel .positive)) (reset regs) [true, false] [] ctx) ∧
      (next caller)^[3]
        (some (cfg (some (phaseLabel .borrow)) regs [] [()] ctx)) =
        some (cfg (some (resultLabel .zero)) (reset regs) [false] [] ctx) :=
  ⟨borrow_iterate caller [true] [()] regs ctx, borrow_iterate caller [] [()] regs ctx⟩

/-! Stale local registers are overwritten while caller state remains unchanged. -/

theorem eof_and_scratch_eof_ignore_stale_local_registers
    [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)] (borrowed : List Unit) (raw : Bits) :
    step caller (cfg (some (phaseLabel .borrow)) regs [] borrowed ctx) =
        some (cfg (some (phaseLabel .restoreFalse)) (reset regs) [] borrowed ctx) ∧
      step caller (cfg (some (phaseLabel .restoreTrue)) regs raw [] ctx) =
        some (cfg (some (resultLabel .positive)) (reset regs) raw [] ctx) ∧
      step caller (cfg (some (phaseLabel .restoreFalse)) regs raw [] ctx) =
        some (cfg (some (resultLabel .zero)) (reset regs) raw [] ctx) := by
  refine ⟨?_, ?_, ?_⟩
  · apply borrow_step_nil
  · apply restoreTrue_step_nil
  · apply restoreFalse_step_nil

theorem restored_failure_has_actual_intermediate_cells
    [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)] :
    step caller (cfg (some (phaseLabel .borrow)) regs [false, false] [] ctx) =
        some (cfg (some (phaseLabel .borrow)) (reset regs) [false] [()] ctx) ∧
      step caller (cfg (some (phaseLabel .borrow)) (reset regs) [false] [()] ctx) =
        some (cfg (some (phaseLabel .borrow)) (reset regs) [] [(), ()] ctx) ∧
      step caller (cfg (some (phaseLabel .borrow)) (reset regs) [] [(), ()] ctx) =
        some (cfg (some (phaseLabel .restoreFalse)) (reset regs) [] [(), ()] ctx) ∧
      step caller (cfg (some (phaseLabel .restoreFalse)) (reset regs) [] [(), ()] ctx) =
        some (cfg (some (phaseLabel .restoreFalse)) (reset regs) [false] [()] ctx) ∧
      step caller (cfg (some (phaseLabel .restoreFalse)) (reset regs) [false] [()] ctx) =
        some (cfg (some (phaseLabel .restoreFalse)) (reset regs) [false, false] [] ctx) ∧
      step caller (cfg (some (phaseLabel .restoreFalse)) (reset regs) [false, false] [] ctx) =
        some (cfg (some (resultLabel .zero)) (reset regs) [false, false] [] ctx) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply borrow_step_false
  · apply borrow_step_false
  · apply borrow_step_nil
  · apply restoreFalse_step_cons
  · apply restoreFalse_step_cons
  · apply restoreFalse_step_nil

theorem primitive_time_is_bounded_without_decoding_a_natural (fuel : Bits) :
    runSteps fuel ≤ 2 * fuel.length + 2 ∧ runSteps fuel ≤ (decFixedRun fuel).2 :=
  ⟨runSteps_le fuel, runSteps_le_source_cost fuel⟩

def uniformBorrowTiming (fuel : Bits) :
    StateTransition.EvalsToInTime (step caller)
      (cfg (some (phaseLabel .borrow)) regs fuel [] ctx)
      (some (cfg (some (resultLabel (predSpec fuel).1))
        (reset regs) (predSpec fuel).2 [] ctx)) (2 * fuel.length + 2) := by
  apply borrowInLinearTime

theorem successful_borrow_keeps_the_old_high_suffix_at_each_stage
    [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)] (higher : Bits) :
    step caller (cfg (some (phaseLabel .borrow)) regs
        (false :: false :: true :: higher) [] ctx) =
        some (cfg (some (phaseLabel .borrow)) (reset regs)
          (false :: true :: higher) [()] ctx) ∧
      step caller (cfg (some (phaseLabel .borrow)) (reset regs)
        (false :: true :: higher) [()] ctx) =
        some (cfg (some (phaseLabel .borrow)) (reset regs) (true :: higher) [(), ()] ctx) ∧
      step caller (cfg (some (phaseLabel .borrow)) (reset regs) (true :: higher) [(), ()] ctx) =
        some (cfg (some (phaseLabel .restoreTrue)) (reset regs)
          (false :: higher) [(), ()] ctx) ∧
      step caller (cfg (some (phaseLabel .restoreTrue)) (reset regs)
        (false :: higher) [(), ()] ctx) =
        some (cfg (some (phaseLabel .restoreTrue)) (reset regs)
          (true :: false :: higher) [()] ctx) ∧
      step caller (cfg (some (phaseLabel .restoreTrue)) (reset regs)
        (true :: false :: higher) [()] ctx) =
        some (cfg (some (phaseLabel .restoreTrue)) (reset regs)
          (true :: true :: false :: higher) [] ctx) ∧
      (next caller)^[6]
        (some (cfg (some (phaseLabel .borrow)) regs
          (false :: false :: true :: higher) [] ctx)) =
        some (cfg (some (resultLabel .positive)) (reset regs)
          (true :: true :: false :: higher) [] ctx) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply borrow_step_false
  · apply borrow_step_false
  · apply borrow_step_true
  · apply restoreTrue_step_cons
  · apply restoreTrue_step_cons
  · exact first_true_preserves_arbitrary_higher_bits caller regs ctx 2 higher

theorem independently_presented_programs_use_the_same_owned_blocks
    [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
    (ambient : Label Λ → Statement Γ Λ R)
    (owned : ∀ phase, ambient (phaseLabel phase) = block phase)
    (zeros : Nat) (higher : Bits) :
    (fun state : Option (Cfg Γ Λ R) => state.bind (Turing.TM2.step ambient))^[2 * zeros + 2]
        (some (cfg (some (phaseLabel .borrow)) regs
          (List.replicate zeros false ++ true :: higher) [] ctx)) =
      some (cfg (some (resultLabel .positive)) (reset regs)
        (List.replicate zeros true ++ false :: higher) [] ctx) := by
  rw [program_eq_of_agrees ambient owned]
  apply borrow_run_first_true

theorem every_actual_prefix_preserves_context_through_the_first_exit
    [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
    (phase : Phase) (raw : Bits) (borrowed : List Unit) (n : Nat)
    (bound : n ≤ phaseSteps phase raw borrowed) (reached : Cfg Γ Λ R)
    (ran : (next caller)^[n]
      (some (cfg (some (phaseLabel phase)) regs raw borrowed ctx)) = some reached) :
    reached.var.2 = regs.2 ∧ (∀ k, reached.stk (.inr k) = ctx k) ∧
      stackCells reached = stackCells (cfg (Λ := Λ) (some (phaseLabel phase)) regs raw borrowed ctx) ∧
      (n < phaseSteps phase raw borrowed ↔ Owned reached.l) ∧
      (0 < n → reached.var.1 = none) := by
  obtain ⟨actual, executed, _, path, inside, canonical⟩ :=
    phase_prefix caller phase raw borrowed regs ctx n bound
  have same : actual = reached := Option.some.inj (executed.symm.trans ran)
  cases same
  have preserved := local_reaches_preserves caller path
  exact ⟨preserved.1, preserved.2.1, preserved.2.2, inside, canonical⟩

theorem arbitrary_callers_have_identical_pre_handoff_runs
    [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
    (other : External Λ → Statement Γ Λ R) (phase : Phase) (raw : Bits)
    (borrowed : List Unit) (n : Nat) (bound : n ≤ phaseSteps phase raw borrowed) :
    (next caller)^[n] (some (cfg (some (phaseLabel phase)) regs raw borrowed ctx)) =
      (next other)^[n] (some (cfg (some (phaseLabel phase)) regs raw borrowed ctx)) :=
  phase_prefix_caller_independent caller other phase raw borrowed regs ctx n bound

theorem every_actual_borrow_prefix_represents_the_same_original_word
    [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
    (raw : Bits) (borrowed : List Unit) (n : Nat) (reached : Cfg Γ Λ R)
    (bound : n ≤ runSteps raw + borrowed.length)
    (ran : (next caller)^[n]
      (some (cfg (some (phaseLabel .borrow)) regs raw borrowed ctx)) = some reached) :
    FuelRepresents (List.replicate borrowed.length false ++ raw) reached :=
  borrow_prefix_represents caller raw borrowed regs ctx n reached bound ran

theorem twelve_to_eleven_has_an_actual_two_token_restore_state
    [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)] :
    (next caller)^[3]
        (some (cfg (some (phaseLabel .borrow)) regs
          [false, false, true, true, false] [] ctx)) =
        some (cfg (some (phaseLabel .restoreTrue)) (reset regs)
          [false, true, false] [(), ()] ctx) ∧
      FuelRepresents [false, false, true, true, false]
        (cfg (Λ := Λ) (some (phaseLabel .restoreTrue)) (reset regs)
          [false, true, false] [(), ()] ctx) ∧
      value [false, false, true, true, false] = 12 ∧
      value [true, true, false, true, false] = 11 := by
  have reached : (next caller)^[3]
      (some (cfg (some (phaseLabel .borrow)) regs
        [false, false, true, true, false] [] ctx)) =
      some (cfg (some (phaseLabel .restoreTrue)) (reset regs)
        [false, true, false] [(), ()] ctx) := by
    change next caller (next caller (next caller
      (some (cfg (some (phaseLabel .borrow)) regs
        [false, false, true, true, false] [] ctx)))) = _
    rw [next_some, borrow_step_false, next_some, borrow_step_false,
      next_some, borrow_step_true]
    rfl
  refine ⟨reached, ?_, rfl, rfl⟩
  exact borrow_prefix_represents caller [false, false, true, true, false] [] regs ctx
    3 _ (by decide) reached

/-- A continuation premise is actual timed execution on the same returned configuration. -/
def borrowThenContinuationTiming (fuel : Bits) (finish : Option (Cfg Γ Λ R)) (budget : Nat)
    (continued : StateTransition.EvalsToInTime (step caller)
      (cfg (some (resultLabel (predSpec fuel).1)) (reset regs) (predSpec fuel).2 [] ctx)
      finish budget) :
    StateTransition.EvalsToInTime (step caller)
      (cfg (some (phaseLabel .borrow)) regs fuel [] ctx) finish
      (budget + (2 * fuel.length + 2)) :=
  StateTransition.EvalsToInTime.trans (step caller) (2 * fuel.length + 2) budget
    (cfg (some (phaseLabel .borrow)) regs fuel [] ctx)
    (cfg (some (resultLabel (predSpec fuel).1)) (reset regs) (predSpec fuel).2 [] ctx)
    finish (uniformBorrowTiming caller regs ctx fuel) continued

end Context

theorem concrete_control_and_stack_families_are_finite :
    Fintype.card (Registers Bool) = 6 ∧ Fintype.card (Label Unit) = 6 ∧
      Fintype.card (StackId Unit) = 3 := by decide

/-! This concrete caller changes a protected stack only after the proved handoff. -/

def sentinelCaller : External Unit → Statement (fun _ : Unit => Bool) Unit Bool
  | .inl .positive => .push (.inr ()) (fun _ => true) .halt
  | .inl .zero => .halt
  | .inr () => .halt

def sentinelStart (flag : Bool) (old : Bits) : Cfg (fun _ : Unit => Bool) Unit Bool :=
  cfg (some (phaseLabel .borrow)) (some true, flag) [true] [] (fun _ => old)

def sentinelHandoff (flag : Bool) (old : Bits) : Cfg (fun _ : Unit => Bool) Unit Bool :=
  cfg (some (resultLabel .positive)) (none, flag) [false] [] (fun _ => old)

def sentinelAfterCaller (flag : Bool) (old : Bits) : Cfg (fun _ : Unit => Bool) Unit Bool :=
  cfg none (none, flag) [false] [] (fun _ => true :: old)

theorem sentinel_handoff_keeps_old_caller_data (flag : Bool) (old : Bits) :
    (next sentinelCaller)^[2] (some (sentinelStart flag old)) =
      some (sentinelHandoff flag old) :=
  borrow_run_first_true sentinelCaller 0 [] (some true, flag) (fun _ => old)

theorem sentinel_body_is_an_additional_actual_transition (flag : Bool) (old : Bits) :
    step sentinelCaller (sentinelHandoff flag old) = some (sentinelAfterCaller flag old) := by
  apply congrArg some
  apply cfg_ext
  · rfl
  · rfl
  · rfl
  · rfl
  · intro token
    cases token
    rfl

def sentinelHandoffInTime (flag : Bool) (old : Bits) :
    StateTransition.EvalsToInTime (step sentinelCaller) (sentinelStart flag old)
      (some (sentinelHandoff flag old)) 2 :=
  borrowInTime sentinelCaller [true] [] (some true, flag) (fun _ => old)

def sentinelCallerInTime (flag : Bool) (old : Bits) :
    StateTransition.EvalsToInTime (step sentinelCaller) (sentinelHandoff flag old)
      (some (sentinelAfterCaller flag old)) 1 where
  steps := 1
  evals_in_steps := sentinel_body_is_an_additional_actual_transition flag old
  steps_le_m := Nat.le_refl _

def sentinelCompositionInTime (flag : Bool) (old : Bits) :
    StateTransition.EvalsToInTime (step sentinelCaller) (sentinelStart flag old)
      (some (sentinelAfterCaller flag old)) 3 :=
  StateTransition.EvalsToInTime.trans (step sentinelCaller) 2 1
    (sentinelStart flag old) (sentinelHandoff flag old) (some (sentinelAfterCaller flag old))
    (sentinelHandoffInTime flag old) (sentinelCallerInTime flag old)

theorem a_live_handoff_then_caller_then_outer_none (flag : Bool) (old : Bits) :
    (sentinelHandoff flag old).l = some (resultLabel .positive) ∧
      (next sentinelCaller)^[3] (some (sentinelStart flag old)) =
        some (sentinelAfterCaller flag old) ∧
      (next sentinelCaller)^[4] (some (sentinelStart flag old)) = none := by
  have completed : (next sentinelCaller)^[3] (some (sentinelStart flag old)) =
      some (sentinelAfterCaller flag old) :=
    (sentinelCompositionInTime flag old).evals_in_steps
  refine ⟨rfl, completed, ?_⟩
  rw [show 4 = 3 + 1 by rfl, Function.iterate_succ_apply', completed]
  rfl

theorem caller_push_is_a_counterexample_to_unrestricted_workspace_preservation
    (flag : Bool) (old : Bits) :
    (next sentinelCaller)^[2] (some (sentinelStart flag old)) =
        some (sentinelHandoff flag old) ∧
      stackCells (sentinelHandoff flag old) = stackCells (sentinelStart flag old) ∧
      (next sentinelCaller)^[3] (some (sentinelStart flag old)) =
        some (sentinelAfterCaller flag old) ∧
      stackCells (sentinelAfterCaller flag old) = stackCells (sentinelStart flag old) + 1 := by
  refine ⟨sentinel_handoff_keeps_old_caller_data flag old, ?_,
    (sentinelCompositionInTime flag old).evals_in_steps, ?_⟩
  · rfl
  · simp [stackCells, sentinelAfterCaller, sentinelStart, cfg, Nat.add_comm]

end Core

namespace Dispatch
open FuelDispatchMachine

section Context
variable {K Λ R : Type} [DecidableEq K]
variable {Γ : K → Type}
variable (caller : (Exit ⊕ Λ) → Statement Γ Λ R)
variable (regs : FixedWidthMachine.Registers R) (ctx : ∀ k, List (Γ k))

/-! EOF is an actual one-step handoff, without touching fuel or pending scratch. -/

theorem eof_preserves_arbitrary_fuel_and_scratch
    [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)] (fuel : Bits) (borrowed : List Unit) :
    step caller (cfg (some inspectLabel) regs fuel borrowed [] ctx) =
      some (cfg (some atEndLabel) (FixedWidthMachine.reset regs) fuel borrowed [] ctx) := by
  apply dispatch_step_nil

theorem every_nonempty_certificate_is_preserved_before_borrow
    [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
    (fuel : Bits) (borrowed : List Unit) (tag : Tag) (tail : Word) :
    step caller (cfg (some inspectLabel) regs fuel borrowed (tag :: tail) ctx) =
      some (cfg (some (FixedWidthMachine.phaseLabel .borrow))
        (FixedWidthMachine.reset regs) fuel borrowed (tag :: tail) ctx) := by
  apply dispatch_step_cons

theorem positive_fuel_hands_to_the_parser_without_consuming_a_tag
    [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
    (zeros : Nat) (higher : Bits) (tag : Tag) (tail : Word) :
    (next caller)^[2 * zeros + 3]
        (some (cfg (some inspectLabel) regs
          (List.replicate zeros false ++ true :: higher) [] (tag :: tail) ctx)) =
      some (cfg (some positiveLabel) (FixedWidthMachine.reset regs)
        (List.replicate zeros true ++ false :: higher) [] (tag :: tail) ctx) := by
  apply dispatch_run_first_true

theorem zero_fuel_hands_to_rejection_with_the_whole_certificate
    [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
    (width : Nat) (tag : Tag) (tail : Word) :
    (next caller)^[2 * width + 3]
        (some (cfg (some inspectLabel) regs
          (List.replicate width false) [] (tag :: tail) ctx)) =
      some (cfg (some zeroLabel) (FixedWidthMachine.reset regs)
        (List.replicate width false) [] (tag :: tail) ctx) := by
  apply dispatch_run_replicate_false

theorem empty_fuel_distinguishes_eof_from_one_raw_symbol
    [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)] (tag : Tag) (tail : Word) :
    (next caller)^[1] (some (cfg (some inspectLabel) regs [] [] [] ctx)) =
        some (cfg (some atEndLabel) (FixedWidthMachine.reset regs) [] [] [] ctx) ∧
      (next caller)^[3] (some (cfg (some inspectLabel) regs [] [] (tag :: tail) ctx)) =
        some (cfg (some zeroLabel) (FixedWidthMachine.reset regs) [] [] (tag :: tail) ctx) := by
  constructor
  · apply dispatch_run_nil
  · exact zero_fuel_hands_to_rejection_with_the_whole_certificate caller regs ctx 0 tag tail

theorem high_zero_fuel_does_not_slow_eof
    [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)] (width : Nat) :
    (next caller)^[1]
        (some (cfg (some inspectLabel) regs (List.replicate width false) [] [] ctx)) =
      some (cfg (some atEndLabel) (FixedWidthMachine.reset regs)
        (List.replicate width false) [] [] ctx) := by
  apply dispatch_run_nil

theorem first_dispatch_keeps_high_zeros_and_later_rejection_observes_them
    [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
    (tag : Tag) (tail : Word) :
    (next caller)^[3]
        (some (cfg (some inspectLabel) regs [true] [] (tag :: tail) ctx)) =
        some (cfg (some positiveLabel) (FixedWidthMachine.reset regs)
          [false] [] (tag :: tail) ctx) ∧
      (next caller)^[3]
        (some (cfg (some inspectLabel) regs [true, false, false] [] (tag :: tail) ctx)) =
        some (cfg (some positiveLabel) (FixedWidthMachine.reset regs)
          [false, false, false] [] (tag :: tail) ctx) ∧
      (next caller)^[5]
        (some (cfg (some inspectLabel) regs [false] [] (tag :: tail) ctx)) =
        some (cfg (some zeroLabel) (FixedWidthMachine.reset regs)
          [false] [] (tag :: tail) ctx) ∧
      (next caller)^[9]
        (some (cfg (some inspectLabel) regs [false, false, false] [] (tag :: tail) ctx)) =
        some (cfg (some zeroLabel) (FixedWidthMachine.reset regs)
          [false, false, false] [] (tag :: tail) ctx) :=
  ⟨positive_fuel_hands_to_the_parser_without_consuming_a_tag caller regs ctx 0 [] tag tail,
    positive_fuel_hands_to_the_parser_without_consuming_a_tag caller regs ctx 0
      [false, false] tag tail,
    zero_fuel_hands_to_rejection_with_the_whole_certificate caller regs ctx 1 tag tail,
    zero_fuel_hands_to_rejection_with_the_whole_certificate caller regs ctx 3 tag tail⟩

theorem one_pending_token_retains_its_dispatch_meaning
    [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)] (tag : Tag) (tail : Word) :
    (next caller)^[4]
        (some (cfg (some inspectLabel) regs [true] [()] (tag :: tail) ctx)) =
        some (cfg (some positiveLabel) (FixedWidthMachine.reset regs)
          [true, false] [] (tag :: tail) ctx) ∧
      (next caller)^[4]
        (some (cfg (some inspectLabel) regs [] [()] (tag :: tail) ctx)) =
        some (cfg (some zeroLabel) (FixedWidthMachine.reset regs)
          [false] [] (tag :: tail) ctx) :=
  ⟨dispatch_run_cons caller [true] [()] tag tail regs ctx,
    dispatch_run_cons caller [] [()] tag tail regs ctx⟩

/-! The same actual returned fuel appears in the source verifier's branch. -/

theorem zero_restoration_and_source_rejection_are_connected
    [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
    (width : Nat) (tag : Tag) (tail : Word) (source target : BinaryTree Unit) :
    (next caller)^[2 * width + 3]
        (some (cfg (some inspectLabel) regs
          (List.replicate width false) [] (tag :: tail) ctx)) =
        some (cfg (some zeroLabel) (FixedWidthMachine.reset regs)
          (List.replicate width false) [] (tag :: tail) ctx) ∧
      checkStreamRun (List.replicate width false) source target (tag :: tail) =
        (false, 2 * width + 4) :=
  ⟨zero_fuel_hands_to_rejection_with_the_whole_certificate caller regs ctx width tag tail,
    checkStreamRun_replicate_false width source target tag tail⟩

theorem reserved_heads_wait_for_the_parser_after_positive_fuel
    [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
    (higher : Bits) (tag : Tag) (reserved : 11 ≤ tag.val) (tail : Word)
    (source target : BinaryTree Unit) :
    (next caller)^[3]
        (some (cfg (some inspectLabel) regs (true :: higher) [] (tag :: tail) ctx)) =
        some (cfg (some positiveLabel) (FixedWidthMachine.reset regs)
          (false :: higher) [] (tag :: tail) ctx) ∧
      checkStreamRun (true :: higher) source target (tag :: tail) = (false, 7) :=
  ⟨positive_fuel_hands_to_the_parser_without_consuming_a_tag caller regs ctx 0 higher tag tail,
    Examples.RotationCertificateVerification.every_reserved_head_stops_after_fuel
      higher source target tag reserved tail⟩

theorem missing_move_delimiter_is_a_later_source_failure
    [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
    (source target : BinaryTree Unit) :
    (next caller)^[3]
        (some (cfg (some inspectLabel) regs [true] [] [rotateRightTag] ctx)) =
        some (cfg (some positiveLabel) (FixedWidthMachine.reset regs)
          [false] [] [rotateRightTag] ctx) ∧
      checkStreamRun [true] source target [rotateRightTag] = (false, 9) :=
  ⟨positive_fuel_hands_to_the_parser_without_consuming_a_tag caller regs ctx 0 []
      rotateRightTag [],
    (Examples.RotationCertificateVerification.missing_move_delimiters_stop_before_execution
      source target).1⟩

theorem eof_handoff_itself_does_not_decide_tree_equality
    [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)] (fuel : Bits) :
    (next caller)^[1] (some (cfg (some inspectLabel) regs fuel [] [] ctx)) =
        some (cfg (some atEndLabel) (FixedWidthMachine.reset regs) fuel [] [] ctx) ∧
      checkStreamRun fuel empty.val empty.val [] = (true, 3) ∧
      checkStreamRun fuel empty.val singleton.val [] = (false, 3) := by
  refine ⟨?_, ?_, ?_⟩
  · apply dispatch_run_nil
  · exact (Examples.RotationCertificateVerification.eof_literal_cases fuel).1
  · exact (Examples.RotationCertificateVerification.eof_literal_cases fuel).2.2.2

theorem all_raw_words_have_a_linear_entry_bound (fuel : Bits) (cert : Word) :
    dispatchSteps fuel cert ≤ 2 * fuel.length + 3 :=
  dispatchSteps_le fuel cert

def uniformDispatchTiming (fuel : Bits) (cert : Word) :
    StateTransition.EvalsToInTime (step caller)
      (cfg (some inspectLabel) regs fuel [] cert ctx)
      (some (cfg (some (exitLabel (dispatchSpec fuel cert).1)) (FixedWidthMachine.reset regs)
        (dispatchSpec fuel cert).2 [] cert ctx)) (2 * fuel.length + 3) := by
  apply dispatchInLinearTime

theorem the_same_returned_fuel_enters_the_actual_source_continuation
    [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
    (fuel returned : Bits) (source target : BinaryTree Unit) (tag : Tag) (tail : Word)
    (ran : (decFixedRun fuel).1 = some returned) :
    let continued := bind (parseMoveRun (tag :: tail)) (fun parsed => match parsed with
      | none => (false, 1)
      | some (move, rest) => bind (applyMoveRun move source) (fun applied => match applied with
        | none => (false, 1)
        | some reached => checkStreamRun returned reached target rest))
    (next caller)^[FixedWidthMachine.runSteps fuel + 1]
        (some (cfg (some inspectLabel) regs fuel [] (tag :: tail) ctx)) =
        some (cfg (some positiveLabel) (FixedWidthMachine.reset regs) returned [] (tag :: tail) ctx) ∧
      checkStreamRun fuel source target (tag :: tail) =
        (continued.1, 1 + (decFixedRun fuel).2 + continued.2) := by
  exact dispatch_positive_stream caller fuel returned source target tag tail regs ctx ran

theorem an_ambient_verifier_needs_only_owned_body_agreement
    [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
    (ambient : Label Λ → Statement Γ Λ R)
    (phases : ∀ phase, ambient (FixedWidthMachine.phaseLabel phase) = FixedWidthMachine.block phase)
    (inspect : ambient inspectLabel = inspectBlock) (width : Nat) (tag : Tag) (tail : Word) :
    (fun state : Option (Cfg Γ Λ R) => state.bind (Turing.TM2.step ambient))^[2 * width + 3]
        (some (cfg (some inspectLabel) regs (List.replicate width false) [] (tag :: tail) ctx)) =
      some (cfg (some zeroLabel) (FixedWidthMachine.reset regs)
        (List.replicate width false) [] (tag :: tail) ctx) := by
  rw [program_eq_of_agrees ambient phases inspect]
  apply dispatch_run_replicate_false

theorem every_actual_dispatch_prefix_preserves_all_represented_data
    [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
    (fuel : Bits) (cert : Word) (n : Nat) (bound : n ≤ dispatchSteps fuel cert)
    (reached : Cfg Γ Λ R)
    (ran : (next caller)^[n]
      (some (cfg (some inspectLabel) regs fuel [] cert ctx)) = some reached) :
    reached.var.2 = regs.2 ∧ reached.stk (.inr (.inl ())) = cert ∧
      (∀ k, reached.stk (.inr (.inr k)) = ctx k) ∧
      stackCells reached = stackCells (cfg (Λ := Λ) (some inspectLabel) regs fuel [] cert ctx) ∧
      (n < dispatchSteps fuel cert ↔ Owned reached.l) ∧
      (0 < n → reached.var.1 = none) := by
  obtain ⟨actual, executed, _, path, inside, canonical⟩ :=
    dispatch_prefix caller fuel cert regs ctx n bound
  have same : actual = reached := Option.some.inj (executed.symm.trans ran)
  cases same
  have preserved := local_reaches_preserves caller path
  exact ⟨preserved.1, preserved.2.1, preserved.2.2.1, preserved.2.2.2, inside, canonical⟩

theorem arbitrary_stream_callers_agree_until_the_handoff
    [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
    (other : (Exit ⊕ Λ) → Statement Γ Λ R) (fuel : Bits) (cert : Word)
    (n : Nat) (bound : n ≤ dispatchSteps fuel cert) :
    (next caller)^[n] (some (cfg (some inspectLabel) regs fuel [] cert ctx)) =
      (next other)^[n] (some (cfg (some inspectLabel) regs fuel [] cert ctx)) :=
  dispatch_prefix_caller_independent caller other fuel cert regs ctx n bound

end Context

/-- Unbounded trees occupy lists of finite tags, never the finite control register. -/
def representedTrees (source target : BinaryTree Unit) : Bool → Word :=
  fun which => if which then treeCode target else treeCode source

theorem an_actual_emitted_rotation_reaches_the_parser_in_three_steps
    (caller : (Exit ⊕ Unit) → Statement (fun _ : Bool => Tag) Unit Bool)
    (regs : Registers Bool) :
    (next caller)^[3]
        (some (cfg (some inspectLabel) regs [true] []
          (emitCertificateRun [rootRight] []).1 (representedTrees leftTwo.val rightTwo.val))) =
        some (cfg (some positiveLabel) (FixedWidthMachine.reset regs) [false] []
          (emitCertificateRun [rootRight] []).1 (representedTrees leftTwo.val rightTwo.val)) ∧
      checkStreamRun [true] leftTwo.val rightTwo.val
        (emitCertificateRun [rootRight] []).1 = (true, 22) := by
  constructor
  · rw [emitCertificateRun_value, List.append_nil]
    exact positive_fuel_hands_to_the_parser_without_consuming_a_tag caller regs
      (representedTrees leftTwo.val rightTwo.val) 0 [] rotateRightTag [endMoveTag]
  · rw [emitCertificateRun_value, List.append_nil]
    exact Examples.RotationCertificateVerification.one_right_move

theorem a_longer_borrow_has_distinct_machine_and_source_counts
    (caller : (Exit ⊕ Unit) → Statement (fun _ : Bool => Tag) Unit Bool)
    (regs : Registers Bool) (zeros : Nat) (higher : Bits) :
    (next caller)^[2 * zeros + 3]
        (some (cfg (some inspectLabel) regs
          (List.replicate zeros false ++ true :: higher) [] (certCode [rootRight])
          (representedTrees leftTwo.val rightTwo.val))) =
        some (cfg (some positiveLabel) (FixedWidthMachine.reset regs)
          (List.replicate zeros true ++ false :: higher) [] (certCode [rootRight])
          (representedTrees leftTwo.val rightTwo.val)) ∧
      checkStreamRun (List.replicate zeros false ++ true :: higher)
        leftTwo.val rightTwo.val (certCode [rootRight]) = (true, 3 * zeros + 22) :=
  ⟨positive_fuel_hands_to_the_parser_without_consuming_a_tag caller regs
      (representedTrees leftTwo.val rightTwo.val) zeros higher rotateRightTag [endMoveTag],
    Examples.RotationCertificateVerification.arbitrary_higher_fuel_is_unvisited_for_one_move
      zeros higher⟩

theorem equal_initial_trees_do_not_skip_a_nonempty_certificate
    (caller : (Exit ⊕ Unit) → Statement (fun _ : Bool => Tag) Unit Bool)
    (regs : Registers Bool) :
    (next caller)^[3]
        (some (cfg (some inspectLabel) regs [true] [] (certCode [rootRight])
          (representedTrees leftTwo.val leftTwo.val))) =
        some (cfg (some positiveLabel) (FixedWidthMachine.reset regs) [false] []
          (certCode [rootRight]) (representedTrees leftTwo.val leftTwo.val)) ∧
      checkStreamRun [true] leftTwo.val leftTwo.val (certCode [rootRight]) = (false, 18) :=
  ⟨positive_fuel_hands_to_the_parser_without_consuming_a_tag caller regs
      (representedTrees leftTwo.val leftTwo.val) 0 [] rotateRightTag [endMoveTag],
    Examples.RotationCertificateVerification.initial_equality_does_not_accept_early⟩

end Dispatch

namespace SourceLayers

theorem actual_emitted_root_rotation_has_source_work_twenty_two :
    checkStreamRun [true] leftTwo.val rightTwo.val
      (emitCertificateRun [rootRight] []).1 = (true, 22) := by
  rw [emitCertificateRun_value, List.append_nil]
  exact Examples.RotationCertificateVerification.one_right_move

theorem eager_binary_decoding_precedes_zero_fuel (bit : Bool) (tag : Tag) :
    (wordBits (inputCode .nil .nil [false])).length = 24 ∧
      verifyBitsRun (wordBits (inputCode .nil .nil [false])) [bit] = (false, 48) ∧
      verifyBitsRun (wordBits (inputCode .nil .nil [false])) (wordBits [tag]) = (false, 57) := by
  have decoded := congrArg Prod.fst (unpackWordRun_code (inputCode .nil .nil [false]))
  have parsed := congrArg Prod.fst (parseInputRun_code .nil .nil [false])
  have short : unpackWordRun [bit] = (none, 2) :=
    unpackWordRun_short [bit] (by simp) (by simp)
  have stopped : checkStreamRun [false] .nil .nil [tag] = (false, 6) :=
    checkStreamRun_replicate_false 1 .nil .nil tag []
  refine ⟨?_, ?_, ?_⟩
  · rw [wordBits_length]
    rfl
  · rw [verifyBitsRun_certificate_none _ _ (inputCode .nil .nil [false])
      .nil .nil [false] decoded parsed (congrArg Prod.fst short),
      unpackWordRun_code, parseInputRun_code, short]
    rfl
  · rw [verifyBitsRun_success _ _ (inputCode .nil .nil [false]) [tag]
      .nil .nil [false] decoded parsed (by rw [unpackWordRun_code]),
      unpackWordRun_code, parseInputRun_code, unpackWordRun_code, stopped]
    rfl

theorem only_the_completely_decoded_certificate_reaches_the_five_step_gate
    {K Λ R : Type} [Fintype K] [DecidableEq K] [Fintype Λ] [Fintype R]
    {Γ : K → Type} [∀ k, Fintype (Γ k)]
    (caller : (FuelDispatchMachine.Exit ⊕ Λ) → FuelDispatchMachine.Statement Γ Λ R)
    (regs : FixedWidthMachine.Registers R) (ctx : ∀ k, List (Γ k)) (bit : Bool) :
    unpackWordRun [bit] = (none, 2) ∧
      unpackWordRun (wordBits [(11 : Tag)]) = (some [11], 6) ∧
      verifyBitsRun (wordBits (inputCode .nil .nil [false])) [bit] = (false, 48) ∧
      verifyBitsRun (wordBits (inputCode .nil .nil [false])) (wordBits [11]) = (false, 57) ∧
      (FuelDispatchMachine.next caller)^[5]
        (some (FuelDispatchMachine.cfg (some FuelDispatchMachine.inspectLabel)
          regs [false] [] [11] ctx)) =
        some (FuelDispatchMachine.cfg (some FuelDispatchMachine.zeroLabel)
          (FixedWidthMachine.reset regs) [false] [] [11] ctx) :=
  ⟨unpackWordRun_short [bit] (by simp) (by simp), unpackWordRun_code [11],
    (eager_binary_decoding_precedes_zero_fuel bit 11).2.1,
    (eager_binary_decoding_precedes_zero_fuel bit 11).2.2,
    Dispatch.zero_fuel_hands_to_rejection_with_the_whole_certificate caller regs ctx 1 11 []⟩

end SourceLayers

end Examples.RotationCertificateFuelMachine
