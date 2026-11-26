import Applications.Resources.RotationCertificate.OpenFramingMachine

/-!
# Connected executions of the open binary framer

The physical outputs, dirty accumulator orientations and clocks were fixed in
the preparation before these clients. Execution uses the public phase, source,
rank, prefix and timed contracts. A live result is distinguished from the next
caller step, a present halted configuration and outer `none`.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.RotationCertificateOpenFramingMachine
open Resources.BinaryCounter (Bits)
open Resources.RotationCertificate
open OpenFramingMachine

/-- Different finite protected alphabets retain different kinds of actual data. -/
def SmallAlphabet : Bool → Type
  | false => Bool
  | true => Tag

instance smallAlphabetFintype (k : Bool) : Fintype (SmallAlphabet k) := by
  cases k with
  | false => change Fintype Bool; infer_instance
  | true => change Fintype Tag; infer_instance

def smallContext (bits : Bits) (tags : Word) : ∀ k, List (SmallAlphabet k)
  | false => bits
  | true => tags

def sentinelContext : ∀ k, List (SmallAlphabet k) :=
  smallContext [true, false, false] [15, 6, 1]

def staleRegisters (flag : Bool) : Registers Bool := (some true, flag)

def haltCaller : External Unit → Statement SmallAlphabet Unit Bool := fun _ => .halt

/-- These are the actual type cardinalities of the two-protected-stack client. -/
theorem concrete_control_and_register_counts :
    Fintype.card (StackId Bool) = 7 ∧
      Fintype.card (Label Unit) = 8 ∧ Fintype.card (Registers Bool) = 6 := by
  refine ⟨?_, ?_, ?_⟩
  · simpa using (stackId_card (K := Bool))
  · simpa using (label_card (Λ := Unit))
  · calc
      Fintype.card (Registers Bool) = 3 * Fintype.card Bool := registers_card
      _ = 6 := by rw [Fintype.card_bool]

section Context
variable {K Λ R : Type} [DecidableEq K] {Γ : K → Type}
variable (caller : External Λ → Statement Γ Λ R)
variable (regs : Registers R) (ctx : ∀ k, List (Γ k))

/-- Failure still executes its scan and its actual cleanup empty probe. -/
theorem empty_raw_fails_in_two :
    (next caller)^[2]
        (some (cfg (some (phaseLabel .scanPrefix)) regs [] [] [] [] [] ctx)) =
      some (cfg (some (resultLabel .failure)) (reset regs) [] [] [] [] [] ctx) :=
  run_of_none caller [] regs ctx rfl

theorem dangling_guard_fails_in_two :
    (next caller)^[2]
        (some (cfg (some (phaseLabel .scanPrefix)) regs [false] [] [] [] [] ctx)) =
      some (cfg (some (resultLabel .failure)) (reset regs) [] [] [] [] [] ctx) :=
  run_of_none caller [false] regs ctx rfl

/-- Empty successful fields have the same empty stores as failure and a different label. -/
theorem empty_fields_succeed_in_four :
    (next caller)^[4]
        (some (cfg (some (phaseLabel .scanPrefix)) regs [true] [] [] [] [] ctx)) =
      some (cfg (some (resultLabel .success)) (reset regs) [] [] [] [] [] ctx) :=
  run_frame caller [] [] regs ctx

theorem empty_success_and_failure_are_distinct_live_results :
    (resultLabel (Λ := Λ) .success) ≠ resultLabel .failure ∧
      (next caller)^[4]
        (some (cfg (some (phaseLabel .scanPrefix)) regs [true] [] [] [] [] ctx)) =
        some (cfg (some (resultLabel .success)) (reset regs) [] [] [] [] [] ctx) ∧
      (next caller)^[2]
        (some (cfg (some (phaseLabel .scanPrefix)) regs [] [] [] [] [] ctx)) =
        some (cfg (some (resultLabel .failure)) (reset regs) [] [] [] [] [] ctx) := by
  refine ⟨?_, empty_fields_succeed_in_four caller regs ctx, empty_raw_fails_in_two caller regs ctx⟩
  intro impossible
  cases impossible

/-- The delimiter and full certificate tail are actually consumed into two forward outputs. -/
theorem literal_pair_returns_two_forward_outputs :
    (next caller)^[14]
        (some (cfg (some (phaseLabel .scanPrefix)) regs
          [false, true, false, false, true, false, true, true] [] [] [] [] ctx)) =
      some (cfg (some (resultLabel .success)) (reset regs) [] [] []
        [true, false] [false, true, true] ctx) :=
  run_frame caller [true, false] [false, true, true] regs ctx

theorem missing_and_dangling_delimiters_discard_the_actual_prefix :
    (next caller)^[6]
        (some (cfg (some (phaseLabel .scanPrefix)) regs
          [false, true, false, false] [] [] [] [] ctx)) =
        some (cfg (some (resultLabel .failure)) (reset regs) [] [] [] [] [] ctx) ∧
      (next caller)^[6]
        (some (cfg (some (phaseLabel .scanPrefix)) regs
          [false, true, false, false, false] [] [] [] [] ctx)) =
        some (cfg (some (resultLabel .failure)) (reset regs) [] [] [] [] [] ctx) :=
  ⟨scanPrefix_missing_delimiter caller [true, false] [] [] [] [] regs ctx,
    scanPrefix_incomplete_guard caller [true, false] [] [] [] [] regs ctx⟩

/-- Both dirty reverse lists have their own forward output and old suffix. -/
theorem dirty_pair_has_two_distinct_output_orientations :
    (next caller)^[18]
        (some (cfg (some (phaseLabel .scanPrefix)) regs
          [false, true, false, false, true, false, true, true]
          [true, false] [false, true] [false] [true, false] ctx)) =
      some (cfg (some (resultLabel .success)) (reset regs) [] [] []
        [false, true, true, false, false]
        [true, false, false, true, true, true, false] ctx) :=
  scanPrefix_frame caller [true, false] [false, true, true]
    [true, false] [false, true] [false] [true, false] regs ctx

theorem dirty_failure_retains_certificate_reverse_and_old_outputs :
    (next caller)^[8]
        (some (cfg (some (phaseLabel .scanPrefix)) regs
          [false, true, false, false] [true, false] [false, true] [false] [true, false] ctx)) =
        some (cfg (some (resultLabel .failure)) (reset regs) [] []
          [false, true] [false] [true, false] ctx) ∧
      (next caller)^[8]
        (some (cfg (some (phaseLabel .scanPrefix)) regs
          [false, true, false, false, false] [true, false] [false, true] [false] [true, false] ctx)) =
        some (cfg (some (resultLabel .failure)) (reset regs) [] []
          [false, true] [false] [true, false] ctx) :=
  ⟨scanPrefix_missing_delimiter caller [true, false]
      [true, false] [false, true] [false] [true, false] regs ctx,
    scanPrefix_incomplete_guard caller [true, false]
      [true, false] [false, true] [false] [true, false] regs ctx⟩

/-- A dirty certificate accumulator invalidates the ordinary four-step empty-field result. -/
theorem dirty_certificate_reverse_is_really_emitted :
    (next caller)^[6]
        (some (cfg (some (phaseLabel .scanPrefix)) regs [true] [] [false, true] [] [] ctx)) =
      some (cfg (some (resultLabel .success)) (reset regs) [] [] [] [] [true, false] ctx) :=
  scanPrefix_frame caller [] [] [] [false, true] [] [] regs ctx

theorem dirty_certificate_reverse_has_not_returned_at_four :
    ∃ reached,
      (next caller)^[4]
        (some (cfg (some (phaseLabel .scanPrefix)) regs [true] [] [false, true] [] [] ctx)) =
          some reached ∧
      Owned reached.l ∧ remainingSteps reached = 2 := by
  obtain ⟨reached, executed, rank, _, owned, _⟩ :=
    phase_prefix caller .scanPrefix [true] [] [false, true] [] [] regs ctx 4 (by decide)
  exact ⟨reached, executed, owned.mp (by decide), rank⟩

/-- The generic family consumes the actual source result, including arbitrary certificate tails. -/
theorem every_frame_has_its_actual_source_result (first second : Bits) :
    BitPairFraming.unframe (BitPairFraming.frame first second) = some (first, second) ∧
      (next caller)^[2 * first.length + 2 * second.length + 4]
        (some (cfg (some (phaseLabel .scanPrefix)) regs (BitPairFraming.frame first second)
          [] [] [] [] ctx)) =
        some (cfg (some (resultLabel .success)) (reset regs) [] [] [] first second ctx) :=
  ⟨BitPairFraming.unframe_frame first second, run_frame caller first second regs ctx⟩

theorem every_dirty_frame_retains_both_old_suffixes
    (first second firstRev certRev input cert : Bits) :
    (next caller)^[2 * first.length + 2 * second.length + firstRev.length + certRev.length + 4]
        (some (cfg (some (phaseLabel .scanPrefix)) regs (BitPairFraming.frame first second)
          firstRev certRev input cert ctx)) =
      some (cfg (some (resultLabel .success)) (reset regs) [] [] []
        (firstRev.reverse ++ first ++ input) (certRev.reverse ++ second ++ cert) ctx) :=
  scanPrefix_frame caller first second firstRev certRev input cert regs ctx

theorem both_malformed_families_preserve_dirty_reverse_and_outputs
    (pref firstRev certRev input cert : Bits) :
    (next caller)^[2 * pref.length + firstRev.length + 2]
        (some (cfg (some (phaseLabel .scanPrefix)) regs (BitPairFraming.escapeBits pref)
          firstRev certRev input cert ctx)) =
        some (cfg (some (resultLabel .failure)) (reset regs) [] [] certRev input cert ctx) ∧
      (next caller)^[2 * pref.length + firstRev.length + 2]
        (some (cfg (some (phaseLabel .scanPrefix)) regs (BitPairFraming.escapeBits pref ++ [false])
          firstRev certRev input cert ctx)) =
        some (cfg (some (resultLabel .failure)) (reset regs) [] [] certRev input cert ctx) :=
  ⟨scanPrefix_missing_delimiter caller pref firstRev certRev input cert regs ctx,
    scanPrefix_incomplete_guard caller pref firstRev certRev input cert regs ctx⟩

/-- Full data transfer is followed by a real empty probe, not a free result conversion. -/
theorem emit_first_retains_arbitrary_raw_and_certificate_data
    (raw firstRev certRev input cert : Bits) :
    (next caller)^[firstRev.length + 1]
        (some (cfg (some (phaseLabel .emitFirst)) regs raw firstRev certRev input cert ctx)) =
      some (cfg (some (resultLabel .success)) (reset regs) raw [] certRev
        (firstRev.reverse ++ input) cert ctx) :=
  emitFirst_iterate caller raw firstRev certRev input cert regs ctx

theorem certificate_copy_places_dirty_reverse_before_the_actual_tail
    (raw firstRev certRev input cert : Bits) :
    (next caller)^[2 * raw.length + certRev.length + firstRev.length + 3]
        (some (cfg (some (phaseLabel .copyCert)) regs raw firstRev certRev input cert ctx)) =
      some (cfg (some (resultLabel .success)) (reset regs) [] [] []
        (firstRev.reverse ++ input) (certRev.reverse ++ raw ++ cert) ctx) :=
  copyCert_iterate caller raw firstRev certRev input cert regs ctx

/-! Each intermediate prefix preserves the literal unconsumed suffix and both old outputs. -/

theorem escaped_prefix_is_consumed_without_looking_into_the_tail
    (accepted tail firstRev certRev input cert : Bits) :
    (next caller)^[accepted.length]
        (some (cfg (some (phaseLabel .scanPrefix)) regs
          (BitPairFraming.escapeBits accepted ++ tail) firstRev certRev input cert ctx)) =
      some (cfg (some (phaseLabel .scanPrefix)) (if accepted = [] then regs else reset regs)
        tail (accepted.reverse ++ firstRev) certRev input cert ctx) :=
  scanPrefix_prefix caller accepted tail firstRev certRev input cert regs ctx

theorem certificate_copy_prefix_keeps_both_old_output_suffixes
    (accepted tail firstRev certRev input cert : Bits) :
    (next caller)^[accepted.length]
        (some (cfg (some (phaseLabel .copyCert)) regs (accepted ++ tail)
          firstRev certRev input cert ctx)) =
      some (cfg (some (phaseLabel .copyCert)) (if accepted = [] then regs else reset regs)
        tail firstRev (accepted.reverse ++ certRev) input cert ctx) :=
  copyCert_prefix caller accepted tail firstRev certRev input cert regs ctx

theorem certificate_emit_prefix_prepends_its_actual_reverse
    (raw firstRev accepted tail input cert : Bits) :
    (next caller)^[accepted.length]
        (some (cfg (some (phaseLabel .emitCert)) regs raw firstRev (accepted ++ tail) input cert ctx)) =
      some (cfg (some (phaseLabel .emitCert)) (if accepted = [] then regs else reset regs)
        raw firstRev tail input (accepted.reverse ++ cert) ctx) :=
  emitCert_prefix caller raw firstRev accepted tail input cert regs ctx

theorem input_emit_prefix_keeps_the_certificate_literal
    (raw accepted tail certRev input cert : Bits) :
    (next caller)^[accepted.length]
        (some (cfg (some (phaseLabel .emitFirst)) regs raw (accepted ++ tail) certRev input cert ctx)) =
      some (cfg (some (phaseLabel .emitFirst)) (if accepted = [] then regs else reset regs)
        raw tail certRev (accepted.reverse ++ input) cert ctx) :=
  emitFirst_prefix caller raw accepted tail certRev input cert regs ctx

theorem cleanup_prefix_does_not_touch_old_outputs
    (raw accepted tail certRev input cert : Bits) :
    (next caller)^[accepted.length]
        (some (cfg (some (phaseLabel .clearFirst)) regs raw (accepted ++ tail) certRev input cert ctx)) =
      some (cfg (some (phaseLabel .clearFirst)) (if accepted = [] then regs else reset regs)
        raw tail certRev input cert ctx) :=
  clearFirst_prefix caller raw accepted tail certRev input cert regs ctx

/-- A nonpalindromic prefix exposes orientation while all remaining lists stay arbitrary. -/
theorem three_transfer_steps_are_not_the_empty_probe
    (raw tail certRev input cert : Bits) :
    (next caller)^[3]
        (some (cfg (some (phaseLabel .emitFirst)) regs raw
          ([true, false, false] ++ tail) certRev input cert ctx)) =
      some (cfg (some (phaseLabel .emitFirst)) (reset regs)
        raw tail certRev ([false, false, true] ++ input) cert ctx) :=
  emitFirst_prefix caller raw [true, false, false] tail certRev input cert regs ctx

theorem zero_transfer_keeps_the_incoming_temporary
    (raw firstRev certRev input cert : Bits) :
    (next caller)^[0]
        (some (cfg (some (phaseLabel .emitFirst)) regs raw firstRev certRev input cert ctx)) =
      some (cfg (some (phaseLabel .emitFirst)) regs raw firstRev certRev input cert ctx) :=
  emitFirst_prefix caller raw [] firstRev certRev input cert regs ctx

theorem an_empty_transfer_still_resets_on_its_one_probe (raw certRev input cert : Bits) :
    (next caller)^[1]
        (some (cfg (some (phaseLabel .emitFirst)) regs raw [] certRev input cert ctx)) =
      some (cfg (some (resultLabel .success)) (reset regs) raw [] certRev input cert ctx) :=
  emitFirst_iterate caller raw [] certRev input cert regs ctx

/-- The arbitrary dirty-state local law couples actual execution with rank, reset and storage. -/
theorem every_owned_phase_has_a_nonallocating_actual_successor
    (phase : Phase) (raw firstRev certRev input cert : Bits) :
    ∃ reached,
      step caller (cfg (some (phaseLabel phase)) regs raw firstRev certRev input cert ctx) =
        some reached ∧
      phaseSteps phase raw firstRev certRev = remainingSteps reached + 1 ∧
      reached.var = reset regs ∧ (∀ k, reached.stk (.inr k) = ctx k) ∧
      ownedCells reached ≤ raw.length + firstRev.length + certRev.length + input.length + cert.length :=
  phase_step_data caller phase raw firstRev certRev input cert regs ctx

theorem callers_agree_through_every_owned_phase_prefix
    (other : External Λ → Statement Γ Λ R) (phase : Phase)
    (raw firstRev certRev input cert : Bits) (n : Nat)
    (bound : n ≤ phaseSteps phase raw firstRev certRev) :
    (next caller)^[n]
        (some (cfg (some (phaseLabel phase)) regs raw firstRev certRev input cert ctx)) =
      (next other)^[n]
        (some (cfg (some (phaseLabel phase)) regs raw firstRev certRev input cert ctx)) :=
  phase_prefix_caller_independent caller other phase raw firstRev certRev input cert regs ctx n bound

theorem source_recognition_uses_the_first_live_result (raw first second : Bits) :
    (FirstSuccess caller raw first second regs ctx ↔ raw = BitPairFraming.frame first second) ∧
      (FirstFailure caller raw regs ctx ↔ BitPairFraming.unframe raw = none) :=
  ⟨firstSuccess_frame_iff caller raw first second regs ctx,
    firstFailure_iff caller raw regs ctx⟩

theorem every_clean_run_has_no_earlier_caller_transition (raw : Bits) :
    ¬ Owned (scanResult (Λ := Λ) regs [] [] [] [] ctx (BitPairFraming.unframe raw)).l ∧
      ∀ n, n < BitPairFraming.runSteps raw → ∃ reached,
        (next caller)^[n]
          (some (cfg (some (phaseLabel .scanPrefix)) regs raw [] [] [] [] ctx)) = some reached ∧
        Owned reached.l :=
  run_first_return caller raw regs ctx

/-- The continuation premise is actual execution of this same program on its actual dirty result. -/
def dirtyScanThenContinuationTiming (raw firstRev certRev input cert : Bits)
    (finish : Option (Cfg Γ Λ R)) (budget : Nat)
    (continued : StateTransition.EvalsToInTime (step caller)
      (scanResult regs firstRev certRev input cert ctx (BitPairFraming.unframe raw)) finish budget) :
    StateTransition.EvalsToInTime (step caller)
      (cfg (some (phaseLabel .scanPrefix)) regs raw firstRev certRev input cert ctx)
      finish (budget + scanSteps raw firstRev certRev) :=
  StateTransition.EvalsToInTime.trans (step caller) (scanSteps raw firstRev certRev) budget
    (cfg (some (phaseLabel .scanPrefix)) regs raw firstRev certRev input cert ctx)
    (scanResult regs firstRev certRev input cert ctx (BitPairFraming.unframe raw)) finish
    (scanInTime caller raw firstRev certRev input cert regs ctx) continued

theorem installed_ambient_bodies_return_the_actual_source
    (ambient : Label Λ → Statement Γ Λ R)
    (installed : ∀ phase, ambient (phaseLabel phase) = block phase) (raw : Bits) :
    (fun c : Option (Cfg Γ Λ R) => c.bind (Turing.TM2.step ambient))^[BitPairFraming.runSteps raw]
        (some (cfg (some (phaseLabel .scanPrefix)) regs raw [] [] [] [] ctx)) =
      some (scanResult regs [] [] [] [] ctx (BitPairFraming.unframe raw)) :=
  ambient_run_source ambient installed raw regs ctx

variable [Fintype K]

/-- Rank, first return, protected data and physical occupancy concern one actual reached state. -/
theorem arbitrary_raw_inclusive_prefix (raw : Bits) (n : Nat)
    (bound : n ≤ BitPairFraming.runSteps raw) :
    ∃ reached,
      (next caller)^[n]
          (some (cfg (some (phaseLabel .scanPrefix)) regs raw [] [] [] [] ctx)) = some reached ∧
      remainingSteps reached = BitPairFraming.runSteps raw - n ∧
      (n < BitPairFraming.runSteps raw ↔ Owned reached.l) ∧
      (0 < n → reached.var.1 = none) ∧ reached.var.2 = regs.2 ∧
      (∀ k, reached.stk (.inr k) = ctx k) ∧
      stackCells reached ≤ raw.length + contextCells ctx := by
  obtain ⟨reached, executed, rank, path, owned, localRegister⟩ :=
    run_prefix caller raw regs ctx n bound
  obtain ⟨callerRegister, contextEq, _⟩ := local_reaches_preserves caller path
  exact ⟨reached, executed, rank, owned, localRegister, callerRegister, contextEq,
    prefix_stackCells_le caller raw regs ctx n reached bound executed⟩

theorem dirty_phase_prefix_counts_every_old_owned_cell
    (phase : Phase) (raw firstRev certRev input cert : Bits) (n : Nat) (reached : Cfg Γ Λ R)
    (bound : n ≤ phaseSteps phase raw firstRev certRev)
    (executed : (next caller)^[n]
      (some (cfg (some (phaseLabel phase)) regs raw firstRev certRev input cert ctx)) = some reached) :
    stackCells reached ≤ raw.length + firstRev.length + certRev.length + input.length + cert.length +
      contextCells ctx :=
  phase_prefix_stackCells_le caller phase raw firstRev certRev input cert regs ctx n reached bound executed

/-- The initial state itself attains the inclusive bound, even for empty raw input. -/
theorem initial_prefix_attains_the_bound (raw : Bits) :
    (next caller)^[0]
        (some (cfg (some (phaseLabel .scanPrefix)) regs raw [] [] [] [] ctx)) =
        some (cfg (some (phaseLabel .scanPrefix)) regs raw [] [] [] [] ctx) ∧
      stackCells (cfg (Λ := Λ) (some (phaseLabel .scanPrefix)) regs raw [] [] [] [] ctx) =
        raw.length + contextCells ctx :=
  ⟨rfl, initial_stackCells raw regs ctx⟩

end Context

theorem literal_frame_and_malformed_lengths :
    BitPairFraming.frame [true, false] [false, true, true] =
        [false, true, false, false, true, false, true, true] ∧
      (BitPairFraming.frame [true, false] [false, true, true]).length = 8 ∧
      (BitPairFraming.escapeBits [true, false]).length = 4 ∧
      (BitPairFraming.escapeBits [true, false] ++ [false]).length = 5 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Quantifying flag tests both caller values, while the borrowed field starts stale. -/
theorem stale_local_field_preserves_both_caller_values (flag : Bool) :
    (next haltCaller)^[14]
        (some (cfg (some (phaseLabel .scanPrefix)) (staleRegisters flag)
          [false, true, false, false, true, false, true, true] [] [] [] [] sentinelContext)) =
      some (cfg (some (resultLabel .success)) (none, flag) [] [] []
        [true, false] [false, true, true] sentinelContext) :=
  literal_pair_returns_two_forward_outputs haltCaller (staleRegisters flag) sentinelContext

theorem literal_prefixes_retain_two_nonpalindromic_sentinels
    (flag : Bool) (n : Nat) (bound : n ≤ 14) :
    ∃ reached,
      (next haltCaller)^[n]
        (some (cfg (some (phaseLabel .scanPrefix)) (staleRegisters flag)
          [false, true, false, false, true, false, true, true] [] [] [] [] sentinelContext)) =
          some reached ∧
      reached.var.2 = flag ∧ reached.stk (.inr false) = [true, false, false] ∧
      reached.stk (.inr true) = ([15, 6, 1] : Word) ∧ stackCells reached ≤ 14 := by
  obtain ⟨reached, executed, _, _, _, register, contextEq, cells⟩ :=
    arbitrary_raw_inclusive_prefix haltCaller (staleRegisters flag) sentinelContext
      [false, true, false, false, true, false, true, true] n bound
  have contextSize : contextCells sentinelContext = 6 := by decide
  change stackCells reached ≤ 8 + contextCells sentinelContext at cells
  rw [contextSize] at cells
  exact ⟨reached, executed, register, contextEq false, contextEq true, cells⟩

/-- The finite package runs the same open program; it does not assert a halted function result. -/
def finiteMachineUniformTiming (raw : Bits) :
    StateTransition.EvalsToInTime (machine haltCaller true).step
      (Turing.initList (machine haltCaller true) raw)
      (some (scanResult (none, true) [] [] [] [] (smallContext [] []) (BitPairFraming.unframe raw)))
      (2 * raw.length + 2) := by
  have emptyContext : (fun k : Bool => ([] : List (SmallAlphabet k))) = smallContext [] [] := by
    funext k
    cases k <;> rfl
  rw [initList_eq, emptyContext]
  exact runInLinearTime haltCaller raw (none, true) (smallContext [] [])

/-! These callers execute only after the proved first result. -/

def sentinelCaller : External Unit → Statement SmallAlphabet Unit Bool
  | .inl _ => .push (.inr false) (fun _ => true) .halt
  | .inr () => .halt

def literalStart (flag : Bool) (bits : Bits) (tags : Word) : Cfg SmallAlphabet Unit Bool :=
  cfg (some (phaseLabel .scanPrefix)) (staleRegisters flag)
    [false, true, false, false, true, false, true, true] [] [] [] [] (smallContext bits tags)

def literalHandoff (flag : Bool) (bits : Bits) (tags : Word) : Cfg SmallAlphabet Unit Bool :=
  cfg (some (resultLabel .success)) (none, flag) [] [] []
    [true, false] [false, true, true] (smallContext bits tags)

def literalAfterCaller (flag : Bool) (bits : Bits) (tags : Word) : Cfg SmallAlphabet Unit Bool :=
  cfg none (none, flag) [] [] [] [true, false] [false, true, true]
    (smallContext (true :: bits) tags)

theorem sentinel_push_is_one_actual_transition
    (result : Result) (regs : Registers Bool) (input cert bits : Bits) (tags : Word) :
    step sentinelCaller
        (cfg (some (resultLabel result)) regs [] [] [] input cert (smallContext bits tags)) =
      some (cfg none regs [] [] [] input cert (smallContext (true :: bits) tags)) := by
  apply congrArg some
  apply cfg_ext <;> first | rfl | exact fun k => by cases k <;> rfl

theorem sentinel_handoff_is_before_the_actual_push (flag : Bool) (bits : Bits) (tags : Word) :
    (next sentinelCaller)^[14] (some (literalStart flag bits tags)) =
      some (literalHandoff flag bits tags) :=
  literal_pair_returns_two_forward_outputs sentinelCaller (staleRegisters flag) (smallContext bits tags)

def sentinelHandoffInTime (flag : Bool) (bits : Bits) (tags : Word) :
    StateTransition.EvalsToInTime (step sentinelCaller) (literalStart flag bits tags)
      (some (literalHandoff flag bits tags)) 14 :=
  runInTime sentinelCaller [false, true, false, false, true, false, true, true]
    (staleRegisters flag) (smallContext bits tags)

def sentinelCallerInTime (flag : Bool) (bits : Bits) (tags : Word) :
    StateTransition.EvalsToInTime (step sentinelCaller) (literalHandoff flag bits tags)
      (some (literalAfterCaller flag bits tags)) 1 where
  steps := 1
  evals_in_steps := sentinel_push_is_one_actual_transition .success (none, flag)
    [true, false] [false, true, true] bits tags
  steps_le_m := Nat.le_refl _

def sentinelCompositionInTime (flag : Bool) (bits : Bits) (tags : Word) :
    StateTransition.EvalsToInTime (step sentinelCaller) (literalStart flag bits tags)
      (some (literalAfterCaller flag bits tags)) 15 :=
  StateTransition.EvalsToInTime.trans (step sentinelCaller) 14 1
    (literalStart flag bits tags) (literalHandoff flag bits tags)
    (some (literalAfterCaller flag bits tags))
    (sentinelHandoffInTime flag bits tags) (sentinelCallerInTime flag bits tags)

theorem success_handoff_halt_and_outer_none_have_clocks_fourteen_fifteen_sixteen
    (flag : Bool) (bits : Bits) (tags : Word) :
    (next sentinelCaller)^[14] (some (literalStart flag bits tags)) =
        some (literalHandoff flag bits tags) ∧
      (literalHandoff flag bits tags).l = some (resultLabel .success) ∧
      (literalHandoff flag bits tags).stk (.inr false) = bits ∧
      (next sentinelCaller)^[15] (some (literalStart flag bits tags)) =
        some (literalAfterCaller flag bits tags) ∧
      (literalAfterCaller flag bits tags).l = none ∧
      (literalAfterCaller flag bits tags).stk (.inr false) = true :: bits ∧
      (next sentinelCaller)^[16] (some (literalStart flag bits tags)) = none := by
  have completed : (next sentinelCaller)^[15] (some (literalStart flag bits tags)) =
      some (literalAfterCaller flag bits tags) :=
    (sentinelCompositionInTime flag bits tags).evals_in_steps
  refine ⟨sentinel_handoff_is_before_the_actual_push flag bits tags, rfl, rfl,
    completed, rfl, rfl, ?_⟩
  rw [show 16 = 15 + 1 by rfl, Function.iterate_succ_apply', completed]
  rfl

def failureStart (flag : Bool) (bits : Bits) (tags : Word) : Cfg SmallAlphabet Unit Bool :=
  cfg (some (phaseLabel .scanPrefix)) (staleRegisters flag) [] [] [] [] [] (smallContext bits tags)

def failureHandoff (flag : Bool) (bits : Bits) (tags : Word) : Cfg SmallAlphabet Unit Bool :=
  cfg (some (resultLabel .failure)) (none, flag) [] [] [] [] [] (smallContext bits tags)

def failureAfterCaller (flag : Bool) (bits : Bits) (tags : Word) : Cfg SmallAlphabet Unit Bool :=
  cfg none (none, flag) [] [] [] [] [] (smallContext (true :: bits) tags)

theorem failure_handoff_halt_and_outer_none_have_clocks_two_three_four
    (flag : Bool) (bits : Bits) (tags : Word) :
    (next sentinelCaller)^[2] (some (failureStart flag bits tags)) =
        some (failureHandoff flag bits tags) ∧
      (failureHandoff flag bits tags).l = some (resultLabel .failure) ∧
      (failureHandoff flag bits tags).stk (.inr false) = bits ∧
      (next sentinelCaller)^[3] (some (failureStart flag bits tags)) =
        some (failureAfterCaller flag bits tags) ∧
      (failureAfterCaller flag bits tags).l = none ∧
      (next sentinelCaller)^[4] (some (failureStart flag bits tags)) = none := by
  have first : (next sentinelCaller)^[2] (some (failureStart flag bits tags)) =
      some (failureHandoff flag bits tags) :=
    empty_raw_fails_in_two sentinelCaller (staleRegisters flag) (smallContext bits tags)
  have after : (next sentinelCaller)^[3] (some (failureStart flag bits tags)) =
      some (failureAfterCaller flag bits tags) := by
    rw [show 3 = 2 + 1 by rfl, Function.iterate_succ_apply', first, next_some]
    exact sentinel_push_is_one_actual_transition .failure (none, flag) [] [] bits tags
  refine ⟨first, rfl, rfl, after, rfl, ?_⟩
  rw [show 4 = 3 + 1 by rfl, Function.iterate_succ_apply', after]
  rfl

theorem distinct_callers_have_the_same_inclusive_framing_prefix
    (flag : Bool) (bits : Bits) (tags : Word) (n : Nat) (bound : n ≤ 14) :
    (next sentinelCaller)^[n] (some (literalStart flag bits tags)) =
      (next haltCaller)^[n] (some (literalStart flag bits tags)) :=
  phase_prefix_caller_independent sentinelCaller haltCaller .scanPrefix
    [false, true, false, false, true, false, true, true] [] [] [] []
    (staleRegisters flag) (smallContext bits tags) n bound

theorem distinct_callers_change_the_next_actual_transition
    (flag : Bool) (bits : Bits) (tags : Word) :
    step sentinelCaller (literalHandoff flag bits tags) ≠
      step haltCaller (literalHandoff flag bits tags) := by
  intro equal
  have contents := congrArg
    (fun state : Option (Cfg SmallAlphabet Unit Bool) => state.map (fun c => c.stk (.inr false))) equal
  change some (true :: bits) = some bits at contents
  have lengths := congrArg List.length (Option.some.inj contents)
  simp at lengths

/-- This fixed external body can allocate indefinitely only after ownership ends. -/
def allocatingCaller : External Unit → Statement SmallAlphabet Unit Bool
  | .inl .failure => .push (.inr false) (fun _ => true) (jump (resultLabel .failure))
  | _ => .halt

def emptyStart : Cfg SmallAlphabet Unit Bool := failureStart true [] []

def allocatingState (count : Nat) : Cfg SmallAlphabet Unit Bool :=
  cfg (some (resultLabel .failure)) (none, true) [] [] [] [] []
    (smallContext (List.replicate count true) [])

theorem allocating_caller_step (count : Nat) :
    step allocatingCaller (allocatingState count) = some (allocatingState (count + 1)) := by
  apply congrArg some
  apply cfg_ext <;> first | rfl | exact fun k => by cases k <;> rfl

theorem allocating_caller_runs_after_the_first_failure (count : Nat) :
    (next allocatingCaller)^[2 + count] (some emptyStart) = some (allocatingState count) := by
  induction count with
  | zero => exact empty_raw_fails_in_two allocatingCaller (staleRegisters true) (smallContext [] [])
  | succ count ih =>
      rw [Nat.add_succ, Function.iterate_succ_apply', ih, next_some, allocating_caller_step]

theorem post_return_allocation_exceeds_the_zero_cell_entry_bound :
    (next allocatingCaller)^[2] (some emptyStart) = some (allocatingState 0) ∧
      (next allocatingCaller)^[3] (some emptyStart) = some (allocatingState 1) ∧
      stackCells emptyStart = 0 ∧ stackCells (allocatingState 1) = 1 ∧
      ¬ stackCells (allocatingState 1) ≤ ([] : Bits).length + contextCells (smallContext [] []) := by
  refine ⟨allocating_caller_runs_after_the_first_failure 0,
    allocating_caller_runs_after_the_first_failure 1, ?_, ?_, ?_⟩ <;> decide

/-- A caller can manufacture a later success and reenter with nonempty output stacks. -/
def misleadingCaller : External Unit → Statement SmallAlphabet Unit Bool
  | .inl .failure => .push (.inl .inputBits) (fun _ => true)
      (.push (.inl .certificateBits) (fun _ => false) (jump (resultLabel .success)))
  | .inl .success => jump (phaseLabel .scanPrefix)
  | .inr () => .halt

def misleadingSuccess : Cfg SmallAlphabet Unit Bool :=
  cfg (some (resultLabel .success)) (none, true) [] [] [] [true] [false] (smallContext [] [])

def misleadingReentry : Cfg SmallAlphabet Unit Bool :=
  cfg (some (phaseLabel .scanPrefix)) (none, true) [] [] [] [true] [false] (smallContext [] [])

theorem one_caller_step_can_manufacture_success :
    step misleadingCaller (allocatingState 0) = some misleadingSuccess := by
  apply congrArg some
  apply cfg_ext <;> first | rfl | exact fun k => by cases k <;> rfl

theorem later_success_is_not_the_source_connected_first_success :
    (next misleadingCaller)^[2] (some emptyStart) = some (allocatingState 0) ∧
      (next misleadingCaller)^[3] (some emptyStart) = some misleadingSuccess ∧
      (next misleadingCaller)^[4] (some emptyStart) = some misleadingReentry ∧
      ¬ FirstSuccess misleadingCaller [] [true] [false] (staleRegisters true) (smallContext [] []) := by
  have first : (next misleadingCaller)^[2] (some emptyStart) = some (allocatingState 0) :=
    empty_raw_fails_in_two misleadingCaller (staleRegisters true) (smallContext [] [])
  have later : (next misleadingCaller)^[3] (some emptyStart) = some misleadingSuccess := by
    rw [show 3 = 2 + 1 by rfl, Function.iterate_succ_apply', first, next_some,
      one_caller_step_can_manufacture_success]
  refine ⟨first, later, ?_, ?_⟩
  · rw [show 4 = 3 + 1 by rfl, Function.iterate_succ_apply', later]
    rfl
  · intro claimed
    have impossible := (firstSuccess_iff misleadingCaller [] [true] [false]
      (staleRegisters true) (smallContext [] [])).mp claimed
    cases impossible

end Examples.RotationCertificateOpenFramingMachine
