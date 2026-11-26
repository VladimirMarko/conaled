import Applications.Resources.RotationCertificate.OpenDecoderMachine

/-!
# Connected executions of the open four-bit decoder

The code words, dirty accumulator orientations, physical stores and clocks in
these cases were fixed before their implementation. The executions consume the
public phase, source, rank, prefix, finite-package and timed interfaces. Live
return, actual caller execution, a present halted configuration and outer
`none` are different observations of this one installed program.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.RotationCertificateOpenDecoderMachine
open Resources.BinaryCounter (Bits)
open Resources.RotationCertificate
open OpenDecoderMachine

/-- Two protected stacks have different finite alphabets. -/
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

/-- All five borrowed fields are occupied; the Boolean observations differ. -/
def staleRegisters (flag : Bool) : Registers Bool :=
  (⟨some true, some false, some false, some true, some 9⟩, flag)

def haltCaller : External Unit → Statement SmallAlphabet Unit Bool := fun _ => .halt

/-- Cardinalities refer to the actual register type and actual sum-index families. -/
theorem concrete_control_and_register_counts :
    Fintype.card (StackId Bool) = 5 ∧ Fintype.card (Label Unit) = 6 ∧
      Fintype.card (Registers Bool) = 2754 := by
  refine ⟨?_, ?_, ?_⟩
  · simpa using (card_stackId (K := Bool))
  · simpa using (card_label (Λ := Unit))
  · simpa using (card_registers (R := Bool))

theorem actual_borrowed_register_cardinality :
    Fintype.card Temporaries = 1377 ∧ Fintype.card Temporaries = 3 ^ 4 * 17 :=
  ⟨card_temporaries, card_temporaries⟩

section Context
variable {K Λ R : Type} [DecidableEq K] {Γ : K → Type}
variable (caller : External Λ → Statement Γ Λ R)
variable (regs : Registers R) (ctx : ∀ k, List (Γ k))

/-- The scan empty probe and emit empty probe are both actual transitions. -/
theorem empty_raw_succeeds_in_two :
    (next caller)^[2] (some (cfg (some (phaseLabel .scan)) regs [] [] [] ctx)) =
      some (cfg (some (resultLabel .success)) (reset regs) [] [] [] ctx) :=
  run_code caller [] regs ctx

/-- Arbitrary bits cover every one-bit partial input, including a true bit. -/
theorem one_bit_fails_in_two (b0 : Bool) :
    (next caller)^[2] (some (cfg (some (phaseLabel .scan)) regs [b0] [] [] ctx)) =
      some (cfg (some (resultLabel .failure)) (reset regs) [] [] [] ctx) :=
  run_partial caller [] [b0] regs ctx (by simp) (by simp)

theorem two_bits_fail_in_two (b0 b1 : Bool) :
    (next caller)^[2] (some (cfg (some (phaseLabel .scan)) regs [b0, b1] [] [] ctx)) =
      some (cfg (some (resultLabel .failure)) (reset regs) [] [] [] ctx) :=
  run_partial caller [] [b0, b1] regs ctx (by simp) (by simp)

theorem three_bits_fail_in_two (b0 b1 b2 : Bool) :
    (next caller)^[2]
        (some (cfg (some (phaseLabel .scan)) regs [b0, b1, b2] [] [] ctx)) =
      some (cfg (some (resultLabel .failure)) (reset regs) [] [] [] ctx) :=
  run_partial caller [] [b0, b1, b2] regs ctx (by simp) (by simp)

theorem every_nonempty_short_input_fails_in_two (short : Bits)
    (positive : 0 < short.length) (incomplete : short.length < 4) :
    (next caller)^[2] (some (cfg (some (phaseLabel .scan)) regs short [] [] ctx)) =
      some (cfg (some (resultLabel .failure)) (reset regs) [] [] [] ctx) :=
  run_partial caller [] short regs ctx positive incomplete

theorem empty_success_and_short_failure_have_distinct_live_labels :
    (resultLabel (Λ := Λ) .success) ≠ resultLabel .failure ∧
      (next caller)^[2] (some (cfg (some (phaseLabel .scan)) regs [] [] [] ctx)) =
        some (cfg (some (resultLabel .success)) (reset regs) [] [] [] ctx) ∧
      (next caller)^[2] (some (cfg (some (phaseLabel .scan)) regs [true] [] [] ctx)) =
        some (cfg (some (resultLabel .failure)) (reset regs) [] [] [] ctx) := by
  refine ⟨?_, empty_raw_succeeds_in_two caller regs ctx, one_bit_fails_in_two caller regs ctx true⟩
  intro impossible
  cases impossible

/-- This universally quantified finite Tag covers all sixteen actual four-bit codes. -/
theorem all_sixteen_tags_return_in_four (tag : Tag) :
    (next caller)^[4] (some (cfg (some (phaseLabel .scan)) regs (tagBits tag) [] [] ctx)) =
      some (cfg (some (resultLabel .success)) (reset regs) [] [] [tag] ctx) := by
  simpa only [wordBits_cons, wordBits_nil, List.append_nil, List.length_singleton] using
    run_code caller [tag] regs ctx

theorem nonpalindromic_bit_order_distinguishes_three_and_twelve :
    (next caller)^[4]
        (some (cfg (some (phaseLabel .scan)) regs [true, true, false, false] [] [] ctx)) =
        some (cfg (some (resultLabel .success)) (reset regs) [] [] [3] ctx) ∧
      (next caller)^[4]
        (some (cfg (some (phaseLabel .scan)) regs [false, false, true, true] [] [] ctx)) =
        some (cfg (some (resultLabel .success)) (reset regs) [] [] [12] ctx) :=
  ⟨all_sixteen_tags_return_in_four caller regs ctx 3,
    all_sixteen_tags_return_in_four caller regs ctx 12⟩

/-- Reserved grammar tags remain legitimate four-bit codec values. -/
theorem reserved_fifteen_decodes_successfully :
    (next caller)^[4]
        (some (cfg (some (phaseLabel .scan)) regs [true, true, true, true] [] [] ctx)) =
      some (cfg (some (resultLabel .success)) (reset regs) [] [] [15] ctx) :=
  all_sixteen_tags_return_in_four caller regs ctx 15

theorem two_tags_return_in_forward_order_in_six :
    (next caller)^[6]
        (some (cfg (some (phaseLabel .scan)) regs (wordBits [3, 12]) [] [] ctx)) =
      some (cfg (some (resultLabel .success)) (reset regs) [] [] [3, 12] ctx) :=
  run_code caller [3, 12] regs ctx

theorem two_nonpalindromic_partial_suffixes_fail_in_six :
    (next caller)^[6]
        (some (cfg (some (phaseLabel .scan)) regs
          (wordBits [3, 12] ++ [true, false]) [] [] ctx)) =
        some (cfg (some (resultLabel .failure)) (reset regs) [] [] [] ctx) ∧
      (next caller)^[6]
        (some (cfg (some (phaseLabel .scan)) regs
          (wordBits [3, 12] ++ [false, true, true]) [] [] ctx)) =
        some (cfg (some (resultLabel .failure)) (reset regs) [] [] [] ctx) :=
  ⟨run_partial caller [3, 12] [true, false] regs ctx (by decide) (by decide),
    run_partial caller [3, 12] [false, true, true] regs ctx (by decide) (by decide)⟩

theorem dirty_success_places_reversed_old_cells_before_the_forward_word :
    (next caller)^[8]
        (some (cfg (some (phaseLabel .scan)) regs (wordBits [3, 12]) [5, 9] [15, 2] ctx)) =
      some (cfg (some (resultLabel .success)) (reset regs) [] [] [9, 5, 3, 12, 15, 2] ctx) :=
  scan_code caller [3, 12] [5, 9] [15, 2] regs ctx

theorem dirty_partial_failure_clears_reverse_and_retains_old_output :
    (next caller)^[8]
        (some (cfg (some (phaseLabel .scan)) regs
          (wordBits [3, 12] ++ [true, false]) [5, 9] [15, 2] ctx)) =
        some (cfg (some (resultLabel .failure)) (reset regs) [] [] [15, 2] ctx) ∧
      (next caller)^[8]
        (some (cfg (some (phaseLabel .scan)) regs
          (wordBits [3, 12] ++ [false, true, true]) [5, 9] [15, 2] ctx)) =
        some (cfg (some (resultLabel .failure)) (reset regs) [] [] [15, 2] ctx) :=
  ⟨scan_partial caller [3, 12] [5, 9] [15, 2] [true, false] regs ctx (by decide) (by decide),
    scan_partial caller [3, 12] [5, 9] [15, 2] [false, true, true] regs ctx
      (by decide) (by decide)⟩

/-- A nonempty dirty reverse stack invalidates the ordinary six-step handoff. -/
theorem dirty_success_is_still_owned_at_six :
    ∃ reached,
      (next caller)^[6]
        (some (cfg (some (phaseLabel .scan)) regs (wordBits [3, 12]) [5, 9] [15, 2] ctx)) =
          some reached ∧ Owned reached.l ∧ remainingSteps reached = 2 := by
  obtain ⟨reached, executed, rank, _, owned, _⟩ :=
    phase_prefix caller .scan (wordBits [3, 12]) [5, 9] [15, 2] regs ctx 6 (by decide)
  exact ⟨reached, executed, owned.mp (by decide), rank⟩

/-- Input bits and old output survive direct entry into either transfer phase. -/
theorem direct_dirty_emit_and_clear_have_three_steps (raw : Bits) :
    (next caller)^[3]
        (some (cfg (some (phaseLabel .emit)) regs raw [5, 9] [15, 2] ctx)) =
        some (cfg (some (resultLabel .success)) (reset regs) raw [] [9, 5, 15, 2] ctx) ∧
      (next caller)^[3]
        (some (cfg (some (phaseLabel .clear)) regs raw [5, 9] [15, 2] ctx)) =
        some (cfg (some (resultLabel .failure)) (reset regs) raw [] [15, 2] ctx) :=
  ⟨emit_iterate caller [5, 9] raw [15, 2] regs ctx,
    clear_iterate caller [5, 9] raw [15, 2] regs ctx⟩

theorem literal_scan_prefix_accumulates_actual_reverse_tags :
    (next caller)^[2]
        (some (cfg (some (phaseLabel .scan)) regs
          (wordBits [3, 12] ++ [true, false]) [5, 9] [15, 2] ctx)) =
      some (cfg (some (phaseLabel .scan)) (reset regs)
        [true, false] [12, 3, 5, 9] [15, 2] ctx) :=
  scan_prefix caller [3, 12] [true, false] [5, 9] [15, 2] regs ctx

theorem literal_transfer_prefixes_keep_the_unvisited_tail :
    (next caller)^[2]
        (some (cfg (some (phaseLabel .emit)) regs [true, false] [5, 9, 7] [15, 2] ctx)) =
        some (cfg (some (phaseLabel .emit)) (reset regs) [true, false] [7] [9, 5, 15, 2] ctx) ∧
      (next caller)^[2]
        (some (cfg (some (phaseLabel .clear)) regs [true, false] [5, 9, 7] [15, 2] ctx)) =
        some (cfg (some (phaseLabel .clear)) (reset regs) [true, false] [7] [15, 2] ctx) :=
  ⟨emit_prefix caller [5, 9] [7] [true, false] [15, 2] regs ctx,
    clear_prefix caller [5, 9] [7] [true, false] [15, 2] regs ctx⟩

theorem arbitrary_scan_prefix (headWord : Word) (raw : Bits) (rev out : Word) :
    (next caller)^[headWord.length]
        (some (cfg (some (phaseLabel .scan)) regs (wordBits headWord ++ raw) rev out ctx)) =
      some (cfg (some (phaseLabel .scan)) (prefixRegisters headWord.length regs)
        raw (headWord.reverse ++ rev) out ctx) :=
  scan_prefix caller headWord raw rev out regs ctx

theorem arbitrary_transfer_prefixes (headWord tail : Word) (raw : Bits) (out : Word) :
    (next caller)^[headWord.length]
        (some (cfg (some (phaseLabel .emit)) regs raw (headWord ++ tail) out ctx)) =
        some (cfg (some (phaseLabel .emit)) (prefixRegisters headWord.length regs)
          raw tail (headWord.reverse ++ out) ctx) ∧
      (next caller)^[headWord.length]
        (some (cfg (some (phaseLabel .clear)) regs raw (headWord ++ tail) out ctx)) =
        some (cfg (some (phaseLabel .clear)) (prefixRegisters headWord.length regs)
          raw tail out ctx) :=
  ⟨emit_prefix caller headWord tail raw out regs ctx,
    clear_prefix caller headWord tail raw out regs ctx⟩

/-- Zero transfers cannot be used to assert a reset of arbitrary incoming observations. -/
theorem zero_transfer_prefix_retains_all_incoming_registers (raw : Bits) (rev out : Word) :
    (next caller)^[0] (some (cfg (some (phaseLabel .emit)) regs raw rev out ctx)) =
        some (cfg (some (phaseLabel .emit)) regs raw rev out ctx) ∧
      prefixRegisters 0 regs = regs :=
  ⟨emit_prefix caller [] rev raw out regs ctx, prefixRegisters_zero regs⟩

/-- Successful source work and actual machine transitions are separate quantities. -/
theorem every_word_source_and_execution (word : Word) :
    unpackWordRun (wordBits word) = (some word, 4 * word.length + 2) ∧
      (wordBits word).length = 4 * word.length ∧
      (next caller)^[2 * word.length + 2]
        (some (cfg (some (phaseLabel .scan)) regs (wordBits word) [] [] ctx)) =
        some (cfg (some (resultLabel .success)) (reset regs) [] [] word ctx) :=
  ⟨unpackWordRun_code word, wordBits_length word, run_code caller word regs ctx⟩

theorem every_partial_word_source_and_execution (word : Word) (short : Bits)
    (positive : 0 < short.length) (incomplete : short.length < 4) :
    unpackWordRun (wordBits word ++ short) = (none, 2 * word.length + 2) ∧
      (wordBits word ++ short).length = 4 * word.length + short.length ∧
      (next caller)^[2 * word.length + 2]
        (some (cfg (some (phaseLabel .scan)) regs (wordBits word ++ short) [] [] ctx)) =
        some (cfg (some (resultLabel .failure)) (reset regs) [] [] [] ctx) := by
  refine ⟨unpackWordRun_partial word short positive incomplete, ?_,
    run_partial caller word short regs ctx positive incomplete⟩
  rw [List.length_append, wordBits_length]

theorem every_dirty_source_endpoint (raw : Bits) (rev out : Word) :
    (next caller)^[runSteps raw + rev.length]
        (some (cfg (some (phaseLabel .scan)) regs raw rev out ctx)) =
      some (resultCfg (unpackWordRun raw).1 rev out regs ctx) :=
  scan_iterate caller raw rev out regs ctx

theorem every_dirty_success_endpoint (raw : Bits) (word rev out : Word)
    (decoded : (unpackWordRun raw).1 = some word) :
    (next caller)^[runSteps raw + rev.length]
        (some (cfg (some (phaseLabel .scan)) regs raw rev out ctx)) =
      some (cfg (some (resultLabel .success)) (reset regs) [] []
        (rev.reverse ++ word ++ out) ctx) :=
  scan_of_some caller raw word rev out regs ctx decoded

theorem every_dirty_failure_endpoint (raw : Bits) (rev out : Word)
    (decoded : (unpackWordRun raw).1 = none) :
    (next caller)^[runSteps raw + rev.length]
        (some (cfg (some (phaseLabel .scan)) regs raw rev out ctx)) =
      some (cfg (some (resultLabel .failure)) (reset regs) [] [] out ctx) :=
  scan_of_none caller raw rev out regs ctx decoded

theorem exact_first_success_is_the_actual_source_result (raw : Bits) (word : Word) :
    FirstSuccess caller raw word regs ctx ↔ (unpackWordRun raw).1 = some word :=
  firstSuccess_iff caller raw word regs ctx

theorem exact_first_success_is_the_exact_code (raw : Bits) (word : Word) :
    FirstSuccess caller raw word regs ctx ↔ raw = wordBits word :=
  firstSuccess_code_iff caller raw word regs ctx

theorem exact_first_failure_is_the_actual_partial_block (raw : Bits) :
    FirstFailure caller raw regs ctx ↔ raw.length % 4 ≠ 0 :=
  firstFailure_length_iff caller raw regs ctx

theorem every_partial_word_is_a_first_failure (word : Word) (short : Bits)
    (positive : 0 < short.length) (incomplete : short.length < 4) :
    FirstFailure caller (wordBits word ++ short) regs ctx :=
  (firstFailure_iff caller (wordBits word ++ short) regs ctx).mpr
    (congrArg Prod.fst (unpackWordRun_partial word short positive incomplete))

/-- An actual arbitrary program with the same owned blocks has the same dirty endpoint. -/
theorem installed_program_source_endpoint (ambient : Label Λ → Statement Γ Λ R)
    (agrees : ∀ phase, ambient (phaseLabel phase) = block phase)
    (raw : Bits) (rev out : Word) :
    (fun c : Option (Cfg Γ Λ R) => c.bind (Turing.TM2.step ambient))^[runSteps raw + rev.length]
        (some (cfg (some (phaseLabel .scan)) regs raw rev out ctx)) =
      some (resultCfg (unpackWordRun raw).1 rev out regs ctx) :=
  ambient_scan_iterate ambient agrees raw rev out regs ctx

def dirtyScanTiming (raw : Bits) (rev out : Word) :
    StateTransition.EvalsToInTime (step caller)
      (cfg (some (phaseLabel .scan)) regs raw rev out ctx)
      (some (resultCfg (unpackWordRun raw).1 rev out regs ctx)) (runSteps raw + rev.length) :=
  scanInTime caller raw rev out regs ctx

def cleanScanExactTiming (raw : Bits) :
    StateTransition.EvalsToInTime (step caller)
      (cfg (some (phaseLabel .scan)) regs raw [] [] ctx)
      (some (resultCfg (unpackWordRun raw).1 [] [] regs ctx)) (runSteps raw) :=
  runInTimeExact caller raw regs ctx

def rawLinearTiming (raw : Bits) :
    StateTransition.EvalsToInTime (step caller)
      (cfg (some (phaseLabel .scan)) regs raw [] [] ctx)
      (some (resultCfg (unpackWordRun raw).1 [] [] regs ctx)) (raw.length + 2) :=
  runInLinearTime caller raw regs ctx

def dirtyEmitTiming (raw : Bits) (rev out : Word) :
    StateTransition.EvalsToInTime (step caller)
      (cfg (some (phaseLabel .emit)) regs raw rev out ctx)
      (some (cfg (some (resultLabel .success)) (reset regs) raw [] (rev.reverse ++ out) ctx))
      (rev.length + 1) :=
  emitInTime caller rev raw out regs ctx

def dirtyClearTiming (raw : Bits) (rev out : Word) :
    StateTransition.EvalsToInTime (step caller)
      (cfg (some (phaseLabel .clear)) regs raw rev out ctx)
      (some (cfg (some (resultLabel .failure)) (reset regs) raw [] out ctx)) (rev.length + 1) :=
  clearInTime caller rev raw out regs ctx

theorem arbitrary_owned_state_has_exact_progress (start : Cfg Γ Λ R)
    (owned : Owned start.l) :
    ∃ reached, step caller start = some reached ∧ remainingSteps start = remainingSteps reached + 1 :=
  local_progress caller start ((remainingSteps_pos_iff start).mpr owned)

theorem arbitrary_owned_step_resets_and_preserves_frame {before after : Cfg Γ Λ R}
    (executed : LocalStep caller before after) :
    remainingSteps before = remainingSteps after + 1 ∧
      after.var.1 = BitDecoderMachine.zeroRegisters ∧ after.var.2 = before.var.2 ∧
      ownedCells after ≤ ownedCells before ∧
      ∀ k, after.stk (.inr k) = before.stk (.inr k) :=
  local_step_data caller executed

theorem arbitrary_owned_prefix_has_exact_rank_and_protected_frame
    (start : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start) :
    ∃ reached,
      (next caller)^[n] (some start) = some reached ∧
      remainingSteps reached = remainingSteps start - n ∧
      (n < remainingSteps start ↔ Owned reached.l) ∧
      (0 < n → reached.var.1 = BitDecoderMachine.zeroRegisters) ∧
      reached.var.2 = start.var.2 ∧ ∀ k, reached.stk (.inr k) = start.stk (.inr k) := by
  obtain ⟨reached, executed, rank, path, owned, canonical⟩ := owned_prefix caller start n bound
  obtain ⟨register, contextEq⟩ := local_reaches_frame caller path
  exact ⟨reached, executed, rank, owned, canonical, register, contextEq⟩

theorem every_phase_returns_first_at_its_exact_rank (phase : Phase) (raw : Bits) (rev out : Word) :
    ∃ reached,
      (next caller)^[phaseSteps phase raw rev]
          (some (cfg (some (phaseLabel phase)) regs raw rev out ctx)) = some reached ∧
      ¬ Owned reached.l ∧
      ∀ n, n < phaseSteps phase raw rev →
        ∃ before, (next caller)^[n]
          (some (cfg (some (phaseLabel phase)) regs raw rev out ctx)) = some before ∧ Owned before.l :=
  first_return caller phase raw rev out regs ctx

theorem every_owned_prefix_is_independent_of_caller_code
    (other : External Λ → Statement Γ Λ R) (phase : Phase) (raw : Bits) (rev out : Word)
    (n : Nat) (bound : n ≤ phaseSteps phase raw rev) :
    (next caller)^[n] (some (cfg (some (phaseLabel phase)) regs raw rev out ctx)) =
      (next other)^[n] (some (cfg (some (phaseLabel phase)) regs raw rev out ctx)) :=
  phase_prefix_caller_independent caller other phase raw rev out regs ctx n bound

variable [Fintype K]

theorem arbitrary_raw_inclusive_prefix (raw : Bits) (n : Nat) (bound : n ≤ runSteps raw) :
    ∃ reached,
      (next caller)^[n] (some (cfg (some (phaseLabel .scan)) regs raw [] [] ctx)) = some reached ∧
      remainingSteps reached = runSteps raw - n ∧
      (n < runSteps raw ↔ Owned reached.l) ∧
      (0 < n → reached.var.1 = BitDecoderMachine.zeroRegisters) ∧
      reached.var.2 = regs.2 ∧ (∀ k, reached.stk (.inr k) = ctx k) ∧
      stackCells reached ≤ raw.length + contextCells ctx := by
  obtain ⟨reached, executed, rank, path, owned, canonical⟩ :=
    phase_prefix caller .scan raw [] [] regs ctx n bound
  obtain ⟨register, contextEq, cells⟩ := local_reaches_preserves caller path
  exact ⟨reached, executed, rank, owned, canonical, register, contextEq, cells⟩

theorem arbitrary_dirty_prefix_includes_all_old_cells (phase : Phase) (raw : Bits) (rev out : Word)
    (n : Nat) (reached : Cfg Γ Λ R) (bound : n ≤ phaseSteps phase raw rev)
    (executed : (next caller)^[n]
      (some (cfg (some (phaseLabel phase)) regs raw rev out ctx)) = some reached) :
    reached.var.2 = regs.2 ∧ (∀ k, reached.stk (.inr k) = ctx k) ∧
      stackCells reached ≤ raw.length + rev.length + out.length + contextCells ctx :=
  prefix_preserves caller (cfg (some (phaseLabel phase)) regs raw rev out ctx)
    reached n bound executed

end Context

/-- These lengths and source tariffs are different from the actual six-step decoder clock. -/
theorem literal_lengths_and_source_tariffs :
    wordBits [3, 12] = [true, true, false, false, false, false, true, true] ∧
      (wordBits [3, 12]).length = 8 ∧
      (wordBits [3, 12] ++ [true, false]).length = 10 ∧
      (wordBits [3, 12] ++ [false, true, true]).length = 11 ∧
      unpackWordRun (wordBits [3, 12]) = (some [3, 12], 10) ∧
      unpackWordRun (wordBits [3, 12] ++ [true, false]) = (none, 6) ∧
      runSteps (wordBits [3, 12]) = 6 ∧
      runSteps (wordBits [3, 12] ++ [true, false]) = 6 :=
  ⟨rfl, rfl, rfl, rfl, unpackWordRun_code [3, 12],
    unpackWordRun_partial [3, 12] [true, false] (by decide) (by decide), rfl, rfl⟩

theorem explicit_rank_formulas (regs : Registers Bool) (raw : Bits) (rev out : Word)
    (ctx : ∀ k, List (SmallAlphabet k)) :
    remainingSteps (cfg (Λ := Unit) (some (phaseLabel .scan)) regs raw rev out ctx) =
        2 * (raw.length / 4) + rev.length + 2 ∧
      remainingSteps (cfg (Λ := Unit) (some (phaseLabel .emit)) regs raw rev out ctx) = rev.length + 1 ∧
      remainingSteps (cfg (Λ := Unit) (some (phaseLabel .clear)) regs raw rev out ctx) = rev.length + 1 := by
  refine ⟨?_, rfl, rfl⟩
  dsimp [remainingSteps, phaseSteps, cfg, phaseLabel, runSteps]
  omega

theorem all_nonowned_labels_have_zero_rank (regs : Registers Bool) (raw : Bits) (rev out : Word)
    (ctx : ∀ k, List (SmallAlphabet k)) :
    remainingSteps (cfg (Λ := Unit) (some (resultLabel .success)) regs raw rev out ctx) = 0 ∧
      remainingSteps (cfg (Λ := Unit) (some (resultLabel .failure)) regs raw rev out ctx) = 0 ∧
      remainingSteps (cfg (some (callerLabel ())) regs raw rev out ctx) = 0 ∧
      remainingSteps (cfg (Λ := Unit) none regs raw rev out ctx) = 0 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Both protected caller values survive stale observations in all five local fields. -/
theorem stale_fields_are_overwritten_before_use (flag : Bool) :
    (next haltCaller)^[6]
        (some (cfg (some (phaseLabel .scan)) (staleRegisters flag)
          (wordBits [3, 12]) [] [] sentinelContext)) =
      some (cfg (some (resultLabel .success)) (BitDecoderMachine.zeroRegisters, flag)
        [] [] [3, 12] sentinelContext) :=
  two_tags_return_in_forward_order_in_six haltCaller (staleRegisters flag) sentinelContext

theorem stale_fields_and_dirty_stacks_have_the_literal_endpoint (flag : Bool) :
    (next haltCaller)^[8]
        (some (cfg (some (phaseLabel .scan)) (staleRegisters flag)
          (wordBits [3, 12]) [5, 9] [15, 2] sentinelContext)) =
      some (cfg (some (resultLabel .success)) (BitDecoderMachine.zeroRegisters, flag)
        [] [] [9, 5, 3, 12, 15, 2] sentinelContext) :=
  dirty_success_places_reversed_old_cells_before_the_forward_word
    haltCaller (staleRegisters flag) sentinelContext

theorem literal_prefixes_reset_locals_and_retain_both_sentinels
    (flag : Bool) (n : Nat) (bound : n ≤ 6) :
    ∃ reached,
      (next haltCaller)^[n]
        (some (cfg (some (phaseLabel .scan)) (staleRegisters flag)
          (wordBits [3, 12]) [] [] sentinelContext)) = some reached ∧
      (0 < n → reached.var.1 = BitDecoderMachine.zeroRegisters) ∧
      reached.var.2 = flag ∧ reached.stk (.inr false) = [true, false, false] ∧
      reached.stk (.inr true) = ([15, 6, 1] : Word) ∧ stackCells reached ≤ 14 := by
  obtain ⟨reached, executed, _, _, canonical, register, contextEq, cells⟩ :=
    arbitrary_raw_inclusive_prefix haltCaller (staleRegisters flag) sentinelContext (wordBits [3, 12])
      n bound
  have contextSize : contextCells sentinelContext = 6 := by decide
  change stackCells reached ≤ 8 + contextCells sentinelContext at cells
  rw [contextSize] at cells
  exact ⟨reached, executed, canonical, register, contextEq false, contextEq true, cells⟩

theorem zero_prefix_is_really_stale (flag : Bool) :
    (next haltCaller)^[0]
        (some (cfg (some (phaseLabel .scan)) (staleRegisters flag)
          (wordBits [3, 12]) [] [] sentinelContext)) =
        some (cfg (some (phaseLabel .scan)) (staleRegisters flag)
          (wordBits [3, 12]) [] [] sentinelContext) ∧
      (staleRegisters flag).1 ≠ BitDecoderMachine.zeroRegisters := by
  refine ⟨rfl, ?_⟩
  intro equal
  have first := congrArg BitDecoderMachine.Registers.b0 equal
  cases first

/-- A concrete finite program is selected before its input. It still returns live labels. -/
def fixedFiniteMachine : Turing.FinTM2 := machine haltCaller true

theorem fixed_finite_package_has_the_actual_carriers :
    @Fintype.card fixedFiniteMachine.K fixedFiniteMachine.kFin = 5 ∧
      @Fintype.card fixedFiniteMachine.Λ fixedFiniteMachine.ΛFin = 6 ∧
      @Fintype.card fixedFiniteMachine.σ fixedFiniteMachine.σFin = 2754 :=
  concrete_control_and_register_counts

theorem fixed_finite_package_uses_direct_tag_output :
    fixedFiniteMachine.k₀ = Sum.inl BitDecoderMachine.StackId.input ∧
      fixedFiniteMachine.k₁ = Sum.inl BitDecoderMachine.StackId.output ∧
      fixedFiniteMachine.main = phaseLabel .scan :=
  ⟨rfl, rfl, rfl⟩

def finiteMachineUniformTiming (raw : Bits) :
    StateTransition.EvalsToInTime fixedFiniteMachine.step
      (Turing.initList fixedFiniteMachine raw)
      (some (resultCfg (unpackWordRun raw).1 [] []
        (BitDecoderMachine.zeroRegisters, true) (fun _ : Bool => []))) (raw.length + 2) :=
  machineInTime haltCaller true raw

theorem actual_finite_machine_source_execution (raw : Bits) :
    (fun c => c.bind fixedFiniteMachine.step)^[runSteps raw]
        (some (Turing.initList fixedFiniteMachine raw)) =
      some (resultCfg (unpackWordRun raw).1 [] []
        (BitDecoderMachine.zeroRegisters, true) (fun _ : Bool => [])) :=
  machine_run_source haltCaller true raw

/-! These callers start executing only after the established live result. -/

def sentinelCaller : External Unit → Statement SmallAlphabet Unit Bool
  | .inl _ => .push (.inr false) (fun _ => true) .halt
  | .inr () => .halt

def literalStart (flag : Bool) (bits : Bits) (tags : Word) : Cfg SmallAlphabet Unit Bool :=
  cfg (some (phaseLabel .scan)) (staleRegisters flag) (wordBits [3, 12]) [] [] (smallContext bits tags)

def literalHandoff (flag : Bool) (bits : Bits) (tags : Word) : Cfg SmallAlphabet Unit Bool :=
  cfg (some (resultLabel .success)) (BitDecoderMachine.zeroRegisters, flag)
    [] [] [3, 12] (smallContext bits tags)

def literalAfterCaller (flag : Bool) (bits : Bits) (tags : Word) : Cfg SmallAlphabet Unit Bool :=
  cfg none (BitDecoderMachine.zeroRegisters, flag) [] [] [3, 12] (smallContext (true :: bits) tags)

theorem sentinel_push_is_one_actual_transition
    (result : Result) (regs : Registers Bool) (raw : Bits) (rev out : Word) (bits : Bits) (tags : Word) :
    step sentinelCaller
        (cfg (some (resultLabel result)) regs raw rev out (smallContext bits tags)) =
      some (cfg none regs raw rev out (smallContext (true :: bits) tags)) := by
  apply congrArg some
  apply cfg_ext <;> first | rfl | exact fun k => by cases k <;> rfl

theorem sentinel_handoff_is_before_the_actual_push (flag : Bool) (bits : Bits) (tags : Word) :
    (next sentinelCaller)^[6] (some (literalStart flag bits tags)) =
      some (literalHandoff flag bits tags) :=
  two_tags_return_in_forward_order_in_six sentinelCaller (staleRegisters flag) (smallContext bits tags)

def sentinelHandoffInTime (flag : Bool) (bits : Bits) (tags : Word) :
    StateTransition.EvalsToInTime (step sentinelCaller) (literalStart flag bits tags)
      (some (literalHandoff flag bits tags)) 6 :=
  runInTimeExact sentinelCaller (wordBits [3, 12]) (staleRegisters flag) (smallContext bits tags)

def sentinelCallerInTime (flag : Bool) (bits : Bits) (tags : Word) :
    StateTransition.EvalsToInTime (step sentinelCaller) (literalHandoff flag bits tags)
      (some (literalAfterCaller flag bits tags)) 1 where
  steps := 1
  evals_in_steps := sentinel_push_is_one_actual_transition .success (BitDecoderMachine.zeroRegisters, flag)
    [] [] [3, 12] bits tags
  steps_le_m := Nat.le_refl _

def sentinelCompositionInTime (flag : Bool) (bits : Bits) (tags : Word) :
    StateTransition.EvalsToInTime (step sentinelCaller) (literalStart flag bits tags)
      (some (literalAfterCaller flag bits tags)) 7 :=
  StateTransition.EvalsToInTime.trans (step sentinelCaller) 6 1
    (literalStart flag bits tags) (literalHandoff flag bits tags)
    (some (literalAfterCaller flag bits tags))
    (sentinelHandoffInTime flag bits tags) (sentinelCallerInTime flag bits tags)

theorem success_handoff_halt_and_outer_none_have_clocks_six_seven_eight
    (flag : Bool) (bits : Bits) (tags : Word) :
    (next sentinelCaller)^[6] (some (literalStart flag bits tags)) =
        some (literalHandoff flag bits tags) ∧
      (literalHandoff flag bits tags).l = some (resultLabel .success) ∧
      (literalHandoff flag bits tags).stk (.inr false) = bits ∧
      (next sentinelCaller)^[7] (some (literalStart flag bits tags)) =
        some (literalAfterCaller flag bits tags) ∧
      (literalAfterCaller flag bits tags).l = none ∧
      (literalAfterCaller flag bits tags).stk (.inr false) = true :: bits ∧
      (next sentinelCaller)^[8] (some (literalStart flag bits tags)) = none := by
  have completed : (next sentinelCaller)^[7] (some (literalStart flag bits tags)) =
      some (literalAfterCaller flag bits tags) := (sentinelCompositionInTime flag bits tags).evals_in_steps
  refine ⟨sentinel_handoff_is_before_the_actual_push flag bits tags, rfl, rfl,
    completed, rfl, rfl, ?_⟩
  rw [show 8 = 7 + 1 by rfl, Function.iterate_succ_apply', completed]
  rfl

/-- Failure uses a nonempty short input; empty raw belongs to the success case. -/
def failureStart (flag : Bool) (bits : Bits) (tags : Word) : Cfg SmallAlphabet Unit Bool :=
  cfg (some (phaseLabel .scan)) (staleRegisters flag) [true] [] [] (smallContext bits tags)

def failureHandoff (flag : Bool) (bits : Bits) (tags : Word) : Cfg SmallAlphabet Unit Bool :=
  cfg (some (resultLabel .failure)) (BitDecoderMachine.zeroRegisters, flag)
    [] [] [] (smallContext bits tags)

def failureAfterCaller (flag : Bool) (bits : Bits) (tags : Word) : Cfg SmallAlphabet Unit Bool :=
  cfg none (BitDecoderMachine.zeroRegisters, flag) [] [] [] (smallContext (true :: bits) tags)

def failureHandoffInTime (flag : Bool) (bits : Bits) (tags : Word) :
    StateTransition.EvalsToInTime (step sentinelCaller) (failureStart flag bits tags)
      (some (failureHandoff flag bits tags)) 2 :=
  runInTimeExact sentinelCaller [true] (staleRegisters flag) (smallContext bits tags)

def failureCallerInTime (flag : Bool) (bits : Bits) (tags : Word) :
    StateTransition.EvalsToInTime (step sentinelCaller) (failureHandoff flag bits tags)
      (some (failureAfterCaller flag bits tags)) 1 where
  steps := 1
  evals_in_steps := sentinel_push_is_one_actual_transition .failure (BitDecoderMachine.zeroRegisters, flag)
    [] [] [] bits tags
  steps_le_m := Nat.le_refl _

def failureCompositionInTime (flag : Bool) (bits : Bits) (tags : Word) :
    StateTransition.EvalsToInTime (step sentinelCaller) (failureStart flag bits tags)
      (some (failureAfterCaller flag bits tags)) 3 :=
  StateTransition.EvalsToInTime.trans (step sentinelCaller) 2 1
    (failureStart flag bits tags) (failureHandoff flag bits tags)
    (some (failureAfterCaller flag bits tags))
    (failureHandoffInTime flag bits tags) (failureCallerInTime flag bits tags)

theorem failure_handoff_halt_and_outer_none_have_clocks_two_three_four
    (flag : Bool) (bits : Bits) (tags : Word) :
    (next sentinelCaller)^[2] (some (failureStart flag bits tags)) =
        some (failureHandoff flag bits tags) ∧
      (failureHandoff flag bits tags).l = some (resultLabel .failure) ∧
      (failureHandoff flag bits tags).stk (.inr false) = bits ∧
      (next sentinelCaller)^[3] (some (failureStart flag bits tags)) =
        some (failureAfterCaller flag bits tags) ∧
      (failureAfterCaller flag bits tags).l = none ∧
      (failureAfterCaller flag bits tags).stk (.inr false) = true :: bits ∧
      (next sentinelCaller)^[4] (some (failureStart flag bits tags)) = none := by
  have after : (next sentinelCaller)^[3] (some (failureStart flag bits tags)) =
      some (failureAfterCaller flag bits tags) := (failureCompositionInTime flag bits tags).evals_in_steps
  refine ⟨one_bit_fails_in_two sentinelCaller (staleRegisters flag) (smallContext bits tags) true,
    rfl, rfl, after, rfl, rfl, ?_⟩
  rw [show 4 = 3 + 1 by rfl, Function.iterate_succ_apply', after]
  rfl

theorem distinct_callers_have_the_same_inclusive_decoder_prefix
    (flag : Bool) (bits : Bits) (tags : Word) (n : Nat) (bound : n ≤ 6) :
    (next sentinelCaller)^[n] (some (literalStart flag bits tags)) =
      (next haltCaller)^[n] (some (literalStart flag bits tags)) :=
  phase_prefix_caller_independent sentinelCaller haltCaller .scan (wordBits [3, 12]) [] []
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

/-- An external caller can allocate without bound after local ownership ends. -/
def allocatingCaller : External Unit → Statement SmallAlphabet Unit Bool
  | .inl .failure => .push (.inr false) (fun _ => true) (jump (resultLabel .failure))
  | _ => .halt

def shortStart : Cfg SmallAlphabet Unit Bool := failureStart true [] []

def allocatingState (count : Nat) : Cfg SmallAlphabet Unit Bool :=
  cfg (some (resultLabel .failure)) (BitDecoderMachine.zeroRegisters, true) [] [] []
    (smallContext (List.replicate count true) [])

theorem allocating_caller_step (count : Nat) :
    step allocatingCaller (allocatingState count) = some (allocatingState (count + 1)) := by
  apply congrArg some
  apply cfg_ext <;> first | rfl | exact fun k => by cases k <;> rfl

theorem allocating_caller_runs_after_the_first_failure (count : Nat) :
    (next allocatingCaller)^[2 + count] (some shortStart) = some (allocatingState count) := by
  induction count with
  | zero => exact one_bit_fails_in_two allocatingCaller (staleRegisters true) (smallContext [] []) true
  | succ count ih =>
      rw [Nat.add_succ, Function.iterate_succ_apply', ih, next_some, allocating_caller_step]

theorem post_return_allocation_exceeds_the_one_cell_entry_bound :
    (next allocatingCaller)^[2] (some shortStart) = some (allocatingState 0) ∧
      (next allocatingCaller)^[4] (some shortStart) = some (allocatingState 2) ∧
      stackCells shortStart = 1 ∧ stackCells (allocatingState 2) = 2 ∧
      ¬ stackCells (allocatingState 2) ≤ ([true] : Bits).length + contextCells (smallContext [] []) := by
  refine ⟨allocating_caller_runs_after_the_first_failure 0,
    allocating_caller_runs_after_the_first_failure 2, ?_, ?_, ?_⟩ <;> decide

/-- A later caller success can have invented output and can reenter with that dirty output. -/
def misleadingCaller : External Unit → Statement SmallAlphabet Unit Bool
  | .inl .failure => .push (.inl .output) (fun _ => 3) (jump (resultLabel .success))
  | .inl .success => jump (phaseLabel .scan)
  | .inr () => .halt

def misleadingSuccess : Cfg SmallAlphabet Unit Bool :=
  cfg (some (resultLabel .success)) (BitDecoderMachine.zeroRegisters, true)
    [] [] [3] (smallContext [] [])

def misleadingReentry : Cfg SmallAlphabet Unit Bool :=
  cfg (some (phaseLabel .scan)) (BitDecoderMachine.zeroRegisters, true) [] [] [3] (smallContext [] [])

theorem one_caller_step_can_manufacture_success :
    step misleadingCaller (allocatingState 0) = some misleadingSuccess := by
  apply congrArg some
  apply cfg_ext <;> first | rfl | exact fun k => by cases k <;> rfl

theorem later_success_is_not_the_source_connected_first_success :
    (next misleadingCaller)^[2] (some shortStart) = some (allocatingState 0) ∧
      (next misleadingCaller)^[3] (some shortStart) = some misleadingSuccess ∧
      (next misleadingCaller)^[4] (some shortStart) = some misleadingReentry ∧
      ¬ FirstSuccess misleadingCaller [true] [3] (staleRegisters true) (smallContext [] []) := by
  have first : (next misleadingCaller)^[2] (some shortStart) = some (allocatingState 0) :=
    one_bit_fails_in_two misleadingCaller (staleRegisters true) (smallContext [] []) true
  have later : (next misleadingCaller)^[3] (some shortStart) = some misleadingSuccess := by
    rw [show 3 = 2 + 1 by rfl, Function.iterate_succ_apply', first, next_some,
      one_caller_step_can_manufacture_success]
  refine ⟨first, later, ?_, ?_⟩
  · rw [show 4 = 3 + 1 by rfl, Function.iterate_succ_apply', later]
    rfl
  · intro claimed
    have impossible := (firstSuccess_iff misleadingCaller [true] [3]
      (staleRegisters true) (smallContext [] [])).mp claimed
    cases impossible

end Examples.RotationCertificateOpenDecoderMachine
