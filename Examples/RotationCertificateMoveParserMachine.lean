import Applications.Resources.RotationCertificate.MoveParserMachine
import Examples.RotationCertificateCodecs

/-!
# Connected clients of the finite move-prefix parser

The complete case plan was fixed before this client was written. Every execution
below uses the producer's actual finite program and its public execution laws.
Dirty reverse stacks, old path outputs, arbitrary untouched suffixes and stale
registers remain visible. Source-event work, machine transitions, delimiter debt
and physical cells are separate observations. This open parser returns one move;
rotation, repeated verification and the final Boolean result remain later work.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.RotationCertificateMoveParserMachine
open Trees Resources
open Search.SharedTree (Branch)
open Trees.Rotations (RotationDirection RotationMove)
open Resources.RotationCertificate
open MoveParserMachine

def SmallAlphabet : Bool → Type
  | false => Bool
  | true => Tag

instance smallAlphabetFintype (k : Bool) : Fintype (SmallAlphabet k) := by
  cases k with
  | false => change Fintype Bool; infer_instance
  | true => change Fintype Tag; infer_instance

def smallContext (bits : List Bool) (tags : Word) : ∀ k, List (SmallAlphabet k)
  | false => bits
  | true => tags

def sampleContext : ∀ k, List (SmallAlphabet k) :=
  smallContext [true, false, true] [15, 6, 1]

def stale (flag : Bool) : Registers Bool := (some 15, flag)

def haltCaller : External Unit → Statement SmallAlphabet Unit Bool := fun _ => .halt

theorem actual_finite_carrier_counts :
    Fintype.card (StackId Bool) = 5 ∧ Fintype.card (Label Unit) = 11 ∧
      Fintype.card (Registers Bool) = 34 ∧
      Fintype.card {label : Label Unit // Owned (some label)} = 7 ∧
      Fintype.card Tag = 16 ∧ Fintype.card Branch = 2 := by
  refine ⟨?_, ?_, ?_, owned_card, by decide, branch_card⟩
  · simpa using (stackId_card (K := Bool))
  · simpa using (label_card (Λ := Unit))
  · exact (registers_card (R := Bool))

/-- The seven local labels stay finite without a finite ambient caller type. -/
theorem infinite_caller_still_has_seven_owned_labels :
    Fintype.card {label : Label Nat // Owned (some label)} = 7 := owned_card

theorem all_physical_alphabets_are_finite (k : StackId Bool) :
    Nonempty (Fintype (Alphabet SmallAlphabet k)) := ⟨inferInstance⟩

theorem fixture_has_six_protected_cells : contextCells sampleContext = 6 := by
  decide

/-- The callback inverse is restricted to real Branch observations. -/
theorem branch_observations_and_total_fallback (b : Branch) :
    inverseBranch (branchTag b) = b ∧
      inverseBranch (0 : Tag) = .left ∧ branchTag (inverseBranch (0 : Tag)) ≠ 0 :=
  ⟨inverseBranch_branchTag b, rfl, by decide⟩

section Generic
variable {K Λ R : Type} [DecidableEq K] {Γ : K → Type}
variable (caller : External Λ → Statement Γ Λ R)
variable (regs : Registers R) (ctx : ∀ k, List (Γ k))

/-- Immediate rejection preserves even a dirty reverse stack. -/
theorem initial_empty_step (rev out : List Branch) :
    step caller (cfg (some (phaseLabel .start)) regs [] rev out ctx) =
      some (cfg (some (resultLabel .failure)) (reset regs) [] rev out ctx) :=
  start_step_nil caller rev out regs ctx

theorem initial_direction_step (d : RotationDirection) (raw : Word) (rev out : List Branch) :
    step caller (cfg (some (phaseLabel .start)) regs (directionTag d :: raw) rev out ctx) =
      some (cfg (some (phaseLabel (.scan d))) (reset regs) raw rev out ctx) :=
  start_step_direction caller d raw rev out regs ctx

theorem initial_foreign_step (tag : Tag) (raw : Word) (rev out : List Branch)
    (left : tag ≠ rotateLeftTag) (right : tag ≠ rotateRightTag) :
    step caller (cfg (some (phaseLabel .start)) regs (tag :: raw) rev out ctx) =
      some (cfg (some (resultLabel .failure)) (reset regs) (tag :: raw) rev out ctx) :=
  start_step_foreign caller tag raw rev out regs ctx left right

theorem scan_empty_step (d : RotationDirection) (rev out : List Branch) :
    step caller (cfg (some (phaseLabel (.scan d))) regs [] rev out ctx) =
      some (cfg (some (phaseLabel (.undo d))) (reset regs) [] rev out ctx) :=
  scan_step_nil caller d rev out regs ctx

theorem scan_branch_step (d : RotationDirection) (b : Branch)
    (raw : Word) (rev out : List Branch) :
    step caller (cfg (some (phaseLabel (.scan d))) regs (branchTag b :: raw) rev out ctx) =
      some (cfg (some (phaseLabel (.scan d))) (reset regs) raw (b :: rev) out ctx) :=
  scan_step_branch caller d b raw rev out regs ctx

theorem scan_delimiter_step (d : RotationDirection) (raw : Word) (rev out : List Branch) :
    step caller (cfg (some (phaseLabel (.scan d))) regs (endMoveTag :: raw) rev out ctx) =
      some (cfg (some (phaseLabel (.emit d))) (reset regs) raw rev out ctx) :=
  scan_step_end caller d raw rev out regs ctx

theorem scan_foreign_step (d : RotationDirection) (tag : Tag) (raw : Word)
    (rev out : List Branch) (ended : tag ≠ endMoveTag)
    (left : tag ≠ pathLeftTag) (right : tag ≠ pathRightTag) :
    step caller (cfg (some (phaseLabel (.scan d))) regs (tag :: raw) rev out ctx) =
      some (cfg (some (phaseLabel (.undo d))) (reset regs) (tag :: raw) rev out ctx) :=
  scan_step_foreign caller d tag raw rev out regs ctx ended left right

theorem emit_branch_step (d : RotationDirection) (b : Branch)
    (raw : Word) (rev out : List Branch) :
    step caller (cfg (some (phaseLabel (.emit d))) regs raw (b :: rev) out ctx) =
      some (cfg (some (phaseLabel (.emit d))) (reset regs) raw rev (b :: out) ctx) :=
  emit_step_cons caller d b raw rev out regs ctx

theorem emit_empty_step (d : RotationDirection) (raw : Word) (out : List Branch) :
    step caller (cfg (some (phaseLabel (.emit d))) regs raw [] out ctx) =
      some (cfg (some (resultLabel (.success d))) (reset regs) raw [] out ctx) :=
  emit_step_nil caller d raw out regs ctx

theorem undo_branch_step (d : RotationDirection) (b : Branch)
    (raw : Word) (rev out : List Branch) :
    step caller (cfg (some (phaseLabel (.undo d))) regs raw (b :: rev) out ctx) =
      some (cfg (some (phaseLabel (.undo d))) (reset regs) (branchTag b :: raw) rev out ctx) :=
  undo_step_cons caller d b raw rev out regs ctx

theorem undo_empty_step (d : RotationDirection) (raw : Word) (out : List Branch) :
    step caller (cfg (some (phaseLabel (.undo d))) regs raw [] out ctx) =
      some (cfg (some (resultLabel .failure)) (reset regs) (directionTag d :: raw) [] out ctx) :=
  undo_step_nil caller d raw out regs ctx

/-- Both generalized transfers retain every old output cell and literal suffix. -/
theorem generalized_transfers (d : RotationDirection) (raw : Word) (rev out : List Branch) :
    (next caller)^[rev.length + 1]
        (some (cfg (some (phaseLabel (.emit d))) regs raw rev out ctx)) =
      some (cfg (some (resultLabel (.success d))) (reset regs) raw [] (rev.reverse ++ out) ctx) ∧
    (next caller)^[rev.length + 1]
        (some (cfg (some (phaseLabel (.undo d))) regs raw rev out ctx)) =
      some (cfg (some (resultLabel .failure)) (reset regs)
        (directionTag d :: (pathTags rev.reverse ++ raw)) [] out ctx) :=
  ⟨emit_iterate caller d raw rev out regs ctx, undo_iterate caller d raw rev out regs ctx⟩

/-- The empty probe has not run in any of these transfer prefixes. -/
theorem generalized_transfer_prefixes (d : RotationDirection) (raw : Word)
    (rev out : List Branch) (j : Nat) (bound : j ≤ rev.length) :
    (next caller)^[j] (some (cfg (some (phaseLabel (.emit d))) regs raw rev out ctx)) =
      some (cfg (some (phaseLabel (.emit d))) (if j = 0 then regs else reset regs)
        raw (rev.drop j) ((rev.take j).reverse ++ out) ctx) ∧
    (next caller)^[j] (some (cfg (some (phaseLabel (.undo d))) regs raw rev out ctx)) =
      some (cfg (some (phaseLabel (.undo d))) (if j = 0 then regs else reset regs)
        (pathTags (rev.take j).reverse ++ raw) (rev.drop j) out ctx) :=
  ⟨emit_prefix caller d raw rev out regs ctx j bound,
    undo_prefix caller d raw rev out regs ctx j bound⟩

/-- Nonpalindromic scanning tests orientation without inspecting the suffix. -/
theorem scan_nonpalindromic_prefix (raw : Word) (rev out : List Branch)
    (d : RotationDirection) :
    (next caller)^[3]
        (some (cfg (some (phaseLabel (.scan d))) regs ([8, 9, 9] ++ raw) rev out ctx)) =
      some (cfg (some (phaseLabel (.scan d))) (reset regs)
        raw ([.right, .right, .left] ++ rev) out ctx) :=
  scan_prefix caller d [.left, .right, .right] raw rev out regs ctx

theorem all_scan_prefixes (d : RotationDirection) (accepted : List Branch)
    (raw : Word) (rev out : List Branch) :
    (next caller)^[accepted.length]
        (some (cfg (some (phaseLabel (.scan d))) regs (pathTags accepted ++ raw) rev out ctx)) =
      some (cfg (some (phaseLabel (.scan d))) (if accepted = [] then regs else reset regs)
        raw (accepted.reverse ++ rev) out ctx) :=
  scan_prefix caller d accepted raw rev out regs ctx

theorem dirty_scan_returns_the_actual_source_result (d : RotationDirection)
    (raw : Word) (rev out : List Branch) :
    (next caller)^[2 * branchCount raw + rev.length + 2]
        (some (cfg (some (phaseLabel (.scan d))) regs raw rev out ctx)) =
      some (scanResult d regs raw rev out ctx (parsePathRun raw).1) :=
  scan_iterate caller d raw rev out regs ctx

theorem dirty_scan_success (d : RotationDirection) (raw : Word) (path : List Branch)
    (rest : Word) (rev out : List Branch)
    (returned : (parsePathRun raw).1 = some (path, rest)) :
    (next caller)^[2 * path.length + rev.length + 2]
        (some (cfg (some (phaseLabel (.scan d))) regs raw rev out ctx)) =
      some (cfg (some (resultLabel (.success d))) (reset regs)
        rest [] (rev.reverse ++ path ++ out) ctx) :=
  scan_of_some caller d raw path rest rev out regs ctx returned

theorem dirty_scan_failure (d : RotationDirection) (raw : Word) (rev out : List Branch)
    (failed : (parsePathRun raw).1 = none) :
    (next caller)^[2 * branchCount raw + rev.length + 2]
        (some (cfg (some (phaseLabel (.scan d))) regs raw rev out ctx)) =
      some (cfg (some (resultLabel .failure)) (reset regs)
        (directionTag d :: (pathTags rev.reverse ++ raw)) [] out ctx) :=
  scan_of_none caller d raw rev out regs ctx failed

theorem dirty_scan_order_sensitive_success :
    (next caller)^[8]
        (some (cfg (some (phaseLabel (.scan .right))) regs
          [8, 9, 10, 15] [.left, .right] [.left] ctx)) =
      some (cfg (some (resultLabel (.success .right))) (reset regs)
        [15] [] [.right, .left, .left, .right, .left] ctx) :=
  scan_of_some caller .right [8, 9, 10, 15] [.left, .right] [15]
    [.left, .right] [.left] regs ctx rfl

theorem dirty_scan_order_sensitive_failure :
    (next caller)^[6]
        (some (cfg (some (phaseLabel (.scan .right))) regs
          [8, 15, 9] [.left, .right] [.left] ctx)) =
      some (cfg (some (resultLabel .failure)) (reset regs)
        [7, 9, 8, 8, 15, 9] [] [.left] ctx) :=
  scan_of_none caller .right [8, 15, 9] [.left, .right] [.left] regs ctx rfl

/-- Dirty start is total, but immediate failure does not clear an old reverse. -/
theorem dirty_initial_foreign_preserves_reverse :
    (next caller)^[1]
        (some (cfg (some (phaseLabel .start)) regs [15, 9, 6] [.left, .right] [.left] ctx)) =
      some (cfg (some (resultLabel .failure)) (reset regs)
        [15, 9, 6] [.left, .right] [.left] ctx) :=
  start_step_foreign caller 15 [9, 6] [.left, .right] [.left] regs ctx (by decide) (by decide)

theorem every_dirty_owned_phase_returns (phase : Phase) (raw : Word) (rev out : List Branch) :
    (next caller)^[phaseSteps phase raw rev]
        (some (cfg (some (phaseLabel phase)) regs raw rev out ctx)) =
      some (phaseResult phase regs raw rev out ctx) ∧
    ¬ Owned (phaseResult (Λ := Λ) phase regs raw rev out ctx).l ∧
    ∀ n, n < phaseSteps phase raw rev → ∃ reached,
      (next caller)^[n] (some (cfg (some (phaseLabel phase)) regs raw rev out ctx)) =
        some reached ∧ Owned reached.l :=
  ⟨phase_iterate caller phase raw rev out regs ctx,
    phase_first_return caller phase raw rev out regs ctx⟩

/-- Complete clean-reverse entry keeps arbitrary old output and arbitrary registers. -/
theorem every_raw_input_returns (raw : Word) (out : List Branch) :
    (next caller)^[fullSteps raw] (some (entry regs raw out ctx)) =
      some (resultCfg regs raw out ctx (parseMoveRun raw).1) ∧
    0 < fullSteps raw ∧ fullSteps raw ≤ 2 * raw.length + 1 :=
  ⟨run_source caller raw out regs ctx, fullSteps_pos raw, fullSteps_le raw⟩

theorem source_success_is_first_machine_success (raw : Word) (move : RotationMove)
    (rest : Word) (out : List Branch) :
    FirstSuccess caller raw move rest out regs ctx ↔
      (parseMoveRun raw).1 = some (move, rest) :=
  firstSuccess_iff caller raw move rest out regs ctx

theorem exact_code_recognition (raw : Word) (move : RotationMove)
    (rest : Word) (out : List Branch) :
    FirstSuccess caller raw move rest out regs ctx ↔ raw = moveCode move ++ rest :=
  firstSuccess_code_iff caller raw move rest out regs ctx

theorem first_failure_restores_the_whole_word (raw : Word) (out : List Branch) :
    FirstFailure caller raw out regs ctx ↔ (parseMoveRun raw).1 = none :=
  firstFailure_iff caller raw out regs ctx

/-- Cancelling an arbitrary old output on the right identifies the parsed path. -/
theorem first_success_is_unique_with_old_output (raw : Word) (move other : RotationMove)
    (rest suffix : Word) (out : List Branch)
    (first : FirstSuccess caller raw move rest out regs ctx)
    (second : FirstSuccess caller raw other suffix out regs ctx) :
    move = other ∧ rest = suffix :=
  firstSuccess_unique caller raw move other rest suffix out regs ctx first second

theorem first_success_has_exact_cost_and_consumption (raw : Word) (move : RotationMove)
    (rest : Word) (out : List Branch)
    (returned : FirstSuccess caller raw move rest out regs ctx) :
    (parseMoveRun raw).2 = 3 * move.position.length + 4 ∧
      fullSteps raw = 2 * move.position.length + 3 ∧
      raw.length = move.position.length + 2 + rest.length ∧
      rest.length + 2 ≤ raw.length ∧ rest.length < raw.length := by
  have source := (firstSuccess_iff caller raw move rest out regs ctx).mp returned
  obtain ⟨work, clock, length⟩ := firstSuccess_costs caller raw move rest out regs ctx returned
  exact ⟨work, clock, length, parseMoveRun_consumes_two raw move rest source,
    parseMoveRun_rest_length_lt raw move rest source⟩

theorem first_failure_has_its_recursive_source_cost (raw : Word) (out : List Branch)
    (failed : FirstFailure caller raw out regs ctx) :
    (parseMoveRun raw).2 = fullSteps raw + 1 := firstFailure_cost caller raw out regs ctx failed

theorem actual_emitter_and_parser_feed_the_same_machine (move : RotationMove)
    (rest : Word) (out : List Branch) :
    parseMoveRun (emitMoveRun move rest).1 = (some (move, rest), 3 * move.position.length + 4) ∧
    (emitMoveRun move rest).2 = 2 * move.position.length + 3 ∧
    (next caller)^[2 * move.position.length + 3]
        (some (entry regs (emitMoveRun move rest).1 out ctx)) =
      some (cfg (some (resultLabel (.success move.direction))) (reset regs)
        rest [] (move.position ++ out) ctx) :=
  ⟨parseMoveRun_emit move rest, emitMoveRun_cost move rest, run_emit caller move rest out regs ctx⟩

theorem eof_after_any_path (d : RotationDirection) (accepted out : List Branch) :
    parseMoveRun (directionTag d :: pathTags accepted) = (none, 2 * accepted.length + 4) ∧
    (next caller)^[2 * accepted.length + 3]
        (some (entry regs (directionTag d :: pathTags accepted) out ctx)) =
      some (cfg (some (resultLabel .failure)) (reset regs)
        (directionTag d :: pathTags accepted) [] out ctx) :=
  ⟨parseMoveRun_eof_prefix d accepted, run_eof_prefix caller d accepted out regs ctx⟩

theorem foreign_after_any_path (d : RotationDirection) (accepted : List Branch)
    (tag : Tag) (tail : Word) (out : List Branch) (ended : tag ≠ endMoveTag)
    (left : tag ≠ pathLeftTag) (right : tag ≠ pathRightTag) :
    parseMoveRun (directionTag d :: (pathTags accepted ++ tag :: tail)) =
      (none, 2 * accepted.length + 4) ∧
    (next caller)^[2 * accepted.length + 3]
        (some (entry regs (directionTag d :: (pathTags accepted ++ tag :: tail)) out ctx)) =
      some (cfg (some (resultLabel .failure)) (reset regs)
        (directionTag d :: (pathTags accepted ++ tag :: tail)) [] out ctx) :=
  ⟨parseMoveRun_foreign_prefix d accepted tag tail ended left right,
    run_foreign_prefix caller d accepted tag tail out regs ctx ended left right⟩

end Generic

section FixedCases
variable {K Λ R : Type} [DecidableEq K] {Γ : K → Type}
variable (caller : External Λ → Statement Γ Λ R)
variable (regs : Registers R) (ctx : ∀ k, List (Γ k))

theorem empty_and_singleton_transfers (d : RotationDirection) (b : Branch)
    (raw : Word) (out : List Branch) :
    (next caller)^[1] (some (cfg (some (phaseLabel (.emit d))) regs raw [] out ctx)) =
      some (cfg (some (resultLabel (.success d))) (reset regs) raw [] out ctx) ∧
    (next caller)^[1] (some (cfg (some (phaseLabel (.undo d))) regs raw [] out ctx)) =
      some (cfg (some (resultLabel .failure)) (reset regs) (directionTag d :: raw) [] out ctx) ∧
    (next caller)^[2] (some (cfg (some (phaseLabel (.emit d))) regs raw [b] out ctx)) =
      some (cfg (some (resultLabel (.success d))) (reset regs) raw [] (b :: out) ctx) ∧
    (next caller)^[2] (some (cfg (some (phaseLabel (.undo d))) regs raw [b] out ctx)) =
      some (cfg (some (resultLabel .failure)) (reset regs)
        (directionTag d :: branchTag b :: raw) [] out ctx) :=
  ⟨emit_iterate caller d raw [] out regs ctx, undo_iterate caller d raw [] out regs ctx,
    emit_iterate caller d raw [b] out regs ctx, undo_iterate caller d raw [b] out regs ctx⟩

theorem nonpalindromic_emit_prefixes :
    (next caller)^[0]
        (some (cfg (some (phaseLabel (.emit .right))) regs [15, 6] [.left, .right, .right] [.left] ctx)) =
      some (cfg (some (phaseLabel (.emit .right))) regs [15, 6] [.left, .right, .right] [.left] ctx) ∧
    (next caller)^[1]
        (some (cfg (some (phaseLabel (.emit .right))) regs [15, 6] [.left, .right, .right] [.left] ctx)) =
      some (cfg (some (phaseLabel (.emit .right))) (reset regs) [15, 6] [.right, .right] [.left, .left] ctx) ∧
    (next caller)^[2]
        (some (cfg (some (phaseLabel (.emit .right))) regs [15, 6] [.left, .right, .right] [.left] ctx)) =
      some (cfg (some (phaseLabel (.emit .right))) (reset regs) [15, 6] [.right]
        [.right, .left, .left] ctx) ∧
    (next caller)^[3]
        (some (cfg (some (phaseLabel (.emit .right))) regs [15, 6] [.left, .right, .right] [.left] ctx)) =
      some (cfg (some (phaseLabel (.emit .right))) (reset regs) [15, 6] []
        [.right, .right, .left, .left] ctx) ∧
    (next caller)^[4]
        (some (cfg (some (phaseLabel (.emit .right))) regs [15, 6] [.left, .right, .right] [.left] ctx)) =
      some (cfg (some (resultLabel (.success .right))) (reset regs) [15, 6] []
        [.right, .right, .left, .left] ctx) :=
  ⟨emit_prefix caller .right [15, 6] [.left, .right, .right] [.left] regs ctx 0 (by decide),
    emit_prefix caller .right [15, 6] [.left, .right, .right] [.left] regs ctx 1 (by decide),
    emit_prefix caller .right [15, 6] [.left, .right, .right] [.left] regs ctx 2 (by decide),
    emit_prefix caller .right [15, 6] [.left, .right, .right] [.left] regs ctx 3 (by decide),
    emit_iterate caller .right [15, 6] [.left, .right, .right] [.left] regs ctx⟩

theorem nonpalindromic_undo_prefixes :
    (next caller)^[0]
        (some (cfg (some (phaseLabel (.undo .right))) regs [15, 6] [.left, .right, .right] [.left] ctx)) =
      some (cfg (some (phaseLabel (.undo .right))) regs [15, 6] [.left, .right, .right] [.left] ctx) ∧
    (next caller)^[1]
        (some (cfg (some (phaseLabel (.undo .right))) regs [15, 6] [.left, .right, .right] [.left] ctx)) =
      some (cfg (some (phaseLabel (.undo .right))) (reset regs) [8, 15, 6] [.right, .right] [.left] ctx) ∧
    (next caller)^[2]
        (some (cfg (some (phaseLabel (.undo .right))) regs [15, 6] [.left, .right, .right] [.left] ctx)) =
      some (cfg (some (phaseLabel (.undo .right))) (reset regs) [9, 8, 15, 6] [.right] [.left] ctx) ∧
    (next caller)^[3]
        (some (cfg (some (phaseLabel (.undo .right))) regs [15, 6] [.left, .right, .right] [.left] ctx)) =
      some (cfg (some (phaseLabel (.undo .right))) (reset regs) [9, 9, 8, 15, 6] [] [.left] ctx) ∧
    (next caller)^[4]
        (some (cfg (some (phaseLabel (.undo .right))) regs [15, 6] [.left, .right, .right] [.left] ctx)) =
      some (cfg (some (resultLabel .failure)) (reset regs) [7, 9, 9, 8, 15, 6] [] [.left] ctx) :=
  ⟨undo_prefix caller .right [15, 6] [.left, .right, .right] [.left] regs ctx 0 (by decide),
    undo_prefix caller .right [15, 6] [.left, .right, .right] [.left] regs ctx 1 (by decide),
    undo_prefix caller .right [15, 6] [.left, .right, .right] [.left] regs ctx 2 (by decide),
    undo_prefix caller .right [15, 6] [.left, .right, .right] [.left] regs ctx 3 (by decide),
    undo_iterate caller .right [15, 6] [.left, .right, .right] [.left] regs ctx⟩

theorem dirty_empty_undo_has_one_more_physical_cell :
    (next caller)^[1]
        (some (cfg (some (phaseLabel (.undo .right))) regs [] [] [] ctx)) =
      some (cfg (some (resultLabel .failure)) (reset regs) [7] [] [] ctx) ∧
    ownedCells (cfg (Λ := Λ) (some (phaseLabel (.undo .right))) regs [] [] [] ctx) = 0 ∧
    debt (some (phaseLabel (Λ := Λ) (.undo .right))) = 1 ∧
    ownedCells (cfg (Λ := Λ) (some (resultLabel .failure)) (reset regs) [7] [] [] ctx) = 1 ∧
    debt (some (resultLabel (Λ := Λ) .failure)) = 0 :=
  ⟨undo_step_nil caller .right [] [] regs ctx, rfl, rfl, rfl, rfl⟩

theorem literal_empty (out : List Branch) :
    (next caller)^[1] (some (entry regs [] out ctx)) =
      some (cfg (some (resultLabel .failure)) (reset regs) [] [] out ctx) ∧
      parseMoveRun [] = (none, 2) :=
  ⟨run_of_none caller [] out regs ctx rfl, parseMoveRun_nil⟩

theorem literal_delimiter_is_not_a_direction (out : List Branch) :
    (next caller)^[1] (some (entry regs [10] out ctx)) =
      some (cfg (some (resultLabel .failure)) (reset regs) [10] [] out ctx) ∧
      parseMoveRun [10] = (none, 2) :=
  ⟨run_of_none caller [10] out regs ctx rfl, rfl⟩

theorem literal_missing_path_terminator (out : List Branch) :
    (next caller)^[3] (some (entry regs [6] out ctx)) =
      some (cfg (some (resultLabel .failure)) (reset regs) [6] [] out ctx) ∧
    (next caller)^[3] (some (entry regs [7] out ctx)) =
      some (cfg (some (resultLabel .failure)) (reset regs) [7] [] out ctx) ∧
    parseMoveRun [6] = (none, 4) ∧ parseMoveRun [7] = (none, 4) :=
  ⟨run_eof_prefix caller .left [] out regs ctx,
    run_eof_prefix caller .right [] out regs ctx,
    parseMoveRun_eof_prefix .left [], parseMoveRun_eof_prefix .right []⟩

theorem literal_root_moves (out : List Branch) :
    (next caller)^[3] (some (entry regs [6, 10] out ctx)) =
      some (cfg (some (resultLabel (.success .left))) (reset regs) [] [] out ctx) ∧
    (next caller)^[3] (some (entry regs [7, 10] out ctx)) =
      some (cfg (some (resultLabel (.success .right))) (reset regs) [] [] out ctx) ∧
    parseMoveRun [6, 10] = (some (⟨.left, []⟩, []), 4) ∧
    parseMoveRun [7, 10] = (some (⟨.right, []⟩, []), 4) :=
  ⟨run_code caller ⟨.left, []⟩ [] out regs ctx,
    run_code caller ⟨.right, []⟩ [] out regs ctx,
    parseMoveRun_code ⟨.left, []⟩ [], parseMoveRun_code ⟨.right, []⟩ []⟩

theorem literal_palindromic_and_nonpalindromic_paths (out : List Branch) :
    (next caller)^[9] (some (entry regs [6, 8, 9, 8, 10, 15, 2] out ctx)) =
      some (cfg (some (resultLabel (.success .left))) (reset regs) [15, 2] []
        ([.left, .right, .left] ++ out) ctx) ∧
    (next caller)^[9] (some (entry regs [7, 8, 9, 9, 10, 15, 2] out ctx)) =
      some (cfg (some (resultLabel (.success .right))) (reset regs) [15, 2] []
        ([.left, .right, .right] ++ out) ctx) ∧
    parseMoveRun [6, 8, 9, 8, 10, 15, 2] =
      (some (⟨.left, [.left, .right, .left]⟩, [15, 2]), 13) ∧
    parseMoveRun [7, 8, 9, 9, 10, 15, 2] =
      (some (⟨.right, [.left, .right, .right]⟩, [15, 2]), 13) :=
  ⟨run_code caller ⟨.left, [.left, .right, .left]⟩ [15, 2] out regs ctx,
    run_code caller ⟨.right, [.left, .right, .right]⟩ [15, 2] out regs ctx,
    parseMoveRun_code ⟨.left, [.left, .right, .left]⟩ [15, 2],
    parseMoveRun_code ⟨.right, [.left, .right, .right]⟩ [15, 2]⟩

theorem literal_eof_rollback (out : List Branch) :
    (next caller)^[7] (some (entry regs [7, 8, 8] out ctx)) =
      some (cfg (some (resultLabel .failure)) (reset regs) [7, 8, 8] [] out ctx) ∧
    parseMoveRun [7, 8, 8] = (none, 8) :=
  ⟨run_eof_prefix caller .right [.left, .left] out regs ctx,
    parseMoveRun_eof_prefix .right [.left, .left]⟩

/-- The final nine is never inspected after the foreign fifteen. -/
theorem literal_foreign_rollback (out : List Branch) :
    (next caller)^[5] (some (entry regs [7, 8, 15, 9] out ctx)) =
      some (cfg (some (resultLabel .failure)) (reset regs) [7, 8, 15, 9] [] out ctx) ∧
    parseMoveRun [7, 8, 15, 9] = (none, 6) :=
  ⟨run_foreign_prefix caller .right [.left] 15 [9] out regs ctx (by decide) (by decide) (by decide),
    parseMoveRun_foreign_prefix .right [.left] 15 [9] (by decide) (by decide) (by decide)⟩

theorem literal_second_move_remains_unparsed (out : List Branch) :
    (next caller)^[3] (some (entry regs [6, 10, 6, 10] out ctx)) =
      some (cfg (some (resultLabel (.success .left))) (reset regs) [6, 10] [] out ctx) ∧
    parseMoveRun [6, 10, 6, 10] = (some (⟨.left, []⟩, [6, 10]), 4) :=
  ⟨run_code caller ⟨.left, []⟩ [6, 10] out regs ctx,
    parseMoveRun_code ⟨.left, []⟩ [6, 10]⟩

/-- A row of the fixed sixteen-head table, stated with complete runtime endpoints. -/
def HeadCase (tag : Tag) (direction : Option RotationDirection) : Prop :=
  match direction with
  | none =>
      (next caller)^[1] (some (entry regs [tag, 10, 15] [] ctx)) =
        some (cfg (some (resultLabel .failure)) (reset regs) [tag, 10, 15] [] [] ctx) ∧
      parseMoveRun [tag, 10, 15] = (none, 2)
  | some d =>
      (next caller)^[3] (some (entry regs [tag, 10, 15] [] ctx)) =
        some (cfg (some (resultLabel (.success d))) (reset regs) [15] [] [] ctx) ∧
      parseMoveRun [tag, 10, 15] = (some (⟨d, []⟩, [15]), 4)

theorem foreign_head_case (tag : Tag)
    (left : tag ≠ rotateLeftTag) (right : tag ≠ rotateRightTag) :
    HeadCase caller regs ctx tag none := by
  refine ⟨?_, parseMoveRun_foreign tag [10, 15] left right⟩
  exact start_step_foreign caller tag [10, 15] [] [] regs ctx left right

theorem all_sixteen_first_head_classifications :
    HeadCase caller regs ctx 0 none ∧ HeadCase caller regs ctx 1 none ∧
    HeadCase caller regs ctx 2 none ∧ HeadCase caller regs ctx 3 none ∧
    HeadCase caller regs ctx 4 none ∧ HeadCase caller regs ctx 5 none ∧
    HeadCase caller regs ctx 6 (some .left) ∧ HeadCase caller regs ctx 7 (some .right) ∧
    HeadCase caller regs ctx 8 none ∧ HeadCase caller regs ctx 9 none ∧
    HeadCase caller regs ctx 10 none ∧ HeadCase caller regs ctx 11 none ∧
    HeadCase caller regs ctx 12 none ∧ HeadCase caller regs ctx 13 none ∧
    HeadCase caller regs ctx 14 none ∧ HeadCase caller regs ctx 15 none := by
  refine ⟨foreign_head_case caller regs ctx 0 (by decide) (by decide),
    foreign_head_case caller regs ctx 1 (by decide) (by decide),
    foreign_head_case caller regs ctx 2 (by decide) (by decide),
    foreign_head_case caller regs ctx 3 (by decide) (by decide),
    foreign_head_case caller regs ctx 4 (by decide) (by decide),
    foreign_head_case caller regs ctx 5 (by decide) (by decide), ?_, ?_,
    foreign_head_case caller regs ctx 8 (by decide) (by decide),
    foreign_head_case caller regs ctx 9 (by decide) (by decide),
    foreign_head_case caller regs ctx 10 (by decide) (by decide),
    foreign_head_case caller regs ctx 11 (by decide) (by decide),
    foreign_head_case caller regs ctx 12 (by decide) (by decide),
    foreign_head_case caller regs ctx 13 (by decide) (by decide),
    foreign_head_case caller regs ctx 14 (by decide) (by decide),
    foreign_head_case caller regs ctx 15 (by decide) (by decide)⟩
  · exact ⟨run_code caller ⟨.left, []⟩ [15] [] regs ctx, parseMoveRun_code ⟨.left, []⟩ [15]⟩
  · exact ⟨run_code caller ⟨.right, []⟩ [15] [] regs ctx, parseMoveRun_code ⟨.right, []⟩ [15]⟩

/-- Directions appearing inside a path are foreign, as are all reserved Tags. -/
theorem all_foreign_path_tags_keep_the_complete_suffix (d : RotationDirection)
    (tag : Tag) (tail : Word) (out : List Branch)
    (foreign : tag ∈ ([0, 1, 2, 3, 4, 5, 6, 7, 11, 12, 13, 14, 15] : List Tag)) :
    (next caller)^[9]
        (some (entry regs (directionTag d :: ([8, 9, 9, tag] ++ tail)) out ctx)) =
      some (cfg (some (resultLabel .failure)) (reset regs)
        (directionTag d :: ([8, 9, 9, tag] ++ tail)) [] out ctx) ∧
    parseMoveRun (directionTag d :: ([8, 9, 9, tag] ++ tail)) = (none, 10) := by
  have ended : tag ≠ endMoveTag := by
    intro equal
    subst tag
    norm_num [endMoveTag] at foreign
  have left : tag ≠ pathLeftTag := by
    intro equal
    subst tag
    norm_num [pathLeftTag] at foreign
  have right : tag ≠ pathRightTag := by
    intro equal
    subst tag
    norm_num [pathRightTag] at foreign
  exact ⟨run_foreign_prefix caller d [.left, .right, .right] tag tail out regs ctx ended left right,
    parseMoveRun_foreign_prefix d [.left, .right, .right] tag tail ended left right⟩

/-- Syntactic recognition does not assert legality at a represented tree. -/
theorem legal_syntax_can_request_an_impossible_rotation :
    (next caller)^[3] (some (entry regs [6, 10] [] ctx)) =
      some (cfg (some (resultLabel (.success .left))) (reset regs) [] [] [] ctx) ∧
    Trees.Rotations.applyMove? (RotationMove.mk .left []) (BinaryTree.nil : BinaryTree Unit) = none :=
  ⟨run_code caller ⟨.left, []⟩ [] [] regs ctx, rfl⟩

end FixedCases

section PrefixContracts
variable {K Λ R : Type} [DecidableEq K] {Γ : K → Type}
variable (caller : External Λ → Statement Γ Λ R)

theorem actual_progress_and_rank (before : Cfg Γ Λ R) (owned : Owned before.l) :
    0 < remainingSteps before ∧
      ∃ after, step caller before = some after ∧ remainingSteps before = remainingSteps after + 1 := by
  have positive := (remainingSteps_pos_iff before).mpr owned
  exact ⟨positive, local_progress caller before positive⟩

theorem each_owned_step_resets_and_conserves_debt {before after : Cfg Γ Λ R}
    (transition : LocalStep caller before after) :
    remainingSteps before = remainingSteps after + 1 ∧ after.var = reset before.var ∧
      (∀ k, after.stk (.inr k) = before.stk (.inr k)) ∧
      ownedCells after + debt after.l = ownedCells before + debt before.l :=
  local_step_data caller transition

theorem every_arbitrary_owned_configuration_returns (start : Cfg Γ Λ R)
    (owned : Owned start.l) :
    ∃ reached, (next caller)^[remainingSteps start] (some start) = some reached ∧
      ¬ Owned reached.l ∧ reached.var = reset start.var ∧
      (∀ k, reached.stk (.inr k) = start.stk (.inr k)) ∧ potential reached = potential start := by
  obtain ⟨reached, executed, rank, _, atReturn, _⟩ :=
    owned_prefix caller start (remainingSteps start) (Nat.le_refl _)
  have positive : 0 < remainingSteps start := (remainingSteps_pos_iff start).mpr owned
  obtain ⟨registers, frame, mass⟩ :=
    prefix_preserves caller start reached (remainingSteps start) (Nat.le_refl _) executed
  refine ⟨reached, executed, ?_, ?_, frame, mass⟩
  · intro bad
    exact (Nat.lt_irrefl _) (atReturn.mpr bad)
  · simpa only [ite_eq_right (Nat.ne_of_gt positive)] using registers

theorem rank_zero_has_only_the_zero_prefix (start : Cfg Γ Λ R)
    (outside : ¬ Owned start.l) (n : Nat) (bound : n ≤ remainingSteps start) :
    n = 0 ∧ (next caller)^[n] (some start) = some start := by
  have zero : remainingSteps start = 0 := by
    have notPositive : ¬ 0 < remainingSteps start :=
      fun positive => outside ((remainingSteps_pos_iff start).mp positive)
    omega
  have count : n = 0 := by omega
  exact ⟨count, by rw [count]; rfl⟩

omit [DecidableEq K] in
theorem all_phase_rank_formulas (d : RotationDirection) (raw : Word) (rev out : List Branch)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    remainingSteps (cfg (Λ := Λ) (some (phaseLabel .start)) regs (directionTag d :: raw) rev out ctx) =
      2 * branchCount raw + rev.length + 3 ∧
    remainingSteps (cfg (Λ := Λ) (some (phaseLabel (.scan d))) regs raw rev out ctx) =
      2 * branchCount raw + rev.length + 2 ∧
    remainingSteps (cfg (Λ := Λ) (some (phaseLabel (.emit d))) regs raw rev out ctx) = rev.length + 1 ∧
    remainingSteps (cfg (Λ := Λ) (some (phaseLabel (.undo d))) regs raw rev out ctx) = rev.length + 1 ∧
    remainingSteps (cfg (Λ := Λ) (some (resultLabel (.success d))) regs raw rev out ctx) = 0 ∧
    remainingSteps (cfg (Λ := Λ) (some (resultLabel .failure)) regs raw rev out ctx) = 0 := by
  refine ⟨?_, rfl, rfl, rfl, rfl, rfl⟩
  change startSteps (directionTag d :: raw) rev = _
  rw [startSteps_direction]
  rfl

omit [DecidableEq K] in
theorem literal_rank_and_debt_domains (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (raw : Word) (rev out : List Branch) (external : Λ) :
    remainingSteps (cfg (Λ := Λ) (some (phaseLabel .start)) regs [] rev out ctx) = 1 ∧
    remainingSteps (cfg (Λ := Λ) (some (phaseLabel .start)) regs (15 :: raw) rev out ctx) = 1 ∧
    remainingSteps (cfg (some (callerLabel external)) regs raw rev out ctx) = 0 ∧
    remainingSteps (cfg (Λ := Λ) none regs raw rev out ctx) = 0 ∧
    debt (some (phaseLabel (Λ := Λ) .start)) = 0 ∧
    debt (some (phaseLabel (Λ := Λ) (.scan .left))) = 1 ∧
    debt (some (phaseLabel (Λ := Λ) (.undo .right))) = 1 ∧
    debt (some (phaseLabel (Λ := Λ) (.emit .right))) = 2 ∧
    debt (some (resultLabel (Λ := Λ) (.success .left))) = 2 ∧
    debt (some (resultLabel (Λ := Λ) .failure)) = 0 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem every_inclusive_owned_prefix (start : Cfg Γ Λ R) (n : Nat)
    (bound : n ≤ remainingSteps start) :
    ∃ reached, (next caller)^[n] (some start) = some reached ∧
      remainingSteps reached = remainingSteps start - n ∧
      Relation.ReflTransGen (LocalStep caller) start reached ∧
      (n < remainingSteps start ↔ Owned reached.l) ∧ (0 < n → reached.var.1 = none) :=
  owned_prefix caller start n bound

theorem exact_first_handoff (start reached : Cfg Γ Λ R) (n : Nat)
    (bound : n ≤ remainingSteps start)
    (executed : (next caller)^[n] (some start) = some reached) (returned : ¬ Owned reached.l) :
    n = remainingSteps start := first_return_exact caller start reached n bound executed returned

theorem arbitrary_local_paths_preserve_caller_and_potential {start reached : Cfg Γ Λ R}
    (path : Relation.ReflTransGen (LocalStep caller) start reached) :
    reached.var.2 = start.var.2 ∧ (∀ k, reached.stk (.inr k) = start.stk (.inr k)) ∧
      potential reached = potential start := local_reaches_preserves caller path

theorem zero_and_positive_prefixes_keep_the_exact_registers (start reached : Cfg Γ Λ R)
    (n : Nat) (bound : n ≤ remainingSteps start)
    (executed : (next caller)^[n] (some start) = some reached) :
    reached.var = (if n = 0 then start.var else reset start.var) ∧
      (∀ k, reached.stk (.inr k) = start.stk (.inr k)) ∧ potential reached = potential start :=
  prefix_preserves caller start reached n bound executed

theorem callers_agree_on_the_exact_owned_prefix (other : External Λ → Statement Γ Λ R)
    (start : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start) :
    (next caller)^[n] (some start) = (next other)^[n] (some start) :=
  prefix_caller_independent caller other start n bound

theorem ambient_program_agreement_needs_only_owned_blocks
    (ambient : Label Λ → Statement Γ Λ R)
    (agrees : ∀ phase, ambient (phaseLabel phase) = block phase)
    (start : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start) :
    (fun c : Option (Cfg Γ Λ R) => c.bind (Turing.TM2.step ambient))^[n] (some start) =
      (next caller)^[n] (some start) := ambient_prefix_eq caller ambient agrees start n bound

def exactRunTime (raw : Word) (out : List Branch) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller) (entry regs raw out ctx)
      (some (resultCfg regs raw out ctx (parseMoveRun raw).1)) (fullSteps raw) :=
  runInTime caller raw out regs ctx

def linearRunTime (raw : Word) (out : List Branch) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller) (entry regs raw out ctx)
      (some (resultCfg regs raw out ctx (parseMoveRun raw).1)) (2 * raw.length + 1) :=
  runInLinearTime caller raw out regs ctx

def dirtyPhaseTime (phase : Phase) (raw : Word) (rev out : List Branch)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller) (cfg (some (phaseLabel phase)) regs raw rev out ctx)
      (some (phaseResult phase regs raw rev out ctx)) (phaseSteps phase raw rev) :=
  phaseInTime caller phase raw rev out regs ctx

theorem timed_data_keeps_the_actual_exact_steps (raw : Word) (out : List Branch)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (exactRunTime caller raw out regs ctx).steps = fullSteps raw ∧
      (linearRunTime caller raw out regs ctx).steps = fullSteps raw := ⟨rfl, rfl⟩

section PhysicalSpace
variable [Fintype K]

omit [DecidableEq K] in
/-- The local notation is the actual unweighted sum over all physical stacks. -/
theorem physical_cells_are_the_full_dependent_sum (c : Cfg Γ Λ R) :
    stackCells c = ∑ k : StackId K, (c.stk k).length := stackCells_eq_sum c

theorem every_full_prefix_preserves_fields_and_mass (raw : Word) (out : List Branch)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) (n : Nat) (bound : n ≤ fullSteps raw)
    (reached : Cfg Γ Λ R)
    (executed : (next caller)^[n] (some (entry regs raw out ctx)) = some reached) :
    reached.var = (if n = 0 then regs else reset regs) ∧
      (∀ k, reached.stk (.inr k) = ctx k) ∧
      ownedCells reached + debt reached.l = raw.length + out.length ∧
      stackCells reached ≤ raw.length + out.length + contextCells ctx := by
  obtain ⟨registers, frame, mass⟩ := run_prefix_preserves caller raw out regs ctx n bound reached executed
  exact ⟨registers, frame, mass, prefix_stackCells_le caller raw out regs ctx n bound reached executed⟩

theorem every_dirty_prefix_uses_its_initial_debt (start reached : Cfg Γ Λ R)
    (n : Nat) (bound : n ≤ remainingSteps start)
    (executed : (next caller)^[n] (some start) = some reached) :
    stackCells reached ≤ ownedCells start + debt start.l +
      contextCells (fun k => start.stk (.inr k)) :=
  owned_prefix_stackCells_le caller start reached n bound executed

theorem malformed_family_attains_both_bounds (n : Nat) (out : List Branch)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (sharpRaw n).length = n ∧ fullSteps (sharpRaw n) = 2 * n + 1 ∧
      parseMoveRun (sharpRaw n) = (none, 2 * n + 2) ∧
      ∃ reached, (next caller)^[2 * n + 1] (some (entry regs (sharpRaw n) out ctx)) = some reached ∧
        ¬ Owned reached.l ∧ stackCells reached = n + out.length + contextCells ctx ∧ 0 < 2 * n + 1 :=
  ⟨sharpRaw_length n, fullSteps_sharpRaw n, parseMoveRun_sharpRaw n,
    space_bound_sharp caller n out regs ctx⟩

omit [Fintype K] in
theorem malformed_sharp_prefixes_are_strictly_owned (n : Nat) (out : List Branch)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) (j : Nat) (strict : j < 2 * n + 1) :
    ∃ reached, (next caller)^[j] (some (entry regs (sharpRaw n) out ctx)) = some reached ∧
      Owned reached.l := sharpRaw_first_return caller n out regs ctx j strict

end PhysicalSpace
end PrefixContracts

/-- All seventeen stale OptionTag values and both caller flags are covered. -/
theorem every_stale_value_and_caller_flag (temporary : Option Tag) (flag : Bool) :
    (next haltCaller)^[3] (some (entry (temporary, flag) [7, 10] [.left] sampleContext)) =
      some (cfg (some (resultLabel (.success .right))) (none, flag) [] [] [.left] sampleContext) ∧
    (next haltCaller)^[5] (some (entry (temporary, flag) [7, 8, 15, 9] [.left] sampleContext)) =
      some (cfg (some (resultLabel .failure)) (none, flag) [7, 8, 15, 9] [] [.left] sampleContext) :=
  ⟨run_code haltCaller ⟨.right, []⟩ [] [.left] (temporary, flag) sampleContext,
    run_foreign_prefix haltCaller .right [.left] 15 [9] [.left] (temporary, flag) sampleContext
      (by decide) (by decide) (by decide)⟩

theorem false_caller_flag_is_preserved :
    (next haltCaller)^[3] (some (entry (stale false) [7, 10] [.left] sampleContext)) =
      some (cfg (some (resultLabel (.success .right))) (none, false) [] [] [.left] sampleContext) :=
  (every_stale_value_and_caller_flag (some 15) false).1

theorem literal_sharp_family_zero_one_two_four :
    (next haltCaller)^[1] (some (entry (stale true) [] [] sampleContext)) =
      some (cfg (some (resultLabel .failure)) (none, true) [] [] [] sampleContext) ∧
    (next haltCaller)^[3] (some (entry (stale true) [6] [] sampleContext)) =
      some (cfg (some (resultLabel .failure)) (none, true) [6] [] [] sampleContext) ∧
    (next haltCaller)^[5] (some (entry (stale true) [6, 8] [] sampleContext)) =
      some (cfg (some (resultLabel .failure)) (none, true) [6, 8] [] [] sampleContext) ∧
    (next haltCaller)^[9] (some (entry (stale true) [6, 8, 8, 8] [] sampleContext)) =
      some (cfg (some (resultLabel .failure)) (none, true) [6, 8, 8, 8] [] [] sampleContext) :=
  ⟨run_sharpRaw haltCaller 0 [] (stale true) sampleContext,
    run_sharpRaw haltCaller 1 [] (stale true) sampleContext,
    run_sharpRaw haltCaller 2 [] (stale true) sampleContext,
    run_sharpRaw haltCaller 4 [] (stale true) sampleContext⟩

/-- Both live success directions and failure execute this real caller block. -/
def sentinelCaller (marker : Bool) : External Unit → Statement SmallAlphabet Unit Bool
  | .inl _ => .push (.inr false) (fun _ => marker) .halt
  | .inr _ => .halt

def sentinelSuccessStart : Cfg SmallAlphabet Unit Bool :=
  entry (stale true) [7, 10] [] sampleContext

def sentinelSuccessHandoff : Cfg SmallAlphabet Unit Bool :=
  cfg (some (resultLabel (.success .right))) (none, true) [] [] [] sampleContext

def sentinelSuccessAfterCaller (marker : Bool) : Cfg SmallAlphabet Unit Bool :=
  cfg none (none, true) [] [] [] (smallContext (marker :: [true, false, true]) [15, 6, 1])

def sentinelFailureStart : Cfg SmallAlphabet Unit Bool :=
  entry (stale true) [15] [] sampleContext

def sentinelFailureHandoff : Cfg SmallAlphabet Unit Bool :=
  cfg (some (resultLabel .failure)) (none, true) [15] [] [] sampleContext

def sentinelFailureAfterCaller (marker : Bool) : Cfg SmallAlphabet Unit Bool :=
  cfg none (none, true) [15] [] [] (smallContext (marker :: [true, false, true]) [15, 6, 1])

theorem actual_sentinel_push (marker : Bool) (result : Result) (regs : Registers Bool)
    (raw : Word) (rev out : List Branch) (bits : List Bool) (tags : Word) :
    step (sentinelCaller marker)
        (cfg (some (resultLabel result)) regs raw rev out (smallContext bits tags)) =
      some (cfg none regs raw rev out (smallContext (marker :: bits) tags)) := by
  apply congrArg some
  apply cfg_ext
  all_goals first | rfl | (intro k; cases k <;> rfl)

def sentinelSuccessTime (marker : Bool) :
    StateTransition.EvalsToInTime (step (sentinelCaller marker)) sentinelSuccessStart
      (some sentinelSuccessHandoff) 3 :=
  runInTime (sentinelCaller marker) [7, 10] [] (stale true) sampleContext

def sentinelFailureTime (marker : Bool) :
    StateTransition.EvalsToInTime (step (sentinelCaller marker)) sentinelFailureStart
      (some sentinelFailureHandoff) 1 :=
  runInTime (sentinelCaller marker) [15] [] (stale true) sampleContext

def sentinelSuccessCallerTime (marker : Bool) :
    StateTransition.EvalsToInTime (step (sentinelCaller marker)) sentinelSuccessHandoff
      (some (sentinelSuccessAfterCaller marker)) 1 where
  steps := 1
  evals_in_steps := actual_sentinel_push marker (.success .right) (none, true) [] [] []
    [true, false, true] [15, 6, 1]
  steps_le_m := Nat.le_refl _

def sentinelFailureCallerTime (marker : Bool) :
    StateTransition.EvalsToInTime (step (sentinelCaller marker)) sentinelFailureHandoff
      (some (sentinelFailureAfterCaller marker)) 1 where
  steps := 1
  evals_in_steps := actual_sentinel_push marker .failure (none, true) [15] [] []
    [true, false, true] [15, 6, 1]
  steps_le_m := Nat.le_refl _

/-- The actual constructor orders the bound as continuation plus component. -/
def sentinelSuccessCompositionTime (marker : Bool) :
    StateTransition.EvalsToInTime (step (sentinelCaller marker)) sentinelSuccessStart
      (some (sentinelSuccessAfterCaller marker)) 4 :=
  StateTransition.EvalsToInTime.trans (step (sentinelCaller marker)) 3 1
    sentinelSuccessStart sentinelSuccessHandoff (some (sentinelSuccessAfterCaller marker))
    (sentinelSuccessTime marker) (sentinelSuccessCallerTime marker)

def sentinelFailureCompositionTime (marker : Bool) :
    StateTransition.EvalsToInTime (step (sentinelCaller marker)) sentinelFailureStart
      (some (sentinelFailureAfterCaller marker)) 2 :=
  StateTransition.EvalsToInTime.trans (step (sentinelCaller marker)) 1 1
    sentinelFailureStart sentinelFailureHandoff (some (sentinelFailureAfterCaller marker))
    (sentinelFailureTime marker) (sentinelFailureCallerTime marker)

def sentinelSuccessHaltTime (marker : Bool) :
    StateTransition.EvalsToInTime (step (sentinelCaller marker)) (sentinelSuccessAfterCaller marker)
      none 1 where
  steps := 1
  evals_in_steps := rfl
  steps_le_m := Nat.le_refl _

def sentinelSuccessOuterNoneTime (marker : Bool) :
    StateTransition.EvalsToInTime (step (sentinelCaller marker)) sentinelSuccessStart none 5 :=
  StateTransition.EvalsToInTime.trans (step (sentinelCaller marker)) 4 1
    sentinelSuccessStart (sentinelSuccessAfterCaller marker) none
    (sentinelSuccessCompositionTime marker) (sentinelSuccessHaltTime marker)

theorem successful_sentinel_has_three_distinct_observations (marker : Bool) :
    (next (sentinelCaller marker))^[3] (some sentinelSuccessStart) = some sentinelSuccessHandoff ∧
    sentinelSuccessHandoff.stk (.inr false) = [true, false, true] ∧
    (next (sentinelCaller marker))^[4] (some sentinelSuccessStart) =
      some (sentinelSuccessAfterCaller marker) ∧
    (sentinelSuccessAfterCaller marker).l = none ∧
    (sentinelSuccessAfterCaller marker).stk (.inr false) = marker :: [true, false, true] ∧
    (next (sentinelCaller marker))^[5] (some sentinelSuccessStart) = none :=
  ⟨(sentinelSuccessTime marker).evals_in_steps, rfl,
    (sentinelSuccessCompositionTime marker).evals_in_steps, rfl, rfl,
    (sentinelSuccessOuterNoneTime marker).evals_in_steps⟩

theorem failed_sentinel_has_three_distinct_observations (marker : Bool) :
    (next (sentinelCaller marker))^[1] (some sentinelFailureStart) = some sentinelFailureHandoff ∧
    sentinelFailureHandoff.stk (.inr false) = [true, false, true] ∧
    (next (sentinelCaller marker))^[2] (some sentinelFailureStart) =
      some (sentinelFailureAfterCaller marker) ∧
    (sentinelFailureAfterCaller marker).l = none ∧
    (sentinelFailureAfterCaller marker).stk (.inr false) = marker :: [true, false, true] ∧
    (next (sentinelCaller marker))^[3] (some sentinelFailureStart) = none := by
  have completed : (next (sentinelCaller marker))^[2] (some sentinelFailureStart) =
      some (sentinelFailureAfterCaller marker) := (sentinelFailureCompositionTime marker).evals_in_steps
  refine ⟨(sentinelFailureTime marker).evals_in_steps, rfl, completed, rfl, rfl, ?_⟩
  rw [show 3 = 2 + 1 by rfl, Function.iterate_succ_apply', completed]
  rfl

theorem two_callers_agree_until_the_first_return (n : Nat) (bound : n ≤ 3) :
    (next (sentinelCaller false))^[n] (some sentinelSuccessStart) =
      (next (sentinelCaller true))^[n] (some sentinelSuccessStart) :=
  run_prefix_caller_independent (sentinelCaller false) (sentinelCaller true)
    [7, 10] [] (stale true) sampleContext n bound

theorem two_callers_really_differ_after_the_return :
    (next (sentinelCaller false))^[4] (some sentinelSuccessStart) =
      some (sentinelSuccessAfterCaller false) ∧
    (next (sentinelCaller true))^[4] (some sentinelSuccessStart) =
      some (sentinelSuccessAfterCaller true) ∧
    sentinelSuccessAfterCaller false ≠ sentinelSuccessAfterCaller true := by
  refine ⟨(sentinelSuccessCompositionTime false).evals_in_steps,
    (sentinelSuccessCompositionTime true).evals_in_steps, ?_⟩
  intro same
  have lists := congrArg (fun c : Cfg SmallAlphabet Unit Bool => c.stk (.inr false)) same
  have heads := congrArg List.head? lists
  cases heads

/-- Every external activation allocates a real protected cell and stays outside. -/
def allocatingCaller : External Unit → Statement SmallAlphabet Unit Bool :=
  fun _ => .push (.inr false) (fun _ => true) (.goto (fun _ => callerLabel ()))

theorem actual_allocating_step (external : External Unit) (regs : Registers Bool)
    (raw : Word) (rev out : List Branch) (bits : List Bool) (tags : Word) :
    step allocatingCaller (cfg (some (.inr external)) regs raw rev out (smallContext bits tags)) =
      some (cfg (some (callerLabel ())) regs raw rev out (smallContext (true :: bits) tags)) := by
  apply congrArg some
  apply cfg_ext
  all_goals first | rfl | (intro k; cases k <;> rfl)

theorem caller_allocation_exceeds_the_owned_bound :
    (next allocatingCaller)^[1] (some sentinelFailureStart) = some sentinelFailureHandoff ∧
    (next allocatingCaller)^[2] (some sentinelFailureStart) =
      some (cfg (some (callerLabel ())) (none, true) [15] [] []
        (smallContext [true, true, false, true] [15, 6, 1])) ∧
    (next allocatingCaller)^[3] (some sentinelFailureStart) =
      some (cfg (some (callerLabel ())) (none, true) [15] [] []
        (smallContext [true, true, true, false, true] [15, 6, 1])) ∧
    stackCells sentinelFailureStart = 7 ∧ stackCells sentinelFailureHandoff = 7 ∧
    stackCells (cfg (Λ := Unit) (some (callerLabel ())) (none, true) [15] [] []
      (smallContext [true, true, false, true] [15, 6, 1])) = 8 ∧
    stackCells (cfg (Λ := Unit) (some (callerLabel ())) (none, true) [15] [] []
      (smallContext [true, true, true, false, true] [15, 6, 1])) = 9 := by
  have first : (next allocatingCaller)^[1] (some sentinelFailureStart) = some sentinelFailureHandoff :=
    run_of_none allocatingCaller [15] [] (stale true) sampleContext rfl
  have second : (next allocatingCaller)^[2] (some sentinelFailureStart) =
      some (cfg (some (callerLabel ())) (none, true) [15] [] []
        (smallContext [true, true, false, true] [15, 6, 1])) := by
    rw [show 2 = 1 + 1 by rfl, Function.iterate_succ_apply', first, next_some]
    exact actual_allocating_step (.inl .failure) (none, true) [15] [] []
      [true, false, true] [15, 6, 1]
  refine ⟨first, second, ?_, by decide, by decide, by decide, by decide⟩
  rw [show 3 = 2 + 1 by rfl, Function.iterate_succ_apply', second, next_some]
  exact actual_allocating_step (.inr ()) (none, true) [15] [] []
    [true, true, false, true] [15, 6, 1]

def misleadingCaller : External Unit → Statement SmallAlphabet Unit Bool
  | .inl .failure => .goto (fun _ => resultLabel (.success .left))
  | _ => .halt

theorem eventual_success_is_not_first_success :
    (next misleadingCaller)^[1] (some sentinelFailureStart) = some sentinelFailureHandoff ∧
    (next misleadingCaller)^[2] (some sentinelFailureStart) =
      some (cfg (some (resultLabel (.success .left))) (none, true) [15] [] [] sampleContext) ∧
    (parseMoveRun [15]).1 = none ∧
    ¬ FirstSuccess misleadingCaller [15] ⟨.left, []⟩ [15] [] (stale true) sampleContext := by
  have first : (next misleadingCaller)^[1] (some sentinelFailureStart) = some sentinelFailureHandoff :=
    run_of_none misleadingCaller [15] [] (stale true) sampleContext rfl
  refine ⟨first, ?_, rfl, ?_⟩
  · rw [show 2 = 1 + 1 by rfl, Function.iterate_succ_apply', first]
    rfl
  · rw [firstSuccess_iff]
    intro impossible
    cases impossible

/-- One actual finite package is selected before its raw input. -/
def concreteMachine : Turing.FinTM2 := machine (sentinelCaller true) true

theorem package_has_the_actual_carriers :
    @Fintype.card concreteMachine.K concreteMachine.kFin = 5 ∧
    @Fintype.card concreteMachine.Λ concreteMachine.ΛFin = 11 ∧
    @Fintype.card concreteMachine.σ concreteMachine.σFin = 34 := by
  exact ⟨actual_finite_carrier_counts.1, actual_finite_carrier_counts.2.1,
    actual_finite_carrier_counts.2.2.1⟩

theorem package_input_output_and_initial_control :
    concreteMachine.k₀ = (.inl .raw : StackId Bool) ∧
      concreteMachine.k₁ = (.inl .path : StackId Bool) ∧
      concreteMachine.main = phaseLabel .start ∧ concreteMachine.initialState = (none, true) :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem package_all_alphabets_are_available (k : concreteMachine.K) :
    Nonempty (Fintype (concreteMachine.Γ k)) := ⟨alphabetFintype k⟩

theorem actual_one_input_initialization (raw : Word) :
    Turing.initList concreteMachine raw =
      cfg (some (phaseLabel .start)) (none, true) raw [] [] (fun _ => []) :=
  initList_eq (sentinelCaller true) true raw

theorem package_step_is_the_installed_step (c : Cfg SmallAlphabet Unit Bool) :
    concreteMachine.step c = step (sentinelCaller true) c :=
  machine_step_eq (sentinelCaller true) true c

theorem actual_package_run (raw : Word) :
    (fun c : Option (Cfg SmallAlphabet Unit Bool) => c.bind concreteMachine.step)^[fullSteps raw]
        (some (Turing.initList concreteMachine raw)) =
      some (resultCfg (none, true) raw [] (fun _ => []) (parseMoveRun raw).1) :=
  machine_run_source (sentinelCaller true) true raw

def actualPackageTime (raw : Word) :
    StateTransition.EvalsToInTime concreteMachine.step (Turing.initList concreteMachine raw)
      (some (resultCfg (none, true) raw [] (fun _ => []) (parseMoveRun raw).1)) (fullSteps raw) :=
  machineRunInTime (sentinelCaller true) true raw

def actualPackageLinearTime (raw : Word) :
    StateTransition.EvalsToInTime concreteMachine.step (Turing.initList concreteMachine raw)
      (some (resultCfg (none, true) raw [] (fun _ => []) (parseMoveRun raw).1)) (2 * raw.length + 1) :=
  machineRunInLinearTime (sentinelCaller true) true raw

theorem package_prefixes_use_only_initial_raw_cells (raw : Word) (n : Nat)
    (bound : n ≤ fullSteps raw) (reached : Cfg SmallAlphabet Unit Bool)
    (executed :
      (fun c : Option (Cfg SmallAlphabet Unit Bool) => c.bind concreteMachine.step)^[n]
        (some (Turing.initList concreteMachine raw)) = some reached) :
    stackCells reached ≤ raw.length :=
  machine_prefix_stackCells_le (sentinelCaller true) true raw n bound reached executed

theorem package_returns_a_live_result_before_its_caller :
    (fun c : Option (Cfg SmallAlphabet Unit Bool) => c.bind concreteMachine.step)^[3]
        (some (Turing.initList concreteMachine ([7, 10] : Word))) =
      some (cfg (some (resultLabel (.success .right))) (none, true) [] [] [] (fun _ => [])) ∧
    (fun c : Option (Cfg SmallAlphabet Unit Bool) => c.bind concreteMachine.step)^[1]
        (some (Turing.initList concreteMachine ([15] : Word))) =
      some (cfg (some (resultLabel .failure)) (none, true) [15] [] [] (fun _ => [])) :=
  ⟨actual_package_run [7, 10], actual_package_run [15]⟩

theorem source_prefix_injectivity_preserves_move_and_suffix
    (move other : RotationMove) (rest suffix : Word)
    (same : moveCode move ++ rest = moveCode other ++ suffix) :
    move = other ∧ rest = suffix := parseMoveRun_prefix_injective move other rest suffix same

end Examples.RotationCertificateMoveParserMachine
