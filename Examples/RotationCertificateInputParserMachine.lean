import Applications.Resources.RotationCertificate.InputParserMachine
import Examples.RotationCertificateParsing

/-!
# Connected executions of the complete represented input parser

The values, counts, dirty-accumulator orientations and caller boundaries were
fixed before implementation in the maintained input-machine cases and checked
independently. These clients use the installed finite program, its actual tree
bridges and actual returned configurations. Source work and machine transitions
remain separate observations. The complete verifier and its model correspondence
are subsequent obligations.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.RotationCertificateInputParserMachine
open Trees Resources
open Resources.BinaryCounter (Bits)
open Resources.RotationCertificate
open InputParserMachine
open RotationDistanceExample (empty singleton leftTwo rightTwo)

def SmallAlphabet : Bool → Type
  | false => Bool
  | true => Tag

instance smallAlphabetFintype (k : Bool) : Fintype (SmallAlphabet k) := by
  cases k with
  | false => change Fintype Bool; infer_instance
  | true => change Fintype Tag; infer_instance

def smallContext (bits : Bits) (certificate : Word) : ∀ k, List (SmallAlphabet k)
  | false => bits
  | true => certificate

def sampleContext : ∀ k, List (SmallAlphabet k) :=
  smallContext [false, true, false] [15, 6, nodeTag]

def staleRegisters : Registers Bool := ((some 15, some ()), true)

def haltCaller : External Unit → Statement SmallAlphabet Unit Bool := fun _ => .halt

instance fullOwnedDecidable (label : Label Unit) : Decidable (FullOwned (some label)) := by
  cases label with
  | inl pair => exact isTrue True.intro
  | inr external =>
      cases external with
      | inl pair =>
          rcases pair with ⟨side, result⟩
          cases side <;> cases result <;> dsimp only [FullOwned] <;> infer_instance
      | inr extra =>
          cases extra with
          | inl phase => exact isTrue True.intro
          | inr rest => exact isFalse id

theorem actual_control_and_owned_labels_are_finite :
    Fintype.card (StackId Bool) = 9 ∧
      Fintype.card (Label Unit) = 28 ∧
      Fintype.card (Registers Bool) = 68 ∧
      Fintype.card {label : Label Unit // FullOwned (some label)} = 25 := by
  decide

/-- Both nonterminal tree results remain owned by the full parser. -/
theorem intermediate_tree_results_are_not_full_returns :
    FullOwned (some (treeResultLabel (Λ := Unit) .source .success)) ∧
      FullOwned (some (treeResultLabel (Λ := Unit) .target .failure)) ∧
      ¬ TreeParserMachine.Owned (some (treeResultLabel (Λ := Unit) .source .success)) ∧
      ¬ FullOwned (some (resultLabel (Λ := Unit) .success)) ∧
      ¬ FullOwned (some (resultLabel (Λ := Unit) .failure)) :=
  ⟨True.intro, True.intro, id, id, id⟩

section Context
variable {K Λ R : Type} [DecidableEq K] {Γ : K → Type}
variable (caller : External Λ → Statement Γ Λ R)
variable (regs : Registers R) (ctx : ∀ k, List (Γ k))

/-- The separator is consumed in the actual source-tree result block, without a routing step. -/
theorem source_return_itself_consumes_the_separator
    [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
    (raw rev : Word) (pending : List Unit) (outputs : TreeSide → Word)
    (fuel bitsReverse : Bits) :
    step caller (cfg (some (treeResultLabel .source .success)) regs
        (separatorTag :: raw) rev pending outputs fuel bitsReverse ctx) =
      some (cfg (some (treeLabel .target .init)) (reset regs)
        raw rev pending outputs fuel bitsReverse ctx) :=
  separator_step_separator caller .source raw rev pending regs outputs fuel bitsReverse ctx

/-- Target failure performs the real restoration push before source rollback begins. -/
theorem target_failure_is_a_restore_step
    [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
    (raw rev : Word) (pending : List Unit) (outputs : TreeSide → Word)
    (fuel bitsReverse : Bits) :
    step caller (cfg (some (treeResultLabel .target .failure)) regs
        raw rev pending outputs fuel bitsReverse ctx) =
      some (cfg (some (phaseLabel .sourceToReverse)) (reset regs)
        (separatorTag :: raw) rev pending outputs fuel bitsReverse ctx) :=
  targetFailure_step caller raw rev pending regs outputs fuel bitsReverse ctx

/-- An invalid separator head and every following tag stay on raw during the failed probe. -/
theorem separator_failure_does_not_consume_the_blocker
    [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
    (d : TreeSide) (tag : Tag) (tail rev : Word) (pending : List Unit)
    (outputs : TreeSide → Word) (fuel bitsReverse : Bits) (different : tag ≠ separatorTag) :
    step caller (cfg (some (treeResultLabel d .success)) regs
        (tag :: tail) rev pending outputs fuel bitsReverse ctx) =
      some (cfg (some (phaseLabel (toReversePhase d))) (reset regs)
        (tag :: tail) rev pending outputs fuel bitsReverse ctx) :=
  separator_step_foreign caller d tag tail rev pending regs outputs fuel bitsReverse ctx different

/-- Empty input and an unfinished first tree return only after actual tree cleanup. -/
theorem initial_tree_failures_restore_every_owned_stack
    [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)] :
    (next caller)^[5] (some (entry regs [] ctx)) = some (resultCfg regs [] ctx none) ∧
      (next caller)^[8] (some (entry regs [nodeTag] ctx)) =
        some (resultCfg regs [nodeTag] ctx none) :=
  ⟨(run_tree_failure_trace caller [] regs ctx rfl).iterate caller,
    (run_tree_failure_trace caller [nodeTag] regs ctx rfl).iterate caller⟩

/-- No part of the arbitrary tail behind a reserved tree tag is parsed. -/
theorem reserved_first_tree_tag_keeps_its_entire_tail
    [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)] (tail : Word) :
    (next caller)^[5] (some (entry regs (15 :: tail) ctx)) =
      some (resultCfg regs (15 :: tail) ctx none) :=
  (run_tree_failure_trace caller (15 :: tail) regs ctx rfl).iterate caller

/-- Syntactic acceptance retains both actual shapes, including unequal endpoint sizes. -/
theorem literal_successes_keep_their_actual_shapes_and_fuel
    [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)] :
    (next caller)^[13]
        (some (entry regs [emptyTag, separatorTag, emptyTag, separatorTag, endInputTag] ctx)) =
      some (cfg (some (resultLabel .success)) (reset regs) [] [] []
        (treeOutputs [emptyTag] [emptyTag]) [] [] ctx) ∧
    (next caller)^[31]
        (some (entry regs [nodeTag, nodeTag, emptyTag, emptyTag, emptyTag, separatorTag,
          nodeTag, emptyTag, nodeTag, emptyTag, emptyTag, separatorTag, bitOneTag, endInputTag] ctx)) =
      some (cfg (some (resultLabel .success)) (reset regs) [] [] []
        (treeOutputs [nodeTag, nodeTag, emptyTag, emptyTag, emptyTag]
          [nodeTag, emptyTag, nodeTag, emptyTag, emptyTag]) [true] [] ctx) ∧
    (next caller)^[17]
        (some (entry regs [emptyTag, separatorTag, nodeTag, emptyTag, emptyTag,
          separatorTag, endInputTag] ctx)) =
      some (cfg (some (resultLabel .success)) (reset regs) [] [] []
        (treeOutputs [emptyTag] [nodeTag, emptyTag, emptyTag]) [] [] ctx) :=
  ⟨(run_code_trace caller empty.val empty.val [] regs ctx).iterate caller,
    (run_code_trace caller leftTwo.val rightTwo.val [true] regs ctx).iterate caller,
    (run_code_trace caller empty.val singleton.val [] regs ctx).iterate caller⟩

/-- Each missing part selects its distinct real rollback path. -/
theorem missing_input_parts_have_the_fixed_failure_times
    [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)] :
    (next caller)^[9] (some (entry regs [emptyTag] ctx)) =
        some (resultCfg regs [emptyTag] ctx none) ∧
      (next caller)^[15] (some (entry regs [emptyTag, separatorTag] ctx)) =
        some (resultCfg regs [emptyTag, separatorTag] ctx none) ∧
      (next caller)^[18] (some (entry regs [emptyTag, separatorTag, nodeTag] ctx)) =
        some (resultCfg regs [emptyTag, separatorTag, nodeTag] ctx none) ∧
      (next caller)^[19] (some (entry regs [emptyTag, separatorTag, emptyTag] ctx)) =
        some (resultCfg regs [emptyTag, separatorTag, emptyTag] ctx none) ∧
      (next caller)^[22] (some (entry regs [emptyTag, separatorTag, emptyTag, separatorTag] ctx)) =
        some (resultCfg regs [emptyTag, separatorTag, emptyTag, separatorTag] ctx none) ∧
      (next caller)^[24]
        (some (entry regs [emptyTag, separatorTag, emptyTag, separatorTag, bitZeroTag] ctx)) =
        some (resultCfg regs [emptyTag, separatorTag, emptyTag, separatorTag, bitZeroTag] ctx none) :=
  ⟨(run_firstSeparator_failure_trace caller empty.val [] regs ctx rfl).iterate caller,
    (run_target_failure_trace caller empty.val [] regs ctx rfl).iterate caller,
    (run_target_failure_trace caller empty.val [nodeTag] regs ctx rfl).iterate caller,
    (run_secondSeparator_failure_trace caller empty.val empty.val [] regs ctx rfl).iterate caller,
    (run_bits_failure_trace caller empty.val empty.val [] [] regs ctx True.intro).iterate caller,
    (run_bits_failure_trace caller empty.val empty.val [false] [] regs ctx True.intro).iterate caller⟩

/-- Foreign material at each boundary is retained, including every uninspected suffix. -/
theorem foreign_boundary_failures_restore_the_whole_original_word
    [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)] (tail : Word) :
    (next caller)^[9] (some (entry regs (emptyTag :: 15 :: tail) ctx)) =
        some (resultCfg regs (emptyTag :: 15 :: tail) ctx none) ∧
      (next caller)^[15] (some (entry regs (emptyTag :: separatorTag :: 15 :: tail) ctx)) =
        some (resultCfg regs (emptyTag :: separatorTag :: 15 :: tail) ctx none) ∧
      (next caller)^[19]
        (some (entry regs (emptyTag :: separatorTag :: emptyTag :: 15 :: tail) ctx)) =
        some (resultCfg regs (emptyTag :: separatorTag :: emptyTag :: 15 :: tail) ctx none) ∧
      (next caller)^[24]
        (some (entry regs (emptyTag :: separatorTag :: emptyTag :: separatorTag :: bitZeroTag :: 15 :: tail) ctx)) =
        some (resultCfg regs
          (emptyTag :: separatorTag :: emptyTag :: separatorTag :: bitZeroTag :: 15 :: tail) ctx none) ∧
      (next caller)^[26]
        (some (entry regs (emptyTag :: separatorTag :: emptyTag :: separatorTag :: endInputTag :: 15 :: tail) ctx)) =
        some (resultCfg regs
          (emptyTag :: separatorTag :: emptyTag :: separatorTag :: endInputTag :: 15 :: tail) ctx none) :=
  ⟨(run_firstSeparator_failure_trace caller empty.val (15 :: tail) regs ctx rfl).iterate caller,
    (run_target_failure_trace caller empty.val (15 :: tail) regs ctx rfl).iterate caller,
    (run_secondSeparator_failure_trace caller empty.val empty.val (15 :: tail) regs ctx rfl).iterate caller,
    (run_bits_failure_trace caller empty.val empty.val [false] (15 :: tail) regs ctx
      ⟨by decide, by decide, by decide⟩).iterate caller,
    (run_trailing_trace caller empty.val empty.val [] (15 :: tail) regs ctx (by simp)).iterate caller⟩

/-- A nonempty old fuel suffix survives the actual reverse transfer. -/
theorem dirty_bits_emit_retains_the_old_fuel_suffix
    [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
    (raw rev : Word) (pending : List Unit) (outputs : TreeSide → Word) (fuel : Bits) :
    (next caller)^[4]
        (some (cfg (some (phaseLabel .bitsEmit)) regs raw rev pending outputs
          fuel [false, true, true] ctx)) =
      some (cfg (some (phaseLabel .eof)) (reset regs) raw rev pending outputs
        ([true, true, false] ++ fuel) [] ctx) :=
  (bitsEmit_run caller raw rev pending regs outputs fuel [false, true, true] ctx).iterate caller

/-- The actual intermediate reverse word is the input to the next rollback loop. -/
theorem dirty_fuel_rollback_preserves_the_accumulator
    [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
    (raw rev : Word) (pending : List Unit) (outputs : TreeSide → Word)
    (fuel bitsReverse : Bits) :
    (next caller)^[fuel.length + 1]
        (some (cfg (some (phaseLabel .fuelUndo)) regs raw rev pending outputs fuel bitsReverse ctx)) =
      some (cfg (some (phaseLabel .bitsUndo)) (reset regs) raw rev pending outputs
        [] (fuel.reverse ++ bitsReverse) ctx) ∧
      (next caller)^[2 * fuel.length + bitsReverse.length + 2]
        (some (cfg (some (phaseLabel .fuelUndo)) regs raw rev pending outputs fuel bitsReverse ctx)) =
      some (cfg (some (phaseLabel .restoreSep2)) (reset regs)
        (bitTags (bitsReverse.reverse ++ fuel) ++ raw) rev pending outputs [] [] ctx) :=
  ⟨(fuelUndo_run caller raw rev pending regs outputs fuel bitsReverse ctx).iterate caller,
    (fuelBitsUndo_run caller raw rev pending regs outputs fuel bitsReverse ctx).iterate caller⟩

/-- A dirty reverse accumulator contributes both real tags and two extra transfers here. -/
theorem dirty_five_bit_rollback_takes_fourteen_steps
    [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
    (raw rev : Word) (pending : List Unit) (outputs : TreeSide → Word) :
    (next caller)^[14]
        (some (cfg (some (phaseLabel .fuelUndo)) regs raw rev pending outputs
          [true, false, false, true, false] [true, false] ctx)) =
      some (cfg (some (phaseLabel .restoreSep2)) (reset regs)
        ([bitZeroTag, bitOneTag, bitOneTag, bitZeroTag, bitZeroTag, bitOneTag, bitZeroTag] ++ raw)
        rev pending outputs [] [] ctx) :=
  (fuelBitsUndo_run caller raw rev pending regs outputs
    [true, false, false, true, false] [true, false] ctx).iterate caller

/-- Arbitrary old tree-reverse material is restored too; it cannot be silently discarded. -/
theorem completed_tree_rollback_retains_a_dirty_reverse_stack
    [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
    (d : TreeSide) (tree : BinaryTree Unit) (raw rev : Word) (pending : List Unit)
    (outputs : TreeSide → Word) (fuel bitsReverse : Bits) :
    (next caller)^[(treeCode tree).length + 1]
        (some (cfg (some (phaseLabel (toReversePhase d))) regs raw rev pending
          (Function.update outputs d (treeCode tree)) fuel bitsReverse ctx)) =
      some (cfg (some (phaseLabel (toRawPhase d))) (reset regs) raw
        ((treeCode tree).reverse ++ rev) pending (Function.update outputs d []) fuel bitsReverse ctx) ∧
      (next caller)^[2 * (treeCode tree).length + rev.length + 2]
        (some (cfg (some (phaseLabel (toReversePhase d))) regs raw rev pending
          (Function.update outputs d (treeCode tree)) fuel bitsReverse ctx)) =
      some (cfg (some (afterRollback d)) (reset regs)
        (rev.reverse ++ treeCode tree ++ raw) [] pending
        (Function.update outputs d []) fuel bitsReverse ctx) :=
  ⟨(toReverse_run caller d (treeCode tree) raw rev pending regs outputs fuel bitsReverse ctx).iterate caller,
    (rollback_run caller d (treeCode tree) raw rev pending regs outputs fuel bitsReverse ctx).iterate caller⟩


/-- High zeros remain literal fuel cells at the complete live return. -/
theorem redundant_high_zeros_survive_the_actual_machine
    [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)] :
    (next caller)^[19]
        (some (entry regs [emptyTag, separatorTag, emptyTag, separatorTag,
          bitOneTag, bitZeroTag, bitZeroTag, endInputTag] ctx)) =
      some (cfg (some (resultLabel .success)) (reset regs) [] [] []
        (treeOutputs [emptyTag] [emptyTag]) [true, false, false] [] ctx) :=
  (run_code_trace caller empty.val empty.val [true, false, false] regs ctx).iterate caller

/-- Five nonpalindromic bits have distinct successful and failed transfer counts. -/
theorem nonpalindromic_fuel_keeps_order_on_success_and_rollback
    [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)] (tail : Word) :
    (next caller)^[23]
        (some (entry regs (inputCode empty.val empty.val [true, false, false, true, false]) ctx)) =
      some (cfg (some (resultLabel .success)) (reset regs) [] [] []
        (treeOutputs [emptyTag] [emptyTag]) [true, false, false, true, false] [] ctx) ∧
    (next caller)^[46]
        (some (entry regs
          (inputCode empty.val empty.val [true, false, false, true, false] ++ 15 :: tail) ctx)) =
      some (resultCfg regs
        (inputCode empty.val empty.val [true, false, false, true, false] ++ 15 :: tail) ctx none) ∧
    (next caller)^[27]
        (some (entry regs
          (inputCode empty.val empty.val [true, false, false, true, false, false, false]) ctx)) =
      some (cfg (some (resultLabel .success)) (reset regs) [] [] []
        (treeOutputs [emptyTag] [emptyTag]) [true, false, false, true, false, false, false] [] ctx) ∧
    (next caller)^[54]
        (some (entry regs
          (inputCode empty.val empty.val [true, false, false, true, false, false, false] ++ 15 :: tail) ctx)) =
      some (resultCfg regs
        (inputCode empty.val empty.val [true, false, false, true, false, false, false] ++ 15 :: tail) ctx none) :=
  ⟨(run_code_trace caller empty.val empty.val [true, false, false, true, false] regs ctx).iterate caller,
    (run_trailing_trace caller empty.val empty.val [true, false, false, true, false]
      (15 :: tail) regs ctx (by simp)).iterate caller,
    (run_code_trace caller empty.val empty.val [true, false, false, true, false, false, false] regs ctx).iterate caller,
    (run_trailing_trace caller empty.val empty.val [true, false, false, true, false, false, false]
      (15 :: tail) regs ctx (by simp)).iterate caller⟩

/-- The actual measured emitter's returned word enters the installed full machine. -/
theorem actual_input_emitter_reaches_the_full_return
    [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
    (source target : BinaryTree Unit) (bs : Bits) :
    (next caller)^[2 * (treeCode source).length + 2 * (treeCode target).length + 2 * bs.length + 9]
        (some (entry regs (emitInputRun source target bs).1 ctx)) =
      some (cfg (some (resultLabel .success)) (reset regs) [] [] []
        (treeOutputs (treeCode source) (treeCode target)) bs [] ctx) := by
  rw [emitInputRun_value]
  exact (run_code_trace caller source target bs regs ctx).iterate caller

/-- Appending junk leaves source-parser work unchanged but invokes real machine rollback. -/
theorem source_and_machine_work_are_separate_observations
    [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)] (tail : Word) :
    parseInputRun (inputCode empty.val empty.val [true, false, false, true, false]) =
      (some (empty.val, empty.val, [true, false, false, true, false]), 30) ∧
    parseInputRun (inputCode empty.val empty.val [true, false, false, true, false] ++ 15 :: tail) =
      (none, 30) ∧
    (next caller)^[46]
        (some (entry regs
          (inputCode empty.val empty.val [true, false, false, true, false] ++ 15 :: tail) ctx)) =
      some (resultCfg regs
        (inputCode empty.val empty.val [true, false, false, true, false] ++ 15 :: tail) ctx none) ∧
    parseInputRun [] = (none, 4) ∧
    (next caller)^[5] (some (entry regs [] ctx)) = some (resultCfg regs [] ctx none) ∧
    ¬ (5 ≤ (parseInputRun []).2) :=
  ⟨parseInputRun_code empty.val empty.val [true, false, false, true, false],
    parseInputRun_trailing empty.val empty.val [true, false, false, true, false] 15 tail,
    (run_trailing_trace caller empty.val empty.val [true, false, false, true, false]
      (15 :: tail) regs ctx (by simp)).iterate caller,
    rfl, (run_tree_failure_trace caller [] regs ctx rfl).iterate caller, by decide⟩


/-- A missing target attains the full linear bound by actual source rollback. -/
theorem missing_target_attains_the_uniform_time_bound
    [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
    (source : BinaryTree Unit) :
    (next caller)^[4 * (treeCode source ++ [separatorTag]).length + 7]
        (some (entry regs (treeCode source ++ [separatorTag]) ctx)) =
      some (resultCfg regs (treeCode source ++ [separatorTag]) ctx none) := by
  have executed := (run_target_failure_trace caller source [] regs ctx rfl).iterate caller
  change (next caller)^[4 * (treeCode source).length + 5 + 6]
    (some (entry regs (treeCode source ++ [separatorTag]) ctx)) = _ at executed
  have count : 4 * (treeCode source).length + 5 + 6 =
      4 * (treeCode source ++ [separatorTag]).length + 7 := by
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  rwa [count] at executed

/-- Two completed trees also attain the bound when the second separator is absent. -/
theorem missing_second_separator_attains_the_uniform_time_bound
    [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
    (source target : BinaryTree Unit) :
    (next caller)^[4 * (treeCode source ++ separatorTag :: treeCode target).length + 7]
        (some (entry regs (treeCode source ++ separatorTag :: treeCode target) ctx)) =
      some (resultCfg regs (treeCode source ++ separatorTag :: treeCode target) ctx none) := by
  have executed := (run_secondSeparator_failure_trace caller source target [] regs ctx rfl).iterate caller
  simp only [List.append_nil] at executed
  have count : 4 * (treeCode source).length + 4 * (treeCode target).length + 11 =
      4 * (treeCode source ++ separatorTag :: treeCode target).length + 7 := by
    simp only [List.length_append, List.length_cons]
    omega
  rwa [count] at executed

/-- A nonpalindromic source and an unequal target keep the sharp cases nontrivial. -/
theorem nonpalindromic_and_unequal_trees_have_sharp_failure_runs
    [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)] :
    (next caller)^[31]
        (some (entry regs [nodeTag, nodeTag, emptyTag, emptyTag, emptyTag, separatorTag] ctx)) =
      some (resultCfg regs [nodeTag, nodeTag, emptyTag, emptyTag, emptyTag, separatorTag] ctx none) ∧
    (next caller)^[35]
        (some (entry regs [nodeTag, emptyTag, nodeTag, emptyTag, emptyTag, separatorTag, emptyTag] ctx)) =
      some (resultCfg regs [nodeTag, emptyTag, nodeTag, emptyTag, emptyTag, separatorTag, emptyTag] ctx none) :=
  ⟨missing_target_attains_the_uniform_time_bound caller regs ctx leftTwo.val,
    missing_second_separator_attains_the_uniform_time_bound caller regs ctx rightTwo.val empty.val⟩

end Context

/-- Both actual full outcomes invoke the same visible caller action. -/
def sentinelCaller : External Unit → Statement SmallAlphabet Unit Bool
  | .inl _ => .push (protectedStack false) (fun _ => true) .halt
  | .inr _ => .halt

def sentinelSuccessStart (flag : Bool) (bits : Bits) (tags : Word) : Cfg SmallAlphabet Unit Bool :=
  entry ((some 15, some ()), flag) (inputCode empty.val empty.val []) (smallContext bits tags)

def sentinelSuccessHandoff (flag : Bool) (bits : Bits) (tags : Word) : Cfg SmallAlphabet Unit Bool :=
  cfg (some (resultLabel .success)) ((none, none), flag) [] [] []
    (treeOutputs [emptyTag] [emptyTag]) [] [] (smallContext bits tags)

def sentinelSuccessAfterCaller (flag : Bool) (bits : Bits) (tags : Word) : Cfg SmallAlphabet Unit Bool :=
  cfg none ((none, none), flag) [] [] []
    (treeOutputs [emptyTag] [emptyTag]) [] [] (smallContext (true :: bits) tags)

def sentinelFailureStart (flag : Bool) (bits : Bits) (tags : Word) : Cfg SmallAlphabet Unit Bool :=
  entry ((some 15, some ()), flag) [] (smallContext bits tags)

def sentinelFailureHandoff (flag : Bool) (bits : Bits) (tags : Word) : Cfg SmallAlphabet Unit Bool :=
  cfg (some (resultLabel .failure)) ((none, none), flag) [] [] []
    (treeOutputs [] []) [] [] (smallContext bits tags)

def sentinelFailureAfterCaller (flag : Bool) (bits : Bits) (tags : Word) : Cfg SmallAlphabet Unit Bool :=
  cfg none ((none, none), flag) [] [] []
    (treeOutputs [] []) [] [] (smallContext (true :: bits) tags)

theorem sentinel_success_handoff_precedes_the_push (flag : Bool) (bits : Bits) (tags : Word) :
    (next sentinelCaller)^[13] (some (sentinelSuccessStart flag bits tags)) =
      some (sentinelSuccessHandoff flag bits tags) :=
  (run_code_trace sentinelCaller empty.val empty.val [] ((some 15, some ()), flag)
    (smallContext bits tags)).iterate sentinelCaller

theorem sentinel_failure_handoff_precedes_the_push (flag : Bool) (bits : Bits) (tags : Word) :
    (next sentinelCaller)^[5] (some (sentinelFailureStart flag bits tags)) =
      some (sentinelFailureHandoff flag bits tags) :=
  (run_tree_failure_trace sentinelCaller [] ((some 15, some ()), flag)
    (smallContext bits tags) rfl).iterate sentinelCaller

/-- Actual caller code preserves every parsed field while changing the protected Bool stack. -/
theorem sentinel_return_step (result : TreeParserMachine.Result) (regs : Registers Bool)
    (raw rev : Word) (pending : List Unit) (outputs : TreeSide → Word)
    (fuel bitsReverse bits : Bits) (tags : Word) :
    step sentinelCaller (cfg (some (resultLabel result)) regs raw rev pending outputs
        fuel bitsReverse (smallContext bits tags)) =
      some (cfg none regs raw rev pending outputs fuel bitsReverse (smallContext (true :: bits) tags)) := by
  cases result <;> apply congrArg some <;> apply cfg_ext
  all_goals first | rfl | exact fun _ => rfl | (intro k; cases k <;> rfl)

def sentinelSuccessInTime (flag : Bool) (bits : Bits) (tags : Word) :
    StateTransition.EvalsToInTime (step sentinelCaller) (sentinelSuccessStart flag bits tags)
      (some (sentinelSuccessHandoff flag bits tags)) 13 where
  steps := 13
  evals_in_steps := by
    change (next sentinelCaller)^[13] (some (sentinelSuccessStart flag bits tags)) = _
    exact sentinel_success_handoff_precedes_the_push flag bits tags
  steps_le_m := Nat.le_refl _

def sentinelFailureInTime (flag : Bool) (bits : Bits) (tags : Word) :
    StateTransition.EvalsToInTime (step sentinelCaller) (sentinelFailureStart flag bits tags)
      (some (sentinelFailureHandoff flag bits tags)) 5 where
  steps := 5
  evals_in_steps := by
    change (next sentinelCaller)^[5] (some (sentinelFailureStart flag bits tags)) = _
    exact sentinel_failure_handoff_precedes_the_push flag bits tags
  steps_le_m := Nat.le_refl _

def sentinelSuccessCallerInTime (flag : Bool) (bits : Bits) (tags : Word) :
    StateTransition.EvalsToInTime (step sentinelCaller) (sentinelSuccessHandoff flag bits tags)
      (some (sentinelSuccessAfterCaller flag bits tags)) 1 where
  steps := 1
  evals_in_steps := sentinel_return_step .success ((none, none), flag) [] [] []
    (treeOutputs [emptyTag] [emptyTag]) [] [] bits tags
  steps_le_m := Nat.le_refl _

def sentinelFailureCallerInTime (flag : Bool) (bits : Bits) (tags : Word) :
    StateTransition.EvalsToInTime (step sentinelCaller) (sentinelFailureHandoff flag bits tags)
      (some (sentinelFailureAfterCaller flag bits tags)) 1 where
  steps := 1
  evals_in_steps := sentinel_return_step .failure ((none, none), flag) [] [] []
    (treeOutputs [] []) [] [] bits tags
  steps_le_m := Nat.le_refl _

def sentinelSuccessCompositionInTime (flag : Bool) (bits : Bits) (tags : Word) :
    StateTransition.EvalsToInTime (step sentinelCaller) (sentinelSuccessStart flag bits tags)
      (some (sentinelSuccessAfterCaller flag bits tags)) 14 :=
  StateTransition.EvalsToInTime.trans (step sentinelCaller) 13 1
    (sentinelSuccessStart flag bits tags) (sentinelSuccessHandoff flag bits tags)
    (some (sentinelSuccessAfterCaller flag bits tags))
    (sentinelSuccessInTime flag bits tags) (sentinelSuccessCallerInTime flag bits tags)

def sentinelFailureCompositionInTime (flag : Bool) (bits : Bits) (tags : Word) :
    StateTransition.EvalsToInTime (step sentinelCaller) (sentinelFailureStart flag bits tags)
      (some (sentinelFailureAfterCaller flag bits tags)) 6 :=
  StateTransition.EvalsToInTime.trans (step sentinelCaller) 5 1
    (sentinelFailureStart flag bits tags) (sentinelFailureHandoff flag bits tags)
    (some (sentinelFailureAfterCaller flag bits tags))
    (sentinelFailureInTime flag bits tags) (sentinelFailureCallerInTime flag bits tags)

/-- Live success, caller halt and outer none occur at three distinct actual times. -/
theorem success_return_halt_and_outer_none_are_distinct
    (flag : Bool) (bits : Bits) (tags : Word) :
    (next sentinelCaller)^[13] (some (sentinelSuccessStart flag bits tags)) =
        some (sentinelSuccessHandoff flag bits tags) ∧
      (sentinelSuccessHandoff flag bits tags).stk (protectedStack false) = bits ∧
      (next sentinelCaller)^[14] (some (sentinelSuccessStart flag bits tags)) =
        some (sentinelSuccessAfterCaller flag bits tags) ∧
      (sentinelSuccessAfterCaller flag bits tags).l = none ∧
      (sentinelSuccessAfterCaller flag bits tags).stk (protectedStack false) = true :: bits ∧
      (next sentinelCaller)^[15] (some (sentinelSuccessStart flag bits tags)) = none := by
  have completed : (next sentinelCaller)^[14] (some (sentinelSuccessStart flag bits tags)) =
      some (sentinelSuccessAfterCaller flag bits tags) :=
    (sentinelSuccessCompositionInTime flag bits tags).evals_in_steps
  refine ⟨sentinel_success_handoff_precedes_the_push flag bits tags, rfl, completed, rfl, rfl, ?_⟩
  rw [show 15 = 14 + 1 by rfl, Function.iterate_succ_apply', completed]
  rfl

/-- Ordinary parse failure also returns live before the caller action and subsequent outer none. -/
theorem failure_return_halt_and_outer_none_are_distinct
    (flag : Bool) (bits : Bits) (tags : Word) :
    (next sentinelCaller)^[5] (some (sentinelFailureStart flag bits tags)) =
        some (sentinelFailureHandoff flag bits tags) ∧
      (sentinelFailureHandoff flag bits tags).stk (protectedStack true) = tags ∧
      (next sentinelCaller)^[6] (some (sentinelFailureStart flag bits tags)) =
        some (sentinelFailureAfterCaller flag bits tags) ∧
      (sentinelFailureAfterCaller flag bits tags).l = none ∧
      (sentinelFailureAfterCaller flag bits tags).stk (protectedStack false) = true :: bits ∧
      (next sentinelCaller)^[7] (some (sentinelFailureStart flag bits tags)) = none := by
  have completed : (next sentinelCaller)^[6] (some (sentinelFailureStart flag bits tags)) =
      some (sentinelFailureAfterCaller flag bits tags) :=
    (sentinelFailureCompositionInTime flag bits tags).evals_in_steps
  refine ⟨sentinel_failure_handoff_precedes_the_push flag bits tags, rfl, completed, rfl, rfl, ?_⟩
  rw [show 7 = 6 + 1 by rfl, Function.iterate_succ_apply', completed]
  rfl

/-- One fixed finite caller allocates only after the complete parser returns failure. -/
def allocatingCaller : External Unit → Statement SmallAlphabet Unit Bool
  | .inl .failure =>
      .push (protectedStack false) (fun _ => true) (jump (resultLabel .failure))
  | _ => .halt

def allocatingStart : Cfg SmallAlphabet Unit Bool := entry staleRegisters [] sampleContext

def allocatingState (count : Nat) : Cfg SmallAlphabet Unit Bool :=
  cfg (some (resultLabel .failure)) (reset staleRegisters) [] [] []
    (treeOutputs [] []) [] []
    (smallContext (List.replicate count true ++ [false, true, false]) [15, 6, nodeTag])

theorem allocating_caller_step (count : Nat) :
    step allocatingCaller (allocatingState count) = some (allocatingState (count + 1)) := by
  apply congrArg some
  apply cfg_ext
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · intro d; cases d <;> rfl
  · rfl
  · rfl
  · intro k; cases k <;> rfl

theorem allocation_is_after_the_actual_first_failure (count : Nat) :
    (next allocatingCaller)^[5 + count] (some allocatingStart) = some (allocatingState count) := by
  induction count with
  | zero =>
      exact (run_tree_failure_trace allocatingCaller [] staleRegisters sampleContext rfl).iterate allocatingCaller
  | succ count ih =>
      rw [Nat.add_succ, Function.iterate_succ_apply', ih, next_some, allocating_caller_step]

/-- These are actual physical cells of the full installed stack family. -/
theorem caller_allocation_exceeds_the_parser_prefix_bound :
    (next allocatingCaller)^[5] (some allocatingStart) = some (allocatingState 0) ∧
      (next allocatingCaller)^[7] (some allocatingStart) = some (allocatingState 2) ∧
      TreeParserMachine.stackCells (allocatingState 0) = 6 ∧
      TreeParserMachine.stackCells (allocatingState 2) = 8 ∧
      2 * ([] : Word).length + TreeParserMachine.contextCells sampleContext + 1 = 7 ∧
      7 < TreeParserMachine.stackCells (allocatingState 2) := by
  refine ⟨allocation_is_after_the_actual_first_failure 0,
    allocation_is_after_the_actual_first_failure 2, ?_, ?_, ?_, ?_⟩ <;> decide

/-- A caller can manufacture a later success label after syntax has already failed. -/
def misleadingCaller : External Unit → Statement SmallAlphabet Unit Bool
  | .inl .failure => jump (resultLabel .success)
  | _ => .halt

def misleadingSuccess : Cfg SmallAlphabet Unit Bool :=
  cfg (some (resultLabel .success)) (reset staleRegisters) [] [] []
    (treeOutputs [] []) [] [] sampleContext

theorem one_real_caller_jump_manufactures_success :
    step misleadingCaller (allocatingState 0) = some misleadingSuccess := rfl

theorem eventual_success_label_does_not_recognize_syntax :
    (next misleadingCaller)^[5] (some allocatingStart) = some (allocatingState 0) ∧
      (next misleadingCaller)^[6] (some allocatingStart) = some misleadingSuccess ∧
      (misleadingSuccess).l = some (resultLabel .success) ∧
      (parseInputRun []).1 = none ∧
      ¬ ∃ source target bs, inputCode source target bs = [] := by
  have first : (next misleadingCaller)^[5] (some allocatingStart) = some (allocatingState 0) :=
    (run_tree_failure_trace misleadingCaller [] staleRegisters sampleContext rfl).iterate misleadingCaller
  refine ⟨first, ?_, rfl, rfl, ?_⟩
  · rw [show 6 = 5 + 1 by rfl, Function.iterate_succ_apply', first, next_some,
      one_real_caller_jump_manufactures_success]
  · rintro ⟨source, target, bs, word⟩
    have parsed := parseInputRun_code source target bs
    rw [word] at parsed
    cases parsed

section Context
variable {K Λ R : Type} [DecidableEq K] {Γ : K → Type}
variable (caller : External Λ → Statement Γ Λ R)
variable (regs : Registers R) (ctx : ∀ k, List (Γ k))

/-- The source's actual proper-prefix decomposition fixes the first-tree cleanup count. -/
theorem represented_first_tree_failure_has_its_exact_cleanup_time
    [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
    (pref rest : Word) (p : Nat) (opened : TreeParserMachine.OpenPrefix pref p)
    (blocked : TreeParserMachine.Blocked rest) :
    (next caller)^[2 * pref.length + p + 4]
        (some (entry regs (pref ++ rest) ctx)) =
      some (resultCfg regs (pref ++ rest) ctx none) := by
  have executed := (run_tree_failure_trace caller (pref ++ rest) regs ctx
    (TreeParserMachine.parseTreeRun_none_of_openPrefix opened blocked)).iterate caller
  rwa [TreeParserMachine.runSteps_openPrefix opened blocked] at executed

/-- Target-tree cleanup also restores the already consumed source and separator. -/
theorem represented_target_failure_restores_the_completed_source
    [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
    (source : BinaryTree Unit) (pref rest : Word) (p : Nat)
    (opened : TreeParserMachine.OpenPrefix pref p) (blocked : TreeParserMachine.Blocked rest) :
    (next caller)^[4 * (treeCode source).length + 2 * pref.length + p + 10]
        (some (entry regs (treeCode source ++ separatorTag :: (pref ++ rest)) ctx)) =
      some (resultCfg regs (treeCode source ++ separatorTag :: (pref ++ rest)) ctx none) := by
  have executed := (run_target_failure_trace caller source (pref ++ rest) regs ctx
    (TreeParserMachine.parseTreeRun_none_of_openPrefix opened blocked)).iterate caller
  rw [TreeParserMachine.runSteps_openPrefix opened blocked] at executed
  have count : 4 * (treeCode source).length + (2 * pref.length + p + 4) + 6 =
      4 * (treeCode source).length + 2 * pref.length + p + 10 := by omega
  rwa [count] at executed

/-- The all-node pending peak belongs to this installed full program and handler. -/
theorem all_nodes_reach_the_actual_full_program_pending_peak
    [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)] (count : Nat) :
    (next caller)^[count + 1] (some (entry regs (List.replicate count nodeTag) ctx)) =
      some (cfg (some (treeLabel .source .scan)) (reset regs) []
        (List.replicate count nodeTag) (List.replicate (count + 1) ())
        (treeOutputs [] []) [] [] ctx) :=
  TreeParserMachine.nodes_prefix (handler caller) .source count regs (treeOutputs [] [])
    (stores [] [] ctx)

end Context

section Context
variable {K Λ R : Type} [DecidableEq K] {Γ : K → Type}
variable (caller : External Λ → Statement Γ Λ R)
variable (regs : Registers R) (ctx : ∀ k, List (Γ k))

/-- Zero, the last transfer and the following empty probe are distinct configurations. -/
theorem bit_emission_has_a_real_final_empty_probe
    [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
    (raw rev : Word) (pending : List Unit) (outputs : TreeSide → Word)
    (fuel bitsReverse : Bits) :
    (next caller)^[0]
        (some (cfg (some (phaseLabel .bitsEmit)) regs raw rev pending outputs fuel bitsReverse ctx)) =
      some (cfg (some (phaseLabel .bitsEmit)) regs raw rev pending outputs fuel bitsReverse ctx) ∧
    (next caller)^[bitsReverse.length]
        (some (cfg (some (phaseLabel .bitsEmit)) regs raw rev pending outputs fuel bitsReverse ctx)) =
      some (cfg (some (phaseLabel .bitsEmit)) (if bitsReverse.length = 0 then regs else reset regs)
        raw rev pending outputs (bitsReverse.reverse ++ fuel) [] ctx) ∧
    (next caller)^[bitsReverse.length + 1]
        (some (cfg (some (phaseLabel .bitsEmit)) regs raw rev pending outputs fuel bitsReverse ctx)) =
      some (cfg (some (phaseLabel .eof)) (reset regs)
        raw rev pending outputs (bitsReverse.reverse ++ fuel) [] ctx) := by
  refine ⟨rfl, ?_, (bitsEmit_run caller raw rev pending regs outputs fuel bitsReverse ctx).iterate caller⟩
  simpa only [List.take_length, List.drop_length] using
    bitsEmit_prefix caller raw rev pending regs outputs fuel bitsReverse ctx bitsReverse.length (Nat.le_refl _)

/-- The nonpalindromic reverse word has the fixed transfer orientation even with an old suffix. -/
theorem three_bit_emission_has_the_expected_intermediate_words
    [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
    (raw rev : Word) (pending : List Unit) (outputs : TreeSide → Word) (fuel : Bits) :
    (next caller)^[1]
        (some (cfg (some (phaseLabel .bitsEmit)) regs raw rev pending outputs fuel [false, true, true] ctx)) =
      some (cfg (some (phaseLabel .bitsEmit)) (reset regs) raw rev pending outputs
        (false :: fuel) [true, true] ctx) ∧
    (next caller)^[3]
        (some (cfg (some (phaseLabel .bitsEmit)) regs raw rev pending outputs fuel [false, true, true] ctx)) =
      some (cfg (some (phaseLabel .bitsEmit)) (reset regs) raw rev pending outputs
        ([true, true, false] ++ fuel) [] ctx) ∧
    (next caller)^[4]
        (some (cfg (some (phaseLabel .bitsEmit)) regs raw rev pending outputs fuel [false, true, true] ctx)) =
      some (cfg (some (phaseLabel .eof)) (reset regs) raw rev pending outputs
        ([true, true, false] ++ fuel) [] ctx) :=
  ⟨(bitsEmit_prefix_run caller [false] [true, true] raw rev pending regs outputs fuel ctx).iterate caller,
    (bitsEmit_prefix_run caller [false, true, true] [] raw rev pending regs outputs fuel ctx).iterate caller,
    (bitsEmit_run caller raw rev pending regs outputs fuel [false, true, true] ctx).iterate caller⟩

/-- Literal observed-bit conversion preserves the unread raw tail and a dirty reverse accumulator. -/
theorem bits_scan_prefix_keeps_unread_tags_and_old_reverse
    [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
    (bs : Bits) (raw rev : Word) (pending : List Unit) (outputs : TreeSide → Word)
    (fuel bitsReverse : Bits) :
    (next caller)^[bs.length]
        (some (cfg (some (phaseLabel .bitsScan)) regs (bitTags bs ++ raw) rev pending
          outputs fuel bitsReverse ctx)) =
      some (cfg (some (phaseLabel .bitsScan)) (if bs = [] then regs else reset regs)
        raw rev pending outputs fuel (bs.reverse ++ bitsReverse) ctx) :=
  (bitsScan_prefix_run caller bs raw rev pending regs outputs fuel bitsReverse ctx).iterate caller

/-- Each rollback prefix preserves the exact remaining list and accumulates its reversed prefix. -/
theorem dirty_bit_rollback_prefixes_preserve_every_unmoved_cell
    [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
    (moved rest : Bits) (raw rev : Word) (pending : List Unit) (outputs : TreeSide → Word)
    (oldReverse fuel : Bits) :
    (next caller)^[moved.length]
        (some (cfg (some (phaseLabel .fuelUndo)) regs raw rev pending outputs
          (moved ++ rest) oldReverse ctx)) =
      some (cfg (some (phaseLabel .fuelUndo)) (if moved = [] then regs else reset regs)
        raw rev pending outputs rest (moved.reverse ++ oldReverse) ctx) ∧
    (next caller)^[moved.length]
        (some (cfg (some (phaseLabel .bitsUndo)) regs raw rev pending outputs
          fuel (moved ++ rest) ctx)) =
      some (cfg (some (phaseLabel .bitsUndo)) (if moved = [] then regs else reset regs)
        (bitTags moved.reverse ++ raw) rev pending outputs fuel rest ctx) :=
  ⟨(fuelUndo_prefix_run caller moved rest raw rev pending regs outputs oldReverse ctx).iterate caller,
    (bitsUndo_prefix_run caller moved rest raw rev pending regs outputs fuel ctx).iterate caller⟩

/-- With clean reverse scratch the two real bit loops recover the forward five-bit word in twelve steps. -/
theorem clean_five_bit_rollback_takes_twelve_steps
    [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
    (raw rev : Word) (pending : List Unit) (outputs : TreeSide → Word) :
    (next caller)^[12]
        (some (cfg (some (phaseLabel .fuelUndo)) regs raw rev pending outputs
          [true, false, false, true, false] [] ctx)) =
      some (cfg (some (phaseLabel .restoreSep2)) (reset regs)
        ([bitOneTag, bitZeroTag, bitZeroTag, bitOneTag, bitZeroTag] ++ raw)
        rev pending outputs [] [] ctx) :=
  (fuelBitsUndo_run caller raw rev pending regs outputs [true, false, false, true, false] [] ctx).iterate caller

/-- Both destinations expose their distinct nonpalindromic reverse code before restoring raw. -/
theorem nonpalindromic_tree_rollbacks_have_distinct_intermediate_orientations
    [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
    (raw oldReverse other : Word) (pending : List Unit) (fuel bitsReverse : Bits) :
    (next caller)^[6]
        (some (cfg (some (phaseLabel .sourceToReverse)) regs raw oldReverse pending
          (treeOutputs (treeCode leftTwo.val) other) fuel bitsReverse ctx)) =
      some (cfg (some (phaseLabel .sourceToRaw)) (reset regs) raw
        ([emptyTag, emptyTag, emptyTag, nodeTag, nodeTag] ++ oldReverse) pending
        (treeOutputs [] other) fuel bitsReverse ctx) ∧
    (next caller)^[6]
        (some (cfg (some (phaseLabel .targetToReverse)) regs raw oldReverse pending
          (treeOutputs other (treeCode rightTwo.val)) fuel bitsReverse ctx)) =
      some (cfg (some (phaseLabel .targetToRaw)) (reset regs) raw
        ([emptyTag, emptyTag, nodeTag, emptyTag, nodeTag] ++ oldReverse) pending
        (treeOutputs other []) fuel bitsReverse ctx) := by
  constructor
  · have count : (treeCode leftTwo.val).length + 1 = 6 := rfl
    have reversed : (treeCode leftTwo.val).reverse =
        [emptyTag, emptyTag, emptyTag, nodeTag, nodeTag] := rfl
    simpa only [treeOutputs_update_source, count, reversed, toReversePhase, toRawPhase] using
      (toReverse_run caller .source (treeCode leftTwo.val) raw oldReverse pending regs
        (treeOutputs [] other) fuel bitsReverse ctx).iterate caller
  · have count : (treeCode rightTwo.val).length + 1 = 6 := rfl
    have reversed : (treeCode rightTwo.val).reverse =
        [emptyTag, emptyTag, nodeTag, emptyTag, nodeTag] := rfl
    simpa only [treeOutputs_update_target, count, reversed, toReversePhase, toRawPhase] using
      (toReverse_run caller .target (treeCode rightTwo.val) raw oldReverse pending regs
        (treeOutputs other []) fuel bitsReverse ctx).iterate caller

/-- Target rollback does not insert a separator until the following actual restore block. -/
theorem separator_restoration_is_a_distinct_transition
    [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
    (raw source : Word) (pending : List Unit) (fuel bitsReverse : Bits) :
    (next caller)^[12]
        (some (cfg (some (phaseLabel .targetToReverse)) regs raw [] pending
          (treeOutputs source (treeCode rightTwo.val)) fuel bitsReverse ctx)) =
      some (cfg (some (phaseLabel .restoreSep1)) (reset regs)
        (treeCode rightTwo.val ++ raw) [] pending (treeOutputs source []) fuel bitsReverse ctx) ∧
    (next caller)^[13]
        (some (cfg (some (phaseLabel .targetToReverse)) regs raw [] pending
          (treeOutputs source (treeCode rightTwo.val)) fuel bitsReverse ctx)) =
      some (cfg (some (phaseLabel .sourceToReverse)) (reset regs)
        (separatorTag :: (treeCode rightTwo.val ++ raw)) [] pending
        (treeOutputs source []) fuel bitsReverse ctx) := by
  have rolled : (next caller)^[12]
      (some (cfg (some (phaseLabel .targetToReverse)) regs raw [] pending
        (treeOutputs source (treeCode rightTwo.val)) fuel bitsReverse ctx)) =
    some (cfg (some (phaseLabel .restoreSep1)) (reset regs)
      (treeCode rightTwo.val ++ raw) [] pending (treeOutputs source []) fuel bitsReverse ctx) := by
    have count : 2 * (treeCode rightTwo.val).length + ([] : Word).length + 2 = 12 := rfl
    simpa only [treeOutputs_update_target, count, List.reverse_nil, List.nil_append,
      toReversePhase, afterRollback] using
      (rollback_run caller .target (treeCode rightTwo.val) raw [] pending regs
        (treeOutputs source []) fuel bitsReverse ctx).iterate caller
  refine ⟨rolled, ?_⟩
  rw [show 13 = 12 + 1 by rfl, Function.iterate_succ_apply', rolled, next_some,
    restoreSep1_step]
  rfl

end Context

section Context
variable {K Λ R : Type} [DecidableEq K] {Γ : K → Type}
variable (caller : External Λ → Statement Γ Λ R)
variable (regs : Registers R) (ctx : ∀ k, List (Γ k))

/-- The same raw input has an actual endpoint and two independently stated work bounds. -/
theorem arbitrary_raw_returns_with_separate_source_and_machine_bounds
    [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)] (raw : Word) :
    (next caller)^[inputSteps raw] (some (entry regs raw ctx)) =
        some (resultCfg regs raw ctx (parseInputRun raw).1) ∧
      inputSteps raw ≤ 4 * raw.length + 7 ∧
      (parseInputRun raw).2 ≤ 20 * (raw.length + 1) :=
  ⟨run_source caller raw regs ctx, inputSteps_le raw, parseInputRun_cost_le raw⟩

/-- The actual returned source fields determine both literal machine outputs and source work. -/
theorem actual_success_preserves_the_returned_fields
    [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
    (raw : Word) (source target : BinaryTree Unit) (bs : Bits)
    (returned : (parseInputRun raw).1 = some (source, target, bs)) :
    raw = inputCode source target bs ∧
      (next caller)^[inputSteps raw] (some (entry regs raw ctx)) =
        some (cfg (some (resultLabel .success)) (reset regs) [] [] []
          (treeOutputs (treeCode source) (treeCode target)) bs [] ctx) ∧
      (parseInputRun raw).2 = 7 * source.numNodes + 7 * target.numNodes + 3 * bs.length + 15 :=
  ⟨(parseInputRun_iff raw source target bs).mp returned,
    run_of_some caller raw source target bs regs ctx returned,
    parseInputRun_cost_of_some raw source target bs returned⟩

/-- No partial output remains after an arbitrary actual source failure. -/
theorem actual_failure_restores_raw_and_all_six_nonraw_owned_stacks
    [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
    (raw : Word) (returned : (parseInputRun raw).1 = none) :
    (next caller)^[inputSteps raw] (some (entry regs raw ctx)) =
      some (cfg (some (resultLabel .failure)) (reset regs) raw [] []
        (treeOutputs [] []) [] [] ctx) :=
  run_of_none caller raw regs ctx returned

/-- This is constructed timing data for the actual transition, including malformed raw inputs. -/
def actual_full_parser_in_linear_time
    [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)] (raw : Word) :
    StateTransition.EvalsToInTime (step caller) (entry regs raw ctx)
      (some (resultCfg regs raw ctx (parseInputRun raw).1)) (4 * raw.length + 7) :=
  runInLinearTime caller raw regs ctx

/-- Composition uses this returned configuration as the next actual program input. -/
def full_parser_then_actual_continuation
    [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
    (raw : Word) (final : Option (Cfg Γ Λ R)) (m : Nat)
    (continuation : StateTransition.EvalsToInTime (step caller)
      (resultCfg regs raw ctx (parseInputRun raw).1) final m) :
    StateTransition.EvalsToInTime (step caller) (entry regs raw ctx)
      final (m + (4 * raw.length + 7)) :=
  StateTransition.EvalsToInTime.trans (step caller) (4 * raw.length + 7) m
    (entry regs raw ctx) (resultCfg regs raw ctx (parseInputRun raw).1) final
    (runInLinearTime caller raw regs ctx) continuation

/-- The real emitter's nil and one-rotation words have separate machine and source clocks. -/
theorem actual_emitted_nil_and_rotation_have_the_fixed_two_clocks
    [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)] :
    parseInputRun (emitInputRun empty.val empty.val []).1 = (some (empty.val, empty.val, []), 15) ∧
      (next caller)^[13] (some (entry regs (emitInputRun empty.val empty.val []).1 ctx)) =
        some (cfg (some (resultLabel .success)) (reset regs) [] [] []
          (treeOutputs [emptyTag] [emptyTag]) [] [] ctx) ∧
      parseInputRun (emitInputRun leftTwo.val rightTwo.val [true]).1 =
        (some (leftTwo.val, rightTwo.val, [true]), 46) ∧
      (next caller)^[31] (some (entry regs (emitInputRun leftTwo.val rightTwo.val [true]).1 ctx)) =
        some (cfg (some (resultLabel .success)) (reset regs) [] [] []
          (treeOutputs (treeCode leftTwo.val) (treeCode rightTwo.val)) [true] [] ctx) :=
  ⟨parseInputRun_emit empty.val empty.val [],
    actual_input_emitter_reaches_the_full_return caller regs ctx empty.val empty.val [],
    parseInputRun_emit leftTwo.val rightTwo.val [true],
    actual_input_emitter_reaches_the_full_return caller regs ctx leftTwo.val rightTwo.val [true]⟩

/-- Input syntax accepts unequal tree sizes without making a rotation-distance assertion. -/
theorem actual_emitted_unequal_trees_have_source22_and_machine17
    [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)] :
    parseInputRun (emitInputRun empty.val singleton.val []).1 =
      (some (empty.val, singleton.val, []), 22) ∧
      (next caller)^[17] (some (entry regs (emitInputRun empty.val singleton.val []).1 ctx)) =
        some (cfg (some (resultLabel .success)) (reset regs) [] [] []
          (treeOutputs (treeCode empty.val) (treeCode singleton.val)) [] [] ctx) ∧
      ∀ moves : List Trees.Rotations.RotationMove, Trees.Rotations.applyMoves? moves empty.val ≠ some singleton.val := by
  refine ⟨parseInputRun_emit empty.val singleton.val [],
    actual_input_emitter_reaches_the_full_return caller regs ctx empty.val singleton.val [], ?_⟩
  intro moves run
  have sizes := Trees.Rotations.applyMoves?_numNodes moves run
  change 1 = 0 at sizes
  omega

/-- High zeros add their literal transfers and source work; they are not normalized away. -/
theorem actual_emitted_nonpalindromic_high_zeros_have_source36_and_machine27
    [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)] :
    parseInputRun (emitInputRun empty.val empty.val [true, false, false, true, false, false, false]).1 =
      (some (empty.val, empty.val, [true, false, false, true, false, false, false]), 36) ∧
      (next caller)^[27]
        (some (entry regs
          (emitInputRun empty.val empty.val [true, false, false, true, false, false, false]).1 ctx)) =
        some (cfg (some (resultLabel .success)) (reset regs) [] [] []
          (treeOutputs [emptyTag] [emptyTag]) [true, false, false, true, false, false, false] [] ctx) :=
  ⟨parseInputRun_emit empty.val empty.val [true, false, false, true, false, false, false],
    actual_input_emitter_reaches_the_full_return caller regs ctx empty.val empty.val
      [true, false, false, true, false, false, false]⟩

/-- EOF rejection has source work fifteen but twenty-six actual machine transitions. -/
theorem actual_nil_EOF_rollback_has_source15_and_machine26
    [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)] (tag : Tag) (tail : Word) :
    parseInputRun (inputCode empty.val empty.val [] ++ tag :: tail) = (none, 15) ∧
      (next caller)^[26] (some (entry regs (inputCode empty.val empty.val [] ++ tag :: tail) ctx)) =
        some (resultCfg regs (inputCode empty.val empty.val [] ++ tag :: tail) ctx none) :=
  ⟨parseInputRun_trailing empty.val empty.val [] tag tail,
    (run_trailing_trace caller empty.val empty.val [] (tag :: tail) regs ctx (by simp)).iterate caller⟩

end Context

private theorem nodesOpenPrefix (count : Nat) :
    TreeParserMachine.OpenPrefix (List.replicate count nodeTag) (count + 1) := by
  induction count with
  | zero => exact .nil
  | succ count ih =>
      simpa only [List.replicate_add, List.replicate_one] using TreeParserMachine.OpenPrefix.node ih

section Context
variable {K Λ R : Type} [DecidableEq K] {Γ : K → Type}
variable (caller : External Λ → Statement Γ Λ R)
variable (regs : Registers R) (ctx : ∀ k, List (Γ k))

/-- Every all-node word actually restores its raw cells and clears its pending tokens. -/
theorem all_node_inputs_have_the_exact_full_failure_time
    [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)] (count : Nat) :
    (next caller)^[3 * count + 5]
        (some (entry regs (List.replicate count nodeTag) ctx)) =
      some (cfg (some (resultLabel .failure)) (reset regs)
        (List.replicate count nodeTag) [] [] (treeOutputs [] []) [] [] ctx) := by
  have source : (parseTreeRun (List.replicate count nodeTag)).1 = none := by
    simpa only [List.append_nil] using
      TreeParserMachine.parseTreeRun_none_of_openPrefix (nodesOpenPrefix count)
        (show TreeParserMachine.Blocked [] from True.intro)
  have executed := (run_tree_failure_trace caller (List.replicate count nodeTag) regs ctx source).iterate caller
  rwa [TreeParserMachine.runSteps_nodes] at executed

/-- The pending peak is an actual strict prefix for every input length and arbitrary protected data. -/
theorem all_node_inputs_attain_the_actual_full_stack_bound
    [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)] (count : Nat) :
    ∃ reached : Cfg Γ Λ R,
      (next caller)^[count + 1] (some (entry regs (List.replicate count nodeTag) ctx)) = some reached ∧
      count + 1 < 3 * count + 5 ∧
      TreeParserMachine.stackCells reached =
        2 * count + TreeParserMachine.contextCells ctx + 1 := by
  obtain ⟨reached, executed, _, cells⟩ :=
    TreeParserMachine.nodes_prefix_sharp (handler caller) .source count regs
      (treeOutputs [] []) (stores [] [] ctx)
  have outputsEmpty : TreeParserMachine.outputCells (treeOutputs [] []) = 0 := by
    have zero : ∀ d : TreeSide, (treeOutputs [] [] d).length = 0 := by
      intro d; cases d <;> rfl
    simp only [TreeParserMachine.outputCells, zero, Finset.sum_const_zero]
  have contextEmpty : TreeParserMachine.contextCells (stores [] [] ctx) =
      TreeParserMachine.contextCells ctx := by
    have zero : ∀ k : ExtraStack, (stores [] [] ctx (.inl k)).length = 0 := by
      intro k; cases k <;> rfl
    unfold TreeParserMachine.contextCells
    rw [Fintype.sum_sum_type]
    change (∑ k : ExtraStack, (stores [] [] ctx (.inl k)).length) +
      (∑ k : K, (ctx k).length) = ∑ k : K, (ctx k).length
    rw [Finset.sum_eq_zero (fun k _ => zero k), Nat.zero_add]
  refine ⟨reached, executed, by omega, ?_⟩
  simpa only [outputsEmpty, contextEmpty, Nat.add_zero] using cells

end Context


section CompletePrefix
variable {K Λ R : Type} [DecidableEq K] {Γ : K → Type}
variable (caller : External Λ → Statement Γ Λ R)
variable (regs : Registers R) (ctx : ∀ k, List (Γ k))

/-- Every requested prefix has an actual witness carrying the complete reached-state invariant. -/
theorem every_actual_prefix_has_mass_slots_frame_and_the_cell_bound
    [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
    (raw : Word) (n : Nat) (bound : n ≤ inputSteps raw) :
    ∃ reached : Cfg Γ Λ R,
      (next caller)^[n] (some (entry regs raw ctx)) = some reached ∧
      (n < inputSteps raw ↔ FullOwned reached.l) ∧
      reached.var = (if n = 0 then regs else reset regs) ∧
      reached.var.2 = regs.2 ∧
      (0 < n → reached.var.1 = (none, none)) ∧
      (∀ k, reached.stk (protectedStack k) = ctx k) ∧
      baseCells reached + debt reached.l = raw.length ∧
      PendingControl raw.length reached ∧
      (reached.stk pendingStack).length ≤ raw.length + 1 ∧
      (¬ TreeParserMachine.Owned reached.l → reached.stk pendingStack = []) ∧
      stackCells reached ≤ 2 * raw.length + contextCells ctx + 1 := by
  obtain ⟨reached, executed, _, _, boundary⟩ := run_prefix caller raw regs ctx n bound
  obtain ⟨registers, frame, mass, slots⟩ := prefix_preserves caller raw regs ctx n bound reached executed
  have callerRegister : reached.var.2 = regs.2 := by
    rw [registers]
    split <;> rfl
  have resetAfter : 0 < n → reached.var.1 = (none, none) := by
    intro positive
    rw [registers, ite_eq_right (by omega)]
    rfl
  exact ⟨reached, executed, boundary, registers, callerRegister, resetAfter, frame, mass, slots,
    pendingControl_bound raw.length reached slots,
    prefix_pending_empty caller raw regs ctx n bound reached executed,
    prefix_stackCells_le caller raw regs ctx n bound reached executed⟩

/-- The arbitrary installed caller has no effect through the inclusive first full return. -/
theorem different_callers_share_every_complete_parser_prefix
    [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
    (other : External Λ → Statement Γ Λ R) (raw : Word) (n : Nat)
    (bound : n ≤ inputSteps raw) :
    (next caller)^[n] (some (entry regs raw ctx)) =
      (next other)^[n] (some (entry regs raw ctx)) :=
  run_prefix_caller_independent caller other raw regs ctx n bound

/-- First-result recognition uses the actual source result, including ordinary parse failure. -/
theorem actual_first_result_iff_source_result
    [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
    (raw : Word) (observed : Option ParsedInput) :
    (next caller)^[inputSteps raw] (some (entry regs raw ctx)) =
        some (resultCfg regs raw ctx observed) ↔ (parseInputRun raw).1 = observed :=
  firstResult_iff caller raw regs ctx observed

/-- The first live success recognizes both exact shapes and the literal finite-width fuel word. -/
theorem actual_first_success_iff_exact_input_word
    [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
    (raw : Word) (source target : BinaryTree Unit) (bs : Bits) :
    (next caller)^[inputSteps raw] (some (entry regs raw ctx)) =
        some (cfg (some (resultLabel .success)) (reset regs) [] [] []
          (treeOutputs (treeCode source) (treeCode target)) bs [] ctx) ↔
      raw = inputCode source target bs :=
  firstSuccess_code_iff caller raw source target bs regs ctx

/-- The exact successful clock is connected to the same observed fields and actual run. -/
theorem successful_source_result_has_the_exact_linear_run
    [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
    (raw : Word) (source target : BinaryTree Unit) (bs : Bits)
    (returned : (parseInputRun raw).1 = some (source, target, bs)) :
    inputSteps raw = 2 * raw.length + 3 ∧
      (next caller)^[2 * raw.length + 3] (some (entry regs raw ctx)) =
        some (cfg (some (resultLabel .success)) (reset regs) [] [] []
          (treeOutputs (treeCode source) (treeCode target)) bs [] ctx) := by
  have count := inputSteps_of_some raw source target bs returned
  refine ⟨count, ?_⟩
  rw [← count]
  exact run_of_some caller raw source target bs regs ctx returned

/-- Node counts describe the same successful execution; they are not runtime callbacks. -/
theorem successful_input_has_the_exact_node_count_run
    [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
    (source target : BinaryTree Unit) (bs : Bits) :
    (next caller)^[4 * source.numNodes + 4 * target.numNodes + 2 * bs.length + 13]
        (some (entry regs (inputCode source target bs) ctx)) =
      some (cfg (some (resultLabel .success)) (reset regs) [] [] []
        (treeOutputs (treeCode source) (treeCode target)) bs [] ctx) := by
  rw [← inputSteps_code_nodes]
  exact run_of_some caller (inputCode source target bs) source target bs regs ctx
    (congrArg Prod.fst (parseInputRun_code source target bs))

omit [DecidableEq K] in
/-- Restoration annotations describe the state before each actual push, even with dirty data. -/
theorem actual_restore_steps_conserve_mass_on_dirty_states
    (caller : External Λ → Statement Γ Λ R) [DecidableEq K]
    [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
    (raw rev : Word) (pending : List Unit) (outputs : TreeSide → Word) (fuel bitsReverse : Bits) :
    Effect (Λ := Λ)
      (cfg (some (phaseLabel .restoreEnd)) regs raw rev pending outputs fuel bitsReverse ctx)
      (cfg (some (phaseLabel .fuelUndo)) (reset regs) (endInputTag :: raw) rev pending outputs fuel bitsReverse ctx) ∧
    debt (some (phaseLabel (Λ := Λ) .restoreEnd)) = 3 ∧
    debt (some (phaseLabel (Λ := Λ) .fuelUndo)) = 2 ∧
    Effect (Λ := Λ)
      (cfg (some (treeResultLabel .target .failure)) regs raw rev pending outputs fuel bitsReverse ctx)
      (cfg (some (phaseLabel .sourceToReverse)) (reset regs) (separatorTag :: raw) rev pending outputs fuel bitsReverse ctx) ∧
    debt (some (treeResultLabel (Λ := Λ) .target .failure)) = 1 ∧
    debt (some (phaseLabel (Λ := Λ) .sourceToReverse)) = 0 :=
  ⟨step_effect caller (fullOwned_phase .restoreEnd)
      (restoreEnd_step caller raw rev pending regs outputs fuel bitsReverse ctx), rfl, rfl,
    step_effect caller (by trivial) (targetFailure_step caller raw rev pending regs outputs fuel bitsReverse ctx),
    rfl, rfl⟩

/-- The actual sharp space witness is strict, and its same complete run subsequently restores failure. -/
theorem all_node_words_have_a_sharp_prefix_and_a_restored_full_return
    [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)] (count : Nat) :
    ∃ reached : Cfg Γ Λ R,
      (next caller)^[count + 1] (some (entry regs (List.replicate count nodeTag) ctx)) = some reached ∧
      count + 1 < inputSteps (List.replicate count nodeTag) ∧
      stackCells reached = 2 * count + contextCells ctx + 1 ∧
      (next caller)^[3 * count + 5] (some (entry regs (List.replicate count nodeTag) ctx)) =
        some (resultCfg regs (List.replicate count nodeTag) ctx none) := by
  obtain ⟨reached, executed, strict, cells⟩ := nodes_prefix_sharp caller count regs ctx
  exact ⟨reached, executed, strict, cells,
    all_node_inputs_have_the_exact_full_failure_time caller regs ctx count⟩

/-- Every shorter prefix in either sharp time family is still owned by the complete parser. -/
theorem sharp_failure_families_really_are_first_full_returns
    [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
    (source target : BinaryTree Unit) :
    (∀ n, n < 4 * (treeCode source ++ [separatorTag]).length + 7 →
      ∃ reached : Cfg Γ Λ R,
        (next caller)^[n] (some (entry regs (treeCode source ++ [separatorTag]) ctx)) = some reached ∧
        FullOwned reached.l) ∧
    (∀ n, n < 4 * (treeCode source ++ separatorTag :: treeCode target).length + 7 →
      ∃ reached : Cfg Γ Λ R,
        (next caller)^[n] (some (entry regs (treeCode source ++ separatorTag :: treeCode target) ctx)) = some reached ∧
        FullOwned reached.l) :=
  ⟨fun n strict => (missing_target_sharp_trace caller source regs ctx).owned_prefix caller n strict,
    fun n strict => (missing_secondSeparator_sharp_trace caller source target regs ctx).owned_prefix caller n strict⟩

end CompletePrefix

/-- The zero state keeps stale temporaries; the actual first init block resets both. -/
theorem stale_temporaries_reset_on_the_actual_first_transition
    (caller : External Unit → Statement SmallAlphabet Unit Bool) (raw : Word) (bits : Bits) (tags : Word) :
    (entry (Λ := Unit) staleRegisters raw (smallContext bits tags)).var.1 = (some 15, some ()) ∧
      step caller (entry staleRegisters raw (smallContext bits tags)) =
        some (cfg (some (treeLabel .source .scan)) ((none, none), true) raw [] [()]
          (treeOutputs [] []) [] [] (smallContext bits tags)) :=
  ⟨rfl, TreeParserMachine.init_step (handler caller) .source raw [] [] staleRegisters
    (treeOutputs [] []) (stores [] [] (smallContext bits tags))⟩

/-- Equal numeric fuel values do not identify the two actual literal result stacks. -/
theorem redundant_zero_width_changes_the_actual_result_configuration :
    BinaryCounter.value [true] = BinaryCounter.value [true, false] ∧
      resultCfg (Λ := Unit) staleRegisters [] sampleContext (some (empty.val, empty.val, [true])) ≠
        resultCfg (Λ := Unit) staleRegisters [] sampleContext (some (empty.val, empty.val, [true, false])) := by
  refine ⟨rfl, ?_⟩
  intro same
  have lengths := congrArg (fun c : Cfg SmallAlphabet Unit Bool => (c.stk fuelStack).length) same
  change 1 = 2 at lengths
  omega

/-- The actual later success label cannot satisfy recognition at the first returned configuration. -/
theorem misleading_later_success_is_never_a_first_success :
    (next misleadingCaller)^[6] (some allocatingStart) = some misleadingSuccess ∧
      ∀ source target bs, ¬ FirstSuccess misleadingCaller [] source target bs staleRegisters sampleContext := by
  refine ⟨eventual_success_label_does_not_recognize_syntax.2.1, ?_⟩
  intro source target bs claimed
  have sourceResult := (firstSuccess_iff misleadingCaller [] source target bs staleRegisters sampleContext).mp claimed
  change none = some (source, target, bs) at sourceResult
  cases sourceResult

/-- The same installed caller satisfies the inclusive parser bound and violates it only afterwards. -/
theorem actual_parser_bound_stops_before_caller_allocation :
    (∀ n, n ≤ inputSteps [] → ∀ reached : Cfg SmallAlphabet Unit Bool,
      (next allocatingCaller)^[n] (some allocatingStart) = some reached → stackCells reached ≤ 7) ∧
      (next allocatingCaller)^[7] (some allocatingStart) = some (allocatingState 2) ∧
      stackCells (allocatingState 2) = 8 := by
  refine ⟨?_, allocation_is_after_the_actual_first_failure 2, by decide⟩
  intro n bound reached executed
  have cells := prefix_stackCells_le allocatingCaller [] staleRegisters sampleContext n bound reached executed
  have boundValue : 2 * ([] : Word).length + contextCells sampleContext + 1 = 7 := by decide
  simpa only [boundValue] using cells

/-- This is the concrete finite installed machine, with raw Tag input and Bool fuel output. -/
def concreteInputMachine : Turing.FinTM2 := machine sentinelCaller true

instance concreteInputMachineStackFintype : Fintype concreteInputMachine.K :=
  concreteInputMachine.kFin

instance concreteInputMachineLabelFintype : Fintype concreteInputMachine.Λ :=
  concreteInputMachine.ΛFin

instance concreteInputMachineRegistersFintype : Fintype concreteInputMachine.σ :=
  concreteInputMachine.σFin

theorem actual_finite_machine_has_the_required_cardinalities_and_entry :
    Fintype.card concreteInputMachine.K = 9 ∧
      Fintype.card concreteInputMachine.Λ = 28 ∧
      Fintype.card concreteInputMachine.σ = 68 ∧
      concreteInputMachine.k₀ = rawStack ∧
      concreteInputMachine.k₁ = fuelStack ∧
      concreteInputMachine.main = treeLabel .source .init ∧
      concreteInputMachine.initialState = ((none, none), true) := by
  refine ⟨?_, ?_, ?_, rfl, rfl, rfl, rfl⟩
  · exact actual_control_and_owned_labels_are_finite.1
  · exact actual_control_and_owned_labels_are_finite.2.1
  · exact actual_control_and_owned_labels_are_finite.2.2.1

theorem actual_finite_machine_initialization_and_step
    (raw : Word) (c : Cfg SmallAlphabet Unit Bool) :
    Turing.initList concreteInputMachine raw = entry ((none, none), true) raw (fun _ => []) ∧
      concreteInputMachine.step c = step sentinelCaller c :=
  ⟨initList_eq sentinelCaller true raw, machine_step_eq sentinelCaller true c⟩

/-- The constructed finite machine has actual timing data from Mathlib's own initializer. -/
def actual_finite_machine_in_linear_time (raw : Word) :
    StateTransition.EvalsToInTime concreteInputMachine.step (Turing.initList concreteInputMachine raw)
      (some (resultCfg ((none, none), true) raw (fun _ : Bool => []) (parseInputRun raw).1))
      (4 * raw.length + 7) where
  steps := inputSteps raw
  evals_in_steps := by
    change (next sentinelCaller)^[inputSteps raw]
      (some (Turing.initList (machine sentinelCaller true) raw)) = _
    rw [initList_eq]
    exact run_source sentinelCaller raw ((none, none), true) (fun _ => [])
  steps_le_m := inputSteps_le raw

/-- Even the finite package returns live; an output-only halted configuration is a later obligation. -/
theorem actual_finite_machine_returns_live_before_any_output_cleanup (raw : Word) :
    ∃ reached : concreteInputMachine.Cfg,
      (fun state : Option concreteInputMachine.Cfg => state.bind concreteInputMachine.step)^[inputSteps raw]
        (some (Turing.initList concreteInputMachine raw)) = some reached ∧
      reached.l ≠ none ∧
      ∀ output : List Bool, reached ≠ Turing.haltList concreteInputMachine output := by
  let reached : Cfg SmallAlphabet Unit Bool :=
    resultCfg ((none, none), true) raw (fun _ => []) (parseInputRun raw).1
  have executed :
      (fun state : Option concreteInputMachine.Cfg => state.bind concreteInputMachine.step)^[inputSteps raw]
        (some (Turing.initList concreteInputMachine raw)) = some reached :=
    (actual_finite_machine_in_linear_time raw).evals_in_steps
  have live : reached.l ≠ none := by
    dsimp only [reached]
    cases returned : (parseInputRun raw).1 with
    | none => exact Option.some_ne_none _
    | some fields =>
        rcases fields with ⟨source, target, bs⟩
        exact Option.some_ne_none _
  refine ⟨reached, executed, live, ?_⟩
  intro output equal
  apply live
  rw [equal]
  rfl


section RemainingFamilies
variable {K Λ R : Type} [DecidableEq K] {Γ : K → Type}
variable (caller : External Λ → Statement Γ Λ R)
variable (regs : Registers R) (ctx : ∀ k, List (Γ k))

/-- Arbitrary completed source trees are restored after their actual failed first separator. -/
theorem first_separator_failure_restores_an_arbitrary_completed_source
    [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
    (source : BinaryTree Unit) (tail : Word) (failed : (parseSeparatorRun tail).1 = none) :
    (next caller)^[4 * (treeCode source).length + 5]
        (some (entry regs (treeCode source ++ tail) ctx)) =
      some (resultCfg regs (treeCode source ++ tail) ctx none) :=
  (run_firstSeparator_failure_trace caller source tail regs ctx failed).iterate caller

/-- Both literal tree codes return in order when their actual second separator fails. -/
theorem second_separator_failure_restores_both_arbitrary_completed_trees
    [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
    (source target : BinaryTree Unit) (tail : Word) (failed : (parseSeparatorRun tail).1 = none) :
    (next caller)^[4 * (treeCode source).length + 4 * (treeCode target).length + 11]
        (some (entry regs (treeCode source ++ separatorTag :: (treeCode target ++ tail)) ctx)) =
      some (resultCfg regs (treeCode source ++ separatorTag :: (treeCode target ++ tail)) ctx none) :=
  (run_secondSeparator_failure_trace caller source target tail regs ctx failed).iterate caller

/-- A genuine blocked bit suffix restores the accepted bit prefix and both earlier tree codes. -/
theorem blocked_bits_restore_every_completed_prefix_in_order
    [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
    (source target : BinaryTree Unit) (bs : Bits) (tail : Word) (blocked : BitsBlocked tail) :
    (next caller)^[4 * (treeCode source).length + 4 * (treeCode target).length + 2 * bs.length + 14]
        (some (entry regs
          (treeCode source ++ separatorTag :: (treeCode target ++ separatorTag :: (bitTags bs ++ tail))) ctx)) =
      some (resultCfg regs
        (treeCode source ++ separatorTag :: (treeCode target ++ separatorTag :: (bitTags bs ++ tail))) ctx none) :=
  (run_bits_failure_trace caller source target bs tail regs ctx blocked).iterate caller

/-- Every nonempty suffix selects the actual EOF rollback without traversing that suffix. -/
theorem arbitrary_EOF_failure_keeps_its_entire_unread_tail
    [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
    (source target : BinaryTree Unit) (bs : Bits) (tag : Tag) (tail : Word) :
    (next caller)^[4 * (treeCode source).length + 4 * (treeCode target).length + 4 * bs.length + 18]
        (some (entry regs (inputCode source target bs ++ tag :: tail) ctx)) =
      some (resultCfg regs (inputCode source target bs ++ tag :: tail) ctx none) :=
  (run_trailing_trace caller source target bs (tag :: tail) regs ctx (by simp)).iterate caller

/-- Both bit rollback loops retain their own label until a separate actual empty probe. -/
theorem fuel_and_bit_rollback_empty_probes_are_actual_steps
    [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
    (raw rev : Word) (pending : List Unit) (outputs : TreeSide → Word) (fuel bitsReverse : Bits) :
    (next caller)^[fuel.length]
        (some (cfg (some (phaseLabel .fuelUndo)) regs raw rev pending outputs fuel bitsReverse ctx)) =
      some (cfg (some (phaseLabel .fuelUndo)) (if fuel = [] then regs else reset regs)
        raw rev pending outputs [] (fuel.reverse ++ bitsReverse) ctx) ∧
    (next caller)^[fuel.length + 1]
        (some (cfg (some (phaseLabel .fuelUndo)) regs raw rev pending outputs fuel bitsReverse ctx)) =
      some (cfg (some (phaseLabel .bitsUndo)) (reset regs)
        raw rev pending outputs [] (fuel.reverse ++ bitsReverse) ctx) ∧
    (next caller)^[bitsReverse.length]
        (some (cfg (some (phaseLabel .bitsUndo)) regs raw rev pending outputs fuel bitsReverse ctx)) =
      some (cfg (some (phaseLabel .bitsUndo)) (if bitsReverse = [] then regs else reset regs)
        (bitTags bitsReverse.reverse ++ raw) rev pending outputs fuel [] ctx) ∧
    (next caller)^[bitsReverse.length + 1]
        (some (cfg (some (phaseLabel .bitsUndo)) regs raw rev pending outputs fuel bitsReverse ctx)) =
      some (cfg (some (phaseLabel .restoreSep2)) (reset regs)
        (bitTags bitsReverse.reverse ++ raw) rev pending outputs fuel [] ctx) := by
  refine ⟨?_, (fuelUndo_run caller raw rev pending regs outputs fuel bitsReverse ctx).iterate caller,
    ?_, (bitsUndo_run caller raw rev pending regs outputs fuel bitsReverse ctx).iterate caller⟩
  · simpa only [List.append_nil] using
      (fuelUndo_prefix_run caller fuel [] raw rev pending regs outputs bitsReverse ctx).iterate caller
  · simpa only [List.append_nil] using
      (bitsUndo_prefix_run caller bitsReverse [] raw rev pending regs outputs fuel ctx).iterate caller

/-- Both tree rollback loops also distinguish the last cell transfer from their empty probe. -/
theorem tree_rollback_empty_probes_are_actual_steps
    [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
    (d : TreeSide) (word raw rev : Word) (pending : List Unit) (outputs : TreeSide → Word)
    (fuel bitsReverse : Bits) :
    (next caller)^[word.length]
        (some (cfg (some (phaseLabel (toReversePhase d))) regs raw rev pending
          (Function.update outputs d word) fuel bitsReverse ctx)) =
      some (cfg (some (phaseLabel (toReversePhase d))) (if word = [] then regs else reset regs)
        raw (word.reverse ++ rev) pending (Function.update outputs d []) fuel bitsReverse ctx) ∧
    (next caller)^[word.length + 1]
        (some (cfg (some (phaseLabel (toReversePhase d))) regs raw rev pending
          (Function.update outputs d word) fuel bitsReverse ctx)) =
      some (cfg (some (phaseLabel (toRawPhase d))) (reset regs)
        raw (word.reverse ++ rev) pending (Function.update outputs d []) fuel bitsReverse ctx) ∧
    (next caller)^[rev.length]
        (some (cfg (some (phaseLabel (toRawPhase d))) regs raw rev pending outputs fuel bitsReverse ctx)) =
      some (cfg (some (phaseLabel (toRawPhase d))) (if rev = [] then regs else reset regs)
        (rev.reverse ++ raw) [] pending outputs fuel bitsReverse ctx) ∧
    (next caller)^[rev.length + 1]
        (some (cfg (some (phaseLabel (toRawPhase d))) regs raw rev pending outputs fuel bitsReverse ctx)) =
      some (cfg (some (afterRollback d)) (reset regs)
        (rev.reverse ++ raw) [] pending outputs fuel bitsReverse ctx) := by
  refine ⟨?_, (toReverse_run caller d word raw rev pending regs outputs fuel bitsReverse ctx).iterate caller,
    ?_, (toRaw_run caller d raw rev pending regs outputs fuel bitsReverse ctx).iterate caller⟩
  · simpa only [List.append_nil] using
      (toReverse_prefix_run caller d word [] raw rev pending regs outputs fuel bitsReverse ctx).iterate caller
  · simpa only [List.append_nil] using
      (toRaw_prefix_run caller d rev [] raw pending regs outputs fuel bitsReverse ctx).iterate caller

end RemainingFamilies

end Examples.RotationCertificateInputParserMachine
