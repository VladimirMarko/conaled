import Applications.Resources.RotationCertificate.TreeParserMachine
import Examples.RotationCertificateParsing

/-!
# Connected executions of the open tree-prefix machine

The expectations were fixed independently in the maintained preparation paper
before this implementation. These clients use actual finite phase equations,
retain arbitrary old output and protected data, and distinguish live handoffs
from subsequent caller execution. Source-parser work and machine transitions
are separate observations.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.RotationCertificateTreeParserMachine
open Trees Resources
open Resources.RotationCertificate
open TreeParserMachine
open RotationDistanceExample (empty singleton leftTwo rightTwo)

/-- Two finite protected alphabets retain genuinely different kinds of data. -/
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

def oldOutputs : Bool → Word
  | false => [15, 6]
  | true => [2, 10, 11]

def staleRegisters : Registers Bool := ((some 15, some ()), true)

def haltCaller : External Bool Unit → Statement Bool SmallAlphabet Unit Bool :=
  fun _ => .halt

theorem concrete_control_is_finite :
    Fintype.card (StackId Bool Bool) = 7 ∧
      Fintype.card (Label Bool Unit) = 15 ∧
      Fintype.card (Registers Bool) = 68 := by
  decide

section Context
variable {D K Λ R : Type} [DecidableEq D] [DecidableEq K]
variable {Γ : K → Type}
variable (caller : External D Λ → Statement D Γ Λ R)
variable (regs : Registers R) (outputs : D → Word) (ctx : ∀ k, List (Γ k))

/-- Nil consumes only its one actual tag and prepends it to arbitrary old output. -/
theorem nil_leaves_the_arbitrary_suffix
    [Fintype D] [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
    (d : D) (tail : Word) :
    (next caller)^[4]
        (some (cfg (some (phaseLabel d .init)) regs (emptyTag :: tail) [] [] outputs ctx)) =
      some (cfg (some (resultLabel d .success)) (reset regs) tail [] []
        (Function.update outputs d (emptyTag :: outputs d)) ctx) := by
  calc
    _ = (next caller)^[3]
        (some (cfg (some (phaseLabel d .scan)) (reset regs)
          (emptyTag :: tail) [] [()] outputs ctx)) :=
      iterate_step caller 3 _ _ (init_step caller d (emptyTag :: tail) [] [] regs outputs ctx)
    _ = (next caller)^[2]
        (some (cfg (some (phaseLabel d .emit)) (reset regs)
          tail [emptyTag] [] outputs ctx)) :=
      iterate_step caller 2 _ _ (scan_step_empty caller d tail [] [()] (reset regs) outputs ctx)
    _ = _ := emit_iterate caller d tail [emptyTag] [] (reset regs) outputs ctx

/-- Empty input still executes init, rejection, rollback and both cleanup probes. -/
theorem empty_input_fails_in_five
    [Fintype D] [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
    (d : D) :
    (next caller)^[5]
        (some (cfg (some (phaseLabel d .init)) regs [] [] [] outputs ctx)) =
      some (cfg (some (resultLabel d .failure)) (reset regs) [] [] [] outputs ctx) := by
  calc
    _ = (next caller)^[4]
        (some (cfg (some (phaseLabel d .scan)) (reset regs) [] [] [()] outputs ctx)) :=
      iterate_step caller 4 _ _ (init_step caller d [] [] [] regs outputs ctx)
    _ = (next caller)^[3]
        (some (cfg (some (phaseLabel d .undo)) (reset regs) [] [] [()] outputs ctx)) :=
      iterate_step caller 3 _ _ (scan_step_nil caller d [] [()] (reset regs) outputs ctx)
    _ = _ := undo_drop_iterate caller d [] [] [()] (reset regs) outputs ctx

/-- A foreign head and everything after it survive the complete actual rollback. -/
theorem foreign_head_restores_its_whole_word
    [Fintype D] [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
    (d : D) (tag : Tag) (tail : Word) (notNode : tag ≠ nodeTag)
    (notEmpty : tag ≠ emptyTag) :
    (next caller)^[5]
        (some (cfg (some (phaseLabel d .init)) regs (tag :: tail) [] [] outputs ctx)) =
      some (cfg (some (resultLabel d .failure)) (reset regs)
        (tag :: tail) [] [] outputs ctx) := by
  calc
    _ = (next caller)^[4]
        (some (cfg (some (phaseLabel d .scan)) (reset regs)
          (tag :: tail) [] [()] outputs ctx)) :=
      iterate_step caller 4 _ _ (init_step caller d (tag :: tail) [] [] regs outputs ctx)
    _ = (next caller)^[3]
        (some (cfg (some (phaseLabel d .undo)) (reset regs)
          (tag :: tail) [] [()] outputs ctx)) :=
      iterate_step caller 3 _ _
        (scan_step_foreign caller d tag tail [] [()] (reset regs) outputs ctx notNode notEmpty)
    _ = _ := undo_drop_iterate caller d (tag :: tail) [] [()] (reset regs) outputs ctx

/-- The transfer actually reverses a nonpalindromic word above the old suffix. -/
theorem nonpalindromic_emit_retains_old_output
    [Fintype D] [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
    (d : D) (raw : Word) (pending : List Unit) :
    (next caller)^[4]
        (some (cfg (some (phaseLabel d .emit)) regs raw
          [emptyTag, nodeTag, nodeTag] pending outputs ctx)) =
      some (cfg (some (resultLabel d .success)) (reset regs) raw [] pending
        (Function.update outputs d ([nodeTag, nodeTag, emptyTag] ++ outputs d)) ctx) :=
  emit_iterate caller d raw [emptyTag, nodeTag, nodeTag] pending regs outputs ctx

/-- Undo uses the same orientation but writes to raw, leaving every output alone. -/
theorem nonpalindromic_undo_retains_the_blocked_tail
    [Fintype D] [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
    (d : D) (raw : Word) (pending : List Unit) :
    (next caller)^[4]
        (some (cfg (some (phaseLabel d .undo)) regs raw
          [emptyTag, nodeTag, nodeTag] pending outputs ctx)) =
      some (cfg (some (phaseLabel d .dropPending)) (reset regs)
        ([nodeTag, nodeTag, emptyTag] ++ raw) [] pending outputs ctx) :=
  undo_iterate caller d raw [emptyTag, nodeTag, nodeTag] pending regs outputs ctx

/-- A generalized emit call does not manufacture the ordinary empty-pending invariant. -/
theorem emit_preserves_nonempty_pending
    [Fintype D] [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
    (d : D) (raw : Word) :
    (next caller)^[2]
        (some (cfg (some (phaseLabel d .emit)) regs raw [emptyTag] [()] outputs ctx)) =
      some (cfg (some (resultLabel d .success)) (reset regs) raw [] [()]
        (Function.update outputs d (emptyTag :: outputs d)) ctx) :=
  emit_iterate caller d raw [emptyTag] [()] regs outputs ctx

theorem pending_cleanup_counts_each_token_and_empty_probe
    [Fintype D] [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
    (d : D) (raw rev : Word) (count : Nat) :
    (next caller)^[count + 1]
        (some (cfg (some (phaseLabel d .dropPending)) regs raw rev
          (List.replicate count ()) outputs ctx)) =
      some (cfg (some (resultLabel d .failure)) (reset regs) raw rev [] outputs ctx) := by
  simpa only [List.length_replicate] using
    dropPending_iterate caller d raw rev (List.replicate count ()) regs outputs ctx


/-- The four independent codes retain arbitrary tails and prepend to the chosen old output. -/
theorem literal_codes_keep_their_shape_and_tail
    [Fintype D] [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
    (d : D) (tail : Word) :
    (next caller)^[8]
        (some (cfg (some (phaseLabel d .init)) regs
          ([nodeTag, emptyTag, emptyTag] ++ tail) [] [] outputs ctx)) =
      some (cfg (some (resultLabel d .success)) (reset regs) tail [] []
        (Function.update outputs d ([nodeTag, emptyTag, emptyTag] ++ outputs d)) ctx) ∧
    (next caller)^[12]
        (some (cfg (some (phaseLabel d .init)) regs
          ([nodeTag, nodeTag, emptyTag, emptyTag, emptyTag] ++ tail) [] [] outputs ctx)) =
      some (cfg (some (resultLabel d .success)) (reset regs) tail [] []
        (Function.update outputs d
          ([nodeTag, nodeTag, emptyTag, emptyTag, emptyTag] ++ outputs d)) ctx) ∧
    (next caller)^[12]
        (some (cfg (some (phaseLabel d .init)) regs
          ([nodeTag, emptyTag, nodeTag, emptyTag, emptyTag] ++ tail) [] [] outputs ctx)) =
      some (cfg (some (resultLabel d .success)) (reset regs) tail [] []
        (Function.update outputs d
          ([nodeTag, emptyTag, nodeTag, emptyTag, emptyTag] ++ outputs d)) ctx) :=
  ⟨run_code caller d singleton.val tail regs outputs ctx,
    run_code caller d leftTwo.val tail regs outputs ctx,
    run_code caller d rightTwo.val tail regs outputs ctx⟩

/-- Truncation restores the accepted prefix, including its nonpalindromic order. -/
theorem incomplete_codes_restore_all_consumed_material
    [Fintype D] [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
    (d : D) :
    (next caller)^[8]
        (some (cfg (some (phaseLabel d .init)) regs [nodeTag] [] [] outputs ctx)) =
      some (cfg (some (resultLabel d .failure)) (reset regs) [nodeTag] [] [] outputs ctx) ∧
    (next caller)^[9]
        (some (cfg (some (phaseLabel d .init)) regs [nodeTag, emptyTag] [] [] outputs ctx)) =
      some (cfg (some (resultLabel d .failure)) (reset regs)
        [nodeTag, emptyTag] [] [] outputs ctx) ∧
    (next caller)^[11]
        (some (cfg (some (phaseLabel d .init)) regs [nodeTag, nodeTag] [] [] outputs ctx)) =
      some (cfg (some (resultLabel d .failure)) (reset regs)
        [nodeTag, nodeTag] [] [] outputs ctx) ∧
    (next caller)^[12]
        (some (cfg (some (phaseLabel d .init)) regs
          [nodeTag, nodeTag, emptyTag] [] [] outputs ctx)) =
      some (cfg (some (resultLabel d .failure)) (reset regs)
        [nodeTag, nodeTag, emptyTag] [] [] outputs ctx) :=
  ⟨run_of_none caller d [nodeTag] regs outputs ctx rfl,
    run_of_none caller d [nodeTag, emptyTag] regs outputs ctx rfl,
    run_of_none caller d [nodeTag, nodeTag] regs outputs ctx rfl,
    run_of_none caller d [nodeTag, nodeTag, emptyTag] regs outputs ctx rfl⟩

/-- The reserved blocker and its unbounded tail are retained after actual rollback. -/
theorem nonpalindromic_rejected_prefix_keeps_the_blocker
    [Fintype D] [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
    (d : D) (tail : Word) :
    (next caller)^[12]
        (some (cfg (some (phaseLabel d .init)) regs
          ([nodeTag, nodeTag, emptyTag, 15] ++ tail) [] [] outputs ctx)) =
      some (cfg (some (resultLabel d .failure)) (reset regs)
        ([nodeTag, nodeTag, emptyTag, 15] ++ tail) [] [] outputs ctx) :=
  run_of_none caller d ([nodeTag, nodeTag, emptyTag, 15] ++ tail) regs outputs ctx rfl

/-- A ghost needLeft frame is entered at scan, with two real Unit slots already present. -/
theorem needLeft_scan_completes_the_parent
    [Fintype D] [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
    (d : D) (tail : Word) :
    (next caller)^[6]
        (some (cfg (some (phaseLabel d .scan)) regs
          ([emptyTag, emptyTag] ++ tail) [nodeTag] [(), ()] outputs ctx)) =
      some (cfg (some (resultLabel d .success)) (reset regs) tail [] []
        (Function.update outputs d ([nodeTag, emptyTag, emptyTag] ++ outputs d)) ctx) :=
  scan_source caller d ([emptyTag, emptyTag] ++ tail) [.needLeft] regs outputs ctx

/-- Failure restores the prefix represented before this scan was entered. -/
theorem needLeft_scan_failure_restores_its_ghost_prefix
    [Fintype D] [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
    (d : D) (tail : Word) :
    (next caller)^[6]
        (some (cfg (some (phaseLabel d .scan)) regs [] [nodeTag] [(), ()] outputs ctx)) =
      some (cfg (some (resultLabel d .failure)) (reset regs) [nodeTag] [] [] outputs ctx) ∧
    (next caller)^[7]
        (some (cfg (some (phaseLabel d .scan)) regs
          (emptyTag :: 15 :: tail) [nodeTag] [(), ()] outputs ctx)) =
      some (cfg (some (resultLabel d .failure)) (reset regs)
        (nodeTag :: emptyTag :: 15 :: tail) [] [] outputs ctx) :=
  ⟨scan_source caller d [] [.needLeft] regs outputs ctx,
    scan_source caller d (emptyTag :: 15 :: tail) [.needLeft] regs outputs ctx⟩

/-- Serialized left subtrees remain physical material even when only one tag is unread. -/
theorem needRight_scan_moves_the_entire_left_prefix
    [Fintype D] [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
    (d : D) (left : BinaryTree Unit) (tail : Word) :
    (next caller)^[(treeCode left).length + 4]
        (some (cfg (some (phaseLabel d .scan)) regs (emptyTag :: tail)
          (nodeTag :: treeCode left).reverse [()] outputs ctx)) =
      some (cfg (some (resultLabel d .success)) (reset regs) tail [] []
        (Function.update outputs d
          (treeCode (.node () left .nil) ++ outputs d)) ctx) := by
  have executed := scan_source caller d (emptyTag :: tail) [.needRight left] regs outputs ctx
  simpa only [stackPrefix, List.nil_append, List.singleton_append, leftSlots,
    Nat.add_zero, List.replicate_one, List.length_cons, scanSteps_empty,
    Nat.le_refl, ite_true, parseTreeLoop_empty_value, resumeTreeRun, Resources.bind,
    resultCfg, Nat.add_assoc] using executed

/-- Equal frame counts and slot counts still distinguish the order of the enclosing nodes. -/
theorem mixed_ghost_frames_keep_outer_first_order
    [Fintype D] [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
    (d : D) (tail : Word) :
    (next caller)^[8]
        (some (cfg (some (phaseLabel d .scan)) regs
          ([emptyTag, emptyTag] ++ tail) [emptyTag, nodeTag, nodeTag]
          [(), ()] outputs ctx)) =
      some (cfg (some (resultLabel d .success)) (reset regs) tail [] []
        (Function.update outputs d (treeCode leftTwo.val ++ outputs d)) ctx) ∧
    (next caller)^[8]
        (some (cfg (some (phaseLabel d .scan)) regs
          ([emptyTag, emptyTag] ++ tail) [nodeTag, emptyTag, nodeTag]
          [(), ()] outputs ctx)) =
      some (cfg (some (resultLabel d .success)) (reset regs) tail [] []
        (Function.update outputs d (treeCode rightTwo.val ++ outputs d)) ctx) :=
  ⟨scan_source caller d ([emptyTag, emptyTag] ++ tail) [.needRight .nil, .needLeft]
      regs outputs ctx,
    scan_source caller d ([emptyTag, emptyTag] ++ tail) [.needLeft, .needRight .nil]
      regs outputs ctx⟩

/-- Actual emitter output enters the machine; the source and machine clocks stay distinct. -/
theorem emitted_tree_enters_the_actual_machine
    [Fintype D] [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
    (d : D) (tree : BinaryTree Unit) (tail : Word) :
    (next caller)^[4 * tree.numNodes + 4]
        (some (cfg (some (phaseLabel d .init)) regs
          (emitTreeRun tree tail).1 [] [] outputs ctx)) =
      some (cfg (some (resultLabel d .success)) (reset regs) tail [] []
        (Function.update outputs d (treeCode tree ++ outputs d)) ctx) ∧
      parseTreeRun (emitTreeRun tree tail).1 = (some (tree, tail), 7 * tree.numNodes + 3) := by
  refine ⟨?_, parseTreeRun_emit tree tail⟩
  rw [emitTreeRun_value]
  have executed := run_code caller d tree tail regs outputs ctx
  rw [treeCode_length] at executed
  have work : 2 * (2 * tree.numNodes + 1) + 2 = 4 * tree.numNodes + 4 := by omega
  rw [work] at executed
  exact executed

/-- Uniform timed evidence targets the actual first live configuration on every raw word. -/
def actual_uniform_tree_time (d : D) (raw : Word) :
    StateTransition.EvalsToInTime (step caller)
      (cfg (some (phaseLabel d .init)) regs raw [] [] outputs ctx)
      (some (resultCfg d regs raw outputs ctx (parseTreeRun raw).1))
      (3 * raw.length + 5) :=
  runInLinearTime caller d raw regs outputs ctx


/-- An old reverse tag becomes part of the emitted word, so empty reverse is essential. -/
theorem nonempty_reverse_changes_an_otherwise_valid_tree
    [Fintype D] [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
    (d : D) :
    (next caller)^[5]
        (some (cfg (some (phaseLabel d .init)) regs [emptyTag] [nodeTag] [] outputs ctx)) =
      some (cfg (some (resultLabel d .success)) (reset regs) [] [] []
        (Function.update outputs d ([nodeTag, emptyTag] ++ outputs d)) ctx) := by
  calc
    _ = (next caller)^[4]
        (some (cfg (some (phaseLabel d .scan)) (reset regs)
          [emptyTag] [nodeTag] [()] outputs ctx)) :=
      iterate_step caller 4 _ _ (init_step caller d [emptyTag] [nodeTag] [] regs outputs ctx)
    _ = (next caller)^[3]
        (some (cfg (some (phaseLabel d .emit)) (reset regs)
          [] [emptyTag, nodeTag] [] outputs ctx)) :=
      iterate_step caller 3 _ _
        (scan_step_empty caller d [] [nodeTag] [()] (reset regs) outputs ctx)
    _ = _ := emit_iterate caller d [] [emptyTag, nodeTag] [] (reset regs) outputs ctx

/-- Nonempty reverse also changes the raw word that a failure restores. -/
theorem nonempty_reverse_changes_failure_restoration
    [Fintype D] [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
    (d : D) :
    (next caller)^[6]
        (some (cfg (some (phaseLabel d .init)) regs [] [nodeTag] [] outputs ctx)) =
      some (cfg (some (resultLabel d .failure)) (reset regs) [nodeTag] [] [] outputs ctx) := by
  calc
    _ = (next caller)^[5]
        (some (cfg (some (phaseLabel d .scan)) (reset regs) [] [nodeTag] [()] outputs ctx)) :=
      iterate_step caller 5 _ _ (init_step caller d [] [nodeTag] [] regs outputs ctx)
    _ = _ := scan_nil_iterate caller d [nodeTag] [()] (reset regs) outputs ctx

/-- One old pending token makes an ordinary nil word fail after real rollback. -/
theorem nonempty_pending_rejects_a_valid_nil_word
    [Fintype D] [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
    (d : D) :
    (next caller)^[7]
        (some (cfg (some (phaseLabel d .init)) regs [emptyTag] [] [()] outputs ctx)) =
      some (cfg (some (resultLabel d .failure)) (reset regs) [emptyTag] [] [] outputs ctx) := by
  calc
    _ = (next caller)^[6]
        (some (cfg (some (phaseLabel d .scan)) (reset regs)
          [emptyTag] [] [(), ()] outputs ctx)) :=
      iterate_step caller 6 _ _ (init_step caller d [emptyTag] [] [()] regs outputs ctx)
    _ = (next caller)^[5]
        (some (cfg (some (phaseLabel d .scan)) (reset regs) [] [emptyTag] [()] outputs ctx)) :=
      iterate_step caller 5 _ _
        (scan_step_empty caller d [] [] [(), ()] (reset regs) outputs ctx)
    _ = _ := scan_nil_iterate caller d [emptyTag] [()] (reset regs) outputs ctx

/-- The same old pending token can consume a second tree that should have remained on raw. -/
theorem nonempty_pending_consumes_two_nil_words
    [Fintype D] [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
    (d : D) :
    (next caller)^[6]
        (some (cfg (some (phaseLabel d .init)) regs [emptyTag, emptyTag] [] [()] outputs ctx)) =
      some (cfg (some (resultLabel d .success)) (reset regs) [] [] []
        (Function.update outputs d ([emptyTag, emptyTag] ++ outputs d)) ctx) := by
  calc
    _ = (next caller)^[5]
        (some (cfg (some (phaseLabel d .scan)) (reset regs)
          [emptyTag, emptyTag] [] [(), ()] outputs ctx)) :=
      iterate_step caller 5 _ _ (init_step caller d [emptyTag, emptyTag] [] [()] regs outputs ctx)
    _ = (next caller)^[4]
        (some (cfg (some (phaseLabel d .scan)) (reset regs)
          [emptyTag] [emptyTag] [()] outputs ctx)) :=
      iterate_step caller 4 _ _
        (scan_step_empty caller d [emptyTag] [] [(), ()] (reset regs) outputs ctx)
    _ = (next caller)^[3]
        (some (cfg (some (phaseLabel d .emit)) (reset regs)
          [] [emptyTag, emptyTag] [] outputs ctx)) :=
      iterate_step caller 3 _ _
        (scan_step_empty caller d [] [emptyTag] [()] (reset regs) outputs ctx)
    _ = _ := emit_iterate caller d [] [emptyTag, emptyTag] [] (reset regs) outputs ctx

/-- A valid needLeft scan representation must not pass through init again. -/
theorem reinitializing_a_ghost_scan_rejects_its_completion
    [Fintype D] [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
    (d : D) :
    (next caller)^[10]
        (some (cfg (some (phaseLabel d .init)) regs
          [emptyTag, emptyTag] [nodeTag] [(), ()] outputs ctx)) =
      some (cfg (some (resultLabel d .failure)) (reset regs)
        [nodeTag, emptyTag, emptyTag] [] [] outputs ctx) := by
  calc
    _ = (next caller)^[9]
        (some (cfg (some (phaseLabel d .scan)) (reset regs)
          [emptyTag, emptyTag] [nodeTag] [(), (), ()] outputs ctx)) :=
      iterate_step caller 9 _ _
        (init_step caller d [emptyTag, emptyTag] [nodeTag] [(), ()] regs outputs ctx)
    _ = (next caller)^[8]
        (some (cfg (some (phaseLabel d .scan)) (reset regs)
          [emptyTag] [emptyTag, nodeTag] [(), ()] outputs ctx)) :=
      iterate_step caller 8 _ _
        (scan_step_empty caller d [emptyTag] [nodeTag] [(), (), ()] (reset regs) outputs ctx)
    _ = (next caller)^[7]
        (some (cfg (some (phaseLabel d .scan)) (reset regs)
          [] [emptyTag, emptyTag, nodeTag] [()] outputs ctx)) :=
      iterate_step caller 7 _ _
        (scan_step_empty caller d [] [emptyTag, nodeTag] [(), ()] (reset regs) outputs ctx)
    _ = _ := scan_nil_iterate caller d [emptyTag, emptyTag, nodeTag] [()] (reset regs) outputs ctx

/-- Rank/progress on arbitrary states does not grant those states the source representation invariant. -/
theorem zero_pending_scan_can_emit_an_incomplete_code
    [Fintype D] [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
    (d : D) :
    (next caller)^[5]
        (some (cfg (some (phaseLabel d .scan)) regs [nodeTag, emptyTag] [] [] outputs ctx)) =
      some (cfg (some (resultLabel d .success)) (reset regs) [] [] []
        (Function.update outputs d ([nodeTag, emptyTag] ++ outputs d)) ctx) ∧
      (parseTreeRun [nodeTag, emptyTag]).1 = none := by
  refine ⟨?_, rfl⟩
  calc
    _ = (next caller)^[4]
        (some (cfg (some (phaseLabel d .scan)) (reset regs)
          [emptyTag] [nodeTag] [()] outputs ctx)) :=
      iterate_step caller 4 _ _ (scan_step_node caller d [emptyTag] [] [] regs outputs ctx)
    _ = (next caller)^[3]
        (some (cfg (some (phaseLabel d .emit)) (reset regs)
          [] [emptyTag, nodeTag] [] outputs ctx)) :=
      iterate_step caller 3 _ _
        (scan_step_empty caller d [] [nodeTag] [()] (reset regs) outputs ctx)
    _ = _ := emit_iterate caller d [] [emptyTag, nodeTag] [] (reset regs) outputs ctx

/-- Every requested prefix is an actual execution with one shared reached configuration. -/
theorem actual_prefix_keeps_context_and_bounds_all_cells
    [Fintype D] [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
    (d : D) (raw : Word) (n : Nat) (bound : n ≤ runSteps raw) :
    ∃ reached : Cfg D Γ Λ R,
      (next caller)^[n]
        (some (cfg (some (phaseLabel d .init)) regs raw [] [] outputs ctx)) = some reached ∧
      remainingSteps reached = runSteps raw - n ∧
      reached.var.2 = regs.2 ∧ destination reached = some d ∧
      (∀ other, other ≠ d → reached.stk (.inl (.output other)) = outputs other) ∧
      (∀ k, reached.stk (.inr k) = ctx k) ∧
      stackCells reached ≤ 2 * raw.length + outputCells outputs + contextCells ctx + 1 ∧
      (n < runSteps raw ↔ Owned reached.l) ∧
      (0 < n → reached.var.1 = (none, none)) := by
  obtain ⟨reached, executed, rank, _, owned, cleared⟩ :=
    run_prefix caller d raw regs outputs ctx n bound
  obtain ⟨registers, dest, others, frameData⟩ :=
    prefix_preserves caller d .init raw [] [] regs outputs ctx n reached bound executed
  exact ⟨reached, executed, rank, registers, dest, others, frameData,
    prefix_stackCells_le caller d raw regs outputs ctx n reached bound executed, owned, cleared⟩

/-- Changing any external caller body cannot change this inclusive first-return interval. -/
theorem different_callers_share_every_owned_prefix
    [Fintype D] [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
    (other : External D Λ → Statement D Γ Λ R) (d : D) (raw : Word)
    (n : Nat) (bound : n ≤ runSteps raw) :
    (next caller)^[n]
        (some (cfg (some (phaseLabel d .init)) regs raw [] [] outputs ctx)) =
      (next other)^[n]
        (some (cfg (some (phaseLabel d .init)) regs raw [] [] outputs ctx)) :=
  phase_prefix_caller_independent caller other d .init raw [] [] regs outputs ctx n bound

/-- The peak is exhibited before failure for every length, including the empty input. -/
theorem all_node_words_attain_the_workspace_bound
    [Fintype D] [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
    (d : D) (count : Nat) :
    (next caller)^[count + 1]
        (some (cfg (some (phaseLabel d .init)) regs
          (List.replicate count nodeTag) [] [] outputs ctx)) =
      some (cfg (some (phaseLabel d .scan)) (reset regs) []
        (List.replicate count nodeTag) (List.replicate (count + 1) ()) outputs ctx) ∧
      count + 1 < runSteps (List.replicate count nodeTag) ∧
      stackCells (cfg (Λ := Λ) (some (phaseLabel d .scan)) (reset regs) []
        (List.replicate count nodeTag) (List.replicate (count + 1) ()) outputs ctx) =
        2 * count + outputCells outputs + contextCells ctx + 1 := by
  refine ⟨nodes_prefix caller d count regs outputs ctx, ?_, ?_⟩
  · rw [runSteps_nodes]; omega
  · simp only [stackCells, cfg, List.length_nil, List.length_replicate]
    dsimp only [outputCells, contextCells]
    omega

/-- The actual first return, rather than a later caller-produced label, recognizes the grammar. -/
theorem actual_first_success_recognizes_exactly_one_prefix
    [Fintype D] [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
    (d : D) (raw : Word) (tree : BinaryTree Unit) (tail : Word) :
    FirstSuccess caller d raw tree tail regs outputs ctx ↔ raw = treeCode tree ++ tail :=
  firstSuccess_code_iff caller d raw tree tail regs outputs ctx

/-- Arbitrary unfinished ghost frames retain both old output and the full reconstructed prefix. -/
theorem needRight_foreign_failure_keeps_its_large_prefix
    [Fintype D] [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
    (d : D) (left : BinaryTree Unit) (tag : Tag) (tail : Word)
    (notNode : tag ≠ nodeTag) (notEmpty : tag ≠ emptyTag) :
    (next caller)^[(treeCode left).length + 5]
        (some (cfg (some (phaseLabel d .scan)) regs (tag :: tail)
          (nodeTag :: treeCode left).reverse [()] outputs ctx)) =
      some (cfg (some (resultLabel d .failure)) (reset regs)
        ((nodeTag :: treeCode left) ++ tag :: tail) [] [] outputs ctx) := by
  have executed := scan_foreign_iterate caller d tag tail
    (nodeTag :: treeCode left).reverse [()] regs outputs ctx notNode notEmpty
  simpa only [List.length_reverse, List.length_cons, List.length_nil,
    List.reverse_reverse, Nat.add_assoc] using executed

/-- The source already stores the left tree, while the machine must move its serialized tags. -/
theorem needRight_source_and_machine_work_are_distinct
    [Fintype D] [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
    (d : D) (left : BinaryTree Unit) (tail : Word) :
    parseTreeLoop (emptyTag :: tail) [.needRight left] =
        (some (.node () left .nil, tail), 5) ∧
      (next caller)^[(treeCode left).length + 4]
        (some (cfg (some (phaseLabel d .scan)) regs (emptyTag :: tail)
          (nodeTag :: treeCode left).reverse [()] outputs ctx)) =
      some (cfg (some (resultLabel d .success)) (reset regs) tail [] []
        (Function.update outputs d (treeCode (.node () left .nil) ++ outputs d)) ctx) :=
  ⟨rfl, needRight_scan_moves_the_entire_left_prefix caller regs outputs ctx d left tail⟩


/-- A source value helper justifies the actual generic needRight machine endpoint. -/
theorem needRight_completes_with_an_arbitrary_right_tree
    [Fintype D] [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
    (d : D) (left right : BinaryTree Unit) (tail : Word) :
    (next caller)^[(treeCode left).length + 2 * (treeCode right).length + 2]
        (some (cfg (some (phaseLabel d .scan)) regs (treeCode right ++ tail)
          (nodeTag :: treeCode left).reverse [()] outputs ctx)) =
      some (cfg (some (resultLabel d .success)) (reset regs) tail [] []
        (Function.update outputs d (treeCode (.node () left right) ++ outputs d)) ctx) := by
  have returned : (parseTreeLoop (treeCode right ++ tail) [.needRight left]).1 =
      some (.node () left right, tail) := by
    rw [parseTreeLoop_code_value]
    rfl
  have work : scanSteps (treeCode right ++ tail) 1 (nodeTag :: treeCode left).length =
      (treeCode left).length + 2 * (treeCode right).length + 2 := by
    rw [scanSteps_code right tail 0 (nodeTag :: treeCode left).length]
    simp only [ite_true, List.length_cons]
    omega
  have executed := scan_source caller d (treeCode right ++ tail) [.needRight left] regs outputs ctx
  change (next caller)^[scanSteps (treeCode right ++ tail) 1 (nodeTag :: treeCode left).length]
      (some (cfg (some (phaseLabel d .scan)) regs (treeCode right ++ tail)
        (nodeTag :: treeCode left).reverse [()] outputs ctx)) =
    some (resultCfg d regs ((nodeTag :: treeCode left) ++ (treeCode right ++ tail))
      outputs ctx (parseTreeLoop (treeCode right ++ tail) [.needRight left]).1) at executed
  rw [work, returned] at executed
  exact executed

/-- Both children are actually scanned; the existing node prefix is actually emitted too. -/
theorem needLeft_completes_with_two_arbitrary_children
    [Fintype D] [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
    (d : D) (left right : BinaryTree Unit) (tail : Word) :
    (next caller)^[2 * ((treeCode left).length + (treeCode right).length) + 2]
        (some (cfg (some (phaseLabel d .scan)) regs
          (treeCode left ++ treeCode right ++ tail) [nodeTag] [(), ()] outputs ctx)) =
      some (cfg (some (resultLabel d .success)) (reset regs) tail [] []
        (Function.update outputs d (treeCode (.node () left right) ++ outputs d)) ctx) := by
  have returned : (parseTreeLoop (treeCode left ++ treeCode right ++ tail) [.needLeft]).1 =
      some (.node () left right, tail) := by
    rw [List.append_assoc, parseTreeLoop_code_value]
    change (parseTreeLoop (treeCode right ++ tail) [.needRight left]).1 = _
    rw [parseTreeLoop_code_value]
    rfl
  have work : scanSteps (treeCode left ++ treeCode right ++ tail) 2 1 =
      2 * ((treeCode left).length + (treeCode right).length) + 2 := by
    rw [List.append_assoc, scanSteps_code left (treeCode right ++ tail) 1 1]
    simp only [Nat.one_ne_zero, ite_false]
    rw [scanSteps_code right tail 0 (1 + (treeCode left).length)]
    simp only [ite_true]
    omega
  have executed := scan_source caller d (treeCode left ++ treeCode right ++ tail)
    [.needLeft] regs outputs ctx
  change (next caller)^[scanSteps (treeCode left ++ treeCode right ++ tail) 2 1]
      (some (cfg (some (phaseLabel d .scan)) regs
        (treeCode left ++ treeCode right ++ tail) [nodeTag] [(), ()] outputs ctx)) =
    some (resultCfg d regs (nodeTag :: (treeCode left ++ treeCode right ++ tail))
      outputs ctx (parseTreeLoop (treeCode left ++ treeCode right ++ tail) [.needLeft]).1) at executed
  rw [work, returned] at executed
  exact executed

private theorem source_nodes_eof (count : Nat) (frames : List TreeFrame) :
    parseTreeLoop (List.replicate count nodeTag) frames = (none, 2 * count + 2) := by
  induction count generalizing frames with
  | zero => rfl
  | succ count ih =>
      rw [List.replicate_succ, parseTreeLoop_node, ih]
      change (none, 2 + (2 * count + 2)) = (none, 2 * (count + 1) + 2)
      have work : 2 + (2 * count + 2) = 2 * (count + 1) + 2 := by omega
      rw [work]

private theorem source_nodes_foreign (count : Nat) (frames : List TreeFrame)
    (tag : Tag) (tail : Word) (notNode : tag ≠ nodeTag) (notEmpty : tag ≠ emptyTag) :
    parseTreeLoop (List.replicate count nodeTag ++ tag :: tail) frames =
      (none, 2 * count + 2) := by
  induction count generalizing frames with
  | zero => exact parseTreeLoop_foreign tag tail frames notNode notEmpty
  | succ count ih =>
      rw [List.replicate_succ, List.cons_append, parseTreeLoop_node, ih]
      change (none, 2 + (2 * count + 2)) = (none, 2 * (count + 1) + 2)
      have work : 2 + (2 * count + 2) = 2 * (count + 1) + 2 := by omega
      rw [work]

/-- Source failure and actual cleanup agree on every all-node input, with different clocks. -/
theorem all_nodes_restore_after_their_exact_failure_time
    [Fintype D] [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
    (d : D) (count : Nat) :
    parseTreeRun (List.replicate count nodeTag) = (none, 2 * count + 2) ∧
      (next caller)^[3 * count + 5]
        (some (cfg (some (phaseLabel d .init)) regs
          (List.replicate count nodeTag) [] [] outputs ctx)) =
      some (cfg (some (resultLabel d .failure)) (reset regs)
        (List.replicate count nodeTag) [] [] outputs ctx) := by
  have source := source_nodes_eof count []
  refine ⟨source, ?_⟩
  have executed := run_of_none caller d (List.replicate count nodeTag) regs outputs ctx
    (congrArg Prod.fst source)
  simpa only [runSteps_nodes] using executed

/-- Arbitrary blocked tails are not traversed even after an arbitrarily long unfinished prefix. -/
theorem all_nodes_before_a_foreign_tag_restore_without_reading_its_tail
    [Fintype D] [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
    (d : D) (count : Nat) (tag : Tag) (tail : Word)
    (notNode : tag ≠ nodeTag) (notEmpty : tag ≠ emptyTag) :
    parseTreeRun (List.replicate count nodeTag ++ tag :: tail) = (none, 2 * count + 2) ∧
      (next caller)^[3 * count + 5]
        (some (cfg (some (phaseLabel d .init)) regs
          (List.replicate count nodeTag ++ tag :: tail) [] [] outputs ctx)) =
      some (cfg (some (resultLabel d .failure)) (reset regs)
        (List.replicate count nodeTag ++ tag :: tail) [] [] outputs ctx) := by
  have source := source_nodes_foreign count [] tag tail notNode notEmpty
  refine ⟨source, ?_⟩
  have executed := run_of_none caller d (List.replicate count nodeTag ++ tag :: tail)
    regs outputs ctx (congrArg Prod.fst source)
  simpa only [runSteps_nodes_foreign count tag tail notNode notEmpty] using executed

/-- A real caller continuation consumes the exact source-connected endpoint of this timed datum. -/
def actual_tree_time_composes_with_a_continuation (d : D) (raw : Word)
    (budget : Nat) (finish : Option (Cfg D Γ Λ R))
    (continued : StateTransition.EvalsToInTime (step caller)
      (resultCfg d regs raw outputs ctx (parseTreeRun raw).1) finish budget) :
    StateTransition.EvalsToInTime (step caller)
      (cfg (some (phaseLabel d .init)) regs raw [] [] outputs ctx) finish
      (3 * raw.length + 5 + budget) := by
  simpa only [Nat.add_comm] using
    StateTransition.EvalsToInTime.trans (step caller) (3 * raw.length + 5) budget
      (cfg (some (phaseLabel d .init)) regs raw [] [] outputs ctx)
      (resultCfg d regs raw outputs ctx (parseTreeRun raw).1) finish
      (runInLinearTime caller d raw regs outputs ctx) continued


/-- General phase clients permit arbitrary material, not only valid tree codes. -/
theorem arbitrary_emit_and_rollback_have_their_literal_endpoints
    [Fintype D] [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
    (d : D) (raw rev : Word) (pending : List Unit) :
    (next caller)^[rev.length + 1]
        (some (cfg (some (phaseLabel d .emit)) regs raw rev pending outputs ctx)) =
      some (cfg (some (resultLabel d .success)) (reset regs) raw [] pending
        (Function.update outputs d (rev.reverse ++ outputs d)) ctx) ∧
      (next caller)^[rev.length + pending.length + 2]
        (some (cfg (some (phaseLabel d .undo)) regs raw rev pending outputs ctx)) =
      some (cfg (some (resultLabel d .failure)) (reset regs)
        (rev.reverse ++ raw) [] [] outputs ctx) :=
  ⟨emit_iterate caller d raw rev pending regs outputs ctx,
    undo_drop_iterate caller d raw rev pending regs outputs ctx⟩

/-- The actual input emitter supplies the word, but this component stops at its first separator. -/
theorem actual_input_emitter_enters_only_the_first_tree_call
    [Fintype D] [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
    (d : D) (source target : BinaryTree Unit) (bs : BinaryCounter.Bits) :
    (next caller)^[2 * (treeCode source).length + 2]
        (some (cfg (some (phaseLabel d .init)) regs
          (emitInputRun source target bs).1 [] [] outputs ctx)) =
      some (cfg (some (resultLabel d .success)) (reset regs)
        (separatorTag :: (treeCode target ++ separatorTag :: (bitTags bs ++ [endInputTag])))
        [] [] (Function.update outputs d (treeCode source ++ outputs d)) ctx) := by
  rw [emitInputRun_value]
  simpa only [inputCode, List.append_assoc, List.cons_append, List.nil_append] using
    run_code caller d source
      (separatorTag :: (treeCode target ++ separatorTag :: (bitTags bs ++ [endInputTag])))
      regs outputs ctx

/-- The same emitted rotation input has first-tree machine time 12 and full source-parser work 46. -/
theorem emitted_rotation_separates_tree_machine_from_full_source_parser
    [Fintype D] [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
    (d : D) :
    (next caller)^[12]
        (some (cfg (some (phaseLabel d .init)) regs
          (emitInputRun leftTwo.val rightTwo.val [true]).1 [] [] outputs ctx)) =
      some (cfg (some (resultLabel d .success)) (reset regs)
        [separatorTag, nodeTag, emptyTag, nodeTag, emptyTag, emptyTag,
          separatorTag, bitOneTag, endInputTag]
        [] [] (Function.update outputs d (treeCode leftTwo.val ++ outputs d)) ctx) ∧
      parseInputRun (emitInputRun leftTwo.val rightTwo.val [true]).1 =
        (some (leftTwo.val, rightTwo.val, [true]), 46) :=
  ⟨actual_input_emitter_enters_only_the_first_tree_call caller regs outputs ctx d
      leftTwo.val rightTwo.val [true],
    parseInputRun_emit leftTwo.val rightTwo.val [true]⟩

/-- Nil already refutes identifying the successful source tariff with actual machine time. -/
theorem nil_source_work_is_smaller_than_its_actual_machine_time
    [Fintype D] [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
    (d : D) (tail : Word) :
    parseTreeRun (emptyTag :: tail) = (some (empty.val, tail), 3) ∧
      (next caller)^[4]
        (some (cfg (some (phaseLabel d .init)) regs (emptyTag :: tail) [] [] outputs ctx)) =
      some (cfg (some (resultLabel d .success)) (reset regs) tail [] []
        (Function.update outputs d (emptyTag :: outputs d)) ctx) ∧
      (parseTreeRun (emptyTag :: tail)).2 < runSteps (emptyTag :: tail) :=
  ⟨rfl, nil_leaves_the_arbitrary_suffix caller regs outputs ctx d tail, by change (3 : Nat) < 4; decide⟩

/-- The same represented mixed frames have source work 10 and actual scan time 8. -/
theorem mixed_frame_source_and_machine_clocks
    [Fintype D] [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
    (d : D) (tail : Word) :
    parseTreeLoop ([emptyTag, emptyTag] ++ tail) [.needRight .nil, .needLeft] =
        (some (leftTwo.val, tail), 10) ∧
      parseTreeLoop ([emptyTag, emptyTag] ++ tail) [.needLeft, .needRight .nil] =
        (some (rightTwo.val, tail), 10) ∧
      (next caller)^[8]
        (some (cfg (some (phaseLabel d .scan)) regs
          ([emptyTag, emptyTag] ++ tail) [emptyTag, nodeTag, nodeTag]
          [(), ()] outputs ctx)) =
      some (cfg (some (resultLabel d .success)) (reset regs) tail [] []
        (Function.update outputs d (treeCode leftTwo.val ++ outputs d)) ctx) :=
  ⟨rfl, rfl, (mixed_ghost_frames_keep_outer_first_order caller regs outputs ctx d tail).1⟩


/-- A partial transfer retains its literal unread reverse suffix and handles zero steps honestly. -/
theorem partial_transfers_preserve_the_unread_material
    [Fintype D] [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
    (d : D) (raw pref rest : Word) (pending : List Unit) :
    (next caller)^[pref.length]
        (some (cfg (some (phaseLabel d .emit)) regs raw (pref ++ rest) pending outputs ctx)) =
      some (cfg (some (phaseLabel d .emit)) (if pref = [] then regs else reset regs)
        raw rest pending (Function.update outputs d (pref.reverse ++ outputs d)) ctx) ∧
      (next caller)^[pref.length]
        (some (cfg (some (phaseLabel d .undo)) regs raw (pref ++ rest) pending outputs ctx)) =
      some (cfg (some (phaseLabel d .undo)) (if pref = [] then regs else reset regs)
        (pref.reverse ++ raw) rest pending outputs ctx) :=
  ⟨emit_prefix caller d raw pref rest pending regs outputs ctx,
    undo_prefix caller d raw pref rest pending regs outputs ctx⟩

/-- Failure decomposition and cleanup time describe the same original raw word and execution. -/
theorem every_actual_source_failure_has_its_exact_cleanup_decomposition
    [Fintype D] [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
    (d : D) (raw : Word) (failed : (parseTreeRun raw).1 = none) :
    ∃ accepted rest p,
      raw = accepted ++ rest ∧ OpenPrefix accepted p ∧ Blocked rest ∧
      0 < p ∧ p ≤ accepted.length + 1 ∧
      (next caller)^[2 * accepted.length + p + 4]
        (some (cfg (some (phaseLabel d .init)) regs raw [] [] outputs ctx)) =
      some (cfg (some (resultLabel d .failure)) (reset regs) raw [] [] outputs ctx) := by
  obtain ⟨accepted, rest, p, rawEq, opened, blocked⟩ :=
    (parseTreeRun_none_iff_openPrefix raw).mp failed
  obtain ⟨positive, bounded⟩ := openPrefix_bounds opened
  refine ⟨accepted, rest, p, rawEq, opened, blocked, positive, bounded, ?_⟩
  rw [rawEq]
  exact run_openPrefix_failure caller d accepted rest p opened blocked regs outputs ctx

end Context

/-! Concrete finite contexts and live caller executions. -/

theorem concrete_left_two_preserves_both_distinct_old_outputs
    (bits : List Bool) (tags : Word) :
    (next haltCaller)^[12]
        (some (cfg (some (phaseLabel false .init)) staleRegisters
          [nodeTag, nodeTag, emptyTag, emptyTag, emptyTag, 15, 6, nodeTag]
          [] [] oldOutputs (smallContext bits tags))) =
      some (cfg (some (resultLabel false .success)) (reset staleRegisters)
        [15, 6, nodeTag] [] []
        (Function.update oldOutputs false
          [nodeTag, nodeTag, emptyTag, emptyTag, emptyTag, 15, 6]) (smallContext bits tags)) ∧
    (next haltCaller)^[12]
        (some (cfg (some (phaseLabel true .init)) staleRegisters
          [nodeTag, nodeTag, emptyTag, emptyTag, emptyTag, 15, 6, nodeTag]
          [] [] oldOutputs (smallContext bits tags))) =
      some (cfg (some (resultLabel true .success)) (reset staleRegisters)
        [15, 6, nodeTag] [] []
        (Function.update oldOutputs true
          [nodeTag, nodeTag, emptyTag, emptyTag, emptyTag, 2, 10, 11]) (smallContext bits tags)) :=
  ⟨run_code haltCaller false leftTwo.val [15, 6, nodeTag] staleRegisters
      oldOutputs (smallContext bits tags),
    run_code haltCaller true leftTwo.val [15, 6, nodeTag] staleRegisters
      oldOutputs (smallContext bits tags)⟩

/-- Old output is permitted even when its concatenation is not a single tree code. -/
theorem old_output_is_distinct_from_corrupt_pending :
    (next haltCaller)^[4]
        (some (cfg (some (phaseLabel false .init)) staleRegisters [emptyTag] [] []
          (fun _ => [emptyTag]) (smallContext [] []))) =
      some (cfg (some (resultLabel false .success)) (reset staleRegisters) [] [] []
        (Function.update (fun _ => [emptyTag]) false [emptyTag, emptyTag]) (smallContext [] [])) :=
  nil_leaves_the_arbitrary_suffix haltCaller staleRegisters (fun _ => [emptyTag])
    (smallContext [] []) false []

/-- The finite package uses the same blocks and actual initialized stack configuration. -/
def actual_finite_machine_uniform_time (raw : Word) :
    StateTransition.EvalsToInTime (machine haltCaller false true).step
      (Turing.initList (machine haltCaller false true) raw)
      (some (resultCfg false ((none, none), true) raw (fun _ => [])
        (smallContext [] []) (parseTreeRun raw).1)) (3 * raw.length + 5) := by
  have emptyCtx : (fun k : Bool => ([] : List (SmallAlphabet k))) = smallContext [] [] := by
    funext k
    cases k <;> rfl
  rw [initList_eq, emptyCtx]
  exact runInLinearTime haltCaller false raw ((none, none), true)
    (fun _ => []) (smallContext [] [])

def sentinelCaller : External Bool Unit → Statement Bool SmallAlphabet Unit Bool
  | .inl (_, .success) => .push (.inr false) (fun _ => true) .halt
  | _ => .halt

def sentinelStart (flag : Bool) (tail : Word) (bits : List Bool) (tags : Word) :
    Cfg Bool SmallAlphabet Unit Bool :=
  cfg (some (phaseLabel false .init)) ((some 15, some ()), flag) (emptyTag :: tail)
    [] [] oldOutputs (smallContext bits tags)

def sentinelHandoff (flag : Bool) (tail : Word) (bits : List Bool) (tags : Word) :
    Cfg Bool SmallAlphabet Unit Bool :=
  cfg (some (resultLabel false .success)) ((none, none), flag) tail [] []
    (Function.update oldOutputs false (emptyTag :: oldOutputs false)) (smallContext bits tags)

def sentinelAfterCaller (flag : Bool) (tail : Word) (bits : List Bool) (tags : Word) :
    Cfg Bool SmallAlphabet Unit Bool :=
  cfg none ((none, none), flag) tail [] []
    (Function.update oldOutputs false (emptyTag :: oldOutputs false))
    (smallContext (true :: bits) tags)

theorem sentinel_handoff_precedes_the_actual_push
    (flag : Bool) (tail : Word) (bits : List Bool) (tags : Word) :
    (next sentinelCaller)^[4] (some (sentinelStart flag tail bits tags)) =
      some (sentinelHandoff flag tail bits tags) :=
  nil_leaves_the_arbitrary_suffix sentinelCaller ((some 15, some ()), flag)
    oldOutputs (smallContext bits tags) false tail

theorem sentinel_push_is_one_additional_actual_step
    (flag : Bool) (tail : Word) (bits : List Bool) (tags : Word) :
    step sentinelCaller (sentinelHandoff flag tail bits tags) =
      some (sentinelAfterCaller flag tail bits tags) := by
  apply congrArg some
  apply cfg_ext
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · intro d; cases d <;> rfl
  · intro k; cases k <;> rfl

def sentinelHandoffInTime (flag : Bool) (tail : Word) (bits : List Bool) (tags : Word) :
    StateTransition.EvalsToInTime (step sentinelCaller) (sentinelStart flag tail bits tags)
      (some (sentinelHandoff flag tail bits tags)) 4 :=
  runInTime sentinelCaller false (emptyTag :: tail) ((some 15, some ()), flag)
    oldOutputs (smallContext bits tags)

def sentinelCallerInTime (flag : Bool) (tail : Word) (bits : List Bool) (tags : Word) :
    StateTransition.EvalsToInTime (step sentinelCaller) (sentinelHandoff flag tail bits tags)
      (some (sentinelAfterCaller flag tail bits tags)) 1 where
  steps := 1
  evals_in_steps := sentinel_push_is_one_additional_actual_step flag tail bits tags
  steps_le_m := Nat.le_refl _

def sentinelCompositionInTime (flag : Bool) (tail : Word) (bits : List Bool) (tags : Word) :
    StateTransition.EvalsToInTime (step sentinelCaller) (sentinelStart flag tail bits tags)
      (some (sentinelAfterCaller flag tail bits tags)) 5 :=
  StateTransition.EvalsToInTime.trans (step sentinelCaller) 4 1
    (sentinelStart flag tail bits tags) (sentinelHandoff flag tail bits tags)
    (some (sentinelAfterCaller flag tail bits tags))
    (sentinelHandoffInTime flag tail bits tags) (sentinelCallerInTime flag tail bits tags)

theorem live_return_halt_and_outer_none_are_three_distinct_stages
    (flag : Bool) (tail : Word) (bits : List Bool) (tags : Word) :
    (next sentinelCaller)^[4] (some (sentinelStart flag tail bits tags)) =
        some (sentinelHandoff flag tail bits tags) ∧
      (sentinelHandoff flag tail bits tags).l = some (resultLabel false .success) ∧
      (sentinelHandoff flag tail bits tags).stk (.inr false) = bits ∧
      (next sentinelCaller)^[5] (some (sentinelStart flag tail bits tags)) =
        some (sentinelAfterCaller flag tail bits tags) ∧
      (sentinelAfterCaller flag tail bits tags).l = none ∧
      (sentinelAfterCaller flag tail bits tags).stk (.inr false) = true :: bits ∧
      (next sentinelCaller)^[6] (some (sentinelStart flag tail bits tags)) = none := by
  have completed : (next sentinelCaller)^[5] (some (sentinelStart flag tail bits tags)) =
      some (sentinelAfterCaller flag tail bits tags) :=
    (sentinelCompositionInTime flag tail bits tags).evals_in_steps
  refine ⟨sentinel_handoff_precedes_the_actual_push flag tail bits tags,
    rfl, rfl, completed, rfl, rfl, ?_⟩
  rw [show 6 = 5 + 1 by rfl, Function.iterate_succ_apply', completed]
  rfl

/-- One fixed finite caller allocates forever only after the tree component has returned. -/
def allocatingCaller : External Bool Unit → Statement Bool SmallAlphabet Unit Bool
  | .inl (d, .failure) =>
      .push (.inr false) (fun _ => true) (jump (resultLabel d .failure))
  | _ => .halt

def emptyStart : Cfg Bool SmallAlphabet Unit Bool :=
  cfg (some (phaseLabel false .init)) staleRegisters [] [] []
    (fun _ => []) (smallContext [] [])

def allocatingState (count : Nat) : Cfg Bool SmallAlphabet Unit Bool :=
  cfg (some (resultLabel false .failure)) (reset staleRegisters) [] [] []
    (fun _ => []) (smallContext (List.replicate count true) [])

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
  · intro k; cases k <;> rfl

theorem allocating_caller_runs_after_the_first_failure (count : Nat) :
    (next allocatingCaller)^[5 + count] (some emptyStart) = some (allocatingState count) := by
  induction count with
  | zero =>
      exact empty_input_fails_in_five allocatingCaller staleRegisters
        (fun _ => []) (smallContext [] []) false
  | succ count ih =>
      rw [Nat.add_succ, Function.iterate_succ_apply', ih, next_some, allocating_caller_step]

/-- The proved component bound is 1 here; two actual caller steps produce 2 cells. -/
theorem a_post_return_loop_exceeds_the_component_workspace_bound :
    (next allocatingCaller)^[5] (some emptyStart) = some (allocatingState 0) ∧
      (next allocatingCaller)^[7] (some emptyStart) = some (allocatingState 2) ∧
      stackCells (allocatingState 2) = 2 ∧
      2 * ([] : Word).length + outputCells (fun _ : Bool => ([] : Word)) +
        contextCells (smallContext [] []) + 1 = 1 := by
  refine ⟨allocating_caller_runs_after_the_first_failure 0,
    allocating_caller_runs_after_the_first_failure 2, ?_, ?_⟩ <;> decide

/-- External code can manufacture a success label and can then reenter init. -/
def misleadingCaller : External Bool Unit → Statement Bool SmallAlphabet Unit Bool
  | .inl (d, .failure) =>
      .push (.inl (.output d)) (fun _ => emptyTag) (jump (resultLabel d .success))
  | .inl (d, .success) => jump (phaseLabel d .init)
  | _ => .halt

def misleadingSuccess : Cfg Bool SmallAlphabet Unit Bool :=
  cfg (some (resultLabel false .success)) (reset staleRegisters) [] [] []
    (Function.update (fun _ => []) false [emptyTag]) (smallContext [] [])

def misleadingReentry : Cfg Bool SmallAlphabet Unit Bool :=
  cfg (some (phaseLabel false .init)) (reset staleRegisters) [] [] []
    (Function.update (fun _ => []) false [emptyTag]) (smallContext [] [])

theorem misleading_success_is_created_by_one_caller_step :
    step misleadingCaller (allocatingState 0) = some misleadingSuccess := by
  apply congrArg some
  apply cfg_ext
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · intro d; cases d <;> rfl
  · intro k; cases k <;> rfl

theorem misleading_success_can_reenter_the_component :
    step misleadingCaller misleadingSuccess = some misleadingReentry := rfl

theorem later_success_is_not_the_parser_first_success :
    (next misleadingCaller)^[5] (some emptyStart) = some (allocatingState 0) ∧
      (next misleadingCaller)^[6] (some emptyStart) = some misleadingSuccess ∧
      (next misleadingCaller)^[7] (some emptyStart) = some misleadingReentry ∧
      ¬ FirstSuccess misleadingCaller false [] .nil [] staleRegisters
        (fun _ => []) (smallContext [] []) := by
  have first : (next misleadingCaller)^[5] (some emptyStart) = some (allocatingState 0) :=
    empty_input_fails_in_five misleadingCaller staleRegisters
      (fun _ => []) (smallContext [] []) false
  have later : (next misleadingCaller)^[6] (some emptyStart) = some misleadingSuccess := by
    rw [show 6 = 5 + 1 by rfl, Function.iterate_succ_apply', first, next_some,
      misleading_success_is_created_by_one_caller_step]
  refine ⟨first, later, ?_, ?_⟩
  · rw [show 7 = 6 + 1 by rfl, Function.iterate_succ_apply', later, next_some,
      misleading_success_can_reenter_the_component]
  · intro claimed
    have impossible := (firstSuccess_iff misleadingCaller false [] .nil [] staleRegisters
      (fun _ => []) (smallContext [] [])).mp claimed
    cases impossible


/-- One actual caller jump connects destination false to destination true in the same machine. -/
def twoStageCaller : External Bool Unit → Statement Bool SmallAlphabet Unit Bool
  | .inl (false, .success) => jump (phaseLabel true .init)
  | _ => .halt

def twoStageStart (source target : BinaryTree Unit) (tail : Word) (regs : Registers Bool)
    (outputs : Bool → Word) (bits : List Bool) (tags : Word) : Cfg Bool SmallAlphabet Unit Bool :=
  cfg (some (phaseLabel false .init)) regs (treeCode source ++ treeCode target ++ tail)
    [] [] outputs (smallContext bits tags)

def twoStageFirstReturn (source target : BinaryTree Unit) (tail : Word) (regs : Registers Bool)
    (outputs : Bool → Word) (bits : List Bool) (tags : Word) : Cfg Bool SmallAlphabet Unit Bool :=
  cfg (some (resultLabel false .success)) (reset regs) (treeCode target ++ tail) [] []
    (Function.update outputs false (treeCode source ++ outputs false)) (smallContext bits tags)

def twoStageSecondEntry (source target : BinaryTree Unit) (tail : Word) (regs : Registers Bool)
    (outputs : Bool → Word) (bits : List Bool) (tags : Word) : Cfg Bool SmallAlphabet Unit Bool :=
  cfg (some (phaseLabel true .init)) (reset regs) (treeCode target ++ tail) [] []
    (Function.update outputs false (treeCode source ++ outputs false)) (smallContext bits tags)

def twoStageFinalReturn (source target : BinaryTree Unit) (tail : Word) (regs : Registers Bool)
    (outputs : Bool → Word) (bits : List Bool) (tags : Word) : Cfg Bool SmallAlphabet Unit Bool :=
  cfg (some (resultLabel true .success)) (reset regs) tail [] []
    (Function.update (Function.update outputs false (treeCode source ++ outputs false))
      true (treeCode target ++ outputs true)) (smallContext bits tags)

theorem the_second_entry_is_the_actual_caller_successor
    (source target : BinaryTree Unit) (tail : Word) (regs : Registers Bool)
    (outputs : Bool → Word) (bits : List Bool) (tags : Word) :
    step twoStageCaller (twoStageFirstReturn source target tail regs outputs bits tags) =
      some (twoStageSecondEntry source target tail regs outputs bits tags) := rfl

def firstTreeInTime (source target : BinaryTree Unit) (tail : Word) (regs : Registers Bool)
    (outputs : Bool → Word) (bits : List Bool) (tags : Word) :
    StateTransition.EvalsToInTime (step twoStageCaller)
      (twoStageStart source target tail regs outputs bits tags)
      (some (twoStageFirstReturn source target tail regs outputs bits tags))
      (2 * (treeCode source).length + 2) where
  steps := 2 * (treeCode source).length + 2
  evals_in_steps := by
    change (next twoStageCaller)^[2 * (treeCode source).length + 2]
      (some (twoStageStart source target tail regs outputs bits tags)) =
      some (twoStageFirstReturn source target tail regs outputs bits tags)
    simpa only [twoStageStart, twoStageFirstReturn, List.append_assoc] using
      run_code twoStageCaller false source (treeCode target ++ tail)
        regs outputs (smallContext bits tags)
  steps_le_m := Nat.le_refl _

def interveningJumpInTime (source target : BinaryTree Unit) (tail : Word) (regs : Registers Bool)
    (outputs : Bool → Word) (bits : List Bool) (tags : Word) :
    StateTransition.EvalsToInTime (step twoStageCaller)
      (twoStageFirstReturn source target tail regs outputs bits tags)
      (some (twoStageSecondEntry source target tail regs outputs bits tags)) 1 where
  steps := 1
  evals_in_steps := the_second_entry_is_the_actual_caller_successor
    source target tail regs outputs bits tags
  steps_le_m := Nat.le_refl _

def secondTreeInTime (source target : BinaryTree Unit) (tail : Word) (regs : Registers Bool)
    (outputs : Bool → Word) (bits : List Bool) (tags : Word) :
    StateTransition.EvalsToInTime (step twoStageCaller)
      (twoStageSecondEntry source target tail regs outputs bits tags)
      (some (twoStageFinalReturn source target tail regs outputs bits tags))
      (2 * (treeCode target).length + 2) where
  steps := 2 * (treeCode target).length + 2
  evals_in_steps := run_code twoStageCaller true target tail (reset regs)
    (Function.update outputs false (treeCode source ++ outputs false)) (smallContext bits tags)
  steps_le_m := Nat.le_refl _

/-- Both actual timed records share their literal configurations and the same step function. -/
def twoTreeCompositionInTime (source target : BinaryTree Unit) (tail : Word) (regs : Registers Bool)
    (outputs : Bool → Word) (bits : List Bool) (tags : Word) :
    StateTransition.EvalsToInTime (step twoStageCaller)
      (twoStageStart source target tail regs outputs bits tags)
      (some (twoStageFinalReturn source target tail regs outputs bits tags))
      ((2 * (treeCode source).length + 2 + 1) + (2 * (treeCode target).length + 2)) :=
  let firstAndJump := StateTransition.EvalsToInTime.trans (step twoStageCaller)
    (2 * (treeCode source).length + 2) 1
    (twoStageStart source target tail regs outputs bits tags)
    (twoStageFirstReturn source target tail regs outputs bits tags)
    (some (twoStageSecondEntry source target tail regs outputs bits tags))
    (firstTreeInTime source target tail regs outputs bits tags)
    (interveningJumpInTime source target tail regs outputs bits tags)
  let both := StateTransition.EvalsToInTime.trans (step twoStageCaller)
    (1 + (2 * (treeCode source).length + 2)) (2 * (treeCode target).length + 2)
    (twoStageStart source target tail regs outputs bits tags)
    (twoStageSecondEntry source target tail regs outputs bits tags)
    (some (twoStageFinalReturn source target tail regs outputs bits tags))
    firstAndJump (secondTreeInTime source target tail regs outputs bits tags)
  { steps := both.steps
    evals_in_steps := both.evals_in_steps
    steps_le_m := by have bounded := both.steps_le_m; omega }

theorem two_tree_calls_include_the_real_intervening_jump
    (source target : BinaryTree Unit) (tail : Word) (regs : Registers Bool)
    (outputs : Bool → Word) (bits : List Bool) (tags : Word) :
    (next twoStageCaller)^[2 * (treeCode source).length + 2 * (treeCode target).length + 5]
        (some (twoStageStart source target tail regs outputs bits tags)) =
      some (twoStageFinalReturn source target tail regs outputs bits tags) := by
  have executed := (twoTreeCompositionInTime source target tail regs outputs bits tags).evals_in_steps
  change (next twoStageCaller)^[(2 * (treeCode target).length + 2) +
      (1 + (2 * (treeCode source).length + 2))]
      (some (twoStageStart source target tail regs outputs bits tags)) = _ at executed
  have work : (2 * (treeCode target).length + 2) + (1 + (2 * (treeCode source).length + 2)) =
      2 * (treeCode source).length + 2 * (treeCode target).length + 5 := by omega
  rw [work] at executed
  exact executed

theorem left_two_then_nil_takes_seventeen_actual_steps
    (tail : Word) (bits : List Bool) (tags : Word) :
    (next twoStageCaller)^[17]
        (some (twoStageStart leftTwo.val empty.val tail staleRegisters oldOutputs bits tags)) =
      some (twoStageFinalReturn leftTwo.val empty.val tail staleRegisters oldOutputs bits tags) ∧
      (twoStageFinalReturn leftTwo.val empty.val tail staleRegisters oldOutputs bits tags).stk
        (.inl (.output false)) = [nodeTag, nodeTag, emptyTag, emptyTag, emptyTag, 15, 6] ∧
      (twoStageFinalReturn leftTwo.val empty.val tail staleRegisters oldOutputs bits tags).stk
        (.inl (.output true)) = [emptyTag, 2, 10, 11] :=
  ⟨two_tree_calls_include_the_real_intervening_jump leftTwo.val empty.val tail
    staleRegisters oldOutputs bits tags, rfl, rfl⟩


private theorem outputCells_prepend {D : Type} [DecidableEq D] [Fintype D]
    (outputs : D → Word) (d : D) (word : Word) :
    outputCells (Function.update outputs d (word ++ outputs d)) = word.length + outputCells outputs := by
  induction word with
  | nil => simp only [List.nil_append, Function.update_eq_self, List.length_nil, Nat.zero_add]
  | cons tag word ih =>
      have transferred := outputCells_update_cons
        (Function.update outputs d (word ++ outputs d)) d tag
      simp only [Function.update_self, Function.update_idem] at transferred
      change outputCells (Function.update outputs d (tag :: (word ++ outputs d))) =
        word.length + 1 + outputCells outputs
      rw [transferred, ih]
      omega

/-- The first tree's emitted code is old output for the second call, not extra unaccounted space. -/
theorem two_tree_calls_keep_the_original_bound_through_every_prefix
    (source target : BinaryTree Unit) (tail : Word) (regs : Registers Bool)
    (outputs : Bool → Word) (bits : List Bool) (tags : Word) (n : Nat)
    (bound : n ≤ 2 * (treeCode source).length + 2 * (treeCode target).length + 5) :
    ∃ reached : Cfg Bool SmallAlphabet Unit Bool,
      (next twoStageCaller)^[n]
        (some (twoStageStart source target tail regs outputs bits tags)) = some reached ∧
      stackCells reached ≤ 2 * (treeCode source ++ treeCode target ++ tail).length +
        outputCells outputs + contextCells (smallContext bits tags) + 1 := by
  have firstTime : runSteps (treeCode source ++ treeCode target ++ tail) =
      2 * (treeCode source).length + 2 := by
    rw [List.append_assoc, runSteps_code]
  by_cases beforeFirst : n ≤ 2 * (treeCode source).length + 2
  · have initialBound : n ≤ runSteps (treeCode source ++ treeCode target ++ tail) := by
      rw [firstTime]
      exact beforeFirst
    obtain ⟨reached, executed, _, _, _, _⟩ := run_prefix twoStageCaller false
      (treeCode source ++ treeCode target ++ tail) regs outputs (smallContext bits tags) n initialBound
    exact ⟨reached, executed, prefix_stackCells_le twoStageCaller false
      (treeCode source ++ treeCode target ++ tail) regs outputs (smallContext bits tags)
      n reached initialBound executed⟩
  · have firstRun := (firstTreeInTime source target tail regs outputs bits tags).evals_in_steps
    change (next twoStageCaller)^[2 * (treeCode source).length + 2]
      (some (twoStageStart source target tail regs outputs bits tags)) =
      some (twoStageFirstReturn source target tail regs outputs bits tags) at firstRun
    have entered : (next twoStageCaller)^[2 * (treeCode source).length + 2 + 1]
        (some (twoStageStart source target tail regs outputs bits tags)) =
        some (twoStageSecondEntry source target tail regs outputs bits tags) := by
      rw [Function.iterate_succ_apply', firstRun, next_some,
        the_second_entry_is_the_actual_caller_successor]
    have secondBound : n - (2 * (treeCode source).length + 2 + 1) ≤
        runSteps (treeCode target ++ tail) := by
      rw [runSteps_code]
      omega
    obtain ⟨reached, executed, _, _, _, _⟩ := run_prefix twoStageCaller true
      (treeCode target ++ tail) (reset regs)
      (Function.update outputs false (treeCode source ++ outputs false)) (smallContext bits tags)
      (n - (2 * (treeCode source).length + 2 + 1)) secondBound
    refine ⟨reached, ?_, ?_⟩
    · have splitTime : n = (n - (2 * (treeCode source).length + 2 + 1)) +
          (2 * (treeCode source).length + 2 + 1) := by omega
      rw [splitTime, Function.iterate_add_apply, entered]
      exact executed
    · have cells := prefix_stackCells_le twoStageCaller true (treeCode target ++ tail) (reset regs)
        (Function.update outputs false (treeCode source ++ outputs false)) (smallContext bits tags)
        (n - (2 * (treeCode source).length + 2 + 1)) reached secondBound executed
      rw [outputCells_prepend] at cells
      simp only [List.length_append] at cells ⊢
      omega

end Examples.RotationCertificateTreeParserMachine
