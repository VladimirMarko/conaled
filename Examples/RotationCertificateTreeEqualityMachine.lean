import Applications.Resources.RotationCertificate.TreeEqualityMachine
import Examples.RotationDistance

/-!
# Connected clients of destructive finite tree-word comparison

Fresh authoring from checkpoint112's fixed independent case plan. Every machine
execution below uses the public comparator program, its actual configurations,
or a declared finite caller statement. Raw equality, represented-tree equality,
source event work, live return, present halt, and outer none remain distinct.

Literal endpoints and timing expectations come from the fixed independent case
plan. The one-input package and a two-word configuration handoff have separate
contracts.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.RotationCertificateTreeEqualityMachine

open Trees Resources.RotationCertificate
open Resources.RotationCertificate.TreeEqualityMachine
open RotationDistanceExample
open scoped BigOperators

section Generic

variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
variable (caller : External Λ → Statement Γ Λ R)

/-- Five observations include both consumed unequal heads and the extra EOF probe. -/
theorem five_actual_observations (a b : Tag) (xs ys : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) (different : a ≠ b) :
    step caller (cfg (some (phaseLabel .compare)) regs [] [] ctx) =
        some (cfg (some (resultLabel .equal)) (reset regs) [] [] ctx) ∧
      step caller (cfg (some (phaseLabel .compare)) regs [] (b :: ys) ctx) =
        some (cfg (some (resultLabel .different)) (reset regs) [] ys ctx) ∧
      step caller (cfg (some (phaseLabel .compare)) regs (a :: xs) [] ctx) =
        some (cfg (some (resultLabel .different)) (reset regs) xs [] ctx) ∧
      step caller (cfg (some (phaseLabel .compare)) regs (a :: xs) (a :: ys) ctx) =
        some (cfg (some (phaseLabel .compare)) (reset regs) xs ys ctx) ∧
      step caller (cfg (some (phaseLabel .compare)) regs (a :: xs) (b :: ys) ctx) =
        some (cfg (some (resultLabel .different)) (reset regs) xs ys ctx) :=
  ⟨compare_step_nil_nil caller regs ctx,
    compare_step_nil_cons caller b ys regs ctx,
    compare_step_cons_nil caller a xs regs ctx,
    compare_step_same caller a xs ys regs ctx,
    compare_step_different caller a b xs ys regs ctx different⟩

/-- There is no tree, equal-size, clean-temporary, or caller-behavior premise. -/
theorem every_raw_word_pair_returns (xs ys : Word) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    (next caller)^[runSteps xs ys]
        (some (cfg (some (phaseLabel .compare)) regs xs ys ctx)) =
      some (cfg (some (resultLabel (wordResult xs ys))) (reset regs)
        (xs.drop (runSteps xs ys)) (ys.drop (runSteps xs ys)) ctx) :=
  run caller xs ys regs ctx

/-- An arbitrary actual owned configuration supplies its own words and context. -/
theorem dirty_owned_configuration_returns (start : Cfg Γ Λ R) (owned : Owned start.l) :
    (next caller)^[remainingSteps start] (some start) =
      some (cfg
        (some (resultLabel
          (wordResult (start.stk (.inl .source)) (start.stk (.inl .target)))))
        (reset start.var)
        ((start.stk (.inl .source)).drop (remainingSteps start))
        ((start.stk (.inl .target)).drop (remainingSteps start))
        (fun k => start.stk (.inr k))) := by
  obtain ⟨regs, xs, ys, ctx, rfl⟩ := owned_cases start owned
  exact run caller xs ys regs ctx

/-- Positive rank is an operational progress condition on arbitrary raw states. -/
theorem owned_progress_resets_and_pops (start : Cfg Γ Λ R) (owned : Owned start.l) :
    0 < remainingSteps start ∧
      ∃ reached, step caller start = some reached ∧
        remainingSteps start = remainingSteps reached + 1 ∧
        reached.var = reset start.var ∧
        reached.stk (.inl .source) = (start.stk (.inl .source)).tail ∧
        reached.stk (.inl .target) = (start.stk (.inl .target)).tail ∧
        ∀ k, reached.stk (.inr k) = start.stk (.inr k) := by
  refine ⟨(remainingSteps_pos_iff start).2 owned, ?_⟩
  obtain ⟨regs, xs, ys, ctx, rfl⟩ := owned_cases start owned
  exact compare_step_data caller xs ys regs ctx

/-- The rank-zero contract at a caller label does not execute that caller. -/
theorem nonowned_prefix_is_only_identity (start : Cfg Γ Λ R)
    (outside : ¬ Owned start.l) :
    remainingSteps start = 0 ∧
      (next caller)^[remainingSteps start] (some start) = some start := by
  have zero : remainingSteps start = 0 := by
    have noPositive : ¬ 0 < remainingSteps start := by
      intro positive
      exact outside ((remainingSteps_pos_iff start).1 positive)
    omega
  exact ⟨zero, by rw [zero]; rfl⟩

omit [DecidableEq K] in
theorem control_rank_domains (regs : Registers R) (xs ys : Word)
    (ctx : ∀ k, List (Γ k)) (external : Λ) :
    remainingSteps (cfg (some (phaseLabel (Λ := Λ) .compare)) regs xs ys ctx) =
        runSteps xs ys ∧
      remainingSteps (cfg (some (resultLabel (Λ := Λ) .equal)) regs xs ys ctx) = 0 ∧
      remainingSteps (cfg (some (resultLabel (Λ := Λ) .different)) regs xs ys ctx) = 0 ∧
      remainingSteps (cfg (some (callerLabel external)) regs xs ys ctx) = 0 ∧
      remainingSteps (cfg (Λ := Λ) none regs xs ys ctx) = 0 :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Inclusive prefixes bind the exact physical state, rank, and local path together. -/
theorem all_raw_prefixes [Fintype K] (xs ys : Word) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (n : Nat) (bound : n ≤ runSteps xs ys) :
    ∃ reached,
      (next caller)^[n] (some (cfg (some (phaseLabel .compare)) regs xs ys ctx)) =
        some reached ∧
      reached = cfg
        (some (if n < runSteps xs ys then phaseLabel .compare
          else resultLabel (wordResult xs ys)))
        (if n = 0 then regs else reset regs) (xs.drop n) (ys.drop n) ctx ∧
      remainingSteps reached = runSteps xs ys - n ∧
      Relation.ReflTransGen (LocalStep caller)
        (cfg (some (phaseLabel .compare)) regs xs ys ctx) reached ∧
      (n < runSteps xs ys ↔ Owned reached.l) ∧
      reached.var.2 = regs.2 ∧
      (∀ k, reached.stk (.inr k) = ctx k) ∧
      stackCells reached = (xs.length - n) + (ys.length - n) + contextCells ctx ∧
      stackCells reached ≤ xs.length + ys.length + contextCells ctx := by
  obtain ⟨reached, executed, rank, path, owns⟩ :=
    owned_prefix caller (cfg (some (phaseLabel .compare)) regs xs ys ctx) n bound
  have actual := prefix_exact caller xs ys regs ctx n bound
  have same : reached = prefixCfg xs ys regs ctx n :=
    Option.some.inj (executed.symm.trans actual)
  have frame := local_reaches_frame caller path
  refine ⟨reached, executed, ?_, rank, path, owns, frame.1, frame.2,
    prefix_stackCells caller xs ys regs ctx n reached bound executed,
    prefix_stackCells_le caller xs ys regs ctx n reached bound executed⟩
  exact same

/-- The unweighted sum contains both owned stacks and every protected alphabet. -/
theorem physical_sum_and_local_preservation [Fintype K]
    {before after : Cfg Γ Λ R} (transition : LocalStep caller before after) :
    stackCells after = ∑ k : StackId K, (after.stk k).length ∧
      remainingSteps before = remainingSteps after + 1 ∧
      after.var.2 = before.var.2 ∧
      (∀ k, after.stk (.inr k) = before.stk (.inr k)) ∧
      stackCells after ≤ stackCells before ∧
      stackCells before - stackCells after =
        min 1 (before.stk (.inl .source)).length +
          min 1 (before.stk (.inl .target)).length := by
  have data := local_step_data caller transition
  have frame := local_step_preserves caller transition
  refine ⟨stackCells_eq_sum after, data.1, frame.1, frame.2.1, frame.2.2, ?_⟩
  have context :
      contextCells (fun k => after.stk (.inr k)) =
        contextCells (fun k => before.stk (.inr k)) :=
    congrArg contextCells (funext data.2.2.2.2)
  simp only [stackCells, ownedCells, data.2.2.1, data.2.2.2.1, context, List.length_tail]
  omega

omit [DecidableEq K] in
/-- Zero, one, and two removed cells are the exact optional-head deletion counts. -/
theorem optional_head_deletion_amounts [Fintype K] (a b : Tag) (xs ys : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    stackCells (cfg (some (phaseLabel (Λ := Λ) .compare)) regs [] [] ctx) =
        stackCells (cfg (some (resultLabel (Λ := Λ) .equal)) (reset regs) [] [] ctx) ∧
      stackCells (cfg (some (phaseLabel (Λ := Λ) .compare)) regs [] (b :: ys) ctx) =
        stackCells (cfg (some (resultLabel (Λ := Λ) .different)) (reset regs) [] ys ctx) + 1 ∧
      stackCells (cfg (some (phaseLabel (Λ := Λ) .compare)) regs (a :: xs) [] ctx) =
        stackCells (cfg (some (resultLabel (Λ := Λ) .different)) (reset regs) xs [] ctx) + 1 ∧
      stackCells (cfg (some (phaseLabel (Λ := Λ) .compare)) regs (a :: xs) (b :: ys) ctx) =
        stackCells (cfg (some (resultLabel (Λ := Λ) .different)) (reset regs) xs ys ctx) + 2 := by
  refine ⟨rfl, ?_, ?_, ?_⟩ <;>
    simp only [stackCells_cfg, List.length_nil, List.length_cons] <;> omega

/-- An arbitrary local path preserves its real caller fields, not just the fixture. -/
theorem arbitrary_local_path_preserves [Fintype K] {start reached : Cfg Γ Λ R}
    (path : Relation.ReflTransGen (LocalStep caller) start reached) :
    reached.var.2 = start.var.2 ∧
      (∀ k, reached.stk (.inr k) = start.stk (.inr k)) ∧
      stackCells reached ≤ stackCells start :=
  local_reaches_preserves caller path

/-- Transition zero attains the bound on the actual configuration, with no spare credit. -/
theorem raw_initial_space_is_attained [Fintype K] (xs ys : Word) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    (next caller)^[0] (some (cfg (some (phaseLabel .compare)) regs xs ys ctx)) =
        some (cfg (some (phaseLabel .compare)) regs xs ys ctx) ∧
      stackCells (cfg (some (phaseLabel (Λ := Λ) .compare)) regs xs ys ctx) =
        xs.length + ys.length + contextCells ctx :=
  ⟨rfl, initial_space_sharp xs ys regs ctx⟩

/-- The observed first external return is unique even for callers that reenter. -/
theorem observed_first_return (xs ys : Word) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (n : Nat) (reached : Cfg Γ Λ R)
    (executed : (next caller)^[n]
      (some (cfg (some (phaseLabel .compare)) regs xs ys ctx)) = some reached)
    (outside : ¬ Owned reached.l)
    (earlier : ∀ k, k < n → ∃ before,
      (next caller)^[k] (some (cfg (some (phaseLabel .compare)) regs xs ys ctx)) =
        some before ∧ Owned before.l) :
    n = runSteps xs ys ∧ reached = resultCfg xs ys regs ctx :=
  first_return_unique caller xs ys regs ctx n reached executed outside earlier

theorem raw_first_result_characterizes_the_original_words (xs ys : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (FirstResult caller .equal xs ys regs ctx ↔ xs = ys) ∧
      (FirstResult caller .different xs ys regs ctx ↔ xs ≠ ys) := by
  constructor
  · rw [firstResult_iff, wordResult_equal_iff]
  · rw [firstResult_iff, wordResult_different_iff]

/-- Changing any caller body cannot change a prefix through the original first return. -/
theorem same_owned_prefix_for_different_callers
    (other : External Λ → Statement Γ Λ R) (start : Cfg Γ Λ R)
    (n : Nat) (bound : n ≤ remainingSteps start) :
    (next caller)^[n] (some start) = (next other)^[n] (some start) :=
  prefix_caller_independent caller other start n bound

/-- The same physical endpoint holds inside any ambient program agreeing on compare. -/
theorem ambient_comparison (ambient : Label Λ → Statement Γ Λ R)
    (agrees : ∀ phase, ambient (phaseLabel phase) = block phase)
    (xs ys : Word) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (fun c : Option (Cfg Γ Λ R) => c.bind (Turing.TM2.step ambient))^[runSteps xs ys]
        (some (cfg (some (phaseLabel .compare)) regs xs ys ctx)) =
      some (resultCfg xs ys regs ctx) :=
  ambient_run ambient agrees xs ys regs ctx

def exactComparisonTime (xs ys : Word) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller)
      (cfg (some (phaseLabel .compare)) regs xs ys ctx)
      (some (resultCfg xs ys regs ctx)) (runSteps xs ys) :=
  runInTimeExact caller xs ys regs ctx

def linearComparisonTime (xs ys : Word) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller)
      (cfg (some (phaseLabel .compare)) regs xs ys ctx)
      (some (resultCfg xs ys regs ctx)) (min xs.length ys.length + 1) :=
  runInLinearTime caller xs ys regs ctx

theorem timed_records_use_the_exact_actual_clock (xs ys : Word) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    (exactComparisonTime caller xs ys regs ctx).steps = runSteps xs ys ∧
      (linearComparisonTime caller xs ys regs ctx).steps = runSteps xs ys :=
  ⟨rfl, rfl⟩

omit [DecidableEq K] in
theorem exact_clock_bounds (xs ys : Word) :
    0 < runSteps xs ys ∧ runSteps xs ys ≤ min xs.length ys.length + 1 ∧
      runSteps xs xs = xs.length + 1 :=
  ⟨runSteps_pos xs ys, runSteps_le xs ys, runSteps_self xs⟩

/-- Composition consumes timing of the same real continuation and complete handoff. -/
def comparisonThenCaller (xs ys : Word) (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (finish : Option (Cfg Γ Λ R)) (budget : Nat)
    (continued : StateTransition.EvalsToInTime (step caller)
      (resultCfg xs ys regs ctx) finish budget) :
    StateTransition.EvalsToInTime (step caller)
      (cfg (some (phaseLabel .compare)) regs xs ys ctx)
      finish (budget + runSteps xs ys) :=
  StateTransition.EvalsToInTime.trans (step caller) (runSteps xs ys) budget
    (cfg (some (phaseLabel .compare)) regs xs ys ctx)
    (resultCfg xs ys regs ctx) finish
    (exactComparisonTime caller xs ys regs ctx) continued

/-- An arbitrary matched word leaves both following words in their original order. -/
theorem common_word_preserves_both_suffixes (common xs ys : Word) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    runSteps (common ++ xs) (common ++ ys) = common.length + runSteps xs ys ∧
      (next caller)^[common.length]
        (some (cfg (some (phaseLabel .compare)) regs (common ++ xs) (common ++ ys) ctx)) =
      some (cfg (some (phaseLabel .compare))
        (if common.length = 0 then regs else reset regs) xs ys ctx) :=
  ⟨runSteps_common_prefix common xs ys, common_prefix caller common xs ys regs ctx⟩

/-- Optional-head mismatch includes a one-sided EOF and consumes the extra head. -/
theorem common_word_followed_by_mismatch (common xs ys : Word) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (different : xs.head? ≠ ys.head?) :
    runSteps (common ++ xs) (common ++ ys) = common.length + 1 ∧
      (next caller)^[common.length + 1]
        (some (cfg (some (phaseLabel .compare)) regs (common ++ xs) (common ++ ys) ctx)) =
      some (cfg (some (resultLabel .different)) (reset regs) xs.tail ys.tail ctx) := by
  refine ⟨?_, common_prefix_mismatch caller common xs ys regs ctx different⟩
  rw [runSteps_common_prefix, runSteps_head_mismatch xs ys different]

theorem strict_word_extension_saturates_bound (common : Word) (a : Tag) (tail : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    runSteps common (common ++ a :: tail) =
        min common.length (common ++ a :: tail).length + 1 ∧
      (next caller)^[common.length + 1]
        (some (cfg (some (phaseLabel .compare)) regs common (common ++ a :: tail) ctx)) =
      some (cfg (some (resultLabel .different)) (reset regs) [] tail ctx) := by
  have actual := common_word_followed_by_mismatch caller common [] (a :: tail)
    regs ctx (by simp)
  refine ⟨?_, by simpa only [List.append_nil, List.tail_nil, List.tail_cons] using actual.2⟩
  have count := actual.1
  simp only [List.append_nil] at count
  rw [count]
  simp only [List.length_append, List.length_cons]
  omega

/-- A self-comparison's EOF probe is visible even when its physical space is unchanged. -/
theorem self_word_all_prefixes [Fintype K] (word : Word) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (n : Nat) (bound : n ≤ word.length + 1) :
    ∃ reached,
      (next caller)^[n] (some (cfg (some (phaseLabel .compare)) regs word word ctx)) =
        some reached ∧
      stackCells reached = 2 * (word.length - n) + contextCells ctx ∧
      (n < word.length + 1 ↔ Owned reached.l) := by
  have actual := prefix_exact caller word word regs ctx n (by simpa using bound)
  refine ⟨prefixCfg word word regs ctx n, actual,
    self_prefix_stackCells caller word regs ctx n _ bound actual, ?_⟩
  simp only [prefixCfg, cfg, runSteps_self]
  split <;> simp_all [Owned, phaseLabel, resultLabel]

/-- At N=0 the first state still has the original stale fields; EOF resets them at N+1. -/
theorem self_last_matched_prefix_and_return [Fintype K] (word : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (next caller)^[word.length]
        (some (cfg (some (phaseLabel .compare)) regs word word ctx)) =
      some (cfg (some (phaseLabel .compare)) (prefixRegisters word.length regs) [] [] ctx) ∧
      (next caller)^[word.length + 1]
        (some (cfg (some (phaseLabel .compare)) regs word word ctx)) =
      some (cfg (some (resultLabel .equal)) (reset regs) [] [] ctx) ∧
      stackCells (cfg (some (phaseLabel (Λ := Λ) .compare))
        (prefixRegisters word.length regs) [] [] ctx) = contextCells ctx ∧
      stackCells (cfg (some (resultLabel (Λ := Λ) .equal))
        (reset regs) [] [] ctx) = contextCells ctx ∧
      stackCells (cfg (some (phaseLabel (Λ := Λ) .compare)) regs word word ctx) =
        2 * word.length + contextCells ctx := by
  refine ⟨?_, run_equal caller word regs ctx, ?_, ?_, ?_⟩
  · simpa only [List.append_nil] using common_prefix caller word [] [] regs ctx
  · simp only [stackCells_cfg, List.length_nil, Nat.zero_add]
  · simp only [stackCells_cfg, List.length_nil, Nat.zero_add]
  · simpa only [two_mul] using initial_space_sharp (Λ := Λ) word word regs ctx

/-- Source parsing is used in the proof of injectivity, not in the finite compare block. -/
theorem represented_tree_semantics (s t : BinaryTree Unit) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    (FirstResult caller .equal (treeCode s) (treeCode t) regs ctx ↔ s = t) ∧
      (FirstResult caller .different (treeCode s) (treeCode t) regs ctx ↔ s ≠ t) ∧
      decide (wordResult (treeCode s) (treeCode t) = .equal) = (eqTreeRun s t).1 ∧
      runSteps (treeCode s) (treeCode t) ≤ 2 * min s.numNodes t.numNodes + 2 ∧
      runSteps (treeCode s) (treeCode t) ≤ 2 * s.numNodes + 2 ∧
      runSteps (treeCode s) (treeCode t) ≤ 2 * t.numNodes + 2 :=
  ⟨first_equal_code_iff caller s t regs ctx,
    first_different_code_iff caller s t regs ctx, result_code_source s t,
    runSteps_code_le s t, runSteps_code_source_le s t, runSteps_code_target_le s t⟩

def representedTreeTime (s t : BinaryTree Unit) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller)
      (cfg (some (phaseLabel .compare)) regs (treeCode s) (treeCode t) ctx)
      (some (resultCfg (treeCode s) (treeCode t) regs ctx))
      (2 * min s.numNodes t.numNodes + 2) :=
  treeInTime caller s t regs ctx

theorem represented_self_has_two_distinct_cost_measures (t : BinaryTree Unit)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (eqTreeRun t t).2 = 3 * t.numNodes + 2 ∧
      runSteps (treeCode t) (treeCode t) = 2 * t.numNodes + 2 ∧
      (next caller)^[2 * t.numNodes + 2]
        (some (cfg (some (phaseLabel .compare)) regs (treeCode t) (treeCode t) ctx)) =
      some (cfg (some (resultLabel .equal)) (reset regs) [] [] ctx) :=
  ⟨(self_source_and_machine_counts t).1, (self_source_and_machine_counts t).2,
    run_code_equal caller t regs ctx⟩

theorem represented_different_retains_actual_suffixes (s t : BinaryTree Unit)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) (different : s ≠ t) :
    (next caller)^[runSteps (treeCode s) (treeCode t)]
        (some (cfg (some (phaseLabel .compare)) regs (treeCode s) (treeCode t) ctx)) =
      some (cfg (some (resultLabel .different)) (reset regs)
        ((treeCode s).drop (runSteps (treeCode s) (treeCode t)))
        ((treeCode t).drop (runSteps (treeCode s) (treeCode t))) ctx) :=
  run_code_different caller s t regs ctx different

end Generic

/-! The two protected alphabets and their nonpalindromic contents are literal. -/

def ProtectedAlphabet : Fin 2 → Type := Fin.cases Bool (fun _ => Tag)

instance protectedAlphabetFintype (k : Fin 2) : Fintype (ProtectedAlphabet k) := by
  exact Fin.cases (motive := fun k : Fin 2 => Fintype (ProtectedAlphabet k))
    (inferInstance : Fintype Bool) (fun _ => (inferInstance : Fintype Tag)) k

def protectedWords (bits : List Bool) (tags : Word) : ∀ k, List (ProtectedAlphabet k) :=
  Fin.cases bits (fun _ => tags)

def ordinaryContext : ∀ k, List (ProtectedAlphabet k) :=
  protectedWords [true, false, false] [7, 2, 14]

def sentinelContext : ∀ k, List (ProtectedAlphabet k) :=
  protectedWords [true, false, false] [7]

def stale (flag : Bool) : Registers Bool := ((some 15, some ()), flag)
def clean (flag : Bool) : Registers Bool := ((none, none), flag)
abbrev ExampleCfg := Cfg ProtectedAlphabet Unit Bool
abbrev ExampleCaller := External Unit → Statement ProtectedAlphabet Unit Bool

def ordinaryStart (flag : Bool) (xs ys : Word) : ExampleCfg :=
  cfg (some (phaseLabel .compare)) (stale flag) xs ys ordinaryContext

def ordinaryReturn (result : Result) (flag : Bool) (xs ys : Word) : ExampleCfg :=
  cfg (some (resultLabel result)) (clean flag) xs ys ordinaryContext

theorem protected_cell_count (bits : List Bool) (tags : Word) :
    contextCells (protectedWords bits tags) = bits.length + tags.length := by
  rw [contextCells, show (Finset.univ : Finset (Fin 2)) = {0, 1} from by decide]
  simp [protectedWords]
  rfl

theorem fixture_cell_counts :
    contextCells ordinaryContext = 6 ∧ contextCells sentinelContext = 4 :=
  ⟨protected_cell_count _ _, protected_cell_count _ _⟩

theorem actual_finite_carrier_counts :
    Fintype.card LocalStack = 2 ∧ Fintype.card Temporaries = 34 ∧
      Fintype.card (OwnedLabel Unit) = 1 ∧ Fintype.card (StackId (Fin 2)) = 4 ∧
      Fintype.card (Label Unit) = 4 ∧ Fintype.card (Registers Bool) = 68 := by
  refine ⟨rfl, card_temporaries, card_ownedLabel, ?_, ?_, ?_⟩
  · simpa using (card_stackId (K := Fin 2))
  · simpa using (card_label (Λ := Unit))
  · exact card_registers (R := Bool)

theorem generic_finite_counts {K Λ R : Type} [Fintype K] [Fintype Λ] [Fintype R] :
    Fintype.card (StackId K) = 2 + Fintype.card K ∧
      Fintype.card (Label Λ) = 3 + Fintype.card Λ ∧
      Fintype.card (Registers R) = 34 * Fintype.card R :=
  ⟨card_stackId, card_label, card_registers⟩

/-- Only the owned subtype is asserted finite for an infinite external label type. -/
def ownedEvenWithNatCaller : OwnedLabel Nat ≃ Unit := ownedLabelEquiv

theorem nat_caller_owned_count : Fintype.card (OwnedLabel Nat) = 1 :=
  card_ownedLabel

section LiteralCases

variable (caller : ExampleCaller) (flag : Bool)

theorem literal_01_empty :
    (next caller)^[1] (some (ordinaryStart flag [] [])) =
      some (ordinaryReturn .equal flag [] []) :=
  run caller [] [] (stale flag) ordinaryContext

theorem literal_02_left_eof :
    (next caller)^[1] (some (ordinaryStart flag [] [3, 12])) =
      some (ordinaryReturn .different flag [] [12]) :=
  run caller [] [3, 12] (stale flag) ordinaryContext

theorem literal_03_right_eof :
    (next caller)^[1] (some (ordinaryStart flag [3, 12] [])) =
      some (ordinaryReturn .different flag [12] []) :=
  run caller [3, 12] [] (stale flag) ordinaryContext

theorem literal_04_equal_word :
    (next caller)^[3] (some (ordinaryStart flag [3, 12] [3, 12])) =
      some (ordinaryReturn .equal flag [] []) :=
  run_equal caller [3, 12] (stale flag) ordinaryContext

theorem literal_05_internal_mismatch :
    (next caller)^[2] (some (ordinaryStart flag [3, 8, 0] [3, 9, 0])) =
      some (ordinaryReturn .different flag [0] [0]) :=
  run caller [3, 8, 0] [3, 9, 0] (stale flag) ordinaryContext

theorem literal_06_target_extension :
    (next caller)^[2] (some (ordinaryStart flag [3] [3, 12, 15])) =
      some (ordinaryReturn .different flag [] [15]) :=
  run caller [3] [3, 12, 15] (stale flag) ordinaryContext

theorem literal_07_source_extension :
    (next caller)^[2] (some (ordinaryStart flag [3, 12, 15] [3])) =
      some (ordinaryReturn .different flag [15] []) :=
  run caller [3, 12, 15] [3] (stale flag) ordinaryContext

theorem literal_08_reserved_equal :
    (next caller)^[2] (some (ordinaryStart flag [15] [15])) =
      some (ordinaryReturn .equal flag [] []) :=
  run_equal caller [15] (stale flag) ordinaryContext

theorem literal_09_reserved_mismatch :
    (next caller)^[1] (some (ordinaryStart flag [15, 2] [14, 7])) =
      some (ordinaryReturn .different flag [2] [7]) :=
  run caller [15, 2] [14, 7] (stale flag) ordinaryContext

theorem literal_10_nil_code :
    (next caller)^[2] (some (ordinaryStart flag [0] [0])) =
      some (ordinaryReturn .equal flag [] []) :=
  run_equal caller [0] (stale flag) ordinaryContext

theorem literal_11_singleton_code :
    (next caller)^[4] (some (ordinaryStart flag [1, 0, 0] [1, 0, 0])) =
      some (ordinaryReturn .equal flag [] []) :=
  run_equal caller [1, 0, 0] (stale flag) ordinaryContext

theorem literal_12_nonpalindromic_trees :
    (next caller)^[2]
        (some (ordinaryStart flag [1, 1, 0, 0, 0] [1, 0, 1, 0, 0])) =
      some (ordinaryReturn .different flag [0, 0, 0] [1, 0, 0]) :=
  run caller [1, 1, 0, 0, 0] [1, 0, 1, 0, 0] (stale flag) ordinaryContext

theorem literal_13_unequal_tree_sizes :
    (next caller)^[1] (some (ordinaryStart flag [0] [1, 0, 0])) =
      some (ordinaryReturn .different flag [] [0, 0]) :=
  run caller [0] [1, 0, 0] (stale flag) ordinaryContext

theorem literal_14_equal_empty_stores_different_result :
    (next caller)^[2] (some (ordinaryStart flag [3] [3, 12])) =
      some (ordinaryReturn .different flag [] []) :=
  run caller [3] [3, 12] (stale flag) ordinaryContext

theorem literal_15_tree_prefix_is_not_raw_equality :
    (next caller)^[2] (some (ordinaryStart flag [0] [0, 0])) =
      some (ordinaryReturn .different flag [] []) :=
  run caller [0] [0, 0] (stale flag) ordinaryContext

theorem unequal_and_equal_can_both_leave_empty_stores :
    (next caller)^[2] (some (ordinaryStart flag [3] [3])) =
        some (ordinaryReturn .equal flag [] []) ∧
      (next caller)^[2] (some (ordinaryStart flag [3] [3, 12])) =
        some (ordinaryReturn .different flag [] []) ∧
      (ordinaryReturn .equal flag [] []).l ≠ (ordinaryReturn .different flag [] []).l :=
  ⟨run_equal caller [3] (stale flag) ordinaryContext,
    literal_14_equal_empty_stores_different_result caller flag, by intro same; cases same⟩

theorem literal_04_all_four_states :
    (next caller)^[0] (some (ordinaryStart flag [3, 12] [3, 12])) =
        some (ordinaryStart flag [3, 12] [3, 12]) ∧
      (next caller)^[1] (some (ordinaryStart flag [3, 12] [3, 12])) =
        some (cfg (some (phaseLabel .compare)) (clean flag) [12] [12] ordinaryContext) ∧
      (next caller)^[2] (some (ordinaryStart flag [3, 12] [3, 12])) =
        some (cfg (some (phaseLabel .compare)) (clean flag) [] [] ordinaryContext) ∧
      (next caller)^[3] (some (ordinaryStart flag [3, 12] [3, 12])) =
        some (ordinaryReturn .equal flag [] []) :=
  ⟨rfl, prefix_exact caller [3, 12] [3, 12] (stale flag) ordinaryContext 1 (by decide),
    prefix_exact caller [3, 12] [3, 12] (stale flag) ordinaryContext 2 (by decide),
    literal_04_equal_word caller flag⟩

theorem literal_04_and_05_prefix_cells (n : Nat) :
    (∀ reached, n ≤ 3 →
      (next caller)^[n] (some (ordinaryStart flag [3, 12] [3, 12])) = some reached →
      stackCells reached = 2 * (2 - n) + 6) ∧
      (∀ reached, n ≤ 2 →
      (next caller)^[n] (some (ordinaryStart flag [3, 8, 0] [3, 9, 0])) = some reached →
      stackCells reached = 2 * (3 - n) + 6) := by
  constructor
  · intro reached bound executed
    have cells := self_prefix_stackCells caller [3, 12] (stale flag) ordinaryContext
      n reached bound executed
    simpa only [List.length_cons, List.length_nil, fixture_cell_counts.1] using cells
  · intro reached bound executed
    have cells := prefix_stackCells caller [3, 8, 0] [3, 9, 0] (stale flag) ordinaryContext
      n reached bound executed
    simp only [List.length_cons, List.length_nil, fixture_cell_counts.1] at cells
    omega

/-- The stale Tag and stale match flag are each overwritten before branching. -/
theorem distinct_stale_temporaries :
    step caller (cfg (some (phaseLabel .compare)) ((some 15, none), flag)
        [] [] ordinaryContext) = some (ordinaryReturn .equal flag [] []) ∧
      step caller (cfg (some (phaseLabel .compare)) ((some 12, some ()), flag)
        [3] [12] ordinaryContext) = some (ordinaryReturn .different flag [] []) ∧
      step caller (cfg (some (phaseLabel .compare)) ((none, none), flag)
        [3] [3] ordinaryContext) =
        some (cfg (some (phaseLabel .compare)) (clean flag) [] [] ordinaryContext) ∧
      step caller (cfg (some (phaseLabel .compare)) ((some 15, some ()), flag)
        [] [15, 2] ordinaryContext) = some (ordinaryReturn .different flag [] [2]) ∧
      step caller (cfg (some (phaseLabel .compare)) ((none, some ()), flag)
        [15, 2] [] ordinaryContext) = some (ordinaryReturn .different flag [2] []) :=
  ⟨compare_step_nil_nil caller _ _,
    compare_step_different caller 3 12 [] [] _ _ (by decide),
    compare_step_same caller 3 [] [] _ _,
    compare_step_nil_cons caller 15 [2] _ _,
    compare_step_cons_nil caller 15 [2] _ _⟩

theorem every_tag_needs_the_separate_eof_probe (a : Tag) :
    step caller (ordinaryStart flag [a] [a]) =
        some (cfg (some (phaseLabel .compare)) (clean flag) [] [] ordinaryContext) ∧
      (next caller)^[2] (some (ordinaryStart flag [a] [a])) =
        some (ordinaryReturn .equal flag [] []) :=
  ⟨compare_step_same caller a [] [] (stale flag) ordinaryContext,
    run_equal caller [a] (stale flag) ordinaryContext⟩

theorem nonpalindromic_prefix_arbitrary_tails (a b : Tag) (xs ys : Word)
    (different : a ≠ b) :
    (next caller)^[3]
        (some (ordinaryStart flag ([3, 12, 5] ++ a :: xs) ([3, 12, 5] ++ b :: ys))) =
      some (cfg (some (phaseLabel .compare)) (clean flag) (a :: xs) (b :: ys)
        ordinaryContext) ∧
      (next caller)^[4]
        (some (ordinaryStart flag ([3, 12, 5] ++ a :: xs) ([3, 12, 5] ++ b :: ys))) =
      some (ordinaryReturn .different flag xs ys) :=
  ⟨common_prefix caller [3, 12, 5] (a :: xs) (b :: ys) (stale flag) ordinaryContext,
    common_prefix_mismatch caller [3, 12, 5] (a :: xs) (b :: ys)
      (stale flag) ordinaryContext (by simpa using different)⟩

theorem nonpalindromic_prefix_literal_and_extensions :
    (next caller)^[3]
        (some (ordinaryStart flag [3, 12, 5, 8, 0, 15, 2] [3, 12, 5, 9, 14, 7])) =
      some (cfg (some (phaseLabel .compare)) (clean flag)
        [8, 0, 15, 2] [9, 14, 7] ordinaryContext) ∧
      (next caller)^[4]
        (some (ordinaryStart flag [3, 12, 5, 8, 0, 15, 2] [3, 12, 5, 9, 14, 7])) =
      some (ordinaryReturn .different flag [0, 15, 2] [14, 7]) ∧
      (next caller)^[4]
        (some (ordinaryStart flag [3, 12, 5] [3, 12, 5, 12, 15, 7])) =
      some (ordinaryReturn .different flag [] [15, 7]) ∧
      (next caller)^[4]
        (some (ordinaryStart flag [3, 12, 5, 12, 15, 7] [3, 12, 5])) =
      some (ordinaryReturn .different flag [15, 7] []) ∧
      (next caller)^[4]
        (some (ordinaryStart flag [3, 12, 5] [3, 12, 5])) =
      some (ordinaryReturn .equal flag [] []) :=
  ⟨(nonpalindromic_prefix_arbitrary_tails caller flag 8 9 [0, 15, 2] [14, 7] (by decide)).1,
    (nonpalindromic_prefix_arbitrary_tails caller flag 8 9 [0, 15, 2] [14, 7] (by decide)).2,
    run caller [3, 12, 5] [3, 12, 5, 12, 15, 7] (stale flag) ordinaryContext,
    run caller [3, 12, 5, 12, 15, 7] [3, 12, 5] (stale flag) ordinaryContext,
    run_equal caller [3, 12, 5] (stale flag) ordinaryContext⟩

/-- The source parser accepts a tree prefix that the raw comparator still distinguishes. -/
theorem tree_prefix_parser_and_raw_comparison_disagree :
    (parseTreeRun [0, 0]).1 = some (.nil, [0]) ∧
      (next caller)^[2] (some (ordinaryStart flag [0] [0, 0])) =
        some (ordinaryReturn .different flag [] []) :=
  ⟨rfl, literal_15_tree_prefix_is_not_raw_equality caller flag⟩

theorem reserved_raw_equal_is_not_tree_validation :
    (parseTreeRun [15]).1 = none ∧ (∀ t, treeCode t ≠ [15]) ∧
      (next caller)^[2] (some (ordinaryStart flag [15] [15])) =
        some (ordinaryReturn .equal flag [] []) := by
  refine ⟨rfl, ?_, literal_08_reserved_equal caller flag⟩
  intro t encoded
  have parsed := (parseTreeRun_iff [15] t []).2 (by simpa only [List.append_nil] using encoded.symm)
  change (none : Option (BinaryTree Unit × Word)) = some (t, []) at parsed
  cases parsed

theorem actual_tree_codes :
    treeCode empty.val = [0] ∧ treeCode singleton.val = [1, 0, 0] ∧
      treeCode leftTwo.val = [1, 1, 0, 0, 0] ∧
      treeCode rightTwo.val = [1, 0, 1, 0, 0] :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Each source tariff is paired with an actual machine execution at its separate clock. -/
theorem source_work_and_machine_time_calibrations :
    eqTreeRun empty.val empty.val = (true, 2) ∧
      (next caller)^[2] (some (ordinaryStart flag (treeCode empty.val) (treeCode empty.val))) =
        some (ordinaryReturn .equal flag [] []) ∧
      eqTreeRun singleton.val singleton.val = (true, 5) ∧
      (next caller)^[4]
        (some (ordinaryStart flag (treeCode singleton.val) (treeCode singleton.val))) =
        some (ordinaryReturn .equal flag [] []) ∧
      eqTreeRun leftTwo.val rightTwo.val = (false, 4) ∧
      (next caller)^[2]
        (some (ordinaryStart flag (treeCode leftTwo.val) (treeCode rightTwo.val))) =
        some (ordinaryReturn .different flag [0, 0, 0] [1, 0, 0]) ∧
      eqTreeRun leftTwo.val leftTwo.val = (true, 8) ∧
      (next caller)^[6]
        (some (ordinaryStart flag (treeCode leftTwo.val) (treeCode leftTwo.val))) =
        some (ordinaryReturn .equal flag [] []) ∧
      eqTreeRun balancedThree.val balancedThree.val = (true, 11) ∧
      (next caller)^[8]
        (some (ordinaryStart flag (treeCode balancedThree.val) (treeCode balancedThree.val))) =
        some (ordinaryReturn .equal flag [] []) :=
  ⟨rfl, literal_10_nil_code caller flag, rfl, literal_11_singleton_code caller flag,
    rfl, literal_12_nonpalindromic_trees caller flag,
    rfl, run_code_equal caller leftTwo.val (stale flag) ordinaryContext,
    rfl, run_code_equal caller balancedThree.val (stale flag) ordinaryContext⟩

end LiteralCases

/-! Actual finite caller statements, with arbitrary protected words in the clients. -/

def withWords (flag : Bool) (xs ys : Word) (bits : List Bool) (tags : Word) : ExampleCfg :=
  cfg (some (phaseLabel .compare)) (stale flag) xs ys (protectedWords bits tags)

def liveWithWords (result : Result) (flag : Bool) (xs ys : Word)
    (bits : List Bool) (tags : Word) : ExampleCfg :=
  cfg (some (resultLabel result)) (clean flag) xs ys (protectedWords bits tags)

def haltedWithWords (flag : Bool) (xs ys : Word) (bits : List Bool) (tags : Word) : ExampleCfg :=
  cfg none (clean flag) xs ys (protectedWords bits tags)

def sentinelCaller (marker : Tag) : ExampleCaller
  | .inl _ => .push (.inr (1 : Fin 2)) (fun _ => marker) .halt
  | .inr _ => .halt

def forgeEqualCaller : ExampleCaller
  | .inl .different => .goto (fun _ => resultLabel .equal)
  | _ => .halt

def reenterCaller : ExampleCaller
  | .inl .different => .goto (fun _ => phaseLabel .compare)
  | _ => .halt

def allocatingCaller : ExampleCaller
  | .inl .equal =>
      .push (.inr (1 : Fin 2)) (fun _ => (13 : Tag)) (.goto (fun _ => resultLabel .equal))
  | _ => .halt

def externalCaller : ExampleCaller
  | .inl _ => .goto (fun _ => callerLabel ())
  | .inr _ => .push (.inr (1 : Fin 2)) (fun _ => (13 : Tag)) .halt

/-- Append one actual transition to an already established complete configuration. -/
theorem append_actual_step (caller : ExampleCaller) (n : Nat)
    (start reached : ExampleCfg) (finish : Option ExampleCfg)
    (executed : (next caller)^[n] (some start) = some reached)
    (continued : step caller reached = finish) :
    (next caller)^[n + 1] (some start) = finish := by
  rw [Function.iterate_succ_apply', executed, next_some, continued]

def oneActualStepTime (caller : ExampleCaller) (start : ExampleCfg)
    (finish : Option ExampleCfg) (executed : step caller start = finish) :
    StateTransition.EvalsToInTime (step caller) start finish 1 where
  steps := 1
  evals_in_steps := executed
  steps_le_m := Nat.le_refl _

theorem sentinel_push_step (marker : Tag) (result : Result) (flag : Bool)
    (xs ys : Word) (bits : List Bool) (tags : Word) :
    step (sentinelCaller marker) (liveWithWords result flag xs ys bits tags) =
      some (haltedWithWords flag xs ys bits (marker :: tags)) := by
  apply congrArg some
  apply cfg_ext
  · rfl
  · rfl
  · rfl
  · rfl
  · intro k
    fin_cases k <;> rfl

theorem present_halt_then_outer_none (caller : ExampleCaller) (flag : Bool)
    (xs ys : Word) (bits : List Bool) (tags : Word) :
    step caller (haltedWithWords flag xs ys bits tags) = none := rfl

def successfulSentinelReturnTime (flag : Bool) (bits : List Bool) (tags : Word) :
    StateTransition.EvalsToInTime (step (sentinelCaller 13))
      (withWords flag [3, 12] [3, 12] bits tags)
      (some (liveWithWords .equal flag [] [] bits tags)) 3 :=
  runInTimeExact (sentinelCaller 13) [3, 12] [3, 12] (stale flag) (protectedWords bits tags)

def successfulSentinelCallerTime (flag : Bool) (bits : List Bool) (tags : Word) :
    StateTransition.EvalsToInTime (step (sentinelCaller 13))
      (liveWithWords .equal flag [] [] bits tags)
      (some (haltedWithWords flag [] [] bits (13 :: tags))) 1 :=
  oneActualStepTime (sentinelCaller 13) _ _ (sentinel_push_step 13 .equal flag [] [] bits tags)

def successfulSentinelHaltTime (flag : Bool) (bits : List Bool) (tags : Word) :
    StateTransition.EvalsToInTime (step (sentinelCaller 13))
      (haltedWithWords flag [] [] bits (13 :: tags)) none 1 :=
  oneActualStepTime (sentinelCaller 13) _ _
    (present_halt_then_outer_none (sentinelCaller 13) flag [] [] bits (13 :: tags))

/-- The real push/halt costs one additional transition after first return. -/
def successfulSentinelCompositionTime (flag : Bool) (bits : List Bool) (tags : Word) :
    StateTransition.EvalsToInTime (step (sentinelCaller 13))
      (withWords flag [3, 12] [3, 12] bits tags)
      (some (haltedWithWords flag [] [] bits (13 :: tags))) 4 :=
  StateTransition.EvalsToInTime.trans (step (sentinelCaller 13)) 3 1
    (withWords flag [3, 12] [3, 12] bits tags)
    (liveWithWords .equal flag [] [] bits tags)
    (some (haltedWithWords flag [] [] bits (13 :: tags)))
    (successfulSentinelReturnTime flag bits tags) (successfulSentinelCallerTime flag bits tags)

def successfulSentinelOuterNoneTime (flag : Bool) (bits : List Bool) (tags : Word) :
    StateTransition.EvalsToInTime (step (sentinelCaller 13))
      (withWords flag [3, 12] [3, 12] bits tags) none 5 :=
  StateTransition.EvalsToInTime.trans (step (sentinelCaller 13)) 4 1
    (withWords flag [3, 12] [3, 12] bits tags)
    (haltedWithWords flag [] [] bits (13 :: tags)) none
    (successfulSentinelCompositionTime flag bits tags) (successfulSentinelHaltTime flag bits tags)

theorem successful_sentinel_three_stages (flag : Bool) (bits : List Bool) (tags : Word) :
    (next (sentinelCaller 13))^[3] (some (withWords flag [3, 12] [3, 12] bits tags)) =
        some (liveWithWords .equal flag [] [] bits tags) ∧
      (next (sentinelCaller 13))^[4] (some (withWords flag [3, 12] [3, 12] bits tags)) =
        some (haltedWithWords flag [] [] bits (13 :: tags)) ∧
      (next (sentinelCaller 13))^[5] (some (withWords flag [3, 12] [3, 12] bits tags)) =
        none ∧
      (successfulSentinelReturnTime flag bits tags).steps = 3 ∧
      (successfulSentinelCallerTime flag bits tags).steps = 1 ∧
      (successfulSentinelHaltTime flag bits tags).steps = 1 ∧
      (successfulSentinelCompositionTime flag bits tags).steps = 4 ∧
      (successfulSentinelOuterNoneTime flag bits tags).steps = 5 := by
  have returned :
      (next (sentinelCaller 13))^[3] (some (withWords flag [3, 12] [3, 12] bits tags)) =
        some (liveWithWords .equal flag [] [] bits tags) :=
    run_equal (sentinelCaller 13) [3, 12] (stale flag) (protectedWords bits tags)
  have halted := append_actual_step (sentinelCaller 13) 3 _ _ _ returned
    (sentinel_push_step 13 .equal flag [] [] bits tags)
  have absent := append_actual_step (sentinelCaller 13) 4 _ _ _ halted
    (present_halt_then_outer_none (sentinelCaller 13) flag [] [] bits (13 :: tags))
  exact ⟨returned, halted, absent, rfl, rfl, rfl, rfl, rfl⟩

/-- The reported 8,6,4,4 and 5 are cells of actual reached configurations. -/
theorem sentinel_fixture_cells (flag : Bool) :
    (∀ n, n ≤ 3 → ∃ reached,
      (next (sentinelCaller 13))^[n]
        (some (withWords flag [3, 12] [3, 12] [true, false, false] [7])) = some reached ∧
      stackCells reached = 2 * (2 - n) + 4) ∧
      (next (sentinelCaller 13))^[4]
        (some (withWords flag [3, 12] [3, 12] [true, false, false] [7])) =
          some (haltedWithWords flag [] [] [true, false, false] [13, 7]) ∧
      stackCells (haltedWithWords flag [] [] [true, false, false] [13, 7]) = 5 := by
  refine ⟨?_, (successful_sentinel_three_stages flag [true, false, false] [7]).2.1, ?_⟩
  · intro n bound
    obtain ⟨reached, executed, cells, _⟩ :=
      self_word_all_prefixes (sentinelCaller 13) [3, 12] (stale flag)
        (protectedWords [true, false, false] [7]) n bound
    refine ⟨reached, executed, ?_⟩
    simpa only [List.length_cons, List.length_nil, protected_cell_count] using cells
  · change 0 + 0 + contextCells (protectedWords [true, false, false] [13, 7]) = 5
    rw [protected_cell_count]
    rfl

theorem callers_agree_through_return_and_differ_afterward (flag : Bool)
    (bits : List Bool) (tags : Word) :
    (∀ n, n ≤ 3 →
      (next (sentinelCaller 13))^[n] (some (withWords flag [3, 12] [3, 12] bits tags)) =
      (next (sentinelCaller 14))^[n] (some (withWords flag [3, 12] [3, 12] bits tags))) ∧
      (next (sentinelCaller 13))^[4] (some (withWords flag [3, 12] [3, 12] bits tags)) ≠
      (next (sentinelCaller 14))^[4] (some (withWords flag [3, 12] [3, 12] bits tags)) := by
  refine ⟨fun n bound => prefix_caller_independent (sentinelCaller 13) (sentinelCaller 14)
    (withWords flag [3, 12] [3, 12] bits tags) n bound, ?_⟩
  have first13 := (successful_sentinel_three_stages flag bits tags).2.1
  have first14 :
      (next (sentinelCaller 14))^[3] (some (withWords flag [3, 12] [3, 12] bits tags)) =
        some (liveWithWords .equal flag [] [] bits tags) :=
    run_equal (sentinelCaller 14) [3, 12] (stale flag) (protectedWords bits tags)
  have after14 := append_actual_step (sentinelCaller 14) 3 _ _ _ first14
    (sentinel_push_step 14 .equal flag [] [] bits tags)
  rw [first13, after14]
  intro same
  have heads := congrArg (fun c : ExampleCfg => (c.stk (.inr (1 : Fin 2))).head?)
    (Option.some.inj same)
  have impossible : (13 : Tag) = 14 := Option.some.inj heads
  exact (by decide : (13 : Tag) ≠ 14) impossible

def failedSentinelReturnTime (flag : Bool) (bits : List Bool) (tags : Word) :
    StateTransition.EvalsToInTime (step (sentinelCaller 13))
      (withWords flag [3, 8, 0] [3, 9, 0] bits tags)
      (some (liveWithWords .different flag [0] [0] bits tags)) 2 :=
  runInTimeExact (sentinelCaller 13) [3, 8, 0] [3, 9, 0]
    (stale flag) (protectedWords bits tags)

def failedSentinelCompositionTime (flag : Bool) (bits : List Bool) (tags : Word) :
    StateTransition.EvalsToInTime (step (sentinelCaller 13))
      (withWords flag [3, 8, 0] [3, 9, 0] bits tags)
      (some (haltedWithWords flag [0] [0] bits (13 :: tags))) 3 :=
  StateTransition.EvalsToInTime.trans (step (sentinelCaller 13)) 2 1
    (withWords flag [3, 8, 0] [3, 9, 0] bits tags)
    (liveWithWords .different flag [0] [0] bits tags)
    (some (haltedWithWords flag [0] [0] bits (13 :: tags)))
    (failedSentinelReturnTime flag bits tags)
    (oneActualStepTime (sentinelCaller 13) _ _
      (sentinel_push_step 13 .different flag [0] [0] bits tags))

theorem failure_sentinel_keeps_consumed_suffixes (flag : Bool)
    (bits : List Bool) (tags : Word) :
    (next (sentinelCaller 13))^[2]
        (some (withWords flag [3, 8, 0] [3, 9, 0] bits tags)) =
      some (liveWithWords .different flag [0] [0] bits tags) ∧
      (next (sentinelCaller 13))^[3]
        (some (withWords flag [3, 8, 0] [3, 9, 0] bits tags)) =
      some (haltedWithWords flag [0] [0] bits (13 :: tags)) ∧
      (next (sentinelCaller 13))^[4]
        (some (withWords flag [3, 8, 0] [3, 9, 0] bits tags)) = none ∧
      runSteps [3, 8, 0] [3, 9, 0] = 2 ∧
      min ([3, 8, 0] : Word).length ([3, 9, 0] : Word).length + 1 = 4 := by
  have returned :
      (next (sentinelCaller 13))^[2]
          (some (withWords flag [3, 8, 0] [3, 9, 0] bits tags)) =
        some (liveWithWords .different flag [0] [0] bits tags) :=
    run (sentinelCaller 13) [3, 8, 0] [3, 9, 0] (stale flag) (protectedWords bits tags)
  have halted := append_actual_step (sentinelCaller 13) 2 _ _ _ returned
    (sentinel_push_step 13 .different flag [0] [0] bits tags)
  have absent := append_actual_step (sentinelCaller 13) 3 _ _ _ halted
    (present_halt_then_outer_none (sentinelCaller 13) flag [0] [0] bits (13 :: tags))
  exact ⟨returned, halted, absent, rfl, rfl⟩

theorem false_caller_flag_is_preserved (caller : ExampleCaller) :
    (next caller)^[2] (some (ordinaryStart false [3, 8, 0] [3, 9, 0])) =
      some (ordinaryReturn .different false [0] [0]) :=
  literal_05_internal_mismatch caller false

theorem forged_equal_step (flag : Bool) (xs ys : Word) (bits : List Bool) (tags : Word) :
    step forgeEqualCaller (liveWithWords .different flag xs ys bits tags) =
      some (liveWithWords .equal flag xs ys bits tags) := rfl

/-- A later live equal label does not characterize the original words. -/
theorem eventual_equal_is_not_first_equal (flag : Bool) (bits : List Bool) (tags : Word) :
    ¬ FirstResult forgeEqualCaller .equal [3] [12] (stale flag) (protectedWords bits tags) ∧
      (next forgeEqualCaller)^[1] (some (withWords flag [3] [12] bits tags)) =
        some (liveWithWords .different flag [] [] bits tags) ∧
      (next forgeEqualCaller)^[2] (some (withWords flag [3] [12] bits tags)) =
        some (liveWithWords .equal flag [] [] bits tags) := by
  have returned :
      (next forgeEqualCaller)^[1] (some (withWords flag [3] [12] bits tags)) =
        some (liveWithWords .different flag [] [] bits tags) :=
    run forgeEqualCaller [3] [12] (stale flag) (protectedWords bits tags)
  refine ⟨?_, returned, append_actual_step forgeEqualCaller 1 _ _ _ returned
    (forged_equal_step flag [] [] bits tags)⟩
  rw [firstResult_iff]
  decide

theorem reentry_step (flag : Bool) (xs ys : Word) (bits : List Bool) (tags : Word) :
    step reenterCaller (liveWithWords .different flag xs ys bits tags) =
      some (cfg (some (phaseLabel .compare)) (clean flag) xs ys (protectedWords bits tags)) :=
  rfl

/-- Reentering compare starts a later owned segment after the original different return. -/
theorem real_reentry_has_a_new_owned_segment (flag : Bool)
    (bits : List Bool) (tags : Word) :
    runSteps [3, 7] [12, 7] = 1 ∧
      (next reenterCaller)^[0] (some (withWords flag [3, 7] [12, 7] bits tags)) =
        some (withWords flag [3, 7] [12, 7] bits tags) ∧
      (next reenterCaller)^[1] (some (withWords flag [3, 7] [12, 7] bits tags)) =
        some (liveWithWords .different flag [7] [7] bits tags) ∧
      (next reenterCaller)^[2] (some (withWords flag [3, 7] [12, 7] bits tags)) =
        some (cfg (some (phaseLabel .compare)) (clean flag) [7] [7] (protectedWords bits tags)) ∧
      (next reenterCaller)^[3] (some (withWords flag [3, 7] [12, 7] bits tags)) =
        some (cfg (some (phaseLabel .compare)) (clean flag) [] [] (protectedWords bits tags)) ∧
      (next reenterCaller)^[4] (some (withWords flag [3, 7] [12, 7] bits tags)) =
        some (liveWithWords .equal flag [] [] bits tags) := by
  have first :
      (next reenterCaller)^[1] (some (withWords flag [3, 7] [12, 7] bits tags)) =
        some (liveWithWords .different flag [7] [7] bits tags) :=
    run reenterCaller [3, 7] [12, 7] (stale flag) (protectedWords bits tags)
  have second := append_actual_step reenterCaller 1 _ _ _ first
    (reentry_step flag [7] [7] bits tags)
  have third := append_actual_step reenterCaller 2 _ _ _ second
    (compare_step_same reenterCaller 7 [] [] (clean flag) (protectedWords bits tags))
  have fourth := append_actual_step reenterCaller 3 _ _ _ third
    (compare_step_nil_nil reenterCaller (clean flag) (protectedWords bits tags))
  exact ⟨rfl, rfl, first, second, third, fourth⟩

theorem allocation_step (flag : Bool) (bits : List Bool) (tags : Word) :
    step allocatingCaller (liveWithWords .equal flag [] [] bits tags) =
      some (liveWithWords .equal flag [] [] bits (13 :: tags)) := by
  apply congrArg some
  apply cfg_ext
  · rfl
  · rfl
  · rfl
  · rfl
  · intro k
    fin_cases k <;> rfl

/-- The sharp owned bound holds at first return and fails under a real allocating caller. -/
theorem caller_allocates_beyond_the_owned_space_bound (flag : Bool)
    (bits : List Bool) (tags : Word) :
    (next allocatingCaller)^[1] (some (withWords flag [] [] bits tags)) =
        some (liveWithWords .equal flag [] [] bits tags) ∧
      (next allocatingCaller)^[2] (some (withWords flag [] [] bits tags)) =
        some (liveWithWords .equal flag [] [] bits (13 :: tags)) ∧
      (next allocatingCaller)^[3] (some (withWords flag [] [] bits tags)) =
        some (liveWithWords .equal flag [] [] bits (13 :: 13 :: tags)) ∧
      stackCells (liveWithWords .equal flag [] [] bits tags) = bits.length + tags.length ∧
      stackCells (liveWithWords .equal flag [] [] bits (13 :: tags)) =
        bits.length + tags.length + 1 ∧
      stackCells (liveWithWords .equal flag [] [] bits (13 :: 13 :: tags)) =
        bits.length + tags.length + 2 ∧
      stackCells (withWords flag [] [] bits tags) <
        stackCells (liveWithWords .equal flag [] [] bits (13 :: tags)) := by
  have first :
      (next allocatingCaller)^[1] (some (withWords flag [] [] bits tags)) =
        some (liveWithWords .equal flag [] [] bits tags) :=
    compare_step_nil_nil allocatingCaller (stale flag) (protectedWords bits tags)
  have second := append_actual_step allocatingCaller 1 _ _ _ first (allocation_step flag bits tags)
  have third := append_actual_step allocatingCaller 2 _ _ _ second
    (allocation_step flag bits (13 :: tags))
  refine ⟨first, second, third, ?_, ?_, ?_, ?_⟩ <;>
    simp [liveWithWords, withWords, stackCells_cfg, protected_cell_count, Nat.add_assoc]

def externalLive (flag : Bool) (bits : List Bool) (tags : Word) : ExampleCfg :=
  cfg (some (callerLabel ())) (clean flag) [] [] (protectedWords bits tags)

theorem external_jump_step (flag : Bool) (bits : List Bool) (tags : Word) :
    step externalCaller (liveWithWords .equal flag [] [] bits tags) =
      some (externalLive flag bits tags) := rfl

theorem external_push_step (flag : Bool) (bits : List Bool) (tags : Word) :
    step externalCaller (externalLive flag bits tags) =
      some (haltedWithWords flag [] [] bits (13 :: tags)) := by
  apply congrArg some
  apply cfg_ext
  · rfl
  · rfl
  · rfl
  · rfl
  · intro k
    fin_cases k <;> rfl

theorem actual_external_label_and_posthalt (flag : Bool) (bits : List Bool) (tags : Word) :
    (next externalCaller)^[1] (some (withWords flag [] [] bits tags)) =
        some (liveWithWords .equal flag [] [] bits tags) ∧
      (next externalCaller)^[2] (some (withWords flag [] [] bits tags)) =
        some (externalLive flag bits tags) ∧
      (next externalCaller)^[3] (some (withWords flag [] [] bits tags)) =
        some (haltedWithWords flag [] [] bits (13 :: tags)) ∧
      (next externalCaller)^[4] (some (withWords flag [] [] bits tags)) = none := by
  have first :
      (next externalCaller)^[1] (some (withWords flag [] [] bits tags)) =
        some (liveWithWords .equal flag [] [] bits tags) :=
    compare_step_nil_nil externalCaller (stale flag) (protectedWords bits tags)
  have second := append_actual_step externalCaller 1 _ _ _ first (external_jump_step flag bits tags)
  have third := append_actual_step externalCaller 2 _ _ _ second (external_push_step flag bits tags)
  have fourth := append_actual_step externalCaller 3 _ _ _ third
    (present_halt_then_outer_none externalCaller flag [] [] bits (13 :: tags))
  exact ⟨first, second, third, fourth⟩

/-! Real FinTM2 package: input initialization is separate from a two-word handoff. -/

theorem package_carriers_are_the_actual_carriers (caller : ExampleCaller) (initial : Bool) :
    @Fintype.card (machine caller initial).K (machine caller initial).kFin = 4 ∧
      @Fintype.card (machine caller initial).Λ (machine caller initial).ΛFin = 4 ∧
      @Fintype.card (machine caller initial).σ (machine caller initial).σFin = 68 := by
  change Fintype.card (StackId (Fin 2)) = 4 ∧
    Fintype.card (Label Unit) = 4 ∧ Fintype.card (Registers Bool) = 68
  exact ⟨actual_finite_carrier_counts.2.2.2.1,
    actual_finite_carrier_counts.2.2.2.2.1, actual_finite_carrier_counts.2.2.2.2.2⟩

theorem package_control_and_initial_registers (caller : ExampleCaller) (initial : Bool) :
    (machine caller initial).k₀ = .inl .source ∧
      (machine caller initial).k₁ = .inl .source ∧
      (machine caller initial).main = phaseLabel .compare ∧
      (machine caller initial).initialState = ((none, none), initial) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The source input is initialized once; the target and all protected stacks are empty. -/
theorem actual_one_input_configuration (caller : ExampleCaller) (initial : Bool) (raw : Word) :
    Turing.initList (machine caller initial) raw =
      cfg (some (phaseLabel .compare)) (clean initial) raw [] (fun _ => []) :=
  initList_eq caller initial raw

def actualOneInputTime (caller : ExampleCaller) (initial : Bool) (raw : Word) :
    StateTransition.EvalsToInTime (machine caller initial).step
      (Turing.initList (machine caller initial) raw)
      (some (cfg (some (resultLabel (if raw = [] then .equal else .different)))
        (clean initial) raw.tail [] (fun _ => []))) 1 :=
  machineInitInTime caller initial raw

theorem actual_one_input_three_literals (caller : ExampleCaller) (initial : Bool) :
    (fun c => c.bind (machine caller initial).step)^[1]
        (some (Turing.initList (machine caller initial) [])) =
      some (cfg (some (resultLabel .equal)) (clean initial) [] [] (fun _ => [])) ∧
      (fun c => c.bind (machine caller initial).step)^[1]
        (some (Turing.initList (machine caller initial) ([3, 12] : Word))) =
      some (cfg (some (resultLabel .different)) (clean initial) [12] [] (fun _ => [])) ∧
      (fun c => c.bind (machine caller initial).step)^[1]
        (some (Turing.initList (machine caller initial) (treeCode empty.val))) =
      some (cfg (some (resultLabel .different)) (clean initial) [] [] (fun _ => [])) :=
  ⟨machine_init_run caller initial [], machine_init_run caller initial [3, 12],
    machine_init_run caller initial (treeCode empty.val)⟩

/-- One fixed package handles arbitrary configurations installed by an executed handoff. -/
def actualTwoWordTime (caller : ExampleCaller) (initial : Bool) (xs ys : Word)
    (regs : Registers Bool) (ctx : ∀ k, List (ProtectedAlphabet k)) :
    StateTransition.EvalsToInTime (machine caller initial).step
      (cfg (some (phaseLabel .compare)) regs xs ys ctx)
      (some (resultCfg xs ys regs ctx)) (runSteps xs ys) :=
  machineCfgInTime caller initial xs ys regs ctx

theorem same_package_two_word_run (caller : ExampleCaller) (initial : Bool) (xs ys : Word)
    (regs : Registers Bool) (ctx : ∀ k, List (ProtectedAlphabet k)) :
    (∀ c : ExampleCfg, (machine caller initial).step c = step caller c) ∧
      (fun c => c.bind (machine caller initial).step)^[runSteps xs ys]
        (some (cfg (some (phaseLabel .compare)) regs xs ys ctx)) =
      some (resultCfg xs ys regs ctx) ∧
      (actualTwoWordTime caller initial xs ys regs ctx).steps = runSteps xs ys :=
  ⟨machine_step_eq caller initial, machine_cfg_run caller initial xs ys regs ctx, rfl⟩

/-- Actual initialization of one nil code is different from two installed nil codes. -/
theorem one_input_nil_is_not_a_free_two_input_adapter (caller : ExampleCaller) (initial : Bool) :
    (fun c => c.bind (machine caller initial).step)^[1]
        (some (Turing.initList (machine caller initial) (treeCode empty.val))) =
      some (cfg (some (resultLabel .different)) (clean initial) [] [] (fun _ => [])) ∧
      (fun c => c.bind (machine caller initial).step)^[2]
        (some (cfg (some (phaseLabel .compare)) (clean initial)
          (treeCode empty.val) (treeCode empty.val) (fun _ => []))) =
      some (cfg (some (resultLabel .equal)) (clean initial) [] [] (fun _ => [])) :=
  ⟨machine_init_run caller initial (treeCode empty.val),
    machine_cfg_run caller initial (treeCode empty.val) (treeCode empty.val)
      (clean initial) (fun _ => [])⟩

/-- The separate external constructor is executed by the same finite machine. -/
theorem package_executes_the_external_caller (initial flag : Bool)
    (bits : List Bool) (tags : Word) :
    (fun c => c.bind (machine externalCaller initial).step)^[2]
        (some (withWords flag [] [] bits tags)) =
      some (externalLive flag bits tags) ∧
      (fun c => c.bind (machine externalCaller initial).step)^[3]
        (some (withWords flag [] [] bits tags)) =
      some (haltedWithWords flag [] [] bits (13 :: tags)) ∧
      (fun c => c.bind (machine externalCaller initial).step)^[4]
        (some (withWords flag [] [] bits tags)) = none :=
  ⟨(actual_external_label_and_posthalt flag bits tags).2.1,
    (actual_external_label_and_posthalt flag bits tags).2.2.1,
    (actual_external_label_and_posthalt flag bits tags).2.2.2⟩

theorem first_return_is_live_not_halted (caller : ExampleCaller) (flag : Bool) :
    (next caller)^[3] (some (ordinaryStart flag [3, 12] [3, 12])) =
      some (ordinaryReturn .equal flag [] []) ∧
      (ordinaryReturn .equal flag [] []).l ≠ none ∧
      (some (ordinaryReturn .equal flag [] []) : Option ExampleCfg) ≠ none := by
  refine ⟨literal_04_equal_word caller flag, ?_, ?_⟩ <;>
    intro impossible <;> cases impossible

end Examples.RotationCertificateTreeEqualityMachine
