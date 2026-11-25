import Examples.RotationCertificateStreamMachine.Execution

/-!
# RotationCertificateStreamMachine: Boundaries
-/

namespace Examples.RotationCertificateStreamMachine
open Trees Resources.RotationCertificate
open Search.SharedTree (Branch)
open Trees.Rotations (RotationDirection RotationMove)
open Resources.BinaryCounter (Bits)
open Resources.RotationCertificate.StreamMachine

/-! ## Selected partial resets preserve every other register component -/

theorem all_eleven_component_steps_keep_the_independently_fixed_reset_stages
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    ∀ c ∈ resetCases, c.Expected (step caller) regs ctx := by
  intro c member
  simp only [resetCases, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact inspect_step_nil caller ({} : LocalData) rfl regs ctx
  · exact inspect_step_cons caller ({certificate := [15]} : LocalData) 15 [] rfl regs ctx
  · exact counter_step_of_step caller (fun _ => .halt) .borrow ({fuel := [false, true]} : LocalData) regs ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_false (FuelDispatchMachine.callerHandler (fun _ => .halt)) [true] regs [] (FuelDispatchMachine.stores (({fuel := [false, true]} : LocalData).certificate) (fuelContext ({fuel := [false, true]} : LocalData) ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .borrow ({fuel := [true]} : LocalData) regs ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.borrow_step_true (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] regs [] (FuelDispatchMachine.stores (({fuel := [true]} : LocalData).certificate) (fuelContext ({fuel := [true]} : LocalData) ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreTrue ({units := [()]} : LocalData) regs ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreTrue_step_cons (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] regs [] (FuelDispatchMachine.stores (({units := [()]} : LocalData).certificate) (fuelContext ({units := [()]} : LocalData) ctx)))
  · exact counter_step_of_step caller (fun _ => .halt) .restoreFalse ({} : LocalData) regs ctx _ _ _ _
      (Resources.BinaryCounter.FixedWidthMachine.restoreFalse_step_nil (FuelDispatchMachine.callerHandler (fun _ => .halt)) [] regs (FuelDispatchMachine.stores (({} : LocalData).certificate) (fuelContext ({} : LocalData) ctx)))
  · exact equality_step_of_step caller (fun _ => .halt) ({source := [15], target := [15]} : LocalData) regs ctx _ _ _ _
      (TreeEqualityMachine.compare_step_same (fun _ => .halt) 15 [] [] (equalityRegisterEquiv.symm regs) (equalityContext ({source := [15], target := [15]} : LocalData) ctx))
  · exact equality_step_of_step caller (fun _ => .halt) ({source := [1], target := [0]} : LocalData) regs ctx _ _ _ _
      (TreeEqualityMachine.compare_step_different (fun _ => .halt) 1 0 [] [] (equalityRegisterEquiv.symm regs) (equalityContext ({source := [1], target := [0]} : LocalData) ctx) (by decide))
  · exact apply_move_step_of_step caller (fun _ => .halt) .start ({certificate := [6, 10]} : LocalData) regs ctx _ _ _ _ _
      (MoveParserMachine.start_step_direction (fun _ => .halt) .left [10] [] [] (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm regs)) (MoveApplyMachine.moveContext (applyData ({certificate := [6, 10]} : LocalData)) (applyContext ({certificate := [6, 10]} : LocalData) ctx)))
  · exact apply_step_of_step caller (fun _ => .halt) (MoveApplyMachine.dispatchPhase (.success .left)) ({} : LocalData) regs ctx _ _ _
      (MoveApplyMachine.dispatch_step (fun _ => .halt) (.success .left) (applyData ({} : LocalData))
        (applyRegisterEquiv.symm regs) (applyContext ({} : LocalData) ctx))
  · exact apply_position_advance_step caller (.seek .left) ({source := [1, 0], path := [.left]} : LocalData) regs ctx

/-! ## The nineteen literal source observations and the same actual executions -/

theorem all_nineteen_literal_source_observations_are_exact :
    ∀ c ∈ sourceCases, c.SourceExpected := by
  intro c member
  simp only [sourceCases, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num [SourceFixture.SourceExpected,
    a03, a04, a05, a06, a09, a10, a11, a12, a13, a14, a15,
    a16, a17, a18, a19, a20, r07, r08, r09, data,
    nilTree, oneTree, rightTwo, leftTwo, rightAtLeft, leftAtLeft, rightAtRight, leftAtRight,
    treeCode, nodeTag, emptyTag, checkStreamRun_nil, checkStreamRun_cons,
    Resources.BinaryCounter.decFixedRun, parseMoveRun, parsePathRun,
    applyMoveRun, applyAtRun, rotateRun, eqTreeRun,
    rotateLeftTag, rotateRightTag, endMoveTag, pathLeftTag, pathRightTag,
    Resources.bind, Resources.CallCount.tick]

theorem every_source_fixture_is_one_of_the_fixed_actual_run_fixtures :
    ∀ c ∈ sourceCases, c.run ∈ allCases := by
  intro c member
  simp only [sourceCases, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [allCases, initialCases, postReadCases]

theorem every_represented_literal_keeps_source_cost_separate_from_machine_time
    {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
    (caller : External Λ → Statement Γ Λ R) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    ∀ c ∈ sourceCases, c.SourceExpected ∧ c.run.RunExpected (step caller) regs ctx := by
  intro c member
  exact ⟨all_nineteen_literal_source_observations_are_exact c member,
    every_original_and_post_read_fixture_is_an_actual_first_run caller regs ctx c.run
      (every_source_fixture_is_one_of_the_fixed_actual_run_fixtures c member)⟩

/-! ## Complete selected boundaries, exact remaining rank and physical cells -/

def Boundary.Expected {K Λ R : Type} {Γ : K → Type} [Fintype K]
    (b : Boundary) (transition : Cfg Γ Λ R → Option (Cfg Γ Λ R))
    (start : Cfg Γ Λ R) (regs : Registers R) (ctx : ∀ k, List (Γ k)) : Prop :=
  b.RunExpected transition start regs ctx ∧
  remainingSteps (b.reached (Λ := Λ) regs ctx) = b.remaining ∧
  physicalCells (b.reached (Λ := Λ) regs ctx) = b.cells + externalCells ctx ∧
  (b.reached (Λ := Λ) regs ctx).var = b.stage.apply regs ∧
  ∀ k, (b.reached (Λ := Λ) regs ctx).stk (.inr k) = ctx k

section LiteralBoundaryConnections
variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
variable (caller : External Λ → Statement Γ Λ R)
variable (regs : Registers R) (ctx : ∀ k, List (Γ k))

theorem boundary_expected_of_actual_trace (c : RunFixture) (points : Nat → TracePoint)
    (literal : evaluate c.phase c.before = ⟨c.result, c.after, c.ticks⟩)
    (first : (points 0).reached (Λ := Λ) regs ctx = c.start regs ctx)
    (adjacent : ∀ n, n < c.ticks →
      step caller ((points n).reached regs ctx) = some ((points (n + 1)).reached regs ctx))
    (b : Boundary) (bound : b.tick ≤ c.ticks)
    (state : (points b.tick).reached (Λ := Λ) regs ctx = b.reached regs ctx)
    (count : fixtureCells b.stores = b.cells)
    (rank : b.remaining = c.ticks - b.tick) :
    b.Expected (step caller) (c.start regs ctx) regs ctx := by
  have executed : Runs (step caller) (c.start regs ctx) b.tick (b.reached regs ctx) := by
    simpa only [first, state] using
      finite_trace_actual_prefix caller regs ctx points c.ticks adjacent b.tick bound
  have initialRank : remainingSteps (c.start (Λ := Λ) regs ctx) = c.ticks := by
    rw [RunFixture.start, remainingSteps_phase_cfg]
    change (evaluate c.phase c.before).steps = c.ticks
    rw [literal]
  obtain ⟨reached, actual, remaining, _, _⟩ := owned_prefix caller (c.start regs ctx)
    b.tick (by rwa [initialRank])
  have same : reached = b.reached regs ctx := Option.some.inj (actual.symm.trans executed)
  subst reached
  refine ⟨executed, ?_, ?_, rfl, fun _ => rfl⟩
  · simpa only [initialRank, rank] using remaining
  · rw [Boundary.reached, actual_physical_cells_of_complete_cfg, count]

theorem all_thirteen_root_left_literal_boundaries_have_their_actual_rank_and_cells :
    ∀ b ∈ rootLeftBoundaries, b.Expected (step caller) (a12.start regs ctx) regs ctx := by
  intro b member
  apply boundary_expected_of_actual_trace caller regs ctx a12 trace_a12
    a12_literal_evaluation rfl (trace_a12_steps caller regs ctx) b
  all_goals
    simp only [rootLeftBoundaries, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | rfl | decide

theorem all_five_dirty_branch_boundaries_have_their_actual_rank_and_cells :
    ∀ b ∈ frontEndDirtyBoundaries, b.Expected (step caller) (r10.start regs ctx) regs ctx := by
  intro b member
  apply boundary_expected_of_actual_trace caller regs ctx r10 trace_r10
    r10_literal_evaluation rfl (trace_r10_steps caller regs ctx) b
  all_goals
    simp only [frontEndDirtyBoundaries, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl
    all_goals first | rfl | decide

end LiteralBoundaryConnections

theorem every_fixed_run_uses_the_actual_finite_register_carrier_and_five_protected_cells
    (caller : ExampleCaller) (regs : Registers Bool) :
    ∀ c ∈ allCases, c.RunExpected (step caller) regs ordinaryContext ∧
      ExactPeak (step caller) (c.start regs ordinaryContext) c.ticks (c.peak + 5) := by
  intro c member
  have actual := every_fixed_original_and_post_read_run_has_its_exact_inclusive_peak
    caller regs ordinaryContext c member
  simpa only [RunFixture.Expected, ordinary_protected_context_has_five_physical_cells] using actual

theorem the_same_finite_physical_examples_allow_infinitely_many_caller_labels
    (caller : External Nat → Statement IndependentAlphabet Nat Bool)
    (regs : Registers Bool) :
    Fintype.card (OwnedLabel Nat) = 39 ∧
      ∀ c ∈ allCases, c.Expected (step caller) regs ordinaryContext :=
  ⟨card_ownedLabel, every_fixed_original_and_post_read_run_has_its_exact_inclusive_peak
    caller regs ordinaryContext⟩

/-! ## Caller continuations are later activations, outside the first result -/

def certificateReentryCaller : ExampleCaller
  | .inl true => .push (.inl .certificate) (fun _ => 15)
      (.goto (fun _ => phaseLabel inspectPhase))
  | _ => .halt

def protectedReentryCaller : ExampleCaller
  | .inl true => .push (.inr 0) (fun _ => true)
      (.goto (fun _ => phaseLabel inspectPhase))
  | _ => .halt

def enlargedContext : ∀ k, List (IndependentAlphabet k) :=
  independentWords [true, true, false, true] [11, 15]

theorem a_later_certificate_push_changes_the_result_only_after_the_first_true
    (flag : Bool) :
    FirstRun (step certificateReentryCaller) (a01.start (stale flag) ordinaryContext) 4
      (a01.finish (stale flag) ordinaryContext) ∧
    Runs (step certificateReentryCaller) (a01.start (stale flag) ordinaryContext) 5
      (cfg (some (phaseLabel inspectPhase)) (clean flag) {certificate := [15]} ordinaryContext) ∧
    Runs (step certificateReentryCaller) (a01.start (stale flag) ordinaryContext) 9
      (cfg (some (resultLabel false)) (clean flag) {certificate := [15]} ordinaryContext) := by
  have first := a01_actual_first_run certificateReentryCaller (stale flag) ordinaryContext
  have push : step certificateReentryCaller (a01.finish (stale flag) ordinaryContext) =
      some (cfg (some (phaseLabel inspectPhase)) (clean flag) {certificate := [15]} ordinaryContext) := by
    apply congrArg some
    apply cfg_ext <;> first | rfl | (funext k; cases k with
      | inl k => cases k <;> rfl
      | inr k => rfl)
  have atFive := iterate_trans certificateReentryCaller first.1 (show
    (next certificateReentryCaller)^[1] (some (a01.finish (stale flag) ordinaryContext)) = _ from push)
  have second := a02_actual_first_run certificateReentryCaller (clean flag) ordinaryContext
  exact ⟨first, atFive, iterate_trans certificateReentryCaller atFive second.1⟩

theorem the_later_false_is_not_the_initial_first_result (flag : Bool) :
    ¬ FirstResult (step certificateReentryCaller) (a01.start (stale flag) ordinaryContext) false := by
  intro later
  have value := (every_owned_entry_has_exactly_its_evaluated_first_boolean
    certificateReentryCaller a01.phase a01.before (stale flag) ordinaryContext false).mp later
  rw [a01_literal_evaluation] at value
  cases value

theorem a_protected_caller_push_occurs_at_five_and_reenters_until_nine
    (flag : Bool) :
    FirstRun (step protectedReentryCaller) (a01.start (stale flag) ordinaryContext) 4
      (a01.finish (stale flag) ordinaryContext) ∧
    Runs (step protectedReentryCaller) (a01.start (stale flag) ordinaryContext) 5
      (cfg (some (phaseLabel inspectPhase)) (clean flag) {} enlargedContext) ∧
    Runs (step protectedReentryCaller) (a01.start (stale flag) ordinaryContext) 9
      (cfg (some (resultLabel true)) (clean flag) {} enlargedContext) := by
  have first := a01_actual_first_run protectedReentryCaller (stale flag) ordinaryContext
  have push : step protectedReentryCaller (a01.finish (stale flag) ordinaryContext) =
      some (cfg (some (phaseLabel inspectPhase)) (clean flag) {} enlargedContext) := by
    apply congrArg some
    apply cfg_ext
    · rfl
    · rfl
    · funext k
      cases k with
      | inl k => cases k <;> rfl
      | inr k => fin_cases k <;> rfl
  have atFive := iterate_trans protectedReentryCaller first.1 (show
    (next protectedReentryCaller)^[1] (some (a01.finish (stale flag) ordinaryContext)) = _ from push)
  have second := a01_actual_first_run protectedReentryCaller (clean flag) enlargedContext
  exact ⟨first, atFive, iterate_trans protectedReentryCaller atFive second.1⟩

theorem the_post_return_protected_push_exceeds_the_owned_prefix_peak
    (flag : Bool) :
    physicalCells (cfg (some (phaseLabel (Λ := Unit) inspectPhase)) (clean flag)
      ({} : LocalData) enlargedContext) = 6 ∧
    (cfg (some (phaseLabel (Λ := Unit) inspectPhase)) (clean flag)
      ({} : LocalData) enlargedContext).stk (.inr 0) = [true, true, false, true] ∧
    5 < physicalCells (cfg (some (phaseLabel (Λ := Unit) inspectPhase)) (clean flag)
      ({} : LocalData) enlargedContext) := by
  have cells : physicalCells (cfg (some (phaseLabel (Λ := Unit) inspectPhase)) (clean flag)
      ({} : LocalData) enlargedContext) = 6 := by
    rw [actual_physical_cells_of_complete_cfg]
    change (∑ k : Fin 2, (enlargedContext k).length) = 6
    rw [Fin.sum_univ_two]
    rfl
  exact ⟨cells, rfl, by omega⟩

theorem halting_the_caller_is_live_at_five_and_outer_none_at_six
    (flag : Bool) :
    Runs (step (fun _ : External Unit => .halt)) (a01.start (stale flag) ordinaryContext) 5
      (cfg none (clean flag) {} ordinaryContext) ∧
    (next (fun _ : External Unit => .halt))^[6]
      (some (a01.start (stale flag) ordinaryContext)) = none := by
  let caller : ExampleCaller := fun _ => .halt
  have first := a01_actual_first_run caller (stale flag) ordinaryContext
  have after : (next caller)^[1] (some (a01.finish (stale flag) ordinaryContext)) =
      some (cfg none (clean flag) {} ordinaryContext) := by
    change step caller (cfg (some (resultLabel true)) (clean flag) {} ordinaryContext) = _
    exact a_live_boolean_can_be_followed_by_a_distinct_live_halt_configuration
      true (clean flag) {} ordinaryContext
  have atFive : (next caller)^[5] (some (a01.start (stale flag) ordinaryContext)) =
      some (cfg none (clean flag) {} ordinaryContext) := iterate_trans caller first.1 after
  refine ⟨atFive, ?_⟩
  change (next caller)^[5 + 1] (some (a01.start (stale flag) ordinaryContext)) = none
  rw [Function.iterate_succ_apply', atFive, next_some]
  rfl

/-! ## Two universal malformed families and eighteen independent finite instances -/

def nodeWord (n : Nat) : Word := List.replicate n 1

def sharpStart {K Λ R : Type} {Γ : K → Type} (direction : RotationDirection)
    (rest : Word) (count : Nat) (target : Word) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) : Cfg Γ Λ R :=
  cfg (some (phaseLabel inspectPhase)) regs
    (data (moveCode ⟨direction, []⟩ ++ rest) [] [] (nodeWord count) [] [] [] [true] target) ctx

def sharpFinish {K Λ R : Type} {Γ : K → Type}
    (rest : Word) (count : Nat) (target : Word) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) : Cfg Γ Λ R :=
  cfg (some (resultLabel false)) (resetAll regs)
    (data rest [] [] (nodeWord count) [] [] [] [false] target) ctx

def sharpDrop {K Λ R : Type} {Γ : K → Type}
    (rest : Word) (count pending : Nat) (target : Word) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) : Cfg Γ Λ R :=
  cfg (some (phaseLabel (applyPhase (MoveApplyMachine.positionPhase .dropPending))))
    (resetAll regs) (data rest [] [] (nodeWord count) [] [] (List.replicate pending ())
      [false] target) ctx

def LeftSharpExpected {K Λ R : Type} {Γ : K → Type} [Fintype K]
    (transition : Cfg Γ Λ R → Option (Cfg Γ Λ R))
    (rest : Word) (n : Nat) (target : Word) (regs : Registers R) (ctx : ∀ k, List (Γ k)) : Prop :=
  FirstRun transition (sharpStart .left rest n target regs ctx) (3 * n + 13)
    (sharpFinish rest n target regs ctx) ∧
  Runs transition (sharpStart .left rest n target regs ctx) (2 * n + 10)
    (sharpDrop rest n n target regs ctx) ∧
  remainingSteps (sharpDrop (Λ := Λ) rest n n target regs ctx) = n + 3 ∧
  physicalCells (sharpDrop (Λ := Λ) rest n n target regs ctx) =
    rest.length + 2 * n + 1 + target.length + externalCells ctx ∧
  ExactPeak transition (sharpStart .left rest n target regs ctx) (3 * n + 13)
    (rest.length + max (n + 2) (2 * n) + 1 + target.length + externalCells ctx)

def RightSharpExpected {K Λ R : Type} {Γ : K → Type} [Fintype K]
    (transition : Cfg Γ Λ R → Option (Cfg Γ Λ R))
    (rest : Word) (m : Nat) (target : Word) (regs : Registers R) (ctx : ∀ k, List (Γ k)) : Prop :=
  FirstRun transition (sharpStart .right rest (m + 2) target regs ctx) (3 * m + 16)
    (sharpFinish rest (m + 2) target regs ctx) ∧
  Runs transition (sharpStart .right rest (m + 2) target regs ctx) (2 * m + 12)
    (sharpDrop rest (m + 2) (m + 1) target regs ctx) ∧
  remainingSteps (sharpDrop (Λ := Λ) rest (m + 2) (m + 1) target regs ctx) = m + 4 ∧
  physicalCells (sharpDrop (Λ := Λ) rest (m + 2) (m + 1) target regs ctx) =
    rest.length + 2 * m + 4 + target.length + externalCells ctx ∧
  ExactPeak transition (sharpStart .right rest (m + 2) target regs ctx) (3 * m + 16)
    (rest.length + max (m + 4) (2 * m + 3) + 1 + target.length + externalCells ctx)

structure SharpFixture where
  direction : RotationDirection
  parameter : Nat
  ticks : Nat
  dropTime : Nat
  remaining : Nat
  peak : Nat
  dropCells : Nat

def SharpFixture.sourceCount (c : SharpFixture) : Nat :=
  match c.direction with | .left => c.parameter | .right => c.parameter + 2

def SharpFixture.pendingCount (c : SharpFixture) : Nat :=
  match c.direction with | .left => c.parameter | .right => c.parameter + 1

def SharpFixture.Expected (c : SharpFixture) (transition : ExampleCfg → Option ExampleCfg)
    (regs : Registers Bool) : Prop :=
  FirstRun transition (sharpStart c.direction [15, 2] c.sourceCount [15] regs ordinaryContext)
    c.ticks (sharpFinish [15, 2] c.sourceCount [15] regs ordinaryContext) ∧
  Runs transition (sharpStart c.direction [15, 2] c.sourceCount [15] regs ordinaryContext)
    c.dropTime (sharpDrop [15, 2] c.sourceCount c.pendingCount [15] regs ordinaryContext) ∧
  remainingSteps (sharpDrop (Λ := Unit) [15, 2] c.sourceCount c.pendingCount [15] regs ordinaryContext) =
    c.remaining ∧
  physicalCells (sharpDrop (Λ := Unit) [15, 2] c.sourceCount c.pendingCount [15] regs ordinaryContext) =
    c.dropCells ∧
  ExactPeak transition (sharpStart c.direction [15, 2] c.sourceCount [15] regs ordinaryContext)
    c.ticks c.peak

def sharpCases : List SharpFixture :=
  [⟨.left, 0, 13, 10, 3, 11, 9⟩,
   ⟨.left, 1, 16, 12, 4, 12, 11⟩,
   ⟨.left, 2, 19, 14, 5, 13, 13⟩,
   ⟨.left, 3, 22, 16, 6, 15, 15⟩,
   ⟨.left, 4, 25, 18, 7, 17, 17⟩,
   ⟨.left, 5, 28, 20, 8, 19, 19⟩,
   ⟨.left, 6, 31, 22, 9, 21, 21⟩,
   ⟨.left, 7, 34, 24, 10, 23, 23⟩,
   ⟨.left, 8, 37, 26, 11, 25, 25⟩,
   ⟨.right, 0, 16, 12, 4, 13, 12⟩,
   ⟨.right, 1, 19, 14, 5, 14, 14⟩,
   ⟨.right, 2, 22, 16, 6, 16, 16⟩,
   ⟨.right, 3, 25, 18, 7, 18, 18⟩,
   ⟨.right, 4, 28, 20, 8, 20, 20⟩,
   ⟨.right, 5, 31, 22, 9, 22, 22⟩,
   ⟨.right, 6, 34, 24, 10, 24, 24⟩,
   ⟨.right, 7, 37, 26, 11, 26, 26⟩,
   ⟨.right, 8, 40, 28, 12, 28, 28⟩]

theorem sharp_cases_count : sharpCases.length = 18 := rfl

/-! ## Complete component physical sums, prefix frames and typed clocks -/

section ComponentPhysicalSums
variable {K Λ R : Type} {Γ : K → Type} [Fintype K]

theorem every_component_view_counts_all_local_and_external_physical_words
    (f : FuelCfg Γ Λ R) (h : ApplyCfg Γ Λ R) (e : EqualityCfg Γ Λ R) :
    physicalCells (fuelCfg f) = FuelDispatchMachine.stackCells f ∧
      physicalCells (applyCfg h) = MoveApplyMachine.stackCells h ∧
      physicalCells (equalityCfg e) = TreeEqualityMachine.stackCells e :=
  ⟨stackCells_fuelCfg f, stackCells_applyCfg h, stackCells_equalityCfg e⟩

theorem dirty_move_allowance_is_the_actual_installed_component_potential
    (q : MoveApplyMachine.Phase) (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    hAllowance q D ctx = fixtureCells D + externalCells ctx +
        MoveApplyMachine.phaseDebt q + MoveApplyMachine.phaseCredit q (applyData D) ∧
      hAllowance q D ctx = MoveApplyMachine.potential
        (applyView (Λ := Λ) (some (MoveApplyMachine.phaseLabel q))
          (applyRegisterEquiv.symm regs) D ctx) :=
  ⟨rfl, hAllowance_eq_potential q D regs ctx⟩

end ComponentPhysicalSums

section ComponentPrefixContracts
variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
variable (caller : External Λ → Statement Γ Λ R)

theorem fuel_prefix_preserves_its_entire_component_complement
    (localCaller : (FuelDispatchMachine.Exit ⊕ FuelCallerLabel Λ) → FuelStatement Γ Λ R)
    (start : FuelCfg Γ Λ R) (n : Nat) (bound : n ≤ FuelDispatchMachine.remainingSteps start)
    (reached : Cfg Γ Λ R) (executed : Runs (step caller) (fuelCfg start) n reached) :
    ∃ middle, reached = fuelCfg middle ∧ middle.var.2 = start.var.2 ∧
      ∀ k, middle.stk (.inr k) = start.stk (.inr k) :=
  fuel_prefix_frame caller localCaller start n bound reached executed

theorem apply_prefix_preserves_fuel_target_bool_and_all_external_data
    (localCaller : MoveApplyMachine.External (ApplyCallerLabel Λ) → ApplyStatement Γ Λ R)
    (start : ApplyCfg Γ Λ R) (n : Nat) (bound : n ≤ MoveApplyMachine.remainingSteps start)
    (reached : Cfg Γ Λ R) (executed : Runs (step caller) (applyCfg start) n reached) :
    ∃ middle, reached = applyCfg middle ∧ middle.var.2 = start.var.2 ∧
      ∀ k, middle.stk (.inr k) = start.stk (.inr k) :=
  apply_prefix_frame caller localCaller start n bound reached executed

theorem equality_prefix_preserves_seven_local_complements_and_the_external_frame
    (localCaller : TreeEqualityMachine.External (EqualityCallerLabel Λ) → EqualityStatement Γ Λ R)
    (start : EqualityCfg Γ Λ R) (n : Nat) (bound : n ≤ TreeEqualityMachine.remainingSteps start)
    (reached : Cfg Γ Λ R) (executed : Runs (step caller) (equalityCfg start) n reached) :
    ∃ middle, reached = equalityCfg middle ∧ middle.var.2 = start.var.2 ∧
      ∀ k, middle.stk (.inr k) = start.stk (.inr k) :=
  equality_prefix_frame caller localCaller start n bound reached executed

def exact_phase_timing (q : Phase) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller) (cfg (some (phaseLabel q)) regs D ctx)
      (some (phaseResult q regs D ctx)) (phaseSteps q D) := phaseInTime caller q D regs ctx

def exact_configuration_timing (start : Cfg Γ Λ R) :
    StateTransition.EvalsToInTime (step caller) start (some (finalCfg start)) (remainingSteps start) :=
  cfgInTime caller start

def exact_dirty_inspection_timing (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller) (cfg (some (phaseLabel inspectPhase)) regs D ctx)
      (some (inspectResult regs D ctx)) (inspectSteps D) := inspectInTime caller D regs ctx

def exact_dirty_counter_stage_timing (q : Resources.BinaryCounter.FixedWidthMachine.Phase)
    (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller)
      (cfg (some (phaseLabel (counterPhase q))) regs D ctx)
      (some (cfg (some (phaseLabel (fuelJoinPhase (FuelDispatchMachine.exitOfResult (counterFinish q D).result))))
        (resetFuel regs) (counterFinish q D).data ctx)) (counterFinish q D).steps :=
  counterStageInTime caller q D regs ctx

def exact_dirty_inspection_stage_timing (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller) (cfg (some (phaseLabel inspectPhase)) regs D ctx)
      (some (cfg (some (phaseLabel (fuelJoinPhase (inspectStageFinish D).result)))
        (resetFuel regs) (inspectStageFinish D).data ctx)) (inspectStageFinish D).steps :=
  fuelStageInTime caller D regs ctx

def exact_dirty_apply_stage_timing (q : MoveApplyMachine.Phase) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller) (cfg (some (phaseLabel (applyPhase q))) regs D ctx)
      (some (cfg (some (phaseLabel (applyJoinPhase (applyFinish q D).result)))
        (resetApply regs) (applyFinish q D).data ctx)) (applyFinish q D).steps :=
  applyStageInTime caller q D regs ctx

def exact_raw_equality_stage_timing (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller) (cfg (some (phaseLabel comparePhase)) regs D ctx)
      (some (cfg (some (phaseLabel (equalityJoinPhase (equalityFinish D).result)))
        (resetEquality regs) (equalityFinish D).data ctx)) (equalityFinish D).steps :=
  equalityStageInTime caller D regs ctx

def every_fuel_join_is_a_one_step_typed_value (r : FuelDispatchMachine.Exit)
    (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller)
      (cfg (some (phaseLabel (fuelJoinPhase r))) regs D ctx)
      (some (cfg (some (fuelJoinTarget r)) (resetAll regs) D ctx)) 1 :=
  fuelJoinInTime caller r D regs ctx

def every_apply_join_is_a_one_step_typed_value (r : MoveApplyMachine.FinalResult)
    (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller)
      (cfg (some (phaseLabel (applyJoinPhase r))) regs D ctx)
      (some (cfg (some (applyJoinTarget r)) (resetAll regs) D ctx)) 1 :=
  applyJoinInTime caller r D regs ctx

def every_equality_join_is_a_one_step_typed_value (r : TreeEqualityMachine.Result)
    (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller)
      (cfg (some (phaseLabel (equalityJoinPhase r))) regs D ctx)
      (some (cfg (some (equalityJoinTarget r)) (resetAll regs) D ctx)) 1 :=
  equalityJoinInTime caller r D regs ctx

theorem all_eight_join_time_records_store_one
    (f : FuelDispatchMachine.Exit) (h : MoveApplyMachine.FinalResult) (e : TreeEqualityMachine.Result)
    (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (every_fuel_join_is_a_one_step_typed_value caller f D regs ctx).steps = 1 ∧
      (every_apply_join_is_a_one_step_typed_value caller h D regs ctx).steps = 1 ∧
      (every_equality_join_is_a_one_step_typed_value caller e D regs ctx).steps = 1 := ⟨rfl, rfl, rfl⟩

theorem global_and_component_typed_records_retain_exact_counts
    (q : Phase) (w : Resources.BinaryCounter.FixedWidthMachine.Phase)
    (h : MoveApplyMachine.Phase) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (start : Cfg Γ Λ R) :
    (exact_phase_timing caller q D regs ctx).steps = phaseSteps q D ∧
    (exact_configuration_timing caller start).steps = remainingSteps start ∧
    (exact_dirty_inspection_timing caller D regs ctx).steps = inspectSteps D ∧
    (exact_dirty_counter_stage_timing caller w D regs ctx).steps = (counterFinish w D).steps ∧
    (exact_dirty_inspection_stage_timing caller D regs ctx).steps = (inspectStageFinish D).steps ∧
    (exact_dirty_apply_stage_timing caller h D regs ctx).steps = (applyFinish h D).steps ∧
    (exact_raw_equality_stage_timing caller D regs ctx).steps = (equalityFinish D).steps :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end ComponentPrefixContracts


end Examples.RotationCertificateStreamMachine
