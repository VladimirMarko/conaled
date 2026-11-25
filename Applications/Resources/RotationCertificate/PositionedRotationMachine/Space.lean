import Applications.Resources.RotationCertificate.PositionedRotationMachine.Prefixes

/-!
# PositionedRotationMachine: Space
-/

set_option autoImplicit false
set_option warningAsError true
namespace Resources.RotationCertificate.PositionedRotationMachine
open Search.SharedTree (Branch)
open Trees.Rotations (RotationDirection RotationMove)
variable {K Λ R : Type} {Γ : K → Type}
variable [DecidableEq K]
variable (caller : External Λ → Statement Γ Λ R)

section PhysicalSpace

variable [Fintype K]

def contextCells (ctx : ∀ k, List (Γ k)) : Nat := ∑ k, (ctx k).length

/-- The actual dependent sum over every physical stack index. -/
def stackCells (c : Cfg Γ Λ R) : Nat := ∑ k : StackId K, (c.stk k).length

omit [DecidableEq K] in
theorem stackCells_eq_sum (c : Cfg Γ Λ R) :
    stackCells c = ∑ k : StackId K, (c.stk k).length := rfl

theorem localStack_sum (f : LocalStack → Nat) :
    ∑ k, f k = f .source + f .saved + f .scratch + f .pending + f .path := by
  change (∑ k ∈ ({.source, .saved, .scratch, .pending, .path} : Finset LocalStack), f k) = _
  simp [Nat.add_comm, Nat.add_left_comm]

omit [DecidableEq K] in
theorem stackCells_cfg (label : Option (Label Λ)) (regs : Registers R)
    (D : LocalData) (ctx : ∀ k, List (Γ k)) :
    stackCells (cfg label regs D ctx) = localCells D + contextCells ctx := by
  rw [stackCells, Fintype.sum_sum_type, localStack_sum]
  rfl

def potential (c : Cfg Γ Λ R) : Nat := stackCells c + debt c.l + credit c

omit [DecidableEq K] in
theorem potential_cfg (control : Control) (regs : Registers R)
    (D : LocalData) (ctx : ∀ k, List (Γ k)) :
    potential (cfg (some (controlLabel (Λ := Λ) control)) regs D ctx) =
      localPotential control D + contextCells ctx := by
  rw [potential, stackCells_cfg, credit_control_cfg]
  change localCells D + contextCells ctx + debt (some (controlLabel (Λ := Λ) control)) +
    controlCredit control D = _
  rw [debt_controlLabel]
  simp only [localPotential]
  omega

omit [DecidableEq K] in
theorem stackCells_le_potential (c : Cfg Γ Λ R) : stackCells c ≤ potential c := by
  unfold potential
  omega

theorem local_step_potential_le {before after : Cfg Γ Λ R}
    (transition : LocalStep caller before after) : potential after ≤ potential before := by
  obtain ⟨q, regs, D, ctx, rfl⟩ := owned_cases before transition.1
  have same := Option.some.inj ((advance_step caller q D regs ctx).symm.trans transition.2)
  subst after
  change potential (cfg (some (controlLabel (Λ := Λ) (advance q D).1)) (reset regs) (advance q D).2 ctx) ≤
    potential (cfg (some (controlLabel (Λ := Λ) (.inl q))) regs D ctx)
  rw [potential_cfg, potential_cfg]
  exact Nat.add_le_add_right (advance_mass q D).2 _

theorem local_reaches_potential_le {start reached : Cfg Γ Λ R}
    (path : Relation.ReflTransGen (LocalStep caller) start reached) : potential reached ≤ potential start := by
  induction path with
  | refl => exact Nat.le_refl _
  | @tail before after _ transition ih => exact (local_step_potential_le caller transition).trans ih

theorem prefix_potential_le (start : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start)
    (reached : Cfg Γ Λ R) (executed : (next caller)^[n] (some start) = some reached) :
    potential reached ≤ potential start := by
  obtain ⟨actual, run, _, path⟩ := Resources.BinaryCounter.FixedWidthMachine.ranked_prefix
    (step caller) remainingSteps (local_progress caller) n start bound
  have same := Option.some.inj (run.symm.trans executed)
  subst reached
  apply local_reaches_potential_le caller
  exact Relation.ReflTransGen.mono
    (fun before _ h => ⟨(remainingSteps_pos_iff before).mp h.1, h.2⟩) _ _ path

theorem prefix_stackCells_le_dirty (start : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start)
    (reached : Cfg Γ Λ R) (executed : (next caller)^[n] (some start) = some reached) :
    stackCells reached ≤ potential start :=
  (stackCells_le_potential reached).trans (prefix_potential_le caller start n bound reached executed)

omit [DecidableEq K] in
theorem entry_potential (d : RotationDirection) (raw : Word) (path : List Branch)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    potential (entry (Λ := Λ) d regs raw path ctx) =
      2 * raw.length + path.length + contextCells ctx := by
  change potential (cfg (some (controlLabel (Λ := Λ) (.inl (.seek d)))) regs
    { source := raw, path := path } ctx) = _
  rw [potential_cfg]
  simp [localPotential, localCells, controlDebt, phaseDebt, controlCredit, phaseCredit]; omega

theorem prefix_stackCells_le (d : RotationDirection) (raw : Word) (path : List Branch)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) (n : Nat) (bound : n ≤ runSteps d raw path)
    (reached : Cfg Γ Λ R) (executed : (next caller)^[n] (some (entry d regs raw path ctx)) = some reached) :
    stackCells reached ≤ 2 * raw.length + path.length + contextCells ctx := by
  have bounded := prefix_stackCells_le_dirty caller (entry d regs raw path ctx) n bound reached executed
  simpa only [entry_potential] using bounded

end PhysicalSpace

/-! ## Sharp malformed-input and path-stop families -/

section MalformedFamilies

omit [DecidableEq K] in
theorem continues_nodes (n h : Nat) :
    Continues (List.replicate n nodeTag) h (h + n) := by
  induction n with
  | zero => simpa using Continues.nil h
  | succ n ih =>
      simpa only [List.replicate_succ', Nat.add_assoc] using Continues.node ih

/-- The scanner prefix really consumes every node and creates every pending cell. -/
theorem scanScratch_nodes_localRun (d : RotationDirection) (n : Nat)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller n
      (cfg (some (phaseLabel (.scanScratch d))) (reset regs)
        { source := List.replicate n nodeTag, pending := [()] } ctx)
      (cfg (some (phaseLabel (.scanScratch d))) (reset regs)
        { scratch := List.replicate n nodeTag, pending := List.replicate (n + 1) () } ctx) := by
  simpa [afterScanRegisters, reset_reset, Nat.add_comm] using
    scanScratch_continues_localRun caller (continues_nodes n 1) d []
      ({} : LocalData) (reset regs) ctx

/-- Left all-node input attains its maximal physical size at this actual drop phase. -/
theorem left_nodes_drop (n : Nat) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (2 * n + 2)
      (cfg (some (phaseLabel (.seek .left))) regs { source := List.replicate n nodeTag } ctx)
      (cfg (some (phaseLabel .dropPending)) (reset regs)
        { source := List.replicate n nodeTag, pending := List.replicate n () } ctx) := by
  cases n with
  | zero =>
      have seek := phase_step_localRun caller
        (seek_step_path_nil caller .left ({} : LocalData) regs ctx)
      have start := phase_step_localRun caller
        (start_left_step_nil caller ({} : LocalData) (reset regs) ctx)
      simpa only [List.replicate_zero, reset_reset] using LocalRun.trans caller seek start
  | succ n =>
      let scanned : LocalData :=
        { scratch := List.replicate n nodeTag, pending := List.replicate (n + 1) () }
      let restored : LocalData :=
        { source := List.replicate n nodeTag, pending := List.replicate (n + 1) () }
      have seek := phase_step_localRun caller
        (seek_step_path_nil caller .left { source := nodeTag :: List.replicate n nodeTag } regs ctx)
      have start := phase_step_localRun caller
        (start_left_step_node caller (List.replicate n nodeTag) ({} : LocalData) (reset regs) ctx)
      have scan := scanScratch_nodes_localRun caller .left n regs ctx
      have failed := phase_step_localRun caller
        (scanScratch_step_nil caller .left scanned (reset regs) ctx)
      have moved : LocalRun caller n
          (cfg (some (phaseLabel (.restoreScratch .failureLeft))) (reset regs) scanned ctx)
          (cfg (some (phaseLabel (.restoreScratch .failureLeft))) (reset regs) restored ctx) := by
        simpa [scanned, restored, reset_reset] using
          restoreScratch_prefix_localRun caller .failureLeft (List.replicate n nodeTag) []
            { pending := List.replicate (n + 1) () } (reset regs) ctx
      have probe := phase_step_localRun caller
        (restoreScratch_step_nil caller .failureLeft restored (reset regs) ctx)
      have joined := LocalRun.trans caller seek (LocalRun.trans caller start
        (LocalRun.trans caller scan (LocalRun.trans caller failed (LocalRun.trans caller moved probe))))
      simpa [scanned, restored, scratchFailure, reset_reset, markerWord, modeResult,
        List.replicate_succ, Nat.mul_add, two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using joined

theorem left_nodes_run (n : Nat) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (3 * n + 4)
      (cfg (some (phaseLabel (.seek .left))) regs { source := List.replicate n nodeTag } ctx)
      (cfg (some (resultLabel .failure)) (reset regs) { source := List.replicate n nodeTag } ctx) := by
  have first := left_nodes_drop caller n regs ctx
  have last := dropPending_localRun caller
    { source := List.replicate n nodeTag, pending := List.replicate n () } (reset regs) ctx
  simpa [dropPendingData, reset_reset, Nat.succ_mul, two_mul,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using LocalRun.trans caller first last

/-- The right-root two-node setup creates one fewer cell than the clean bound. -/
theorem right_nodes_drop (m : Nat) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (2 * m + 4)
      (cfg (some (phaseLabel (.seek .right))) regs
        { source := List.replicate (m + 2) nodeTag } ctx)
      (cfg (some (phaseLabel .dropPending)) (reset regs)
        { source := List.replicate (m + 2) nodeTag,
          pending := List.replicate (m + 1) () } ctx) := by
  let scanned : LocalData :=
    { scratch := List.replicate m nodeTag, pending := List.replicate (m + 1) () }
  let restored : LocalData :=
    { source := List.replicate m nodeTag, pending := List.replicate (m + 1) () }
  have seek := phase_step_localRun caller
    (seek_step_path_nil caller .right
      { source := nodeTag :: nodeTag :: List.replicate m nodeTag } regs ctx)
  have start := phase_step_localRun caller
    (start_right_step_nodes caller (List.replicate m nodeTag) ({} : LocalData) (reset regs) ctx)
  have scan := scanScratch_nodes_localRun caller .right m regs ctx
  have failed := phase_step_localRun caller
    (scanScratch_step_nil caller .right scanned (reset regs) ctx)
  have moved : LocalRun caller m
      (cfg (some (phaseLabel (.restoreScratch .failureRight))) (reset regs) scanned ctx)
      (cfg (some (phaseLabel (.restoreScratch .failureRight))) (reset regs) restored ctx) := by
    simpa [scanned, restored, reset_reset] using
      restoreScratch_prefix_localRun caller .failureRight (List.replicate m nodeTag) []
        { pending := List.replicate (m + 1) () } (reset regs) ctx
  have probe := phase_step_localRun caller
    (restoreScratch_step_nil caller .failureRight restored (reset regs) ctx)
  have joined := LocalRun.trans caller seek (LocalRun.trans caller start
    (LocalRun.trans caller scan (LocalRun.trans caller failed (LocalRun.trans caller moved probe))))
  simpa [scanned, restored, scratchFailure, reset_reset, markerWord, modeResult,
    List.replicate_succ, two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using joined

theorem right_nodes_run (m : Nat) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (3 * m + 7)
      (cfg (some (phaseLabel (.seek .right))) regs
        { source := List.replicate (m + 2) nodeTag } ctx)
      (cfg (some (resultLabel .failure)) (reset regs)
        { source := List.replicate (m + 2) nodeTag } ctx) := by
  have first := right_nodes_drop caller m regs ctx
  have last := dropPending_localRun caller
    { source := List.replicate (m + 2) nodeTag,
      pending := List.replicate (m + 1) () } (reset regs) ctx
  simpa [dropPendingData, reset_reset, Nat.succ_mul, two_mul,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using LocalRun.trans caller first last

/-- Every successful left descent moves one literal marker to saved and pops one Branch. -/
theorem seek_left_nodes_localRun (d : RotationDirection) (n : Nat)
    (raw : Word) (p : List Branch) (f : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller n
      (cfg (some (phaseLabel (.seek d))) regs
        { source := List.replicate n nodeTag ++ raw,
          saved := f, path := List.replicate n Branch.left ++ p } ctx)
      (cfg (some (phaseLabel (.seek d))) (if n = 0 then regs else reset regs)
        { source := raw, saved := (List.replicate n nodeTag).reverse ++ f, path := p } ctx) := by
  induction n generalizing f regs with
  | zero =>
      simpa using LocalRun.refl (caller := caller)
        (cfg (some (phaseLabel (.seek d))) regs { source := raw, saved := f, path := p } ctx)
  | succ n ih =>
      have first := phase_step_localRun caller
        (seek_step_node_left caller d (List.replicate n nodeTag ++ raw)
          (List.replicate n Branch.left ++ p) { saved := f } regs ctx)
      have tail := ih (nodeTag :: f) (reset regs)
      simpa only [List.replicate_succ, List.cons_append, List.reverse_cons,
        List.append_assoc, List.singleton_append, List.nil_append, Nat.succ_ne_zero, ite_false,
        reset_reset, ite_self, Nat.add_comm 1 n] using LocalRun.trans caller first tail

/-- The failed head is consumed, while every remaining overlong path cell survives. -/
theorem left_path_overrun (d : RotationDirection) (n k : Nat) (positive : 0 < k)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (2 * n + 3)
      (cfg (some (phaseLabel (.seek d))) regs
        { source := List.replicate n nodeTag,
          path := List.replicate (n + k) Branch.left } ctx)
      (cfg (some (resultLabel .failure)) (reset regs)
        { source := List.replicate n nodeTag,
          path := List.replicate (k - 1) Branch.left } ctx) := by
  cases k with
  | zero => omega
  | succ k =>
      let midRegs := if n = 0 then regs else reset regs
      let stopped : LocalData :=
        { saved := List.replicate n nodeTag, path := List.replicate k Branch.left }
      have navigate : LocalRun caller n
          (cfg (some (phaseLabel (.seek d))) regs
            { source := List.replicate n nodeTag,
              path := List.replicate (n + (k + 1)) Branch.left } ctx)
          (cfg (some (phaseLabel (.seek d))) midRegs
            { stopped with path := Branch.left :: List.replicate k Branch.left } ctx) := by
        simpa [midRegs, stopped, List.replicate_add, List.replicate_succ] using
          seek_left_nodes_localRun caller d n []
            (Branch.left :: List.replicate k Branch.left) [] regs ctx
      have failed := phase_step_localRun caller
        (seek_step_source_nil caller d .left (List.replicate k Branch.left) stopped midRegs ctx)
      have cleanup := dropPending_localRun caller stopped (reset midRegs) ctx
      have joined := LocalRun.trans caller navigate (LocalRun.trans caller failed cleanup)
      simpa [midRegs, stopped, dropPendingData, apply_ite, reset_reset,
        List.replicate_add, List.replicate_succ, two_mul,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using joined

/-- Exhausting the path first takes the distinct paid empty-root route. -/
theorem left_path_exhausted (d : RotationDirection) (n : Nat)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (2 * n + 4)
      (cfg (some (phaseLabel (.seek d))) regs
        { source := List.replicate n nodeTag, path := List.replicate n Branch.left } ctx)
      (cfg (some (resultLabel .failure)) (reset regs)
        { source := List.replicate n nodeTag } ctx) := by
  let midRegs := if n = 0 then regs else reset regs
  have navigate : LocalRun caller n
      (cfg (some (phaseLabel (.seek d))) regs
        { source := List.replicate n nodeTag, path := List.replicate n Branch.left } ctx)
      (cfg (some (phaseLabel (.seek d))) midRegs { saved := List.replicate n nodeTag } ctx) := by
    simpa [midRegs] using seek_left_nodes_localRun caller d n [] [] [] regs ctx
  have root := root_nonnode_localRun caller d [] (List.replicate n nodeTag)
    True.intro midRegs ctx
  simpa [midRegs, apply_ite, reset_reset, two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    LocalRun.trans caller navigate root

theorem left_nodes_exact_clock (caller : External Λ → Statement Γ Λ R) (n : Nat) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    runSteps .left (List.replicate n nodeTag) [] = 3 * n + 4 := by
  simpa only [remainingSteps, cfg, phaseLabel, resultLabel, dataOfCfg, Nat.add_zero, runSteps] using
    LocalRun.remaining caller (left_nodes_run caller n regs ctx)

theorem right_nodes_exact_clock (caller : External Λ → Statement Γ Λ R) (m : Nat) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    runSteps .right (List.replicate (m + 2) nodeTag) [] = 3 * m + 7 := by
  simpa only [remainingSteps, cfg, phaseLabel, resultLabel, dataOfCfg, Nat.add_zero, runSteps] using
    LocalRun.remaining caller (right_nodes_run caller m regs ctx)

theorem left_nodes_drop_rank (caller : External Λ → Statement Γ Λ R) (n : Nat) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    remainingSteps (cfg (some (phaseLabel .dropPending)) regs
      { source := List.replicate n nodeTag, pending := List.replicate n () } ctx : Cfg Γ Λ R) = n + 2 := by
  simpa only [remainingSteps, cfg, phaseLabel, resultLabel, dataOfCfg, Nat.add_zero,
    List.length_replicate, List.length_nil] using
    LocalRun.remaining caller (dropPending_localRun caller
      { source := List.replicate n nodeTag, pending := List.replicate n () } regs ctx)

theorem right_nodes_drop_rank (caller : External Λ → Statement Γ Λ R) (m : Nat) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    remainingSteps (cfg (some (phaseLabel .dropPending)) regs
      { source := List.replicate (m + 2) nodeTag,
        pending := List.replicate (m + 1) () } ctx : Cfg Γ Λ R) = m + 3 := by
  have exact := LocalRun.remaining caller (dropPending_localRun caller
    { source := List.replicate (m + 2) nodeTag,
      pending := List.replicate (m + 1) () } regs ctx)
  simpa only [remainingSteps, cfg, phaseLabel, resultLabel, dataOfCfg, Nat.add_zero,
    List.length_replicate, List.length_nil, Nat.add_assoc] using exact

variable [Fintype K]

omit [DecidableEq K] in
theorem left_nodes_drop_cells (n : Nat) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    stackCells (cfg (some (phaseLabel .dropPending)) regs
      { source := List.replicate n nodeTag, pending := List.replicate n () } ctx : Cfg Γ Λ R) =
        2 * n + contextCells ctx := by
  rw [stackCells_cfg]
  simp [localCells, two_mul]

omit [DecidableEq K] in
theorem right_nodes_drop_cells (m : Nat) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    stackCells (cfg (some (phaseLabel .dropPending)) regs
      { source := List.replicate (m + 2) nodeTag,
        pending := List.replicate (m + 1) () } ctx : Cfg Γ Λ R) =
        2 * m + 3 + contextCells ctx := by
  rw [stackCells_cfg]
  simp [localCells]
  omega

end MalformedFamilies



end Resources.RotationCertificate.PositionedRotationMachine
