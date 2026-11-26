import Applications.Resources.RotationCertificate.StreamMachine.Basic

/-!
# StreamMachine: Execution
-/

set_option autoImplicit false
set_option warningAsError true
namespace Resources.RotationCertificate.StreamMachine
open Search.SharedTree (Branch)
open Trees.Rotations (RotationDirection RotationMove)
open Resources.BinaryCounter (Bits)
variable {K Λ R : Type} {Γ : K → Type}
variable [DecidableEq K]
variable (caller : External Λ → Statement Γ Λ R)

/-! ## Canonical actual owned runs, before the global rank law -/

theorem equality_complete_localRun (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (evaluateEquality D).steps
      (cfg (some (phaseLabel comparePhase)) regs D ctx)
      (evaluationCfg regs (evaluateEquality D) ctx) := by
  have first := equality_phase_localRun caller D regs ctx
  have last := equality_join_localRun caller (equalityFinish D).result (equalityFinish D).data
    (resetEquality regs) ctx
  simpa only [evaluateEquality, evaluationCfg, equalityJoinTarget, resetAll_resetEquality] using
    LocalRun.trans caller first last

theorem fuel_atEnd_complete_localRun (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (evaluateFuelJoin .atEnd D).steps
      (cfg (some (phaseLabel (fuelJoinPhase .atEnd))) regs D ctx)
      (evaluationCfg regs (evaluateFuelJoin .atEnd D) ctx) := by
  have first := fuel_join_localRun caller .atEnd D regs ctx
  have last := equality_complete_localRun caller D (resetAll regs) ctx
  simpa only [evaluateFuelJoin, addSteps, evaluationCfg, resetAll_resetAll] using
    LocalRun.trans caller first last

/-- The continuation premise is required only for an actual successful endpoint.
It retains the complete dirty output rather than assuming cleanup or consumption. -/
theorem apply_complete_localRun_of_success (q : MoveApplyMachine.Phase) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (continued : (applyFinish q D).result = MoveApplyMachine.success →
      LocalRun caller (evaluateInspect (applyFinish q D).data).steps
        (cfg (some (phaseLabel inspectPhase)) (resetAll regs) (applyFinish q D).data ctx)
        (evaluationCfg regs (evaluateInspect (applyFinish q D).data) ctx)) :
    LocalRun caller (evaluateApply q D).steps
      (cfg (some (phaseLabel (applyPhase q))) regs D ctx)
      (evaluationCfg regs (evaluateApply q D) ctx) := by
  have first := apply_phase_localRun caller q D regs ctx
  cases returned : (applyFinish q D).result with
  | inl u =>
      rw [returned] at first
      have last := apply_join_localRun caller (.inl u) (applyFinish q D).data (resetApply regs) ctx
      simpa only [evaluateApply, returned, evaluateApplyJoin, addSteps, evaluationCfg,
        applyJoinTarget, resetAll_resetApply] using LocalRun.trans caller first last
  | inr r => cases r with
    | failure =>
        rw [returned] at first
        have last := apply_join_localRun caller (.inr .failure) (applyFinish q D).data (resetApply regs) ctx
        simpa only [evaluateApply, returned, evaluateApplyJoin, addSteps, evaluationCfg,
          applyJoinTarget, resetAll_resetApply] using LocalRun.trans caller first last
    | success =>
        rw [returned] at first
        have joined := apply_join_localRun caller MoveApplyMachine.success (applyFinish q D).data (resetApply regs) ctx
        simp only [applyJoinTarget, MoveApplyMachine.success, resetAll_resetApply] at joined
        have last := continued returned
        have complete := LocalRun.trans caller (LocalRun.trans caller first joined) last
        simpa only [evaluateApply, returned, evaluateApplyJoin, addSteps,
          evaluationCfg, Nat.add_assoc] using complete

/-- Well-founded actual execution through the first live Boolean result. The
recursive hypothesis is invoked only on the exact shorter full-MoveApplyMachine.start suffix. -/
theorem inspect_localRun (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (evaluateInspect D).steps
      (cfg (some (phaseLabel inspectPhase)) regs D ctx)
      (evaluationCfg regs (evaluateInspect D) ctx) := by
  revert regs
  refine (measure (fun D : LocalData => D.certificate.length)).wf.induction
    (C := fun D : LocalData => ∀ regs : Registers R,
      LocalRun caller (evaluateInspect D).steps
        (cfg (some (phaseLabel inspectPhase)) regs D ctx)
        (evaluationCfg regs (evaluateInspect D) ctx)) D ?_
  intro D ih regs
  by_cases empty : D.certificate = []
  · rw [evaluateInspect_nil D empty]
    have first := phase_step_localRun caller (inspect_step_nil caller D empty regs ctx)
    have last := fuel_atEnd_complete_localRun caller D (resetFuel regs) ctx
    have complete := LocalRun.trans caller first last
    have clock : 1 + (evaluateFuelJoin .atEnd D).steps = (addSteps 2 (evaluateEquality D)).steps := by
      simp only [evaluateFuelJoin, addSteps]
      omega
    rw [clock] at complete
    simpa only [evaluateFuelJoin, evaluationCfg, resetAll_resetFuel, addSteps] using complete
  · rw [evaluateInspect_nonempty D empty]
    have stage := inspect_stage_localRun caller D regs ctx
    have certificate : ∃ tag raw, D.certificate = tag :: raw := List.exists_cons_of_ne_nil empty
    obtain ⟨tag, raw, certificate⟩ := certificate
    simp only [inspectStageFinish, certificate] at stage
    cases fuel : (counterFinish .borrow D).result with
    | zero =>
        simp only [fuel, FuelDispatchMachine.exitOfResult] at stage
        have last := fuel_join_localRun caller .zero (counterFinish .borrow D).data (resetFuel regs) ctx
        simpa only [evaluateCounter, fuel, FuelDispatchMachine.exitOfResult, evaluateFuelJoin, addSteps,
          evaluationCfg, fuelJoinTarget, resetAll_resetFuel, Nat.add_assoc] using
          LocalRun.trans caller stage last
    | positive =>
        simp only [fuel, FuelDispatchMachine.exitOfResult] at stage
        have joined := fuel_join_localRun caller .positive (counterFinish .borrow D).data (resetFuel regs) ctx
        simp only [fuelJoinTarget, resetAll_resetFuel] at joined
        have applied := apply_complete_localRun_of_success caller (MoveApplyMachine.movePhase .start)
          (counterFinish .borrow D).data (resetAll regs) ctx (by
            intro returned
            have decrease := apply_start_certificate_lt (counterFinish .borrow D).data returned
            have lower :
                (applyFinish (MoveApplyMachine.movePhase .start) (counterFinish .borrow D).data).data.certificate.length <
                  D.certificate.length := by simpa only [counterFinish_certificate] using decrease
            simpa only [evaluationCfg, resetAll_resetAll] using
              ih (applyFinish (MoveApplyMachine.movePhase .start) (counterFinish .borrow D).data).data lower (resetAll regs))
        have complete := LocalRun.trans caller (LocalRun.trans caller stage joined) applied
        simpa only [evaluateCounter, fuel, FuelDispatchMachine.exitOfResult, evaluateFuelJoin, addSteps,
          evaluationCfg, resetAll_resetAll, Nat.add_assoc] using complete

theorem apply_complete_localRun (q : MoveApplyMachine.Phase) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (evaluateApply q D).steps
      (cfg (some (phaseLabel (applyPhase q))) regs D ctx)
      (evaluationCfg regs (evaluateApply q D) ctx) := by
  apply apply_complete_localRun_of_success caller q D regs ctx
  intro _
  simpa only [evaluationCfg, resetAll_resetAll] using inspect_localRun caller (applyFinish q D).data (resetAll regs) ctx

theorem apply_join_complete_localRun (r : MoveApplyMachine.FinalResult) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (evaluateApplyJoin r D).steps
      (cfg (some (phaseLabel (applyJoinPhase r))) regs D ctx)
      (evaluationCfg regs (evaluateApplyJoin r D) ctx) := by
  cases r with
  | inl u => exact apply_join_localRun caller (.inl u) D regs ctx
  | inr r => cases r with
    | failure => exact apply_join_localRun caller (.inr .failure) D regs ctx
    | success =>
        have first := apply_join_localRun caller MoveApplyMachine.success D regs ctx
        have last := inspect_localRun caller D (resetAll regs) ctx
        simpa only [MoveApplyMachine.success, evaluateApplyJoin, addSteps, evaluationCfg,
          resetAll_resetAll] using LocalRun.trans caller first last

theorem fuel_join_complete_localRun (r : FuelDispatchMachine.Exit) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (evaluateFuelJoin r D).steps
      (cfg (some (phaseLabel (fuelJoinPhase r))) regs D ctx)
      (evaluationCfg regs (evaluateFuelJoin r D) ctx) := by
  cases r with
  | atEnd => exact fuel_atEnd_complete_localRun caller D regs ctx
  | zero => exact fuel_join_localRun caller .zero D regs ctx
  | positive =>
      have first := fuel_join_localRun caller .positive D regs ctx
      have last := apply_complete_localRun caller (MoveApplyMachine.movePhase .start) D (resetAll regs) ctx
      simpa only [evaluateFuelJoin, addSteps, evaluationCfg, resetAll_resetAll] using
        LocalRun.trans caller first last

theorem counter_complete_localRun (q : Resources.BinaryCounter.FixedWidthMachine.Phase) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (evaluateCounter q D).steps
      (cfg (some (phaseLabel (counterPhase q))) regs D ctx)
      (evaluationCfg regs (evaluateCounter q D) ctx) := by
  have first := counter_phase_localRun caller q D regs ctx
  have last := fuel_join_complete_localRun caller (FuelDispatchMachine.exitOfResult (counterFinish q D).result)
    (counterFinish q D).data (resetFuel regs) ctx
  simpa only [evaluateCounter, addSteps, evaluationCfg, resetAll_resetFuel] using
    LocalRun.trans caller first last

/-- Canonical complete execution for every one of the 39 owned phases. -/
theorem phase_localRun (q : Phase) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (phaseSteps q D)
      (cfg (some (phaseLabel q)) regs D ctx) (phaseResult q regs D ctx) := by
  rcases q with fuel | (applied | equality)
  · rcases fuel with q | (r | (d | impossible))
    · exact counter_complete_localRun caller q D regs ctx
    · cases r with
      | positive => exact fuel_join_complete_localRun caller .positive D regs ctx
      | zero => exact fuel_join_complete_localRun caller .zero D regs ctx
    · cases d with
      | inspectCertificate => exact inspect_localRun caller D regs ctx
      | atEnd => exact fuel_join_complete_localRun caller .atEnd D regs ctx
    · exact Empty.elim impossible
  · rcases applied with q | (r | (q | (r | impossible)))
    · exact apply_complete_localRun caller (MoveApplyMachine.movePhase q) D regs ctx
    · exact apply_complete_localRun caller (MoveApplyMachine.dispatchPhase r) D regs ctx
    · exact apply_complete_localRun caller (MoveApplyMachine.positionPhase q) D regs ctx
    · exact apply_join_complete_localRun caller r D regs ctx
    · exact Empty.elim impossible
  · rcases equality with q | (r | impossible)
    · cases q; exact equality_complete_localRun caller D regs ctx
    · exact equality_join_localRun caller r D regs ctx
    · exact Empty.elim impossible

theorem phase_iterate (q : Phase) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    (next caller)^[phaseSteps q D] (some (cfg (some (phaseLabel q)) regs D ctx)) =
      some (phaseResult q regs D ctx) := (phase_localRun caller q D regs ctx).iterate caller

omit [DecidableEq K] in
theorem phaseResult_not_owned (q : Phase) (regs : Registers R) (D : LocalData)
    (ctx : ∀ k, List (Γ k)) : ¬ Owned (phaseResult (Λ := Λ) q regs D ctx).l :=
  not_owned_result (evaluate q D).result

theorem phase_first_return (q : Phase) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    (next caller)^[phaseSteps q D] (some (cfg (some (phaseLabel q)) regs D ctx)) =
      some (phaseResult q regs D ctx) ∧
    ¬ Owned (phaseResult (Λ := Λ) q regs D ctx).l ∧
    ∀ n, n < phaseSteps q D → ∃ reached,
      (next caller)^[n] (some (cfg (some (phaseLabel q)) regs D ctx)) = some reached ∧ Owned reached.l :=
  ⟨phase_iterate caller q D regs ctx, phaseResult_not_owned q regs D ctx,
    (phase_localRun caller q D regs ctx).owned_prefix caller⟩

theorem first_return_unique (q : Phase) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (n : Nat) (reached : Cfg Γ Λ R)
    (executed : (next caller)^[n] (some (cfg (some (phaseLabel q)) regs D ctx)) = some reached)
    (nonowned : ¬ Owned reached.l)
    (earlier : ∀ j, j < n → ∃ middle,
      (next caller)^[j] (some (cfg (some (phaseLabel q)) regs D ctx)) = some middle ∧ Owned middle.l) :
    n = phaseSteps q D ∧ reached = phaseResult q regs D ctx :=
  LocalRun.first_unique caller (LocalRun.of_iterate caller executed earlier)
    (phase_localRun caller q D regs ctx) nonowned (phaseResult_not_owned q regs D ctx)


omit [DecidableEq K] in
theorem phaseSteps_pos (q : Phase) (D : LocalData) : 0 < phaseSteps q D := by
  let localCaller : External Empty → Statement (fun _ : Empty => Empty) Empty Unit := fun _ => .halt
  let regs : Registers Unit := (none, ((none, (none, none)), ()))
  have executed := phase_iterate localCaller q D regs (fun k : Empty => Empty.elim k)
  have nonowned := phaseResult_not_owned (Γ := fun _ : Empty => Empty) (Λ := Empty)
    q regs D (fun k => Empty.elim k)
  by_contra failure
  have zero : phaseSteps q D = 0 := by omega
  rw [zero] at executed
  have same : cfg (some (phaseLabel q)) regs D (fun k : Empty => Empty.elim k) =
      phaseResult (Γ := fun _ : Empty => Empty) (Λ := Empty) q regs D (fun k => Empty.elim k) :=
    Option.some.inj executed
  apply nonowned
  rw [← same]
  exact owned_phase q

omit [DecidableEq K] in
def remainingSteps (c : Cfg Γ Λ R) : Nat :=
  match c.l with
  | some (.inl q) => phaseSteps (.inl q) (dataOfCfg c)
  | some (.inr (.inl q)) => phaseSteps (.inr (.inl q)) (dataOfCfg c)
  | some (.inr (.inr (.inl q))) => phaseSteps (.inr (.inr q)) (dataOfCfg c)
  | _ => 0

omit [DecidableEq K] in
def finalCfg (c : Cfg Γ Λ R) : Cfg Γ Λ R :=
  match c.l with
  | some (.inl q) => phaseResult (.inl q) c.var (dataOfCfg c) (contextOfCfg c)
  | some (.inr (.inl q)) => phaseResult (.inr (.inl q)) c.var (dataOfCfg c) (contextOfCfg c)
  | some (.inr (.inr (.inl q))) => phaseResult (.inr (.inr q)) c.var (dataOfCfg c) (contextOfCfg c)
  | _ => c

omit [DecidableEq K] in
def stateRemainingSteps : Option (Cfg Γ Λ R) → Nat
  | none => 0
  | some c => remainingSteps c

omit [DecidableEq K] in
@[simp] theorem stateRemainingSteps_none : stateRemainingSteps (Γ := Γ) (Λ := Λ) (R := R) none = 0 := rfl

omit [DecidableEq K] in
@[simp] theorem stateRemainingSteps_some (c : Cfg Γ Λ R) :
    stateRemainingSteps (some c) = remainingSteps c := rfl

omit [DecidableEq K] in
theorem remainingSteps_phase_cfg (q : Phase) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    remainingSteps (cfg (some (phaseLabel (Λ := Λ) q)) regs D ctx) = phaseSteps q D := by
  cases q with
  | inl q => rfl
  | inr q => cases q <;> rfl

omit [DecidableEq K] in
theorem finalCfg_phase_cfg (q : Phase) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    finalCfg (cfg (some (phaseLabel (Λ := Λ) q)) regs D ctx) = phaseResult q regs D ctx := by
  cases q with
  | inl q => rfl
  | inr q => cases q <;> rfl

omit [DecidableEq K] in
theorem remainingSteps_pos_iff (c : Cfg Γ Λ R) : 0 < remainingSteps c ↔ Owned c.l := by
  cases labelEq : c.l with
  | none => simp only [remainingSteps, Owned, labelEq, Nat.lt_irrefl]
  | some label =>
      rcases label with f | (h | (e | external))
      · simp only [remainingSteps, Owned, labelEq, phaseSteps_pos]
      · simp only [remainingSteps, Owned, labelEq, phaseSteps_pos]
      · simp only [remainingSteps, Owned, labelEq, phaseSteps_pos]
      · simp only [remainingSteps, Owned, labelEq, Nat.lt_irrefl]

omit [DecidableEq K] in
theorem owned_cases (c : Cfg Γ Λ R) (owned : Owned c.l) :
    ∃ q regs D ctx, c = cfg (some (phaseLabel q)) regs D ctx := by
  cases labelEq : c.l with
  | none => simp only [labelEq, Owned] at owned
  | some label =>
      rcases label with f | (h | (e | external))
      · refine ⟨.inl f, c.var, dataOfCfg c, contextOfCfg c, ?_⟩
        simpa only [labelEq, phaseLabel] using (cfg_eta c).symm
      · refine ⟨.inr (.inl h), c.var, dataOfCfg c, contextOfCfg c, ?_⟩
        simpa only [labelEq, phaseLabel] using (cfg_eta c).symm
      · refine ⟨.inr (.inr e), c.var, dataOfCfg c, contextOfCfg c, ?_⟩
        simpa only [labelEq, phaseLabel] using (cfg_eta c).symm
      · simp only [labelEq, Owned] at owned
omit [DecidableEq K] in
theorem nonowned_remaining (c : Cfg Γ Λ R) (returned : ¬ Owned c.l) : remainingSteps c = 0 := by
  have notPositive : ¬ 0 < remainingSteps c := fun h => returned ((remainingSteps_pos_iff c).mp h)
  omega

omit [DecidableEq K] in
theorem nonowned_finalCfg (c : Cfg Γ Λ R) (returned : ¬ Owned c.l) : finalCfg c = c := by
  cases labelEq : c.l with
  | none => simp only [finalCfg, labelEq]
  | some label =>
      rcases label with q | (r | (q | external))
      · exact False.elim (returned (by simp only [labelEq, Owned]))
      · exact False.elim (returned (by simp only [labelEq, Owned]))
      · exact False.elim (returned (by simp only [labelEq, Owned]))
      · simp only [finalCfg, labelEq]

theorem cfg_localRun (c : Cfg Γ Λ R) : LocalRun caller (remainingSteps c) c (finalCfg c) := by
  by_cases owned : Owned c.l
  · obtain ⟨q, regs, D, ctx, rfl⟩ := owned_cases c owned
    rw [remainingSteps_phase_cfg, finalCfg_phase_cfg]
    exact phase_localRun caller q D regs ctx
  · rw [nonowned_remaining c owned, nonowned_finalCfg c owned]
    exact .refl c

omit [DecidableEq K] in
theorem finalCfg_not_owned (c : Cfg Γ Λ R) : ¬ Owned (finalCfg c).l := by
  by_cases owned : Owned c.l
  · obtain ⟨q, regs, D, ctx, rfl⟩ := owned_cases c owned
    rw [finalCfg_phase_cfg]
    exact phaseResult_not_owned q regs D ctx
  · rw [nonowned_finalCfg c owned]
    exact owned

theorem cfg_iterate (c : Cfg Γ Λ R) :
    (next caller)^[remainingSteps c] (some c) = some (finalCfg c) :=
  LocalRun.iterate caller (cfg_localRun caller c)

theorem local_step_remaining {before after : Cfg Γ Λ R}
    (transition : LocalStep caller before after) :
    remainingSteps before = remainingSteps after + 1 := by
  have composed := LocalRun.cons transition (cfg_localRun caller after)
  exact (LocalRun.first_unique caller (cfg_localRun caller before) composed
    (finalCfg_not_owned before) (finalCfg_not_owned after)).1

theorem finalCfg_step {before after : Cfg Γ Λ R} (transition : LocalStep caller before after) :
    finalCfg before = finalCfg after := by
  exact (LocalRun.first_unique caller (cfg_localRun caller before)
    (LocalRun.cons transition (cfg_localRun caller after))
    (finalCfg_not_owned before) (finalCfg_not_owned after)).2

theorem local_progress (before : Cfg Γ Λ R) (positive : 0 < remainingSteps before) :
    ∃ after, step caller before = some after ∧ remainingSteps before = remainingSteps after + 1 := by
  obtain ⟨after, transition⟩ := LocalRun.head caller (cfg_localRun caller before) positive
  exact ⟨after, transition.2, local_step_remaining caller transition⟩

theorem LocalRun.remaining {n : Nat} {a b : Cfg Γ Λ R} (run : LocalRun caller n a b) :
    remainingSteps a = n + remainingSteps b := by
  induction run with
  | refl => omega
  | cons head tail ih => have first := local_step_remaining caller head; omega

theorem LocalRun.finalCfg_eq {n : Nat} {a b : Cfg Γ Λ R} (run : LocalRun caller n a b) :
    finalCfg a = finalCfg b := by
  induction run with
  | refl => rfl
  | cons head tail ih => exact (finalCfg_step caller head).trans ih

theorem LocalRun.phase_endpoint {q : Phase} {D E : LocalData} {regs outRegs : Registers R}
    {ctx outCtx : ∀ k, List (Γ k)} {n : Nat} {r : Bool}
    (run : LocalRun caller n (cfg (some (phaseLabel q)) regs D ctx)
      (cfg (some (resultLabel r)) outRegs E outCtx)) :
    phaseSteps q D = n ∧
      phaseResult (Λ := Λ) q regs D ctx = cfg (some (resultLabel r)) outRegs E outCtx := by
  exact LocalRun.first_unique caller (phase_localRun caller q D regs ctx) run
    (phaseResult_not_owned q regs D ctx) (not_owned_result r)

theorem owned_prefix (start : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start) :
    ∃ reached, (next caller)^[n] (some start) = some reached ∧
      remainingSteps reached = remainingSteps start - n ∧
      Relation.ReflTransGen (LocalStep caller) start reached ∧
      (n < remainingSteps start ↔ Owned reached.l) := by
  obtain ⟨reached, executed, rank, path⟩ := Resources.BinaryCounter.FixedWidthMachine.ranked_prefix
    (step caller) remainingSteps (local_progress caller) n start bound
  refine ⟨reached, executed, rank, ?_, ?_⟩
  · exact Relation.ReflTransGen.mono
      (fun before _ h => ⟨(remainingSteps_pos_iff before).mp h.1, h.2⟩) _ _ path
  · rw [← remainingSteps_pos_iff, rank]
    omega

omit [DecidableEq K] in
theorem program_phase_independent (other : External Λ → Statement Γ Λ R) (q : Phase) :
    program caller (phaseLabel q) = program other (phaseLabel q) := by
  rcases q with fuel | (applied | equality)
  · rcases fuel with q | (r | (d | impossible))
    · rfl
    · rfl
    · cases d <;> rfl
    · exact Empty.elim impossible
  · rcases applied with q | (r | (q | (r | impossible)))
    · rfl
    · rfl
    · rfl
    · rfl
    · exact Empty.elim impossible
  · rcases equality with q | (r | impossible)
    · cases q; rfl
    · rfl
    · exact Empty.elim impossible

theorem step_caller_independent (other : External Λ → Statement Γ Λ R)
    (c : Cfg Γ Λ R) (owned : Owned c.l) : step caller c = step other c := by
  obtain ⟨q, regs, D, ctx, rfl⟩ := owned_cases c owned
  change some (Turing.TM2.stepAux (program caller (phaseLabel q)) regs
      (cfg (Λ := Λ) (some (phaseLabel q)) regs D ctx).stk) =
    some (Turing.TM2.stepAux (program other (phaseLabel q)) regs
      (cfg (Λ := Λ) (some (phaseLabel q)) regs D ctx).stk)
  rw [program_phase_independent caller other q]

theorem prefix_caller_independent (other : External Λ → Statement Γ Λ R)
    (start : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start) :
    (next caller)^[n] (some start) = (next other)^[n] (some start) :=
  Resources.BinaryCounter.FixedWidthMachine.ranked_prefix_eq
    (step caller) (step other) remainingSteps (local_progress caller)
    (fun c positive => step_caller_independent caller other c ((remainingSteps_pos_iff c).mp positive))
    n start bound

omit [DecidableEq K] in
theorem program_eq_of_agrees (ambient : Label Λ → Statement Γ Λ R)
    (agrees : ∀ q, ambient (phaseLabel q) = program (fun _ => .halt) (phaseLabel q)) :
    ambient = program (fun external => ambient (.inr (.inr (.inr external)))) := by
  funext label
  rcases label with q | (r | (q | external))
  · exact (agrees (.inl q)).trans
      (program_phase_independent (fun _ => .halt) _ (.inl q))
  · exact (agrees (.inr (.inl r))).trans
      (program_phase_independent (fun _ => .halt) _ (.inr (.inl r)))
  · exact (agrees (.inr (.inr q))).trans
      (program_phase_independent (fun _ => .halt) _ (.inr (.inr q)))
  · rfl

theorem ambient_prefix_eq (ambient : Label Λ → Statement Γ Λ R)
    (agrees : ∀ q, ambient (phaseLabel q) = program (fun _ => .halt) (phaseLabel q))
    (start : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start) :
    (fun c : Option (Cfg Γ Λ R) => c.bind (Turing.TM2.step ambient))^[n] (some start) =
      (next caller)^[n] (some start) := by
  rw [program_eq_of_agrees ambient agrees]
  exact prefix_caller_independent _ caller start n bound

theorem first_return_exact (start : Cfg Γ Λ R) (n : Nat) (reached : Cfg Γ Λ R)
    (bound : n ≤ remainingSteps start)
    (executed : (next caller)^[n] (some start) = some reached)
    (returned : ¬ Owned reached.l) : n = remainingSteps start := by
  obtain ⟨actual, run, rank, path, ownership⟩ := owned_prefix caller start n bound
  have same : actual = reached := Option.some.inj (run.symm.trans executed)
  subst actual
  have notStrict : ¬ n < remainingSteps start := fun h => returned (ownership.mp h)
  omega

theorem iterate_trans {start middle finish : Cfg Γ Λ R} {first second : Nat}
    (before : (next caller)^[first] (some start) = some middle)
    (after : (next caller)^[second] (some middle) = some finish) :
    (next caller)^[first + second] (some start) = some finish := by
  rw [Nat.add_comm first second, Function.iterate_add_apply, before, after]


def FirstRun (start : Cfg Γ Λ R) (n : Nat) (finish : Cfg Γ Λ R) : Prop :=
  (next caller)^[n] (some start) = some finish ∧ ¬ Owned finish.l ∧
    ∀ j, j < n → ∃ reached,
      (next caller)^[j] (some start) = some reached ∧ Owned reached.l

def FirstResult (start : Cfg Γ Λ R) (b : Bool) : Prop :=
  ∃ n finish, FirstRun caller start n finish ∧ finish.l = some (resultLabel b)

theorem cfg_firstRun (start : Cfg Γ Λ R) :
    FirstRun caller start (remainingSteps start) (finalCfg start) :=
  ⟨cfg_iterate caller start, finalCfg_not_owned start,
    (cfg_localRun caller start).owned_prefix caller⟩

theorem firstRun_iff (start finish : Cfg Γ Λ R) (n : Nat) :
    FirstRun caller start n finish ↔ n = remainingSteps start ∧ finish = finalCfg start := by
  constructor
  · rintro ⟨executed, nonowned, earlier⟩
    exact LocalRun.first_unique caller (LocalRun.of_iterate caller executed earlier)
      (cfg_localRun caller start) nonowned (finalCfg_not_owned start)
  · rintro ⟨rfl, rfl⟩
    exact cfg_firstRun caller start

theorem firstResult_iff_finalCfg (start : Cfg Γ Λ R) (b : Bool) :
    FirstResult caller start b ↔ (finalCfg start).l = some (resultLabel b) := by
  constructor
  · rintro ⟨n, finish, first, label⟩
    rcases (firstRun_iff caller start finish n).mp first with ⟨_, rfl⟩
    exact label
  · intro label
    exact ⟨remainingSteps start, finalCfg start, cfg_firstRun caller start, label⟩

theorem phase_firstResult_iff (q : Phase) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (b : Bool) :
    FirstResult caller (cfg (some (phaseLabel q)) regs D ctx) b ↔ (evaluate q D).result = b := by
  rw [firstResult_iff_finalCfg, finalCfg_phase_cfg]
  change some (resultLabel (evaluate q D).result) = some (resultLabel b) ↔ _
  simp only [resultLabel, Option.some.injEq, Sum.inr.injEq, Sum.inl.injEq]

theorem nonowned_firstResult_iff (start : Cfg Γ Λ R) (nonowned : ¬ Owned start.l) (b : Bool) :
    FirstResult caller start b ↔ start.l = some (resultLabel b) := by
  rw [firstResult_iff_finalCfg, nonowned_finalCfg start nonowned]

theorem phase_firstRun (q : Phase) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    FirstRun caller (cfg (some (phaseLabel q)) regs D ctx) (phaseSteps q D) (phaseResult q regs D ctx) :=
  phase_first_return caller q D regs ctx


/-! ## Complete-data one-step bridges for independent connected clients -/

omit [DecidableEq K] in
theorem fuelCfg_partial (label : Option (FuelDispatchMachine.Label (FuelCallerLabel Λ)))
    (regs : Registers R) (D : LocalData) (fuel : Bits) (units : List Unit) (certificate : Word)
    (ctx : ∀ k, List (Γ k)) :
    fuelCfg (FuelDispatchMachine.cfg label regs fuel units certificate (fuelContext D ctx)) =
      cfg (label.map fuelLabelEquiv) regs
        { D with certificate := certificate, units := units, fuel := fuel } ctx := by
  change fuelCfg (fuelView label regs
    { D with certificate := certificate, units := units, fuel := fuel } ctx) = _
  exact fuelCfg_view label regs _ ctx

omit [DecidableEq K] in
theorem applyCfg_partial (label : Option (MoveApplyMachine.Label (ApplyCallerLabel Λ)))
    (regs : MoveApplyMachine.Registers (ApplyCallerRegister R)) (D : LocalData) (output : MoveApplyMachine.LocalData)
    (ctx : ∀ k, List (Γ k)) :
    applyCfg (MoveApplyMachine.cfg label regs output (applyContext D ctx)) =
      cfg (label.map applyLabelEquiv) (applyRegisterEquiv regs) (setApplyData D output) ctx := by
  change applyCfg (applyView label regs (setApplyData D output) ctx) = _
  exact applyCfg_view label regs _ ctx

omit [DecidableEq K] in
theorem equalityCfg_partial (label : Option (TreeEqualityMachine.Label (EqualityCallerLabel Λ)))
    (regs : TreeEqualityMachine.Registers (EqualityCallerRegister R)) (D : LocalData) (source target : Word)
    (ctx : ∀ k, List (Γ k)) :
    equalityCfg (TreeEqualityMachine.cfg label regs source target (equalityContext D ctx)) =
      cfg (label.map equalityLabelEquiv) (equalityRegisterEquiv regs)
        { D with source := source, target := target } ctx := by
  change equalityCfg (equalityView label regs { D with source := source, target := target } ctx) = _
  exact equalityCfg_view label regs _ ctx

theorem counter_step_of_step
    (localCaller : (FuelDispatchMachine.Exit ⊕ FuelCallerLabel Λ) → FuelStatement Γ Λ R)
    (q : Resources.BinaryCounter.FixedWidthMachine.Phase) (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (label : Option (FuelDispatchMachine.Label (FuelCallerLabel Λ))) (outRegs : Registers R)
    (fuel : Bits) (units : List Unit)
    (executed : FuelDispatchMachine.step localCaller (fuelView (some (Resources.BinaryCounter.FixedWidthMachine.phaseLabel q)) regs D ctx) =
      some (FuelDispatchMachine.cfg label outRegs fuel units D.certificate (fuelContext D ctx))) :
    step caller (cfg (some (phaseLabel (counterPhase q))) regs D ctx) =
      some (cfg (label.map fuelLabelEquiv) outRegs { D with fuel := fuel, units := units } ctx) := by
  have actual := fuel_step_transport caller localCaller
    (fuelView (some (Resources.BinaryCounter.FixedWidthMachine.phaseLabel q)) regs D ctx) (Or.inl True.intro)
  rw [fuelCfg_view, executed] at actual
  simp only [Option.map_some] at actual
  rw [fuelCfg_partial] at actual
  simpa only [Option.map_some, fuelLabelEquiv_counter, fuelRegisterEquiv, Equiv.refl_apply] using actual

theorem apply_step_of_step
    (localCaller : MoveApplyMachine.External (ApplyCallerLabel Λ) → ApplyStatement Γ Λ R)
    (q : MoveApplyMachine.Phase) (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (label : Option (MoveApplyMachine.Label (ApplyCallerLabel Λ)))
    (outRegs : MoveApplyMachine.Registers (ApplyCallerRegister R)) (output : MoveApplyMachine.LocalData)
    (executed : MoveApplyMachine.step localCaller
      (applyView (some (MoveApplyMachine.phaseLabel q)) (applyRegisterEquiv.symm regs) D ctx) =
      some (MoveApplyMachine.cfg label outRegs output (applyContext D ctx))) :
    step caller (cfg (some (phaseLabel (applyPhase q))) regs D ctx) =
      some (cfg (label.map applyLabelEquiv) (applyRegisterEquiv outRegs) (setApplyData D output) ctx) := by
  have actual := apply_step_transport caller localCaller
    (applyView (some (MoveApplyMachine.phaseLabel q)) (applyRegisterEquiv.symm regs) D ctx) (MoveApplyMachine.owned_phase q)
  rw [applyCfg_view, executed] at actual
  simp only [Option.map_some] at actual
  rw [applyCfg_partial] at actual
  simpa only [Option.map_some, applyLabelEquiv_phase, Equiv.apply_symm_apply] using actual

theorem equality_step_of_step
    (localCaller : TreeEqualityMachine.External (EqualityCallerLabel Λ) → EqualityStatement Γ Λ R)
    (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (label : Option (TreeEqualityMachine.Label (EqualityCallerLabel Λ)))
    (outRegs : TreeEqualityMachine.Registers (EqualityCallerRegister R)) (source target : Word)
    (executed : TreeEqualityMachine.step localCaller
      (equalityView (some (TreeEqualityMachine.phaseLabel .compare)) (equalityRegisterEquiv.symm regs) D ctx) =
      some (TreeEqualityMachine.cfg label outRegs source target (equalityContext D ctx))) :
    step caller (cfg (some (phaseLabel comparePhase)) regs D ctx) =
      some (cfg (label.map equalityLabelEquiv) (equalityRegisterEquiv outRegs)
        { D with source := source, target := target } ctx) := by
  have actual := equality_step_transport caller localCaller
    (equalityView (some (TreeEqualityMachine.phaseLabel .compare)) (equalityRegisterEquiv.symm regs) D ctx) True.intro
  rw [equalityCfg_view, executed] at actual
  simp only [Option.map_some] at actual
  rw [equalityCfg_partial] at actual
  simpa only [Option.map_some, equalityLabelEquiv_phase, Equiv.apply_symm_apply] using actual

theorem apply_position_advance_step (q : PositionedRotationMachine.Phase)
    (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel (applyPhase (MoveApplyMachine.positionPhase q)))) regs D ctx) =
      some (cfg
        (some (applyLabelEquiv (MoveApplyMachine.positionControlLabel
          (PositionedRotationMachine.advance q (MoveApplyMachine.positionData (applyData D))).1)))
        (resetApply regs)
        (setApplyData D (MoveApplyMachine.setPositionData (applyData D)
          (PositionedRotationMachine.advance q (MoveApplyMachine.positionData (applyData D))).2)) ctx) := by
  let localCaller : MoveApplyMachine.External (ApplyCallerLabel Λ) → ApplyStatement Γ Λ R := fun _ => .halt
  have actual := apply_step_of_step caller localCaller (MoveApplyMachine.positionPhase q) D regs ctx _ _ _
    (MoveApplyMachine.position_advance_step localCaller q (applyData D) (applyRegisterEquiv.symm regs) (applyContext D ctx))
  simpa only [Option.map_some, applyRegisterEquiv_reset, Equiv.apply_symm_apply] using actual


omit [DecidableEq K] in
@[simp] theorem apply_move_register_reset
    (regs : MoveParserMachine.Registers (MoveApplyMachine.MoveCallerRegister (ApplyCallerRegister R))) :
    applyRegisterEquiv (MoveApplyMachine.moveRegisterEquiv (MoveParserMachine.reset regs)) =
      resetMove (applyRegisterEquiv (MoveApplyMachine.moveRegisterEquiv regs)) := rfl

/-- A literal parser activation through both complete physical transports. -/
theorem apply_move_step_of_step
    (localCaller : MoveParserMachine.External (MoveApplyMachine.MoveCallerLabel (ApplyCallerLabel Λ)) →
      MoveApplyMachine.MoveStatement (ApplyProtectedAlphabet Γ) (ApplyCallerLabel Λ) (ApplyCallerRegister R))
    (q : MoveParserMachine.Phase) (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (label : Option (MoveParserMachine.Label (MoveApplyMachine.MoveCallerLabel (ApplyCallerLabel Λ))))
    (outRegs : MoveParserMachine.Registers (MoveApplyMachine.MoveCallerRegister (ApplyCallerRegister R)))
    (raw : Word) (rev path : List Branch)
    (executed : MoveParserMachine.step localCaller
      (MoveApplyMachine.moveView (some (MoveParserMachine.phaseLabel q))
        (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm regs))
        (applyData D) (applyContext D ctx)) =
      some (MoveParserMachine.cfg label outRegs raw rev path
        (MoveApplyMachine.moveContext (applyData D) (applyContext D ctx)))) :
    step caller (cfg (some (phaseLabel (applyPhase (MoveApplyMachine.movePhase q)))) regs D ctx) =
      some (cfg ((label.map MoveApplyMachine.moveLabelEquiv).map applyLabelEquiv)
        (applyRegisterEquiv (MoveApplyMachine.moveRegisterEquiv outRegs))
        { D with certificate := raw, moveReverse := rev, path := path } ctx) := by
  let hCaller : MoveApplyMachine.External (ApplyCallerLabel Λ) → ApplyStatement Γ Λ R := fun _ => .halt
  let output : MoveApplyMachine.LocalData :=
    { applyData D with certificate := raw, moveReverse := rev, path := path }
  have inner := MoveApplyMachine.move_step_transport hCaller localCaller
    (MoveApplyMachine.moveView (some (MoveParserMachine.phaseLabel q))
      (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm regs))
      (applyData D) (applyContext D ctx)) True.intro
  rw [MoveApplyMachine.moveCfg_view, executed] at inner
  simp only [Option.map_some] at inner
  have out : MoveApplyMachine.moveCfg
      (MoveParserMachine.cfg label outRegs raw rev path
        (MoveApplyMachine.moveContext (applyData D) (applyContext D ctx))) =
      MoveApplyMachine.cfg (label.map MoveApplyMachine.moveLabelEquiv)
        (MoveApplyMachine.moveRegisterEquiv outRegs) output (applyContext D ctx) := by
    change MoveApplyMachine.moveCfg (MoveApplyMachine.moveView label outRegs output (applyContext D ctx)) = _
    exact MoveApplyMachine.moveCfg_view label outRegs output (applyContext D ctx)
  rw [out] at inner
  have localStep : MoveApplyMachine.step hCaller
      (applyView (some (MoveApplyMachine.phaseLabel (MoveApplyMachine.movePhase q)))
        (applyRegisterEquiv.symm regs) D ctx) =
      some (MoveApplyMachine.cfg (label.map MoveApplyMachine.moveLabelEquiv)
        (MoveApplyMachine.moveRegisterEquiv outRegs) output (applyContext D ctx)) := by
    simpa only [MoveApplyMachine.moveLabelEquiv_phase, Equiv.apply_symm_apply, applyView,
      MoveApplyMachine.phaseLabel, MoveApplyMachine.movePhase, MoveApplyMachine.moveLabel] using inner
  have actual := apply_step_of_step caller hCaller (MoveApplyMachine.movePhase q) D regs ctx _ _ output localStep
  exact actual


/-! ## Arbitrary caller frame and the invariant after a paid full reset -/

omit [DecidableEq K] in
def FrameResult (before after : Cfg Γ Λ R) : Prop :=
  after.var.2.2 = before.var.2.2 ∧
    (∀ k, after.stk (.inr k) = before.stk (.inr k)) ∧
    (resetAll before.var = before.var → after.var = before.var)

omit [DecidableEq K] in
theorem fuelCfg_context (c : FuelCfg Γ Λ R) (k : K) :
    (fuelCfg c).stk (.inr k) = c.stk (.inr (.inr (.inr k))) := by
  change FrontEndMachine.Transport.stackEquiv fuelStackEquiv (fuelSymbolEquiv (Γ := Γ))
    c.stk (fuelStackEquiv (.inr (.inr (.inr k)))) = _
  rw [FrontEndMachine.Transport.stackEquiv_apply]
  change List.map id _ = _
  exact List.map_id _

omit [DecidableEq K] in
theorem applyCfg_context (c : ApplyCfg Γ Λ R) (k : K) :
    (applyCfg c).stk (.inr k) = c.stk (.inr (.inr k)) := by
  change FrontEndMachine.Transport.stackEquiv applyStackEquiv (applySymbolEquiv (Γ := Γ))
    c.stk (applyStackEquiv (.inr (.inr k))) = _
  rw [FrontEndMachine.Transport.stackEquiv_apply]
  change List.map id _ = _
  exact List.map_id _

omit [DecidableEq K] in
theorem equalityCfg_context (c : EqualityCfg Γ Λ R) (k : K) :
    (equalityCfg c).stk (.inr k) = c.stk (.inr (.inr k)) := by
  change FrontEndMachine.Transport.stackEquiv equalityStackEquiv (equalitySymbolEquiv (Γ := Γ))
    c.stk (equalityStackEquiv (.inr (.inr k))) = _
  rw [FrontEndMachine.Transport.stackEquiv_apply]
  change List.map id _ = _
  exact List.map_id _

/-- Fuel's register/frame law without imposing finiteness on the protected family. -/
theorem fuel_local_step_data
    (localCaller : (FuelDispatchMachine.Exit ⊕ FuelCallerLabel Λ) → FuelStatement Γ Λ R)
    {before after : FuelCfg Γ Λ R} (transition : FuelDispatchMachine.LocalStep localCaller before after) :
    after.var = Resources.BinaryCounter.FixedWidthMachine.reset before.var ∧
      ∀ k, after.stk (.inr k) = before.stk (.inr k) := by
  rcases transition with ⟨owned, executed⟩
  rcases owned with core | inspect
  · obtain ⟨_, bit, registers, _, frame⟩ :=
      Resources.BinaryCounter.FixedWidthMachine.local_step_data (FuelDispatchMachine.callerHandler localCaller) ⟨core, executed⟩
    refine ⟨?_, frame⟩
    apply Prod.ext
    · exact bit
    · exact registers
  · obtain ⟨regs, fuel, units, cert, ctx, rfl⟩ := FuelDispatchMachine.inspection_cases before inspect
    cases cert with
    | nil =>
        rw [FuelDispatchMachine.dispatch_step_nil] at executed
        cases Option.some.inj executed
        exact ⟨rfl, fun _ => rfl⟩
    | cons tag raw =>
        rw [FuelDispatchMachine.dispatch_step_cons] at executed
        cases Option.some.inj executed
        exact ⟨rfl, fun _ => rfl⟩

omit [DecidableEq K] in
theorem apply_registersAt_clean (c : ApplyCfg Γ Λ R) (n : Nat)
    (clean : MoveApplyMachine.reset c.var = c.var) : MoveApplyMachine.registersAt c n = c.var := by
  have parserClean : MoveApplyMachine.resetMove c.var = c.var := by rw [← clean]; rfl
  unfold MoveApplyMachine.registersAt
  split
  · rfl
  · split
    · simp only [clean, parserClean, ite_self]
    · exact clean

theorem fuel_step_frame
    (localCaller : (FuelDispatchMachine.Exit ⊕ FuelCallerLabel Λ) → FuelStatement Γ Λ R)
    (c : FuelCfg Γ Λ R) (owned : FuelDispatchMachine.Owned c.l) (after : Cfg Γ Λ R)
    (executed : step caller (fuelCfg c) = some after) : FrameResult (fuelCfg c) after := by
  obtain ⟨middle, moved, _⟩ := FuelDispatchMachine.local_progress localCaller c ((FuelDispatchMachine.remainingSteps_pos_iff c).mpr owned)
  have actual := fuel_step_transport caller localCaller c owned
  rw [moved, Option.map_some] at actual
  have same : after = fuelCfg middle := Option.some.inj (executed.symm.trans actual)
  subst after
  obtain ⟨registers, frame⟩ := fuel_local_step_data localCaller ⟨owned, moved⟩
  refine ⟨?_, ?_, ?_⟩
  · change middle.var.2.2 = c.var.2.2
    rw [registers]
    rfl
  · intro k
    rw [fuelCfg_context, fuelCfg_context]
    exact frame (.inr (.inr k))
  · intro clean
    change resetAll c.var = c.var at clean
    change middle.var = c.var
    rw [registers]
    change resetFuel c.var = c.var
    rw [← clean]
    rfl

theorem apply_step_frame
    (localCaller : MoveApplyMachine.External (ApplyCallerLabel Λ) → ApplyStatement Γ Λ R)
    (c : ApplyCfg Γ Λ R) (owned : MoveApplyMachine.Owned c.l) (after : Cfg Γ Λ R)
    (executed : step caller (applyCfg c) = some after) : FrameResult (applyCfg c) after := by
  have positive := (MoveApplyMachine.remainingSteps_pos_iff c).mpr owned
  obtain ⟨middle, moved, _⟩ := MoveApplyMachine.local_progress localCaller c positive
  have actual := apply_step_transport caller localCaller c owned
  rw [moved, Option.map_some] at actual
  have same : after = applyCfg middle := Option.some.inj (executed.symm.trans actual)
  subst after
  obtain ⟨registers, frame⟩ := MoveApplyMachine.local_step_frame localCaller ⟨owned, moved⟩
  refine ⟨?_, ?_, ?_⟩
  · change middle.var.2.2 = c.var.2.2
    exact congrArg Prod.snd registers
  · intro k
    rw [applyCfg_context, applyCfg_context]
    exact frame (.inr k)
  · intro clean
    change resetAll (applyRegisterEquiv c.var) = applyRegisterEquiv c.var at clean
    have localClean : MoveApplyMachine.reset c.var = c.var := by
      apply applyRegisterEquiv.injective
      rw [applyRegisterEquiv_reset, ← clean]
      rfl
    have reset := MoveApplyMachine.prefix_reset localCaller c middle 1 (by omega) moved
    rw [apply_registersAt_clean c 1 localClean] at reset
    change applyRegisterEquiv middle.var = applyRegisterEquiv c.var
    rw [reset]

theorem equality_step_frame
    (localCaller : TreeEqualityMachine.External (EqualityCallerLabel Λ) → EqualityStatement Γ Λ R)
    (c : EqualityCfg Γ Λ R) (owned : TreeEqualityMachine.Owned c.l) (after : Cfg Γ Λ R)
    (executed : step caller (equalityCfg c) = some after) : FrameResult (equalityCfg c) after := by
  obtain ⟨middle, moved, _⟩ := TreeEqualityMachine.local_progress localCaller c ((TreeEqualityMachine.remainingSteps_pos_iff c).mpr owned)
  have actual := equality_step_transport caller localCaller c owned
  rw [moved, Option.map_some] at actual
  have same : after = equalityCfg middle := Option.some.inj (executed.symm.trans actual)
  subst after
  obtain ⟨_, registers, _, _, frame⟩ := TreeEqualityMachine.local_step_data localCaller ⟨owned, moved⟩
  refine ⟨?_, ?_, ?_⟩
  · change middle.var.2.2.2 = c.var.2.2.2
    rw [registers]
    rfl
  · intro k
    rw [equalityCfg_context, equalityCfg_context]
    exact frame (.inr k)
  · intro clean
    change resetAll (equalityRegisterEquiv c.var) = equalityRegisterEquiv c.var at clean
    change equalityRegisterEquiv middle.var = equalityRegisterEquiv c.var
    rw [registers, equalityRegisterEquiv_reset, ← clean]
    rfl

theorem counter_step_frame (q : Resources.BinaryCounter.FixedWidthMachine.Phase) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (after : Cfg Γ Λ R)
    (executed : step caller (cfg (some (phaseLabel (counterPhase q))) regs D ctx) = some after) :
    FrameResult (cfg (some (phaseLabel (counterPhase q))) regs D ctx) after := by
  let localCaller : (FuelDispatchMachine.Exit ⊕ FuelCallerLabel Λ) → FuelStatement Γ Λ R := fun _ => .halt
  have startEq : fuelCfg (Λ := Λ) (fuelView (some (Resources.BinaryCounter.FixedWidthMachine.phaseLabel q)) regs D ctx) =
      cfg (some (phaseLabel (counterPhase q))) regs D ctx := by
    rw [fuelCfg_view]
    rfl
  rw [← startEq] at executed ⊢
  exact fuel_step_frame caller localCaller
    (fuelView (some (Resources.BinaryCounter.FixedWidthMachine.phaseLabel q)) regs D ctx)
    (Or.inl True.intro) after executed

theorem inspect_step_frame (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (after : Cfg Γ Λ R)
    (executed : step caller (cfg (some (phaseLabel inspectPhase)) regs D ctx) = some after) :
    FrameResult (cfg (some (phaseLabel inspectPhase)) regs D ctx) after := by
  let localCaller : (FuelDispatchMachine.Exit ⊕ FuelCallerLabel Λ) → FuelStatement Γ Λ R := fun _ => .halt
  have startEq : fuelCfg (Λ := Λ) (fuelView (some FuelDispatchMachine.inspectLabel) regs D ctx) =
      cfg (some (phaseLabel inspectPhase)) regs D ctx := by
    rw [fuelCfg_view]
    rfl
  rw [← startEq] at executed ⊢
  exact fuel_step_frame caller localCaller _ (Or.inr rfl) after executed

theorem apply_phase_step_frame (q : MoveApplyMachine.Phase) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (after : Cfg Γ Λ R)
    (executed : step caller (cfg (some (phaseLabel (applyPhase q))) regs D ctx) = some after) :
    FrameResult (cfg (some (phaseLabel (applyPhase q))) regs D ctx) after := by
  let localCaller : MoveApplyMachine.External (ApplyCallerLabel Λ) → ApplyStatement Γ Λ R := fun _ => .halt
  have startEq : applyCfg (Λ := Λ) (applyView (some (MoveApplyMachine.phaseLabel q)) (applyRegisterEquiv.symm regs) D ctx) =
      cfg (some (phaseLabel (applyPhase q))) regs D ctx := by
    rw [applyCfg_view]
    simp only [Option.map_some, applyLabelEquiv_phase, Equiv.apply_symm_apply]
  rw [← startEq] at executed ⊢
  exact apply_step_frame caller localCaller _ (MoveApplyMachine.owned_phase q) after executed

theorem compare_step_frame (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (after : Cfg Γ Λ R)
    (executed : step caller (cfg (some (phaseLabel comparePhase)) regs D ctx) = some after) :
    FrameResult (cfg (some (phaseLabel comparePhase)) regs D ctx) after := by
  let localCaller : TreeEqualityMachine.External (EqualityCallerLabel Λ) → EqualityStatement Γ Λ R := fun _ => .halt
  have startEq : equalityCfg (Λ := Λ) (equalityView (some (TreeEqualityMachine.phaseLabel .compare)) (equalityRegisterEquiv.symm regs) D ctx) =
      cfg (some (phaseLabel comparePhase)) regs D ctx := by
    rw [equalityCfg_view]
    simp only [Option.map_some, equalityLabelEquiv_phase, Equiv.apply_symm_apply]
  rw [← startEq] at executed ⊢
  exact equality_step_frame caller localCaller
    (equalityView (some (TreeEqualityMachine.phaseLabel .compare)) (equalityRegisterEquiv.symm regs) D ctx)
    True.intro after executed

omit [DecidableEq K] in
theorem reset_cfg_frame (label target : Option (Label Λ)) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    FrameResult (cfg label regs D ctx) (cfg target (resetAll regs) D ctx) :=
  ⟨rfl, fun _ => rfl, fun clean => clean⟩

theorem local_step_frame_data {before after : Cfg Γ Λ R} (transition : LocalStep caller before after) :
    FrameResult before after := by
  obtain ⟨q, regs, D, ctx, rfl⟩ := owned_cases before transition.1
  rcases q with fuel | (applied | equality)
  · rcases fuel with q | (r | (d | impossible))
    · exact counter_step_frame caller q D regs ctx after transition.2
    · cases r with
      | positive =>
          have same := Option.some.inj (transition.2.symm.trans (fuel_join_step caller .positive D regs ctx))
          subst after
          exact reset_cfg_frame _ _ D regs ctx
      | zero =>
          have same := Option.some.inj (transition.2.symm.trans (fuel_join_step caller .zero D regs ctx))
          subst after
          exact reset_cfg_frame _ _ D regs ctx
    · cases d with
      | inspectCertificate => exact inspect_step_frame caller D regs ctx after transition.2
      | atEnd =>
          have same := Option.some.inj (transition.2.symm.trans (fuel_join_step caller .atEnd D regs ctx))
          subst after
          exact reset_cfg_frame _ _ D regs ctx
    · exact Empty.elim impossible
  · rcases applied with q | (r | (q | (r | impossible)))
    · exact apply_phase_step_frame caller (MoveApplyMachine.movePhase q) D regs ctx after transition.2
    · exact apply_phase_step_frame caller (MoveApplyMachine.dispatchPhase r) D regs ctx after transition.2
    · exact apply_phase_step_frame caller (MoveApplyMachine.positionPhase q) D regs ctx after transition.2
    · have same := Option.some.inj (transition.2.symm.trans (apply_join_step caller r D regs ctx))
      subst after
      exact reset_cfg_frame _ _ D regs ctx
    · exact Empty.elim impossible
  · rcases equality with q | (r | impossible)
    · cases q; exact compare_step_frame caller D regs ctx after transition.2
    · have same := Option.some.inj (transition.2.symm.trans (equality_join_step caller r D regs ctx))
      subst after
      exact reset_cfg_frame _ _ D regs ctx
    · exact Empty.elim impossible

theorem local_step_frame {before after : Cfg Γ Λ R} (transition : LocalStep caller before after) :
    after.var.2.2 = before.var.2.2 ∧ ∀ k, after.stk (.inr k) = before.stk (.inr k) :=
  ⟨(local_step_frame_data caller transition).1, (local_step_frame_data caller transition).2.1⟩

theorem local_reaches_frame {start reached : Cfg Γ Λ R}
    (path : Relation.ReflTransGen (LocalStep caller) start reached) :
    reached.var.2.2 = start.var.2.2 ∧ ∀ k, reached.stk (.inr k) = start.stk (.inr k) := by
  induction path with
  | refl => exact ⟨rfl, fun _ => rfl⟩
  | @tail before after _ transition ih =>
      obtain ⟨registers, frame⟩ := local_step_frame caller transition
      exact ⟨registers.trans ih.1, fun k => (frame k).trans (ih.2 k)⟩

theorem local_reaches_resetAll {start reached : Cfg Γ Λ R}
    (path : Relation.ReflTransGen (LocalStep caller) start reached)
    (clean : resetAll start.var = start.var) : reached.var = start.var := by
  induction path with
  | refl => rfl
  | @tail before after _ transition ih =>
      have beforeClean : resetAll before.var = before.var := by rwa [ih]
      exact ((local_step_frame_data caller transition).2.2 beforeClean).trans ih

theorem prefix_frame (start reached : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start)
    (executed : (next caller)^[n] (some start) = some reached) :
    reached.var.2.2 = start.var.2.2 ∧ ∀ k, reached.stk (.inr k) = start.stk (.inr k) := by
  obtain ⟨actual, run, _, path, _⟩ := owned_prefix caller start n bound
  have same : actual = reached := Option.some.inj (run.symm.trans executed)
  subst actual
  exact local_reaches_frame caller path

theorem prefix_resetAll (start reached : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start)
    (executed : (next caller)^[n] (some start) = some reached)
    (clean : resetAll start.var = start.var) : reached.var = start.var := by
  obtain ⟨actual, run, _, path, _⟩ := owned_prefix caller start n bound
  have same : actual = reached := Option.some.inj (run.symm.trans executed)
  subst actual
  exact local_reaches_resetAll caller path clean

/-! ### Exact reindexing and prefix-bound composition for actual owned segments -/

/-- Reindex the actual Option-valued iterate after a proved complete local
segment. The continuation may include arbitrary caller behavior; this equality
itself does not extend any owned-prefix guarantee. -/
theorem prefix_iterate_after_localRun {start middle : Cfg Γ Λ R} {ticks : Nat}
    (run : LocalRun caller ticks start middle) (n : Nat) :
    (next caller)^[ticks + n] (some start) = (next caller)^[n] (some middle) := by
  rw [Nat.add_comm ticks n, Function.iterate_add_apply, LocalRun.iterate caller run]

/-- Compose two inclusive prefix properties through the literal intermediate
configuration. Both endpoint copies are retained at the shared boundary. -/
theorem prefix_property_after_localRun {start middle : Cfg Γ Λ R} {ticks tail : Nat}
    (run : LocalRun caller ticks start middle) (property : Cfg Γ Λ R → Prop)
    (first : ∀ n, n ≤ ticks → ∀ reached,
      (next caller)^[n] (some start) = some reached → property reached)
    (second : ∀ n, n ≤ tail → ∀ reached,
      (next caller)^[n] (some middle) = some reached → property reached) :
    ∀ n, n ≤ ticks + tail → ∀ reached,
      (next caller)^[n] (some start) = some reached → property reached := by
  intro n bound reached executed
  by_cases early : n ≤ ticks
  · exact first n early reached executed
  · have count : n = ticks + (n - ticks) := by omega
    apply second (n - ticks) (by omega) reached
    rw [← prefix_iterate_after_localRun caller run (n - ticks)]
    simpa only [← count] using executed

/-- Every actual prefix through the global first return lies either in the
proved component segment or in its literal continuation. The bound is an
explicit maximum of the supplied allowances, never a maximum over a trace. -/
theorem prefix_bound_after_localRun {start middle : Cfg Γ Λ R} {ticks : Nat}
    (run : LocalRun caller ticks start middle) (weight : Cfg Γ Λ R → Nat)
    (firstBound secondBound : Nat)
    (first : ∀ n, n ≤ ticks → ∀ reached,
      (next caller)^[n] (some start) = some reached → weight reached ≤ firstBound)
    (second : ∀ n, n ≤ remainingSteps middle → ∀ reached,
      (next caller)^[n] (some middle) = some reached → weight reached ≤ secondBound) :
    ∀ n, n ≤ remainingSteps start → ∀ reached,
      (next caller)^[n] (some start) = some reached →
        weight reached ≤ max firstBound secondBound := by
  have composed := prefix_property_after_localRun caller run
    (fun reached => weight reached ≤ max firstBound secondBound)
    (fun n bound reached executed => (first n bound reached executed).trans (Nat.le_max_left _ _))
    (fun n bound reached executed => (second n bound reached executed).trans (Nat.le_max_right _ _))
  simpa only [LocalRun.remaining caller run] using composed

/-! ## The genuine physical sum and endpoint-recursive dirty allowance -/

/-! ### Complete actual component prefixes and their protected complements -/

theorem fuel_owned_prefix
    (localCaller : (FuelDispatchMachine.Exit ⊕ FuelCallerLabel Λ) → FuelStatement Γ Λ R)
    (start : FuelCfg Γ Λ R) (n : Nat) (bound : n ≤ FuelDispatchMachine.remainingSteps start) :
    ∃ reached, (FuelDispatchMachine.next localCaller)^[n] (some start) = some reached ∧
      FuelDispatchMachine.remainingSteps reached = FuelDispatchMachine.remainingSteps start - n ∧
      Relation.ReflTransGen (FuelDispatchMachine.LocalStep localCaller) start reached ∧
      (n < FuelDispatchMachine.remainingSteps start ↔ FuelDispatchMachine.Owned reached.l) := by
  obtain ⟨reached, executed, rank, path⟩ := Resources.BinaryCounter.FixedWidthMachine.ranked_prefix
    (FuelDispatchMachine.step localCaller) FuelDispatchMachine.remainingSteps
    (FuelDispatchMachine.local_progress localCaller) n start bound
  refine ⟨reached, executed, rank, ?_, ?_⟩
  · exact Relation.ReflTransGen.mono
      (fun before _ h => ⟨(FuelDispatchMachine.remainingSteps_pos_iff before).mp h.1, h.2⟩) _ _ path
  · rw [← FuelDispatchMachine.remainingSteps_pos_iff, rank]
    omega

theorem fuel_prefix_lift
    (localCaller : (FuelDispatchMachine.Exit ⊕ FuelCallerLabel Λ) → FuelStatement Γ Λ R)
    (start : FuelCfg Γ Λ R) (n : Nat) (bound : n ≤ FuelDispatchMachine.remainingSteps start)
    (reached : Cfg Γ Λ R) (executed : (next caller)^[n] (some (fuelCfg start)) = some reached) :
    ∃ middle, (FuelDispatchMachine.next localCaller)^[n] (some start) = some middle ∧
      Relation.ReflTransGen (FuelDispatchMachine.LocalStep localCaller) start middle ∧
      reached = fuelCfg middle := by
  obtain ⟨middle, run, _, path, _⟩ := fuel_owned_prefix localCaller start n bound
  have earlier : ∀ j, j < n → ∃ prior,
      (FuelDispatchMachine.next localCaller)^[j] (some start) = some prior ∧ FuelDispatchMachine.Owned prior.l := by
    intro j strict
    obtain ⟨prior, arrived, _, _, live⟩ := fuel_owned_prefix localCaller start j (by omega)
    exact ⟨prior, arrived, live.mp (by omega)⟩
  have transported := fuel_prefix_transport caller localCaller n start earlier
  rw [run, Option.map_some] at transported
  exact ⟨middle, run, path, Option.some.inj (executed.symm.trans transported)⟩

theorem apply_prefix_lift
    (localCaller : MoveApplyMachine.External (ApplyCallerLabel Λ) → ApplyStatement Γ Λ R)
    (start : ApplyCfg Γ Λ R) (n : Nat) (bound : n ≤ MoveApplyMachine.remainingSteps start)
    (reached : Cfg Γ Λ R) (executed : (next caller)^[n] (some (applyCfg start)) = some reached) :
    ∃ middle, (MoveApplyMachine.next localCaller)^[n] (some start) = some middle ∧
      Relation.ReflTransGen (MoveApplyMachine.LocalStep localCaller) start middle ∧
      reached = applyCfg middle := by
  obtain ⟨middle, run, _, path, _⟩ := MoveApplyMachine.owned_prefix localCaller start n bound
  have earlier : ∀ j, j < n → ∃ prior,
      (MoveApplyMachine.next localCaller)^[j] (some start) = some prior ∧ MoveApplyMachine.Owned prior.l := by
    intro j strict
    obtain ⟨prior, arrived, _, _, live⟩ := MoveApplyMachine.owned_prefix localCaller start j (by omega)
    exact ⟨prior, arrived, live.mp (by omega)⟩
  have transported := apply_prefix_transport caller localCaller n start earlier
  rw [run, Option.map_some] at transported
  exact ⟨middle, run, path, Option.some.inj (executed.symm.trans transported)⟩

theorem equality_prefix_lift
    (localCaller : TreeEqualityMachine.External (EqualityCallerLabel Λ) → EqualityStatement Γ Λ R)
    (start : EqualityCfg Γ Λ R) (n : Nat) (bound : n ≤ TreeEqualityMachine.remainingSteps start)
    (reached : Cfg Γ Λ R) (executed : (next caller)^[n] (some (equalityCfg start)) = some reached) :
    ∃ middle, (TreeEqualityMachine.next localCaller)^[n] (some start) = some middle ∧
      Relation.ReflTransGen (TreeEqualityMachine.LocalStep localCaller) start middle ∧
      reached = equalityCfg middle := by
  obtain ⟨middle, run, _, path, _⟩ := TreeEqualityMachine.owned_prefix localCaller start n bound
  have earlier : ∀ j, j < n → ∃ prior,
      (TreeEqualityMachine.next localCaller)^[j] (some start) = some prior ∧ TreeEqualityMachine.Owned prior.l := by
    intro j strict
    obtain ⟨prior, arrived, _, _, live⟩ := TreeEqualityMachine.owned_prefix localCaller start j (by omega)
    exact ⟨prior, arrived, live.mp (by omega)⟩
  have transported := equality_prefix_transport caller localCaller n start earlier
  rw [run, Option.map_some] at transported
  exact ⟨middle, run, path, Option.some.inj (executed.symm.trans transported)⟩

theorem fuel_local_reaches_frame
    (localCaller : (FuelDispatchMachine.Exit ⊕ FuelCallerLabel Λ) → FuelStatement Γ Λ R)
    {start reached : FuelCfg Γ Λ R}
    (path : Relation.ReflTransGen (FuelDispatchMachine.LocalStep localCaller) start reached) :
    reached.var.2 = start.var.2 ∧ ∀ k, reached.stk (.inr k) = start.stk (.inr k) := by
  induction path with
  | refl => exact ⟨rfl, fun _ => rfl⟩
  | @tail before after _ transition ih =>
      obtain ⟨registers, frame⟩ := fuel_local_step_data localCaller transition
      refine ⟨?_, fun k => (frame k).trans (ih.2 k)⟩
      rw [registers]
      exact ih.1

/-- The full Fuel-protected complement includes the untouched certificate,
all six complementary local stores, and every external stack. -/
theorem fuel_prefix_frame
    (localCaller : (FuelDispatchMachine.Exit ⊕ FuelCallerLabel Λ) → FuelStatement Γ Λ R)
    (start : FuelCfg Γ Λ R) (n : Nat) (bound : n ≤ FuelDispatchMachine.remainingSteps start)
    (reached : Cfg Γ Λ R) (executed : (next caller)^[n] (some (fuelCfg start)) = some reached) :
    ∃ middle, reached = fuelCfg middle ∧ middle.var.2 = start.var.2 ∧
      ∀ k, middle.stk (.inr k) = start.stk (.inr k) := by
  obtain ⟨middle, _, path, rfl⟩ := fuel_prefix_lift caller localCaller start n bound reached executed
  exact ⟨middle, rfl, fuel_local_reaches_frame localCaller path⟩

/-- MoveApply prefixes preserve the full fuel/target/external complement and
the complete component caller register, including the borrowed Bool field. -/
theorem apply_prefix_frame
    (localCaller : MoveApplyMachine.External (ApplyCallerLabel Λ) → ApplyStatement Γ Λ R)
    (start : ApplyCfg Γ Λ R) (n : Nat) (bound : n ≤ MoveApplyMachine.remainingSteps start)
    (reached : Cfg Γ Λ R) (executed : (next caller)^[n] (some (applyCfg start)) = some reached) :
    ∃ middle, reached = applyCfg middle ∧ middle.var.2 = start.var.2 ∧
      ∀ k, middle.stk (.inr k) = start.stk (.inr k) := by
  obtain ⟨middle, _, path, rfl⟩ := apply_prefix_lift caller localCaller start n bound reached executed
  exact ⟨middle, rfl, MoveApplyMachine.local_reaches_frame localCaller path⟩

/-- Equality preserves all seven complementary local stores and every
external stack, as well as Bool/Branch/caller-register data. -/
theorem equality_prefix_frame
    (localCaller : TreeEqualityMachine.External (EqualityCallerLabel Λ) → EqualityStatement Γ Λ R)
    (start : EqualityCfg Γ Λ R) (n : Nat) (bound : n ≤ TreeEqualityMachine.remainingSteps start)
    (reached : Cfg Γ Λ R) (executed : (next caller)^[n] (some (equalityCfg start)) = some reached) :
    ∃ middle, reached = equalityCfg middle ∧ middle.var.2 = start.var.2 ∧
      ∀ k, middle.stk (.inr k) = start.stk (.inr k) := by
  obtain ⟨middle, _, path, rfl⟩ := equality_prefix_lift caller localCaller start n bound reached executed
  exact ⟨middle, rfl, TreeEqualityMachine.local_reaches_frame localCaller path⟩

/-! ### Exact Type-valued timing at every local boundary -/

omit [DecidableEq K] in
def inspectSteps (D : LocalData) : Nat := (evaluateInspect D).steps

omit [DecidableEq K] in
def inspectResult (regs : Registers R) (D : LocalData) (ctx : ∀ k, List (Γ k)) : Cfg Γ Λ R :=
  evaluationCfg regs (evaluateInspect D) ctx

def phaseInTime (q : Phase) (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller)
      (cfg (some (phaseLabel q)) regs D ctx) (some (phaseResult q regs D ctx)) (phaseSteps q D) where
  steps := phaseSteps q D
  evals_in_steps := phase_iterate caller q D regs ctx
  steps_le_m := Nat.le_refl _

def cfgInTime (start : Cfg Γ Λ R) :
    StateTransition.EvalsToInTime (step caller) start (some (finalCfg start)) (remainingSteps start) where
  steps := remainingSteps start
  evals_in_steps := cfg_iterate caller start
  steps_le_m := Nat.le_refl _

def inspectInTime (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller)
      (cfg (some (phaseLabel inspectPhase)) regs D ctx) (some (inspectResult regs D ctx)) (inspectSteps D) where
  steps := inspectSteps D
  evals_in_steps := LocalRun.iterate caller (inspect_localRun caller D regs ctx)
  steps_le_m := Nat.le_refl _

def counterStageInTime (q : Resources.BinaryCounter.FixedWidthMachine.Phase) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller)
      (cfg (some (phaseLabel (counterPhase q))) regs D ctx)
      (some (cfg (some (phaseLabel (fuelJoinPhase (FuelDispatchMachine.exitOfResult (counterFinish q D).result))))
        (resetFuel regs) (counterFinish q D).data ctx)) (counterFinish q D).steps where
  steps := (counterFinish q D).steps
  evals_in_steps := LocalRun.iterate caller (counter_phase_localRun caller q D regs ctx)
  steps_le_m := Nat.le_refl _

def fuelStageInTime (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller)
      (cfg (some (phaseLabel inspectPhase)) regs D ctx)
      (some (cfg (some (phaseLabel (fuelJoinPhase (inspectStageFinish D).result)))
        (resetFuel regs) (inspectStageFinish D).data ctx)) (inspectStageFinish D).steps where
  steps := (inspectStageFinish D).steps
  evals_in_steps := LocalRun.iterate caller (inspect_stage_localRun caller D regs ctx)
  steps_le_m := Nat.le_refl _

def applyStageInTime (q : MoveApplyMachine.Phase) (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller)
      (cfg (some (phaseLabel (applyPhase q))) regs D ctx)
      (some (cfg (some (phaseLabel (applyJoinPhase (applyFinish q D).result)))
        (resetApply regs) (applyFinish q D).data ctx)) (applyFinish q D).steps where
  steps := (applyFinish q D).steps
  evals_in_steps := LocalRun.iterate caller (apply_phase_localRun caller q D regs ctx)
  steps_le_m := Nat.le_refl _

def equalityStageInTime (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller)
      (cfg (some (phaseLabel comparePhase)) regs D ctx)
      (some (cfg (some (phaseLabel (equalityJoinPhase (equalityFinish D).result)))
        (resetEquality regs) (equalityFinish D).data ctx)) (equalityFinish D).steps where
  steps := (equalityFinish D).steps
  evals_in_steps := LocalRun.iterate caller (equality_phase_localRun caller D regs ctx)
  steps_le_m := Nat.le_refl _

def fuelJoinInTime (r : FuelDispatchMachine.Exit) (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller)
      (cfg (some (phaseLabel (fuelJoinPhase r))) regs D ctx)
      (some (cfg (some (fuelJoinTarget r)) (resetAll regs) D ctx)) 1 where
  steps := 1
  evals_in_steps := fuel_join_step caller r D regs ctx
  steps_le_m := Nat.le_refl _

def applyJoinInTime (r : MoveApplyMachine.FinalResult) (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller)
      (cfg (some (phaseLabel (applyJoinPhase r))) regs D ctx)
      (some (cfg (some (applyJoinTarget r)) (resetAll regs) D ctx)) 1 where
  steps := 1
  evals_in_steps := apply_join_step caller r D regs ctx
  steps_le_m := Nat.le_refl _

def equalityJoinInTime (r : TreeEqualityMachine.Result) (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller)
      (cfg (some (phaseLabel (equalityJoinPhase r))) regs D ctx)
      (some (cfg (some (equalityJoinTarget r)) (resetAll regs) D ctx)) 1 where
  steps := 1
  evals_in_steps := equality_join_step caller r D regs ctx
  steps_le_m := Nat.le_refl _

@[simp] theorem phaseInTime_steps (q : Phase) (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (phaseInTime caller q D regs ctx).steps = phaseSteps q D := rfl
@[simp] theorem cfgInTime_steps (start : Cfg Γ Λ R) :
    (cfgInTime caller start).steps = remainingSteps start := rfl
@[simp] theorem inspectInTime_steps (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (inspectInTime caller D regs ctx).steps = inspectSteps D := rfl
@[simp] theorem counterStageInTime_steps (q : Resources.BinaryCounter.FixedWidthMachine.Phase) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (counterStageInTime caller q D regs ctx).steps = (counterFinish q D).steps := rfl
@[simp] theorem fuelStageInTime_steps (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (fuelStageInTime caller D regs ctx).steps = (inspectStageFinish D).steps := rfl
@[simp] theorem applyStageInTime_steps (q : MoveApplyMachine.Phase) (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (applyStageInTime caller q D regs ctx).steps = (applyFinish q D).steps := rfl
@[simp] theorem equalityStageInTime_steps (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (equalityStageInTime caller D regs ctx).steps = (equalityFinish D).steps := rfl
@[simp] theorem fuelJoinInTime_steps (r : FuelDispatchMachine.Exit) (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (fuelJoinInTime caller r D regs ctx).steps = 1 := rfl
@[simp] theorem applyJoinInTime_steps (r : MoveApplyMachine.FinalResult) (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (applyJoinInTime caller r D regs ctx).steps = 1 := rfl
@[simp] theorem equalityJoinInTime_steps (r : TreeEqualityMachine.Result) (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (equalityJoinInTime caller r D regs ctx).steps = 1 := rfl


end Resources.RotationCertificate.StreamMachine
