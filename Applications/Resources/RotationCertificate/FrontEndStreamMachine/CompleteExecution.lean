import Applications.Resources.RotationCertificate.FrontEndStreamMachine.DirtyPrefixes

/-!
# FrontEndStreamMachine: CompleteExecution
-/

set_option autoImplicit false
set_option warningAsError true

namespace Resources.RotationCertificate.FrontEndStreamMachine

open Search.SharedTree (Branch)
open Resources.BinaryCounter (Bits)

variable {K Λ R : Type} {Γ : K → Type}
variable [DecidableEq K]
variable (caller : Λ → Statement Γ Λ R)

omit caller [DecidableEq K] in
theorem cleanupSteps_ge_two (i : Fin 16) (D : LocalData) : 2 ≤ cleanupSteps i D := by
  unfold cleanupSteps
  have := i.isLt
  omega

omit caller [DecidableEq K] in
def cleanupRegistersAt (i : Fin 16) (regs : Registers R) (D : LocalData) (n : Nat) : Registers R :=
  if n = 0 then regs else
  if n = cleanupSteps i D - 1 then occupancyRegisters false regs else
  if cleanupSteps i D ≤ n then fullReset regs else
  if ∃ j : Fin 16, i.val ≤ j.val ∧ n = boundarySteps i j D then occupancyRegisters false regs
  else occupancyRegisters true regs

omit caller [DecidableEq K] in
@[simp] theorem user_occupancyRegisters (b : Bool) (regs : Registers R) :
    user (occupancyRegisters b regs) = user regs := rfl

omit caller [DecidableEq K] in
theorem cleanupRegistersAt_user (i : Fin 16) (regs : Registers R) (D : LocalData) (n : Nat) :
    user (cleanupRegistersAt i regs D n) = user regs := by
  unfold cleanupRegistersAt
  split_ifs <;> rfl

include caller in
theorem cleanup_prefix_before_emit (i j : Fin 16) (t : Nat) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (ordered : i.val ≤ j.val) (within : t ≤ slotLength j D) :
    boundarySteps i j D + t < cleanupSteps i D - 1 := by
  have first := cleanup_prefix_localRun caller i j t D regs ctx ordered within
  have last := cleanup_localRun caller j (dropData j t (boundaryData i j D))
    (drainRegisters (boundaryRegisters i j regs) t) ctx
  have canonical := cleanup_localRun caller i D regs ctx
  have count := (LocalRun.first_unique caller canonical (LocalRun.trans caller first last)
    not_owned_none not_owned_none).1
  have atLeast := cleanupSteps_ge_two j (dropData j t (boundaryData i j D))
  omega

include caller in
theorem cleanupRegistersAt_indexed (i j : Fin 16) (t : Nat) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (ordered : i.val ≤ j.val) (within : t ≤ slotLength j D) :
    cleanupRegistersAt i regs D (boundarySteps i j D + t) =
      drainRegisters (boundaryRegisters i j regs) t := by
  have beforeEmit := cleanup_prefix_before_emit caller i j t D regs ctx ordered within
  by_cases zero : boundarySteps i j D + t = 0
  · have clock : boundarySteps i i D + 0 = boundarySteps i j D + t := by
      rw [boundarySteps_self]
      omega
    obtain ⟨same, tZero⟩ := cleanup_prefix_unique caller i i j 0 t D regs ctx (Nat.le_refl _) ordered
      (Nat.zero_le _) within clock
    subst j
    have tEq : t = 0 := tZero.symm
    subst t
    simp only [boundarySteps_self, Nat.zero_add, cleanupRegistersAt, ite_true,
      boundaryRegisters_self, drainRegisters]
  · have notEmit : boundarySteps i j D + t ≠ cleanupSteps i D - 1 := by omega
    have notHalted : ¬ cleanupSteps i D ≤ boundarySteps i j D + t := by omega
    by_cases emptyPrefix : t = 0
    · subst t
      have distinct : i ≠ j := by
        intro same
        subst j
        exact zero (by simp only [boundarySteps_self, Nat.add_zero])
      have boundary : ∃ k : Fin 16, i.val ≤ k.val ∧ boundarySteps i j D + 0 = boundarySteps i k D :=
        ⟨j, ordered, Nat.add_zero _⟩
      simp only [cleanupRegistersAt, zero, ite_false, notEmit, notHalted, boundary, ite_true,
        drainRegisters, boundaryRegisters, distinct]
    · have notBoundary : ¬ ∃ k : Fin 16, i.val ≤ k.val ∧
          boundarySteps i j D + t = boundarySteps i k D := by
        rintro ⟨k, lower, count⟩
        have clock : boundarySteps i j D + t = boundarySteps i k D + 0 := by omega
        have equal := cleanup_prefix_unique caller i j k t 0 D regs ctx ordered lower within (Nat.zero_le _) clock
        exact emptyPrefix equal.2
      simp only [cleanupRegistersAt, zero, ite_false, notEmit, notHalted, notBoundary,
        drainRegisters, emptyPrefix, boundaryRegisters]
      split_ifs <;> simp only [occupancyRegisters_occupancyRegisters]

omit caller [DecidableEq K] in
theorem cleanupRegistersAt_emit (i : Fin 16) (regs : Registers R) (D : LocalData) :
    cleanupRegistersAt i regs D (cleanupSteps i D - 1) = occupancyRegisters false regs := by
  have positive := cleanupSteps_ge_two i D
  have nonzero : cleanupSteps i D - 1 ≠ 0 := by omega
  simp only [cleanupRegistersAt, nonzero, ite_false, ite_true]

omit caller [DecidableEq K] in
theorem cleanupRegistersAt_halt (i : Fin 16) (regs : Registers R) (D : LocalData) :
    cleanupRegistersAt i regs D (cleanupSteps i D) = fullReset regs := by
  have positive := cleanupSteps_ge_two i D
  have nonzero : cleanupSteps i D ≠ 0 := by omega
  have notEmit : cleanupSteps i D ≠ cleanupSteps i D - 1 := by omega
  simp only [cleanupRegistersAt, nonzero, ite_false, notEmit, Nat.le_refl, ite_true]

theorem cleanup_prefix_registers (i : Fin 16) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (n : Nat) (bound : n ≤ cleanupSteps i D)
    (reached : Cfg Γ Λ R)
    (executed : (next caller)^[n] (some (cfg (some (clearLabel i)) regs D ctx)) = some reached) :
    reached.var = cleanupRegistersAt i regs D n ∧ user reached.var = user regs ∧
      ∀ k, reached.stk (.inr (.inr k)) = ctx k := by
  have minimum := cleanupSteps_ge_two i D
  by_cases early : n < cleanupSteps i D - 1
  · obtain ⟨j, lower, t, tBound, count⟩ := cleanup_prefix_cover i D n early
    have actual := cleanup_prefix_iterate caller i j t D regs ctx lower tBound
    rw [← count] at actual
    have same := Option.some.inj (actual.symm.trans executed)
    subst reached
    have registers : (cleanupPrefixCfg (Λ := Λ) i j t regs D ctx).var = cleanupRegistersAt i regs D n := by
      rw [count, cleanupRegistersAt_indexed caller i j t D regs ctx lower tBound]
      rfl
    refine ⟨registers, ?_, fun _ => rfl⟩
    rw [registers, cleanupRegistersAt_user]
  · by_cases atEmit : n = cleanupSteps i D - 1
    · subst n
      have same := Option.some.inj ((cleanup_emit_iterate caller i D regs ctx).symm.trans executed)
      subst reached
      exact ⟨(cleanupRegistersAt_emit i regs D).symm, rfl, fun _ => rfl⟩
    · have atHalt : n = cleanupSteps i D := by omega
      subst n
      have same := Option.some.inj ((cleanup_iterate caller i D regs ctx).symm.trans executed)
      subst reached
      exact ⟨(cleanupRegistersAt_halt i regs D).symm, rfl, fun _ => rfl⟩

omit caller [DecidableEq K] in
def frontEndControl : FrontEndMachine.OwnedLabels ⊕ Bool → FrontEndMachine.Label Empty
  | .inl q => (FrontEndMachine.ownedLabelEquiv q).val
  | .inr false => FrontEndMachine.rejectLabel
  | .inr true => FrontEndMachine.dispatchLabel

omit caller [DecidableEq K] in
def frontEndClass (q : FrontEndMachine.Label Empty) : FrontEndMachine.OwnedLabels ⊕ Bool :=
  match FrontEndMachine.inputPartitionEquiv.symm q with
  | .inl input => .inl (.inl input)
  | .inr (.inl .failure) => .inr false
  | .inr (.inl .success) => .inl (.inr (.inr (.inr .scan)))
  | .inr (.inr (.inl framing)) => .inl (.inr (.inl framing))
  | .inr (.inr (.inr (.inl decoding))) => .inl (.inr (.inr (.inl decoding)))
  | .inr (.inr (.inr (.inr (.inl tail)))) =>
      .inl (.inr (.inr (.inr (FrontEndMachine.tailPhase tail))))
  | .inr (.inr (.inr (.inr (.inr (.inl _))))) => .inr true
  | .inr (.inr (.inr (.inr (.inr (.inr impossible))))) => Empty.elim impossible

omit caller [DecidableEq K] in
theorem frontEndClass_control (q : FrontEndMachine.OwnedLabels ⊕ Bool) :
    frontEndClass (frontEndControl q) = q := by
  cases q with
  | inl q =>
      have partition : FrontEndMachine.inputPartitionEquiv.symm
          (FrontEndMachine.ownedLabelEquiv (Λ := Empty) q).val =
          (FrontEndMachine.ownedPartitionEquiv q).val :=
        FrontEndMachine.inputPartitionEquiv.symm_apply_apply _
      unfold frontEndClass frontEndControl
      rw [partition]
      cases q with
      | inl input => rfl
      | inr q => cases q with
        | inl framing => rfl
        | inr q => cases q with
          | inl decoding => rfl
          | inr decoding => cases decoding <;> rfl
  | inr b => cases b <;> rfl

omit caller [DecidableEq K] in
theorem frontEndControl_class (q : FrontEndMachine.Label Empty) :
    frontEndControl (frontEndClass q) = q := by
  obtain ⟨partition, rfl⟩ := FrontEndMachine.inputPartitionEquiv.surjective q
  unfold frontEndClass
  rw [Equiv.symm_apply_apply]
  cases partition with
  | inl input => rfl
  | inr partition => cases partition with
    | inl result => cases result <;> rfl
    | inr extra => cases extra with
      | inl framing => rfl
      | inr extra => cases extra with
        | inl decoding => rfl
        | inr extra => cases extra with
          | inl tail => cases tail <;> rfl
          | inr extra => cases extra with
            | inl token => cases token; rfl
            | inr impossible => exact Empty.elim impossible

omit caller [DecidableEq K] in
def frontEndControlEquiv : (FrontEndMachine.OwnedLabels ⊕ Bool) ≃ FrontEndMachine.Label Empty where
  toFun := frontEndControl
  invFun := frontEndClass
  left_inv := frontEndClass_control
  right_inv := frontEndControl_class

omit caller [DecidableEq K] in
@[simp] theorem frontEndControlEquiv_apply (q : FrontEndMachine.OwnedLabels ⊕ Bool) :
    frontEndControlEquiv q = frontEndControl q := rfl

omit caller [DecidableEq K] in
def streamControl : StreamMachine.Phase ⊕ Bool → StreamMachine.Label Empty
  | .inl q => StreamMachine.phaseLabel q
  | .inr b => StreamMachine.resultLabel b

omit caller [DecidableEq K] in
def streamClass : StreamMachine.Label Empty → StreamMachine.Phase ⊕ Bool
  | .inl q => .inl (.inl q)
  | .inr (.inl q) => .inl (.inr (.inl q))
  | .inr (.inr (.inl q)) => .inl (.inr (.inr q))
  | .inr (.inr (.inr (.inl b))) => .inr b
  | .inr (.inr (.inr (.inr impossible))) => Empty.elim impossible

omit caller [DecidableEq K] in
theorem streamClass_control (q : StreamMachine.Phase ⊕ Bool) : streamClass (streamControl q) = q := by
  rcases q with (q | (q | q)) | b <;> rfl

omit caller [DecidableEq K] in
theorem streamControl_class (q : StreamMachine.Label Empty) : streamControl (streamClass q) = q := by
  rcases q with q | (q | (q | (b | impossible)))
  · rfl
  · rfl
  · rfl
  · rfl
  · exact Empty.elim impossible

omit caller [DecidableEq K] in
def streamControlEquiv : (StreamMachine.Phase ⊕ Bool) ≃ StreamMachine.Label Empty where
  toFun := streamControl
  invFun := streamClass
  left_inv := streamClass_control
  right_inv := streamControl_class

omit caller [DecidableEq K] in
@[simp] theorem streamControlEquiv_apply (q : StreamMachine.Phase ⊕ Bool) :
    streamControlEquiv q = streamControl q := rfl

omit caller [DecidableEq K] in
@[simp] theorem frontEndData_withFrontEnd (D : LocalData) (E : FrontEndMachine.LocalData) :
    frontEndData (withFrontEnd D E) = E := by cases E; rfl

omit caller [DecidableEq K] in
@[simp] theorem frontEndContext_withFrontEnd (D : LocalData) (E : FrontEndMachine.LocalData)
    (ctx : ∀ k, List (Γ k)) : frontEndContext (withFrontEnd D E) ctx = frontEndContext D ctx := rfl

omit caller [DecidableEq K] in
theorem frontEndLabelEquiv_owned (q : FrontEndMachine.OwnedLabels) :
    frontEndLabelEquiv (FrontEndMachine.ownedLabelEquiv (Λ := FrontEndCallerLabel Λ) q).val =
      phaseLabel (frontEndPhase q) := by
  cases q with
  | inl q => cases q with
    | inl pair => rcases pair with ⟨side, phase⟩; rfl
    | inr q => cases q with
      | inl side => cases side <;> rfl
      | inr q => cases q with
        | inl token => cases token; rfl
        | inr phase => rfl
  | inr q => cases q with
    | inl framing => rfl
    | inr q => cases q with
      | inl decoding => rfl
      | inr decoding => cases decoding <;> rfl

omit caller [DecidableEq K] in
def frontEndResultPhase : TreeParserMachine.Result → Phase
  | .success => dispatchPhase
  | .failure => rejectPhase

omit caller [DecidableEq K] in
theorem frontEndLabelEquiv_result (r : TreeParserMachine.Result) :
    frontEndLabelEquiv (DirtyFrontEnd.frontEndResultLabel (Λ := FrontEndCallerLabel Λ) r) =
      phaseLabel (frontEndResultPhase r) := by cases r <;> rfl

omit caller [DecidableEq K] in
theorem fullReset_frontEndMaskRegs (masks : List DirtyFrontEnd.FrontEndMask) (regs : Registers R) :
    fullReset (DirtyFrontEnd.frontEndMaskRegs masks regs) = fullReset regs := by
  induction masks generalizing regs with
  | nil => rfl
  | cons mask masks ih =>
      change fullReset (DirtyFrontEnd.frontEndMaskRegs masks (mask.apply regs)) = fullReset regs
      rw [ih]
      cases mask <;> rfl

omit caller [DecidableEq K] in
def frontEndFinishData (q : FrontEndMachine.OwnedLabels) (D : LocalData) : LocalData :=
  withFrontEnd D (DirtyFrontEnd.frontEndPhaseFinish q (frontEndData D)).data

omit caller [DecidableEq K] in
def frontEndFinishRegisters (q : FrontEndMachine.OwnedLabels) (D : LocalData)
    (regs : Registers R) : Registers R :=
  DirtyFrontEnd.frontEndMaskRegs (DirtyFrontEnd.frontEndPhaseFinish q (frontEndData D)).masks regs

omit caller [DecidableEq K] in
def frontEndComponentCfg (q : FrontEndMachine.OwnedLabels) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) : Cfg Γ Λ R :=
  cfg (some (phaseLabel (frontEndResultPhase (DirtyFrontEnd.frontEndPhaseFinish q (frontEndData D)).result)))
    (frontEndFinishRegisters q D regs) (frontEndFinishData q D) ctx

omit caller [DecidableEq K] in
theorem frontEndCfg_phaseResult (q : FrontEndMachine.OwnedLabels) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    frontEndCfg (DirtyFrontEnd.frontEndPhaseResult (Λ := FrontEndCallerLabel Λ) q regs
      (frontEndData D) (frontEndContext D ctx)) = frontEndComponentCfg q D regs ctx := by
  have transported := frontEndCfg_view (Λ := Λ)
    (some (DirtyFrontEnd.frontEndResultLabel (DirtyFrontEnd.frontEndPhaseFinish q (frontEndData D)).result))
    (frontEndFinishRegisters q D regs) (frontEndFinishData q D) ctx
  simpa only [frontEndView, frontEndFinishData, frontEndData_withFrontEnd, frontEndContext_withFrontEnd,
    DirtyFrontEnd.frontEndPhaseResult, DirtyFrontEnd.frontEndFinishCfg, frontEndFinishRegisters,
    Option.map_some, frontEndLabelEquiv_result, frontEndComponentCfg] using transported

theorem frontEnd_phase_localRun (q : FrontEndMachine.OwnedLabels) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (DirtyFrontEnd.frontEndPhaseSteps q (frontEndData D))
      (cfg (some (phaseLabel (frontEndPhase q))) regs D ctx) (frontEndComponentCfg q D regs ctx) := by
  have trace := DirtyFrontEnd.frontEnd_phase_trace
    (Γ := StreamMachine.frontEndAddedAlphabet Γ) (Λ := FrontEndCallerLabel Λ)
    (fun _ => .halt) q (frontEndData D) regs (frontEndContext D ctx)
  have transported := frontEnd_trace_localRun caller (fun _ => .halt) trace
  have start := frontEndCfg_view (Λ := Λ) (some (FrontEndMachine.ownedLabelEquiv q).val) regs D ctx
  simp only [Option.map_some, frontEndLabelEquiv_owned] at start
  change frontEndCfg (FrontEndMachine.cfg (some (FrontEndMachine.ownedLabelEquiv q).val)
    regs (frontEndData D) (frontEndContext D ctx)) = _ at start
  rw [start, frontEndCfg_phaseResult] at transported
  exact transported

omit caller [DecidableEq K] in
def frontEndEvaluation (q : FrontEndMachine.OwnedLabels) (D : LocalData) : Evaluation :=
  let finish := DirtyFrontEnd.frontEndPhaseFinish q (frontEndData D)
  addSteps finish.steps (match finish.result with
    | .success => dispatchEvaluation (withFrontEnd D finish.data)
    | .failure => answerEvaluation false (withFrontEnd D finish.data))

theorem frontEnd_complete_localRun (q : FrontEndMachine.OwnedLabels) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (frontEndEvaluation q D).steps
      (cfg (some (phaseLabel (frontEndPhase q))) regs D ctx)
      (evaluationCfg regs (frontEndEvaluation q D) ctx) := by
  let finish := DirtyFrontEnd.frontEndPhaseFinish q (frontEndData D)
  have first := frontEnd_phase_localRun caller q D regs ctx
  change LocalRun caller finish.steps _
    (cfg (some (phaseLabel (frontEndResultPhase finish.result)))
      (DirtyFrontEnd.frontEndMaskRegs finish.masks regs) (withFrontEnd D finish.data) ctx) at first
  change LocalRun caller (finish.steps + (match finish.result with
      | .success => dispatchEvaluation (withFrontEnd D finish.data)
      | .failure => answerEvaluation false (withFrontEnd D finish.data)).steps)
    (cfg (some (phaseLabel (frontEndPhase q))) regs D ctx)
    (evaluationCfg regs (match finish.result with
      | .success => dispatchEvaluation (withFrontEnd D finish.data)
      | .failure => answerEvaluation false (withFrontEnd D finish.data)) ctx)
  cases result : finish.result with
  | success =>
      rw [result] at first
      have last := dispatch_complete_localRun caller (withFrontEnd D finish.data)
        (DirtyFrontEnd.frontEndMaskRegs finish.masks regs) ctx
      simpa only [evaluationCfg, fullReset_frontEndMaskRegs, frontEndResultPhase] using LocalRun.trans caller first last
  | failure =>
      rw [result] at first
      have last := reject_complete_localRun caller (withFrontEnd D finish.data)
        (DirtyFrontEnd.frontEndMaskRegs finish.masks regs) ctx
      simpa only [evaluationCfg, fullReset_frontEndMaskRegs, frontEndResultPhase] using LocalRun.trans caller first last

omit caller [DecidableEq K] in
def evaluate (q : Phase) (initialAnswer : Bool) (D : LocalData) : Evaluation := match q with
  | .inl q => match frontEndClass q with
    | .inl q => frontEndEvaluation q D
    | .inr false => answerEvaluation false D
    | .inr true => dispatchEvaluation D
  | .inr (.inl q) => match streamClass q with
    | .inl q => streamEvaluation q D
    | .inr b => answerEvaluation b D
  | .inr (.inr (.clear i)) => ⟨cleanupSteps i D, cleanupData i initialAnswer D⟩
  | .inr (.inr .emit) => ⟨1, emitData initialAnswer D⟩

omit caller [DecidableEq K] in
theorem evaluate_steps_answer_independent (q : Phase) (a b : Bool) (D : LocalData) :
    (evaluate q a D).steps = (evaluate q b D).steps := by
  cases q with
  | inl q => rfl
  | inr q => cases q with
    | inl q => rfl
    | inr q => cases q <;> rfl

omit caller [DecidableEq K] in
def phaseSteps (q : Phase) (D : LocalData) : Nat := (evaluate q false D).steps

omit caller [DecidableEq K] in
def phaseResult (q : Phase) (regs : Registers R) (D : LocalData)
    (ctx : ∀ k, List (Γ k)) : Cfg Γ Λ R := evaluationCfg regs (evaluate q (answer regs) D) ctx

theorem phase_localRun (q : Phase) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (phaseSteps q D) (cfg (some (phaseLabel q)) regs D ctx) (phaseResult q regs D ctx) := by
  cases q with
  | inl q =>
      obtain ⟨kind, rfl⟩ := frontEndControlEquiv.surjective q
      cases kind with
      | inl q =>
          simp only [phaseSteps, phaseResult, evaluate, frontEndControlEquiv_apply, frontEndClass_control]
          change LocalRun caller (frontEndEvaluation q D).steps
            (cfg (some (phaseLabel (frontEndPhase q))) regs D ctx)
            (evaluationCfg regs (frontEndEvaluation q D) ctx)
          exact frontEnd_complete_localRun caller q D regs ctx
      | inr b => cases b with
        | false => exact reject_complete_localRun caller D regs ctx
        | true => exact dispatch_complete_localRun caller D regs ctx
  | inr q => cases q with
    | inl q =>
        obtain ⟨kind, rfl⟩ := streamControlEquiv.surjective q
        cases kind with
        | inl q =>
            simp only [phaseSteps, phaseResult, evaluate, streamControlEquiv_apply, streamClass_control]
            change LocalRun caller (streamEvaluation q D).steps
              (cfg (some (phaseLabel (streamPhase q))) regs D ctx)
              (evaluationCfg regs (streamEvaluation q D) ctx)
            exact stream_complete_localRun caller q D regs ctx
        | inr b => exact result_complete_localRun caller b D regs ctx
    | inr q => cases q with
      | clear i => exact cleanup_localRun caller i D regs ctx
      | emit => exact emit_localRun caller D regs ctx

theorem phase_iterate (q : Phase) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    (next caller)^[phaseSteps q D] (some (cfg (some (phaseLabel q)) regs D ctx)) =
      some (phaseResult q regs D ctx) := (phase_localRun caller q D regs ctx).iterate caller

omit caller [DecidableEq K] in
theorem phaseResult_not_owned (q : Phase) (regs : Registers R) (D : LocalData)
    (ctx : ∀ k, List (Γ k)) : ¬ Owned (phaseResult (Λ := Λ) q regs D ctx).l := not_owned_none

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

omit caller [DecidableEq K] in
theorem phaseSteps_pos (q : Phase) (D : LocalData) : 0 < phaseSteps q D := by
  let localCaller : Empty → Statement (fun _ : Empty => Empty) Empty Unit := fun _ => .halt
  let regs : Registers Unit := ((none, none), BitDecoderMachine.zeroRegisters, (none, ()))
  let ctx : Empty → List Empty := fun k => Empty.elim k
  have executed := phase_iterate localCaller q D regs ctx
  have nonowned := phaseResult_not_owned (Γ := fun _ : Empty => Empty) (Λ := Empty) q regs D ctx
  by_contra failure
  have zero : phaseSteps q D = 0 := by omega
  rw [zero] at executed
  have same : cfg (some (phaseLabel q)) regs D ctx = phaseResult (Λ := Empty) q regs D ctx :=
    Option.some.inj executed
  apply nonowned
  rw [← same]
  exact owned_phase q

omit caller [DecidableEq K] in
def remainingSteps (c : Cfg Γ Λ R) : Nat :=
  match c.l with
  | some (.inl q) => phaseSteps (.inl q) (dataOfCfg c)
  | some (.inr (.inl q)) => phaseSteps (.inr (.inl q)) (dataOfCfg c)
  | some (.inr (.inr (.inl q))) => phaseSteps (.inr (.inr q)) (dataOfCfg c)
  | _ => 0

omit caller [DecidableEq K] in
def finalCfg (c : Cfg Γ Λ R) : Cfg Γ Λ R :=
  match c.l with
  | some (.inl q) => phaseResult (.inl q) c.var (dataOfCfg c) (contextOfCfg c)
  | some (.inr (.inl q)) => phaseResult (.inr (.inl q)) c.var (dataOfCfg c) (contextOfCfg c)
  | some (.inr (.inr (.inl q))) => phaseResult (.inr (.inr q)) c.var (dataOfCfg c) (contextOfCfg c)
  | _ => c

omit caller [DecidableEq K] in
def stateRemainingSteps : Option (Cfg Γ Λ R) → Nat
  | none => 0
  | some c => remainingSteps c

omit caller [DecidableEq K] in
@[simp] theorem stateRemainingSteps_none : stateRemainingSteps (Γ := Γ) (Λ := Λ) (R := R) none = 0 := rfl

omit caller [DecidableEq K] in
@[simp] theorem stateRemainingSteps_some (c : Cfg Γ Λ R) :
    stateRemainingSteps (some c) = remainingSteps c := rfl

omit caller [DecidableEq K] in
theorem remainingSteps_phase_cfg (q : Phase) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    remainingSteps (cfg (some (phaseLabel (Λ := Λ) q)) regs D ctx) = phaseSteps q D := by
  cases q with
  | inl q => rfl
  | inr q => cases q <;> rfl

omit caller [DecidableEq K] in
theorem finalCfg_phase_cfg (q : Phase) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    finalCfg (cfg (some (phaseLabel (Λ := Λ) q)) regs D ctx) = phaseResult q regs D ctx := by
  cases q with
  | inl q => rfl
  | inr q => cases q <;> rfl

omit caller [DecidableEq K] in
theorem remainingSteps_pos_iff (c : Cfg Γ Λ R) : 0 < remainingSteps c ↔ Owned c.l := by
  cases labelEq : c.l with
  | none => simp only [remainingSteps, Owned, labelEq, Nat.lt_irrefl]
  | some label =>
      rcases label with f | (h | (e | external))
      · simp only [remainingSteps, Owned, labelEq, phaseSteps_pos]
      · simp only [remainingSteps, Owned, labelEq, phaseSteps_pos]
      · simp only [remainingSteps, Owned, labelEq, phaseSteps_pos]
      · simp only [remainingSteps, Owned, labelEq, Nat.lt_irrefl]

omit caller [DecidableEq K] in
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
omit caller [DecidableEq K] in
theorem nonowned_remaining (c : Cfg Γ Λ R) (returned : ¬ Owned c.l) : remainingSteps c = 0 := by
  have notPositive : ¬ 0 < remainingSteps c := fun h => returned ((remainingSteps_pos_iff c).mp h)
  omega

omit caller [DecidableEq K] in
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

omit caller [DecidableEq K] in
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

theorem LocalRun.phase_endpoint {q : Phase} {D : LocalData} {regs : Registers R}
    {ctx : ∀ k, List (Γ k)} {n : Nat} {finish : Cfg Γ Λ R}
    (run : LocalRun caller n (cfg (some (phaseLabel q)) regs D ctx) finish)
    (halted : finish.l = none) :
    phaseSteps q D = n ∧ phaseResult (Λ := Λ) q regs D ctx = finish := by
  exact LocalRun.first_unique caller (phase_localRun caller q D regs ctx) run
    (phaseResult_not_owned q regs D ctx) (by rw [halted]; exact not_owned_none)

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
theorem program_phase_independent (other : Λ → Statement Γ Λ R) (q : Phase) :
    program caller (phaseLabel q) = program other (phaseLabel q) := by
  cases q with
  | inl q => rfl
  | inr q => cases q with
    | inl q => rfl
    | inr q => cases q <;> rfl

theorem step_caller_independent (other : Λ → Statement Γ Λ R)
    (c : Cfg Γ Λ R) (owned : Owned c.l) : step caller c = step other c := by
  obtain ⟨q, regs, D, ctx, rfl⟩ := owned_cases c owned
  change some (Turing.TM2.stepAux (program caller (phaseLabel q)) regs
      (cfg (Λ := Λ) (some (phaseLabel q)) regs D ctx).stk) =
    some (Turing.TM2.stepAux (program other (phaseLabel q)) regs
      (cfg (Λ := Λ) (some (phaseLabel q)) regs D ctx).stk)
  rw [program_phase_independent caller other q]

theorem prefix_caller_independent (other : Λ → Statement Γ Λ R)
    (start : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start) :
    (next caller)^[n] (some start) = (next other)^[n] (some start) :=
  Resources.BinaryCounter.FixedWidthMachine.ranked_prefix_eq
    (step caller) (step other) remainingSteps (local_progress caller)
    (fun c positive => step_caller_independent caller other c ((remainingSteps_pos_iff c).mp positive))
    n start bound

omit caller [DecidableEq K] in
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

/-- The first boundary includes an external zero-step identity as well as a live halt. -/
def FirstBoundary (start : Cfg Γ Λ R) (n : Nat) (finish : Cfg Γ Λ R) : Prop :=
  (next caller)^[n] (some start) = some finish ∧ ¬ Owned finish.l ∧
    ∀ j, j < n → ∃ reached,
      (next caller)^[j] (some start) = some reached ∧ Owned reached.l

/-- A live halt is distinguished from the outer `Option.none` after its next step. -/
def FirstHalt (start : Cfg Γ Λ R) (n : Nat) (finish : Cfg Γ Λ R) : Prop :=
  (next caller)^[n] (some start) = some finish ∧ finish.l = none ∧
    ∀ j, j < n → ∃ reached,
      (next caller)^[j] (some start) = some reached ∧ Owned reached.l

theorem cfg_first_return (start : Cfg Γ Λ R) :
    FirstBoundary caller start (remainingSteps start) (finalCfg start) :=
  ⟨cfg_iterate caller start, finalCfg_not_owned start,
    (cfg_localRun caller start).owned_prefix caller⟩

theorem first_boundary_iff (start finish : Cfg Γ Λ R) (n : Nat) :
    FirstBoundary caller start n finish ↔ n = remainingSteps start ∧ finish = finalCfg start := by
  constructor
  · rintro ⟨executed, nonowned, earlier⟩
    exact LocalRun.first_unique caller (LocalRun.of_iterate caller executed earlier)
      (cfg_localRun caller start) nonowned (finalCfg_not_owned start)
  · rintro ⟨rfl, rfl⟩
    exact cfg_first_return caller start

theorem first_halt_iff (start finish : Cfg Γ Λ R) (n : Nat) :
    FirstHalt caller start n finish ↔
      n = remainingSteps start ∧ finish = finalCfg start ∧ (finalCfg start).l = none := by
  constructor
  · rintro ⟨executed, halted, earlier⟩
    have nonowned : ¬ Owned finish.l := by rw [halted]; exact not_owned_none
    rcases (first_boundary_iff caller start finish n).mp ⟨executed, nonowned, earlier⟩ with ⟨count, same⟩
    exact ⟨count, same, same ▸ halted⟩
  · rintro ⟨rfl, rfl, halted⟩
    exact ⟨cfg_iterate caller start, halted, (cfg_localRun caller start).owned_prefix caller⟩

omit caller [DecidableEq K] in
theorem finalCfg_halted_of_owned (start : Cfg Γ Λ R) (owned : Owned start.l) :
    (finalCfg start).l = none := by
  obtain ⟨q, regs, D, ctx, rfl⟩ := owned_cases start owned
  rw [finalCfg_phase_cfg]
  rfl

theorem cfg_first_halt (start : Cfg Γ Λ R) (owned : Owned start.l) :
    FirstHalt caller start (remainingSteps start) (finalCfg start) :=
  (first_halt_iff caller start (finalCfg start) (remainingSteps start)).mpr
    ⟨rfl, rfl, finalCfg_halted_of_owned start owned⟩

theorem phase_first_halt (q : Phase) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    FirstHalt caller (cfg (some (phaseLabel q)) regs D ctx) (phaseSteps q D) (phaseResult q regs D ctx) := by
  simpa only [remainingSteps_phase_cfg, finalCfg_phase_cfg] using
    cfg_first_halt caller (cfg (some (phaseLabel q)) regs D ctx) (owned_phase q)

theorem next_iterate_none (n : Nat) :
    (next caller)^[n] (none : Option (Cfg Γ Λ R)) = none := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, next_none]

theorem step_live_halt (c : Cfg Γ Λ R) (halted : c.l = none) : step caller c = none := by
  rcases c with ⟨label, regs, storage⟩
  change label = none at halted
  subst label
  rfl

theorem cfg_halt_then_none (start : Cfg Γ Λ R) (halted : (finalCfg start).l = none) :
    (next caller)^[remainingSteps start + 1] (some start) = none := by
  rw [Function.iterate_succ_apply', cfg_iterate, next_some, step_live_halt caller _ halted]

theorem cfg_after_halt (start : Cfg Γ Λ R) (halted : (finalCfg start).l = none)
    (n : Nat) (strict : remainingSteps start < n) :
    (next caller)^[n] (some start) = none := by
  have count : n = (n - (remainingSteps start + 1)) + (remainingSteps start + 1) := by omega
  rw [count, Function.iterate_add_apply, cfg_halt_then_none caller start halted, next_iterate_none]

theorem phase_after_halt (q : Phase) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (n : Nat) (strict : phaseSteps q D < n) :
    (next caller)^[n] (some (cfg (some (phaseLabel q)) regs D ctx)) = none :=
  cfg_after_halt caller _ (finalCfg_halted_of_owned _ (owned_phase q)) n
    (by simpa only [remainingSteps_phase_cfg] using strict)

/-- Owned program agreement suffices at every later time from an owned entry. -/
theorem owned_iterate_caller_independent (other : Λ → Statement Γ Λ R)
    (start : Cfg Γ Λ R) (owned : Owned start.l) (n : Nat) :
    (next caller)^[n] (some start) = (next other)^[n] (some start) := by
  by_cases early : n ≤ remainingSteps start
  · exact prefix_caller_independent caller other start n early
  · have halted := finalCfg_halted_of_owned start owned
    rw [cfg_after_halt caller start halted n (by omega),
      cfg_after_halt other start halted n (by omega)]

theorem ambient_owned_iterate_eq (ambient : Label Λ → Statement Γ Λ R)
    (agrees : ∀ q, ambient (phaseLabel q) = program (fun _ => .halt) (phaseLabel q))
    (start : Cfg Γ Λ R) (owned : Owned start.l) (n : Nat) :
    (fun c : Option (Cfg Γ Λ R) => c.bind (Turing.TM2.step ambient))^[n] (some start) =
      (next caller)^[n] (some start) := by
  rw [program_eq_of_agrees ambient agrees]
  exact owned_iterate_caller_independent _ caller start owned n

def phaseInTime (q : Phase) (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller) (cfg (some (phaseLabel q)) regs D ctx)
      (some (phaseResult q regs D ctx)) (phaseSteps q D) where
  steps := phaseSteps q D
  evals_in_steps := phase_iterate caller q D regs ctx
  steps_le_m := Nat.le_refl _

@[simp] theorem phaseInTime_steps (q : Phase) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) : (phaseInTime caller q D regs ctx).steps = phaseSteps q D := rfl

def cfgInTime (start : Cfg Γ Λ R) :
    StateTransition.EvalsToInTime (step caller) start (some (finalCfg start)) (remainingSteps start) where
  steps := remainingSteps start
  evals_in_steps := cfg_iterate caller start
  steps_le_m := Nat.le_refl _

@[simp] theorem cfgInTime_steps (start : Cfg Γ Λ R) :
    (cfgInTime caller start).steps = remainingSteps start := rfl

def haltNoneInTime (start : Cfg Γ Λ R) (halted : (finalCfg start).l = none) :
    StateTransition.EvalsToInTime (step caller) start none (remainingSteps start + 1) where
  steps := remainingSteps start + 1
  evals_in_steps := cfg_halt_then_none caller start halted
  steps_le_m := Nat.le_refl _

@[simp] theorem haltNoneInTime_steps (start : Cfg Γ Λ R) (halted : (finalCfg start).l = none) :
    (haltNoneInTime caller start halted).steps = remainingSteps start + 1 := rfl

omit caller [DecidableEq K] in
theorem evaluate_frontEnd (q : FrontEndMachine.OwnedLabels) (a : Bool) (D : LocalData) :
    evaluate (frontEndPhase q) a D = frontEndEvaluation q D := by
  change (match frontEndClass (frontEndControl (.inl q)) with
    | .inl q => frontEndEvaluation q D
    | .inr false => answerEvaluation false D
    | .inr true => dispatchEvaluation D) = _
  rw [frontEndClass_control]

omit caller [DecidableEq K] in
theorem evaluate_reject (a : Bool) (D : LocalData) :
    evaluate rejectPhase a D = answerEvaluation false D := rfl

omit caller [DecidableEq K] in
theorem evaluate_dispatch (a : Bool) (D : LocalData) :
    evaluate dispatchPhase a D = dispatchEvaluation D := rfl

omit caller [DecidableEq K] in
theorem evaluate_stream (q : StreamMachine.Phase) (a : Bool) (D : LocalData) :
    evaluate (streamPhase q) a D = streamEvaluation q D := by
  change (match streamClass (streamControl (.inl q)) with
    | .inl q => streamEvaluation q D
    | .inr b => answerEvaluation b D) = _
  rw [streamClass_control]

omit caller [DecidableEq K] in
theorem evaluate_result (b a : Bool) (D : LocalData) :
    evaluate (resultPhase b) a D = answerEvaluation b D := rfl

omit caller [DecidableEq K] in
theorem evaluate_clear (i : Fin 16) (a : Bool) (D : LocalData) :
    evaluate (clearPhase i) a D = ⟨cleanupSteps i D, cleanupData i a D⟩ := rfl

omit caller [DecidableEq K] in
theorem evaluate_emit (a : Bool) (D : LocalData) :
    evaluate emitPhase a D = ⟨1, emitData a D⟩ := rfl

omit caller [DecidableEq K] in
theorem phaseSteps_frontEnd (q : FrontEndMachine.OwnedLabels) (D : LocalData) :
    phaseSteps (frontEndPhase q) D =
      (DirtyFrontEnd.frontEndPhaseFinish q (frontEndData D)).steps +
      (match (DirtyFrontEnd.frontEndPhaseFinish q (frontEndData D)).result with
        | .success => (dispatchEvaluation (frontEndFinishData q D)).steps
        | .failure => (answerEvaluation false (frontEndFinishData q D)).steps) := by
  rw [phaseSteps, evaluate_frontEnd]
  unfold frontEndEvaluation
  dsimp only [addSteps]
  cases (DirtyFrontEnd.frontEndPhaseFinish q (frontEndData D)).result <;> rfl

omit caller [DecidableEq K] in
theorem phaseSteps_reject (D : LocalData) : phaseSteps rejectPhase D = localCells D + 18 := by
  simp only [phaseSteps, evaluate_reject, answerEvaluation, cleanupSteps_zero]
  omega

omit caller [DecidableEq K] in
theorem phaseSteps_dispatch (D : LocalData) :
    phaseSteps dispatchPhase D =
      StreamMachine.phaseSteps StreamMachine.inspectPhase (streamData D) +
      localCells (withStream D (StreamMachine.evaluate StreamMachine.inspectPhase (streamData D)).data) + 19 := by
  simp only [phaseSteps, evaluate_dispatch, dispatchEvaluation, streamEvaluation, answerEvaluation,
    addSteps, cleanupSteps_zero, StreamMachine.phaseSteps]
  omega

omit caller [DecidableEq K] in
theorem phaseSteps_stream (q : StreamMachine.Phase) (D : LocalData) :
    phaseSteps (streamPhase q) D = StreamMachine.phaseSteps q (streamData D) +
      localCells (withStream D (StreamMachine.evaluate q (streamData D)).data) + 18 := by
  simp only [phaseSteps, evaluate_stream, streamEvaluation, answerEvaluation, addSteps,
    cleanupSteps_zero, StreamMachine.phaseSteps]
  omega

omit caller [DecidableEq K] in
theorem phaseSteps_result (b : Bool) (D : LocalData) :
    phaseSteps (resultPhase b) D = localCells D + 18 := by
  simp only [phaseSteps, evaluate_result, answerEvaluation, cleanupSteps_zero]
  omega

omit caller [DecidableEq K] in
theorem phaseSteps_clear (i : Fin 16) (D : LocalData) : phaseSteps (clearPhase i) D = cleanupSteps i D := rfl

omit caller [DecidableEq K] in
theorem phaseSteps_emit (D : LocalData) : phaseSteps emitPhase D = 1 := rfl

omit caller [DecidableEq K] in
theorem phaseResult_frontEnd (q : FrontEndMachine.OwnedLabels) (regs : Registers R) (D : LocalData)
    (ctx : ∀ k, List (Γ k)) :
    phaseResult (Λ := Λ) (frontEndPhase q) regs D ctx =
      cfg none (fullReset regs) (frontEndEvaluation q D).data ctx := by
  rw [phaseResult, evaluate_frontEnd]
  rfl

omit caller [DecidableEq K] in
theorem phaseResult_reject (regs : Registers R) (D : LocalData) (ctx : ∀ k, List (Γ k)) :
    phaseResult (Λ := Λ) rejectPhase regs D ctx = cfg none (fullReset regs) { fuel := [false] } ctx := by
  simp only [phaseResult, evaluate_reject, evaluationCfg, answerEvaluation, cleanupData_zero]

omit caller [DecidableEq K] in
theorem phaseResult_dispatch (regs : Registers R) (D : LocalData) (ctx : ∀ k, List (Γ k)) :
    phaseResult (Λ := Λ) dispatchPhase regs D ctx = cfg none (fullReset regs)
      { fuel := [(StreamMachine.evaluate StreamMachine.inspectPhase (streamData D)).result] } ctx := by
  simp only [phaseResult, evaluate_dispatch, evaluationCfg, dispatchEvaluation, streamEvaluation,
    answerEvaluation, addSteps, cleanupData_zero]

omit caller [DecidableEq K] in
theorem phaseResult_stream (q : StreamMachine.Phase) (regs : Registers R) (D : LocalData)
    (ctx : ∀ k, List (Γ k)) :
    phaseResult (Λ := Λ) (streamPhase q) regs D ctx = cfg none (fullReset regs)
      { fuel := [(StreamMachine.evaluate q (streamData D)).result] } ctx := by
  simp only [phaseResult, evaluate_stream, evaluationCfg, streamEvaluation, answerEvaluation,
    addSteps, cleanupData_zero]

omit caller [DecidableEq K] in
theorem phaseResult_result (b : Bool) (regs : Registers R) (D : LocalData) (ctx : ∀ k, List (Γ k)) :
    phaseResult (Λ := Λ) (resultPhase b) regs D ctx = cfg none (fullReset regs) { fuel := [b] } ctx := by
  simp only [phaseResult, evaluate_result, evaluationCfg, answerEvaluation, cleanupData_zero]

omit caller [DecidableEq K] in
theorem phaseResult_clear (i : Fin 16) (regs : Registers R) (D : LocalData) (ctx : ∀ k, List (Γ k)) :
    phaseResult (Λ := Λ) (clearPhase i) regs D ctx =
      cfg none (fullReset regs) (cleanupData i (answer regs) D) ctx := rfl

omit caller [DecidableEq K] in
theorem phaseResult_emit (regs : Registers R) (D : LocalData) (ctx : ∀ k, List (Γ k)) :
    phaseResult (Λ := Λ) emitPhase regs D ctx =
      cfg none (fullReset regs) (emitData (answer regs) D) ctx := rfl

def frontEndInTime (q : FrontEndMachine.OwnedLabels) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller)
      (cfg (some (phaseLabel (frontEndPhase q))) regs D ctx)
      (some (frontEndComponentCfg q D regs ctx)) (DirtyFrontEnd.frontEndPhaseSteps q (frontEndData D)) where
  steps := DirtyFrontEnd.frontEndPhaseSteps q (frontEndData D)
  evals_in_steps := (frontEnd_phase_localRun caller q D regs ctx).iterate caller
  steps_le_m := Nat.le_refl _

@[simp] theorem frontEndInTime_steps (q : FrontEndMachine.OwnedLabels) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    (frontEndInTime caller q D regs ctx).steps = DirtyFrontEnd.frontEndPhaseSteps q (frontEndData D) := rfl

def streamInTime (q : StreamMachine.Phase) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller)
      (cfg (some (phaseLabel (streamPhase q))) regs D ctx)
      (some (cfg (some (phaseLabel (resultPhase (StreamMachine.evaluate q (streamData D)).result)))
        (streamReset regs) (withStream D (StreamMachine.evaluate q (streamData D)).data) ctx))
      (StreamMachine.phaseSteps q (streamData D)) where
  steps := StreamMachine.phaseSteps q (streamData D)
  evals_in_steps := (stream_phase_localRun caller q D regs ctx).iterate caller
  steps_le_m := Nat.le_refl _

@[simp] theorem streamInTime_steps (q : StreamMachine.Phase) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    (streamInTime caller q D regs ctx).steps = StreamMachine.phaseSteps q (streamData D) := rfl

theorem clear_first_return (i : Fin 16) (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    FirstHalt caller (cfg (some (clearLabel i)) regs D ctx) (cleanupSteps i D)
      (cfg none (fullReset regs) (cleanupData i (answer regs) D) ctx) :=
  phase_first_halt caller (clearPhase i) D regs ctx

theorem emit_first_return (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    FirstHalt caller (cfg (some emitLabel) regs D ctx) 1
      (cfg none (fullReset regs) (emitData (answer regs) D) ctx) :=
  phase_first_halt caller emitPhase D regs ctx

theorem clear_first_return_unique (i : Fin 16) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (n : Nat) (finish : Cfg Γ Λ R) :
    FirstHalt caller (cfg (some (clearLabel i)) regs D ctx) n finish ↔
      n = cleanupSteps i D ∧ finish = cfg none (fullReset regs) (cleanupData i (answer regs) D) ctx := by
  change FirstHalt caller (cfg (some (phaseLabel (clearPhase i))) regs D ctx) n finish ↔ _
  rw [first_halt_iff caller, remainingSteps_phase_cfg, finalCfg_phase_cfg]
  simp only [phaseSteps_clear, phaseResult_clear, cfg, and_true]

theorem emit_first_return_unique (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (n : Nat) (finish : Cfg Γ Λ R) :
    FirstHalt caller (cfg (some emitLabel) regs D ctx) n finish ↔
      n = 1 ∧ finish = cfg none (fullReset regs) (emitData (answer regs) D) ctx := by
  change FirstHalt caller (cfg (some (phaseLabel emitPhase)) regs D ctx) n finish ↔ _
  rw [first_halt_iff caller, remainingSteps_phase_cfg, finalCfg_phase_cfg]
  simp only [phaseSteps_emit, phaseResult_emit, cfg, and_true]

open Trees.Rotations (RotationMove applyMoves?)

omit caller [DecidableEq K] in
theorem runSteps_frameFailure (raw : Bits)
    (returned : FrontEndMachine.sourceOutcome raw = .frameFailure) :
    runSteps raw = FrontEndMachine.runSteps raw + 18 := by
  simp only [runSteps, runEvaluation, addSteps, returned, outcomeContinuation, answerEvaluation,
    cleanupSteps_zero, frontEndOutcomeData, localCells, List.length_nil]

omit caller [DecidableEq K] in
theorem runSteps_inputDecodeFailure (raw cert : Bits)
    (returned : FrontEndMachine.sourceOutcome raw = .inputDecodeFailure cert) :
    runSteps raw = FrontEndMachine.runSteps raw + cert.length + 18 := by
  simp only [runSteps, runEvaluation, addSteps, returned, outcomeContinuation, answerEvaluation,
    cleanupSteps_zero, frontEndOutcomeData, localCells, List.length_nil]
  omega

omit caller [DecidableEq K] in
theorem runSteps_inputParseFailure (raw : Bits) (input : Word) (cert : Bits)
    (returned : FrontEndMachine.sourceOutcome raw = .inputParseFailure input cert) :
    runSteps raw = FrontEndMachine.runSteps raw + input.length + cert.length + 18 := by
  simp only [runSteps, runEvaluation, addSteps, returned, outcomeContinuation, answerEvaluation,
    cleanupSteps_zero, frontEndOutcomeData, localCells, List.length_nil]
  omega

omit caller [DecidableEq K] in
theorem runSteps_certificateDecodeFailure (raw : Bits) (source target : BinaryTree Unit) (fuel : Bits)
    (returned : FrontEndMachine.sourceOutcome raw = .certificateDecodeFailure source target fuel) :
    runSteps raw = FrontEndMachine.runSteps raw + (treeCode source).length + (treeCode target).length + fuel.length + 18 := by
  simp only [runSteps, runEvaluation, addSteps, returned, outcomeContinuation, answerEvaluation,
    cleanupSteps_zero, frontEndOutcomeData, localCells, List.length_nil]
  omega

omit caller [DecidableEq K] in
theorem runSteps_accepting_code (source target : BinaryTree Unit) (fuel : Bits) (cert : Word)
    (accepted : (checkStreamRun fuel source target cert).1 = true) :
    runSteps (BitPairFraming.frame (wordBits (inputCode source target fuel)) (wordBits cert)) =
      12 * (inputCode source target fuel).length + 10 * cert.length +
      StreamMachine.runSteps fuel cert (treeCode source) (treeCode target) + fuel.length + 30 := by
  have machineAccepted : (StreamMachine.runEvaluation fuel cert (treeCode source) (treeCode target)).result = true := by
    rwa [StreamMachine.runEvaluation_code_value]
  obtain ⟨finalFuel, data, width⟩ := StreamMachine.run_accept_cleanup fuel cert
    (treeCode source) (treeCode target) machineAccepted
  rw [runSteps_code, data]
  simp only [StreamMachine.localCells, StreamMachine.cleanData, List.length_nil, Nat.zero_add, Nat.add_zero, width]

omit caller [DecidableEq K] in
theorem clean_canonical_evaluation (raw : Bits) :
    phaseSteps entryPhase (cleanData raw) = runSteps raw ∧
      (evaluate entryPhase false (cleanData raw)).data = (runEvaluation raw).data := by
  let localCaller : Empty → Statement (fun _ : Empty => Empty) Empty Unit := fun _ => .halt
  let regs : Registers Unit := ((none, none), BitDecoderMachine.zeroRegisters, (none, ()))
  let ctx : Empty → List Empty := fun k => Empty.elim k
  have endpoints := (run_localRun localCaller regs raw ctx).phase_endpoint localCaller rfl
  refine ⟨endpoints.1, ?_⟩
  have same := congrArg dataOfCfg endpoints.2
  change (evaluate entryPhase (answer regs) (cleanData raw)).data = (runEvaluation raw).data at same
  have savedAnswer : answer regs = false := rfl
  rwa [savedAnswer] at same

omit caller [DecidableEq K] in
theorem remainingSteps_entry (regs : Registers R) (raw : Bits) (ctx : ∀ k, List (Γ k)) :
    remainingSteps (entry (Λ := Λ) regs raw ctx) = runSteps raw := by
  exact (remainingSteps_phase_cfg entryPhase (cleanData raw) regs ctx).trans
    (clean_canonical_evaluation raw).1

omit caller [DecidableEq K] in
theorem finalCfg_entry (regs : Registers R) (raw : Bits) (ctx : ∀ k, List (Γ k)) :
    finalCfg (entry (Λ := Λ) regs raw ctx) = runResult regs raw ctx := by
  rw [entry, finalCfg_phase_cfg]
  change cfg none (fullReset regs) (evaluate entryPhase false (cleanData raw)).data ctx =
    cfg none (fullReset regs) (runEvaluation raw).data ctx
  rw [(clean_canonical_evaluation raw).2]

theorem run_first_halt (regs : Registers R) (raw : Bits) (ctx : ∀ k, List (Γ k)) :
    FirstHalt caller (entry regs raw ctx) (runSteps raw) (runResult regs raw ctx) :=
  ⟨run_iterate caller regs raw ctx, rfl, (run_localRun caller regs raw ctx).owned_prefix caller⟩

theorem run_first_halt_iff (regs : Registers R) (raw : Bits) (ctx : ∀ k, List (Γ k))
    (n : Nat) (finish : Cfg Γ Λ R) :
    FirstHalt caller (entry regs raw ctx) n finish ↔
      n = runSteps raw ∧
      finish = cfg none (fullReset regs) { fuel := [BitPairFraming.verifyFramed raw] } ctx := by
  rw [first_halt_iff caller, remainingSteps_entry, finalCfg_entry, runResult_eq]
  simp only [cfg, and_true]

theorem run_verifyFramed (regs : Registers R) (raw : Bits) (ctx : ∀ k, List (Γ k)) :
    FirstHalt caller (entry regs raw ctx) (runSteps raw)
      (cfg none (fullReset regs) { fuel := [BitPairFraming.verifyFramed raw] } ctx) := by
  rw [← runResult_eq]
  exact run_first_halt caller regs raw ctx

theorem run_accept_iff (regs : Registers R) (raw : Bits) (ctx : ∀ k, List (Γ k)) :
    (∃ n finish, FirstHalt caller (entry regs raw ctx) n finish ∧ finish.stk (.inl .fuel) = [true]) ↔
      ∃ (source target : BinaryTree Unit) (fuel : Bits) (moves : List RotationMove),
        raw = BitPairFraming.frame (wordBits (inputCode source target fuel)) (wordBits (certCode moves)) ∧
        applyMoves? moves source = some target ∧ moves.length ≤ Resources.BinaryCounter.value fuel := by
  rw [← BitPairFraming.verifyFramed_accept_iff_trace]
  constructor
  · rintro ⟨n, finish, first, output⟩
    obtain ⟨_, rfl⟩ := (run_first_halt_iff caller regs raw ctx n finish).mp first
    simpa only [cfg, stores, FrontEndMachine.stores, frontEndData, List.cons.injEq, and_true] using output
  · intro accepted
    refine ⟨runSteps raw, runResult regs raw ctx, run_first_halt caller regs raw ctx, ?_⟩
    rw [runResult_eq, accepted]
    rfl

theorem run_earlier_owned (regs : Registers R) (raw : Bits) (ctx : ∀ k, List (Γ k))
    (n : Nat) (strict : n < runSteps raw) :
    ∃ reached, (next caller)^[n] (some (entry regs raw ctx)) = some reached ∧ Owned reached.l :=
  (run_localRun caller regs raw ctx).owned_prefix caller n strict

theorem run_outer_none (regs : Registers R) (raw : Bits) (ctx : ∀ k, List (Γ k)) :
    (next caller)^[runSteps raw + 1] (some (entry regs raw ctx)) = none := by
  rw [Function.iterate_succ_apply', run_iterate, next_some]
  exact step_live_halt caller _ rfl

theorem run_after_halt (regs : Registers R) (raw : Bits) (ctx : ∀ k, List (Γ k))
    (n : Nat) (strict : runSteps raw < n) :
    (next caller)^[n] (some (entry regs raw ctx)) = none := by
  apply cfg_after_halt caller
  · rw [finalCfg_entry]
    rfl
  · rwa [remainingSteps_entry]

def runInTimeExact (regs : Registers R) (raw : Bits) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller) (entry regs raw ctx)
      (some (runResult regs raw ctx)) (runSteps raw) where
  steps := runSteps raw
  evals_in_steps := run_iterate caller regs raw ctx
  steps_le_m := Nat.le_refl _

def runInTimePolynomial (regs : Registers R) (raw : Bits) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller) (entry regs raw ctx)
      (some (runResult regs raw ctx)) (raw.length * raw.length + 10 * raw.length + 36) where
  steps := runSteps raw
  evals_in_steps := run_iterate caller regs raw ctx
  steps_le_m := runSteps_le raw

@[simp] theorem runInTimeExact_steps (regs : Registers R) (raw : Bits) (ctx : ∀ k, List (Γ k)) :
    (runInTimeExact caller regs raw ctx).steps = runSteps raw := rfl

@[simp] theorem runInTimePolynomial_steps (regs : Registers R) (raw : Bits) (ctx : ∀ k, List (Γ k)) :
    (runInTimePolynomial caller regs raw ctx).steps = runSteps raw := rfl

omit caller [DecidableEq K] in
/-- The source observation records exactly the already measured bit verifier.
Framing failure has no invented bit-verifier invocation. -/
def sourceObservation (raw : Bits) : Option (Bool × Nat) :=
  (BitPairFraming.unframe raw).map (fun pair => verifyBitsRun pair.1 pair.2)

omit caller [DecidableEq K] in
theorem sourceObservation_frameFailure (raw : Bits) (failed : BitPairFraming.unframe raw = none) :
    sourceObservation raw = none := by simp only [sourceObservation, failed, Option.map_none]

omit caller [DecidableEq K] in
theorem sourceObservation_inputDecodeFailure (raw input cert : Bits)
    (framed : BitPairFraming.unframe raw = some (input, cert))
    (failed : (unpackWordRun input).1 = none) :
    sourceObservation raw = some (false, (unpackWordRun input).2 + 2) := by
  simp only [sourceObservation, framed, Option.map_some, verifyBitsRun_input_none input cert failed]

omit caller [DecidableEq K] in
theorem sourceObservation_inputParseFailure (raw input cert : Bits) (word : Word)
    (framed : BitPairFraming.unframe raw = some (input, cert))
    (decoded : (unpackWordRun input).1 = some word) (failed : (parseInputRun word).1 = none) :
    sourceObservation raw = some (false, (unpackWordRun input).2 + (parseInputRun word).2 + 2) := by
  simp only [sourceObservation, framed, Option.map_some,
    verifyBitsRun_parse_none input cert word decoded failed]

omit caller [DecidableEq K] in
theorem sourceObservation_certificateDecodeFailure (raw input cert : Bits) (word : Word)
    (source target : BinaryTree Unit) (fuel : Bits)
    (framed : BitPairFraming.unframe raw = some (input, cert))
    (decoded : (unpackWordRun input).1 = some word)
    (parsed : (parseInputRun word).1 = some (source, target, fuel))
    (failed : (unpackWordRun cert).1 = none) :
    sourceObservation raw = some (false, (unpackWordRun input).2 + (parseInputRun word).2 +
      (unpackWordRun cert).2 + 2) := by
  simp only [sourceObservation, framed, Option.map_some,
    verifyBitsRun_certificate_none input cert word source target fuel decoded parsed failed]

omit caller [DecidableEq K] in
theorem sourceObservation_success (raw input cert : Bits) (word moves : Word)
    (source target : BinaryTree Unit) (fuel : Bits)
    (framed : BitPairFraming.unframe raw = some (input, cert))
    (decoded : (unpackWordRun input).1 = some word)
    (parsed : (parseInputRun word).1 = some (source, target, fuel))
    (certificate : (unpackWordRun cert).1 = some moves) :
    sourceObservation raw = some ((checkStreamRun fuel source target moves).1,
      (unpackWordRun input).2 + (parseInputRun word).2 + (unpackWordRun cert).2 +
        (checkStreamRun fuel source target moves).2 + 1) := by
  simp only [sourceObservation, framed, Option.map_some,
    verifyBitsRun_success input cert word moves source target fuel decoded parsed certificate]

omit caller [DecidableEq K] in
@[simp] theorem remainingSteps_external (label : Λ) (regs : Registers R) (D : LocalData)
    (ctx : ∀ k, List (Γ k)) :
    remainingSteps (cfg (some (callerLabel label)) regs D ctx) = 0 := rfl

omit caller [DecidableEq K] in
@[simp] theorem finalCfg_external (label : Λ) (regs : Registers R) (D : LocalData)
    (ctx : ∀ k, List (Γ k)) :
    finalCfg (cfg (some (callerLabel label)) regs D ctx) = cfg (some (callerLabel label)) regs D ctx := rfl

omit caller [DecidableEq K] in
@[simp] theorem remainingSteps_live_halt (regs : Registers R) (D : LocalData) (ctx : ∀ k, List (Γ k)) :
    remainingSteps (cfg (Λ := Λ) none regs D ctx) = 0 := rfl

omit caller [DecidableEq K] in
@[simp] theorem finalCfg_live_halt (regs : Registers R) (D : LocalData) (ctx : ∀ k, List (Γ k)) :
    finalCfg (cfg (Λ := Λ) none regs D ctx) = cfg none regs D ctx := rfl

theorem external_goto_step (label : Λ) (q : Phase) (regs : Registers R) (D : LocalData)
    (ctx : ∀ k, List (Γ k)) (body : caller label = .goto (fun _ => phaseLabel q)) :
    step caller (cfg (some (callerLabel label)) regs D ctx) =
      some (cfg (some (phaseLabel q)) regs D ctx) := by
  change some (Turing.TM2.stepAux (caller label) regs (stores D ctx)) = _
  rw [body]
  rfl

theorem external_halt_step (label : Λ) (regs : Registers R) (D : LocalData)
    (ctx : ∀ k, List (Γ k)) (body : caller label = .halt) :
    step caller (cfg (some (callerLabel label)) regs D ctx) = some (cfg none regs D ctx) := by
  change some (Turing.TM2.stepAux (caller label) regs (stores D ctx)) = _
  rw [body]
  rfl

/-- A caller can reenter an owned phase in one real activation. Its initial
rank-zero boundary remains the original external configuration; this later
execution is a separate caller-behaviour theorem. -/
theorem external_reentry_iterate (label : Λ) (q : Phase) (regs : Registers R) (D : LocalData)
    (ctx : ∀ k, List (Γ k)) (body : caller label = .goto (fun _ => phaseLabel q)) :
    (next caller)^[1 + phaseSteps q D] (some (cfg (some (callerLabel label)) regs D ctx)) =
      some (phaseResult q regs D ctx) := by
  rw [Nat.add_comm 1, iterate_step caller _ _ _ (external_goto_step caller label q regs D ctx body)]
  exact phase_iterate caller q D regs ctx

def externalReentryInTime (label : Λ) (q : Phase) (regs : Registers R) (D : LocalData)
    (ctx : ∀ k, List (Γ k)) (body : caller label = .goto (fun _ => phaseLabel q)) :
    StateTransition.EvalsToInTime (step caller) (cfg (some (callerLabel label)) regs D ctx)
      (some (phaseResult q regs D ctx)) (1 + phaseSteps q D) where
  steps := 1 + phaseSteps q D
  evals_in_steps := external_reentry_iterate caller label q regs D ctx body
  steps_le_m := Nat.le_refl _

@[simp] theorem externalReentryInTime_steps (label : Λ) (q : Phase) (regs : Registers R)
    (D : LocalData) (ctx : ∀ k, List (Γ k)) (body : caller label = .goto (fun _ => phaseLabel q)) :
    (externalReentryInTime caller label q regs D ctx body).steps = 1 + phaseSteps q D := rfl

theorem prefix_zero (start reached : Cfg Γ Λ R)
    (executed : (next caller)^[0] (some start) = some reached) : reached = start :=
  (Option.some.inj executed).symm

omit caller [DecidableEq K] in
def stateFinalCfg (start : Option (Cfg Γ Λ R)) : Option (Cfg Γ Λ R) := start.map finalCfg

omit caller [DecidableEq K] in
@[simp] theorem stateFinalCfg_none : stateFinalCfg (Γ := Γ) (Λ := Λ) (R := R) none = none := rfl

omit caller [DecidableEq K] in
@[simp] theorem stateFinalCfg_some (start : Cfg Γ Λ R) : stateFinalCfg (some start) = some (finalCfg start) := rfl

theorem state_iterate (start : Option (Cfg Γ Λ R)) :
    (next caller)^[stateRemainingSteps start] start = stateFinalCfg start := by
  cases start with
  | none => rfl
  | some start => exact cfg_iterate caller start

omit caller [DecidableEq K] in
def answerRegistersAt (b : Bool) (regs : Registers R) (D : LocalData) (n : Nat) : Registers R :=
  if n = 0 then regs else cleanupRegistersAt 0 (answerRegisters b regs) D (n - 1)

omit caller [DecidableEq K] in
def streamStageRegistersAt (q : StreamMachine.Phase) (regs : Registers R) (D : LocalData)
    (ctx : ∀ k, List (Γ k)) (n : Nat) : Registers R :=
  StreamMachine.frontEndRegisterEquiv.symm
    (StreamMachine.phaseRegistersAt (Λ := StreamCallerLabel Λ) q
      (StreamMachine.frontEndRegisterEquiv regs) (streamData D) (streamContext D ctx) n)

omit caller [DecidableEq K] in
def streamCompleteRegistersAt (q : StreamMachine.Phase) (regs : Registers R) (D : LocalData)
    (ctx : ∀ k, List (Γ k)) (n : Nat) : Registers R :=
  if n ≤ StreamMachine.phaseSteps q (streamData D)
  then streamStageRegistersAt (Λ := Λ) q regs D ctx n
  else
    let finish := StreamMachine.evaluate q (streamData D)
    answerRegistersAt finish.result (streamReset regs) (withStream D finish.data)
      (n - StreamMachine.phaseSteps q (streamData D))

omit caller [DecidableEq K] in
def dispatchRegistersAt (regs : Registers R) (D : LocalData)
    (ctx : ∀ k, List (Γ k)) (n : Nat) : Registers R :=
  if n = 0 then regs
  else streamCompleteRegistersAt (Λ := Λ) StreamMachine.inspectPhase (fullReset regs) D ctx (n - 1)

omit caller [DecidableEq K] in
def frontEndCompleteRegistersAt (q : FrontEndMachine.OwnedLabels) (regs : Registers R) (D : LocalData)
    (ctx : ∀ k, List (Γ k)) (n : Nat) : Registers R :=
  if n ≤ DirtyFrontEnd.frontEndPhaseSteps q (frontEndData D)
  then DirtyFrontEnd.frontEndPhaseRegisters q (frontEndData D) regs n
  else
    let finish := DirtyFrontEnd.frontEndPhaseFinish q (frontEndData D)
    let outRegs := frontEndFinishRegisters q D regs
    let outData := frontEndFinishData q D
    match finish.result with
    | .success => dispatchRegistersAt (Λ := Λ) outRegs outData ctx (n - finish.steps)
    | .failure => answerRegistersAt false outRegs outData (n - finish.steps)

omit caller [DecidableEq K] in
def phaseRegistersAt (q : Phase) (regs : Registers R) (D : LocalData)
    (ctx : ∀ k, List (Γ k)) (n : Nat) : Registers R := match q with
  | .inl q => match frontEndClass q with
    | .inl q => frontEndCompleteRegistersAt (Λ := Λ) q regs D ctx n
    | .inr false => answerRegistersAt false regs D n
    | .inr true => dispatchRegistersAt (Λ := Λ) regs D ctx n
  | .inr (.inl q) => match streamClass q with
    | .inl q => streamCompleteRegistersAt (Λ := Λ) q regs D ctx n
    | .inr b => answerRegistersAt b regs D n
  | .inr (.inr (.clear i)) => cleanupRegistersAt i regs D n
  | .inr (.inr .emit) => if n = 0 then regs else fullReset regs

omit caller [DecidableEq K] in
def registersAt (start : Cfg Γ Λ R) (n : Nat) : Registers R := match start.l with
  | some (.inl q) => phaseRegistersAt (Λ := Λ) (.inl q) start.var (dataOfCfg start) (contextOfCfg start) n
  | some (.inr (.inl q)) => phaseRegistersAt (Λ := Λ) (.inr (.inl q)) start.var (dataOfCfg start) (contextOfCfg start) n
  | some (.inr (.inr (.inl q))) => phaseRegistersAt (Λ := Λ) (.inr (.inr q)) start.var (dataOfCfg start) (contextOfCfg start) n
  | _ => start.var

omit caller [DecidableEq K] in
theorem registersAt_phase_cfg (q : Phase) (regs : Registers R) (D : LocalData)
    (ctx : ∀ k, List (Γ k)) (n : Nat) :
    registersAt (cfg (some (phaseLabel (Λ := Λ) q)) regs D ctx) n = phaseRegistersAt (Λ := Λ) q regs D ctx n := by
  rcases q with q | (q | q) <;> rfl

omit caller [DecidableEq K] in
@[simp] theorem user_answerRegisters (b : Bool) (regs : Registers R) : user (answerRegisters b regs) = user regs := rfl

omit caller [DecidableEq K] in
@[simp] theorem user_streamReset (regs : Registers R) : user (streamReset regs) = user regs := rfl

omit caller [DecidableEq K] in
theorem user_frontEndFinishRegisters (q : FrontEndMachine.OwnedLabels) (D : LocalData) (regs : Registers R) :
    user (frontEndFinishRegisters q D regs) = user regs := by
  have h := fullReset_frontEndMaskRegs (DirtyFrontEnd.frontEndPhaseFinish q (frontEndData D)).masks regs
  have projected := congrArg user h
  simpa only [user_fullReset, frontEndFinishRegisters] using projected

omit caller [DecidableEq K] in
theorem frontEndCfg_registers (c : FrontEndCfg Γ Λ R) : (frontEndCfg c).var = c.var := rfl

omit caller [DecidableEq K] in
theorem frontEndCfg_stores (c : FrontEndCfg Γ Λ R) (k : StackId K) :
    (frontEndCfg c).stk k = c.stk k :=
  (FrontEndMachine.Transport.stackEquiv_apply (Equiv.refl _) (fun j => Equiv.refl (alphabet Γ j)) c.stk k).trans
    (List.map_id _)

omit caller [DecidableEq K] in
theorem streamCfg_registers (c : StreamCfg Γ Λ R) :
    (streamCfg c).var = StreamMachine.frontEndRegisterEquiv.symm c.var := rfl

omit caller [DecidableEq K] in
theorem streamCfg_user (c : StreamCfg Γ Λ R) : user (streamCfg c).var = c.var.2.2.2 := rfl

omit caller [DecidableEq K] in
theorem streamCfg_protected (c : StreamCfg Γ Λ R) (k : K) :
    (streamCfg c).stk (.inr (.inr k)) = c.stk (.inr (.inr k)) := by
  have h := FrontEndMachine.Transport.stackEquiv_apply streamStackEquiv streamSymbolEquiv c.stk (.inr (.inr k))
  change (FrontEndMachine.Transport.stackEquiv streamStackEquiv streamSymbolEquiv c.stk)
    (.inr (.inr k)) = (c.stk (.inr (.inr k))).map (Equiv.refl _) at h
  change (FrontEndMachine.Transport.stackEquiv streamStackEquiv streamSymbolEquiv c.stk)
    (.inr (.inr k)) = c.stk (.inr (.inr k))
  simpa only [Equiv.coe_refl, List.map_id] using h

theorem prefix_after_localRun {start middle reached : Cfg Γ Λ R} {ticks n : Nat}
    (segment : LocalRun caller ticks start middle) (late : ticks ≤ n)
    (executed : (next caller)^[n] (some start) = some reached) :
    (next caller)^[n - ticks] (some middle) = some reached := by
  have count : n = (n - ticks) + ticks := by omega
  rw [count, Function.iterate_add_apply, segment.iterate caller] at executed
  exact executed

theorem frontEnd_component_prefix_state (q : FrontEndMachine.OwnedLabels) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (n : Nat) (bound : n ≤ DirtyFrontEnd.frontEndPhaseSteps q (frontEndData D))
    (reached : Cfg Γ Λ R)
    (executed : (next caller)^[n] (some (cfg (some (phaseLabel (frontEndPhase q))) regs D ctx)) = some reached) :
    reached.var = DirtyFrontEnd.frontEndPhaseRegisters q (frontEndData D) regs n ∧
      user reached.var = user regs ∧ ∀ k, reached.stk (.inr (.inr k)) = ctx k := by
  let localCaller : FrontEndMachine.External (FrontEndCallerLabel Λ) → FrontEndStatement Γ Λ R := fun _ => .halt
  let start := FrontEndMachine.cfg (some (FrontEndMachine.ownedLabelEquiv (Λ := FrontEndCallerLabel Λ) q).val)
    regs (frontEndData D) (frontEndContext D ctx)
  have trace := DirtyFrontEnd.frontEnd_phase_trace localCaller q (frontEndData D) regs (frontEndContext D ctx)
  have localReached : ∃ c, (FrontEndMachine.next localCaller)^[n] (some start) = some c := by
    by_cases strict : n < DirtyFrontEnd.frontEndPhaseSteps q (frontEndData D)
    · obtain ⟨c, run, _⟩ := trace.owned_prefix n strict
      exact ⟨c, run⟩
    · have same : n = DirtyFrontEnd.frontEndPhaseSteps q (frontEndData D) := by omega
      subst n
      exact ⟨_, trace.run⟩
  obtain ⟨localReached, localRun⟩ := localReached
  have transported := frontEnd_prefix_transport caller localCaller n start
    (fun j earlier => trace.owned_prefix j (by omega))
  have startEq := frontEndCfg_view (Λ := Λ) (some (FrontEndMachine.ownedLabelEquiv q).val) regs D ctx
  simp only [Option.map_some, frontEndLabelEquiv_owned] at startEq
  change frontEndCfg start = _ at startEq
  rw [localRun, startEq] at transported
  have same := Option.some.inj (transported.symm.trans executed)
  subst reached
  have state := DirtyFrontEnd.frontEnd_phase_prefix_state localCaller q (frontEndData D) regs
    (frontEndContext D ctx) n bound localReached localRun
  refine ⟨state.1, ?_, ?_⟩
  · rw [frontEndCfg_registers, state.1]
    exact congrArg Prod.snd (DirtyFrontEnd.frontEndPhaseRegisters_caller q (frontEndData D) regs n)
  · intro k
    rw [frontEndCfg_stores]
    exact state.2 (.inr k)

theorem stream_component_prefix_state (q : StreamMachine.Phase) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (n : Nat) (bound : n ≤ StreamMachine.phaseSteps q (streamData D))
    (reached : Cfg Γ Λ R)
    (executed : (next caller)^[n] (some (cfg (some (phaseLabel (streamPhase q))) regs D ctx)) = some reached) :
    reached.var = streamStageRegistersAt (Λ := Λ) q regs D ctx n ∧
      user reached.var = user regs ∧ ∀ k, reached.stk (.inr (.inr k)) = ctx k := by
  let localCaller : StreamMachine.External (StreamCallerLabel Λ) → StreamStatement Γ Λ R := fun _ => .halt
  let start := StreamMachine.cfg (some (StreamMachine.phaseLabel (Λ := StreamCallerLabel Λ) q))
    (StreamMachine.frontEndRegisterEquiv regs) (streamData D) (streamContext D ctx)
  have bounded : n ≤ StreamMachine.remainingSteps start := by
    simpa only [start, StreamMachine.remainingSteps_phase_cfg] using bound
  obtain ⟨localReached, localRun, _, _, _⟩ := StreamMachine.owned_prefix localCaller start n bounded
  have trace := StreamMachine.phase_localRun localCaller q (streamData D)
    (StreamMachine.frontEndRegisterEquiv regs) (streamContext D ctx)
  have transported := stream_prefix_transport caller localCaller n start
    (fun j earlier => trace.owned_prefix localCaller j (by omega))
  have startEq := streamCfg_view (Λ := Λ) (some (StreamMachine.phaseLabel q)) regs D ctx
  simp only [Option.map_some, streamLabelEquiv_phase] at startEq
  change streamCfg start = _ at startEq
  rw [localRun, startEq] at transported
  have same := Option.some.inj (transported.symm.trans executed)
  subst reached
  have reset := StreamMachine.phase_prefix_reset localCaller q (streamData D)
    (StreamMachine.frontEndRegisterEquiv regs) (streamContext D ctx) n localReached bound localRun
  have frame := StreamMachine.prefix_frame localCaller start localReached n bounded localRun
  refine ⟨congrArg StreamMachine.frontEndRegisterEquiv.symm reset, ?_, ?_⟩
  · change localReached.var.2.2.2 = user regs
    have retainedUser := congrArg Prod.snd frame.1
    exact retainedUser
  · intro k
    rw [streamCfg_protected]
    exact frame.2 (.inr k)

theorem result_prefix_state (b : Bool) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (n : Nat) (bound : n ≤ (answerEvaluation b D).steps)
    (reached : Cfg Γ Λ R)
    (executed : (next caller)^[n] (some (cfg (some (phaseLabel (resultPhase b))) regs D ctx)) = some reached) :
    reached.var = answerRegistersAt b regs D n ∧ user reached.var = user regs ∧
      ∀ k, reached.stk (.inr (.inr k)) = ctx k := by
  by_cases zero : n = 0
  · subst n
    have same := Option.some.inj executed
    subst reached
    exact ⟨rfl, rfl, fun _ => rfl⟩
  · have segment := phase_step_localRun caller (result_step caller b D regs ctx)
    have later := prefix_after_localRun caller segment (by omega) executed
    have bounded : n - 1 ≤ cleanupSteps 0 D := by change n ≤ 1 + cleanupSteps 0 D at bound; omega
    have state := cleanup_prefix_registers caller 0 D (answerRegisters b regs) ctx (n - 1) bounded reached later
    simpa only [answerRegistersAt, zero, ite_false, user_answerRegisters] using state

theorem reject_prefix_state (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (n : Nat) (bound : n ≤ (answerEvaluation false D).steps)
    (reached : Cfg Γ Λ R)
    (executed : (next caller)^[n] (some (cfg (some (phaseLabel rejectPhase)) regs D ctx)) = some reached) :
    reached.var = answerRegistersAt false regs D n ∧ user reached.var = user regs ∧
      ∀ k, reached.stk (.inr (.inr k)) = ctx k := by
  by_cases zero : n = 0
  · subst n
    have same := Option.some.inj executed
    subst reached
    exact ⟨rfl, rfl, fun _ => rfl⟩
  · have segment := phase_step_localRun caller (reject_step caller D regs ctx)
    have later := prefix_after_localRun caller segment (by omega) executed
    have bounded : n - 1 ≤ cleanupSteps 0 D := by change n ≤ 1 + cleanupSteps 0 D at bound; omega
    have state := cleanup_prefix_registers caller 0 D (answerRegisters false regs) ctx (n - 1) bounded reached later
    simpa only [answerRegistersAt, zero, ite_false, user_answerRegisters] using state

theorem stream_complete_prefix_state (q : StreamMachine.Phase) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (n : Nat) (bound : n ≤ (streamEvaluation q D).steps)
    (reached : Cfg Γ Λ R)
    (executed : (next caller)^[n] (some (cfg (some (phaseLabel (streamPhase q))) regs D ctx)) = some reached) :
    reached.var = streamCompleteRegistersAt (Λ := Λ) q regs D ctx n ∧ user reached.var = user regs ∧
      ∀ k, reached.stk (.inr (.inr k)) = ctx k := by
  by_cases early : n ≤ StreamMachine.phaseSteps q (streamData D)
  · simpa only [streamCompleteRegistersAt, early, ite_true] using
      stream_component_prefix_state caller q D regs ctx n early reached executed
  · have later := prefix_after_localRun caller (stream_phase_localRun caller q D regs ctx) (by omega) executed
    let E := StreamMachine.evaluate q (streamData D)
    have bounded : n - StreamMachine.phaseSteps q (streamData D) ≤ (answerEvaluation E.result (withStream D E.data)).steps := by
      change n ≤ E.steps + (answerEvaluation E.result (withStream D E.data)).steps at bound
      change n - E.steps ≤ _
      omega
    have state := result_prefix_state caller E.result (withStream D E.data) (streamReset regs) ctx
      (n - StreamMachine.phaseSteps q (streamData D)) bounded reached later
    simpa only [streamCompleteRegistersAt, early, ite_false, user_streamReset] using state

theorem dispatch_prefix_state (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (n : Nat) (bound : n ≤ (dispatchEvaluation D).steps)
    (reached : Cfg Γ Λ R)
    (executed : (next caller)^[n] (some (cfg (some (phaseLabel dispatchPhase)) regs D ctx)) = some reached) :
    reached.var = dispatchRegistersAt (Λ := Λ) regs D ctx n ∧ user reached.var = user regs ∧
      ∀ k, reached.stk (.inr (.inr k)) = ctx k := by
  by_cases zero : n = 0
  · subst n
    have same := Option.some.inj executed
    subst reached
    exact ⟨rfl, rfl, fun _ => rfl⟩
  · have later := prefix_after_localRun caller (phase_step_localRun caller (dispatch_step caller D regs ctx))
      (by omega) executed
    have bounded : n - 1 ≤ (streamEvaluation StreamMachine.inspectPhase D).steps := by
      change n ≤ 1 + (streamEvaluation StreamMachine.inspectPhase D).steps at bound
      omega
    have state := stream_complete_prefix_state caller StreamMachine.inspectPhase D (fullReset regs) ctx
      (n - 1) bounded reached later
    simpa only [dispatchRegistersAt, zero, ite_false, user_fullReset] using state

theorem frontEnd_complete_prefix_state (q : FrontEndMachine.OwnedLabels) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (n : Nat) (bound : n ≤ (frontEndEvaluation q D).steps)
    (reached : Cfg Γ Λ R)
    (executed : (next caller)^[n] (some (cfg (some (phaseLabel (frontEndPhase q))) regs D ctx)) = some reached) :
    reached.var = frontEndCompleteRegistersAt (Λ := Λ) q regs D ctx n ∧ user reached.var = user regs ∧
      ∀ k, reached.stk (.inr (.inr k)) = ctx k := by
  by_cases early : n ≤ DirtyFrontEnd.frontEndPhaseSteps q (frontEndData D)
  · simpa only [frontEndCompleteRegistersAt, early, ite_true] using
      frontEnd_component_prefix_state caller q D regs ctx n early reached executed
  · have later := prefix_after_localRun caller (frontEnd_phase_localRun caller q D regs ctx) (by omega) executed
    let finish := DirtyFrontEnd.frontEndPhaseFinish q (frontEndData D)
    have bounded : n - finish.steps ≤ (match finish.result with
        | .success => dispatchEvaluation (frontEndFinishData q D)
        | .failure => answerEvaluation false (frontEndFinishData q D)).steps := by
      change n ≤ finish.steps + (match finish.result with
        | .success => dispatchEvaluation (frontEndFinishData q D)
        | .failure => answerEvaluation false (frontEndFinishData q D)).steps at bound
      omega
    change (next caller)^[n - finish.steps]
      (some (cfg (some (phaseLabel (frontEndResultPhase finish.result)))
        (frontEndFinishRegisters q D regs) (frontEndFinishData q D) ctx)) = some reached at later
    cases result : finish.result with
    | success =>
        rw [result] at later bounded
        have state := dispatch_prefix_state caller (frontEndFinishData q D) (frontEndFinishRegisters q D regs) ctx
          (n - finish.steps) bounded reached later
        change (DirtyFrontEnd.frontEndPhaseFinish q (frontEndData D)).result = .success at result
        simpa only [frontEndCompleteRegistersAt, early, ite_false, result, user_frontEndFinishRegisters] using state
    | failure =>
        rw [result] at later bounded
        have state := reject_prefix_state caller (frontEndFinishData q D) (frontEndFinishRegisters q D regs) ctx
          (n - finish.steps) bounded reached later
        change (DirtyFrontEnd.frontEndPhaseFinish q (frontEndData D)).result = .failure at result
        simpa only [frontEndCompleteRegistersAt, early, ite_false, result, user_frontEndFinishRegisters] using state

theorem phase_prefix_state (q : Phase) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (n : Nat) (bound : n ≤ phaseSteps q D) (reached : Cfg Γ Λ R)
    (executed : (next caller)^[n] (some (cfg (some (phaseLabel q)) regs D ctx)) = some reached) :
    reached.var = phaseRegistersAt (Λ := Λ) q regs D ctx n ∧ user reached.var = user regs ∧
      ∀ k, reached.stk (.inr (.inr k)) = ctx k := by
  cases q with
  | inl q =>
      obtain ⟨kind, rfl⟩ := frontEndControlEquiv.surjective q
      cases kind with
      | inl q =>
          simp only [phaseSteps, evaluate, frontEndControlEquiv_apply, frontEndClass_control] at bound
          simpa only [phaseRegistersAt, frontEndControlEquiv_apply, frontEndClass_control] using
            frontEnd_complete_prefix_state caller q D regs ctx n bound reached executed
      | inr b => cases b with
        | false => exact reject_prefix_state caller D regs ctx n bound reached executed
        | true => exact dispatch_prefix_state caller D regs ctx n bound reached executed
  | inr q => cases q with
    | inl q =>
        obtain ⟨kind, rfl⟩ := streamControlEquiv.surjective q
        cases kind with
        | inl q =>
            simp only [phaseSteps, evaluate, streamControlEquiv_apply, streamClass_control] at bound
            simpa only [phaseRegistersAt, streamControlEquiv_apply, streamClass_control] using
              stream_complete_prefix_state caller q D regs ctx n bound reached executed
        | inr b => exact result_prefix_state caller b D regs ctx n bound reached executed
    | inr q => cases q with
      | clear i => exact cleanup_prefix_registers caller i D regs ctx n bound reached executed
      | emit =>
          change n ≤ 1 at bound
          by_cases zero : n = 0
          · subst n
            have same := Option.some.inj executed
            subst reached
            exact ⟨rfl, rfl, fun _ => rfl⟩
          · have one : n = 1 := by omega
            subst n
            have same := Option.some.inj (((emit_localRun caller D regs ctx).iterate caller).symm.trans executed)
            subst reached
            exact ⟨rfl, rfl, fun _ => rfl⟩

theorem prefix_reset (start reached : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start)
    (executed : (next caller)^[n] (some start) = some reached) :
    reached.var = registersAt start n := by
  by_cases owned : Owned start.l
  · obtain ⟨q, regs, D, ctx, rfl⟩ := owned_cases start owned
    rw [registersAt_phase_cfg]
    rw [remainingSteps_phase_cfg] at bound
    exact (phase_prefix_state caller q D regs ctx n bound reached executed).1
  · have rank := nonowned_remaining start owned
    have zero : n = 0 := by omega
    subst n
    have same : start = reached := Option.some.inj executed
    subst reached
    cases labelEq : start.l with
    | none => simp only [registersAt, labelEq]
    | some label =>
        rcases label with front | (stream | (cleanup | external))
        · exact False.elim (owned (by simp only [labelEq, Owned]))
        · exact False.elim (owned (by simp only [labelEq, Owned]))
        · exact False.elim (owned (by simp only [labelEq, Owned]))
        · simp only [registersAt, labelEq]

theorem prefix_frame (start reached : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start)
    (executed : (next caller)^[n] (some start) = some reached) :
    user reached.var = user start.var ∧
      ∀ k, reached.stk (.inr (.inr k)) = start.stk (.inr (.inr k)) := by
  by_cases owned : Owned start.l
  · obtain ⟨q, regs, D, ctx, rfl⟩ := owned_cases start owned
    rw [remainingSteps_phase_cfg] at bound
    exact (phase_prefix_state caller q D regs ctx n bound reached executed).2
  · have rank := nonowned_remaining start owned
    have zero : n = 0 := by omega
    subst n
    have same : start = reached := Option.some.inj executed
    subst reached
    exact ⟨rfl, fun _ => rfl⟩

theorem local_step_frame {before after : Cfg Γ Λ R} (transition : LocalStep caller before after) :
    user after.var = user before.var ∧
      ∀ k, after.stk (.inr (.inr k)) = before.stk (.inr (.inr k)) := by
  have count := local_step_remaining caller transition
  exact prefix_frame caller before after 1 (by omega) transition.2

theorem local_reaches_frame {start reached : Cfg Γ Λ R}
    (path : Relation.ReflTransGen (LocalStep caller) start reached) :
    user reached.var = user start.var ∧
      ∀ k, reached.stk (.inr (.inr k)) = start.stk (.inr (.inr k)) := by
  induction path with
  | refl => exact ⟨rfl, fun _ => rfl⟩
  | @tail before after _ transition ih =>
      obtain ⟨registers, frame⟩ := local_step_frame caller transition
      exact ⟨registers.trans ih.1, fun k => (frame k).trans (ih.2 k)⟩

theorem local_reaches_finalCfg {start reached : Cfg Γ Λ R}
    (path : Relation.ReflTransGen (LocalStep caller) start reached) : finalCfg start = finalCfg reached := by
  induction path with
  | refl => rfl
  | @tail before after _ transition ih => exact ih.trans (finalCfg_step caller transition)

/-- A single reached state carries the complete inclusive operational prefix. -/
theorem owned_prefix_frame (start : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start) :
    ∃ reached, (next caller)^[n] (some start) = some reached ∧
      remainingSteps reached = remainingSteps start - n ∧
      Relation.ReflTransGen (LocalStep caller) start reached ∧
      (n < remainingSteps start ↔ Owned reached.l) ∧
      (n = 0 → reached = start) ∧ reached.var = registersAt start n ∧
      user reached.var = user start.var ∧
      (∀ k, reached.stk (.inr (.inr k)) = start.stk (.inr (.inr k))) ∧
      finalCfg reached = finalCfg start := by
  obtain ⟨reached, executed, rank, path, ownership⟩ := owned_prefix caller start n bound
  have frame := prefix_frame caller start reached n bound executed
  refine ⟨reached, executed, rank, path, ownership, ?_, prefix_reset caller start reached n bound executed,
    frame.1, frame.2, (local_reaches_finalCfg caller path).symm⟩
  intro zero
  subst n
  exact (Option.some.inj executed).symm

section CompletePhysicalSpace
variable [Fintype K]

omit caller [DecidableEq K] in
def frontEndAllowance (q : FrontEndMachine.OwnedLabels) (D : LocalData)
    (ctx : ∀ k, List (Γ k)) : Nat :=
  let finish := DirtyFrontEnd.frontEndPhaseFinish q (frontEndData D)
  let out := withFrontEnd D finish.data
  max (localCells D + DirtyFrontEnd.frontEndPhaseCredit q (frontEndData D) + contextCells ctx)
    (match finish.result with
      | .success => max (StreamMachine.inspectAllowance (streamData out) (streamContext out ctx))
          (1 + contextCells ctx)
      | .failure => max (localCells out) 1 + contextCells ctx)

omit caller [DecidableEq K] in
def phaseAllowance (q : Phase) (D : LocalData) (ctx : ∀ k, List (Γ k)) : Nat := match q with
  | .inl q => match frontEndClass q with
    | .inl q => frontEndAllowance q D ctx
    | .inr false => max (localCells D) 1 + contextCells ctx
    | .inr true => max (StreamMachine.inspectAllowance (streamData D) (streamContext D ctx))
        (1 + contextCells ctx)
  | .inr (.inl q) => match streamClass q with
    | .inl q => max (StreamMachine.phaseAllowance q (streamData D) (streamContext D ctx))
        (1 + contextCells ctx)
    | .inr _ => max (localCells D) 1 + contextCells ctx
  | .inr (.inr (.clear i)) => max (localCells D) (prefixCells i D + 1) + contextCells ctx
  | .inr (.inr .emit) => localCells D + 1 + contextCells ctx

omit caller [DecidableEq K] in
def allowance (start : Cfg Γ Λ R) : Nat := match start.l with
  | some (.inl q) => phaseAllowance (.inl q) (dataOfCfg start) (contextOfCfg start)
  | some (.inr (.inl q)) => phaseAllowance (.inr (.inl q)) (dataOfCfg start) (contextOfCfg start)
  | some (.inr (.inr (.inl q))) => phaseAllowance (.inr (.inr q)) (dataOfCfg start) (contextOfCfg start)
  | _ => stackCells start

omit caller [DecidableEq K] in
theorem allowance_phase_cfg (q : Phase) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    allowance (cfg (some (phaseLabel (Λ := Λ) q)) regs D ctx) = phaseAllowance q D ctx := by
  rcases q with q | (q | q) <;> rfl

omit caller [DecidableEq K] in
theorem localCells_frontEndData (D : LocalData) :
    localCells D = FrontEndMachine.localCells (frontEndData D) + D.moveReverse.length + D.path.length := by
  simp only [localCells, FrontEndMachine.localCells, frontEndData]
  omega

theorem frontEnd_component_prefix_cells (q : FrontEndMachine.OwnedLabels) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    PrefixProperty caller (fun c => stackCells c ≤
      localCells D + DirtyFrontEnd.frontEndPhaseCredit q (frontEndData D) + contextCells ctx)
      (cfg (some (phaseLabel (frontEndPhase q))) regs D ctx)
      (DirtyFrontEnd.frontEndPhaseSteps q (frontEndData D)) := by
  intro n bound reached executed
  let localCaller : FrontEndMachine.External (FrontEndCallerLabel Λ) → FrontEndStatement Γ Λ R := fun _ => .halt
  let start := FrontEndMachine.cfg (some (FrontEndMachine.ownedLabelEquiv (Λ := FrontEndCallerLabel Λ) q).val)
    regs (frontEndData D) (frontEndContext D ctx)
  have trace := DirtyFrontEnd.frontEnd_phase_trace localCaller q (frontEndData D) regs (frontEndContext D ctx)
  have someReached : ∃ c, (FrontEndMachine.next localCaller)^[n] (some start) = some c := by
    by_cases strict : n < DirtyFrontEnd.frontEndPhaseSteps q (frontEndData D)
    · obtain ⟨c, run, _⟩ := trace.owned_prefix n strict
      exact ⟨c, run⟩
    · have last : n = DirtyFrontEnd.frontEndPhaseSteps q (frontEndData D) := by omega
      subst n
      exact ⟨_, trace.run⟩
  obtain ⟨localReached, localRun⟩ := someReached
  have transported := frontEnd_prefix_transport caller localCaller n start
    (fun j earlier => trace.owned_prefix j (Nat.lt_of_lt_of_le earlier bound))
  have startEq := frontEndCfg_view (Λ := Λ)
    (some (FrontEndMachine.ownedLabelEquiv (Λ := FrontEndCallerLabel Λ) q).val) regs D ctx
  simp only [Option.map_some, frontEndLabelEquiv_owned] at startEq
  change frontEndCfg start = _ at startEq
  rw [localRun, startEq] at transported
  have same : frontEndCfg localReached = reached := Option.some.inj (transported.symm.trans executed)
  subst reached
  rw [stackCells_frontEndCfg]
  have physical := DirtyFrontEnd.frontEnd_phase_prefix_cells localCaller q (frontEndData D) regs
    (frontEndContext D ctx) n bound localReached localRun
  rw [frontEndContext_cells] at physical
  rw [localCells_frontEndData]
  omega

theorem frontEnd_complete_prefix_cells (q : FrontEndMachine.OwnedLabels) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    PrefixProperty caller (fun c => stackCells c ≤ frontEndAllowance q D ctx)
      (cfg (some (phaseLabel (frontEndPhase q))) regs D ctx) (frontEndEvaluation q D).steps := by
  let finish := DirtyFrontEnd.frontEndPhaseFinish q (frontEndData D)
  let out := withFrontEnd D finish.data
  let outRegs := DirtyFrontEnd.frontEndMaskRegs finish.masks regs
  have firstRun := frontEnd_phase_localRun caller q D regs ctx
  have first := (frontEnd_component_prefix_cells caller q D regs ctx).mono caller
    (Q := fun c => stackCells c ≤ frontEndAllowance q D ctx)
    (fun _ bounded => bounded.trans (Nat.le_max_left _ _))
  change LocalRun caller finish.steps _
    (cfg (some (phaseLabel (frontEndResultPhase finish.result))) outRegs out ctx) at firstRun
  change PrefixProperty caller _ _
    (finish.steps + (match finish.result with
      | .success => dispatchEvaluation out
      | .failure => answerEvaluation false out).steps)
  cases returned : finish.result with
  | success =>
      rw [returned] at firstRun
      have last := (dispatch_prefix_cells caller out outRegs ctx).mono caller
        (Q := fun c => stackCells c ≤ frontEndAllowance q D ctx)
        (fun _ bounded => bounded.trans (by
          change _ ≤ max _ (match finish.result with
            | .success => max (StreamMachine.inspectAllowance (streamData out) (streamContext out ctx))
                (1 + contextCells ctx)
            | .failure => max (localCells out) 1 + contextCells ctx)
          rw [returned]
          exact Nat.le_max_right _ _))
      exact PrefixProperty.trans caller (firstRun.iterate caller) first last
  | failure =>
      rw [returned] at firstRun
      have last := (reject_prefix_cells caller out outRegs ctx).mono caller
        (Q := fun c => stackCells c ≤ frontEndAllowance q D ctx)
        (fun _ bounded => bounded.trans (by
          change _ ≤ max _ (match finish.result with
            | .success => max (StreamMachine.inspectAllowance (streamData out) (streamContext out ctx))
                (1 + contextCells ctx)
            | .failure => max (localCells out) 1 + contextCells ctx)
          rw [returned]
          exact Nat.le_max_right _ _))
      exact PrefixProperty.trans caller (firstRun.iterate caller) first last

theorem phase_prefix_cells (q : Phase) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    PrefixProperty caller (fun c => stackCells c ≤ phaseAllowance q D ctx)
      (cfg (some (phaseLabel q)) regs D ctx) (phaseSteps q D) := by
  cases q with
  | inl q =>
      obtain ⟨kind, rfl⟩ := frontEndControlEquiv.surjective q
      cases kind with
      | inl q =>
          simp only [phaseSteps, evaluate, frontEndControlEquiv_apply, frontEndClass_control, phaseAllowance]
          change PrefixProperty caller (fun c => stackCells c ≤ frontEndAllowance q D ctx)
            (cfg (some (phaseLabel (frontEndPhase q))) regs D ctx) (frontEndEvaluation q D).steps
          exact frontEnd_complete_prefix_cells caller q D regs ctx
      | inr b => cases b with
        | false => exact reject_prefix_cells caller D regs ctx
        | true => exact dispatch_prefix_cells caller D regs ctx
  | inr q => cases q with
    | inl q =>
        obtain ⟨kind, rfl⟩ := streamControlEquiv.surjective q
        cases kind with
        | inl q =>
            simp only [phaseSteps, evaluate, streamControlEquiv_apply, streamClass_control, phaseAllowance]
            change PrefixProperty caller (fun c => stackCells c ≤
                max (StreamMachine.phaseAllowance q (streamData D) (streamContext D ctx))
                  (1 + contextCells ctx))
              (cfg (some (phaseLabel (streamPhase q))) regs D ctx) (streamEvaluation q D).steps
            exact stream_complete_prefix_cells caller q D regs ctx
        | inr b => exact result_prefix_cells caller b D regs ctx
    | inr q => cases q with
      | clear i => exact cleanup_prefix_cells caller i D regs ctx
      | emit => exact emit_prefix_cells caller D regs ctx

theorem prefix_stackCells_le_dirty (start : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start)
    (reached : Cfg Γ Λ R) (executed : (next caller)^[n] (some start) = some reached) :
    stackCells reached ≤ allowance start := by
  by_cases owned : Owned start.l
  · obtain ⟨q, regs, D, ctx, rfl⟩ := owned_cases start owned
    rw [remainingSteps_phase_cfg] at bound
    rw [allowance_phase_cfg]
    exact phase_prefix_cells caller q D regs ctx n bound reached executed
  · have count : n = 0 := by rw [nonowned_remaining start owned] at bound; omega
    subst n
    have same : start = reached := Option.some.inj executed
    subst reached
    cases labelEq : start.l with
    | none => simp only [allowance, labelEq, Nat.le_refl]
    | some label =>
        rcases label with f | (s | (cleaner | external))
        · exact False.elim (owned (by simp only [labelEq, Owned]))
        · exact False.elim (owned (by simp only [labelEq, Owned]))
        · exact False.elim (owned (by simp only [labelEq, Owned]))
        · simp only [allowance, labelEq, Nat.le_refl]

include caller in
theorem stackCells_le_allowance (start : Cfg Γ Λ R) : stackCells start ≤ allowance start :=
  prefix_stackCells_le_dirty caller start 0 (Nat.zero_le _) start rfl

theorem owned_prefix_space (start : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start) :
    ∃ reached, (next caller)^[n] (some start) = some reached ∧
      remainingSteps reached = remainingSteps start - n ∧
      Relation.ReflTransGen (LocalStep caller) start reached ∧
      (n < remainingSteps start ↔ Owned reached.l) ∧
      (n = 0 → reached = start) ∧
      reached.var = registersAt start n ∧ user reached.var = user start.var ∧
      (∀ k, reached.stk (.inr (.inr k)) = start.stk (.inr (.inr k))) ∧
      finalCfg reached = finalCfg start ∧ stackCells reached ≤ allowance start := by
  obtain ⟨reached, executed, rank, path, ownership, zero, registers, user, frame, final⟩ :=
    owned_prefix_frame caller start n bound
  exact ⟨reached, executed, rank, path, ownership, zero, registers, user, frame, final,
    prefix_stackCells_le_dirty caller start n bound reached executed⟩

theorem run_owned_prefix (regs : Registers R) (raw : Bits) (ctx : ∀ k, List (Γ k))
    (n : Nat) (bound : n ≤ runSteps raw) :
    ∃ reached, (next caller)^[n] (some (entry regs raw ctx)) = some reached ∧
      remainingSteps reached = runSteps raw - n ∧
      Relation.ReflTransGen (LocalStep caller) (entry regs raw ctx) reached ∧
      (n < runSteps raw ↔ Owned reached.l) ∧
      (n = 0 → reached = entry regs raw ctx) ∧
      reached.var = registersAt (entry (Λ := Λ) regs raw ctx) n ∧ user reached.var = user regs ∧
      (∀ k, reached.stk (.inr (.inr k)) = ctx k) ∧
      finalCfg reached = runResult regs raw ctx ∧
      stackCells reached ≤ max raw.length 1 + contextCells ctx ∧
      runSteps raw ≤ raw.length * raw.length + 10 * raw.length + 36 := by
  have rankBound : n ≤ remainingSteps (entry (Λ := Λ) regs raw ctx) := by
    rwa [remainingSteps_entry]
  obtain ⟨reached, executed, rank, path, ownership, zero, registers, retainedUser, frame, final⟩ :=
    owned_prefix_frame caller (entry regs raw ctx) n rankBound
  rw [remainingSteps_entry] at rank ownership
  rw [finalCfg_entry] at final
  exact ⟨reached, executed, rank, path, ownership, zero, registers, retainedUser, frame, final,
    run_prefix_cells caller regs raw ctx n bound reached executed, runSteps_le raw⟩

end CompletePhysicalSpace

end Resources.RotationCertificate.FrontEndStreamMachine

