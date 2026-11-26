import Applications.Resources.RotationCertificate.FrontEndStreamMachine.DirtyPotential

/-!
# FrontEndStreamMachine: DirtyPrefixes
-/

set_option autoImplicit false
set_option warningAsError true
namespace Resources.RotationCertificate.FrontEndStreamMachine.DirtyFrontEnd
open Resources.BinaryCounter (Bits)
variable {D K Λ R : Type} {Γ : K → Type}

theorem frontEndAdvance_potential (phase : FrontEndMachine.OwnedLabels)
    (data : FrontEndMachine.LocalData) :
    frontEndLocalPotential (frontEndAdvance phase data).1 (frontEndAdvance phase data).2 ≤
      frontEndLocalPotential (.inl phase) data := by
  cases phase with
  | inl phase =>
      exact front_end_inputAdvance_potential (K := Unit) (Γ := fun _ => Unit) phase data
        ((none, none), (BitDecoderMachine.zeroRegisters, ())) (fun _ => [])
  | inr phase =>
      cases phase with
      | inl phase => exact frontEndFramerAdvance_potential phase data
      | inr phase =>
          cases phase with
          | inl phase => exact frontEndDecoderAdvance_potential .input phase data
          | inr phase => exact frontEndDecoderAdvance_potential .certificate phase data

theorem frontEndControlLabel_result_not_owned (result : TreeParserMachine.Result) :
    ¬ FrontEndMachine.Owned (some (frontEndControlLabel (Λ := Λ) (.inr result))) := by
  cases result with
  | success => exact FrontEndMachine.not_owned_dispatch
  | failure => exact FrontEndMachine.not_owned_reject

section FrontEndPotentialPrefixes
variable [DecidableEq K]
variable (caller : FrontEndMachine.External Λ → FrontEndMachine.Statement Γ Λ R)

/-- A typed description of the actual prefix, carrying the fixed local potential. -/
theorem front_end_phase_prefix_description (phase : FrontEndMachine.OwnedLabels)
    (data : FrontEndMachine.LocalData) (regs : FrontEndMachine.Registers R)
    (ctx : ∀ k, List (Γ k)) (n : Nat) (bound : n ≤ frontEndPhaseSteps phase data) :
    ∃ control current currentRegs,
      (FrontEndMachine.next caller)^[n]
          (some (FrontEndMachine.cfg (some (FrontEndMachine.ownedLabelEquiv phase).val) regs data ctx)) =
        some (FrontEndMachine.cfg (some (frontEndControlLabel control)) currentRegs current ctx) ∧
      frontEndLocalPotential control current ≤ frontEndLocalPotential (.inl phase) data := by
  revert bound
  induction n with
  | zero =>
      intro _
      exact ⟨.inl phase, data, regs, rfl, Nat.le_refl _⟩
  | succ n ih =>
      intro bound
      obtain ⟨control, current, currentRegs, executed, potential⟩ := ih (by omega)
      obtain ⟨actual, actualRun, actualOwned⟩ :=
        front_end_phase_owned_prefix caller phase data regs ctx n (by omega)
      have same := Option.some.inj (actualRun.symm.trans executed)
      subst actual
      cases control with
      | inr result => exact False.elim (frontEndControlLabel_result_not_owned result actualOwned)
      | inl currentPhase =>
          refine ⟨(frontEndAdvance currentPhase current).1,
            (frontEndAdvance currentPhase current).2,
            (frontEndPhaseMask currentPhase).apply currentRegs, ?_, ?_⟩
          · rw [Function.iterate_succ_apply', executed]
            exact frontEndAdvance_step caller currentPhase current currentRegs ctx
          · exact (frontEndAdvance_potential currentPhase current).trans potential

variable [Fintype K]

/-- The actual inclusive component prefix is bounded by the fixed phase credit. -/
theorem front_end_phase_prefix_cells (phase : FrontEndMachine.OwnedLabels)
    (data : FrontEndMachine.LocalData) (regs : FrontEndMachine.Registers R)
    (ctx : ∀ k, List (Γ k)) (n : Nat) (bound : n ≤ frontEndPhaseSteps phase data)
    (reached : FrontEndMachine.Cfg Γ Λ R)
    (executed : (FrontEndMachine.next caller)^[n]
      (some (FrontEndMachine.cfg (some (FrontEndMachine.ownedLabelEquiv phase).val) regs data ctx)) =
        some reached) :
    FrontEndMachine.stackCells reached ≤ FrontEndMachine.localCells data +
      frontEndPhaseCredit phase data + FrontEndMachine.contextCells ctx := by
  obtain ⟨control, current, currentRegs, actual, potential⟩ :=
    front_end_phase_prefix_description caller phase data regs ctx n bound
  have same := Option.some.inj (executed.symm.trans actual)
  subst reached
  rw [FrontEndMachine.stackCells_cfg]
  unfold frontEndLocalPotential at potential
  change FrontEndMachine.localCells current + frontEndControlCredit control current ≤
    FrontEndMachine.localCells data + frontEndPhaseCredit phase data at potential
  omega

/-- Execution, the staged register mask, the protected context, and cells share one witness. -/
theorem front_end_phase_shared_prefix (phase : FrontEndMachine.OwnedLabels)
    (data : FrontEndMachine.LocalData) (regs : FrontEndMachine.Registers R)
    (ctx : ∀ k, List (Γ k)) (n : Nat) (bound : n ≤ frontEndPhaseSteps phase data) :
    ∃ reached : FrontEndMachine.Cfg Γ Λ R,
      (FrontEndMachine.next caller)^[n]
          (some (FrontEndMachine.cfg (some (FrontEndMachine.ownedLabelEquiv phase).val) regs data ctx)) =
        some reached ∧
      reached.var = frontEndPhaseRegisters phase data regs n ∧
      reached.var.2.2 = regs.2.2 ∧
      (∀ k, reached.stk (.inr k) = ctx k) ∧
      FrontEndMachine.stackCells reached ≤ FrontEndMachine.localCells data +
        frontEndPhaseCredit phase data + FrontEndMachine.contextCells ctx ∧
      (n < frontEndPhaseSteps phase data ↔ FrontEndMachine.Owned reached.l) ∧
      (n = 0 → reached = FrontEndMachine.cfg
        (some (FrontEndMachine.ownedLabelEquiv phase).val) regs data ctx) ∧
      (n = frontEndPhaseSteps phase data → reached = frontEndPhaseResult phase regs data ctx) := by
  obtain ⟨control, current, currentRegs, executed, _⟩ :=
    front_end_phase_prefix_description caller phase data regs ctx n bound
  let reached : FrontEndMachine.Cfg Γ Λ R :=
    FrontEndMachine.cfg (some (frontEndControlLabel control)) currentRegs current ctx
  have state := front_end_phase_prefix_state caller phase data regs ctx n bound reached executed
  have atEnd : n = frontEndPhaseSteps phase data → reached = frontEndPhaseResult phase regs data ctx := by
    intro finalTime
    rw [finalTime, front_end_phase_iterate] at executed
    exact (Option.some.inj executed).symm
  refine ⟨reached, executed, state.1, ?_, state.2,
    front_end_phase_prefix_cells caller phase data regs ctx n bound reached executed, ?_, ?_, atEnd⟩
  · rw [state.1]
    exact frontEndPhaseRegisters_caller phase data regs n
  · constructor
    · intro strict
      obtain ⟨actual, actualRun, actualOwned⟩ := front_end_phase_owned_prefix caller phase data regs ctx n strict
      have same : actual = reached := Option.some.inj (actualRun.symm.trans executed)
      rw [← same]
      exact actualOwned
    · intro owned
      by_contra notStrict
      have finalTime : n = frontEndPhaseSteps phase data := by omega
      rw [atEnd finalTime] at owned
      exact frontEndFinishCfg_not_owned (frontEndPhaseFinish phase data) regs ctx owned
  · intro zero
    subst n
    exact (Option.some.inj executed).symm

end FrontEndPotentialPrefixes

/-! Complete dirty FrontEnd configuration wrappers and exact first-boundary contracts. -/

def frontEndPartitionPhase : FrontEndMachine.LabelPartition Λ → Option FrontEndMachine.OwnedLabels
    | .inl phase => some (.inl phase)
    | .inr (.inl .success) => some (.inr (.inr (.inr .scan)))
    | .inr (.inl .failure) => none
    | .inr (.inr (.inl phase)) => some (.inr (.inl phase))
    | .inr (.inr (.inr (.inl phase))) => some (.inr (.inr (.inl phase)))
    | .inr (.inr (.inr (.inr (.inl phase)))) =>
        some (.inr (.inr (.inr (FrontEndMachine.tailPhase phase))))
    | .inr (.inr (.inr (.inr (.inr _)))) => none

def frontEndPhaseOf : Option (FrontEndMachine.Label Λ) → Option FrontEndMachine.OwnedLabels
  | none => none
  | some label => frontEndPartitionPhase (FrontEndMachine.inputPartitionEquiv.symm label)

@[simp] theorem frontEndPhaseOf_owned (phase : FrontEndMachine.OwnedLabels) :
    frontEndPhaseOf (some (FrontEndMachine.ownedLabelEquiv (Λ := Λ) phase).val) = some phase := by
  change frontEndPartitionPhase (FrontEndMachine.inputPartitionEquiv.symm
    (FrontEndMachine.inputPartitionEquiv (FrontEndMachine.ownedPartitionEquiv phase).val)) = some phase
  rw [Equiv.symm_apply_apply]
  cases phase with
  | inl phase => rfl
  | inr phase => cases phase with
    | inl phase => rfl
    | inr phase => cases phase with
      | inl phase => rfl
      | inr phase => cases phase <;> rfl

theorem frontEndPhaseOf_spec (label : Option (FrontEndMachine.Label Λ)) :
    match frontEndPhaseOf label with
    | none => ¬ FrontEndMachine.Owned label
    | some phase => label = some (FrontEndMachine.ownedLabelEquiv phase).val := by
  cases label with
  | none => simp only [frontEndPhaseOf, FrontEndMachine.Owned, not_false_eq_true]
  | some label =>
      obtain ⟨partition, rfl⟩ := FrontEndMachine.inputPartitionEquiv.surjective label
      simp only [frontEndPhaseOf, Equiv.symm_apply_apply]
      cases partition with
      | inl phase => rfl
      | inr partition => cases partition with
        | inl result => cases result with
          | success => rfl
          | failure =>
              simp only [frontEndPartitionPhase, FrontEndMachine.Owned,
                Equiv.symm_apply_apply, FrontEndMachine.OwnedPartition, not_false_eq_true]
        | inr partition => cases partition with
          | inl phase => rfl
          | inr partition => cases partition with
            | inl phase => rfl
            | inr partition => cases partition with
              | inl phase => cases phase <;> rfl
              | inr label =>
                  simp only [frontEndPartitionPhase, FrontEndMachine.Owned,
                    Equiv.symm_apply_apply, FrontEndMachine.OwnedPartition, not_false_eq_true]

theorem frontEndPhaseOf_none_iff (label : Option (FrontEndMachine.Label Λ)) :
    frontEndPhaseOf label = none ↔ ¬ FrontEndMachine.Owned label := by
  constructor
  · intro absent
    simpa only [absent] using frontEndPhaseOf_spec label
  · intro outside
    cases selected : frontEndPhaseOf label with
    | none => rfl
    | some phase =>
        have control : label = some (FrontEndMachine.ownedLabelEquiv phase).val := by
          simpa only [selected] using frontEndPhaseOf_spec label
        exact False.elim (outside (control.symm ▸ (FrontEndMachine.ownedLabelEquiv phase).property))

def frontEndDataOf (c : FrontEndMachine.Cfg Γ Λ R) : FrontEndMachine.LocalData where
  framedRaw := c.stk (.inl .framedRaw)
  frameFirstReverse := c.stk (.inl .frameFirstReverse)
  frameCertReverse := c.stk (.inl .frameCertReverse)
  inputBits := c.stk (.inl .inputBits)
  certificateBits := c.stk (.inl .certificateBits)
  inputRaw := c.stk (.inl .inputRaw)
  decodeReverse := c.stk (.inl .decodeReverse)
  certificateWord := c.stk (.inl .certificateWord)
  sourceTree := c.stk (.inl .sourceTree)
  targetTree := c.stk (.inl .targetTree)
  treeReverse := c.stk (.inl .treeReverse)
  pending := c.stk (.inl .pending)
  fuel := c.stk (.inl .fuel)
  bitsReverse := c.stk (.inl .bitsReverse)

def frontEndContextOf (c : FrontEndMachine.Cfg Γ Λ R) (k : K) : List (Γ k) := c.stk (.inr k)

@[simp] theorem frontEndDataOf_cfg (label : Option (FrontEndMachine.Label Λ))
    (regs : FrontEndMachine.Registers R) (data : FrontEndMachine.LocalData)
    (ctx : ∀ k, List (Γ k)) : frontEndDataOf (FrontEndMachine.cfg label regs data ctx) = data := by
  cases data
  rfl

@[simp] theorem frontEndContextOf_cfg (label : Option (FrontEndMachine.Label Λ))
    (regs : FrontEndMachine.Registers R) (data : FrontEndMachine.LocalData)
    (ctx : ∀ k, List (Γ k)) : frontEndContextOf (FrontEndMachine.cfg label regs data ctx) = ctx := rfl

theorem front_end_cfg_eta (c : FrontEndMachine.Cfg Γ Λ R) :
    FrontEndMachine.cfg c.l c.var (frontEndDataOf c) (frontEndContextOf c) = c := by
  apply FrontEndMachine.cfg_ext
  · rfl
  · rfl
  · funext slot
    cases slot with
    | inl slot => cases slot <;> rfl
    | inr k => rfl

def frontEndRemainingSteps (c : FrontEndMachine.Cfg Γ Λ R) : Nat :=
  match frontEndPhaseOf c.l with
  | none => 0
  | some phase => frontEndPhaseSteps phase (frontEndDataOf c)

def frontEndFinalCfg (c : FrontEndMachine.Cfg Γ Λ R) : FrontEndMachine.Cfg Γ Λ R :=
  match frontEndPhaseOf c.l with
  | none => c
  | some phase => frontEndPhaseResult phase c.var (frontEndDataOf c) (frontEndContextOf c)

def frontEndRegistersAt (c : FrontEndMachine.Cfg Γ Λ R) (n : Nat) : FrontEndMachine.Registers R :=
  match frontEndPhaseOf c.l with
  | none => c.var
  | some phase => frontEndPhaseRegisters phase (frontEndDataOf c) c.var n

@[simp] theorem frontEndRemainingSteps_phase (phase : FrontEndMachine.OwnedLabels)
    (data : FrontEndMachine.LocalData) (regs : FrontEndMachine.Registers R) (ctx : ∀ k, List (Γ k)) :
    frontEndRemainingSteps (FrontEndMachine.cfg
      (some (FrontEndMachine.ownedLabelEquiv (Λ := Λ) phase).val) regs data ctx) =
        frontEndPhaseSteps phase data := by
  change (match frontEndPhaseOf (some (FrontEndMachine.ownedLabelEquiv (Λ := Λ) phase).val) with
    | none => 0
    | some selected => frontEndPhaseSteps selected (frontEndDataOf
        (FrontEndMachine.cfg (some (FrontEndMachine.ownedLabelEquiv phase).val) regs data ctx))) = _
  rw [frontEndPhaseOf_owned, frontEndDataOf_cfg]

@[simp] theorem frontEndFinalCfg_phase (phase : FrontEndMachine.OwnedLabels)
    (data : FrontEndMachine.LocalData) (regs : FrontEndMachine.Registers R) (ctx : ∀ k, List (Γ k)) :
    frontEndFinalCfg (FrontEndMachine.cfg
      (some (FrontEndMachine.ownedLabelEquiv (Λ := Λ) phase).val) regs data ctx) =
        frontEndPhaseResult phase regs data ctx := by
  change (match frontEndPhaseOf (some (FrontEndMachine.ownedLabelEquiv (Λ := Λ) phase).val) with
    | none => FrontEndMachine.cfg (some (FrontEndMachine.ownedLabelEquiv phase).val) regs data ctx
    | some selected => frontEndPhaseResult selected regs
        (frontEndDataOf (FrontEndMachine.cfg (some (FrontEndMachine.ownedLabelEquiv phase).val) regs data ctx))
        (frontEndContextOf (FrontEndMachine.cfg (some (FrontEndMachine.ownedLabelEquiv phase).val) regs data ctx))) = _
  rw [frontEndPhaseOf_owned, frontEndDataOf_cfg, frontEndContextOf_cfg]

theorem front_end_nonowned_identity (c : FrontEndMachine.Cfg Γ Λ R)
    (outside : ¬ FrontEndMachine.Owned c.l) :
    frontEndRemainingSteps c = 0 ∧ frontEndFinalCfg c = c := by
  have absent := (frontEndPhaseOf_none_iff c.l).mpr outside
  simp only [frontEndRemainingSteps, frontEndFinalCfg, absent, and_self]

theorem frontEndFinalCfg_not_owned (c : FrontEndMachine.Cfg Γ Λ R) :
    ¬ FrontEndMachine.Owned (frontEndFinalCfg c).l := by
  cases selected : frontEndPhaseOf c.l with
  | none =>
      have outside := (frontEndPhaseOf_none_iff c.l).mp selected
      simpa only [frontEndFinalCfg, selected] using outside
  | some phase =>
      simpa only [frontEndFinalCfg, selected, frontEndPhaseResult] using
        frontEndFinishCfg_not_owned (Λ := Λ) (frontEndPhaseFinish phase (frontEndDataOf c))
          c.var (frontEndContextOf c)

theorem front_end_owned_view (c : FrontEndMachine.Cfg Γ Λ R) (owned : FrontEndMachine.Owned c.l) :
    ∃ phase, c = FrontEndMachine.cfg (some (FrontEndMachine.ownedLabelEquiv phase).val)
      c.var (frontEndDataOf c) (frontEndContextOf c) := by
  cases selected : frontEndPhaseOf c.l with
  | none => exact False.elim ((frontEndPhaseOf_none_iff c.l).mp selected owned)
  | some phase =>
      have control : c.l = some (FrontEndMachine.ownedLabelEquiv phase).val := by
        simpa only [selected] using frontEndPhaseOf_spec c.l
      have rebuilt := front_end_cfg_eta c
      rw [control] at rebuilt
      exact ⟨phase, rebuilt.symm⟩

section FrontEndCfgExecution
variable [DecidableEq K]
variable (caller : FrontEndMachine.External Λ → FrontEndMachine.Statement Γ Λ R)

theorem front_end_cfg_trace (c : FrontEndMachine.Cfg Γ Λ R) :
    FrontEndMachine.Trace caller c (frontEndFinalCfg c) (frontEndRemainingSteps c) := by
  cases selected : frontEndPhaseOf c.l with
  | none =>
      simp only [frontEndRemainingSteps, frontEndFinalCfg, selected]
      refine ⟨rfl, ?_⟩
      intro n impossible
      omega
  | some phase =>
      have control : c.l = some (FrontEndMachine.ownedLabelEquiv phase).val := by
        simpa only [selected] using frontEndPhaseOf_spec c.l
      have trace := front_end_phase_trace caller phase (frontEndDataOf c) c.var (frontEndContextOf c)
      rw [← control, front_end_cfg_eta] at trace
      simpa only [frontEndRemainingSteps, frontEndFinalCfg, selected] using trace

theorem front_end_cfg_iterate (c : FrontEndMachine.Cfg Γ Λ R) :
    (FrontEndMachine.next caller)^[frontEndRemainingSteps c] (some c) = some (frontEndFinalCfg c) :=
  (front_end_cfg_trace caller c).run

theorem front_end_trace_first_unique {start first last : FrontEndMachine.Cfg Γ Λ R} {m n : Nat}
    (before : FrontEndMachine.Trace caller start first m)
    (after : FrontEndMachine.Trace caller start last n)
    (firstExit : ¬ FrontEndMachine.Owned first.l)
    (lastExit : ¬ FrontEndMachine.Owned last.l) : m = n ∧ first = last := by
  have count : m = n := by
    by_contra different
    rcases Nat.lt_or_gt_of_ne different with early | late
    · obtain ⟨reached, executed, owned⟩ := after.owned_prefix m early
      have same := Option.some.inj (before.run.symm.trans executed)
      exact firstExit (same.symm ▸ owned)
    · obtain ⟨reached, executed, owned⟩ := before.owned_prefix n late
      have same := Option.some.inj (after.run.symm.trans executed)
      exact lastExit (same.symm ▸ owned)
  refine ⟨count, ?_⟩
  subst n
  exact Option.some.inj (before.run.symm.trans after.run)

theorem front_end_first_return_unique (start reached : FrontEndMachine.Cfg Γ Λ R) (n : Nat)
    (executed : (FrontEndMachine.next caller)^[n] (some start) = some reached)
    (outside : ¬ FrontEndMachine.Owned reached.l)
    (earlier : ∀ j, j < n → ∃ actual,
      (FrontEndMachine.next caller)^[j] (some start) = some actual ∧ FrontEndMachine.Owned actual.l) :
    n = frontEndRemainingSteps start ∧ reached = frontEndFinalCfg start :=
  front_end_trace_first_unique caller ⟨executed, earlier⟩ (front_end_cfg_trace caller start)
    outside (frontEndFinalCfg_not_owned start)

include caller in
theorem frontEndRemainingSteps_pos_iff (c : FrontEndMachine.Cfg Γ Λ R) :
    0 < frontEndRemainingSteps c ↔ FrontEndMachine.Owned c.l := by
  constructor
  · intro positive
    obtain ⟨reached, executed, owned⟩ := (front_end_cfg_trace caller c).owned_prefix 0 positive
    have same := Option.some.inj executed
    exact same.symm ▸ owned
  · intro owned
    by_contra notPositive
    have zero : frontEndRemainingSteps c = 0 := by omega
    have run := front_end_cfg_iterate caller c
    rw [zero] at run
    have same := Option.some.inj run
    exact frontEndFinalCfg_not_owned c (same ▸ owned)

omit [DecidableEq K] in
theorem frontEndPhaseSteps_pos (phase : FrontEndMachine.OwnedLabels)
    (data : FrontEndMachine.LocalData) :
    0 < frontEndPhaseSteps phase data := by
  let localCaller : FrontEndMachine.External Unit →
    FrontEndMachine.Statement (fun _ : Unit => Unit) Unit Unit := fun _ => .halt
  let regs : FrontEndMachine.Registers Unit := ((none, none), (BitDecoderMachine.zeroRegisters, ()))
  let ctx : Unit → List Unit := fun _ => []
  have positive := (frontEndRemainingSteps_pos_iff localCaller
    (FrontEndMachine.cfg (some (FrontEndMachine.ownedLabelEquiv phase).val) regs data ctx)).mpr
    (FrontEndMachine.ownedLabelEquiv phase).property
  simpa only [frontEndRemainingSteps_phase] using positive

theorem front_end_local_step_remaining {before after : FrontEndMachine.Cfg Γ Λ R}
    (owned : FrontEndMachine.Owned before.l)
    (executed : FrontEndMachine.step caller before = some after) :
    frontEndRemainingSteps before = frontEndRemainingSteps after + 1 ∧
      frontEndFinalCfg before = frontEndFinalCfg after := by
  have first : FrontEndMachine.Trace caller before after 1 := by
    refine ⟨executed, ?_⟩
    intro n strict
    have zero : n = 0 := by omega
    subst n
    exact ⟨before, rfl, owned⟩
  have joined := first.trans caller (front_end_cfg_trace caller after)
  have unique := front_end_trace_first_unique caller (front_end_cfg_trace caller before) joined
    (frontEndFinalCfg_not_owned before) (frontEndFinalCfg_not_owned after)
  exact ⟨by omega, unique.2⟩

theorem front_end_trace_after {start reached finish : FrontEndMachine.Cfg Γ Λ R} {n total : Nat}
    (whole : FrontEndMachine.Trace caller start finish total)
    (bound : n ≤ total)
    (executed : (FrontEndMachine.next caller)^[n] (some start) = some reached) :
    FrontEndMachine.Trace caller reached finish (total - n) := by
  refine ⟨front_end_prefix_after caller executed bound whole.run, ?_⟩
  intro j strict
  obtain ⟨actual, actualRun, actualOwned⟩ := whole.owned_prefix (n + j) (by omega)
  have after := front_end_prefix_after caller executed (Nat.le_add_right n j) actualRun
  have count : n + j - n = j := by omega
  exact ⟨actual, by simpa only [count] using after, actualOwned⟩

theorem front_end_prefix_remaining (start reached : FrontEndMachine.Cfg Γ Λ R)
    (n : Nat) (bound : n ≤ frontEndRemainingSteps start)
    (executed : (FrontEndMachine.next caller)^[n] (some start) = some reached) :
    frontEndRemainingSteps reached = frontEndRemainingSteps start - n ∧
      frontEndFinalCfg reached = frontEndFinalCfg start := by
  exact front_end_trace_first_unique caller (front_end_cfg_trace caller reached)
    (front_end_trace_after caller (front_end_cfg_trace caller start) bound executed)
    (frontEndFinalCfg_not_owned reached) (frontEndFinalCfg_not_owned start)

def FrontEndLocalStep (before after : FrontEndMachine.Cfg Γ Λ R) : Prop :=
  FrontEndMachine.Owned before.l ∧ FrontEndMachine.step caller before = some after

theorem front_end_prefix_reachable (start : FrontEndMachine.Cfg Γ Λ R) (n : Nat)
    (bound : n ≤ frontEndRemainingSteps start) (reached : FrontEndMachine.Cfg Γ Λ R)
    (executed : (FrontEndMachine.next caller)^[n] (some start) = some reached) :
    Relation.ReflTransGen (FrontEndLocalStep caller) start reached := by
  revert bound reached executed
  induction n with
  | zero =>
      intro _ reached executed
      have same := Option.some.inj executed
      subst reached
      exact .refl
  | succ n ih =>
      intro bound reached executed
      obtain ⟨middle, first, owned⟩ := (front_end_cfg_trace caller start).owned_prefix n (by omega)
      have before := ih (by omega) middle first
      have transition : FrontEndMachine.step caller middle = some reached := by
        simpa only [Function.iterate_succ_apply', first, FrontEndMachine.next, Option.bind_some] using executed
      exact before.trans (.single ⟨owned, transition⟩)

theorem front_end_cfg_prefix_state (start reached : FrontEndMachine.Cfg Γ Λ R) (n : Nat)
    (bound : n ≤ frontEndRemainingSteps start)
    (executed : (FrontEndMachine.next caller)^[n] (some start) = some reached) :
    reached.var = frontEndRegistersAt start n ∧
      reached.var.2.2 = start.var.2.2 ∧
      ∀ k, reached.stk (.inr k) = start.stk (.inr k) := by
  cases selected : frontEndPhaseOf start.l with
  | none =>
      have zero : n = 0 := by simpa only [frontEndRemainingSteps, selected, Nat.le_zero] using bound
      subst n
      have same := Option.some.inj executed
      subst reached
      exact ⟨by simp only [frontEndRegistersAt, selected], rfl, fun _ => rfl⟩
  | some phase =>
      have control : start.l = some (FrontEndMachine.ownedLabelEquiv phase).val := by
        simpa only [selected] using frontEndPhaseOf_spec start.l
      have explicitRun : (FrontEndMachine.next caller)^[n]
          (some (FrontEndMachine.cfg (some (FrontEndMachine.ownedLabelEquiv phase).val)
            start.var (frontEndDataOf start) (frontEndContextOf start))) = some reached := by
        rw [← control, front_end_cfg_eta]
        exact executed
      have actualBound : n ≤ frontEndPhaseSteps phase (frontEndDataOf start) := by
        simpa only [frontEndRemainingSteps, selected] using bound
      have state := front_end_phase_prefix_state caller phase (frontEndDataOf start) start.var
        (frontEndContextOf start) n actualBound reached explicitRun
      refine ⟨?_, ?_, state.2⟩
      · simpa only [frontEndRegistersAt, selected] using state.1
      · rw [state.1]
        exact frontEndPhaseRegisters_caller phase (frontEndDataOf start) start.var n

theorem front_end_cfg_prefix_exists (start : FrontEndMachine.Cfg Γ Λ R) (n : Nat)
    (bound : n ≤ frontEndRemainingSteps start) :
    ∃ reached, (FrontEndMachine.next caller)^[n] (some start) = some reached ∧
      (n < frontEndRemainingSteps start ↔ FrontEndMachine.Owned reached.l) ∧
      (n = 0 → reached = start) ∧
      (n = frontEndRemainingSteps start → reached = frontEndFinalCfg start) := by
  by_cases strict : n < frontEndRemainingSteps start
  · obtain ⟨reached, executed, owned⟩ := (front_end_cfg_trace caller start).owned_prefix n strict
    refine ⟨reached, executed, iff_of_true strict owned, ?_, ?_⟩
    · intro zero
      subst n
      exact (Option.some.inj executed).symm
    · intro finalTime
      omega
  · have finalTime : n = frontEndRemainingSteps start := by omega
    subst n
    refine ⟨frontEndFinalCfg start, front_end_cfg_iterate caller start,
      iff_of_false (Nat.lt_irrefl _) (frontEndFinalCfg_not_owned start), ?_, fun _ => rfl⟩
    intro zero
    have actual := front_end_cfg_iterate caller start
    rw [zero] at actual
    exact (Option.some.inj actual).symm

def frontEndPhaseInTime (phase : FrontEndMachine.OwnedLabels)
    (data : FrontEndMachine.LocalData) (regs : FrontEndMachine.Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (FrontEndMachine.step caller)
      (FrontEndMachine.cfg (some (FrontEndMachine.ownedLabelEquiv phase).val) regs data ctx)
      (some (frontEndPhaseResult phase regs data ctx)) (frontEndPhaseSteps phase data) where
  steps := frontEndPhaseSteps phase data
  evals_in_steps := front_end_phase_iterate caller phase data regs ctx
  steps_le_m := Nat.le_refl _

@[simp] theorem frontEndPhaseInTime_steps (phase : FrontEndMachine.OwnedLabels)
    (data : FrontEndMachine.LocalData) (regs : FrontEndMachine.Registers R) (ctx : ∀ k, List (Γ k)) :
    (frontEndPhaseInTime caller phase data regs ctx).steps = frontEndPhaseSteps phase data := rfl

def frontEndCfgInTime (c : FrontEndMachine.Cfg Γ Λ R) :
    StateTransition.EvalsToInTime (FrontEndMachine.step caller) c
      (some (frontEndFinalCfg c)) (frontEndRemainingSteps c) where
  steps := frontEndRemainingSteps c
  evals_in_steps := front_end_cfg_iterate caller c
  steps_le_m := Nat.le_refl _

@[simp] theorem frontEndCfgInTime_steps (c : FrontEndMachine.Cfg Γ Λ R) :
    (frontEndCfgInTime caller c).steps = frontEndRemainingSteps c := rfl

include caller in
theorem front_end_clean_alignment (regs : FrontEndMachine.Registers R) (raw : Bits)
    (ctx : ∀ k, List (Γ k)) :
    frontEndRemainingSteps (FrontEndMachine.entry (Λ := Λ) regs raw ctx) = FrontEndMachine.runSteps raw ∧
      frontEndFinalCfg (FrontEndMachine.entry (Λ := Λ) regs raw ctx) =
        FrontEndMachine.resultCfg regs ctx (FrontEndMachine.sourceOutcome raw) := by
  exact front_end_trace_first_unique caller
    (front_end_cfg_trace caller (FrontEndMachine.entry regs raw ctx))
    (FrontEndMachine.run_source_trace caller regs raw ctx)
    (frontEndFinalCfg_not_owned _) (FrontEndMachine.resultCfg_not_owned regs ctx _)

end FrontEndCfgExecution

def frontEndCredit (c : FrontEndMachine.Cfg Γ Λ R) : Nat :=
  match frontEndPhaseOf c.l with
  | none => 0
  | some phase => frontEndPhaseCredit phase (frontEndDataOf c)

theorem frontEndCredit_control_cfg (control : FrontEndControl)
    (data : FrontEndMachine.LocalData) (regs : FrontEndMachine.Registers R) (ctx : ∀ k, List (Γ k)) :
    frontEndCredit (FrontEndMachine.cfg (some (frontEndControlLabel (Λ := Λ) control)) regs data ctx) =
      frontEndControlCredit control data := by
  cases control with
  | inl phase =>
      change (match frontEndPhaseOf (some (FrontEndMachine.ownedLabelEquiv (Λ := Λ) phase).val) with
        | none => 0
        | some selected => frontEndPhaseCredit selected (frontEndDataOf
            (FrontEndMachine.cfg (some (FrontEndMachine.ownedLabelEquiv phase).val) regs data ctx))) = _
      rw [frontEndPhaseOf_owned, frontEndDataOf_cfg]
      rfl
  | inr result =>
      have absent := (frontEndPhaseOf_none_iff
        (some (frontEndControlLabel (Λ := Λ) (.inr result)))).mpr
        (frontEndControlLabel_result_not_owned result)
      change (match frontEndPhaseOf (some (frontEndControlLabel (Λ := Λ) (.inr result))) with
        | none => 0
        | some selected => frontEndPhaseCredit selected (frontEndDataOf
            (FrontEndMachine.cfg (some (frontEndControlLabel (.inr result))) regs data ctx))) = 0
      rw [absent]

section FrontEndCfgSpace
variable [Fintype K]

def frontEndPotential (c : FrontEndMachine.Cfg Γ Λ R) : Nat :=
  FrontEndMachine.stackCells c + frontEndCredit c

theorem frontEndPotential_control_cfg (control : FrontEndControl)
    (data : FrontEndMachine.LocalData) (regs : FrontEndMachine.Registers R) (ctx : ∀ k, List (Γ k)) :
    frontEndPotential (FrontEndMachine.cfg (some (frontEndControlLabel (Λ := Λ) control)) regs data ctx) =
      frontEndLocalPotential control data + FrontEndMachine.contextCells ctx := by
  rw [frontEndPotential, FrontEndMachine.stackCells_cfg, frontEndCredit_control_cfg]
  unfold frontEndLocalPotential
  omega

variable [DecidableEq K]
variable (caller : FrontEndMachine.External Λ → FrontEndMachine.Statement Γ Λ R)

theorem front_end_phase_step_potential (phase : FrontEndMachine.OwnedLabels)
    (data : FrontEndMachine.LocalData) (regs : FrontEndMachine.Registers R) (ctx : ∀ k, List (Γ k))
    (after : FrontEndMachine.Cfg Γ Λ R)
    (executed : FrontEndMachine.step caller
      (FrontEndMachine.cfg (some (FrontEndMachine.ownedLabelEquiv phase).val) regs data ctx) = some after) :
    frontEndPotential after ≤ frontEndPotential
      (FrontEndMachine.cfg (Λ := Λ) (some (FrontEndMachine.ownedLabelEquiv phase).val) regs data ctx) := by
  have same := Option.some.inj
    (executed.symm.trans (frontEndAdvance_step caller phase data regs ctx))
  rw [same, frontEndPotential_control_cfg]
  change frontEndLocalPotential (frontEndAdvance phase data).1 (frontEndAdvance phase data).2 +
      FrontEndMachine.contextCells ctx ≤
    frontEndPotential (FrontEndMachine.cfg (some (frontEndControlLabel (.inl phase))) regs data ctx)
  rw [frontEndPotential_control_cfg]
  exact Nat.add_le_add_right (frontEndAdvance_potential phase data) _

theorem front_end_local_step_potential {before after : FrontEndMachine.Cfg Γ Λ R}
    (owned : FrontEndMachine.Owned before.l)
    (executed : FrontEndMachine.step caller before = some after) :
    frontEndPotential after ≤ frontEndPotential before := by
  obtain ⟨phase, rebuilt⟩ := front_end_owned_view before owned
  rw [rebuilt] at executed ⊢
  exact front_end_phase_step_potential caller phase _ _ _ after executed

theorem front_end_reaches_potential {start reached : FrontEndMachine.Cfg Γ Λ R}
    (path : Relation.ReflTransGen (FrontEndLocalStep caller) start reached) :
    frontEndPotential reached ≤ frontEndPotential start := by
  induction path with
  | refl => exact Nat.le_refl _
  | @tail before after _ transition ih =>
      exact (front_end_local_step_potential caller transition.1 transition.2).trans ih

/-- One actual inclusive witness carries rank, ownership, masks, frame and the physical allowance. -/
theorem front_end_owned_prefix (start : FrontEndMachine.Cfg Γ Λ R) (n : Nat)
    (bound : n ≤ frontEndRemainingSteps start) :
    ∃ reached, (FrontEndMachine.next caller)^[n] (some start) = some reached ∧
      frontEndRemainingSteps reached = frontEndRemainingSteps start - n ∧
      Relation.ReflTransGen (FrontEndLocalStep caller) start reached ∧
      (n < frontEndRemainingSteps start ↔ FrontEndMachine.Owned reached.l) ∧
      (n = 0 → reached = start) ∧
      reached.var = frontEndRegistersAt start n ∧
      reached.var.2.2 = start.var.2.2 ∧
      (∀ k, reached.stk (.inr k) = start.stk (.inr k)) ∧
      frontEndPotential reached ≤ frontEndPotential start ∧
      FrontEndMachine.stackCells reached ≤ frontEndPotential start ∧
      frontEndFinalCfg reached = frontEndFinalCfg start ∧
      (n = frontEndRemainingSteps start → reached = frontEndFinalCfg start) := by
  obtain ⟨reached, executed, owned, zero, final⟩ := front_end_cfg_prefix_exists caller start n bound
  have remaining := front_end_prefix_remaining caller start reached n bound executed
  have path := front_end_prefix_reachable caller start n bound reached executed
  have state := front_end_cfg_prefix_state caller start reached n bound executed
  have potential := front_end_reaches_potential caller path
  refine ⟨reached, executed, remaining.1, path, owned, zero, state.1, state.2.1, state.2.2,
    potential, ?_, remaining.2, final⟩
  unfold frontEndPotential at potential ⊢
  omega

end FrontEndCfgSpace

section DirtyInputFirstBoundary
variable [DecidableEq K]
variable (caller : InputParserMachine.External Λ → InputParserMachine.Statement Γ Λ R)

theorem inputPhaseFinish_first_return_unique (phase : InputParserMachine.OwnedLabels)
    (data : InputState) (regs : InputParserMachine.Registers R) (ctx : ∀ k, List (Γ k))
    (n : Nat) (reached : InputParserMachine.Cfg Γ Λ R)
    (executed : (InputParserMachine.next caller)^[n]
      (some (inputCfg (some (InputParserMachine.ownedLabelEquiv phase).val) regs data ctx)) = some reached)
    (outside : ¬ InputParserMachine.FullOwned reached.l)
    (earlier : ∀ j, j < n → ∃ actual,
      (InputParserMachine.next caller)^[j]
        (some (inputCfg (some (InputParserMachine.ownedLabelEquiv phase).val) regs data ctx)) = some actual ∧
      InputParserMachine.FullOwned actual.l) :
    n = (inputPhaseFinish phase data).steps ∧
      reached = inputCfg (some (InputParserMachine.resultLabel (inputPhaseFinish phase data).result))
        (InputParserMachine.reset regs) (inputPhaseFinish phase data).data ctx := by
  have canonical := inputPhaseFinish_iterate caller phase data regs ctx
  have canonicalExit : ¬ InputParserMachine.FullOwned
      (inputCfg (Λ := Λ) (some (InputParserMachine.resultLabel (inputPhaseFinish phase data).result))
        (InputParserMachine.reset regs) (inputPhaseFinish phase data).data ctx).l := by
    exact InputParserMachine.not_fullOwned_result (inputPhaseFinish phase data).result
  have count : n = (inputPhaseFinish phase data).steps := by
    by_contra different
    rcases Nat.lt_or_gt_of_ne different with early | late
    · obtain ⟨actual, actualRun, owned⟩ := inputPhaseFinish_owned_prefix caller phase data regs ctx n early
      have same := Option.some.inj (executed.symm.trans actualRun)
      exact outside (same.symm ▸ owned)
    · obtain ⟨actual, actualRun, owned⟩ := earlier (inputPhaseFinish phase data).steps late
      have same := Option.some.inj (canonical.symm.trans actualRun)
      exact canonicalExit (same.symm ▸ owned)
  refine ⟨count, ?_⟩
  rw [count] at executed
  exact Option.some.inj (executed.symm.trans canonical)

end DirtyInputFirstBoundary

end Resources.RotationCertificate.FrontEndStreamMachine.DirtyFrontEnd

