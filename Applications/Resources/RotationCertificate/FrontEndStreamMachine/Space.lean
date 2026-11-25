import Applications.Resources.RotationCertificate.FrontEndStreamMachine.Basic

/-!
# FrontEndStreamMachine: Space
-/

set_option autoImplicit false
set_option warningAsError true
namespace Resources.RotationCertificate.FrontEndStreamMachine
open Search.SharedTree (Branch)
open Resources.BinaryCounter (Bits)
variable {K Λ R : Type} {Γ : K → Type}
variable [DecidableEq K]
variable (caller : Λ → Statement Γ Λ R)

section PhysicalSpace
variable [Fintype K]

omit caller [DecidableEq K] in
def contextCells (ctx : ∀ k, List (Γ k)) : Nat := ∑ k, (ctx k).length

omit caller [DecidableEq K] in
def stackCells (c : Cfg Γ Λ R) : Nat := ∑ k, (c.stk k).length

omit caller [DecidableEq K] in
theorem stackCells_eq_sum (c : Cfg Γ Λ R) : stackCells c = ∑ k, (c.stk k).length := rfl

omit caller [DecidableEq K] in
theorem newBranch_sum (f : StreamMachine.NewBranchStores → Nat) :
    ∑ k, f k = f .moveReverse + f .path := by
  change (∑ k ∈ ({.moveReverse, .path} : Finset StreamMachine.NewBranchStores), f k) = _
  simp

omit caller [DecidableEq K] in
theorem stackCells_cfg (label : Option (Label Λ)) (regs : Registers R) (D : LocalData)
    (ctx : ∀ k, List (Γ k)) : stackCells (cfg label regs D ctx) = localCells D + contextCells ctx := by
  rw [stackCells, Fintype.sum_sum_type, FrontEndMachine.localStack_sum,
    Fintype.sum_sum_type, newBranch_sum]
  dsimp only [cfg, stores, frontEndData, FrontEndMachine.stores, frontEndContext,
    StreamMachine.frontEndAddedContext, localCells, contextCells]
  omega

omit caller [DecidableEq K] in
theorem stackCells_frontEndCfg (c : FrontEndCfg Γ Λ R) :
    stackCells (frontEndCfg c) = FrontEndMachine.stackCells c :=
  FrontEndMachine.Transport.stackEquiv_total_length (Equiv.refl _) (fun _ => Equiv.refl _) c.stk

omit caller [DecidableEq K] in
theorem stackCells_streamCfg (c : StreamCfg Γ Λ R) :
    stackCells (streamCfg c) = StreamMachine.stackCells c :=
  FrontEndMachine.Transport.stackEquiv_total_length streamStackEquiv streamSymbolEquiv c.stk

omit caller [DecidableEq K] in
theorem streamContext_cells (D : LocalData) (ctx : ∀ k, List (Γ k)) :
    StreamMachine.contextCells (streamContext D ctx) =
      D.framedRaw.length + D.frameFirstReverse.length + D.frameCertReverse.length +
      D.inputBits.length + D.certificateBits.length + D.inputRaw.length + D.bitsReverse.length + contextCells ctx := by
  have sum (f : StreamMachine.FrontEndProtected → Nat) :
      ∑ k, f k = f .framedRaw + f .frameFirstReverse + f .frameCertReverse +
        f .inputBits + f .certificateBits + f .inputRaw + f .bitsReverse := by
    change (∑ k ∈ ({.framedRaw, .frameFirstReverse, .frameCertReverse, .inputBits,
      .certificateBits, .inputRaw, .bitsReverse} : Finset StreamMachine.FrontEndProtected), f k) = _
    simp
    omega
  rw [StreamMachine.contextCells, Fintype.sum_sum_type, sum]
  rfl

def ExactPeak (start : Cfg Γ Λ R) (ticks peak : Nat) : Prop :=
  PrefixProperty caller (fun c => stackCells c ≤ peak) start ticks ∧
    ∃ n, n ≤ ticks ∧ ∃ reached, (next caller)^[n] (some start) = some reached ∧ stackCells reached = peak

theorem clear_slot_prefix_cells (i : Fin 16) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    PrefixProperty caller (fun c => stackCells c ≤ localCells D + contextCells ctx)
      (cfg (some (clearLabel i)) regs D ctx) (slotLength i D + 1) := by
  intro n bound reached executed
  by_cases early : n ≤ slotLength i D
  · have same := Option.some.inj ((drain_slot_iterate caller i D regs ctx n early).symm.trans executed)
    subst reached
    rw [stackCells_cfg]
    exact Nat.add_le_add_right (localCells_dropData_le i n D) _
  · have nEq : n = slotLength i D + 1 := by omega
    subst n
    have same := Option.some.inj ((clear_slot_iterate caller i D regs ctx).symm.trans executed)
    subst reached
    rw [stackCells_cfg]
    exact Nat.add_le_add_right (localCells_emptySlot_le i D) _

theorem emit_prefix_cells (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    PrefixProperty caller (fun c => stackCells c ≤ localCells D + 1 + contextCells ctx)
      (cfg (some emitLabel) regs D ctx) 1 := by
  intro n bound reached executed
  cases n with
  | zero =>
      have same := Option.some.inj executed
      subst reached
      rw [stackCells_cfg]
      omega
  | succ n =>
      have nEq : n = 0 := by omega
      subst n
      have same := Option.some.inj ((emit_localRun caller D regs ctx).iterate caller |>.symm.trans executed)
      subst reached
      rw [stackCells_cfg, localCells_emitData]

theorem cleanup_prefix_cells (i : Fin 16) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    PrefixProperty caller (fun c => stackCells c ≤ max (localCells D) (prefixCells i D + 1) + contextCells ctx)
      (cfg (some (clearLabel i)) regs D ctx) (cleanupSteps i D) := by
  induction i using Fin.reverseInduction generalizing D regs with
  | last =>
      have first := clear_slot_prefix_cells caller 15 D regs ctx
      have before := first.mono caller (Q := fun c => stackCells c ≤ max (localCells D) (prefixCells 15 D + 1) + contextCells ctx) (fun c hc => hc.trans
        (Nat.add_le_add_right (Nat.le_max_left _ _) _))
      have last := emit_prefix_cells caller (emptySlot 15 D) (occupancyRegisters false regs) ctx
      have after := last.mono caller (Q := fun c => stackCells c ≤ max (localCells D) (prefixCells 15 D + 1) + contextCells ctx) (fun c hc => hc.trans (by
        rw [emptySlot_last_eq_clearSuffix, localCells_clearSuffix]
        exact Nat.add_le_add_right (Nat.le_max_right _ _) _))
      have joined := PrefixProperty.trans caller (clear_slot_iterate caller 15 D regs ctx) before after
      simpa [cleanupSteps, suffixCells, slotLength, nextClear] using joined
  | cast i ih =>
      have first := clear_slot_prefix_cells caller i.castSucc D regs ctx
      have before := first.mono caller (Q := fun c => stackCells c ≤ max (localCells D) (prefixCells i.castSucc D + 1) + contextCells ctx) (fun c hc => hc.trans
        (Nat.add_le_add_right (Nat.le_max_left _ _) _))
      have last := ih (emptySlot i.castSucc D) (occupancyRegisters false regs)
      have after := last.mono caller (Q := fun c => stackCells c ≤ max (localCells D) (prefixCells i.castSucc D + 1) + contextCells ctx) (fun c hc => hc.trans (Nat.add_le_add_right (by
        rw [prefixCells_castSucc]
        exact max_le_max (localCells_emptySlot_le i.castSucc D) (Nat.le_refl _)) _))
      have headRun := clear_slot_iterate caller i.castSucc D regs ctx
      rw [nextClear_castSucc] at headRun
      have joined := PrefixProperty.trans caller headRun before after
      rwa [← cleanupSteps_castSucc] at joined

theorem cleanup_peak (i : Fin 16) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    ExactPeak caller (cfg (some (clearLabel i)) regs D ctx) (cleanupSteps i D)
      (max (prefixCells i D + suffixCells i D) (prefixCells i D + 1) + contextCells ctx) := by
  rw [prefixCells_add_suffixCells]
  refine ⟨cleanup_prefix_cells caller i D regs ctx, ?_⟩
  by_cases large : prefixCells i D + 1 ≤ localCells D
  · refine ⟨0, Nat.zero_le _, _, rfl, ?_⟩
    rw [stackCells_cfg, Nat.max_eq_left large]
  · refine ⟨cleanupSteps i D, Nat.le_refl _, _, cleanup_iterate caller i D regs ctx, ?_⟩
    rw [stackCells_cfg, localCells_cleanupData, Nat.max_eq_right (by omega)]

theorem emit_peak (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ExactPeak caller (cfg (some emitLabel) regs D ctx) 1 (localCells D + 1 + contextCells ctx) := by
  refine ⟨emit_prefix_cells caller D regs ctx, 1, Nat.le_refl _, _,
    (emit_localRun caller D regs ctx).iterate caller, ?_⟩
  rw [stackCells_cfg, localCells_emitData]

end PhysicalSpace

theorem frontEnd_trace_localRun
    (localCaller : FrontEndMachine.External (FrontEndCallerLabel Λ) → FrontEndStatement Γ Λ R)
    {start finish : FrontEndCfg Γ Λ R} {ticks : Nat}
    (trace : FrontEndMachine.Trace localCaller start finish ticks) :
    LocalRun caller ticks (frontEndCfg start) (frontEndCfg finish) := by
  apply LocalRun.of_iterate caller
  · have transported := frontEnd_prefix_transport caller localCaller ticks start trace.owned_prefix
    rw [trace.run] at transported
    exact transported
  · intro n strict
    obtain ⟨reached, executed, owned⟩ := trace.owned_prefix n strict
    have transported := frontEnd_prefix_transport caller localCaller n start
      (fun j earlier => trace.owned_prefix j (by omega))
    rw [executed] at transported
    exact ⟨frontEndCfg reached, transported, owned_frontEndCfg reached owned⟩

omit caller [DecidableEq K] in
def cleanData (raw : Bits) : LocalData := { framedRaw := raw }

omit caller [DecidableEq K] in
def entryPhase : Phase := .inl (FrontEndMachine.framerLabel .scanPrefix)

omit caller [DecidableEq K] in
def entry (regs : Registers R) (raw : Bits) (ctx : ∀ k, List (Γ k)) : Cfg Γ Λ R :=
  cfg (some (phaseLabel entryPhase)) regs (cleanData raw) ctx

omit caller [DecidableEq K] in
def frontEndOutcomeData : FrontEndMachine.Outcome → LocalData
  | .frameFailure => {}
  | .inputDecodeFailure cert => { certificateBits := cert }
  | .inputParseFailure input cert => { inputRaw := input, certificateBits := cert }
  | .certificateDecodeFailure source target fuel =>
      { sourceTree := treeCode source, targetTree := treeCode target, fuel := fuel }
  | .success source target fuel cert =>
      { sourceTree := treeCode source, targetTree := treeCode target, fuel := fuel, certificateWord := cert }

omit caller [DecidableEq K] in
def frontEndOutcomeRegisters (outcome : FrontEndMachine.Outcome) (regs : Registers R) : Registers R :=
  match outcome with
  | .frameFailure => FrontEndMachine.resetFramer regs
  | .inputDecodeFailure _ => FrontEndMachine.afterInputDecoder regs
  | _ => FrontEndMachine.reset regs

omit caller [DecidableEq K] in
def frontEndOutcomePhase : FrontEndMachine.Outcome → Phase
  | .success _ _ _ _ => dispatchPhase
  | _ => rejectPhase

omit caller [DecidableEq K] in
def frontEndOutcomeCfg (outcome : FrontEndMachine.Outcome) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) : Cfg Γ Λ R :=
  cfg (some (phaseLabel (frontEndOutcomePhase outcome))) (frontEndOutcomeRegisters outcome regs)
    (frontEndOutcomeData outcome) ctx

omit caller [DecidableEq K] in
@[simp] theorem fullReset_frontEndOutcomeRegisters (outcome : FrontEndMachine.Outcome) (regs : Registers R) :
    fullReset (frontEndOutcomeRegisters outcome regs) = fullReset regs := by cases outcome <;> rfl

omit caller [DecidableEq K] in
theorem frontEndCfg_entry (regs : Registers R) (raw : Bits) (ctx : ∀ k, List (Γ k)) :
    frontEndCfg (FrontEndMachine.entry (Λ := FrontEndCallerLabel Λ) regs raw (frontEndContext {} ctx)) =
      entry regs raw ctx :=
  frontEndCfg_view (some (FrontEndMachine.framerLabel .scanPrefix)) regs (cleanData raw) ctx

omit caller [DecidableEq K] in
theorem frontEndCfg_resultCfg (outcome : FrontEndMachine.Outcome) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    frontEndCfg (FrontEndMachine.resultCfg (Λ := FrontEndCallerLabel Λ) regs
      (frontEndContext {} ctx) outcome) = frontEndOutcomeCfg outcome regs ctx := by
  cases outcome with
  | frameFailure =>
      exact frontEndCfg_view (some FrontEndMachine.rejectLabel) (FrontEndMachine.resetFramer regs) {} ctx
  | inputDecodeFailure cert =>
      exact frontEndCfg_view (some FrontEndMachine.rejectLabel) (FrontEndMachine.afterInputDecoder regs)
        { certificateBits := cert } ctx
  | inputParseFailure input cert =>
      exact frontEndCfg_view (some FrontEndMachine.rejectLabel) (FrontEndMachine.reset regs)
        { inputRaw := input, certificateBits := cert } ctx
  | certificateDecodeFailure source target fuel =>
      exact frontEndCfg_view (some FrontEndMachine.rejectLabel) (FrontEndMachine.reset regs)
        { sourceTree := treeCode source, targetTree := treeCode target, fuel := fuel } ctx
  | success source target fuel cert =>
      exact frontEndCfg_view (some FrontEndMachine.dispatchLabel) (FrontEndMachine.reset regs)
        { sourceTree := treeCode source, targetTree := treeCode target, fuel := fuel, certificateWord := cert } ctx

theorem frontEnd_clean_localRun (regs : Registers R) (raw : Bits) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (FrontEndMachine.runSteps raw) (entry regs raw ctx)
      (frontEndOutcomeCfg (FrontEndMachine.sourceOutcome raw) regs ctx) := by
  have trace := FrontEndMachine.run_source_trace
    (Γ := StreamMachine.frontEndAddedAlphabet Γ) (Λ := FrontEndCallerLabel Λ)
    (fun _ => .halt) regs raw (frontEndContext {} ctx)
  have transported := frontEnd_trace_localRun caller (fun _ => .halt) trace
  simpa only [frontEndCfg_entry, frontEndCfg_resultCfg] using transported

omit caller [DecidableEq K] in
def outcomeContinuation (outcome : FrontEndMachine.Outcome) : Evaluation := match outcome with
  | .success _ _ _ _ => dispatchEvaluation (frontEndOutcomeData outcome)
  | _ => answerEvaluation false (frontEndOutcomeData outcome)

omit caller [DecidableEq K] in
def runEvaluation (raw : Bits) : Evaluation :=
  addSteps (FrontEndMachine.runSteps raw) (outcomeContinuation (FrontEndMachine.sourceOutcome raw))

omit caller [DecidableEq K] in
def runSteps (raw : Bits) : Nat := (runEvaluation raw).steps

omit caller [DecidableEq K] in
def runResult (regs : Registers R) (raw : Bits) (ctx : ∀ k, List (Γ k)) : Cfg Γ Λ R :=
  evaluationCfg regs (runEvaluation raw) ctx

theorem outcomeContinuation_localRun (outcome : FrontEndMachine.Outcome) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (outcomeContinuation outcome).steps (frontEndOutcomeCfg outcome regs ctx)
      (evaluationCfg regs (outcomeContinuation outcome) ctx) := by
  cases outcome with
  | frameFailure =>
      exact reject_complete_localRun caller {} (FrontEndMachine.resetFramer regs) ctx
  | inputDecodeFailure cert =>
      exact reject_complete_localRun caller { certificateBits := cert } (FrontEndMachine.afterInputDecoder regs) ctx
  | inputParseFailure input cert =>
      exact reject_complete_localRun caller { inputRaw := input, certificateBits := cert }
        (FrontEndMachine.reset regs) ctx
  | certificateDecodeFailure source target fuel =>
      exact reject_complete_localRun caller
        { sourceTree := treeCode source, targetTree := treeCode target, fuel := fuel }
        (FrontEndMachine.reset regs) ctx
  | success source target fuel cert =>
      exact dispatch_complete_localRun caller
        { sourceTree := treeCode source, targetTree := treeCode target, fuel := fuel, certificateWord := cert }
        (FrontEndMachine.reset regs) ctx

theorem run_localRun (regs : Registers R) (raw : Bits) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (runSteps raw) (entry regs raw ctx) (runResult regs raw ctx) :=
  LocalRun.trans caller (frontEnd_clean_localRun caller regs raw ctx)
    (outcomeContinuation_localRun caller (FrontEndMachine.sourceOutcome raw) regs ctx)

theorem run_iterate (regs : Registers R) (raw : Bits) (ctx : ∀ k, List (Γ k)) :
    (next caller)^[runSteps raw] (some (entry regs raw ctx)) = some (runResult regs raw ctx) :=
  (run_localRun caller regs raw ctx).iterate caller

omit caller [DecidableEq K] in
@[simp] theorem cleanupData_zero (b : Bool) (D : LocalData) : cleanupData 0 b D = { fuel := [b] } := by
  simp [cleanupData, clearSuffix, emitData]

omit caller [DecidableEq K] in
theorem cleanupSteps_zero (D : LocalData) : cleanupSteps 0 D = localCells D + 17 := by
  simp [cleanupSteps, suffixCells, localCells]

omit caller [DecidableEq K] in
def outcomeValue : FrontEndMachine.Outcome → Bool
  | .success source target fuel cert => (checkStreamRun fuel source target cert).1
  | _ => false

omit caller [DecidableEq K] in
theorem outcomeValue_sourceOutcome (raw : Bits) :
    outcomeValue (FrontEndMachine.sourceOutcome raw) = BitPairFraming.verifyFramed raw := by
  unfold FrontEndMachine.sourceOutcome BitPairFraming.verifyFramed
  cases framing : BitPairFraming.unframe raw with
  | none => rfl
  | some pair =>
      rcases pair with ⟨input, cert⟩
      dsimp only
      cases decoded : (unpackWordRun input).1 with
      | none =>
          rw [verifyBitsRun_input_none input cert decoded]
          rfl
      | some word =>
          dsimp only
          cases parsed : (parseInputRun word).1 with
          | none =>
              rw [verifyBitsRun_parse_none input cert word decoded parsed]
              rfl
          | some triple =>
              rcases triple with ⟨source, target, fuel⟩
              dsimp only
              cases certified : (unpackWordRun cert).1 with
              | none =>
                  rw [verifyBitsRun_certificate_none input cert word source target fuel decoded parsed certified]
                  rfl
              | some moves =>
                  rw [verifyBitsRun_success input cert word moves source target fuel decoded parsed certified]
                  rfl

omit caller [DecidableEq K] in
theorem outcomeContinuation_data (outcome : FrontEndMachine.Outcome) :
    (outcomeContinuation outcome).data = { fuel := [outcomeValue outcome] } := by
  cases outcome with
  | frameFailure => exact cleanupData_zero false {}
  | inputDecodeFailure cert => exact cleanupData_zero false { certificateBits := cert }
  | inputParseFailure input cert => exact cleanupData_zero false { inputRaw := input, certificateBits := cert }
  | certificateDecodeFailure source target fuel => exact cleanupData_zero false _
  | success source target fuel cert =>
      change cleanupData 0 (StreamMachine.runEvaluation fuel cert (treeCode source) (treeCode target)).result _ = _
      rw [cleanupData_zero, StreamMachine.runEvaluation_code_value]
      rfl

omit caller [DecidableEq K] in
theorem runEvaluation_data (raw : Bits) :
    (runEvaluation raw).data = { fuel := [BitPairFraming.verifyFramed raw] } := by
  exact (outcomeContinuation_data (FrontEndMachine.sourceOutcome raw)).trans
    (congrArg (fun b => ({ fuel := [b] } : LocalData)) (outcomeValue_sourceOutcome raw))

omit caller [DecidableEq K] in
theorem runResult_eq (regs : Registers R) (raw : Bits) (ctx : ∀ k, List (Γ k)) :
    runResult (Λ := Λ) regs raw ctx =
      cfg none (fullReset regs) { fuel := [BitPairFraming.verifyFramed raw] } ctx := by
  unfold runResult evaluationCfg
  rw [runEvaluation_data]

theorem run_output (regs : Registers R) (raw : Bits) (ctx : ∀ k, List (Γ k)) :
    (next caller)^[runSteps raw] (some (entry regs raw ctx)) =
      some (cfg none (fullReset regs) { fuel := [BitPairFraming.verifyFramed raw] } ctx) := by
  rw [run_iterate, runResult_eq]

omit caller [DecidableEq K] in
theorem runSteps_failure (raw : Bits)
    (failed : ∀ source target fuel cert,
      FrontEndMachine.sourceOutcome raw ≠ .success source target fuel cert) :
    runSteps raw = FrontEndMachine.runSteps raw +
      localCells (frontEndOutcomeData (FrontEndMachine.sourceOutcome raw)) + 18 := by
  unfold runSteps runEvaluation addSteps
  cases outcome : FrontEndMachine.sourceOutcome raw with
  | frameFailure | inputDecodeFailure | inputParseFailure | certificateDecodeFailure =>
      simp only [outcomeContinuation, answerEvaluation, cleanupSteps_zero]
      omega
  | success source target fuel cert => exact False.elim (failed source target fuel cert outcome)

omit caller [DecidableEq K] in
theorem runSteps_success (raw : Bits) (source target : BinaryTree Unit) (fuel : Bits) (cert : Word)
    (returned : FrontEndMachine.sourceOutcome raw = .success source target fuel cert) :
    runSteps raw = FrontEndMachine.runSteps raw +
      StreamMachine.runSteps fuel cert (treeCode source) (treeCode target) +
      StreamMachine.localCells (StreamMachine.runEvaluation fuel cert (treeCode source) (treeCode target)).data + 19 := by
  simp only [runSteps, runEvaluation, addSteps, returned, outcomeContinuation, dispatchEvaluation,
    streamEvaluation, answerEvaluation, cleanupSteps_zero]
  change _ + (1 + ((StreamMachine.runEvaluation fuel cert (treeCode source) (treeCode target)).steps +
    (1 + (localCells (withStream (frontEndOutcomeData (.success source target fuel cert))
      (StreamMachine.runEvaluation fuel cert (treeCode source) (treeCode target)).data) + 17)))) = _
  simp only [localCells, withStream, frontEndOutcomeData, StreamMachine.localCells,
    StreamMachine.runSteps, List.length_nil]
  omega

omit caller [DecidableEq K] in
theorem runSteps_code (source target : BinaryTree Unit) (fuel : Bits) (cert : Word) :
    runSteps (BitPairFraming.frame (wordBits (inputCode source target fuel)) (wordBits cert)) =
      12 * (inputCode source target fuel).length + 10 * cert.length +
      StreamMachine.runSteps fuel cert (treeCode source) (treeCode target) +
      StreamMachine.localCells (StreamMachine.runEvaluation fuel cert (treeCode source) (treeCode target)).data + 30 := by
  rw [runSteps_success _ source target fuel cert ((FrontEndMachine.sourceOutcome_success_iff _ _ _ _ _).mpr rfl),
    FrontEndMachine.runSteps_code]
  omega


omit caller [DecidableEq K] in
theorem frontEndOutcome_cells_le (raw : Bits) :
    localCells (frontEndOutcomeData (FrontEndMachine.sourceOutcome raw)) ≤ raw.length := by
  let localCaller : FrontEndMachine.External Empty →
      FrontEndMachine.Statement (fun _ : Empty => Empty) Empty Unit := fun _ => .halt
  let regs : FrontEndMachine.Registers Unit := ((none, none), BitDecoderMachine.zeroRegisters, ())
  let ctx : Empty → List Empty := fun k => Empty.elim k
  have executed := FrontEndMachine.run_source localCaller regs raw ctx
  have bound := FrontEndMachine.prefix_stackCells_le localCaller regs raw ctx
    (FrontEndMachine.runSteps raw) (Nat.le_refl _) _ executed
  have cells : FrontEndMachine.stackCells
      (FrontEndMachine.resultCfg (Λ := Empty) regs ctx (FrontEndMachine.sourceOutcome raw)) =
      localCells (frontEndOutcomeData (FrontEndMachine.sourceOutcome raw)) := by
    cases FrontEndMachine.sourceOutcome raw <;>
      simp [FrontEndMachine.resultCfg, FrontEndMachine.stackCells_cfg,
        FrontEndMachine.localCells, FrontEndMachine.contextCells, FrontEndMachine.decodedInputData,
        FrontEndMachine.parsedData, FrontEndMachine.successData, localCells, frontEndOutcomeData, ctx]
  rw [cells] at bound
  simpa [FrontEndMachine.contextCells, ctx] using bound

omit caller [DecidableEq K] in
theorem stream_run_final_cells_le (fuel : Bits) (certificate source target : Word) :
    StreamMachine.localCells (StreamMachine.runEvaluation fuel certificate source target).data ≤
      certificate.length + 2 * source.length + fuel.length + target.length := by
  let localCaller : StreamMachine.External Empty →
      StreamMachine.Statement (fun _ : Empty => Empty) Empty Unit := fun _ => .halt
  let regs := StreamMachine.initialRegisters ()
  let ctx : Empty → List Empty := fun k => Empty.elim k
  have executed := StreamMachine.run localCaller regs fuel certificate source target ctx
  have bound := StreamMachine.run_prefix_cells localCaller regs fuel certificate source target ctx
    (StreamMachine.runSteps fuel certificate source target) (Nat.le_refl _) _ executed
  simpa [StreamMachine.runResult, StreamMachine.evaluationCfg, StreamMachine.stackCells_cfg,
    StreamMachine.mass, StreamMachine.contextCells, ctx] using bound

omit caller [DecidableEq K] in
theorem successful_raw_size (raw : Bits) (source target : BinaryTree Unit) (fuel : Bits) (cert : Word)
    (returned : FrontEndMachine.sourceOutcome raw = .success source target fuel cert) :
    raw.length = 8 * ((treeCode source).length + (treeCode target).length + fuel.length + 3) +
      4 * cert.length + 1 := by
  rw [(FrontEndMachine.sourceOutcome_success_iff _ _ _ _ _).mp returned,
    BitPairFraming.frame_length, wordBits_length, wordBits_length, inputCode_length]
  simp only [treeCode_length]
  omega

omit caller [DecidableEq K] in
theorem successful_stream_allowance_le (raw : Bits) (source target : BinaryTree Unit)
    (fuel : Bits) (cert : Word)
    (returned : FrontEndMachine.sourceOutcome raw = .success source target fuel cert) :
    cert.length + 2 * (treeCode source).length + fuel.length + (treeCode target).length ≤ raw.length := by
  have size := successful_raw_size raw source target fuel cert returned
  omega

omit caller [DecidableEq K] in
theorem runSteps_failure_le (raw : Bits)
    (failed : ∀ source target fuel cert,
      FrontEndMachine.sourceOutcome raw ≠ .success source target fuel cert) :
    runSteps raw ≤ 9 * raw.length + 31 := by
  rw [runSteps_failure raw failed]
  have front := FrontEndMachine.runSteps_le raw
  have cells := frontEndOutcome_cells_le raw
  omega

omit caller [DecidableEq K] in
theorem runSteps_le (raw : Bits) : runSteps raw ≤ raw.length * raw.length + 10 * raw.length + 36 := by
  by_cases failed : ∀ source target fuel cert,
      FrontEndMachine.sourceOutcome raw ≠ .success source target fuel cert
  · have bound := runSteps_failure_le raw failed
    omega
  · push Not at failed
    obtain ⟨source, target, fuel, cert, returned⟩ := failed
    rw [runSteps_success raw source target fuel cert returned]
    have front := FrontEndMachine.runSteps_le raw
    have sourceBound := StreamMachine.runSteps_le fuel cert (treeCode source) (treeCode target)
    have cellBound := (stream_run_final_cells_le fuel cert (treeCode source) (treeCode target)).trans
      (successful_stream_allowance_le raw source target fuel cert returned)
    have size := successful_raw_size raw source target fuel cert returned
    have factor : 2 * fuel.length + 3 * (treeCode source).length + 7 ≤ raw.length := by omega
    have certBound : cert.length ≤ raw.length := by omega
    have sourceLength : (treeCode source).length ≤ raw.length := by omega
    have product := Nat.mul_le_mul factor certBound
    omega

theorem PrefixProperty.single {P : Cfg Γ Λ R → Prop} {start finish : Cfg Γ Λ R}
    (executed : step caller start = some finish) (initial : P start) (final : P finish) :
    PrefixProperty caller P start 1 := by
  intro n bound reached run
  cases n with
  | zero =>
      have same : start = reached := Option.some.inj run
      exact same ▸ initial
  | succ n =>
      have zero : n = 0 := by omega
      subst n
      have same : finish = reached := Option.some.inj (executed.symm.trans run)
      exact same ▸ final

section ComposedPhysicalSpace
variable [Fintype K]

omit caller [DecidableEq K] in
theorem frontEndContext_cells (D : LocalData) (ctx : ∀ k, List (Γ k)) :
    FrontEndMachine.contextCells (frontEndContext D ctx) =
      D.moveReverse.length + D.path.length + contextCells ctx := by
  rw [FrontEndMachine.contextCells, Fintype.sum_sum_type, newBranch_sum]
  rfl

theorem result_prefix_cells (b : Bool) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    PrefixProperty caller (fun c => stackCells c ≤ max (localCells D) 1 + contextCells ctx)
      (cfg (some (phaseLabel (resultPhase b))) regs D ctx) (answerEvaluation b D).steps := by
  have bound (label : Option (Label Λ)) (r : Registers R) :
      stackCells (cfg label r D ctx) ≤ max (localCells D) 1 + contextCells ctx := by
    rw [stackCells_cfg]
    omega
  have first := PrefixProperty.single caller
    (P := fun c => stackCells c ≤ max (localCells D) 1 + contextCells ctx)
    (result_step caller b D regs ctx)
    (bound _ _) (bound _ _)
  have last := cleanup_prefix_cells caller 0 D (answerRegisters b regs) ctx
  have prefixZero : prefixCells 0 D = 0 := by simp [prefixCells, suffixCells, localCells]
  rw [prefixZero, Nat.zero_add] at last
  exact PrefixProperty.trans caller (result_step caller b D regs ctx) first last

theorem reject_prefix_cells (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    PrefixProperty caller (fun c => stackCells c ≤ max (localCells D) 1 + contextCells ctx)
      (cfg (some (phaseLabel rejectPhase)) regs D ctx) (answerEvaluation false D).steps := by
  have bound (label : Option (Label Λ)) (r : Registers R) :
      stackCells (cfg label r D ctx) ≤ max (localCells D) 1 + contextCells ctx := by
    rw [stackCells_cfg]
    omega
  have first := PrefixProperty.single caller
    (P := fun c => stackCells c ≤ max (localCells D) 1 + contextCells ctx)
    (reject_step caller D regs ctx)
    (bound _ _) (bound _ _)
  have last := cleanup_prefix_cells caller 0 D (answerRegisters false regs) ctx
  have prefixZero : prefixCells 0 D = 0 := by simp [prefixCells, suffixCells, localCells]
  rw [prefixZero, Nat.zero_add] at last
  exact PrefixProperty.trans caller (reject_step caller D regs ctx) first last

theorem stream_component_prefix_cells (q : StreamMachine.Phase) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    PrefixProperty caller (fun c => stackCells c ≤
      StreamMachine.phaseAllowance q (streamData D) (streamContext D ctx))
      (cfg (some (phaseLabel (streamPhase q))) regs D ctx) (StreamMachine.phaseSteps q (streamData D)) := by
  intro n bound reached executed
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
  have same : streamCfg localReached = reached := Option.some.inj (transported.symm.trans executed)
  subst reached
  rw [stackCells_streamCfg]
  have physical := StreamMachine.prefix_stackCells_le_dirty localCaller start n bounded localReached localRun
  simpa only [start, StreamMachine.allowance_phase_cfg] using physical

theorem stream_complete_prefix_cells (q : StreamMachine.Phase) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    PrefixProperty caller (fun c => stackCells c ≤
      max (StreamMachine.phaseAllowance q (streamData D) (streamContext D ctx)) (1 + contextCells ctx))
      (cfg (some (phaseLabel (streamPhase q))) regs D ctx) (streamEvaluation q D).steps := by
  let E := StreamMachine.evaluate q (streamData D)
  let out := withStream D E.data
  let limit := max (StreamMachine.phaseAllowance q (streamData D) (streamContext D ctx)) (1 + contextCells ctx)
  have firstRun := stream_phase_localRun caller q D regs ctx
  have component := stream_component_prefix_cells caller q D regs ctx
  have endpoint := component (StreamMachine.phaseSteps q (streamData D)) (Nat.le_refl _)
    _ (firstRun.iterate caller)
  change stackCells (cfg (some (phaseLabel (resultPhase E.result))) (streamReset regs) out ctx) ≤ _ at endpoint
  rw [stackCells_cfg] at endpoint
  have first := component.mono caller (Q := fun c => stackCells c ≤ limit)
    (fun _ h => h.trans (Nat.le_max_left _ _))
  have last := (result_prefix_cells caller E.result out (streamReset regs) ctx).mono caller
    (Q := fun c => stackCells c ≤ limit) (fun _ h => h.trans (by dsimp only [limit]; omega))
  exact PrefixProperty.trans caller (firstRun.iterate caller) first last

theorem dispatch_prefix_cells (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    PrefixProperty caller (fun c => stackCells c ≤
      max (StreamMachine.inspectAllowance (streamData D) (streamContext D ctx)) (1 + contextCells ctx))
      (cfg (some (phaseLabel dispatchPhase)) regs D ctx) (dispatchEvaluation D).steps := by
  let limit := max (StreamMachine.inspectAllowance (streamData D) (streamContext D ctx)) (1 + contextCells ctx)
  have after := stream_complete_prefix_cells caller StreamMachine.inspectPhase D (fullReset regs) ctx
  change PrefixProperty caller (fun c => stackCells c ≤ limit) _ _ at after
  have startBound := after 0 (Nat.zero_le _) _ rfl
  have beforeBound : stackCells (cfg (some (phaseLabel (Λ := Λ) dispatchPhase)) regs D ctx) ≤ limit := by
    simpa only [stackCells_cfg] using startBound
  have first := PrefixProperty.single caller (P := fun c => stackCells c ≤ limit)
    (dispatch_step caller D regs ctx) beforeBound startBound
  exact PrefixProperty.trans caller (dispatch_step caller D regs ctx) first after

theorem frontEnd_clean_prefix_cells (regs : Registers R) (raw : Bits) (ctx : ∀ k, List (Γ k)) :
    PrefixProperty caller (fun c => stackCells c ≤ raw.length + contextCells ctx)
      (entry regs raw ctx) (FrontEndMachine.runSteps raw) := by
  intro n bound reached executed
  let localCaller : FrontEndMachine.External (FrontEndCallerLabel Λ) → FrontEndStatement Γ Λ R := fun _ => .halt
  let oldContext := frontEndContext ({} : LocalData) ctx
  obtain ⟨localReached, localRun, _⟩ := FrontEndMachine.run_prefix localCaller regs raw oldContext n bound
  have trace := FrontEndMachine.run_source_trace localCaller regs raw oldContext
  have transported := frontEnd_prefix_transport caller localCaller n (FrontEndMachine.entry regs raw oldContext)
    (fun j earlier => trace.owned_prefix j (by omega))
  rw [localRun, frontEndCfg_entry] at transported
  have same : frontEndCfg localReached = reached := Option.some.inj (transported.symm.trans executed)
  subst reached
  rw [stackCells_frontEndCfg]
  have physical := FrontEndMachine.prefix_stackCells_le localCaller regs raw oldContext n bound localReached localRun
  simpa only [oldContext, frontEndContext_cells, List.length_nil, Nat.zero_add] using physical

theorem outcomeContinuation_prefix_cells (raw : Bits) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    PrefixProperty caller (fun c => stackCells c ≤ max raw.length 1 + contextCells ctx)
      (frontEndOutcomeCfg (FrontEndMachine.sourceOutcome raw) regs ctx)
      (outcomeContinuation (FrontEndMachine.sourceOutcome raw)).steps := by
  have frontMass := frontEndOutcome_cells_le raw
  cases outcome : FrontEndMachine.sourceOutcome raw with
  | frameFailure =>
      exact (reject_prefix_cells caller {} (FrontEndMachine.resetFramer regs) ctx).mono caller
        (fun _ h => h.trans (by simp only [localCells, List.length_nil] at h ⊢; omega))
  | inputDecodeFailure cert =>
      rw [outcome] at frontMass
      exact (reject_prefix_cells caller { certificateBits := cert } (FrontEndMachine.afterInputDecoder regs) ctx).mono caller
        (fun _ h => h.trans (by change localCells { certificateBits := cert } ≤ raw.length at frontMass; omega))
  | inputParseFailure input cert =>
      rw [outcome] at frontMass
      exact (reject_prefix_cells caller { inputRaw := input, certificateBits := cert } (FrontEndMachine.reset regs) ctx).mono caller
        (fun _ h => h.trans (by change localCells { inputRaw := input, certificateBits := cert } ≤ raw.length at frontMass; omega))
  | certificateDecodeFailure source target fuel =>
      rw [outcome] at frontMass
      exact (reject_prefix_cells caller
        { sourceTree := treeCode source, targetTree := treeCode target, fuel := fuel } (FrontEndMachine.reset regs) ctx).mono caller
        (fun _ h => h.trans (by change localCells { sourceTree := treeCode source, targetTree := treeCode target, fuel := fuel } ≤ raw.length at frontMass; omega))
  | success source target fuel cert =>
      let D := frontEndOutcomeData (.success source target fuel cert)
      have sourceBound := StreamMachine.inspectAllowance_clean_le fuel cert (treeCode source) (treeCode target)
        (streamContext D ctx)
      have context : StreamMachine.contextCells (streamContext D ctx) = contextCells ctx := by
        rw [streamContext_cells]
        simp only [D, frontEndOutcomeData, List.length_nil, Nat.zero_add]
      rw [context] at sourceBound
      have size := successful_stream_allowance_le raw source target fuel cert outcome
      exact (dispatch_prefix_cells caller D (FrontEndMachine.reset regs) ctx).mono caller
        (fun _ h => h.trans (by change StreamMachine.inspectAllowance (streamData D) (streamContext D ctx) ≤ _ at sourceBound; omega))

theorem run_prefix_cells (regs : Registers R) (raw : Bits) (ctx : ∀ k, List (Γ k)) :
    PrefixProperty caller (fun c => stackCells c ≤ max raw.length 1 + contextCells ctx)
      (entry regs raw ctx) (runSteps raw) := by
  have first := (frontEnd_clean_prefix_cells caller regs raw ctx).mono caller
    (Q := fun c => stackCells c ≤ max raw.length 1 + contextCells ctx)
    (fun _ h => h.trans (Nat.add_le_add_right (Nat.le_max_left _ _) _))
  have last := outcomeContinuation_prefix_cells caller raw regs ctx
  exact PrefixProperty.trans caller ((frontEnd_clean_localRun caller regs raw ctx).iterate caller) first last

theorem run_peak (regs : Registers R) (raw : Bits) (ctx : ∀ k, List (Γ k)) :
    ExactPeak caller (entry regs raw ctx) (runSteps raw) (max raw.length 1 + contextCells ctx) := by
  refine ⟨run_prefix_cells caller regs raw ctx, ?_⟩
  by_cases nonempty : 1 ≤ raw.length
  · refine ⟨0, Nat.zero_le _, _, rfl, ?_⟩
    simp only [entry, stackCells_cfg, cleanData, localCells, List.length_nil, Nat.add_zero,
      Nat.max_eq_left nonempty]
  · have small : raw.length ≤ 1 := by omega
    refine ⟨runSteps raw, Nat.le_refl _, _, run_output caller regs raw ctx, ?_⟩
    simp only [stackCells_cfg, localCells, List.length_nil, List.length_cons, Nat.zero_add,
      Nat.add_zero, Nat.max_eq_right small]

end ComposedPhysicalSpace


end Resources.RotationCertificate.FrontEndStreamMachine

