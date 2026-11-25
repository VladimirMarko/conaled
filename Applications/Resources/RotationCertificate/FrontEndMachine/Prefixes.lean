import Applications.Resources.RotationCertificate.FrontEndMachine.Execution

/-!
# FrontEndMachine: Prefixes
-/

set_option autoImplicit false
set_option warningAsError true

namespace Resources.RotationCertificate.FrontEndMachine
open Resources.BinaryCounter (Bits)

variable {K Λ R : Type} {Γ : K → Type}

def framerResult (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    Option (Bits × Bits) → Cfg Γ Λ R
  | none => resultCfg regs ctx .frameFailure
  | some (input, cert) => inputDecoderEntry regs input cert ctx

def inputDecoderResult (regs : Registers R) (cert : Bits) (ctx : ∀ k, List (Γ k)) :
    Option Word → Cfg Γ Λ R
  | none => resultCfg regs ctx (.inputDecodeFailure cert)
  | some word => inputEntry regs word cert ctx

def inputResult (regs : Registers R) (input : Word) (cert : Bits)
    (ctx : ∀ k, List (Γ k)) : Option ParsedInput → Cfg Γ Λ R
  | none => resultCfg regs ctx (.inputParseFailure input cert)
  | some (source, target, fuel) => certificateDecoderEntry regs source target fuel cert ctx

def certificateDecoderResult (regs : Registers R) (source target : BinaryTree Unit)
    (fuel : Bits) (ctx : ∀ k, List (Γ k)) : Option Word → Cfg Γ Λ R
  | none => resultCfg regs ctx (.certificateDecodeFailure source target fuel)
  | some cert => resultCfg regs ctx (.success source target fuel cert)

theorem framer_start_transport (regs : Registers R) (raw : Bits) (ctx : ∀ k, List (Γ k)) :
    framerCfg (Λ := Λ) (OpenFramingMachine.cfg (some (OpenFramingMachine.phaseLabel .scanPrefix))
      (framerRegisterEquiv.symm regs) raw [] [] [] [] (framerContext {} ctx)) = entry regs raw ctx := by
  change framerCfg (framerView _ _ { framedRaw := raw } ctx) = _
  rw [framerCfg_view]
  simp only [Option.map_some, framerLabelEquiv_phase, Equiv.apply_symm_apply]
  rfl

theorem framer_result_transport (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (result : Option (Bits × Bits)) :
    framerCfg (Λ := Λ) (OpenFramingMachine.scanResult (framerRegisterEquiv.symm regs)
      [] [] [] [] (framerContext {} ctx) result) = framerResult regs ctx result := by
  cases result with
  | none =>
      change framerCfg (framerView (some (OpenFramingMachine.resultLabel .failure))
        (OpenFramingMachine.reset (framerRegisterEquiv.symm regs)) {} ctx) = _
      rw [framerCfg_view]
      simp only [Option.map_some, framerLabelEquiv_failure, framerRegisterEquiv_reset,
        Equiv.apply_symm_apply]
      rfl
  | some pair =>
      rcases pair with ⟨input, cert⟩
      simp only [OpenFramingMachine.scanResult, List.reverse_nil, List.nil_append, List.append_nil]
      change framerCfg (framerView (some (OpenFramingMachine.resultLabel .success))
        (OpenFramingMachine.reset (framerRegisterEquiv.symm regs)) (framedData input cert) ctx) = _
      rw [framerCfg_view]
      simp only [Option.map_some, framerLabelEquiv_success, framerRegisterEquiv_reset,
        Equiv.apply_symm_apply]
      rfl

theorem inputDecoder_start_transport (regs : Registers R) (input cert : Bits)
    (ctx : ∀ k, List (Γ k)) :
    inputDecoderCfg (Λ := Λ) (OpenDecoderMachine.cfg (some (OpenDecoderMachine.phaseLabel .scan))
      (decoderRegisterEquiv.symm (resetFramer regs)) input [] []
      (decoderContext .input (framedData input cert) ctx)) = inputDecoderEntry regs input cert ctx := by
  change inputDecoderCfg (inputDecoderView _ _ (framedData input cert) ctx) = _
  rw [inputDecoderCfg_view]
  simp only [Option.map_some, inputDecoderLabelEquiv_phase, Equiv.apply_symm_apply]
  rfl

theorem inputDecoder_result_transport (regs : Registers R) (input cert : Bits)
    (ctx : ∀ k, List (Γ k)) (result : Option Word) :
    inputDecoderCfg (Λ := Λ) (OpenDecoderMachine.resultCfg result [] []
      (decoderRegisterEquiv.symm (resetFramer regs))
      (decoderContext .input (framedData input cert) ctx)) = inputDecoderResult regs cert ctx result := by
  cases result with
  | none =>
      change inputDecoderCfg (inputDecoderView (some (OpenDecoderMachine.resultLabel .failure))
        (OpenDecoderMachine.reset (decoderRegisterEquiv.symm (resetFramer regs)))
        { certificateBits := cert } ctx) = _
      rw [inputDecoderCfg_view]
      simp only [Option.map_some, inputDecoderLabelEquiv_failure, decoderRegisterEquiv_reset]
      rfl
  | some word =>
      simp only [OpenDecoderMachine.resultCfg, List.reverse_nil, List.nil_append, List.append_nil]
      change inputDecoderCfg (inputDecoderView (some (OpenDecoderMachine.resultLabel .success))
        (OpenDecoderMachine.reset (decoderRegisterEquiv.symm (resetFramer regs)))
        (decodedInputData word cert) ctx) = _
      rw [inputDecoderCfg_view]
      simp only [Option.map_some, inputDecoderLabelEquiv_success, decoderRegisterEquiv_reset]
      rfl

theorem input_start_transport (regs : Registers R) (input : Word) (cert : Bits)
    (ctx : ∀ k, List (Γ k)) :
    inputCfg (Λ := Λ) (InputParserMachine.entry (inputRegisterEquiv.symm (afterInputDecoder regs)) input
      (inputContext (decodedInputData input cert) ctx)) = inputEntry regs input cert ctx := by
  change inputCfg (inputView _ _ (decodedInputData input cert) ctx) = _
  rw [inputCfg_view]
  rfl

theorem input_result_transport (regs : Registers R) (input : Word) (cert : Bits)
    (ctx : ∀ k, List (Γ k)) (result : Option ParsedInput) :
    inputCfg (Λ := Λ) (InputParserMachine.resultCfg (inputRegisterEquiv.symm (afterInputDecoder regs)) input
      (inputContext (decodedInputData input cert) ctx) result) = inputResult regs input cert ctx result := by
  cases result with
  | none =>
      change inputCfg (inputView (some (InputParserMachine.resultLabel .failure))
        (InputParserMachine.reset (inputRegisterEquiv.symm (afterInputDecoder regs)))
        (decodedInputData input cert) ctx) = _
      rw [inputCfg_view]
      rfl
  | some parsed =>
      rcases parsed with ⟨source, target, fuel⟩
      change inputCfg (inputView (some (InputParserMachine.resultLabel .success))
        (InputParserMachine.reset (inputRegisterEquiv.symm (afterInputDecoder regs)))
        (parsedData source target fuel cert) ctx) = _
      rw [inputCfg_view]
      rfl

theorem certificateDecoder_start_transport (regs : Registers R) (source target : BinaryTree Unit)
    (fuel cert : Bits) (ctx : ∀ k, List (Γ k)) :
    certificateDecoderCfg (Λ := Λ) (OpenDecoderMachine.cfg (some (OpenDecoderMachine.phaseLabel .scan))
      (decoderRegisterEquiv.symm (reset regs)) cert [] []
      (decoderContext .certificate (parsedData source target fuel cert) ctx)) =
        certificateDecoderEntry regs source target fuel cert ctx := by
  change certificateDecoderCfg (certificateDecoderView _ _ (parsedData source target fuel cert) ctx) = _
  rw [certificateDecoderCfg_view]
  simp only [Option.map_some, certificateDecoderLabelEquiv_phase, Equiv.apply_symm_apply]
  rfl

theorem certificateDecoder_result_transport (regs : Registers R) (source target : BinaryTree Unit)
    (fuel cert : Bits) (ctx : ∀ k, List (Γ k)) (result : Option Word) :
    certificateDecoderCfg (Λ := Λ) (OpenDecoderMachine.resultCfg result [] []
      (decoderRegisterEquiv.symm (reset regs))
      (decoderContext .certificate (parsedData source target fuel cert) ctx)) =
        certificateDecoderResult regs source target fuel ctx result := by
  cases result with
  | none =>
      change certificateDecoderCfg (certificateDecoderView (some (OpenDecoderMachine.resultLabel .failure))
        (OpenDecoderMachine.reset (decoderRegisterEquiv.symm (reset regs)))
        (parsedData source target fuel []) ctx) = _
      rw [certificateDecoderCfg_view]
      simp only [Option.map_some, certificateDecoderLabelEquiv_failure, decoderRegisterEquiv_reset]
      rfl
  | some word =>
      simp only [OpenDecoderMachine.resultCfg, List.reverse_nil, List.nil_append, List.append_nil]
      change certificateDecoderCfg (certificateDecoderView (some (OpenDecoderMachine.resultLabel .success))
        (OpenDecoderMachine.reset (decoderRegisterEquiv.symm (reset regs)))
        (successData source target fuel word) ctx) = _
      rw [certificateDecoderCfg_view]
      simp only [Option.map_some, certificateDecoderLabelEquiv_success, decoderRegisterEquiv_reset]
      rfl

theorem owned_framerCfg (c : FramerCfg Γ Λ R) (owned : OpenFramingMachine.Owned c.l) :
    Owned (framerCfg c).l := by
  cases control : c.l with
  | none => rw [control] at owned; cases owned
  | some label =>
      cases label with
      | inl phase =>
          change Owned (c.l.map framerLabelEquiv)
          rw [control]
          change Owned (some (framerLabelEquiv (OpenFramingMachine.phaseLabel phase)))
          rw [framerLabelEquiv_phase]
          exact owned_framer phase
      | inr exit => rw [control] at owned; cases owned

theorem owned_inputCfg (c : InputCfg Γ Λ R) (owned : InputParserMachine.FullOwned c.l) :
    Owned (inputCfg c).l := by
  cases control : c.l with
  | none => rw [control] at owned; cases owned
  | some label =>
      change Owned (c.l.map inputLabelEquiv)
      rw [control]
      exact input_fullOwned_owned label (by simpa only [control] using owned)

theorem owned_inputDecoderCfg (c : InputDecoderCfg Γ Λ R) (owned : OpenDecoderMachine.Owned c.l) :
    Owned (inputDecoderCfg c).l := by
  cases control : c.l with
  | none => rw [control] at owned; cases owned
  | some label =>
      cases label with
      | inl phase =>
          change Owned (c.l.map inputDecoderLabelEquiv)
          rw [control]
          change Owned (some (inputDecoderLabelEquiv (OpenDecoderMachine.phaseLabel phase)))
          rw [inputDecoderLabelEquiv_phase]
          exact owned_inputDecoder phase
      | inr exit => rw [control] at owned; cases owned

theorem owned_certificateDecoderCfg (c : CertificateDecoderCfg Γ Λ R)
    (owned : OpenDecoderMachine.Owned c.l) : Owned (certificateDecoderCfg c).l := by
  cases control : c.l with
  | none => rw [control] at owned; cases owned
  | some label =>
      cases label with
      | inl phase =>
          change Owned (c.l.map certificateDecoderLabelEquiv)
          rw [control]
          change Owned (some (certificateDecoderLabelEquiv (OpenDecoderMachine.phaseLabel phase)))
          rw [certificateDecoderLabelEquiv_phase]
          exact owned_certificateDecoder phase
      | inr exit => rw [control] at owned; cases owned

variable [DecidableEq K]
variable (caller : External Λ → Statement Γ Λ R)

/-- Actual execution and strict-prefix ownership. The caller at the endpoint has not run. -/
structure Trace (start finish : Cfg Γ Λ R) (ticks : Nat) : Prop where
  run : (next caller)^[ticks] (some start) = some finish
  owned_prefix : ∀ n, n < ticks → ∃ reached,
    (next caller)^[n] (some start) = some reached ∧ Owned reached.l

theorem iterate_trans {start middle finish : Cfg Γ Λ R} {first second : Nat}
    (before : (next caller)^[first] (some start) = some middle)
    (after : (next caller)^[second] (some middle) = some finish) :
    (next caller)^[first + second] (some start) = some finish := by
  rw [Nat.add_comm first second, Function.iterate_add_apply, before, after]

theorem Trace.trans {start middle finish : Cfg Γ Λ R} {first second : Nat}
    (before : Trace caller start middle first) (after : Trace caller middle finish second) :
    Trace caller start finish (first + second) := by
  refine ⟨iterate_trans caller before.run after.run, ?_⟩
  intro n bound
  by_cases early : n < first
  · exact before.owned_prefix n early
  · obtain ⟨reached, executed, owned⟩ := after.owned_prefix (n - first) (by omega)
    refine ⟨reached, ?_, owned⟩
    have total : first + (n - first) = n := by omega
    simpa only [total] using iterate_trans caller before.run executed

theorem framer_trace (regs : Registers R) (raw : Bits) (ctx : ∀ k, List (Γ k)) :
    Trace caller (entry regs raw ctx) (framerResult regs ctx (BitPairFraming.unframe raw))
      (BitPairFraming.runSteps raw) := by
  let localCaller : OpenFramingMachine.External (FramerCaller Λ) → FramerStatement Γ Λ R := fun _ => .halt
  let localRegs := framerRegisterEquiv.symm regs
  let localContext := framerContext (Γ := Γ) {} ctx
  have whole := framer_run_installed caller localCaller raw localRegs localContext
  rw [framer_start_transport, framer_result_transport] at whole
  refine ⟨whole, ?_⟩
  intro n strict
  obtain ⟨reached, executed, owned⟩ :=
    (OpenFramingMachine.run_first_return localCaller raw localRegs localContext).2 n strict
  have translated := framer_prefix_installed caller localCaller n
    (OpenFramingMachine.cfg (some (OpenFramingMachine.phaseLabel .scanPrefix))
      localRegs raw [] [] [] [] localContext)
    (fun j smaller => (OpenFramingMachine.run_first_return localCaller raw localRegs localContext).2
      j (by omega))
  rw [framer_start_transport, executed] at translated
  exact ⟨framerCfg reached, translated, owned_framerCfg reached owned⟩

theorem inputDecoder_trace (regs : Registers R) (input cert : Bits) (ctx : ∀ k, List (Γ k)) :
    Trace caller (inputDecoderEntry regs input cert ctx)
      (inputDecoderResult regs cert ctx (unpackWordRun input).1) (OpenDecoderMachine.runSteps input) := by
  let localCaller : OpenDecoderMachine.External (InputDecoderCaller Λ) → InputDecoderStatement Γ Λ R := fun _ => .halt
  let localRegs := decoderRegisterEquiv.symm (resetFramer regs)
  let localContext := decoderContext (Γ := Γ) .input (framedData input cert) ctx
  have whole := inputDecoder_scan_installed caller localCaller input [] [] localRegs localContext
  simp only [List.length_nil, Nat.add_zero] at whole
  rw [inputDecoder_start_transport, inputDecoder_result_transport] at whole
  refine ⟨whole, ?_⟩
  intro n strict
  have within : ∀ j, j < OpenDecoderMachine.runSteps input → ∃ reached,
      (OpenDecoderMachine.next localCaller)^[j]
        (some (OpenDecoderMachine.cfg (some (OpenDecoderMachine.phaseLabel .scan))
          localRegs input [] [] localContext)) = some reached ∧ OpenDecoderMachine.Owned reached.l := by
    intro j small
    obtain ⟨reached, executed, _, _, owned, _⟩ :=
      OpenDecoderMachine.phase_prefix localCaller .scan input [] [] localRegs localContext j (by
        change j ≤ OpenDecoderMachine.runSteps input + 0
        omega)
    exact ⟨reached, executed, owned.mp (by simpa only [OpenDecoderMachine.phaseSteps, List.length_nil,
      Nat.add_zero] using small)⟩
  obtain ⟨reached, executed, owned⟩ := within n strict
  have translated := inputDecoder_prefix_installed caller localCaller n
    (OpenDecoderMachine.cfg (some (OpenDecoderMachine.phaseLabel .scan)) localRegs input [] [] localContext)
    (fun j smaller => within j (by omega))
  rw [inputDecoder_start_transport, executed] at translated
  exact ⟨inputDecoderCfg reached, translated, owned_inputDecoderCfg reached owned⟩

theorem input_trace (regs : Registers R) (input : Word) (cert : Bits) (ctx : ∀ k, List (Γ k)) :
    Trace caller (inputEntry regs input cert ctx)
      (inputResult regs input cert ctx (parseInputRun input).1) (InputParserMachine.inputSteps input) := by
  let localCaller : InputParserMachine.External (ExtraLabel Λ) → InputStatement Γ Λ R := fun _ => .halt
  let localRegs := inputRegisterEquiv.symm (afterInputDecoder regs)
  let localContext := inputContext (Γ := Γ) (decodedInputData input cert) ctx
  have whole := input_run_installed caller localCaller input localRegs localContext
  rw [input_start_transport, input_result_transport] at whole
  refine ⟨whole, ?_⟩
  intro n strict
  have within : ∀ j, j < InputParserMachine.inputSteps input → ∃ reached,
      (InputParserMachine.next localCaller)^[j] (some (InputParserMachine.entry localRegs input localContext)) =
        some reached ∧ InputParserMachine.FullOwned reached.l := by
    intro j small
    obtain ⟨reached, executed, _, _, owned⟩ :=
      InputParserMachine.run_prefix localCaller input localRegs localContext j (Nat.le_of_lt small)
    exact ⟨reached, executed, owned.mp small⟩
  obtain ⟨reached, executed, owned⟩ := within n strict
  have translated := input_prefix_installed caller localCaller n
    (InputParserMachine.entry localRegs input localContext) (fun j smaller => within j (by omega))
  rw [input_start_transport, executed] at translated
  exact ⟨inputCfg reached, translated, owned_inputCfg reached owned⟩

theorem certificateDecoder_trace (regs : Registers R) (source target : BinaryTree Unit)
    (fuel cert : Bits) (ctx : ∀ k, List (Γ k)) :
    Trace caller (certificateDecoderEntry regs source target fuel cert ctx)
      (certificateDecoderResult regs source target fuel ctx (unpackWordRun cert).1)
      (OpenDecoderMachine.runSteps cert) := by
  let localCaller : OpenDecoderMachine.External (CertificateDecoderCaller Λ) →
    CertificateDecoderStatement Γ Λ R := fun _ => .halt
  let localRegs := decoderRegisterEquiv.symm (reset regs)
  let localContext := decoderContext (Γ := Γ) .certificate (parsedData source target fuel cert) ctx
  have whole := certificateDecoder_scan_installed caller localCaller cert [] [] localRegs localContext
  simp only [List.length_nil, Nat.add_zero] at whole
  rw [certificateDecoder_start_transport, certificateDecoder_result_transport] at whole
  refine ⟨whole, ?_⟩
  intro n strict
  have within : ∀ j, j < OpenDecoderMachine.runSteps cert → ∃ reached,
      (OpenDecoderMachine.next localCaller)^[j]
        (some (OpenDecoderMachine.cfg (some (OpenDecoderMachine.phaseLabel .scan))
          localRegs cert [] [] localContext)) = some reached ∧ OpenDecoderMachine.Owned reached.l := by
    intro j small
    obtain ⟨reached, executed, _, _, owned, _⟩ :=
      OpenDecoderMachine.phase_prefix localCaller .scan cert [] [] localRegs localContext j (by
        change j ≤ OpenDecoderMachine.runSteps cert + 0
        omega)
    exact ⟨reached, executed, owned.mp (by simpa only [OpenDecoderMachine.phaseSteps, List.length_nil,
      Nat.add_zero] using small)⟩
  obtain ⟨reached, executed, owned⟩ := within n strict
  have translated := certificateDecoder_prefix_installed caller localCaller n
    (OpenDecoderMachine.cfg (some (OpenDecoderMachine.phaseLabel .scan)) localRegs cert [] [] localContext)
    (fun j smaller => within j (by omega))
  rw [certificateDecoder_start_transport, executed] at translated
  exact ⟨certificateDecoderCfg reached, translated, owned_certificateDecoderCfg reached owned⟩

/-- Unconditional composition follows the actual returned fields at every stage. -/
theorem run_source_trace (regs : Registers R) (raw : Bits) (ctx : ∀ k, List (Γ k)) :
    Trace caller (entry regs raw ctx) (resultCfg regs ctx (sourceOutcome raw)) (runSteps raw) := by
  have framing := framer_trace caller regs raw ctx
  cases framed : BitPairFraming.unframe raw with
  | none => simpa only [runSteps, sourceOutcome, framed, Nat.add_zero, framerResult] using framing
  | some pair =>
      rcases pair with ⟨input, cert⟩
      rw [framed] at framing
      have decoding := inputDecoder_trace caller regs input cert ctx
      cases decoded : (unpackWordRun input).1 with
      | none =>
          rw [decoded] at decoding
          simpa only [runSteps, sourceOutcome, framed, decoded, Nat.add_zero,
            framerResult, inputDecoderResult] using Trace.trans caller framing decoding
      | some word =>
          rw [decoded] at decoding
          have parsing := input_trace caller regs word cert ctx
          cases parsed : (parseInputRun word).1 with
          | none =>
              rw [parsed] at parsing
              simpa only [runSteps, sourceOutcome, framed, decoded, parsed, Nat.add_zero,
                framerResult, inputDecoderResult, inputResult] using
                Trace.trans caller framing (Trace.trans caller decoding parsing)
          | some triple =>
              rcases triple with ⟨source, target, fuel⟩
              rw [parsed] at parsing
              have certificate := certificateDecoder_trace caller regs source target fuel cert ctx
              cases certified : (unpackWordRun cert).1 with
              | none =>
                  rw [certified] at certificate
                  simpa only [runSteps, sourceOutcome, framed, decoded, parsed, certified,
                    framerResult, inputDecoderResult, inputResult, certificateDecoderResult] using
                    Trace.trans caller framing (Trace.trans caller decoding (Trace.trans caller parsing certificate))
              | some moves =>
                  rw [certified] at certificate
                  simpa only [runSteps, sourceOutcome, framed, decoded, parsed, certified,
                    framerResult, inputDecoderResult, inputResult, certificateDecoderResult] using
                    Trace.trans caller framing (Trace.trans caller decoding (Trace.trans caller parsing certificate))

theorem run_source (regs : Registers R) (raw : Bits) (ctx : ∀ k, List (Γ k)) :
    (next caller)^[runSteps raw] (some (entry regs raw ctx)) =
      some (resultCfg regs ctx (sourceOutcome raw)) :=
  (run_source_trace caller regs raw ctx).run

omit [DecidableEq K] in
theorem resultCfg_not_owned (regs : Registers R) (ctx : ∀ k, List (Γ k)) (outcome : Outcome) :
    ¬ Owned (resultCfg (Λ := Λ) regs ctx outcome).l := by
  cases outcome <;> first | exact not_owned_reject | exact not_owned_dispatch

theorem run_prefix (regs : Registers R) (raw : Bits) (ctx : ∀ k, List (Γ k))
    (n : Nat) (bound : n ≤ runSteps raw) :
    ∃ reached, (next caller)^[n] (some (entry regs raw ctx)) = some reached ∧
      (n < runSteps raw ↔ Owned reached.l) := by
  by_cases strict : n < runSteps raw
  · obtain ⟨reached, executed, owned⟩ := (run_source_trace caller regs raw ctx).owned_prefix n strict
    exact ⟨reached, executed, iff_of_true strict owned⟩
  · have equal : n = runSteps raw := by omega
    subst n
    exact ⟨resultCfg regs ctx (sourceOutcome raw), run_source caller regs raw ctx,
      iff_of_false (Nat.lt_irrefl _) (resultCfg_not_owned regs ctx (sourceOutcome raw))⟩

/-- The exact clock reaches a live exit, never an outer failure or a halt convention. -/
def runTimed (regs : Registers R) (raw : Bits) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller) (entry regs raw ctx)
      (some (resultCfg regs ctx (sourceOutcome raw))) (runSteps raw) where
  steps := runSteps raw
  evals_in_steps := run_source caller regs raw ctx
  steps_le_m := Nat.le_refl _

def runTimedLinear (regs : Registers R) (raw : Bits) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller) (entry regs raw ctx)
      (some (resultCfg regs ctx (sourceOutcome raw))) (8 * raw.length + 13) where
  steps := runSteps raw
  evals_in_steps := run_source caller regs raw ctx
  steps_le_m := runSteps_le raw

end Resources.RotationCertificate.FrontEndMachine

namespace Resources.RotationCertificate.FrontEndMachine
open Resources.BinaryCounter (Bits)

variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
variable (caller : External Λ → Statement Γ Λ R)

theorem framer_prefix_lift (regs : Registers R) (raw : Bits) (ctx : ∀ k, List (Γ k))
    (n : Nat) (bound : n ≤ BitPairFraming.runSteps raw) :
    ∃ reached : FramerCfg Γ Λ R,
      (OpenFramingMachine.next (fun _ => .halt))^[n]
        (some (OpenFramingMachine.cfg (some (OpenFramingMachine.phaseLabel .scanPrefix))
          (framerRegisterEquiv.symm regs) raw [] [] [] [] (framerContext {} ctx))) = some reached ∧
      (next caller)^[n] (some (entry regs raw ctx)) = some (framerCfg reached) := by
  let localCaller : OpenFramingMachine.External (FramerCaller Λ) → FramerStatement Γ Λ R := fun _ => .halt
  obtain ⟨reached, executed, _, _, _, _⟩ := OpenFramingMachine.run_prefix localCaller raw
    (framerRegisterEquiv.symm regs) (framerContext {} ctx) n bound
  have translated := framer_prefix_installed caller localCaller n
    (OpenFramingMachine.cfg (some (OpenFramingMachine.phaseLabel .scanPrefix))
      (framerRegisterEquiv.symm regs) raw [] [] [] [] (framerContext {} ctx))
    (fun j strict => (OpenFramingMachine.run_first_return localCaller raw
      (framerRegisterEquiv.symm regs) (framerContext {} ctx)).2 j (by omega))
  rw [framer_start_transport, executed] at translated
  exact ⟨reached, executed, translated⟩

theorem inputDecoder_prefix_lift (regs : Registers R) (input cert : Bits) (ctx : ∀ k, List (Γ k))
    (n : Nat) (bound : n ≤ OpenDecoderMachine.runSteps input) :
    ∃ reached : InputDecoderCfg Γ Λ R,
      (OpenDecoderMachine.next (fun _ => .halt))^[n]
        (some (OpenDecoderMachine.cfg (some (OpenDecoderMachine.phaseLabel .scan))
          (decoderRegisterEquiv.symm (resetFramer regs)) input [] []
          (decoderContext .input (framedData input cert) ctx))) = some reached ∧
      (next caller)^[n] (some (inputDecoderEntry regs input cert ctx)) = some (inputDecoderCfg reached) := by
  let localCaller : OpenDecoderMachine.External (InputDecoderCaller Λ) → InputDecoderStatement Γ Λ R := fun _ => .halt
  let localRegs := decoderRegisterEquiv.symm (resetFramer regs)
  let localContext := decoderContext (Γ := Γ) .input (framedData input cert) ctx
  have phaseBound : n ≤ OpenDecoderMachine.phaseSteps .scan input [] := by
    simpa only [OpenDecoderMachine.phaseSteps, List.length_nil, Nat.add_zero] using bound
  obtain ⟨reached, executed, _, _, _, _⟩ :=
    OpenDecoderMachine.phase_prefix localCaller .scan input [] [] localRegs localContext n phaseBound
  have translated := inputDecoder_prefix_installed caller localCaller n
    (OpenDecoderMachine.cfg (some (OpenDecoderMachine.phaseLabel .scan)) localRegs input [] [] localContext) (by
      intro j strict
      obtain ⟨actual, run, _, _, owned, _⟩ :=
        OpenDecoderMachine.phase_prefix localCaller .scan input [] [] localRegs localContext j (by omega)
      exact ⟨actual, run, owned.mp (by omega)⟩)
  rw [inputDecoder_start_transport, executed] at translated
  exact ⟨reached, executed, translated⟩

theorem input_prefix_lift (regs : Registers R) (input : Word) (cert : Bits) (ctx : ∀ k, List (Γ k))
    (n : Nat) (bound : n ≤ InputParserMachine.inputSteps input) :
    ∃ reached : InputCfg Γ Λ R,
      (InputParserMachine.next (fun _ => .halt))^[n]
        (some (InputParserMachine.entry (inputRegisterEquiv.symm (afterInputDecoder regs)) input
          (inputContext (decodedInputData input cert) ctx))) = some reached ∧
      (next caller)^[n] (some (inputEntry regs input cert ctx)) = some (inputCfg reached) := by
  let localCaller : InputParserMachine.External (ExtraLabel Λ) → InputStatement Γ Λ R := fun _ => .halt
  let localRegs := inputRegisterEquiv.symm (afterInputDecoder regs)
  let localContext := inputContext (Γ := Γ) (decodedInputData input cert) ctx
  obtain ⟨reached, executed, _, _, _⟩ :=
    InputParserMachine.run_prefix localCaller input localRegs localContext n bound
  have translated := input_prefix_installed caller localCaller n
    (InputParserMachine.entry localRegs input localContext) (by
      intro j strict
      obtain ⟨actual, run, _, _, owned⟩ :=
        InputParserMachine.run_prefix localCaller input localRegs localContext j (by omega)
      exact ⟨actual, run, owned.mp (by omega)⟩)
  rw [input_start_transport, executed] at translated
  exact ⟨reached, executed, translated⟩

theorem certificateDecoder_prefix_lift (regs : Registers R) (source target : BinaryTree Unit)
    (fuel cert : Bits) (ctx : ∀ k, List (Γ k)) (n : Nat)
    (bound : n ≤ OpenDecoderMachine.runSteps cert) :
    ∃ reached : CertificateDecoderCfg Γ Λ R,
      (OpenDecoderMachine.next (fun _ => .halt))^[n]
        (some (OpenDecoderMachine.cfg (some (OpenDecoderMachine.phaseLabel .scan))
          (decoderRegisterEquiv.symm (reset regs)) cert [] []
          (decoderContext .certificate (parsedData source target fuel cert) ctx))) = some reached ∧
      (next caller)^[n] (some (certificateDecoderEntry regs source target fuel cert ctx)) =
        some (certificateDecoderCfg reached) := by
  let localCaller : OpenDecoderMachine.External (CertificateDecoderCaller Λ) →
    CertificateDecoderStatement Γ Λ R := fun _ => .halt
  let localRegs := decoderRegisterEquiv.symm (reset regs)
  let localContext := decoderContext (Γ := Γ) .certificate (parsedData source target fuel cert) ctx
  have phaseBound : n ≤ OpenDecoderMachine.phaseSteps .scan cert [] := by
    simpa only [OpenDecoderMachine.phaseSteps, List.length_nil, Nat.add_zero] using bound
  obtain ⟨reached, executed, _, _, _, _⟩ :=
    OpenDecoderMachine.phase_prefix localCaller .scan cert [] [] localRegs localContext n phaseBound
  have translated := certificateDecoder_prefix_installed caller localCaller n
    (OpenDecoderMachine.cfg (some (OpenDecoderMachine.phaseLabel .scan)) localRegs cert [] [] localContext) (by
      intro j strict
      obtain ⟨actual, run, _, _, owned, _⟩ :=
        OpenDecoderMachine.phase_prefix localCaller .scan cert [] [] localRegs localContext j (by omega)
      exact ⟨actual, run, owned.mp (by omega)⟩)
  rw [certificateDecoder_start_transport, executed] at translated
  exact ⟨reached, executed, translated⟩

variable [Fintype K]

def contextCells (ctx : ∀ k, List (Γ k)) : Nat := ∑ k, (ctx k).length
def stackCells (c : Cfg Γ Λ R) : Nat := ∑ k, (c.stk k).length

def localCells (data : LocalData) : Nat :=
  data.framedRaw.length + data.frameFirstReverse.length + data.frameCertReverse.length +
  data.inputBits.length + data.certificateBits.length + data.inputRaw.length + data.decodeReverse.length +
  data.certificateWord.length + data.sourceTree.length + data.targetTree.length + data.treeReverse.length +
  data.pending.length + data.fuel.length + data.bitsReverse.length

theorem localStack_sum (f : LocalStack → Nat) :
    ∑ k, f k = f .framedRaw + f .frameFirstReverse + f .frameCertReverse + f .inputBits +
      f .certificateBits + f .inputRaw + f .decodeReverse + f .certificateWord + f .sourceTree +
      f .targetTree + f .treeReverse + f .pending + f .fuel + f .bitsReverse := by
  have enumeration : (Finset.univ : Finset LocalStack) =
      {.framedRaw, .frameFirstReverse, .frameCertReverse, .inputBits, .certificateBits,
       .inputRaw, .decodeReverse, .certificateWord, .sourceTree, .targetTree, .treeReverse,
       .pending, .fuel, .bitsReverse} := by
    ext slot
    cases slot <;> simp
  rw [enumeration]
  simp
  omega

omit [DecidableEq K] in
theorem stackCells_cfg (label : Option (Label Λ)) (regs : Registers R) (data : LocalData)
    (ctx : ∀ k, List (Γ k)) :
    stackCells (cfg label regs data ctx) = localCells data + contextCells ctx := by
  rw [stackCells, Fintype.sum_sum_type, localStack_sum]
  rfl

theorem decoderStackCells_eq_sum {P Q S : Type} {Δ : P → Type} [Fintype P]
    (c : OpenDecoderMachine.Cfg Δ Q S) :
    OpenDecoderMachine.stackCells c = ∑ k, (c.stk k).length := by
  have localSum (f : OpenDecoderMachine.LocalStack → Nat) :
      ∑ k, f k = f .input + f .reverse + f .output := by
    change (∑ k ∈ ({.input, .reverse, .output} : Finset OpenDecoderMachine.LocalStack), f k) = _
    simp
    omega
  rw [Fintype.sum_sum_type, localSum]
  rfl

theorem inputStackCells_eq_sum {P Q S : Type} {Δ : P → Type} [Fintype P]
    (c : InputParserMachine.Cfg Δ Q S) :
    InputParserMachine.stackCells c = ∑ k, (c.stk k).length := by
  have treeSum (f : TreeParserMachine.LocalStack InputParserMachine.TreeSide → Nat) :
      ∑ k, f k = f .raw + f .reverse + f .pending + f (.output .source) + f (.output .target) := by
    have enumeration : (Finset.univ : Finset (TreeParserMachine.LocalStack InputParserMachine.TreeSide)) =
        {.raw, .reverse, .pending, .output .source, .output .target} := by
      ext slot
      cases slot with
      | raw => simp
      | reverse => simp
      | pending => simp
      | output side => cases side <;> simp
    rw [enumeration]
    simp
    omega
  have extraSum (f : InputParserMachine.ExtraStack → Nat) : ∑ k, f k = f .fuel + f .bitsReverse := by
    change (∑ k ∈ ({.fuel, .bitsReverse} : Finset InputParserMachine.ExtraStack), f k) = _
    simp
  rw [Fintype.sum_sum_type, treeSum, Fintype.sum_sum_type, extraSum]
  unfold InputParserMachine.stackCells InputParserMachine.baseCells InputParserMachine.outputCells
    InputParserMachine.contextCells
  dsimp only [InputParserMachine.rawStack, InputParserMachine.reverseStack,
    InputParserMachine.pendingStack, InputParserMachine.outputStack, InputParserMachine.fuelStack,
    InputParserMachine.bitsReverseStack, InputParserMachine.protectedStack]
  omega

omit [DecidableEq K] in
theorem stackCells_framerCfg (c : FramerCfg Γ Λ R) :
    stackCells (framerCfg c) = OpenFramingMachine.stackCells c := by
  rw [OpenFramingMachine.stackCells_eq_sum]
  exact Transport.stackEquiv_total_length framerStackEquiv (framerSymbolEquiv (Γ := Γ)) c.stk

omit [DecidableEq K] in
theorem stackCells_inputCfg (c : InputCfg Γ Λ R) :
    stackCells (inputCfg c) = InputParserMachine.stackCells c := by
  rw [inputStackCells_eq_sum]
  exact Transport.stackEquiv_total_length inputStackEquiv (inputSymbolEquiv (Γ := Γ)) c.stk

omit [DecidableEq K] in
theorem stackCells_inputDecoderCfg (c : InputDecoderCfg Γ Λ R) :
    stackCells (inputDecoderCfg c) = OpenDecoderMachine.stackCells c := by
  rw [decoderStackCells_eq_sum]
  exact Transport.stackEquiv_total_length (decoderStackEquiv .input) (decoderSymbolEquiv (Γ := Γ) .input) c.stk

omit [DecidableEq K] in
theorem stackCells_certificateDecoderCfg (c : CertificateDecoderCfg Γ Λ R) :
    stackCells (certificateDecoderCfg c) = OpenDecoderMachine.stackCells c := by
  rw [decoderStackCells_eq_sum]
  exact Transport.stackEquiv_total_length (decoderStackEquiv .certificate) (decoderSymbolEquiv (Γ := Γ) .certificate) c.stk

/-- An inclusive bound on actual prefixes of one fixed program. -/
def PrefixBound (start : Cfg Γ Λ R) (ticks budget : Nat) : Prop :=
  ∀ n, n ≤ ticks → ∀ reached, (next caller)^[n] (some start) = some reached → stackCells reached ≤ budget

theorem PrefixBound.mono {start : Cfg Γ Λ R} {ticks before after : Nat}
    (bounded : PrefixBound caller start ticks before) (larger : before ≤ after) :
    PrefixBound caller start ticks after := by
  intro n small reached executed
  exact (bounded n small reached executed).trans larger

theorem PrefixBound.trans {start middle : Cfg Γ Λ R} {first second budget : Nat}
    (run : (next caller)^[first] (some start) = some middle)
    (before : PrefixBound caller start first budget)
    (after : PrefixBound caller middle second budget) :
    PrefixBound caller start (first + second) budget := by
  intro n bound reached executed
  by_cases early : n ≤ first
  · exact before n early reached executed
  · have later : n - first ≤ second := by omega
    apply after (n - first) later reached
    have count : n = (n - first) + first := by omega
    rw [count, Function.iterate_add_apply, run] at executed
    exact executed

theorem framer_prefix_bound (regs : Registers R) (raw : Bits) (ctx : ∀ k, List (Γ k)) :
    PrefixBound caller (entry regs raw ctx) (BitPairFraming.runSteps raw)
      (raw.length + contextCells ctx) := by
  intro n bound reached executed
  obtain ⟨actual, localRun, globalRun⟩ := framer_prefix_lift caller regs raw ctx n bound
  have same : framerCfg actual = reached := Option.some.inj (globalRun.symm.trans executed)
  subst reached
  have localBound := OpenFramingMachine.prefix_stackCells_le (fun _ => .halt) raw
    (framerRegisterEquiv.symm regs) (framerContext {} ctx) n actual bound localRun
  have contextEq : OpenFramingMachine.contextCells (framerContext (Γ := Γ) {} ctx) = contextCells ctx := by
    have initial := stackCells_framerCfg (Γ := Γ) (Λ := Λ)
      (OpenFramingMachine.cfg (some (OpenFramingMachine.phaseLabel .scanPrefix))
        (framerRegisterEquiv.symm regs) raw [] [] [] [] (framerContext {} ctx))
    rw [framer_start_transport, entry, stackCells_cfg,
      OpenFramingMachine.initial_stackCells] at initial
    simp only [localCells, List.length_nil, Nat.add_zero] at initial
    omega
  rw [stackCells_framerCfg]
  rw [contextEq] at localBound
  exact localBound

theorem inputDecoder_prefix_bound (regs : Registers R) (input cert : Bits) (ctx : ∀ k, List (Γ k)) :
    PrefixBound caller (inputDecoderEntry regs input cert ctx) (OpenDecoderMachine.runSteps input)
      (input.length + cert.length + contextCells ctx) := by
  intro n bound reached executed
  obtain ⟨actual, localRun, globalRun⟩ := inputDecoder_prefix_lift caller regs input cert ctx n bound
  have same : inputDecoderCfg actual = reached := Option.some.inj (globalRun.symm.trans executed)
  subst reached
  have preservation := OpenDecoderMachine.prefix_preserves (fun _ => .halt)
    (OpenDecoderMachine.cfg (some (OpenDecoderMachine.phaseLabel .scan))
      (decoderRegisterEquiv.symm (resetFramer regs)) input [] []
      (decoderContext .input (framedData input cert) ctx)) actual n (by
        simpa only [OpenDecoderMachine.remainingSteps, OpenDecoderMachine.cfg,
          OpenDecoderMachine.phaseLabel, OpenDecoderMachine.phaseSteps, List.length_nil, Nat.add_zero] using bound) localRun
  rw [← stackCells_inputDecoderCfg actual,
    ← stackCells_inputDecoderCfg, inputDecoder_start_transport, inputDecoderEntry, stackCells_cfg] at preservation
  simpa only [localCells, framedData, List.length_nil, Nat.add_zero, Nat.zero_add, Nat.add_assoc]
    using preservation.2.2

theorem input_prefix_bound (regs : Registers R) (input : Word) (cert : Bits) (ctx : ∀ k, List (Γ k)) :
    PrefixBound caller (inputEntry regs input cert ctx) (InputParserMachine.inputSteps input)
      (2 * input.length + cert.length + contextCells ctx + 1) := by
  intro n bound reached executed
  obtain ⟨actual, localRun, globalRun⟩ := input_prefix_lift caller regs input cert ctx n bound
  have same : inputCfg actual = reached := Option.some.inj (globalRun.symm.trans executed)
  subst reached
  have localBound := InputParserMachine.prefix_stackCells_le (fun _ => .halt) input
    (inputRegisterEquiv.symm (afterInputDecoder regs)) (inputContext (decodedInputData input cert) ctx)
    n bound actual localRun
  have contextEq : InputParserMachine.contextCells (inputContext (Γ := Γ) (decodedInputData input cert) ctx) =
      cert.length + contextCells ctx := by
    have initial := stackCells_inputCfg (Γ := Γ) (Λ := Λ)
      (InputParserMachine.entry (inputRegisterEquiv.symm (afterInputDecoder regs)) input
        (inputContext (decodedInputData input cert) ctx))
    rw [input_start_transport, inputEntry, stackCells_cfg] at initial
    have localInitial : InputParserMachine.stackCells
        (InputParserMachine.entry (Λ := ExtraLabel Λ) (inputRegisterEquiv.symm (afterInputDecoder regs)) input
          (inputContext (decodedInputData input cert) ctx)) = input.length +
        InputParserMachine.contextCells (inputContext (Γ := Γ) (decodedInputData input cert) ctx) := rfl
    rw [localInitial] at initial
    simp only [localCells, decodedInputData, List.length_nil, Nat.add_zero, Nat.zero_add] at initial
    change cert.length + input.length + contextCells ctx = input.length +
      InputParserMachine.contextCells
        (inputContext (decodedInputData input cert) ctx) at initial
    omega
  rw [stackCells_inputCfg]
  rw [contextEq] at localBound
  omega

theorem certificateDecoder_prefix_bound (regs : Registers R) (source target : BinaryTree Unit)
    (fuel cert : Bits) (ctx : ∀ k, List (Γ k)) :
    PrefixBound caller (certificateDecoderEntry regs source target fuel cert ctx)
      (OpenDecoderMachine.runSteps cert)
      (cert.length + (treeCode source).length + (treeCode target).length + fuel.length + contextCells ctx) := by
  intro n bound reached executed
  obtain ⟨actual, localRun, globalRun⟩ := certificateDecoder_prefix_lift caller regs source target fuel cert ctx n bound
  have same : certificateDecoderCfg actual = reached := Option.some.inj (globalRun.symm.trans executed)
  subst reached
  have preservation := OpenDecoderMachine.prefix_preserves (fun _ => .halt)
    (OpenDecoderMachine.cfg (some (OpenDecoderMachine.phaseLabel .scan))
      (decoderRegisterEquiv.symm (reset regs)) cert [] []
      (decoderContext .certificate (parsedData source target fuel cert) ctx)) actual n (by
        simpa only [OpenDecoderMachine.remainingSteps, OpenDecoderMachine.cfg,
          OpenDecoderMachine.phaseLabel, OpenDecoderMachine.phaseSteps, List.length_nil, Nat.add_zero] using bound) localRun
  rw [← stackCells_certificateDecoderCfg actual,
    ← stackCells_certificateDecoderCfg, certificateDecoder_start_transport,
    certificateDecoderEntry, stackCells_cfg] at preservation
  simpa only [localCells, parsedData, List.length_nil, Nat.add_zero, Nat.zero_add, Nat.add_assoc]
    using preservation.2.2

end Resources.RotationCertificate.FrontEndMachine

