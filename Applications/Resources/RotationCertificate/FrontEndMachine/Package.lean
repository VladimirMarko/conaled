import Applications.Resources.RotationCertificate.FrontEndMachine.Prefixes

/-!
# FrontEndMachine: Package
-/

set_option autoImplicit false
set_option warningAsError true

namespace Resources.RotationCertificate.FrontEndMachine
open Resources.BinaryCounter (Bits)

variable {K Λ R : Type} {Γ : K → Type}

theorem framerCfg_outside (c : FramerCfg Γ Λ R) (k : K) :
    (framerCfg c).stk (.inr k) = c.stk (.inr (.inr k)) := by
  change Transport.stackEquiv framerStackEquiv (framerSymbolEquiv (Γ := Γ)) c.stk
    (framerStackEquiv (.inr (.inr k))) = _
  rw [Transport.stackEquiv_apply]
  change List.map id _ = _
  simp

theorem inputCfg_outside (c : InputCfg Γ Λ R) (k : K) :
    (inputCfg c).stk (.inr k) = c.stk (InputParserMachine.protectedStack (.inr k)) := by
  change Transport.stackEquiv inputStackEquiv (inputSymbolEquiv (Γ := Γ)) c.stk
    (inputStackEquiv (InputParserMachine.protectedStack (.inr k))) = _
  rw [Transport.stackEquiv_apply]
  change List.map id _ = _
  simp

theorem inputDecoderCfg_outside (c : InputDecoderCfg Γ Λ R) (k : K) :
    (inputDecoderCfg c).stk (.inr k) = c.stk (.inr (.inr k)) := by
  change Transport.stackEquiv (decoderStackEquiv .input) (decoderSymbolEquiv (Γ := Γ) .input) c.stk
    (decoderStackEquiv .input (.inr (.inr k))) = _
  rw [Transport.stackEquiv_apply]
  change List.map id _ = _
  simp

theorem certificateDecoderCfg_outside (c : CertificateDecoderCfg Γ Λ R) (k : K) :
    (certificateDecoderCfg c).stk (.inr k) = c.stk (.inr (.inr k)) := by
  change Transport.stackEquiv (decoderStackEquiv .certificate) (decoderSymbolEquiv (Γ := Γ) .certificate) c.stk
    (decoderStackEquiv .certificate (.inr (.inr k))) = _
  rw [Transport.stackEquiv_apply]
  change List.map id _ = _
  simp

theorem inputDecoderCfg_certificate (c : InputDecoderCfg Γ Λ R) :
    (inputDecoderCfg c).stk (.inl .certificateBits) = c.stk (.inr (.inl .otherBits)) := by
  change Transport.stackEquiv (decoderStackEquiv .input) (decoderSymbolEquiv (Γ := Γ) .input) c.stk
    (decoderStackEquiv .input (.inr (.inl .otherBits))) = _
  rw [Transport.stackEquiv_apply]
  change List.map id _ = _
  simp

theorem inputCfg_certificate (c : InputCfg Γ Λ R) :
    (inputCfg c).stk (.inl .certificateBits) =
      c.stk (InputParserMachine.protectedStack (.inl .certificateBits)) := by
  change Transport.stackEquiv inputStackEquiv (inputSymbolEquiv (Γ := Γ)) c.stk
    (inputStackEquiv (InputParserMachine.protectedStack (.inl .certificateBits))) = _
  rw [Transport.stackEquiv_apply]
  change List.map id _ = _
  simp

theorem framerCfg_caller (c : FramerCfg Γ Λ R) : (framerCfg c).var.2.2 = c.var.2.2.2 := rfl
theorem inputCfg_caller (c : InputCfg Γ Λ R) : (inputCfg c).var.2.2 = c.var.2.2 := rfl
theorem inputDecoderCfg_caller (c : InputDecoderCfg Γ Λ R) : (inputDecoderCfg c).var.2.2 = c.var.2.2 := rfl
theorem certificateDecoderCfg_caller (c : CertificateDecoderCfg Γ Λ R) :
    (certificateDecoderCfg c).var.2.2 = c.var.2.2 := rfl

def Protected (regs : Registers R) (ctx : ∀ k, List (Γ k)) (c : Cfg Γ Λ R) : Prop :=
  c.var.2.2 = regs.2.2 ∧ ∀ k, c.stk (.inr k) = ctx k

variable [DecidableEq K]
variable (caller : External Λ → Statement Γ Λ R)

/-- Every observed state of an inclusive actual prefix satisfies the stated property. -/
def PrefixProperty (property : Cfg Γ Λ R → Prop) (start : Cfg Γ Λ R) (ticks : Nat) : Prop :=
  ∀ n, n ≤ ticks → ∀ reached, (next caller)^[n] (some start) = some reached → property reached

theorem PrefixProperty.trans {property : Cfg Γ Λ R → Prop} {start middle : Cfg Γ Λ R}
    {first second : Nat} (run : (next caller)^[first] (some start) = some middle)
    (before : PrefixProperty caller property start first)
    (after : PrefixProperty caller property middle second) :
    PrefixProperty caller property start (first + second) := by
  intro n bound reached executed
  by_cases early : n ≤ first
  · exact before n early reached executed
  · have later : n - first ≤ second := by omega
    apply after (n - first) later reached
    have count : n = (n - first) + first := by omega
    rw [count, Function.iterate_add_apply, run] at executed
    exact executed

theorem framer_prefix_protected (regs : Registers R) (raw : Bits) (ctx : ∀ k, List (Γ k)) :
    PrefixProperty caller (Protected regs ctx) (entry regs raw ctx) (BitPairFraming.runSteps raw) := by
  intro n bound reached executed
  obtain ⟨actual, localRun, globalRun⟩ := framer_prefix_lift caller regs raw ctx n bound
  have same : framerCfg actual = reached := Option.some.inj (globalRun.symm.trans executed)
  subst reached
  have phaseBound : n ≤ OpenFramingMachine.phaseSteps .scanPrefix raw [] [] := by
    change n ≤ OpenFramingMachine.scanSteps raw [] []
    unfold OpenFramingMachine.scanSteps
    split <;> simp only [List.length_nil, Nat.add_zero] <;> exact bound
  obtain ⟨registers, frame, _⟩ := OpenFramingMachine.prefix_preserves (fun _ => .halt) .scanPrefix
    raw [] [] [] [] (framerRegisterEquiv.symm regs) (framerContext {} ctx) n actual phaseBound localRun
  constructor
  · rw [framerCfg_caller]
    exact congrArg (fun r : FramerRegisterCaller R => r.2.2) registers
  · intro k
    rw [framerCfg_outside]
    exact frame (.inr k)

theorem inputDecoder_prefix_protected (regs : Registers R) (input cert : Bits) (ctx : ∀ k, List (Γ k)) :
    PrefixProperty caller (Protected regs ctx) (inputDecoderEntry regs input cert ctx)
      (OpenDecoderMachine.runSteps input) := by
  intro n bound reached executed
  obtain ⟨actual, localRun, globalRun⟩ := inputDecoder_prefix_lift caller regs input cert ctx n bound
  have same : inputDecoderCfg actual = reached := Option.some.inj (globalRun.symm.trans executed)
  subst reached
  obtain ⟨registers, frame⟩ := OpenDecoderMachine.prefix_frame (fun _ => .halt)
    (OpenDecoderMachine.cfg (some (OpenDecoderMachine.phaseLabel .scan))
      (decoderRegisterEquiv.symm (resetFramer regs)) input [] []
      (decoderContext .input (framedData input cert) ctx)) actual n (by
        simpa only [OpenDecoderMachine.remainingSteps, OpenDecoderMachine.cfg,
          OpenDecoderMachine.phaseLabel, OpenDecoderMachine.phaseSteps, List.length_nil, Nat.add_zero] using bound) localRun
  constructor
  · rw [inputDecoderCfg_caller]
    exact congrArg (fun r : DecoderRegisterCaller R => r.2) registers
  · intro k
    rw [inputDecoderCfg_outside]
    exact frame (.inr k)

theorem input_prefix_protected (regs : Registers R) (input : Word) (cert : Bits) (ctx : ∀ k, List (Γ k)) :
    PrefixProperty caller (Protected regs ctx) (inputEntry regs input cert ctx)
      (InputParserMachine.inputSteps input) := by
  intro n bound reached executed
  obtain ⟨actual, localRun, globalRun⟩ := input_prefix_lift caller regs input cert ctx n bound
  have same : inputCfg actual = reached := Option.some.inj (globalRun.symm.trans executed)
  subst reached
  obtain ⟨registers, frame, _, _⟩ := InputParserMachine.prefix_preserves (fun _ => .halt) input
    (inputRegisterEquiv.symm (afterInputDecoder regs)) (inputContext (decodedInputData input cert) ctx)
    n bound actual localRun
  constructor
  · rw [inputCfg_caller, registers]
    split <;> rfl
  · intro k
    rw [inputCfg_outside]
    exact frame (.inr k)

theorem certificateDecoder_prefix_protected (regs : Registers R) (source target : BinaryTree Unit)
    (fuel cert : Bits) (ctx : ∀ k, List (Γ k)) :
    PrefixProperty caller (Protected regs ctx) (certificateDecoderEntry regs source target fuel cert ctx)
      (OpenDecoderMachine.runSteps cert) := by
  intro n bound reached executed
  obtain ⟨actual, localRun, globalRun⟩ := certificateDecoder_prefix_lift caller regs source target fuel cert ctx n bound
  have same : certificateDecoderCfg actual = reached := Option.some.inj (globalRun.symm.trans executed)
  subst reached
  obtain ⟨registers, frame⟩ := OpenDecoderMachine.prefix_frame (fun _ => .halt)
    (OpenDecoderMachine.cfg (some (OpenDecoderMachine.phaseLabel .scan))
      (decoderRegisterEquiv.symm (reset regs)) cert [] []
      (decoderContext .certificate (parsedData source target fuel cert) ctx)) actual n (by
        simpa only [OpenDecoderMachine.remainingSteps, OpenDecoderMachine.cfg,
          OpenDecoderMachine.phaseLabel, OpenDecoderMachine.phaseSteps, List.length_nil, Nat.add_zero] using bound) localRun
  constructor
  · rw [certificateDecoderCfg_caller]
    exact congrArg (fun r : DecoderRegisterCaller R => r.2) registers
  · intro k
    rw [certificateDecoderCfg_outside]
    exact frame (.inr k)

/-- Input decoding protects every actual certificate bit, including a malformed ending. -/
theorem inputDecoder_prefix_certificate (regs : Registers R) (input cert : Bits)
    (ctx : ∀ k, List (Γ k)) (n : Nat) (bound : n ≤ OpenDecoderMachine.runSteps input)
    (reached : Cfg Γ Λ R)
    (executed : (next caller)^[n] (some (inputDecoderEntry regs input cert ctx)) = some reached) :
    reached.stk (.inl .certificateBits) = cert := by
  obtain ⟨actual, localRun, globalRun⟩ := inputDecoder_prefix_lift caller regs input cert ctx n bound
  have same : inputDecoderCfg actual = reached := Option.some.inj (globalRun.symm.trans executed)
  subst reached
  obtain ⟨_, frame⟩ := OpenDecoderMachine.prefix_frame (fun _ => .halt)
    (OpenDecoderMachine.cfg (some (OpenDecoderMachine.phaseLabel .scan))
      (decoderRegisterEquiv.symm (resetFramer regs)) input [] []
      (decoderContext .input (framedData input cert) ctx)) actual n (by
        simpa only [OpenDecoderMachine.remainingSteps, OpenDecoderMachine.cfg,
          OpenDecoderMachine.phaseLabel, OpenDecoderMachine.phaseSteps, List.length_nil, Nat.add_zero] using bound) localRun
  rw [inputDecoderCfg_certificate]
  exact frame (.inl .otherBits)

/-- The complete parser and its rollback also protect the entire certificate bit stack. -/
theorem input_prefix_certificate (regs : Registers R) (input : Word) (cert : Bits)
    (ctx : ∀ k, List (Γ k)) (n : Nat) (bound : n ≤ InputParserMachine.inputSteps input)
    (reached : Cfg Γ Λ R)
    (executed : (next caller)^[n] (some (inputEntry regs input cert ctx)) = some reached) :
    reached.stk (.inl .certificateBits) = cert := by
  obtain ⟨actual, localRun, globalRun⟩ := input_prefix_lift caller regs input cert ctx n bound
  have same : inputCfg actual = reached := Option.some.inj (globalRun.symm.trans executed)
  subst reached
  obtain ⟨_, frame, _, _⟩ := InputParserMachine.prefix_preserves (fun _ => .halt) input
    (inputRegisterEquiv.symm (afterInputDecoder regs)) (inputContext (decodedInputData input cert) ctx)
    n bound actual localRun
  rw [inputCfg_certificate]
  exact frame (.inl .certificateBits)

theorem prefix_protected (regs : Registers R) (raw : Bits) (ctx : ∀ k, List (Γ k)) :
    PrefixProperty caller (Protected regs ctx) (entry regs raw ctx) (runSteps raw) := by
  have framing := framer_prefix_protected caller regs raw ctx
  cases framed : BitPairFraming.unframe raw with
  | none => simpa only [runSteps, framed, Nat.add_zero] using framing
  | some pair =>
      rcases pair with ⟨input, cert⟩
      have frameRun := (framer_trace caller regs raw ctx).run
      rw [framed] at frameRun
      have decoding := inputDecoder_prefix_protected caller regs input cert ctx
      cases decoded : (unpackWordRun input).1 with
      | none =>
          simpa only [runSteps, framed, decoded, Nat.add_zero, framerResult] using
            PrefixProperty.trans caller frameRun framing decoding
      | some word =>
          have decodeRun := (inputDecoder_trace caller regs input cert ctx).run
          rw [decoded] at decodeRun
          have parsing := input_prefix_protected caller regs word cert ctx
          cases parsed : (parseInputRun word).1 with
          | none =>
              simpa only [runSteps, framed, decoded, parsed, Nat.add_zero, framerResult, inputDecoderResult]
                using PrefixProperty.trans caller frameRun framing
                  (PrefixProperty.trans caller decodeRun decoding parsing)
          | some triple =>
              rcases triple with ⟨source, target, fuel⟩
              have parseRun := (input_trace caller regs word cert ctx).run
              rw [parsed] at parseRun
              have certificate := certificateDecoder_prefix_protected caller regs source target fuel cert ctx
              simpa only [runSteps, framed, decoded, parsed, framerResult, inputDecoderResult, inputResult]
                using PrefixProperty.trans caller frameRun framing
                  (PrefixProperty.trans caller decodeRun decoding
                    (PrefixProperty.trans caller parseRun parsing certificate))

theorem prefix_context (regs : Registers R) (raw : Bits) (ctx : ∀ k, List (Γ k))
    (n : Nat) (bound : n ≤ runSteps raw) (reached : Cfg Γ Λ R)
    (executed : (next caller)^[n] (some (entry regs raw ctx)) = some reached) :
    reached.var.2.2 = regs.2.2 ∧ ∀ k, reached.stk (.inr k) = ctx k :=
  prefix_protected caller regs raw ctx n bound reached executed

end Resources.RotationCertificate.FrontEndMachine

namespace Resources.RotationCertificate.FrontEndMachine
open Resources.BinaryCounter (Bits)

variable {K Λ R : Type} {Γ : K → Type}

theorem program_caller_independent
    (caller other : External Λ → Statement Γ Λ R) (label : Label Λ)
    (owned : Owned (some label)) : program caller label = program other label := by
  unfold program
  change OwnedPartition (inputPartitionEquiv.symm label) at owned
  generalize selected : inputPartitionEquiv.symm label = part at *
  cases part with
  | inl ownedLabel => rfl
  | inr rest => cases rest with
    | inl result => cases result with
      | success => rfl
      | failure => cases owned
    | inr rest => cases rest with
      | inl framePhase => rfl
      | inr rest => cases rest with
        | inl decoderPhase => rfl
        | inr rest => cases rest with
          | inl certTail => rfl
          | inr rest => cases rest with
            | inl dispatch => cases owned
            | inr outside => cases owned

variable [DecidableEq K]
variable (caller : External Λ → Statement Γ Λ R)

theorem step_caller_independent (other : External Λ → Statement Γ Λ R)
    (c : Cfg Γ Λ R) (owned : Owned c.l) : step caller c = step other c := by
  rcases c with ⟨label, regs, data⟩
  cases label with
  | none => rfl
  | some label =>
      change some (Turing.TM2.stepAux (program caller label) regs data) =
        some (Turing.TM2.stepAux (program other label) regs data)
      rw [program_caller_independent caller other label owned]

theorem run_prefix_caller_independent (other : External Λ → Statement Γ Λ R)
    (regs : Registers R) (raw : Bits) (ctx : ∀ k, List (Γ k)) (n : Nat)
    (bound : n ≤ runSteps raw) :
    (next caller)^[n] (some (entry regs raw ctx)) =
      (next other)^[n] (some (entry regs raw ctx)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have previous := ih (by omega)
      obtain ⟨reached, executed, owned⟩ := (run_source_trace caller regs raw ctx).owned_prefix n (by omega)
      have otherRun := previous.symm.trans executed
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', executed, otherRun]
      exact step_caller_independent caller other reached owned

theorem first_return_exact (regs : Registers R) (raw : Bits) (ctx : ∀ k, List (Γ k))
    (n : Nat) (bound : n ≤ runSteps raw) (reached : Cfg Γ Λ R)
    (executed : (next caller)^[n] (some (entry regs raw ctx)) = some reached)
    (outside : ¬ Owned reached.l) : n = runSteps raw := by
  obtain ⟨actual, run, owned⟩ := run_prefix caller regs raw ctx n bound
  have equal : actual = reached := Option.some.inj (run.symm.trans executed)
  subst actual
  have notStrict : ¬ n < runSteps raw := fun strict => outside (owned.mp strict)
  omega

omit [DecidableEq K] in
theorem treeCode_injective : Function.Injective treeCode := by
  intro left right encoded
  have observed := congrArg (fun raw => (parseTreeRun raw).1) encoded
  have leftRun : (parseTreeRun (treeCode left)).1 = some (left, []) := by
    simpa only [List.append_nil] using congrArg Prod.fst (parseTreeRun_code left [])
  have rightRun : (parseTreeRun (treeCode right)).1 = some (right, []) := by
    simpa only [List.append_nil] using congrArg Prod.fst (parseTreeRun_code right [])
  rw [leftRun, rightRun] at observed
  exact (Prod.mk.inj (Option.some.inj observed)).1

omit [DecidableEq K] in
theorem resultCfg_success_iff (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (outcome : Outcome) (source target : BinaryTree Unit) (fuel : Bits) (cert : Word) :
    resultCfg (Λ := Λ) regs ctx outcome = resultCfg regs ctx (.success source target fuel cert) ↔
      outcome = .success source target fuel cert := by
  constructor
  · intro equal
    cases outcome with
    | frameFailure =>
        have labels := congrArg (fun c : Cfg Γ Λ R => c.l) equal
        cases labels
    | inputDecodeFailure certBits =>
        have labels := congrArg (fun c : Cfg Γ Λ R => c.l) equal
        cases labels
    | inputParseFailure input certBits =>
        have labels := congrArg (fun c : Cfg Γ Λ R => c.l) equal
        cases labels
    | certificateDecodeFailure actualSource actualTarget actualFuel =>
        have labels := congrArg (fun c : Cfg Γ Λ R => c.l) equal
        cases labels
    | success actualSource actualTarget actualFuel actualCert =>
        have sourceEq : treeCode actualSource = treeCode source :=
          congrArg (fun c : Cfg Γ Λ R => c.stk (.inl .sourceTree)) equal
        have targetEq : treeCode actualTarget = treeCode target :=
          congrArg (fun c : Cfg Γ Λ R => c.stk (.inl .targetTree)) equal
        have fuelEq : actualFuel = fuel := congrArg (fun c : Cfg Γ Λ R => c.stk (.inl .fuel)) equal
        have certEq : actualCert = cert := congrArg (fun c : Cfg Γ Λ R => c.stk (.inl .certificateWord)) equal
        cases treeCode_injective sourceEq
        cases treeCode_injective targetEq
        cases fuelEq
        cases certEq
        rfl
  · rintro rfl
    rfl

/-- Full raw recognition at the actual finite program's first-return clock. -/
theorem run_code_iff (regs : Registers R) (raw : Bits) (ctx : ∀ k, List (Γ k))
    (source target : BinaryTree Unit) (fuel : Bits) (cert : Word) :
    (next caller)^[runSteps raw] (some (entry regs raw ctx)) =
        some (resultCfg regs ctx (.success source target fuel cert)) ↔
      raw = BitPairFraming.frame (wordBits (inputCode source target fuel)) (wordBits cert) := by
  rw [run_source, Option.some.injEq, resultCfg_success_iff, sourceOutcome_success_iff]

end Resources.RotationCertificate.FrontEndMachine

namespace Resources.RotationCertificate.FrontEndMachine
open Resources.BinaryCounter (Bits)

variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
variable (caller : External Λ → Statement Γ Λ R)

/-- Every actual prefix through the first front-end handoff fits the original raw storage. -/
theorem prefix_bound (regs : Registers R) (raw : Bits) (ctx : ∀ k, List (Γ k)) :
    PrefixBound caller (entry regs raw ctx) (runSteps raw) (raw.length + contextCells ctx) := by
  have framing := framer_prefix_bound caller regs raw ctx
  cases framed : BitPairFraming.unframe raw with
  | none => simpa only [runSteps, framed, Nat.add_zero] using framing
  | some pair =>
      rcases pair with ⟨input, cert⟩
      have rawSize : raw.length = 2 * input.length + cert.length + 1 := by
        rw [(BitPairFraming.unframe_iff raw input cert).mp framed, BitPairFraming.frame_length]
      have frameRun := (framer_trace caller regs raw ctx).run
      rw [framed] at frameRun
      have decoding := PrefixBound.mono caller (inputDecoder_prefix_bound caller regs input cert ctx)
        (show input.length + cert.length + contextCells ctx ≤ raw.length + contextCells ctx by omega)
      cases decoded : (unpackWordRun input).1 with
      | none =>
          simpa only [runSteps, framed, decoded, Nat.add_zero, framerResult] using
            PrefixBound.trans caller frameRun framing decoding
      | some word =>
          have inputSize : input.length = 4 * word.length := by
            rw [(unpackWordRun_iff input word).mp decoded, wordBits_length]
          have decodeRun := (inputDecoder_trace caller regs input cert ctx).run
          rw [decoded] at decodeRun
          have parsing := PrefixBound.mono caller (input_prefix_bound caller regs word cert ctx)
            (show 2 * word.length + cert.length + contextCells ctx + 1 ≤
              raw.length + contextCells ctx by omega)
          cases parsed : (parseInputRun word).1 with
          | none =>
              simpa only [runSteps, framed, decoded, parsed, Nat.add_zero, framerResult, inputDecoderResult]
                using PrefixBound.trans caller frameRun framing
                  (PrefixBound.trans caller decodeRun decoding parsing)
          | some triple =>
              rcases triple with ⟨source, target, fuel⟩
              have fieldsSize : (treeCode source).length + (treeCode target).length + fuel.length + 3 =
                  word.length := by
                rw [(parseInputRun_iff word source target fuel).mp parsed,
                  inputCode_length, treeCode_length, treeCode_length]
                omega
              have parseRun := (input_trace caller regs word cert ctx).run
              rw [parsed] at parseRun
              have certificate := PrefixBound.mono caller
                (certificateDecoder_prefix_bound caller regs source target fuel cert ctx)
                (show cert.length + (treeCode source).length + (treeCode target).length +
                  fuel.length + contextCells ctx ≤ raw.length + contextCells ctx by omega)
              simpa only [runSteps, framed, decoded, parsed, framerResult, inputDecoderResult, inputResult]
                using PrefixBound.trans caller frameRun framing
                  (PrefixBound.trans caller decodeRun decoding
                    (PrefixBound.trans caller parseRun parsing certificate))

theorem prefix_stackCells_le (regs : Registers R) (raw : Bits) (ctx : ∀ k, List (Γ k))
    (n : Nat) (bound : n ≤ runSteps raw) (reached : Cfg Γ Λ R)
    (executed : (next caller)^[n] (some (entry regs raw ctx)) = some reached) :
    stackCells reached ≤ raw.length + contextCells ctx :=
  prefix_bound caller regs raw ctx n bound reached executed

omit [DecidableEq K] in
theorem initial_stackCells (regs : Registers R) (raw : Bits) (ctx : ∀ k, List (Γ k)) :
    stackCells (entry (Λ := Λ) regs raw ctx) = raw.length + contextCells ctx := by
  rw [entry, stackCells_cfg]
  simp only [localCells, List.length_nil, Nat.add_zero]

theorem zero_prefix_space_sharp (regs : Registers R) (raw : Bits) (ctx : ∀ k, List (Γ k)) :
    (next caller)^[0] (some (entry regs raw ctx)) = some (entry regs raw ctx) ∧
      stackCells (entry (Λ := Λ) regs raw ctx) = raw.length + contextCells ctx :=
  ⟨rfl, initial_stackCells regs raw ctx⟩

omit [DecidableEq K] in
theorem success_stackCells (regs : Registers R) (source target : BinaryTree Unit)
    (fuel : Bits) (cert : Word) (ctx : ∀ k, List (Γ k)) :
    stackCells (resultCfg (Λ := Λ) regs ctx (.success source target fuel cert)) =
      (inputCode source target fuel).length - 3 + cert.length + contextCells ctx := by
  rw [resultCfg, stackCells_cfg]
  simp only [localCells, successData, List.length_nil, Nat.add_zero, Nat.zero_add,
    inputCode_length, treeCode_length]
  omega

omit [Fintype K] in
theorem run_code (regs : Registers R) (source target : BinaryTree Unit) (fuel : Bits)
    (cert : Word) (ctx : ∀ k, List (Γ k)) :
    (next caller)^[12 * (inputCode source target fuel).length + 10 * cert.length + 11]
        (some (entry regs (BitPairFraming.frame
          (wordBits (inputCode source target fuel)) (wordBits cert)) ctx)) =
      some (resultCfg regs ctx (.success source target fuel cert)) := by
  have run := run_source caller regs (BitPairFraming.frame
    (wordBits (inputCode source target fuel)) (wordBits cert)) ctx
  rw [runSteps_code, (sourceOutcome_success_iff _ source target fuel cert).mpr rfl] at run
  exact run

variable [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]

/-- One finite installed program before raw data is supplied, with two genuinely live exits. -/
def machine (initial : R) : Turing.FinTM2 where
  K := StackId K
  k₀ := .inl .framedRaw
  k₁ := .inl .certificateWord
  Γ := alphabet Γ
  Λ := Label Λ
  main := framerLabel .scanPrefix
  σ := Registers R
  initialState := ((none, none), BitDecoderMachine.zeroRegisters, initial)
  Γk₀Fin := alphabetFintype (.inl .framedRaw)
  m := program caller

theorem machine_step_eq (initial : R) (c : Cfg Γ Λ R) :
    (machine caller initial).step c = step caller c := rfl

theorem initList_eq (initial : R) (raw : Bits) :
    Turing.initList (machine caller initial) raw =
      entry ((none, none), BitDecoderMachine.zeroRegisters, initial) raw (fun _ => []) := by
  apply cfg_ext
  · rfl
  · rfl
  · funext slot
    cases slot with
    | inl slot => cases slot <;> rfl
    | inr k => rfl

theorem machine_run_source (initial : R) (raw : Bits) :
    (fun c => c.bind (machine caller initial).step)^[runSteps raw]
        (some (Turing.initList (machine caller initial) raw)) =
      some (resultCfg ((none, none), BitDecoderMachine.zeroRegisters, initial)
        (fun _ => []) (sourceOutcome raw)) := by
  change (next caller)^[runSteps raw] (some (Turing.initList (machine caller initial) raw)) = _
  rw [initList_eq]
  exact run_source caller ((none, none), BitDecoderMachine.zeroRegisters, initial) raw (fun _ => [])

/-- Timed live handoff; no marker projection or `haltList` convention is assumed. -/
def machineInTime (initial : R) (raw : Bits) :
    StateTransition.EvalsToInTime (machine caller initial).step
      (Turing.initList (machine caller initial) raw)
      (some (resultCfg ((none, none), BitDecoderMachine.zeroRegisters, initial)
        (fun _ => []) (sourceOutcome raw))) (8 * raw.length + 13) where
  steps := runSteps raw
  evals_in_steps := machine_run_source caller initial raw
  steps_le_m := runSteps_le raw

theorem machine_prefix_stackCells_le (initial : R) (raw : Bits) (n : Nat)
    (bound : n ≤ runSteps raw) (reached : Cfg Γ Λ R)
    (executed : (fun c => c.bind (machine caller initial).step)^[n]
      (some (Turing.initList (machine caller initial) raw)) = some reached) :
    stackCells reached ≤ raw.length := by
  change (next caller)^[n] (some (Turing.initList (machine caller initial) raw)) = some reached at executed
  rw [initList_eq] at executed
  have cells := prefix_stackCells_le caller ((none, none), BitDecoderMachine.zeroRegisters, initial)
    raw (fun _ => []) n bound reached executed
  simpa only [contextCells, List.length_nil, Finset.sum_const_zero, Nat.add_zero] using cells

end Resources.RotationCertificate.FrontEndMachine
