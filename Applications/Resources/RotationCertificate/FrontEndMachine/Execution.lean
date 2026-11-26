import Applications.Resources.RotationCertificate.FrontEndMachine.Basic

/-!
# FrontEndMachine: Execution
-/

set_option autoImplicit false
set_option warningAsError true

namespace Resources.RotationCertificate.FrontEndMachine
open Resources.BinaryCounter (Bits)

variable {K Λ R : Type} {Γ : K → Type}

abbrev External (Λ : Type) := TreeParserMachine.Result ⊕ Λ
abbrev InputStatement (Γ : K → Type) (Λ R : Type) :=
  InputParserMachine.Statement (InputProtectedAlphabet Γ) (ExtraLabel Λ) (InputRegisterCaller R)
abbrev FramerStatement (Γ : K → Type) (Λ R : Type) :=
  OpenFramingMachine.Statement (FramerProtectedAlphabet Γ) (FramerCaller Λ) (FramerRegisterCaller R)
abbrev InputDecoderStatement (Γ : K → Type) (Λ R : Type) :=
  OpenDecoderMachine.Statement (DecoderProtectedAlphabet Γ) (InputDecoderCaller Λ) (DecoderRegisterCaller R)
abbrev CertificateDecoderStatement (Γ : K → Type) (Λ R : Type) :=
  OpenDecoderMachine.Statement (DecoderProtectedAlphabet Γ) (CertificateDecoderCaller Λ) (DecoderRegisterCaller R)

abbrev InputCfg (Γ : K → Type) (Λ R : Type) :=
  InputParserMachine.Cfg (InputProtectedAlphabet Γ) (ExtraLabel Λ) (InputRegisterCaller R)
abbrev FramerCfg (Γ : K → Type) (Λ R : Type) :=
  OpenFramingMachine.Cfg (FramerProtectedAlphabet Γ) (FramerCaller Λ) (FramerRegisterCaller R)
abbrev InputDecoderCfg (Γ : K → Type) (Λ R : Type) :=
  OpenDecoderMachine.Cfg (DecoderProtectedAlphabet Γ) (InputDecoderCaller Λ) (DecoderRegisterCaller R)
abbrev CertificateDecoderCfg (Γ : K → Type) (Λ R : Type) :=
  OpenDecoderMachine.Cfg (DecoderProtectedAlphabet Γ) (CertificateDecoderCaller Λ) (DecoderRegisterCaller R)

def inputTranslate (body : InputStatement Γ Λ R) : Statement Γ Λ R :=
  Transport.statement inputStackEquiv (inputSymbolEquiv (Γ := Γ)) inputRegisterEquiv inputLabelEquiv body
def framerTranslate (body : FramerStatement Γ Λ R) : Statement Γ Λ R :=
  Transport.statement framerStackEquiv (framerSymbolEquiv (Γ := Γ)) framerRegisterEquiv framerLabelEquiv body
def inputDecoderTranslate (body : InputDecoderStatement Γ Λ R) : Statement Γ Λ R :=
  Transport.statement (decoderStackEquiv .input) (decoderSymbolEquiv (Γ := Γ) .input)
    decoderRegisterEquiv inputDecoderLabelEquiv body
def certificateDecoderTranslate (body : CertificateDecoderStatement Γ Λ R) : Statement Γ Λ R :=
  Transport.statement (decoderStackEquiv .certificate) (decoderSymbolEquiv (Γ := Γ) .certificate)
    decoderRegisterEquiv certificateDecoderLabelEquiv body

def inputCfg (c : InputCfg Γ Λ R) : Cfg Γ Λ R :=
  Transport.cfg inputStackEquiv (inputSymbolEquiv (Γ := Γ)) inputRegisterEquiv inputLabelEquiv c
def framerCfg (c : FramerCfg Γ Λ R) : Cfg Γ Λ R :=
  Transport.cfg framerStackEquiv (framerSymbolEquiv (Γ := Γ)) framerRegisterEquiv framerLabelEquiv c
def inputDecoderCfg (c : InputDecoderCfg Γ Λ R) : Cfg Γ Λ R :=
  Transport.cfg (decoderStackEquiv .input) (decoderSymbolEquiv (Γ := Γ) .input)
    decoderRegisterEquiv inputDecoderLabelEquiv c
def certificateDecoderCfg (c : CertificateDecoderCfg Γ Λ R) : Cfg Γ Λ R :=
  Transport.cfg (decoderStackEquiv .certificate) (decoderSymbolEquiv (Γ := Γ) .certificate)
    decoderRegisterEquiv certificateDecoderLabelEquiv c

/-- A presentation of Input's interior only; no global result installs these placeholders. -/
def inputInterior (label : Label Λ) : Statement Γ Λ R :=
  inputTranslate (InputParserMachine.program (fun _ => .halt) label)

/-- Every globally owned label executes one translated actual finite component body. -/
def program (caller : External Λ → Statement Γ Λ R) (label : Label Λ) : Statement Γ Λ R :=
  match inputPartitionEquiv.symm label with
  | .inl owned => inputInterior (inputOwnedLabel owned)
  | .inr (.inl .success) => certificateDecoderTranslate (OpenDecoderMachine.block .scan)
  | .inr (.inl .failure) => caller (.inl .failure)
  | .inr (.inr (.inl phase)) => framerTranslate (OpenFramingMachine.block phase)
  | .inr (.inr (.inr (.inl phase))) => inputDecoderTranslate (OpenDecoderMachine.block phase)
  | .inr (.inr (.inr (.inr (.inl tail)))) =>
      certificateDecoderTranslate (OpenDecoderMachine.block (tailPhase tail))
  | .inr (.inr (.inr (.inr (.inr (.inl _))))) => caller (.inl .success)
  | .inr (.inr (.inr (.inr (.inr (.inr external))))) => caller (.inr external)

variable (caller : External Λ → Statement Γ Λ R)

theorem program_inputOwned (owned : InputOwned) :
    program caller (inputOwnedLabel owned) = inputInterior (inputOwnedLabel owned) := by
  change program caller (inputPartitionEquiv (.inl owned)) = _
  simp only [program, Equiv.symm_apply_apply]

@[simp] theorem program_framer (phase : OpenFramingMachine.Phase) :
    program caller (framerLabel phase) = framerTranslate (OpenFramingMachine.block phase) := rfl
@[simp] theorem program_input_decoder (phase : OpenDecoderMachine.Phase) :
    program caller (inputDecoderLabel phase) = inputDecoderTranslate (OpenDecoderMachine.block phase) := rfl
@[simp] theorem program_certificate_decoder (phase : OpenDecoderMachine.Phase) :
    program caller (certificateDecoderLabel phase) =
      certificateDecoderTranslate (OpenDecoderMachine.block phase) := by cases phase <;> rfl
@[simp] theorem program_dispatch : program caller dispatchLabel = caller (.inl .success) := rfl
@[simp] theorem program_reject : program caller rejectLabel = caller (.inl .failure) := rfl
@[simp] theorem program_caller (label : Λ) : program caller (callerLabel label) = caller (.inr label) := rfl

theorem input_body_caller_independent
    (first second : InputParserMachine.External (ExtraLabel Λ) → InputStatement Γ Λ R)
    (label : Label Λ) (owned : InputParserMachine.FullOwned (some label)) :
    InputParserMachine.program first label = InputParserMachine.program second label := by
  cases label with
  | inl pair => rcases pair with ⟨side, phase⟩; rfl
  | inr external => cases external with
    | inl pair =>
        rcases pair with ⟨side, result⟩
        cases side with
        | source => cases result with
          | success => rfl
          | failure => cases owned
        | target => cases result <;> rfl
    | inr extra => cases extra with
      | inl phase => rfl
      | inr exit => cases owned

theorem installed_input_owned
    (localCaller : InputParserMachine.External (ExtraLabel Λ) → InputStatement Γ Λ R)
    (label : InputParserMachine.Label (ExtraLabel Λ))
    (owned : InputParserMachine.FullOwned (some label)) :
    program caller (inputLabelEquiv label) = inputTranslate (InputParserMachine.program localCaller label) := by
  change program caller label = _
  obtain ⟨owner, rfl⟩ := (inputOwnedLabel_image label).mpr owned
  rw [program_inputOwned]
  exact congrArg inputTranslate
    (input_body_caller_independent (fun _ => .halt) localCaller _ owned)

theorem installed_framer_owned
    (localCaller : OpenFramingMachine.External (FramerCaller Λ) → FramerStatement Γ Λ R)
    (label : OpenFramingMachine.Label (FramerCaller Λ)) (owned : OpenFramingMachine.Owned (some label)) :
    program caller (framerLabelEquiv label) = framerTranslate (OpenFramingMachine.program localCaller label) := by
  cases label with
  | inl phase => rfl
  | inr external => cases owned

theorem installed_input_decoder_owned
    (localCaller : OpenDecoderMachine.External (InputDecoderCaller Λ) → InputDecoderStatement Γ Λ R)
    (label : OpenDecoderMachine.Label (InputDecoderCaller Λ)) (owned : OpenDecoderMachine.Owned (some label)) :
    program caller (inputDecoderLabelEquiv label) = inputDecoderTranslate (OpenDecoderMachine.program localCaller label) := by
  cases label with
  | inl phase => rfl
  | inr external => cases owned

theorem installed_certificate_decoder_owned
    (localCaller : OpenDecoderMachine.External (CertificateDecoderCaller Λ) → CertificateDecoderStatement Γ Λ R)
    (label : OpenDecoderMachine.Label (CertificateDecoderCaller Λ)) (owned : OpenDecoderMachine.Owned (some label)) :
    program caller (certificateDecoderLabelEquiv label) =
      certificateDecoderTranslate (OpenDecoderMachine.program localCaller label) := by
  cases label with
  | inl phase => cases phase <;> rfl
  | inr external => cases owned

variable [DecidableEq K]

abbrev step : Cfg Γ Λ R → Option (Cfg Γ Λ R) := Turing.TM2.step (program caller)
def next : Option (Cfg Γ Λ R) → Option (Cfg Γ Λ R) := fun c => c.bind (step caller)

theorem framer_prefix_installed
    (localCaller : OpenFramingMachine.External (FramerCaller Λ) → FramerStatement Γ Λ R)
    (n : Nat) (start : FramerCfg Γ Λ R)
    (within : ∀ j, j < n → ∃ reached,
      (OpenFramingMachine.next localCaller)^[j] (some start) = some reached ∧
        OpenFramingMachine.Owned reached.l) :
    (next caller)^[n] (some (framerCfg start)) =
      ((OpenFramingMachine.next localCaller)^[n] (some start)).map framerCfg := by
  exact Transport.iterate_owned framerStackEquiv (framerSymbolEquiv (Γ := Γ))
    framerRegisterEquiv framerLabelEquiv (OpenFramingMachine.program localCaller)
    (program caller) OpenFramingMachine.Owned (installed_framer_owned caller localCaller) n start within

theorem input_prefix_installed
    (localCaller : InputParserMachine.External (ExtraLabel Λ) → InputStatement Γ Λ R)
    (n : Nat) (start : InputCfg Γ Λ R)
    (within : ∀ j, j < n → ∃ reached,
      (InputParserMachine.next localCaller)^[j] (some start) = some reached ∧
        InputParserMachine.FullOwned reached.l) :
    (next caller)^[n] (some (inputCfg start)) =
      ((InputParserMachine.next localCaller)^[n] (some start)).map inputCfg := by
  exact Transport.iterate_owned inputStackEquiv (inputSymbolEquiv (Γ := Γ))
    inputRegisterEquiv inputLabelEquiv (InputParserMachine.program localCaller)
    (program caller) InputParserMachine.FullOwned (installed_input_owned caller localCaller) n start within

theorem input_decoder_prefix_installed
    (localCaller : OpenDecoderMachine.External (InputDecoderCaller Λ) → InputDecoderStatement Γ Λ R)
    (n : Nat) (start : InputDecoderCfg Γ Λ R)
    (within : ∀ j, j < n → ∃ reached,
      (OpenDecoderMachine.next localCaller)^[j] (some start) = some reached ∧
        OpenDecoderMachine.Owned reached.l) :
    (next caller)^[n] (some (inputDecoderCfg start)) =
      ((OpenDecoderMachine.next localCaller)^[n] (some start)).map inputDecoderCfg := by
  exact Transport.iterate_owned (decoderStackEquiv .input) (decoderSymbolEquiv (Γ := Γ) .input)
    decoderRegisterEquiv inputDecoderLabelEquiv (OpenDecoderMachine.program localCaller)
    (program caller) OpenDecoderMachine.Owned (installed_input_decoder_owned caller localCaller) n start within

theorem certificate_decoder_prefix_installed
    (localCaller : OpenDecoderMachine.External (CertificateDecoderCaller Λ) → CertificateDecoderStatement Γ Λ R)
    (n : Nat) (start : CertificateDecoderCfg Γ Λ R)
    (within : ∀ j, j < n → ∃ reached,
      (OpenDecoderMachine.next localCaller)^[j] (some start) = some reached ∧
        OpenDecoderMachine.Owned reached.l) :
    (next caller)^[n] (some (certificateDecoderCfg start)) =
      ((OpenDecoderMachine.next localCaller)^[n] (some start)).map certificateDecoderCfg := by
  exact Transport.iterate_owned (decoderStackEquiv .certificate) (decoderSymbolEquiv (Γ := Γ) .certificate)
    decoderRegisterEquiv certificateDecoderLabelEquiv (OpenDecoderMachine.program localCaller)
    (program caller) OpenDecoderMachine.Owned (installed_certificate_decoder_owned caller localCaller) n start within

/-- The actual complete framer execution under the one installed global program. -/
theorem framer_run_installed
    (localCaller : OpenFramingMachine.External (FramerCaller Λ) → FramerStatement Γ Λ R)
    (raw : Bits) (regs : OpenFramingMachine.Registers (FramerRegisterCaller R))
    (ctx : ∀ k, List (FramerProtectedAlphabet Γ k)) :
    (next caller)^[BitPairFraming.runSteps raw]
        (some (framerCfg (OpenFramingMachine.cfg
          (some (OpenFramingMachine.phaseLabel .scanPrefix)) regs raw [] [] [] [] ctx))) =
      some (framerCfg (OpenFramingMachine.scanResult regs [] [] [] [] ctx (BitPairFraming.unframe raw))) := by
  have run := framer_prefix_installed caller localCaller (BitPairFraming.runSteps raw)
    (OpenFramingMachine.cfg (some (OpenFramingMachine.phaseLabel .scanPrefix)) regs raw [] [] [] [] ctx)
    (OpenFramingMachine.run_first_return localCaller raw regs ctx).2
  rw [OpenFramingMachine.run_source] at run
  exact run

/-- Input rollback and success retain their actual complete component configurations. -/
theorem input_run_installed
    (localCaller : InputParserMachine.External (ExtraLabel Λ) → InputStatement Γ Λ R)
    (raw : Word) (regs : InputParserMachine.Registers (InputRegisterCaller R))
    (ctx : ∀ k, List (InputProtectedAlphabet Γ k)) :
    (next caller)^[InputParserMachine.inputSteps raw]
        (some (inputCfg (InputParserMachine.entry regs raw ctx))) =
      some (inputCfg (InputParserMachine.resultCfg regs raw ctx (parseInputRun raw).1)) := by
  have within : ∀ j, j < InputParserMachine.inputSteps raw → ∃ reached,
      (InputParserMachine.next localCaller)^[j] (some (InputParserMachine.entry regs raw ctx)) = some reached ∧
        InputParserMachine.FullOwned reached.l := by
    intro j strict
    obtain ⟨reached, executed, _, _, owned⟩ :=
      InputParserMachine.run_prefix localCaller raw regs ctx j (Nat.le_of_lt strict)
    exact ⟨reached, executed, owned.mp strict⟩
  have run := input_prefix_installed caller localCaller (InputParserMachine.inputSteps raw)
    (InputParserMachine.entry regs raw ctx) within
  rw [InputParserMachine.run_source] at run
  exact run

/-- Generalized dirty-output decoding is transported without erasing any physical data. -/
theorem input_decoder_scan_installed
    (localCaller : OpenDecoderMachine.External (InputDecoderCaller Λ) → InputDecoderStatement Γ Λ R)
    (raw : Bits) (rev out : Word) (regs : OpenDecoderMachine.Registers (DecoderRegisterCaller R))
    (ctx : ∀ k, List (DecoderProtectedAlphabet Γ k)) :
    (next caller)^[OpenDecoderMachine.runSteps raw + rev.length]
        (some (inputDecoderCfg (OpenDecoderMachine.cfg
          (some (OpenDecoderMachine.phaseLabel .scan)) regs raw rev out ctx))) =
      some (inputDecoderCfg (OpenDecoderMachine.resultCfg (unpackWordRun raw).1 rev out regs ctx)) := by
  have within : ∀ j, j < OpenDecoderMachine.runSteps raw + rev.length → ∃ reached,
      (OpenDecoderMachine.next localCaller)^[j]
        (some (OpenDecoderMachine.cfg (some (OpenDecoderMachine.phaseLabel .scan)) regs raw rev out ctx)) =
          some reached ∧ OpenDecoderMachine.Owned reached.l := by
    intro j strict
    obtain ⟨reached, executed, _, _, owned, _⟩ :=
      OpenDecoderMachine.phase_prefix localCaller .scan raw rev out regs ctx j (Nat.le_of_lt strict)
    exact ⟨reached, executed, owned.mp strict⟩
  have run := input_decoder_prefix_installed caller localCaller (OpenDecoderMachine.runSteps raw + rev.length)
    (OpenDecoderMachine.cfg (some (OpenDecoderMachine.phaseLabel .scan)) regs raw rev out ctx) within
  rw [OpenDecoderMachine.scan_iterate] at run
  exact run

theorem certificate_decoder_scan_installed
    (localCaller : OpenDecoderMachine.External (CertificateDecoderCaller Λ) → CertificateDecoderStatement Γ Λ R)
    (raw : Bits) (rev out : Word) (regs : OpenDecoderMachine.Registers (DecoderRegisterCaller R))
    (ctx : ∀ k, List (DecoderProtectedAlphabet Γ k)) :
    (next caller)^[OpenDecoderMachine.runSteps raw + rev.length]
        (some (certificateDecoderCfg (OpenDecoderMachine.cfg
          (some (OpenDecoderMachine.phaseLabel .scan)) regs raw rev out ctx))) =
      some (certificateDecoderCfg (OpenDecoderMachine.resultCfg (unpackWordRun raw).1 rev out regs ctx)) := by
  have within : ∀ j, j < OpenDecoderMachine.runSteps raw + rev.length → ∃ reached,
      (OpenDecoderMachine.next localCaller)^[j]
        (some (OpenDecoderMachine.cfg (some (OpenDecoderMachine.phaseLabel .scan)) regs raw rev out ctx)) =
          some reached ∧ OpenDecoderMachine.Owned reached.l := by
    intro j strict
    obtain ⟨reached, executed, _, _, owned, _⟩ :=
      OpenDecoderMachine.phase_prefix localCaller .scan raw rev out regs ctx j (Nat.le_of_lt strict)
    exact ⟨reached, executed, owned.mp strict⟩
  have run := certificate_decoder_prefix_installed caller localCaller (OpenDecoderMachine.runSteps raw + rev.length)
    (OpenDecoderMachine.cfg (some (OpenDecoderMachine.phaseLabel .scan)) regs raw rev out ctx) within
  rw [OpenDecoderMachine.scan_iterate] at run
  exact run

end Resources.RotationCertificate.FrontEndMachine

namespace Resources.RotationCertificate.FrontEndMachine
open Resources.BinaryCounter (Bits)

variable {K Λ R : Type} {Γ : K → Type}

/-- Proof-facing names for all fourteen physical stores. -/
structure LocalData where
  framedRaw : Bits := []
  frameFirstReverse : Bits := []
  frameCertReverse : Bits := []
  inputBits : Bits := []
  certificateBits : Bits := []
  inputRaw : Word := []
  decodeReverse : Word := []
  certificateWord : Word := []
  sourceTree : Word := []
  targetTree : Word := []
  treeReverse : Word := []
  pending : List Unit := []
  fuel : Bits := []
  bitsReverse : Bits := []

def stores (data : LocalData) (ctx : ∀ k, List (Γ k)) :
    ∀ k, List (Alphabet Γ k)
  | .inl .framedRaw => data.framedRaw
  | .inl .frameFirstReverse => data.frameFirstReverse
  | .inl .frameCertReverse => data.frameCertReverse
  | .inl .inputBits => data.inputBits
  | .inl .certificateBits => data.certificateBits
  | .inl .inputRaw => data.inputRaw
  | .inl .decodeReverse => data.decodeReverse
  | .inl .certificateWord => data.certificateWord
  | .inl .sourceTree => data.sourceTree
  | .inl .targetTree => data.targetTree
  | .inl .treeReverse => data.treeReverse
  | .inl .pending => data.pending
  | .inl .fuel => data.fuel
  | .inl .bitsReverse => data.bitsReverse
  | .inr k => ctx k

def cfg (label : Option (Label Λ)) (regs : Registers R) (data : LocalData)
    (ctx : ∀ k, List (Γ k)) : Cfg Γ Λ R where
  l := label
  var := regs
  stk := stores data ctx

theorem cfg_ext {before after : Cfg Γ Λ R}
    (control : before.l = after.l) (regs : before.var = after.var)
    (data : before.stk = after.stk) : before = after := by
  cases before
  cases after
  cases control
  cases regs
  cases data
  rfl

def framerContext (data : LocalData) (ctx : ∀ k, List (Γ k)) :
    ∀ k, List (FramerProtectedAlphabet Γ k)
  | .inl .inputRaw => data.inputRaw
  | .inl .sourceTree => data.sourceTree
  | .inl .targetTree => data.targetTree
  | .inl .treeReverse => data.treeReverse
  | .inl .pending => data.pending
  | .inl .fuel => data.fuel
  | .inl .bitsReverse => data.bitsReverse
  | .inl .decodeReverse => data.decodeReverse
  | .inl .certificateWord => data.certificateWord
  | .inr k => ctx k

def inputContext (data : LocalData) (ctx : ∀ k, List (Γ k)) :
    ∀ k, List (InputProtectedAlphabet Γ k)
  | .inl .framedRaw => data.framedRaw
  | .inl .frameFirstReverse => data.frameFirstReverse
  | .inl .frameCertReverse => data.frameCertReverse
  | .inl .inputBits => data.inputBits
  | .inl .certificateBits => data.certificateBits
  | .inl .decodeReverse => data.decodeReverse
  | .inl .certificateWord => data.certificateWord
  | .inr k => ctx k

def decoderContext (call : DecoderCall) (data : LocalData) (ctx : ∀ k, List (Γ k)) :
    ∀ k, List (DecoderProtectedAlphabet Γ k)
  | .inl .framedRaw => data.framedRaw
  | .inl .frameFirstReverse => data.frameFirstReverse
  | .inl .frameCertReverse => data.frameCertReverse
  | .inl .otherBits => match call with
    | .input => data.certificateBits
    | .certificate => data.inputBits
  | .inl .otherWord => match call with
    | .input => data.certificateWord
    | .certificate => data.inputRaw
  | .inl .sourceTree => data.sourceTree
  | .inl .targetTree => data.targetTree
  | .inl .treeReverse => data.treeReverse
  | .inl .pending => data.pending
  | .inl .fuel => data.fuel
  | .inl .bitsReverse => data.bitsReverse
  | .inr k => ctx k

def framerView (label : Option (OpenFramingMachine.Label (FramerCaller Λ)))
    (regs : OpenFramingMachine.Registers (FramerRegisterCaller R))
    (data : LocalData) (ctx : ∀ k, List (Γ k)) : FramerCfg Γ Λ R :=
  OpenFramingMachine.cfg label regs data.framedRaw data.frameFirstReverse
    data.frameCertReverse data.inputBits data.certificateBits (framerContext data ctx)

def inputView (label : Option (InputParserMachine.Label (ExtraLabel Λ)))
    (regs : InputParserMachine.Registers (InputRegisterCaller R))
    (data : LocalData) (ctx : ∀ k, List (Γ k)) : InputCfg Γ Λ R :=
  InputParserMachine.cfg label regs data.inputRaw data.treeReverse data.pending
    (InputParserMachine.treeOutputs data.sourceTree data.targetTree) data.fuel data.bitsReverse
    (inputContext data ctx)

def inputDecoderView (label : Option (OpenDecoderMachine.Label (InputDecoderCaller Λ)))
    (regs : OpenDecoderMachine.Registers (DecoderRegisterCaller R))
    (data : LocalData) (ctx : ∀ k, List (Γ k)) : InputDecoderCfg Γ Λ R :=
  OpenDecoderMachine.cfg label regs data.inputBits data.decodeReverse data.inputRaw
    (decoderContext .input data ctx)

def certificateDecoderView
    (label : Option (OpenDecoderMachine.Label (CertificateDecoderCaller Λ)))
    (regs : OpenDecoderMachine.Registers (DecoderRegisterCaller R))
    (data : LocalData) (ctx : ∀ k, List (Γ k)) : CertificateDecoderCfg Γ Λ R :=
  OpenDecoderMachine.cfg label regs data.certificateBits data.decodeReverse data.certificateWord
    (decoderContext .certificate data ctx)

theorem framerCfg_view (label : Option (OpenFramingMachine.Label (FramerCaller Λ)))
    (regs : OpenFramingMachine.Registers (FramerRegisterCaller R))
    (data : LocalData) (ctx : ∀ k, List (Γ k)) :
    framerCfg (framerView label regs data ctx) =
      cfg (label.map framerLabelEquiv) (framerRegisterEquiv regs) data ctx := by
  apply cfg_ext
  · rfl
  · rfl
  · funext slot
    obtain ⟨slot, rfl⟩ := framerStackEquiv.surjective slot
    change Transport.stackEquiv framerStackEquiv (framerSymbolEquiv (Γ := Γ))
      (framerView label regs data ctx).stk (framerStackEquiv slot) = _
    rw [Transport.stackEquiv_apply]
    cases slot with
    | inl slot => cases slot <;> change List.map id _ = _ <;> exact List.map_id _
    | inr slot => cases slot with
      | inl slot => cases slot <;> change List.map id _ = _ <;> exact List.map_id _
      | inr k => change List.map id _ = _; exact List.map_id _

theorem inputCfg_view (label : Option (InputParserMachine.Label (ExtraLabel Λ)))
    (regs : InputParserMachine.Registers (InputRegisterCaller R))
    (data : LocalData) (ctx : ∀ k, List (Γ k)) :
    inputCfg (inputView label regs data ctx) =
      cfg (label.map inputLabelEquiv) (inputRegisterEquiv regs) data ctx := by
  apply cfg_ext
  · rfl
  · rfl
  · funext slot
    obtain ⟨slot, rfl⟩ := inputStackEquiv.surjective slot
    change Transport.stackEquiv inputStackEquiv (inputSymbolEquiv (Γ := Γ))
      (inputView label regs data ctx).stk (inputStackEquiv slot) = _
    rw [Transport.stackEquiv_apply]
    cases slot with
    | inl slot => cases slot with
      | raw => change List.map id _ = _; exact List.map_id _
      | reverse => change List.map id _ = _; exact List.map_id _
      | pending => change List.map id _ = _; exact List.map_id _
      | output side => cases side <;> change List.map id _ = _ <;> exact List.map_id _
    | inr slot => cases slot with
      | inl slot => cases slot <;> change List.map id _ = _ <;> exact List.map_id _
      | inr slot => cases slot with
        | inl slot => cases slot <;> change List.map id _ = _ <;> exact List.map_id _
        | inr k => change List.map id _ = _; exact List.map_id _

theorem inputDecoderCfg_view (label : Option (OpenDecoderMachine.Label (InputDecoderCaller Λ)))
    (regs : OpenDecoderMachine.Registers (DecoderRegisterCaller R))
    (data : LocalData) (ctx : ∀ k, List (Γ k)) :
    inputDecoderCfg (inputDecoderView label regs data ctx) =
      cfg (label.map inputDecoderLabelEquiv) (decoderRegisterEquiv regs) data ctx := by
  apply cfg_ext
  · rfl
  · rfl
  · funext slot
    obtain ⟨slot, rfl⟩ := (decoderStackEquiv .input).surjective slot
    change Transport.stackEquiv (decoderStackEquiv .input) (decoderSymbolEquiv (Γ := Γ) .input)
      (inputDecoderView label regs data ctx).stk (decoderStackEquiv .input slot) = _
    rw [Transport.stackEquiv_apply]
    cases slot with
    | inl slot => cases slot <;> change List.map id _ = _ <;> exact List.map_id _
    | inr slot => cases slot with
      | inl slot => cases slot <;> change List.map id _ = _ <;> exact List.map_id _
      | inr k => change List.map id _ = _; exact List.map_id _

theorem certificateDecoderCfg_view
    (label : Option (OpenDecoderMachine.Label (CertificateDecoderCaller Λ)))
    (regs : OpenDecoderMachine.Registers (DecoderRegisterCaller R))
    (data : LocalData) (ctx : ∀ k, List (Γ k)) :
    certificateDecoderCfg (certificateDecoderView label regs data ctx) =
      cfg (label.map certificateDecoderLabelEquiv) (decoderRegisterEquiv regs) data ctx := by
  apply cfg_ext
  · rfl
  · rfl
  · funext slot
    obtain ⟨slot, rfl⟩ := (decoderStackEquiv .certificate).surjective slot
    change Transport.stackEquiv (decoderStackEquiv .certificate) (decoderSymbolEquiv (Γ := Γ) .certificate)
      (certificateDecoderView label regs data ctx).stk (decoderStackEquiv .certificate slot) = _
    rw [Transport.stackEquiv_apply]
    cases slot with
    | inl slot => cases slot <;> change List.map id _ = _ <;> exact List.map_id _
    | inr slot => cases slot with
      | inl slot => cases slot <;> change List.map id _ = _ <;> exact List.map_id _
      | inr k => change List.map id _ = _; exact List.map_id _

def afterInputDecoder (regs : Registers R) : Registers R :=
  (regs.1, BitDecoderMachine.zeroRegisters, regs.2.2)

def reset (regs : Registers R) : Registers R :=
  ((none, none), BitDecoderMachine.zeroRegisters, regs.2.2)

@[simp] theorem afterInputDecoder_resetFramer (regs : Registers R) :
    afterInputDecoder (resetFramer regs) = afterInputDecoder regs := rfl
@[simp] theorem reset_afterInputDecoder (regs : Registers R) :
    reset (afterInputDecoder regs) = reset regs := rfl
@[simp] theorem reset_reset (regs : Registers R) : reset (reset regs) = reset regs := rfl
@[simp] theorem afterInputDecoder_reset (regs : Registers R) :
    afterInputDecoder (reset regs) = reset regs := rfl

def entry (regs : Registers R) (raw : Bits) (ctx : ∀ k, List (Γ k)) : Cfg Γ Λ R :=
  cfg (some (framerLabel .scanPrefix)) regs { framedRaw := raw } ctx

def framedData (input cert : Bits) : LocalData :=
  { inputBits := input, certificateBits := cert }
def decodedInputData (input : Word) (cert : Bits) : LocalData :=
  { inputRaw := input, certificateBits := cert }
def parsedData (source target : BinaryTree Unit) (fuel cert : Bits) : LocalData :=
  { sourceTree := treeCode source, targetTree := treeCode target, fuel := fuel,
    certificateBits := cert }
def successData (source target : BinaryTree Unit) (fuel : Bits) (cert : Word) : LocalData :=
  { sourceTree := treeCode source, targetTree := treeCode target, fuel := fuel,
    certificateWord := cert }

def inputDecoderEntry (regs : Registers R) (input cert : Bits) (ctx : ∀ k, List (Γ k)) : Cfg Γ Λ R :=
  cfg (some (inputDecoderLabel .scan)) (resetFramer regs) (framedData input cert) ctx
def inputEntry (regs : Registers R) (input : Word) (cert : Bits)
    (ctx : ∀ k, List (Γ k)) : Cfg Γ Λ R :=
  cfg (some (InputParserMachine.treeLabel .source .init)) (afterInputDecoder regs)
    (decodedInputData input cert) ctx
def certificateDecoderEntry (regs : Registers R) (source target : BinaryTree Unit)
    (fuel cert : Bits) (ctx : ∀ k, List (Γ k)) : Cfg Γ Λ R :=
  cfg (some (certificateDecoderLabel .scan)) (reset regs) (parsedData source target fuel cert) ctx

/-- An independent source specification, including each distinct rejection boundary. -/
inductive Outcome
  | frameFailure
  | inputDecodeFailure (certificateBits : Bits)
  | inputParseFailure (input : Word) (certificateBits : Bits)
  | certificateDecodeFailure (source target : BinaryTree Unit) (fuel : Bits)
  | success (source target : BinaryTree Unit) (fuel : Bits) (certificate : Word)

def sourceOutcome (raw : Bits) : Outcome :=
  match BitPairFraming.unframe raw with
  | none => .frameFailure
  | some (input, cert) =>
      match (unpackWordRun input).1 with
      | none => .inputDecodeFailure cert
      | some word =>
          match (parseInputRun word).1 with
          | none => .inputParseFailure word cert
          | some (source, target, fuel) =>
              match (unpackWordRun cert).1 with
              | none => .certificateDecodeFailure source target fuel
              | some moves => .success source target fuel moves

def resultCfg (regs : Registers R) (ctx : ∀ k, List (Γ k)) : Outcome → Cfg Γ Λ R
  | .frameFailure => cfg (some rejectLabel) (resetFramer regs) {} ctx
  | .inputDecodeFailure cert =>
      cfg (some rejectLabel) (afterInputDecoder regs) { certificateBits := cert } ctx
  | .inputParseFailure input cert =>
      cfg (some rejectLabel) (reset regs) (decodedInputData input cert) ctx
  | .certificateDecodeFailure source target fuel =>
      cfg (some rejectLabel) (reset regs) (parsedData source target fuel []) ctx
  | .success source target fuel cert =>
      cfg (some dispatchLabel) (reset regs) (successData source target fuel cert) ctx

/-- Exact branchwise clock. This proof-side function never occurs in the program. -/
def runSteps (raw : Bits) : Nat :=
  BitPairFraming.runSteps raw +
    match BitPairFraming.unframe raw with
    | none => 0
    | some (input, cert) =>
        OpenDecoderMachine.runSteps input +
          match (unpackWordRun input).1 with
          | none => 0
          | some word =>
              InputParserMachine.inputSteps word +
                match (parseInputRun word).1 with
                | none => 0
                | some _ => OpenDecoderMachine.runSteps cert

theorem sourceOutcome_success_iff (raw : Bits) (source target : BinaryTree Unit)
    (fuel : Bits) (cert : Word) :
    sourceOutcome raw = .success source target fuel cert ↔
      raw = BitPairFraming.frame (wordBits (inputCode source target fuel)) (wordBits cert) := by
  constructor
  · intro returned
    unfold sourceOutcome at returned
    cases framing : BitPairFraming.unframe raw with
    | none => simp only [framing] at returned; cases returned
    | some pair =>
        rcases pair with ⟨inputBits, certBits⟩
        simp only [framing] at returned
        cases decoded : (unpackWordRun inputBits).1 with
        | none => simp only [decoded] at returned; cases returned
        | some input =>
            simp only [decoded] at returned
            cases parsed : (parseInputRun input).1 with
            | none => simp only [parsed] at returned; cases returned
            | some triple =>
                rcases triple with ⟨actualSource, actualTarget, actualFuel⟩
                simp only [parsed] at returned
                cases certificate : (unpackWordRun certBits).1 with
                | none => simp only [certificate] at returned; cases returned
                | some actualCert =>
                    simp only [certificate] at returned
                    obtain ⟨sourceEq, targetEq, fuelEq, certEq⟩ := Outcome.success.inj returned
                    have encoded := (BitPairFraming.unframe_iff raw inputBits certBits).mp framing
                    rw [
                      (unpackWordRun_iff inputBits input).mp decoded,
                      (parseInputRun_iff input actualSource actualTarget actualFuel).mp parsed,
                      (unpackWordRun_iff certBits actualCert).mp certificate] at encoded
                    simpa only [sourceEq, targetEq, fuelEq, certEq] using encoded
  · rintro rfl
    simp only [sourceOutcome, BitPairFraming.unframe_frame, unpackWordRun_code, parseInputRun_code]

theorem runSteps_pos (raw : Bits) : 0 < runSteps raw := by
  have positive := OpenFramingMachine.runSteps_pos raw
  unfold runSteps
  omega

theorem runSteps_le (raw : Bits) : runSteps raw ≤ 8 * raw.length + 13 := by
  have frameBound := BitPairFraming.runSteps_le raw
  unfold runSteps
  cases framing : BitPairFraming.unframe raw with
  | none => dsimp only; omega
  | some pair =>
      rcases pair with ⟨inputBits, certBits⟩
      dsimp only
      have size : raw.length = 2 * inputBits.length + certBits.length + 1 := by
        rw [(BitPairFraming.unframe_iff raw inputBits certBits).mp framing,
          BitPairFraming.frame_length]
      have inputBound := OpenDecoderMachine.runSteps_le inputBits
      have certBound := OpenDecoderMachine.runSteps_le certBits
      cases decoded : (unpackWordRun inputBits).1 with
      | none =>
          dsimp only
          exact (Nat.add_le_add frameBound inputBound).trans (by omega)
      | some input =>
          dsimp only
          have inputSize : inputBits.length = 4 * input.length := by
            rw [(unpackWordRun_iff inputBits input).mp decoded, wordBits_length]
          have parserBound := InputParserMachine.inputSteps_le input
          cases parsed : (parseInputRun input).1 with
          | none =>
              dsimp only
              exact (Nat.add_le_add frameBound
                (Nat.add_le_add inputBound parserBound)).trans (by omega)
          | some parsedInput =>
              dsimp only
              exact (Nat.add_le_add frameBound
                (Nat.add_le_add inputBound (Nat.add_le_add parserBound certBound))).trans (by omega)

theorem runSteps_code (source target : BinaryTree Unit) (fuel : Bits) (cert : Word) :
    runSteps (BitPairFraming.frame (wordBits (inputCode source target fuel)) (wordBits cert)) =
      12 * (inputCode source target fuel).length + 10 * cert.length + 11 := by
  simp only [runSteps, BitPairFraming.unframe_frame, unpackWordRun_code,
    parseInputRun_code, BitPairFraming.runSteps_frame, OpenDecoderMachine.runSteps_code,
    InputParserMachine.inputSteps_code, wordBits_length, inputCode_length, treeCode_length]
  simp only [← Nat.add_assoc]
  omega

end Resources.RotationCertificate.FrontEndMachine

