import Applications.Resources.RotationCertificate.FrontEndMachine.Transport

/-!
# FrontEndMachine: Basic
-/

set_option autoImplicit false
set_option warningAsError true

namespace Resources.RotationCertificate.FrontEndMachine

inductive LocalStack
  | framedRaw | frameFirstReverse | frameCertReverse | inputBits | certificateBits
  | inputRaw | decodeReverse | certificateWord | sourceTree | targetTree
  | treeReverse | pending | fuel | bitsReverse
  deriving DecidableEq

instance : Fintype LocalStack where
  elems := {.framedRaw, .frameFirstReverse, .frameCertReverse, .inputBits, .certificateBits,
    .inputRaw, .decodeReverse, .certificateWord, .sourceTree, .targetTree, .treeReverse,
    .pending, .fuel, .bitsReverse}
  complete slot := by cases slot <;> decide

abbrev StackId (K : Type) := LocalStack ⊕ K

variable {K Λ R : Type} {Γ : K → Type}

abbrev alphabet (Γ : K → Type) : StackId K → Type
  | .inl .framedRaw | .inl .frameFirstReverse | .inl .frameCertReverse
  | .inl .inputBits | .inl .certificateBits | .inl .fuel | .inl .bitsReverse => Bool
  | .inl .inputRaw | .inl .decodeReverse | .inl .certificateWord
  | .inl .sourceTree | .inl .targetTree | .inl .treeReverse => Tag
  | .inl .pending => Unit
  | .inr k => Γ k

instance alphabetFintype [∀ k, Fintype (Γ k)] (slot : StackId K) :
    Fintype (alphabet Γ slot) := by
  cases slot with
  | inl slot => cases slot <;> exact inferInstance
  | inr k => exact inferInstance

inductive InputProtected
  | framedRaw | frameFirstReverse | frameCertReverse | inputBits | certificateBits
  | decodeReverse | certificateWord
  deriving DecidableEq

instance : Fintype InputProtected where
  elems := {.framedRaw, .frameFirstReverse, .frameCertReverse, .inputBits, .certificateBits,
    .decodeReverse, .certificateWord}
  complete slot := by cases slot <;> decide

abbrev inputProtectedAlphabet (Γ : K → Type) : InputProtected ⊕ K → Type
  | .inl .framedRaw | .inl .frameFirstReverse | .inl .frameCertReverse
  | .inl .inputBits | .inl .certificateBits => Bool
  | .inl .decodeReverse | .inl .certificateWord => Tag
  | .inr k => Γ k

instance inputProtectedFintype [∀ k, Fintype (Γ k)] (slot : InputProtected ⊕ K) :
    Fintype (inputProtectedAlphabet Γ slot) := by
  cases slot with
  | inl slot => cases slot <;> exact inferInstance
  | inr k => exact inferInstance

/-- Includes every Input-owned and protected physical stack, with no missing component. -/
def inputStackEquiv : InputParserMachine.StackId (InputProtected ⊕ K) ≃ StackId K where
  toFun
    | .inl .raw => .inl .inputRaw
    | .inl .reverse => .inl .treeReverse
    | .inl .pending => .inl .pending
    | .inl (.output .source) => .inl .sourceTree
    | .inl (.output .target) => .inl .targetTree
    | .inr (.inl .fuel) => .inl .fuel
    | .inr (.inl .bitsReverse) => .inl .bitsReverse
    | .inr (.inr (.inl .framedRaw)) => .inl .framedRaw
    | .inr (.inr (.inl .frameFirstReverse)) => .inl .frameFirstReverse
    | .inr (.inr (.inl .frameCertReverse)) => .inl .frameCertReverse
    | .inr (.inr (.inl .inputBits)) => .inl .inputBits
    | .inr (.inr (.inl .certificateBits)) => .inl .certificateBits
    | .inr (.inr (.inl .decodeReverse)) => .inl .decodeReverse
    | .inr (.inr (.inl .certificateWord)) => .inl .certificateWord
    | .inr (.inr (.inr k)) => .inr k
  invFun
    | .inl .framedRaw => .inr (.inr (.inl .framedRaw))
    | .inl .frameFirstReverse => .inr (.inr (.inl .frameFirstReverse))
    | .inl .frameCertReverse => .inr (.inr (.inl .frameCertReverse))
    | .inl .inputBits => .inr (.inr (.inl .inputBits))
    | .inl .certificateBits => .inr (.inr (.inl .certificateBits))
    | .inl .inputRaw => .inl .raw
    | .inl .decodeReverse => .inr (.inr (.inl .decodeReverse))
    | .inl .certificateWord => .inr (.inr (.inl .certificateWord))
    | .inl .sourceTree => .inl (.output .source)
    | .inl .targetTree => .inl (.output .target)
    | .inl .treeReverse => .inl .reverse
    | .inl .pending => .inl .pending
    | .inl .fuel => .inr (.inl .fuel)
    | .inl .bitsReverse => .inr (.inl .bitsReverse)
    | .inr k => .inr (.inr (.inr k))
  left_inv slot := by
    cases slot with
    | inl slot => cases slot with
      | raw => rfl
      | reverse => rfl
      | pending => rfl
      | output side => cases side <;> rfl
    | inr extra => cases extra with
      | inl slot => cases slot <;> rfl
      | inr rest => cases rest with
        | inl slot => cases slot <;> rfl
        | inr k => rfl
  right_inv slot := by
    cases slot with
    | inl slot => cases slot <;> rfl
    | inr k => rfl

def inputSymbolEquiv (slot : InputParserMachine.StackId (InputProtected ⊕ K)) :
    InputParserMachine.alphabet (inputProtectedAlphabet Γ) slot ≃
      alphabet Γ (inputStackEquiv slot) := by
  cases slot with
  | inl slot => cases slot with
    | raw => exact Equiv.refl _
    | reverse => exact Equiv.refl _
    | pending => exact Equiv.refl _
    | output side => cases side <;> exact Equiv.refl _
  | inr extra => cases extra with
    | inl slot => cases slot <;> exact Equiv.refl _
    | inr rest => cases rest with
      | inl slot => cases slot <;> exact Equiv.refl _
      | inr k => exact Equiv.refl _

inductive FramerProtected
  | inputRaw | sourceTree | targetTree | treeReverse | pending | fuel | bitsReverse
  | decodeReverse | certificateWord
  deriving DecidableEq

instance : Fintype FramerProtected where
  elems := {.inputRaw, .sourceTree, .targetTree, .treeReverse, .pending, .fuel, .bitsReverse,
    .decodeReverse, .certificateWord}
  complete slot := by cases slot <;> decide

abbrev framerProtectedAlphabet (Γ : K → Type) : FramerProtected ⊕ K → Type
  | .inl .inputRaw | .inl .sourceTree | .inl .targetTree | .inl .treeReverse
  | .inl .decodeReverse | .inl .certificateWord => Tag
  | .inl .pending => Unit
  | .inl .fuel | .inl .bitsReverse => Bool
  | .inr k => Γ k

instance framerProtectedFintype [∀ k, Fintype (Γ k)] (slot : FramerProtected ⊕ K) :
    Fintype (framerProtectedAlphabet Γ slot) := by
  cases slot with
  | inl slot => cases slot <;> exact inferInstance
  | inr k => exact inferInstance

def framerStackEquiv : OpenFramingMachine.StackId (FramerProtected ⊕ K) ≃ StackId K where
  toFun
    | .inl .raw => .inl .framedRaw
    | .inl .firstReverse => .inl .frameFirstReverse
    | .inl .certificateReverse => .inl .frameCertReverse
    | .inl .inputBits => .inl .inputBits
    | .inl .certificateBits => .inl .certificateBits
    | .inr (.inl .inputRaw) => .inl .inputRaw
    | .inr (.inl .sourceTree) => .inl .sourceTree
    | .inr (.inl .targetTree) => .inl .targetTree
    | .inr (.inl .treeReverse) => .inl .treeReverse
    | .inr (.inl .pending) => .inl .pending
    | .inr (.inl .fuel) => .inl .fuel
    | .inr (.inl .bitsReverse) => .inl .bitsReverse
    | .inr (.inl .decodeReverse) => .inl .decodeReverse
    | .inr (.inl .certificateWord) => .inl .certificateWord
    | .inr (.inr k) => .inr k
  invFun
    | .inl .framedRaw => .inl .raw
    | .inl .frameFirstReverse => .inl .firstReverse
    | .inl .frameCertReverse => .inl .certificateReverse
    | .inl .inputBits => .inl .inputBits
    | .inl .certificateBits => .inl .certificateBits
    | .inl .inputRaw => .inr (.inl .inputRaw)
    | .inl .sourceTree => .inr (.inl .sourceTree)
    | .inl .targetTree => .inr (.inl .targetTree)
    | .inl .treeReverse => .inr (.inl .treeReverse)
    | .inl .pending => .inr (.inl .pending)
    | .inl .fuel => .inr (.inl .fuel)
    | .inl .bitsReverse => .inr (.inl .bitsReverse)
    | .inl .decodeReverse => .inr (.inl .decodeReverse)
    | .inl .certificateWord => .inr (.inl .certificateWord)
    | .inr k => .inr (.inr k)
  left_inv slot := by
    cases slot with
    | inl slot => cases slot <;> rfl
    | inr rest => cases rest with
      | inl slot => cases slot <;> rfl
      | inr k => rfl
  right_inv slot := by
    cases slot with
    | inl slot => cases slot <;> rfl
    | inr k => rfl

def framerSymbolEquiv (slot : OpenFramingMachine.StackId (FramerProtected ⊕ K)) :
    OpenFramingMachine.alphabet (framerProtectedAlphabet Γ) slot ≃
      alphabet Γ (framerStackEquiv slot) := by
  cases slot with
  | inl slot => cases slot <;> exact Equiv.refl _
  | inr rest => cases rest with
    | inl slot => cases slot <;> exact Equiv.refl _
    | inr k => exact Equiv.refl _

inductive DecoderCall | input | certificate
  deriving DecidableEq

instance : Fintype DecoderCall where
  elems := {.input, .certificate}
  complete call := by cases call <;> decide

inductive DecoderProtected
  | framedRaw | frameFirstReverse | frameCertReverse | otherBits | otherWord
  | sourceTree | targetTree | treeReverse | pending | fuel | bitsReverse
  deriving DecidableEq

instance : Fintype DecoderProtected where
  elems := {.framedRaw, .frameFirstReverse, .frameCertReverse, .otherBits, .otherWord,
    .sourceTree, .targetTree, .treeReverse, .pending, .fuel, .bitsReverse}
  complete slot := by cases slot <;> decide

abbrev decoderProtectedAlphabet (Γ : K → Type) : DecoderProtected ⊕ K → Type
  | .inl .framedRaw | .inl .frameFirstReverse | .inl .frameCertReverse
  | .inl .otherBits | .inl .fuel | .inl .bitsReverse => Bool
  | .inl .otherWord | .inl .sourceTree | .inl .targetTree | .inl .treeReverse => Tag
  | .inl .pending => Unit
  | .inr k => Γ k

instance decoderProtectedFintype [∀ k, Fintype (Γ k)] (slot : DecoderProtected ⊕ K) :
    Fintype (decoderProtectedAlphabet Γ slot) := by
  cases slot with
  | inl slot => cases slot <;> exact inferInstance
  | inr k => exact inferInstance

def activeBits : DecoderCall → LocalStack
  | .input => .inputBits
  | .certificate => .certificateBits
def inactiveBits : DecoderCall → LocalStack
  | .input => .certificateBits
  | .certificate => .inputBits
def activeWord : DecoderCall → LocalStack
  | .input => .inputRaw
  | .certificate => .certificateWord
def inactiveWord : DecoderCall → LocalStack
  | .input => .certificateWord
  | .certificate => .inputRaw

/-- The two calls share only the declared reverse stack; inactive bit/word stores remain protected. -/
def decoderStackEquiv (call : DecoderCall) :
    OpenDecoderMachine.StackId (DecoderProtected ⊕ K) ≃ StackId K where
  toFun
    | .inl .input => .inl (activeBits call)
    | .inl .reverse => .inl .decodeReverse
    | .inl .output => .inl (activeWord call)
    | .inr (.inl .framedRaw) => .inl .framedRaw
    | .inr (.inl .frameFirstReverse) => .inl .frameFirstReverse
    | .inr (.inl .frameCertReverse) => .inl .frameCertReverse
    | .inr (.inl .otherBits) => .inl (inactiveBits call)
    | .inr (.inl .otherWord) => .inl (inactiveWord call)
    | .inr (.inl .sourceTree) => .inl .sourceTree
    | .inr (.inl .targetTree) => .inl .targetTree
    | .inr (.inl .treeReverse) => .inl .treeReverse
    | .inr (.inl .pending) => .inl .pending
    | .inr (.inl .fuel) => .inl .fuel
    | .inr (.inl .bitsReverse) => .inl .bitsReverse
    | .inr (.inr k) => .inr k
  invFun
    | .inl .framedRaw => .inr (.inl .framedRaw)
    | .inl .frameFirstReverse => .inr (.inl .frameFirstReverse)
    | .inl .frameCertReverse => .inr (.inl .frameCertReverse)
    | .inl .inputBits => match call with
      | .input => .inl .input
      | .certificate => .inr (.inl .otherBits)
    | .inl .certificateBits => match call with
      | .input => .inr (.inl .otherBits)
      | .certificate => .inl .input
    | .inl .inputRaw => match call with
      | .input => .inl .output
      | .certificate => .inr (.inl .otherWord)
    | .inl .certificateWord => match call with
      | .input => .inr (.inl .otherWord)
      | .certificate => .inl .output
    | .inl .decodeReverse => .inl .reverse
    | .inl .sourceTree => .inr (.inl .sourceTree)
    | .inl .targetTree => .inr (.inl .targetTree)
    | .inl .treeReverse => .inr (.inl .treeReverse)
    | .inl .pending => .inr (.inl .pending)
    | .inl .fuel => .inr (.inl .fuel)
    | .inl .bitsReverse => .inr (.inl .bitsReverse)
    | .inr k => .inr (.inr k)
  left_inv slot := by
    cases call <;> cases slot with
    | inl slot => cases slot <;> rfl
    | inr rest => cases rest with
      | inl slot => cases slot <;> rfl
      | inr k => rfl
  right_inv slot := by
    cases call <;> cases slot with
    | inl slot => cases slot <;> rfl
    | inr k => rfl

def decoderSymbolEquiv (call : DecoderCall)
    (slot : OpenDecoderMachine.StackId (DecoderProtected ⊕ K)) :
    OpenDecoderMachine.alphabet (decoderProtectedAlphabet Γ) slot ≃
      alphabet Γ (decoderStackEquiv call slot) := by
  cases call <;> cases slot with
  | inl slot => cases slot <;> exact Equiv.refl _
  | inr rest => cases rest with
    | inl slot => cases slot <;> exact Equiv.refl _
    | inr k => exact Equiv.refl _

abbrev Registers (R : Type) := TreeParserMachine.Temporaries × (OpenDecoderMachine.Temporaries × R)
abbrev RemainingDecoderFields := Option Bool × (Option Bool × (Option Bool × Option Tag))
abbrev InputRegisterCaller (R : Type) := OpenDecoderMachine.Temporaries × R
abbrev DecoderRegisterCaller (R : Type) := TreeParserMachine.Temporaries × R
abbrev FramerRegisterCaller (R : Type) := TreeParserMachine.Temporaries × (RemainingDecoderFields × R)

def inputRegisterEquiv : InputParserMachine.Registers (InputRegisterCaller R) ≃ Registers R :=
  Equiv.refl _

/-- A static finite permutation; no tree state is reset by this representation map. -/
def decoderRegisterEquiv : OpenDecoderMachine.Registers (DecoderRegisterCaller R) ≃ Registers R where
  toFun | (decoder, tree, caller) => (tree, decoder, caller)
  invFun | (tree, decoder, caller) => (decoder, tree, caller)
  left_inv regs := by rcases regs with ⟨decoder, tree, caller⟩; rfl
  right_inv regs := by rcases regs with ⟨tree, decoder, caller⟩; rfl

/-- Framing borrows exactly b0 and protects the other four decoder fields. -/
def framerRegisterEquiv : OpenFramingMachine.Registers (FramerRegisterCaller R) ≃ Registers R where
  toFun | (b0, tree, (b1, b2, b3, tag), caller) => (tree, ⟨b0, b1, b2, b3, tag⟩, caller)
  invFun
    | (tree, decoder, caller) =>
      (decoder.b0, tree, (decoder.b1, decoder.b2, decoder.b3, decoder.tag), caller)
  left_inv regs := by rcases regs with ⟨b0, tree, ⟨b1, b2, b3, tag⟩, caller⟩; rfl
  right_inv regs := by rcases regs with ⟨tree, decoder, caller⟩; cases decoder; rfl

def resetFramer (regs : Registers R) : Registers R :=
  (regs.1, { regs.2.1 with b0 := none }, regs.2.2)

@[simp] theorem framerRegisterEquiv_reset (regs : OpenFramingMachine.Registers (FramerRegisterCaller R)) :
    framerRegisterEquiv (OpenFramingMachine.reset regs) = resetFramer (framerRegisterEquiv regs) := by
  rcases regs with ⟨b0, tree, ⟨b1, b2, b3, tag⟩, caller⟩
  rfl

@[simp] theorem decoderRegisterEquiv_reset (regs : OpenDecoderMachine.Registers (DecoderRegisterCaller R)) :
    decoderRegisterEquiv (OpenDecoderMachine.reset regs) =
      (regs.2.1, BitDecoderMachine.zeroRegisters, regs.2.2) := rfl

@[simp] theorem inputRegisterEquiv_reset (regs : InputParserMachine.Registers (InputRegisterCaller R)) :
    inputRegisterEquiv (InputParserMachine.reset regs) = ((none, none), regs.2) := rfl

inductive DecoderTail | emit | clear
  deriving DecidableEq

instance : Fintype DecoderTail where
  elems := {.emit, .clear}
  complete phase := by cases phase <;> decide

def tailPhase : DecoderTail → OpenDecoderMachine.Phase
  | .emit => .emit
  | .clear => .clear

abbrev ExtraLabel (Λ : Type) := OpenFramingMachine.Phase ⊕
  (OpenDecoderMachine.Phase ⊕ (DecoderTail ⊕ (Unit ⊕ Λ)))
abbrev Label (Λ : Type) := InputParserMachine.Label (ExtraLabel Λ)
abbrev Statement (Γ : K → Type) (Λ R : Type) := Turing.TM2.Stmt (alphabet Γ) (Label Λ) (Registers R)
abbrev Cfg (Γ : K → Type) (Λ R : Type) := Turing.TM2.Cfg (alphabet Γ) (Label Λ) (Registers R)

def framerLabel (phase : OpenFramingMachine.Phase) : Label Λ :=
  InputParserMachine.callerLabel (.inl phase)
def inputDecoderLabel (phase : OpenDecoderMachine.Phase) : Label Λ :=
  InputParserMachine.callerLabel (.inr (.inl phase))
def certificateDecoderLabel : OpenDecoderMachine.Phase → Label Λ
  | .scan => InputParserMachine.resultLabel .success
  | .emit => InputParserMachine.callerLabel (.inr (.inr (.inl .emit)))
  | .clear => InputParserMachine.callerLabel (.inr (.inr (.inl .clear)))
def dispatchLabel : Label Λ := InputParserMachine.callerLabel (.inr (.inr (.inr (.inl ()))))
def rejectLabel : Label Λ := InputParserMachine.resultLabel .failure
def callerLabel (label : Λ) : Label Λ :=
  InputParserMachine.callerLabel (.inr (.inr (.inr (.inr label))))

def inputLabelEquiv : InputParserMachine.Label (ExtraLabel Λ) ≃ Label Λ := Equiv.refl _

abbrev InputOwned := InputParserMachine.OwnedLabels

/-- Reuses the actual constructor-by-constructor presentation of exactly Input.FullOwned. -/
def inputOwnedLabel (label : InputOwned) : Label Λ :=
  (InputParserMachine.ownedLabelEquiv (Λ := ExtraLabel Λ) label).1

theorem inputOwnedLabel_injective : Function.Injective (inputOwnedLabel (Λ := Λ)) := by
  intro left right equal
  exact (InputParserMachine.ownedLabelEquiv (Λ := ExtraLabel Λ)).injective (Subtype.ext equal)

theorem inputOwnedLabel_image (label : Label Λ) :
    (∃ owned, inputOwnedLabel owned = label) ↔ InputParserMachine.FullOwned (some label) := by
  constructor
  · rintro ⟨owned, rfl⟩
    exact (InputParserMachine.ownedLabelEquiv (Λ := ExtraLabel Λ) owned).2
  · intro owned
    refine ⟨(InputParserMachine.ownedLabelEquiv (Λ := ExtraLabel Λ)).symm ⟨label, owned⟩, ?_⟩
    exact congrArg Subtype.val
      ((InputParserMachine.ownedLabelEquiv (Λ := ExtraLabel Λ)).apply_symm_apply ⟨label, owned⟩)

abbrev LabelPartition (Λ : Type) := InputOwned ⊕ (TreeParserMachine.Result ⊕ ExtraLabel Λ)

/-- A complete constructive partition into the 25 Input phases, its two exits and all callers. -/
def inputPartitionEquiv : LabelPartition Λ ≃ Label Λ where
  toFun
    | .inl owned => inputOwnedLabel owned
    | .inr (.inl result) => InputParserMachine.resultLabel result
    | .inr (.inr label) => InputParserMachine.callerLabel label
  invFun
    | .inl (side, phase) => .inl (.inl (side, phase))
    | .inr (.inl (side, .success)) => .inl (.inr (.inl side))
    | .inr (.inl (.source, .failure)) => .inr (.inl .failure)
    | .inr (.inl (.target, .failure)) => .inl (.inr (.inr (.inl ())))
    | .inr (.inr (.inl phase)) => .inl (.inr (.inr (.inr phase)))
    | .inr (.inr (.inr (.inl _))) => .inr (.inl .success)
    | .inr (.inr (.inr (.inr label))) => .inr (.inr label)
  left_inv label := by
    cases label with
    | inl owned => cases owned with
      | inl pair => rcases pair with ⟨side, phase⟩; rfl
      | inr extra => cases extra with
        | inl side => cases side <;> rfl
        | inr extra => cases extra with
          | inl token => cases token; rfl
          | inr phase => rfl
    | inr rest => cases rest with
      | inl result => cases result <;> rfl
      | inr label => rfl
  right_inv label := by
    cases label with
    | inl pair => rcases pair with ⟨side, phase⟩; rfl
    | inr rest => cases rest with
      | inl pair => rcases pair with ⟨side, result⟩; cases side <;> cases result <;> rfl
      | inr rest => cases rest with
        | inl phase => rfl
        | inr rest => cases rest with
          | inl token => cases token; rfl
          | inr label => rfl

abbrev FramerCaller (Λ : Type) := InputOwned ⊕
  (DecoderTail ⊕ (OpenDecoderMachine.Phase ⊕ (Unit ⊕ Λ)))

/-- Complete framer labels, including its disjoint caller complement. -/
def framerPartitionEquiv : OpenFramingMachine.Label (FramerCaller Λ) ≃ LabelPartition Λ where
  toFun
    | .inl phase => .inr (.inr (.inl phase))
    | .inr (.inl .success) => .inr (.inr (.inr (.inl .scan)))
    | .inr (.inl .failure) => .inr (.inl .failure)
    | .inr (.inr (.inl owned)) => .inl owned
    | .inr (.inr (.inr (.inl tail))) => .inr (.inr (.inr (.inl (tailPhase tail))))
    | .inr (.inr (.inr (.inr (.inl .scan)))) => .inr (.inl .success)
    | .inr (.inr (.inr (.inr (.inl .emit)))) => .inr (.inr (.inr (.inr (.inl .emit))))
    | .inr (.inr (.inr (.inr (.inl .clear)))) => .inr (.inr (.inr (.inr (.inl .clear))))
    | .inr (.inr (.inr (.inr (.inr (.inl token))))) =>
        .inr (.inr (.inr (.inr (.inr (.inl token)))))
    | .inr (.inr (.inr (.inr (.inr (.inr label))))) =>
        .inr (.inr (.inr (.inr (.inr (.inr label)))))
  invFun
    | .inl owned => .inr (.inr (.inl owned))
    | .inr (.inl .success) => .inr (.inr (.inr (.inr (.inl .scan))))
    | .inr (.inl .failure) => .inr (.inl .failure)
    | .inr (.inr (.inl phase)) => .inl phase
    | .inr (.inr (.inr (.inl .scan))) => .inr (.inl .success)
    | .inr (.inr (.inr (.inl .emit))) => .inr (.inr (.inr (.inl .emit)))
    | .inr (.inr (.inr (.inl .clear))) => .inr (.inr (.inr (.inl .clear)))
    | .inr (.inr (.inr (.inr (.inl tail)))) => .inr (.inr (.inr (.inr (.inl (tailPhase tail)))))
    | .inr (.inr (.inr (.inr (.inr (.inl token))))) =>
        .inr (.inr (.inr (.inr (.inr (.inl token)))))
    | .inr (.inr (.inr (.inr (.inr (.inr label))))) =>
        .inr (.inr (.inr (.inr (.inr (.inr label)))))
  left_inv label := by
    cases label with
    | inl phase => rfl
    | inr external => cases external with
      | inl result => cases result <;> rfl
      | inr caller => cases caller with
        | inl owned => rfl
        | inr rest => cases rest with
          | inl tail => cases tail <;> rfl
          | inr rest => cases rest with
            | inl phase => cases phase <;> rfl
            | inr rest => cases rest <;> rfl
  right_inv label := by
    cases label with
    | inl owned => rfl
    | inr rest => cases rest with
      | inl result => cases result <;> rfl
      | inr extra => cases extra with
        | inl phase => rfl
        | inr rest => cases rest with
          | inl phase => cases phase <;> rfl
          | inr rest => cases rest with
            | inl tail => cases tail <;> rfl
            | inr rest => cases rest <;> rfl

def framerLabelEquiv : OpenFramingMachine.Label (FramerCaller Λ) ≃ Label Λ :=
  framerPartitionEquiv.trans inputPartitionEquiv

inductive SourceAfterEntry | scan | emit | undo | dropPending
  deriving DecidableEq

instance : Fintype SourceAfterEntry where
  elems := {.scan, .emit, .undo, .dropPending}
  complete phase := by cases phase <;> decide

def sourceAfterPhase : SourceAfterEntry → TreeParserMachine.Phase
  | .scan => .scan
  | .emit => .emit
  | .undo => .undo
  | .dropPending => .dropPending

abbrev InputAfterEntry := SourceAfterEntry ⊕ (TreeParserMachine.Phase ⊕
  (InputParserMachine.TreeSide ⊕ (Unit ⊕ InputParserMachine.Phase)))

/-- Removes exactly source init, with an explicit inverse for every remaining constructor. -/
def inputEntryEquiv : Unit ⊕ InputAfterEntry ≃ InputOwned where
  toFun
    | .inl _ => .inl (.source, .init)
    | .inr (.inl phase) => .inl (.source, sourceAfterPhase phase)
    | .inr (.inr (.inl phase)) => .inl (.target, phase)
    | .inr (.inr (.inr (.inl side))) => .inr (.inl side)
    | .inr (.inr (.inr (.inr (.inl token)))) => .inr (.inr (.inl token))
    | .inr (.inr (.inr (.inr (.inr phase)))) => .inr (.inr (.inr phase))
  invFun
    | .inl (.source, .init) => .inl ()
    | .inl (.source, .scan) => .inr (.inl .scan)
    | .inl (.source, .emit) => .inr (.inl .emit)
    | .inl (.source, .undo) => .inr (.inl .undo)
    | .inl (.source, .dropPending) => .inr (.inl .dropPending)
    | .inl (.target, phase) => .inr (.inr (.inl phase))
    | .inr (.inl side) => .inr (.inr (.inr (.inl side)))
    | .inr (.inr (.inl token)) => .inr (.inr (.inr (.inr (.inl token))))
    | .inr (.inr (.inr phase)) => .inr (.inr (.inr (.inr (.inr phase))))
  left_inv label := by
    cases label with
    | inl token => cases token; rfl
    | inr afterEntry => cases afterEntry with
      | inl phase => cases phase <;> rfl
      | inr rest => cases rest with
        | inl phase => rfl
        | inr rest => cases rest with
          | inl side => rfl
          | inr rest => cases rest <;> rfl
  right_inv label := by
    cases label with
    | inl pair => rcases pair with ⟨side, phase⟩; cases side <;> cases phase <;> rfl
    | inr rest => cases rest with
      | inl side => rfl
      | inr rest => cases rest <;> rfl

def inputAfterEntryLabel (label : InputAfterEntry) : InputOwned := inputEntryEquiv (.inr label)

theorem inputAfterEntryLabel_injective : Function.Injective inputAfterEntryLabel := by
  intro left right equal
  exact Sum.inr.inj (inputEntryEquiv.injective equal)

theorem inputAfterEntryLabel_image (label : InputOwned) :
    (∃ afterEntry, inputAfterEntryLabel afterEntry = label) ↔ label ≠ .inl (.source, .init) := by
  constructor
  · rintro ⟨afterEntry, rfl⟩ equal
    have same := inputEntryEquiv.injective
      (show inputEntryEquiv (.inr afterEntry) = inputEntryEquiv (.inl ()) from equal)
    cases same
  · intro different
    obtain ⟨entry, rfl⟩ := inputEntryEquiv.surjective label
    cases entry with
    | inl token => cases token; exact False.elim (different rfl)
    | inr afterEntry => exact ⟨afterEntry, rfl⟩

abbrev InputDecoderCaller (Λ : Type) := OpenFramingMachine.Phase ⊕
  (InputAfterEntry ⊕ (OpenDecoderMachine.Phase ⊕ (Unit ⊕ Λ)))
abbrev EntryPartition (Λ : Type) := (Unit ⊕ InputAfterEntry) ⊕
  (TreeParserMachine.Result ⊕ ExtraLabel Λ)

def inputDecoderSplitEquiv : OpenDecoderMachine.Label (InputDecoderCaller Λ) ≃ EntryPartition Λ where
  toFun
    | .inl phase => .inr (.inr (.inr (.inl phase)))
    | .inr (.inl .success) => .inl (.inl ())
    | .inr (.inl .failure) => .inr (.inl .failure)
    | .inr (.inr (.inl phase)) => .inr (.inr (.inl phase))
    | .inr (.inr (.inr (.inl afterEntry))) => .inl (.inr afterEntry)
    | .inr (.inr (.inr (.inr (.inl .scan)))) => .inr (.inl .success)
    | .inr (.inr (.inr (.inr (.inl .emit)))) => .inr (.inr (.inr (.inr (.inl .emit))))
    | .inr (.inr (.inr (.inr (.inl .clear)))) => .inr (.inr (.inr (.inr (.inl .clear))))
    | .inr (.inr (.inr (.inr (.inr (.inl token))))) =>
        .inr (.inr (.inr (.inr (.inr (.inl token)))))
    | .inr (.inr (.inr (.inr (.inr (.inr label))))) =>
        .inr (.inr (.inr (.inr (.inr (.inr label)))))
  invFun
    | .inl (.inl _) => .inr (.inl .success)
    | .inl (.inr afterEntry) => .inr (.inr (.inr (.inl afterEntry)))
    | .inr (.inl .success) => .inr (.inr (.inr (.inr (.inl .scan))))
    | .inr (.inl .failure) => .inr (.inl .failure)
    | .inr (.inr (.inl phase)) => .inr (.inr (.inl phase))
    | .inr (.inr (.inr (.inl phase))) => .inl phase
    | .inr (.inr (.inr (.inr (.inl tail)))) => .inr (.inr (.inr (.inr (.inl (tailPhase tail)))))
    | .inr (.inr (.inr (.inr (.inr (.inl token))))) =>
        .inr (.inr (.inr (.inr (.inr (.inl token)))))
    | .inr (.inr (.inr (.inr (.inr (.inr label))))) =>
        .inr (.inr (.inr (.inr (.inr (.inr label)))))
  left_inv label := by
    cases label with
    | inl phase => rfl
    | inr external => cases external with
      | inl result => cases result <;> rfl
      | inr caller => cases caller with
        | inl phase => rfl
        | inr rest => cases rest with
          | inl afterEntry => rfl
          | inr rest => cases rest with
            | inl phase => cases phase <;> rfl
            | inr rest => cases rest <;> rfl
  right_inv label := by
    cases label with
    | inl entry => cases entry with
      | inl token => cases token; rfl
      | inr afterEntry => rfl
    | inr rest => cases rest with
      | inl result => cases result <;> rfl
      | inr extra => cases extra with
        | inl phase => rfl
        | inr rest => cases rest with
          | inl phase => rfl
          | inr rest => cases rest with
            | inl tail => cases tail <;> rfl
            | inr rest => cases rest <;> rfl

def inputDecoderLabelEquiv : OpenDecoderMachine.Label (InputDecoderCaller Λ) ≃ Label Λ :=
  (inputDecoderSplitEquiv.trans
    (Equiv.sumCongr inputEntryEquiv (Equiv.refl (TreeParserMachine.Result ⊕ ExtraLabel Λ)))).trans
      inputPartitionEquiv

abbrev CertificateDecoderCaller (Λ : Type) := InputOwned ⊕
  (OpenFramingMachine.Phase ⊕ (OpenDecoderMachine.Phase ⊕ Λ))

def certificateDecoderPartitionEquiv :
    OpenDecoderMachine.Label (CertificateDecoderCaller Λ) ≃ LabelPartition Λ where
  toFun
    | .inl .scan => .inr (.inl .success)
    | .inl .emit => .inr (.inr (.inr (.inr (.inl .emit))))
    | .inl .clear => .inr (.inr (.inr (.inr (.inl .clear))))
    | .inr (.inl .success) => .inr (.inr (.inr (.inr (.inr (.inl ())))))
    | .inr (.inl .failure) => .inr (.inl .failure)
    | .inr (.inr (.inl owned)) => .inl owned
    | .inr (.inr (.inr (.inl phase))) => .inr (.inr (.inl phase))
    | .inr (.inr (.inr (.inr (.inl phase)))) => .inr (.inr (.inr (.inl phase)))
    | .inr (.inr (.inr (.inr (.inr label)))) =>
        .inr (.inr (.inr (.inr (.inr (.inr label)))))
  invFun
    | .inl owned => .inr (.inr (.inl owned))
    | .inr (.inl .success) => .inl .scan
    | .inr (.inl .failure) => .inr (.inl .failure)
    | .inr (.inr (.inl phase)) => .inr (.inr (.inr (.inl phase)))
    | .inr (.inr (.inr (.inl phase))) => .inr (.inr (.inr (.inr (.inl phase))))
    | .inr (.inr (.inr (.inr (.inl tail)))) => .inl (tailPhase tail)
    | .inr (.inr (.inr (.inr (.inr (.inl _))))) => .inr (.inl .success)
    | .inr (.inr (.inr (.inr (.inr (.inr label))))) => .inr (.inr (.inr (.inr (.inr label))))
  left_inv label := by
    cases label with
    | inl phase => cases phase <;> rfl
    | inr external => cases external with
      | inl result => cases result <;> rfl
      | inr caller => cases caller with
        | inl owned => rfl
        | inr rest => cases rest with
          | inl phase => rfl
          | inr rest => cases rest <;> rfl
  right_inv label := by
    cases label with
    | inl owned => rfl
    | inr rest => cases rest with
      | inl result => cases result <;> rfl
      | inr extra => cases extra with
        | inl phase => rfl
        | inr rest => cases rest with
          | inl phase => rfl
          | inr rest => cases rest with
            | inl tail => cases tail <;> rfl
            | inr rest => cases rest with
              | inl token => cases token; rfl
              | inr label => rfl

def certificateDecoderLabelEquiv :
    OpenDecoderMachine.Label (CertificateDecoderCaller Λ) ≃ Label Λ :=
  certificateDecoderPartitionEquiv.trans inputPartitionEquiv

@[simp] theorem framerLabelEquiv_phase (phase : OpenFramingMachine.Phase) :
    framerLabelEquiv (OpenFramingMachine.phaseLabel phase) = framerLabel (Λ := Λ) phase := rfl
@[simp] theorem framerLabelEquiv_success :
    framerLabelEquiv (OpenFramingMachine.resultLabel .success) = inputDecoderLabel (Λ := Λ) .scan := rfl
@[simp] theorem framerLabelEquiv_failure :
    framerLabelEquiv (OpenFramingMachine.resultLabel .failure) = rejectLabel (Λ := Λ) := rfl
@[simp] theorem inputDecoderLabelEquiv_phase (phase : OpenDecoderMachine.Phase) :
    inputDecoderLabelEquiv (OpenDecoderMachine.phaseLabel phase) = inputDecoderLabel (Λ := Λ) phase := rfl
@[simp] theorem inputDecoderLabelEquiv_success :
    inputDecoderLabelEquiv (OpenDecoderMachine.resultLabel .success) =
      InputParserMachine.treeLabel (Λ := ExtraLabel Λ) .source .init := rfl
@[simp] theorem inputDecoderLabelEquiv_failure :
    inputDecoderLabelEquiv (OpenDecoderMachine.resultLabel .failure) = rejectLabel (Λ := Λ) := rfl
@[simp] theorem certificateDecoderLabelEquiv_phase (phase : OpenDecoderMachine.Phase) :
    certificateDecoderLabelEquiv (OpenDecoderMachine.phaseLabel phase) =
      certificateDecoderLabel (Λ := Λ) phase := by cases phase <;> rfl
@[simp] theorem certificateDecoderLabelEquiv_success :
    certificateDecoderLabelEquiv (OpenDecoderMachine.resultLabel .success) = dispatchLabel (Λ := Λ) := rfl
@[simp] theorem certificateDecoderLabelEquiv_failure :
    certificateDecoderLabelEquiv (OpenDecoderMachine.resultLabel .failure) = rejectLabel (Λ := Λ) := rfl
@[simp] theorem input_success_is_certificate_scan :
    inputLabelEquiv (InputParserMachine.resultLabel .success) = certificateDecoderLabel (Λ := Λ) .scan := rfl
@[simp] theorem input_failure_is_reject :
    inputLabelEquiv (InputParserMachine.resultLabel .failure) = rejectLabel (Λ := Λ) := rfl

/-- Ownership includes certificate scan at the old Input success label. -/
def OwnedPartition : LabelPartition Λ → Prop
  | .inl _ => True
  | .inr (.inl .success) => True
  | .inr (.inl .failure) => False
  | .inr (.inr (.inl _)) => True
  | .inr (.inr (.inr (.inl _))) => True
  | .inr (.inr (.inr (.inr (.inl _)))) => True
  | .inr (.inr (.inr (.inr (.inr _)))) => False

def Owned : Option (Label Λ) → Prop
  | none => False
  | some label => OwnedPartition (inputPartitionEquiv.symm label)

abbrev OwnedLabels := InputOwned ⊕
  (OpenFramingMachine.Phase ⊕ (OpenDecoderMachine.Phase ⊕ OpenDecoderMachine.Phase))

def ownedPartitionEquiv : OwnedLabels ≃ {label : LabelPartition Λ // OwnedPartition label} where
  toFun
    | .inl owned => ⟨.inl owned, True.intro⟩
    | .inr (.inl phase) => ⟨.inr (.inr (.inl phase)), True.intro⟩
    | .inr (.inr (.inl phase)) => ⟨.inr (.inr (.inr (.inl phase))), True.intro⟩
    | .inr (.inr (.inr .scan)) => ⟨.inr (.inl .success), True.intro⟩
    | .inr (.inr (.inr .emit)) => ⟨.inr (.inr (.inr (.inr (.inl .emit)))), True.intro⟩
    | .inr (.inr (.inr .clear)) => ⟨.inr (.inr (.inr (.inr (.inl .clear)))), True.intro⟩
  invFun
    | ⟨.inl owned, _⟩ => .inl owned
    | ⟨.inr (.inl .success), _⟩ => .inr (.inr (.inr .scan))
    | ⟨.inr (.inl .failure), bad⟩ => False.elim bad
    | ⟨.inr (.inr (.inl phase)), _⟩ => .inr (.inl phase)
    | ⟨.inr (.inr (.inr (.inl phase))), _⟩ => .inr (.inr (.inl phase))
    | ⟨.inr (.inr (.inr (.inr (.inl tail)))), _⟩ => .inr (.inr (.inr (tailPhase tail)))
    | ⟨.inr (.inr (.inr (.inr (.inr _)))), bad⟩ => False.elim bad
  left_inv label := by
    cases label with
    | inl owned => rfl
    | inr rest => cases rest with
      | inl phase => rfl
      | inr rest => cases rest with
        | inl phase => rfl
        | inr phase => cases phase <;> rfl
  right_inv label := by
    rcases label with ⟨label, owned⟩
    cases label with
    | inl input => rfl
    | inr rest => cases rest with
      | inl result => cases result with
        | success => rfl
        | failure => cases owned
      | inr extra => cases extra with
        | inl phase => rfl
        | inr rest => cases rest with
          | inl phase => rfl
          | inr rest => cases rest with
            | inl tail => cases tail <;> rfl
            | inr rest => cases owned

def ownedTransportEquiv : {label : LabelPartition Λ // OwnedPartition label} ≃
    {label : Label Λ // Owned (some label)} where
  toFun label := ⟨inputPartitionEquiv label.1, by
    change OwnedPartition (inputPartitionEquiv.symm (inputPartitionEquiv label.1))
    simpa only [Equiv.symm_apply_apply] using label.2⟩
  invFun label := ⟨inputPartitionEquiv.symm label.1, label.2⟩
  left_inv label := Subtype.ext (inputPartitionEquiv.symm_apply_apply label.1)
  right_inv label := Subtype.ext (inputPartitionEquiv.apply_symm_apply label.1)

def ownedLabelEquiv : OwnedLabels ≃ {label : Label Λ // Owned (some label)} :=
  ownedPartitionEquiv.trans ownedTransportEquiv

instance ownedFintype : Fintype {label : Label Λ // Owned (some label)} :=
  Fintype.ofEquiv OwnedLabels ownedLabelEquiv

theorem owned_input (label : InputOwned) : Owned (some (inputOwnedLabel (Λ := Λ) label)) := by
  change OwnedPartition (inputPartitionEquiv.symm (inputPartitionEquiv (.inl label)))
  simp only [Equiv.symm_apply_apply, OwnedPartition]

theorem input_fullOwned_owned (label : Label Λ) (owned : InputParserMachine.FullOwned (some label)) :
    Owned (some label) := by
  obtain ⟨label, rfl⟩ := (inputOwnedLabel_image label).mpr owned
  exact owned_input label

@[simp] theorem owned_framer (phase : OpenFramingMachine.Phase) :
    Owned (some (framerLabel (Λ := Λ) phase)) := True.intro
@[simp] theorem owned_inputDecoder (phase : OpenDecoderMachine.Phase) :
    Owned (some (inputDecoderLabel (Λ := Λ) phase)) := True.intro
@[simp] theorem owned_certificateDecoder (phase : OpenDecoderMachine.Phase) :
    Owned (some (certificateDecoderLabel (Λ := Λ) phase)) := by cases phase <;> trivial
@[simp] theorem not_owned_dispatch : ¬ Owned (some (dispatchLabel (Λ := Λ))) := id
@[simp] theorem not_owned_reject : ¬ Owned (some (rejectLabel (Λ := Λ))) := id
@[simp] theorem not_owned_caller (label : Λ) : ¬ Owned (some (callerLabel label)) := id

@[simp] theorem inputStackEquiv_protected (k : K) :
    inputStackEquiv (InputParserMachine.protectedStack (.inr k)) = .inr k := rfl
@[simp] theorem framerStackEquiv_protected (k : K) :
    framerStackEquiv (.inr (.inr k)) = .inr k := rfl
@[simp] theorem decoderStackEquiv_protected (call : DecoderCall) (k : K) :
    decoderStackEquiv call (.inr (.inr k)) = .inr k := rfl

theorem localStack_card : Fintype.card LocalStack = 14 := by decide
theorem inputProtected_card : Fintype.card InputProtected = 7 := by decide
theorem framerProtected_card : Fintype.card FramerProtected = 9 := by decide
theorem decoderProtected_card : Fintype.card DecoderProtected = 11 := by decide
theorem inputOwned_card : Fintype.card InputOwned = 25 := by decide
theorem inputAfterEntry_card : Fintype.card InputAfterEntry = 24 := by decide
theorem decoderTail_card : Fintype.card DecoderTail = 2 := by decide
theorem framerPhase_card : Fintype.card OpenFramingMachine.Phase = 5 := by decide
theorem decoderPhase_card : Fintype.card OpenDecoderMachine.Phase = 3 := by decide

theorem stackId_card [Fintype K] : Fintype.card (StackId K) = 14 + Fintype.card K := by
  rw [Fintype.card_sum, localStack_card]

theorem extraLabel_card [Fintype Λ] : Fintype.card (ExtraLabel Λ) = 11 + Fintype.card Λ := by
  simp only [Fintype.card_sum, Fintype.card_unit, framerPhase_card, decoderPhase_card, decoderTail_card]
  omega

theorem label_card [Fintype Λ] : Fintype.card (Label Λ) = 38 + Fintype.card Λ := by
  rw [InputParserMachine.label_card, extraLabel_card]
  omega

theorem registers_card [Fintype R] : Fintype.card (Registers R) = 46818 * Fintype.card R := by
  change Fintype.card (InputParserMachine.Registers (OpenDecoderMachine.Temporaries × R)) = _
  rw [InputParserMachine.registers_card, Fintype.card_prod, OpenDecoderMachine.card_temporaries]
  omega

theorem remainingDecoderFields_card : Fintype.card RemainingDecoderFields = 459 := by
  simp [RemainingDecoderFields]

theorem framerRegisterCaller_card [Fintype R] :
    Fintype.card (FramerRegisterCaller R) = 15606 * Fintype.card R := by
  change Fintype.card (InputParserMachine.Registers (RemainingDecoderFields × R)) = _
  rw [InputParserMachine.registers_card, Fintype.card_prod, remainingDecoderFields_card]
  omega

theorem decoderRegisterCaller_card [Fintype R] :
    Fintype.card (DecoderRegisterCaller R) = 34 * Fintype.card R :=
  InputParserMachine.registers_card

theorem framerCaller_card [Fintype Λ] : Fintype.card (FramerCaller Λ) = 31 + Fintype.card Λ := by
  rw [Fintype.card_sum, inputOwned_card, Fintype.card_sum, decoderTail_card,
    Fintype.card_sum, decoderPhase_card, Fintype.card_sum, Fintype.card_unit]
  omega

theorem inputDecoderCaller_card [Fintype Λ] :
    Fintype.card (InputDecoderCaller Λ) = 33 + Fintype.card Λ := by
  rw [Fintype.card_sum, framerPhase_card, Fintype.card_sum, inputAfterEntry_card,
    Fintype.card_sum, decoderPhase_card, Fintype.card_sum, Fintype.card_unit]
  omega

theorem certificateDecoderCaller_card [Fintype Λ] :
    Fintype.card (CertificateDecoderCaller Λ) = 33 + Fintype.card Λ := by
  rw [Fintype.card_sum, inputOwned_card, Fintype.card_sum, framerPhase_card,
    Fintype.card_sum, decoderPhase_card]
  omega

theorem ownedLabels_card : Fintype.card OwnedLabels = 36 := by decide

/-- Exactly the 36 actual owned labels, even when the external label type is infinite. -/
theorem owned_card : Fintype.card {label : Label Λ // Owned (some label)} = 36 := by
  calc
    _ = Fintype.card OwnedLabels := (Fintype.card_congr ownedLabelEquiv).symm
    _ = 36 := ownedLabels_card

end Resources.RotationCertificate.FrontEndMachine

