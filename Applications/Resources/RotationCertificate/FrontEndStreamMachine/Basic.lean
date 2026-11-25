import Applications.Resources.RotationCertificate.StreamMachine
import Mathlib.Algebra.BigOperators.Fin

/-!
# Framed verifier with physical cleanup and Boolean output

The complete FrontEnd and Stream programs share sixteen physical stores. Four
new result joins are paid activations. The cleaner drains a fixed suffix of
those stores, and the emitter pushes its saved answer before resetting and
halting. All configuration evaluators and resource functions are proof-side.
Correspondence: the complete requirements15 controller specification.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.RotationCertificate.FrontEndStreamMachine
open Search.SharedTree (Branch)
open Resources.BinaryCounter (Bits)

abbrev StackId (K : Type) := FrontEndMachine.StackId (StreamMachine.NewBranchStores ⊕ K)
abbrev alphabet {K : Type} (Γ : K → Type) :=
  FrontEndMachine.alphabet (StreamMachine.frontEndAddedAlphabet Γ)
abbrev Registers (R : Type) := FrontEndMachine.Registers (Option Branch × R)
abbrev Temporaries := TreeParserMachine.Temporaries ×
  (OpenDecoderMachine.Temporaries × Option Branch)

inductive CleanupPhase
  | clear (index : Fin 16)
  | emit
  deriving DecidableEq

def cleanupPhaseEquiv : Option (Fin 16) ≃ CleanupPhase where
  toFun | none => .emit | some i => .clear i
  invFun | .emit => none | .clear i => some i
  left_inv q := by cases q <;> rfl
  right_inv q := by cases q <;> rfl

instance : Fintype CleanupPhase := Fintype.ofEquiv (Option (Fin 16)) cleanupPhaseEquiv

abbrev Phase := FrontEndMachine.Label Empty ⊕ (StreamMachine.Label Empty ⊕ CleanupPhase)
abbrev Label (Λ : Type) :=
  FrontEndMachine.Label Empty ⊕ (StreamMachine.Label Empty ⊕ (CleanupPhase ⊕ Λ))

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
  bitsReverse : Bits := []
  moveReverse : List Branch := []
  path : List Branch := []
  fuel : Bits := []
  deriving DecidableEq

variable {K Λ R : Type} {Γ : K → Type}

abbrev Statement (Γ : K → Type) (Λ R : Type) :=
  Turing.TM2.Stmt (alphabet Γ) (Label Λ) (Registers R)
abbrev Cfg (Γ : K → Type) (Λ R : Type) :=
  Turing.TM2.Cfg (alphabet Γ) (Label Λ) (Registers R)

def phaseLabel : Phase → Label Λ
  | .inl q => .inl q
  | .inr (.inl q) => .inr (.inl q)
  | .inr (.inr q) => .inr (.inr (.inl q))
def callerLabel (label : Λ) : Label Λ := .inr (.inr (.inr label))
def frontEndPhase (q : FrontEndMachine.OwnedLabels) : Phase :=
  .inl (FrontEndMachine.ownedLabelEquiv (Λ := Empty) q).1
def streamPhase (q : StreamMachine.Phase) : Phase :=
  .inr (.inl (StreamMachine.phaseLabel q))
def rejectPhase : Phase := .inl FrontEndMachine.rejectLabel
def dispatchPhase : Phase := .inl FrontEndMachine.dispatchLabel
def resultPhase (b : Bool) : Phase := .inr (.inl (StreamMachine.resultLabel b))
def clearPhase (i : Fin 16) : Phase := .inr (.inr (.clear i))
def emitPhase : Phase := .inr (.inr .emit)
def clearLabel (i : Fin 16) : Label Λ := phaseLabel (clearPhase i)
def emitLabel : Label Λ := phaseLabel emitPhase

def Owned : Option (Label Λ) → Prop
  | some (.inl _) | some (.inr (.inl _)) | some (.inr (.inr (.inl _))) => True
  | _ => False

@[simp] theorem owned_phase (q : Phase) : Owned (some (phaseLabel (Λ := Λ) q)) := by
  cases q with
  | inl q => trivial
  | inr q => cases q <;> trivial

@[simp] theorem not_owned_none : ¬ Owned (Λ := Λ) none := by simp only [Owned, not_false_eq_true]
@[simp] theorem not_owned_caller (q : Λ) : ¬ Owned (some (callerLabel q)) := by
  simp only [Owned, callerLabel, not_false_eq_true]

abbrev OwnedLabel (Λ : Type) := {label : Label Λ // Owned (some label)}
def ownedLabelEquiv : Phase ≃ OwnedLabel Λ where
  toFun q := ⟨phaseLabel q, owned_phase q⟩
  invFun q := match q with
    | ⟨.inl q, _⟩ => .inl q
    | ⟨.inr (.inl q), _⟩ => .inr (.inl q)
    | ⟨.inr (.inr (.inl q)), _⟩ => .inr (.inr q)
    | ⟨.inr (.inr (.inr _)), h⟩ => False.elim h
  left_inv q := by cases q with
    | inl q => rfl
    | inr q => cases q <;> rfl
  right_inv q := by
    rcases q with ⟨q, h⟩
    cases q with
    | inl q => rfl
    | inr q => cases q with
      | inl q => rfl
      | inr q => cases q with
        | inl q => rfl
        | inr q => exact False.elim h

instance : Fintype (OwnedLabel Λ) := Fintype.ofEquiv Phase ownedLabelEquiv

def user (regs : Registers R) : R := regs.2.2.2
def fullReset (regs : Registers R) : Registers R :=
  ((none, none), BitDecoderMachine.zeroRegisters, (none, user regs))
def answer (regs : Registers R) : Bool := regs.2.1.b0.getD false
def answerRegisters (b : Bool) (regs : Registers R) : Registers R :=
  ((none, none), { BitDecoderMachine.zeroRegisters with b0 := some b }, (none, user regs))
def observeOccupied {α : Type} (regs : Registers R) (head : Option α) : Registers R :=
  (regs.1, { regs.2.1 with b1 := some head.isSome }, regs.2.2)
def occupied (regs : Registers R) : Bool := regs.2.1.b1.getD false

@[simp] theorem user_fullReset (regs : Registers R) : user (fullReset regs) = user regs := rfl
@[simp] theorem fullReset_fullReset (regs : Registers R) : fullReset (fullReset regs) = fullReset regs := rfl
@[simp] theorem fullReset_answerRegisters (b : Bool) (regs : Registers R) :
    fullReset (answerRegisters b regs) = fullReset regs := rfl
@[simp] theorem answer_answerRegisters (b : Bool) (regs : Registers R) :
    answer (answerRegisters b regs) = b := rfl
@[simp] theorem answer_observeOccupied {α : Type} (regs : Registers R) (head : Option α) :
    answer (observeOccupied regs head) = answer regs := rfl
@[simp] theorem occupied_observeOccupied {α : Type} (regs : Registers R) (head : Option α) :
    occupied (observeOccupied regs head) = head.isSome := rfl
@[simp] theorem fullReset_observeOccupied {α : Type} (regs : Registers R) (head : Option α) :
    fullReset (observeOccupied regs head) = fullReset regs := rfl

def frontEndData (D : LocalData) : FrontEndMachine.LocalData where
  framedRaw := D.framedRaw
  frameFirstReverse := D.frameFirstReverse
  frameCertReverse := D.frameCertReverse
  inputBits := D.inputBits
  certificateBits := D.certificateBits
  inputRaw := D.inputRaw
  decodeReverse := D.decodeReverse
  certificateWord := D.certificateWord
  sourceTree := D.sourceTree
  targetTree := D.targetTree
  treeReverse := D.treeReverse
  pending := D.pending
  fuel := D.fuel
  bitsReverse := D.bitsReverse

def withFrontEnd (D : LocalData) (E : FrontEndMachine.LocalData) : LocalData where
  framedRaw := E.framedRaw
  frameFirstReverse := E.frameFirstReverse
  frameCertReverse := E.frameCertReverse
  inputBits := E.inputBits
  certificateBits := E.certificateBits
  inputRaw := E.inputRaw
  decodeReverse := E.decodeReverse
  certificateWord := E.certificateWord
  sourceTree := E.sourceTree
  targetTree := E.targetTree
  treeReverse := E.treeReverse
  pending := E.pending
  bitsReverse := E.bitsReverse
  moveReverse := D.moveReverse
  path := D.path
  fuel := E.fuel

def streamData (D : LocalData) : StreamMachine.LocalData where
  certificate := D.certificateWord
  moveReverse := D.moveReverse
  path := D.path
  source := D.sourceTree
  saved := D.treeReverse
  scratch := D.decodeReverse
  units := D.pending
  fuel := D.fuel
  target := D.targetTree

def withStream (D : LocalData) (E : StreamMachine.LocalData) : LocalData :=
  { D with
    certificateWord := E.certificate
    moveReverse := E.moveReverse
    path := E.path
    sourceTree := E.source
    treeReverse := E.saved
    decodeReverse := E.scratch
    pending := E.units
    fuel := E.fuel
    targetTree := E.target }

def frontEndContext (D : LocalData) (ctx : ∀ k, List (Γ k)) :
    ∀ k, List (StreamMachine.frontEndAddedAlphabet Γ k) :=
  StreamMachine.frontEndAddedContext D.moveReverse D.path ctx

def streamContext (D : LocalData) (ctx : ∀ k, List (Γ k)) :
    ∀ k, List (StreamMachine.frontEndProtectedAlphabet Γ k)
  | .inl .framedRaw => D.framedRaw
  | .inl .frameFirstReverse => D.frameFirstReverse
  | .inl .frameCertReverse => D.frameCertReverse
  | .inl .inputBits => D.inputBits
  | .inl .certificateBits => D.certificateBits
  | .inl .inputRaw => D.inputRaw
  | .inl .bitsReverse => D.bitsReverse
  | .inr k => ctx k

def stores (D : LocalData) (ctx : ∀ k, List (Γ k)) : ∀ k, List (alphabet Γ k) :=
  FrontEndMachine.stores (frontEndData D) (frontEndContext D ctx)

def cfg (label : Option (Label Λ)) (regs : Registers R) (D : LocalData)
    (ctx : ∀ k, List (Γ k)) : Cfg Γ Λ R where
  l := label
  var := regs
  stk := stores D ctx

def dataOfCfg (c : Cfg Γ Λ R) : LocalData where
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
  bitsReverse := c.stk (.inl .bitsReverse)
  moveReverse := c.stk (.inr (.inl .moveReverse))
  path := c.stk (.inr (.inl .path))
  fuel := c.stk (.inl .fuel)

def contextOfCfg (c : Cfg Γ Λ R) : ∀ k, List (Γ k) := fun k => c.stk (.inr (.inr k))

theorem cfg_ext {a b : Cfg Γ Λ R} (labels : a.l = b.l) (regs : a.var = b.var)
    (words : a.stk = b.stk) : a = b := by
  cases a
  cases b
  cases labels
  cases regs
  cases words
  rfl

theorem cfg_eta (c : Cfg Γ Λ R) : cfg c.l c.var (dataOfCfg c) (contextOfCfg c) = c := by
  apply cfg_ext
  · rfl
  · rfl
  · funext k
    cases k with
    | inl k => cases k <;> rfl
    | inr k => cases k with
      | inl k => cases k <;> rfl
      | inr k => rfl

@[simp] theorem dataOfCfg_cfg (label : Option (Label Λ)) (regs : Registers R)
    (D : LocalData) (ctx : ∀ k, List (Γ k)) : dataOfCfg (cfg label regs D ctx) = D := by
  cases D
  rfl
@[simp] theorem contextOfCfg_cfg (label : Option (Label Λ)) (regs : Registers R)
    (D : LocalData) (ctx : ∀ k, List (Γ k)) : contextOfCfg (cfg label regs D ctx) = ctx := rfl
@[simp] theorem withFrontEnd_frontEndData (D : LocalData) : withFrontEnd D (frontEndData D) = D := rfl
@[simp] theorem withStream_streamData (D : LocalData) : withStream D (streamData D) = D := rfl

/-- The fixed physical order, with fuel last. -/
def slot (i : Fin 16) : StackId K :=
  match i.val with
  | 0 => .inl .framedRaw
  | 1 => .inl .frameFirstReverse
  | 2 => .inl .frameCertReverse
  | 3 => .inl .inputBits
  | 4 => .inl .certificateBits
  | 5 => .inl .inputRaw
  | 6 => .inl .decodeReverse
  | 7 => .inl .certificateWord
  | 8 => .inl .sourceTree
  | 9 => .inl .targetTree
  | 10 => .inl .treeReverse
  | 11 => .inl .pending
  | 12 => .inl .bitsReverse
  | 13 => .inr (.inl .moveReverse)
  | 14 => .inr (.inl .path)
  | _ => .inl .fuel

def localCells (D : LocalData) : Nat :=
  D.framedRaw.length + D.frameFirstReverse.length + D.frameCertReverse.length +
  D.inputBits.length + D.certificateBits.length + D.inputRaw.length +
  D.decodeReverse.length + D.certificateWord.length + D.sourceTree.length +
  D.targetTree.length + D.treeReverse.length + D.pending.length +
  D.bitsReverse.length + D.moveReverse.length + D.path.length + D.fuel.length

def closeSum {A B C X : Type} (e : B ≃ C ⊕ X) : A ⊕ B ≃ (A ⊕ C) ⊕ X :=
  (Equiv.sumCongr (Equiv.refl A) e).trans (Equiv.sumAssoc A C X).symm

/-- Separate the actual external parameter without dropping any closed label. -/
def frontEndClosedEquiv : FrontEndMachine.Label Λ ≃ FrontEndMachine.Label Empty ⊕ Λ :=
  closeSum (closeSum (closeSum (closeSum (closeSum (closeSum (closeSum
    (closeSum (Equiv.emptySum Empty Λ).symm)))))))

def streamClosedEquiv : StreamMachine.Label Λ ≃ StreamMachine.Label Empty ⊕ Λ :=
  closeSum (closeSum (closeSum (closeSum (Equiv.emptySum Empty Λ).symm)))

def swapHeads (A B C : Type) : A ⊕ (B ⊕ C) ≃ B ⊕ (A ⊕ C) where
  toFun | .inl a => .inr (.inl a) | .inr (.inl b) => .inl b
        | .inr (.inr c) => .inr (.inr c)
  invFun | .inl b => .inr (.inl b) | .inr (.inl a) => .inl a
         | .inr (.inr c) => .inr (.inr c)
  left_inv x := by cases x with
    | inl a => rfl
    | inr x => cases x <;> rfl
  right_inv x := by cases x with
    | inl b => rfl
    | inr x => cases x <;> rfl

abbrev FrontEndCallerLabel (Λ : Type) := StreamMachine.Label Empty ⊕ (CleanupPhase ⊕ Λ)
abbrev StreamCallerLabel (Λ : Type) := FrontEndMachine.Label Empty ⊕ (CleanupPhase ⊕ Λ)

def frontEndLabelEquiv : FrontEndMachine.Label (FrontEndCallerLabel Λ) ≃ Label Λ :=
  frontEndClosedEquiv
def streamLabelEquiv : StreamMachine.Label (StreamCallerLabel Λ) ≃ Label Λ :=
  streamClosedEquiv.trans (swapHeads _ _ _)

def streamStackEquiv : StreamMachine.StackId (StreamMachine.FrontEndProtected ⊕ K) ≃
    StackId K := StreamMachine.frontEndStackEquiv.symm

def streamSymbolEquiv (k : StreamMachine.StackId (StreamMachine.FrontEndProtected ⊕ K)) :
    StreamMachine.alphabet (StreamMachine.frontEndProtectedAlphabet Γ) k ≃
      alphabet Γ (streamStackEquiv k) := by
  cases k with
  | inl k => cases k <;> exact Equiv.refl _
  | inr k => cases k with
    | inl k => cases k <;> exact Equiv.refl _
    | inr k => exact Equiv.refl _

def streamRegisterEquiv : StreamMachine.Registers (StreamMachine.FrontEndDecoderComplement × R) ≃
    Registers R := StreamMachine.frontEndRegisterEquiv.symm

abbrev FrontEndStatement (Γ : K → Type) (Λ R : Type) :=
  FrontEndMachine.Statement (StreamMachine.frontEndAddedAlphabet Γ) (FrontEndCallerLabel Λ)
    (Option Branch × R)
abbrev StreamStatement (Γ : K → Type) (Λ R : Type) :=
  StreamMachine.Statement (StreamMachine.frontEndProtectedAlphabet Γ) (StreamCallerLabel Λ)
    (StreamMachine.FrontEndDecoderComplement × R)
abbrev FrontEndCfg (Γ : K → Type) (Λ R : Type) :=
  FrontEndMachine.Cfg (StreamMachine.frontEndAddedAlphabet Γ) (FrontEndCallerLabel Λ)
    (Option Branch × R)
abbrev StreamCfg (Γ : K → Type) (Λ R : Type) :=
  StreamMachine.Cfg (StreamMachine.frontEndProtectedAlphabet Γ) (StreamCallerLabel Λ)
    (StreamMachine.FrontEndDecoderComplement × R)

def frontEndTranslate (body : FrontEndStatement Γ Λ R) : Statement Γ Λ R :=
  FrontEndMachine.Transport.statement (Equiv.refl _) (fun _ => Equiv.refl _)
    (Equiv.refl _) frontEndLabelEquiv body
def streamTranslate (body : StreamStatement Γ Λ R) : Statement Γ Λ R :=
  FrontEndMachine.Transport.statement streamStackEquiv streamSymbolEquiv
    streamRegisterEquiv streamLabelEquiv body
def frontEndCfg (c : FrontEndCfg Γ Λ R) : Cfg Γ Λ R :=
  FrontEndMachine.Transport.cfg (Equiv.refl _) (fun _ => Equiv.refl _)
    (Equiv.refl _) frontEndLabelEquiv c
def streamCfg (c : StreamCfg Γ Λ R) : Cfg Γ Λ R :=
  FrontEndMachine.Transport.cfg streamStackEquiv streamSymbolEquiv
    streamRegisterEquiv streamLabelEquiv c

def nextClear (i : Fin 16) : Label Λ :=
  if h : i.val + 1 < 16 then clearLabel ⟨i.val + 1, h⟩ else emitLabel

def clearBlock (i : Fin 16) : Statement Γ Λ R :=
  .pop (slot i) (fun regs head => observeOccupied regs head)
    (.branch occupied (.goto (fun _ => clearLabel i)) (.goto (fun _ => nextClear i)))
def emitBlock : Statement Γ Λ R :=
  .push (.inl .fuel) answer (.load fullReset .halt)
def answerBlock (b : Bool) : Statement Γ Λ R :=
  .load (answerRegisters b) (.goto (fun _ => clearLabel 0))
def dispatchBlock : Statement Γ Λ R :=
  .load fullReset (.goto (fun _ => phaseLabel (streamPhase StreamMachine.inspectPhase)))

def frontEndBody (label : FrontEndMachine.Label Empty) : Statement Γ Λ R :=
  frontEndTranslate (FrontEndMachine.program (fun _ => .halt)
    (frontEndClosedEquiv.symm (.inl label)))
def streamBody (label : StreamMachine.Label Empty) : Statement Γ Λ R :=
  streamTranslate (StreamMachine.program (fun _ => .halt)
    (streamClosedEquiv.symm (.inl label)))

/-- Only the four common joins replace component result bodies. -/
def program (caller : Λ → Statement Γ Λ R) : Label Λ → Statement Γ Λ R
  | .inl q =>
      match FrontEndMachine.inputPartitionEquiv.symm q with
      | .inr (.inl .failure) => answerBlock false
      | .inr (.inr (.inr (.inr (.inr (.inl _))))) => dispatchBlock
      | _ => frontEndBody q
  | .inr (.inl q) =>
      match q with
      | .inr (.inr (.inr (.inl b))) => answerBlock b
      | _ => streamBody q
  | .inr (.inr (.inl (.clear i))) => clearBlock i
  | .inr (.inr (.inl .emit)) => emitBlock
  | .inr (.inr (.inr q)) => caller q


/-- Overwrite only the occupancy temporary. -/
def occupancyRegisters (b : Bool) (regs : Registers R) : Registers R :=
  (regs.1, { regs.2.1 with b1 := some b }, regs.2.2)

@[simp] theorem occupancyRegisters_occupancyRegisters (b c : Bool) (regs : Registers R) :
    occupancyRegisters b (occupancyRegisters c regs) = occupancyRegisters b regs := by
  rcases regs with ⟨main, decoder, branch, user⟩
  cases decoder
  rfl
@[simp] theorem answer_occupancyRegisters (b : Bool) (regs : Registers R) :
    answer (occupancyRegisters b regs) = answer regs := rfl
@[simp] theorem fullReset_occupancyRegisters (b : Bool) (regs : Registers R) :
    fullReset (occupancyRegisters b regs) = fullReset regs := rfl

def slotLength (i : Fin 16) (D : LocalData) : Nat :=
  match i.val with
  | 0 => D.framedRaw.length
  | 1 => D.frameFirstReverse.length
  | 2 => D.frameCertReverse.length
  | 3 => D.inputBits.length
  | 4 => D.certificateBits.length
  | 5 => D.inputRaw.length
  | 6 => D.decodeReverse.length
  | 7 => D.certificateWord.length
  | 8 => D.sourceTree.length
  | 9 => D.targetTree.length
  | 10 => D.treeReverse.length
  | 11 => D.pending.length
  | 12 => D.bitsReverse.length
  | 13 => D.moveReverse.length
  | 14 => D.path.length
  | _ => D.fuel.length

def dropData (i : Fin 16) (n : Nat) (D : LocalData) : LocalData :=
  match i.val with
  | 0 => { D with framedRaw := D.framedRaw.drop n }
  | 1 => { D with frameFirstReverse := D.frameFirstReverse.drop n }
  | 2 => { D with frameCertReverse := D.frameCertReverse.drop n }
  | 3 => { D with inputBits := D.inputBits.drop n }
  | 4 => { D with certificateBits := D.certificateBits.drop n }
  | 5 => { D with inputRaw := D.inputRaw.drop n }
  | 6 => { D with decodeReverse := D.decodeReverse.drop n }
  | 7 => { D with certificateWord := D.certificateWord.drop n }
  | 8 => { D with sourceTree := D.sourceTree.drop n }
  | 9 => { D with targetTree := D.targetTree.drop n }
  | 10 => { D with treeReverse := D.treeReverse.drop n }
  | 11 => { D with pending := D.pending.drop n }
  | 12 => { D with bitsReverse := D.bitsReverse.drop n }
  | 13 => { D with moveReverse := D.moveReverse.drop n }
  | 14 => { D with path := D.path.drop n }
  | _ => { D with fuel := D.fuel.drop n }

def emptySlot (i : Fin 16) (D : LocalData) : LocalData := dropData i (slotLength i D) D
def emitData (b : Bool) (D : LocalData) : LocalData := { D with fuel := b :: D.fuel }

def clearSuffix (i : Fin 16) (D : LocalData) : LocalData where
  framedRaw := if i.val ≤ 0 then [] else D.framedRaw
  frameFirstReverse := if i.val ≤ 1 then [] else D.frameFirstReverse
  frameCertReverse := if i.val ≤ 2 then [] else D.frameCertReverse
  inputBits := if i.val ≤ 3 then [] else D.inputBits
  certificateBits := if i.val ≤ 4 then [] else D.certificateBits
  inputRaw := if i.val ≤ 5 then [] else D.inputRaw
  decodeReverse := if i.val ≤ 6 then [] else D.decodeReverse
  certificateWord := if i.val ≤ 7 then [] else D.certificateWord
  sourceTree := if i.val ≤ 8 then [] else D.sourceTree
  targetTree := if i.val ≤ 9 then [] else D.targetTree
  treeReverse := if i.val ≤ 10 then [] else D.treeReverse
  pending := if i.val ≤ 11 then [] else D.pending
  bitsReverse := if i.val ≤ 12 then [] else D.bitsReverse
  moveReverse := if i.val ≤ 13 then [] else D.moveReverse
  path := if i.val ≤ 14 then [] else D.path
  fuel := if i.val ≤ 15 then [] else D.fuel

def suffixCells (i : Fin 16) (D : LocalData) : Nat :=
  (if i.val ≤ 0 then D.framedRaw.length else 0) +
  (if i.val ≤ 1 then D.frameFirstReverse.length else 0) +
  (if i.val ≤ 2 then D.frameCertReverse.length else 0) +
  (if i.val ≤ 3 then D.inputBits.length else 0) +
  (if i.val ≤ 4 then D.certificateBits.length else 0) +
  (if i.val ≤ 5 then D.inputRaw.length else 0) +
  (if i.val ≤ 6 then D.decodeReverse.length else 0) +
  (if i.val ≤ 7 then D.certificateWord.length else 0) +
  (if i.val ≤ 8 then D.sourceTree.length else 0) +
  (if i.val ≤ 9 then D.targetTree.length else 0) +
  (if i.val ≤ 10 then D.treeReverse.length else 0) +
  (if i.val ≤ 11 then D.pending.length else 0) +
  (if i.val ≤ 12 then D.bitsReverse.length else 0) +
  (if i.val ≤ 13 then D.moveReverse.length else 0) +
  (if i.val ≤ 14 then D.path.length else 0) +
  (if i.val ≤ 15 then D.fuel.length else 0)

def prefixCells (i : Fin 16) (D : LocalData) : Nat := localCells D - suffixCells i D
def cleanupSteps (i : Fin 16) (D : LocalData) : Nat := suffixCells i D + (16 - i.val) + 1
def cleanupData (i : Fin 16) (b : Bool) (D : LocalData) : LocalData := emitData b (clearSuffix i D)
def drainRegisters (regs : Registers R) (n : Nat) : Registers R :=
  if n = 0 then regs else occupancyRegisters true regs

@[simp] theorem dropData_zero (i : Fin 16) (D : LocalData) : dropData i 0 D = D := by
  fin_cases i <;> rfl

theorem dropData_add (i : Fin 16) (n m : Nat) (D : LocalData) :
    dropData i m (dropData i n D) = dropData i (n + m) D := by
  fin_cases i <;> simp only [dropData, List.drop_drop]

theorem slotLength_dropData (i : Fin 16) (n : Nat) (D : LocalData) :
    slotLength i (dropData i n D) = slotLength i D - n := by
  fin_cases i <;> simp only [slotLength, dropData, List.length_drop]

@[simp] theorem slotLength_emptySlot (i : Fin 16) (D : LocalData) :
    slotLength i (emptySlot i D) = 0 := by
  rw [emptySlot, slotLength_dropData, Nat.sub_self]

@[simp] theorem dropData_one_emptySlot (i : Fin 16) (D : LocalData) :
    dropData i 1 (emptySlot i D) = emptySlot i D := by
  fin_cases i <;> simp [emptySlot, dropData, slotLength]

variable [DecidableEq K]

def step (caller : Λ → Statement Γ Λ R) : Cfg Γ Λ R → Option (Cfg Γ Λ R) :=
  Turing.TM2.step (program caller)
def next (caller : Λ → Statement Γ Λ R) (c : Option (Cfg Γ Λ R)) : Option (Cfg Γ Λ R) :=
  c.bind (step caller)

omit [DecidableEq K] in
@[simp] theorem program_clear (caller : Λ → Statement Γ Λ R) (i : Fin 16) :
    program caller (clearLabel i) = clearBlock i := rfl
omit [DecidableEq K] in
@[simp] theorem program_emit (caller : Λ → Statement Γ Λ R) :
    program caller emitLabel = emitBlock := rfl
omit [DecidableEq K] in
@[simp] theorem program_reject (caller : Λ → Statement Γ Λ R) :
    program caller (phaseLabel rejectPhase) = answerBlock false := rfl
omit [DecidableEq K] in
@[simp] theorem program_dispatch (caller : Λ → Statement Γ Λ R) :
    program caller (phaseLabel dispatchPhase) = dispatchBlock := rfl
omit [DecidableEq K] in
@[simp] theorem program_result (caller : Λ → Statement Γ Λ R) (b : Bool) :
    program caller (phaseLabel (resultPhase b)) = answerBlock b := rfl
omit [DecidableEq K] in
@[simp] theorem program_caller (caller : Λ → Statement Γ Λ R) (q : Λ) :
    program caller (callerLabel q) = caller q := rfl

@[simp] theorem step_none (caller : Λ → Statement Γ Λ R) (regs : Registers R)
    (D : LocalData) (ctx : ∀ k, List (Γ k)) : step caller (cfg none regs D ctx) = none := rfl
@[simp] theorem next_none (caller : Λ → Statement Γ Λ R) : next caller none = none := rfl

variable (caller : Λ → Statement Γ Λ R)

@[simp] theorem next_some (c : Cfg Γ Λ R) : next caller (some c) = step caller c := rfl

theorem iterate_step (n : Nat) (before after : Cfg Γ Λ R)
    (transition : step caller before = some after) :
    (next caller)^[n + 1] (some before) = (next caller)^[n] (some after) := by
  rw [Function.iterate_succ_apply, next_some, transition]

def LocalStep (before after : Cfg Γ Λ R) : Prop :=
  Owned before.l ∧ step caller before = some after

inductive LocalRun : Nat → Cfg Γ Λ R → Cfg Γ Λ R → Prop
  | refl (c) : LocalRun 0 c c
  | cons {n before middle after} (head : LocalStep caller before middle)
      (tail : LocalRun n middle after) : LocalRun (n + 1) before after

theorem LocalRun.single {before after : Cfg Γ Λ R}
    (transition : LocalStep caller before after) : LocalRun caller 1 before after :=
  .cons transition (.refl after)

theorem phase_step_localRun {q : Phase} {D : LocalData} {regs : Registers R}
    {ctx : ∀ k, List (Γ k)} {after : Cfg Γ Λ R}
    (executed : step caller (cfg (some (phaseLabel q)) regs D ctx) = some after) :
    LocalRun caller 1 (cfg (some (phaseLabel q)) regs D ctx) after :=
  LocalRun.single caller ⟨owned_phase q, executed⟩

theorem LocalRun.head {n : Nat} {a b : Cfg Γ Λ R}
    (run : LocalRun caller n a b) (positive : 0 < n) :
    ∃ middle, LocalStep caller a middle := by
  cases run with
  | refl => omega
  | cons first tail => exact ⟨_, first⟩

theorem LocalRun.trans {m n : Nat} {a b c : Cfg Γ Λ R}
    (first : LocalRun caller m a b) (second : LocalRun caller n b c) :
    LocalRun caller (m + n) a c := by
  induction first with
  | refl => simpa only [Nat.zero_add] using second
  | @cons k before middle after head tail ih =>
      simpa only [show k + 1 + n = k + n + 1 by omega] using
        LocalRun.cons head (ih second)

theorem LocalRun.iterate {n : Nat} {a b : Cfg Γ Λ R} (run : LocalRun caller n a b) :
    (next caller)^[n] (some a) = some b := by
  induction run with
  | refl => rfl
  | @cons n before middle after head tail ih =>
      rw [iterate_step caller n before middle head.2]
      exact ih

theorem LocalRun.reaches {n : Nat} {a b : Cfg Γ Λ R} (run : LocalRun caller n a b) :
    Relation.ReflTransGen (LocalStep caller) a b := by
  induction run with
  | refl => exact .refl
  | cons head tail ih => exact (Relation.ReflTransGen.single head).trans ih

theorem LocalRun.owned_prefix {n : Nat} {a b : Cfg Γ Λ R}
    (run : LocalRun caller n a b) (j : Nat) (strict : j < n) :
    ∃ reached, (next caller)^[j] (some a) = some reached ∧ Owned reached.l := by
  induction run generalizing j with
  | refl => omega
  | @cons n before middle after head tail ih =>
      cases j with
      | zero => exact ⟨before, rfl, head.1⟩
      | succ j =>
          obtain ⟨reached, executed, owned⟩ := ih j (by omega)
          exact ⟨reached, (iterate_step caller j before middle head.2).trans executed, owned⟩

theorem LocalRun.of_iterate {n : Nat} {a b : Cfg Γ Λ R}
    (executed : (next caller)^[n] (some a) = some b)
    (earlier : ∀ j, j < n → ∃ reached,
      (next caller)^[j] (some a) = some reached ∧ Owned reached.l) :
    LocalRun caller n a b := by
  induction n generalizing b with
  | zero =>
      have same : a = b := Option.some.inj executed
      subst b
      exact .refl a
  | succ n ih =>
      obtain ⟨middle, arrived, owned⟩ := earlier n (by omega)
      have first := ih arrived (fun j strict => earlier j (by omega))
      have last : step caller middle = some b := by
        simpa only [Function.iterate_succ_apply', arrived, next_some] using executed
      exact LocalRun.trans caller first (LocalRun.single caller ⟨owned, last⟩)

/-- Determinism and strict ownership fix the first live handoff independently of any rank. -/
theorem LocalRun.first_unique {n m : Nat} {a b c : Cfg Γ Λ R}
    (first : LocalRun caller n a b) (second : LocalRun caller m a c)
    (bReturn : ¬ Owned b.l) (cReturn : ¬ Owned c.l) : n = m ∧ b = c := by
  induction first generalizing m c with
  | refl a =>
      cases second with
      | refl => exact ⟨rfl, rfl⟩
      | cons head tail => exact False.elim (bReturn head.1)
  | @cons n before middle after head tail ih =>
      cases second with
      | refl => exact False.elim (cReturn head.1)
      | @cons m _ other finish otherHead otherTail =>
          have same : middle = other := Option.some.inj (head.2.symm.trans otherHead.2)
          subst other
          obtain ⟨count, endpoint⟩ := ih otherTail bReturn cReturn
          exact ⟨congrArg (fun k => k + 1) count, endpoint⟩


theorem reject_step (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel rejectPhase)) regs D ctx) =
      some (cfg (some (clearLabel 0)) (answerRegisters false regs) D ctx) := rfl

theorem dispatch_step (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel dispatchPhase)) regs D ctx) =
      some (cfg (some (phaseLabel (streamPhase StreamMachine.inspectPhase)))
        (fullReset regs) D ctx) := rfl

theorem result_step (b : Bool) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel (resultPhase b))) regs D ctx) =
      some (cfg (some (clearLabel 0)) (answerRegisters b regs) D ctx) := rfl

omit caller in
theorem stores_emitData (b : Bool) (D : LocalData) (ctx : ∀ k, List (Γ k)) :
    stores (emitData b D) ctx = Function.update (stores D ctx) (.inl .fuel) (b :: D.fuel) := by
  funext k
  cases k with
  | inl k => cases k <;> rfl
  | inr k => cases k with
    | inl k => cases k <;> rfl
    | inr k => rfl

theorem emit_step (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some emitLabel) regs D ctx) =
      some (cfg none (fullReset regs) (emitData (answer regs) D) ctx) := by
  simp only [step, cfg, Turing.TM2.step, program_emit, emitBlock, Turing.TM2.stepAux]
  congr 1
  exact cfg_ext rfl rfl (stores_emitData (answer regs) D ctx).symm

omit caller in
private theorem stores_dropData_one_0 (D : LocalData) (ctx : ∀ k, List (Γ k)) :
    stores (dropData 0 1 D) ctx =
      Function.update (stores D ctx) (slot 0) ((stores D ctx (slot 0)).tail) := by
  funext k
  cases k with
  | inl k =>
      cases k <;> try rfl
      exact List.drop_one
  | inr k => cases k with
    | inl k => cases k <;> rfl
    | inr k => rfl

omit caller in
private theorem stores_dropData_one_1 (D : LocalData) (ctx : ∀ k, List (Γ k)) :
    stores (dropData 1 1 D) ctx =
      Function.update (stores D ctx) (slot 1) ((stores D ctx (slot 1)).tail) := by
  funext k
  cases k with
  | inl k =>
      cases k <;> try rfl
      exact List.drop_one
  | inr k => cases k with
    | inl k => cases k <;> rfl
    | inr k => rfl

omit caller in
private theorem stores_dropData_one_2 (D : LocalData) (ctx : ∀ k, List (Γ k)) :
    stores (dropData 2 1 D) ctx =
      Function.update (stores D ctx) (slot 2) ((stores D ctx (slot 2)).tail) := by
  funext k
  cases k with
  | inl k =>
      cases k <;> try rfl
      exact List.drop_one
  | inr k => cases k with
    | inl k => cases k <;> rfl
    | inr k => rfl

omit caller in
private theorem stores_dropData_one_3 (D : LocalData) (ctx : ∀ k, List (Γ k)) :
    stores (dropData 3 1 D) ctx =
      Function.update (stores D ctx) (slot 3) ((stores D ctx (slot 3)).tail) := by
  funext k
  cases k with
  | inl k =>
      cases k <;> try rfl
      exact List.drop_one
  | inr k => cases k with
    | inl k => cases k <;> rfl
    | inr k => rfl

omit caller in
private theorem stores_dropData_one_4 (D : LocalData) (ctx : ∀ k, List (Γ k)) :
    stores (dropData 4 1 D) ctx =
      Function.update (stores D ctx) (slot 4) ((stores D ctx (slot 4)).tail) := by
  funext k
  cases k with
  | inl k =>
      cases k <;> try rfl
      exact List.drop_one
  | inr k => cases k with
    | inl k => cases k <;> rfl
    | inr k => rfl

omit caller in
private theorem stores_dropData_one_5 (D : LocalData) (ctx : ∀ k, List (Γ k)) :
    stores (dropData 5 1 D) ctx =
      Function.update (stores D ctx) (slot 5) ((stores D ctx (slot 5)).tail) := by
  funext k
  cases k with
  | inl k =>
      cases k <;> try rfl
      exact List.drop_one
  | inr k => cases k with
    | inl k => cases k <;> rfl
    | inr k => rfl

omit caller in
private theorem stores_dropData_one_6 (D : LocalData) (ctx : ∀ k, List (Γ k)) :
    stores (dropData 6 1 D) ctx =
      Function.update (stores D ctx) (slot 6) ((stores D ctx (slot 6)).tail) := by
  funext k
  cases k with
  | inl k =>
      cases k <;> try rfl
      exact List.drop_one
  | inr k => cases k with
    | inl k => cases k <;> rfl
    | inr k => rfl

omit caller in
private theorem stores_dropData_one_7 (D : LocalData) (ctx : ∀ k, List (Γ k)) :
    stores (dropData 7 1 D) ctx =
      Function.update (stores D ctx) (slot 7) ((stores D ctx (slot 7)).tail) := by
  funext k
  cases k with
  | inl k =>
      cases k <;> try rfl
      exact List.drop_one
  | inr k => cases k with
    | inl k => cases k <;> rfl
    | inr k => rfl

omit caller in
private theorem stores_dropData_one_8 (D : LocalData) (ctx : ∀ k, List (Γ k)) :
    stores (dropData 8 1 D) ctx =
      Function.update (stores D ctx) (slot 8) ((stores D ctx (slot 8)).tail) := by
  funext k
  cases k with
  | inl k =>
      cases k <;> try rfl
      exact List.drop_one
  | inr k => cases k with
    | inl k => cases k <;> rfl
    | inr k => rfl

omit caller in
private theorem stores_dropData_one_9 (D : LocalData) (ctx : ∀ k, List (Γ k)) :
    stores (dropData 9 1 D) ctx =
      Function.update (stores D ctx) (slot 9) ((stores D ctx (slot 9)).tail) := by
  funext k
  cases k with
  | inl k =>
      cases k <;> try rfl
      exact List.drop_one
  | inr k => cases k with
    | inl k => cases k <;> rfl
    | inr k => rfl

omit caller in
private theorem stores_dropData_one_10 (D : LocalData) (ctx : ∀ k, List (Γ k)) :
    stores (dropData 10 1 D) ctx =
      Function.update (stores D ctx) (slot 10) ((stores D ctx (slot 10)).tail) := by
  funext k
  cases k with
  | inl k =>
      cases k <;> try rfl
      exact List.drop_one
  | inr k => cases k with
    | inl k => cases k <;> rfl
    | inr k => rfl

omit caller in
private theorem stores_dropData_one_11 (D : LocalData) (ctx : ∀ k, List (Γ k)) :
    stores (dropData 11 1 D) ctx =
      Function.update (stores D ctx) (slot 11) ((stores D ctx (slot 11)).tail) := by
  funext k
  cases k with
  | inl k =>
      cases k <;> try rfl
      exact List.drop_one
  | inr k => cases k with
    | inl k => cases k <;> rfl
    | inr k => rfl

omit caller in
private theorem stores_dropData_one_12 (D : LocalData) (ctx : ∀ k, List (Γ k)) :
    stores (dropData 12 1 D) ctx =
      Function.update (stores D ctx) (slot 12) ((stores D ctx (slot 12)).tail) := by
  funext k
  cases k with
  | inl k =>
      cases k <;> try rfl
      exact List.drop_one
  | inr k => cases k with
    | inl k => cases k <;> rfl
    | inr k => rfl

omit caller in
private theorem stores_dropData_one_13 (D : LocalData) (ctx : ∀ k, List (Γ k)) :
    stores (dropData 13 1 D) ctx =
      Function.update (stores D ctx) (slot 13) ((stores D ctx (slot 13)).tail) := by
  funext k
  cases k with
  | inl k => cases k <;> rfl
  | inr k => cases k with
    | inl k =>
        cases k <;> try rfl
        exact List.drop_one
    | inr k => rfl

omit caller in
private theorem stores_dropData_one_14 (D : LocalData) (ctx : ∀ k, List (Γ k)) :
    stores (dropData 14 1 D) ctx =
      Function.update (stores D ctx) (slot 14) ((stores D ctx (slot 14)).tail) := by
  funext k
  cases k with
  | inl k => cases k <;> rfl
  | inr k => cases k with
    | inl k =>
        cases k <;> try rfl
        exact List.drop_one
    | inr k => rfl

omit caller in
private theorem stores_dropData_one_15 (D : LocalData) (ctx : ∀ k, List (Γ k)) :
    stores (dropData 15 1 D) ctx =
      Function.update (stores D ctx) (slot 15) ((stores D ctx (slot 15)).tail) := by
  funext k
  cases k with
  | inl k =>
      cases k <;> try rfl
      exact List.drop_one
  | inr k => cases k with
    | inl k => cases k <;> rfl
    | inr k => rfl

omit caller in
theorem stores_dropData_one (i : Fin 16) (D : LocalData) (ctx : ∀ k, List (Γ k)) :
    stores (dropData i 1 D) ctx =
      Function.update (stores D ctx) (slot i) ((stores D ctx (slot i)).tail) := by
  fin_cases i
  · exact stores_dropData_one_0 D ctx
  · exact stores_dropData_one_1 D ctx
  · exact stores_dropData_one_2 D ctx
  · exact stores_dropData_one_3 D ctx
  · exact stores_dropData_one_4 D ctx
  · exact stores_dropData_one_5 D ctx
  · exact stores_dropData_one_6 D ctx
  · exact stores_dropData_one_7 D ctx
  · exact stores_dropData_one_8 D ctx
  · exact stores_dropData_one_9 D ctx
  · exact stores_dropData_one_10 D ctx
  · exact stores_dropData_one_11 D ctx
  · exact stores_dropData_one_12 D ctx
  · exact stores_dropData_one_13 D ctx
  · exact stores_dropData_one_14 D ctx
  · exact stores_dropData_one_15 D ctx

omit caller [DecidableEq K] in
theorem stores_slot_length (i : Fin 16) (D : LocalData) (ctx : ∀ k, List (Γ k)) :
    (stores D ctx (slot i)).length = slotLength i D := by
  fin_cases i <;> rfl

theorem clear_step (i : Fin 16) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (clearLabel i)) regs D ctx) =
      some (cfg (some (if slotLength i D = 0 then nextClear i else clearLabel i))
        (occupancyRegisters (!(slotLength i D == 0)) regs) (dropData i 1 D) ctx) := by
  have storeLength := stores_slot_length i D ctx
  have storeUpdate := stores_dropData_one i D ctx
  simp only [step, cfg, Turing.TM2.step, program_clear, clearBlock, Turing.TM2.stepAux,
    occupied_observeOccupied]
  cases values : stores D ctx (slot i) with
  | nil =>
      have size : slotLength i D = 0 := by simpa only [values, List.length_nil] using storeLength.symm
      simp only [List.head?_nil, Option.isSome_none, Bool.cond_false,
        observeOccupied, size, beq_self_eq_true, Bool.not_true, ite_true, occupancyRegisters]
      congr 1
      apply cfg_ext
      · rfl
      · rfl
      · simpa only [values] using storeUpdate.symm
  | cons a rest =>
      have size : slotLength i D ≠ 0 := by
        simp only [values, List.length_cons] at storeLength
        omega
      simp only [List.head?_cons, Option.isSome_some, Bool.cond_true, observeOccupied,
        size, beq_eq_false_iff_ne.mpr size, Bool.not_false, ite_false, occupancyRegisters]
      congr 1
      apply cfg_ext
      · rfl
      · rfl
      · simpa only [values] using storeUpdate.symm



omit [DecidableEq K] caller in
theorem card_cleanupPhase : Fintype.card CleanupPhase = 17 := by
  rw [← Fintype.card_congr cleanupPhaseEquiv, Fintype.card_option, Fintype.card_fin]

omit [DecidableEq K] caller in
theorem card_phase : Fintype.card Phase = 96 := by
  have f : Fintype.card (FrontEndMachine.Label Empty) = 38 := by
    simpa only [Fintype.card_empty, Nat.add_zero] using FrontEndMachine.label_card (Λ := Empty)
  have s : Fintype.card (StreamMachine.Label Empty) = 41 := by
    simpa only [Fintype.card_empty, Nat.add_zero] using StreamMachine.card_label (Λ := Empty)
  simp only [Phase, Fintype.card_sum, f, s, card_cleanupPhase]

omit [DecidableEq K] caller in
theorem card_ownedLabel : Fintype.card (OwnedLabel Λ) = 96 := by
  rw [← Fintype.card_congr (ownedLabelEquiv (Λ := Λ)), card_phase]

omit [DecidableEq K] caller in
theorem card_label [Fintype Λ] : Fintype.card (Label Λ) = 96 + Fintype.card Λ := by
  have f : Fintype.card (FrontEndMachine.Label Empty) = 38 := by
    simpa only [Fintype.card_empty, Nat.add_zero] using FrontEndMachine.label_card (Λ := Empty)
  have s : Fintype.card (StreamMachine.Label Empty) = 41 := by
    simpa only [Fintype.card_empty, Nat.add_zero] using StreamMachine.card_label (Λ := Empty)
  simp only [Label, Fintype.card_sum, f, s, card_cleanupPhase]
  omega

omit [DecidableEq K] caller in
theorem card_stackId [Fintype K] : Fintype.card (StackId K) = 16 + Fintype.card K :=
  StreamMachine.frontEnd_source_stack_card

omit [DecidableEq K] caller in
theorem card_registers [Fintype R] : Fintype.card (Registers R) = 140454 * Fintype.card R :=
  StreamMachine.frontEnd_source_register_card

omit [DecidableEq K] caller in
theorem card_temporaries : Fintype.card Temporaries = 140454 := by
  have t : Fintype.card TreeParserMachine.Temporaries = 34 := by decide
  have b : Fintype.card (Option Branch) = 3 := by decide
  simp only [Temporaries, Fintype.card_prod, t, b, OpenDecoderMachine.card_temporaries]

omit [DecidableEq K] caller in
def frontEndView (label : Option (FrontEndMachine.Label (FrontEndCallerLabel Λ)))
    (regs : Registers R) (D : LocalData) (ctx : ∀ k, List (Γ k)) : FrontEndCfg Γ Λ R :=
  FrontEndMachine.cfg label regs (frontEndData D) (frontEndContext D ctx)

omit [DecidableEq K] caller in
def streamView (label : Option (StreamMachine.Label (StreamCallerLabel Λ)))
    (regs : Registers R) (D : LocalData) (ctx : ∀ k, List (Γ k)) : StreamCfg Γ Λ R :=
  StreamMachine.cfg label (StreamMachine.frontEndRegisterEquiv regs)
    (streamData D) (streamContext D ctx)

omit [DecidableEq K] caller in
theorem frontEndCfg_view (label : Option (FrontEndMachine.Label (FrontEndCallerLabel Λ)))
    (regs : Registers R) (D : LocalData) (ctx : ∀ k, List (Γ k)) :
    frontEndCfg (frontEndView label regs D ctx) = cfg (label.map frontEndLabelEquiv) regs D ctx := by
  apply cfg_ext
  · rfl
  · rfl
  · funext k
    exact (FrontEndMachine.Transport.stackEquiv_apply (Equiv.refl _)
      (fun j => Equiv.refl (alphabet Γ j)) (stores D ctx) k).trans (List.map_id _)

omit [DecidableEq K] caller in
theorem streamCfg_view (label : Option (StreamMachine.Label (StreamCallerLabel Λ)))
    (regs : Registers R) (D : LocalData) (ctx : ∀ k, List (Γ k)) :
    streamCfg (streamView label regs D ctx) = cfg (label.map streamLabelEquiv) regs D ctx := by
  apply cfg_ext
  · rfl
  · exact StreamMachine.frontEndRegisterEquiv.symm_apply_apply regs
  · funext k
    obtain ⟨j, rfl⟩ := streamStackEquiv.surjective k
    change FrontEndMachine.Transport.stackEquiv streamStackEquiv streamSymbolEquiv
      (streamView label regs D ctx).stk (streamStackEquiv j) = _
    rw [FrontEndMachine.Transport.stackEquiv_apply]
    cases j with
    | inl j => cases j <;> change List.map id _ = _ <;> exact List.map_id _
    | inr j => cases j with
      | inl j => cases j <;> change List.map id _ = _ <;> exact List.map_id _
      | inr k => change List.map id _ = _; exact List.map_id _

omit [DecidableEq K] in
theorem frontEnd_body_agrees
    (localCaller : FrontEndMachine.External (FrontEndCallerLabel Λ) → FrontEndStatement Γ Λ R)
    (label : FrontEndMachine.Label (FrontEndCallerLabel Λ))
    (owned : FrontEndMachine.Owned (some label)) :
    program caller (frontEndLabelEquiv label) =
      frontEndTranslate (FrontEndMachine.program localCaller label) := by
  rw [← FrontEndMachine.program_caller_independent (fun _ => .halt) localCaller label owned]
  rcases label with pair | (pair | (q | (token | (q | (q | (q | (token | outside)))))))
  · rcases pair with ⟨d, q⟩
    rfl
  · rcases pair with ⟨d, r⟩
    cases d <;> cases r <;> first | rfl | cases owned
  · rfl
  · cases token
    rfl
  · rfl
  · rfl
  · cases q <;> rfl
  · cases owned
  · cases owned

omit [DecidableEq K] in
theorem stream_phase_body
    (localCaller : StreamMachine.External (StreamCallerLabel Λ) → StreamStatement Γ Λ R)
    (q : StreamMachine.Phase) :
    program caller (streamLabelEquiv (StreamMachine.phaseLabel q)) =
      streamTranslate (StreamMachine.program localCaller (StreamMachine.phaseLabel q)) := by
  have independent := StreamMachine.program_phase_independent (fun _ => .halt) localCaller q
  cases q with
  | inl q => exact congrArg streamTranslate independent
  | inr q => cases q with
    | inl q => exact congrArg streamTranslate independent
    | inr q => exact congrArg streamTranslate independent

omit [DecidableEq K] in
theorem stream_body_agrees
    (localCaller : StreamMachine.External (StreamCallerLabel Λ) → StreamStatement Γ Λ R)
    (label : StreamMachine.Label (StreamCallerLabel Λ))
    (owned : StreamMachine.Owned (some label)) :
    program caller (streamLabelEquiv label) =
      streamTranslate (StreamMachine.program localCaller label) := by
  let q := (StreamMachine.ownedLabelEquiv (Λ := StreamCallerLabel Λ)).symm ⟨label, owned⟩
  have same : StreamMachine.phaseLabel q = label :=
    congrArg Subtype.val ((StreamMachine.ownedLabelEquiv (Λ := StreamCallerLabel Λ)).apply_symm_apply ⟨label, owned⟩)
  rw [← same]
  exact stream_phase_body caller localCaller q

omit [DecidableEq K] caller in
theorem owned_frontEndCfg (c : FrontEndCfg Γ Λ R) (h : FrontEndMachine.Owned c.l) :
    Owned (frontEndCfg c).l := by
  rcases c with ⟨l, regs, words⟩
  cases l with
  | none => cases h
  | some label =>
      rcases label with pair | (pair | (q | (token | (q | (q | (q | (token | outside)))))))
      · trivial
      · trivial
      · trivial
      · trivial
      · trivial
      · trivial
      · trivial
      · cases h
      · cases h

omit [DecidableEq K] caller in
theorem owned_streamCfg (c : StreamCfg Γ Λ R) (h : StreamMachine.Owned c.l) :
    Owned (streamCfg c).l := by
  rcases c with ⟨l, regs, words⟩
  cases l with
  | none => cases h
  | some label =>
      rcases label with q | (q | (q | outside))
      · trivial
      · trivial
      · trivial
      · cases h

theorem frontEnd_step_of_step
    (localCaller : FrontEndMachine.External (FrontEndCallerLabel Λ) → FrontEndStatement Γ Λ R)
    (before after : FrontEndCfg Γ Λ R) (owned : FrontEndMachine.Owned before.l)
    (executed : FrontEndMachine.step localCaller before = some after) :
    step caller (frontEndCfg before) = some (frontEndCfg after) := by
  have transported := FrontEndMachine.Transport.step_owned (Equiv.refl _) (fun _ => Equiv.refl _)
    (Equiv.refl _) frontEndLabelEquiv (FrontEndMachine.program localCaller) (program caller)
    FrontEndMachine.Owned (frontEnd_body_agrees caller localCaller) before owned
  change step caller (frontEndCfg before) =
    (FrontEndMachine.step localCaller before).map frontEndCfg at transported
  rw [executed] at transported
  exact transported

theorem stream_step_of_step
    (localCaller : StreamMachine.External (StreamCallerLabel Λ) → StreamStatement Γ Λ R)
    (before after : StreamCfg Γ Λ R) (owned : StreamMachine.Owned before.l)
    (executed : StreamMachine.step localCaller before = some after) :
    step caller (streamCfg before) = some (streamCfg after) := by
  have transported := FrontEndMachine.Transport.step_owned streamStackEquiv streamSymbolEquiv
    streamRegisterEquiv streamLabelEquiv (StreamMachine.program localCaller) (program caller)
    StreamMachine.Owned (stream_body_agrees caller localCaller) before owned
  change step caller (streamCfg before) =
    (StreamMachine.step localCaller before).map streamCfg at transported
  rw [executed] at transported
  exact transported

theorem frontEnd_prefix_transport
    (localCaller : FrontEndMachine.External (FrontEndCallerLabel Λ) → FrontEndStatement Γ Λ R)
    (n : Nat) (start : FrontEndCfg Γ Λ R)
    (earlier : ∀ j, j < n → ∃ reached,
      (FrontEndMachine.next localCaller)^[j] (some start) = some reached ∧ FrontEndMachine.Owned reached.l) :
    (next caller)^[n] (some (frontEndCfg start)) =
      ((FrontEndMachine.next localCaller)^[n] (some start)).map frontEndCfg := by
  exact FrontEndMachine.Transport.iterate_owned (Equiv.refl _) (fun _ => Equiv.refl _)
    (Equiv.refl _) frontEndLabelEquiv (FrontEndMachine.program localCaller) (program caller)
    FrontEndMachine.Owned (frontEnd_body_agrees caller localCaller) n start earlier

theorem stream_prefix_transport
    (localCaller : StreamMachine.External (StreamCallerLabel Λ) → StreamStatement Γ Λ R)
    (n : Nat) (start : StreamCfg Γ Λ R)
    (earlier : ∀ j, j < n → ∃ reached,
      (StreamMachine.next localCaller)^[j] (some start) = some reached ∧ StreamMachine.Owned reached.l) :
    (next caller)^[n] (some (streamCfg start)) =
      ((StreamMachine.next localCaller)^[n] (some start)).map streamCfg := by
  exact FrontEndMachine.Transport.iterate_owned streamStackEquiv streamSymbolEquiv
    streamRegisterEquiv streamLabelEquiv (StreamMachine.program localCaller) (program caller)
    StreamMachine.Owned (stream_body_agrees caller localCaller) n start earlier

theorem stream_localRun
    (localCaller : StreamMachine.External (StreamCallerLabel Λ) → StreamStatement Γ Λ R)
    {n : Nat} {before after : StreamCfg Γ Λ R} (run : StreamMachine.LocalRun localCaller n before after) :
    LocalRun caller n (streamCfg before) (streamCfg after) := by
  induction run with
  | refl => exact .refl _
  | cons head tail ih =>
      exact .cons ⟨owned_streamCfg _ head.1, stream_step_of_step caller localCaller _ _ head.1 head.2⟩ ih


omit caller [DecidableEq K] in
theorem emptySlot_eq_of_zero (i : Fin 16) (D : LocalData) (h : slotLength i D = 0) :
    emptySlot i D = D := by
  rw [emptySlot, h, dropData_zero]

omit caller [DecidableEq K] in
theorem dropData_one_of_zero (i : Fin 16) (D : LocalData) (h : slotLength i D = 0) :
    dropData i 1 D = D := by
  calc
    dropData i 1 D = dropData i 1 (emptySlot i D) := by rw [emptySlot_eq_of_zero i D h]
    _ = emptySlot i D := dropData_one_emptySlot i D
    _ = D := emptySlot_eq_of_zero i D h

theorem clear_step_nil (i : Fin 16) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (empty : slotLength i D = 0) :
    step caller (cfg (some (clearLabel i)) regs D ctx) =
      some (cfg (some (nextClear i)) (occupancyRegisters false regs) D ctx) := by
  simpa only [empty, ite_true, beq_self_eq_true, Bool.not_true, dropData_one_of_zero i D empty]
    using clear_step caller i D regs ctx

theorem clear_step_cons (i : Fin 16) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (nonempty : slotLength i D ≠ 0) :
    step caller (cfg (some (clearLabel i)) regs D ctx) =
      some (cfg (some (clearLabel i)) (occupancyRegisters true regs) (dropData i 1 D) ctx) := by
  simpa only [nonempty, ite_false, beq_eq_false_iff_ne.mpr nonempty, Bool.not_false]
    using clear_step caller i D regs ctx

omit caller [DecidableEq K] in
theorem drainRegisters_succ (regs : Registers R) (n : Nat) :
    drainRegisters regs (n + 1) = occupancyRegisters true (drainRegisters regs n) := by
  cases n with
  | zero => rfl
  | succ n => exact (occupancyRegisters_occupancyRegisters true true regs).symm

omit caller [DecidableEq K] in
theorem occupancyRegisters_drainRegisters (b : Bool) (regs : Registers R) (n : Nat) :
    occupancyRegisters b (drainRegisters regs n) = occupancyRegisters b regs := by
  cases n with
  | zero => rfl
  | succ n => exact occupancyRegisters_occupancyRegisters b true regs

theorem drain_slot_localRun (i : Fin 16) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (n : Nat) (within : n ≤ slotLength i D) :
    LocalRun caller n (cfg (some (clearLabel i)) regs D ctx)
      (cfg (some (clearLabel i)) (drainRegisters regs n) (dropData i n D) ctx) := by
  induction n with
  | zero => simpa only [dropData_zero, drainRegisters, ite_true] using
      (LocalRun.refl (caller := caller) (cfg (some (clearLabel i)) regs D ctx))
  | succ n ih =>
      have first := ih (by omega)
      have nonempty : slotLength i (dropData i n D) ≠ 0 := by
        rw [slotLength_dropData]
        omega
      have last := phase_step_localRun caller
        (clear_step_cons caller i (dropData i n D) (drainRegisters regs n) ctx nonempty)
      simpa only [dropData_add, drainRegisters_succ] using LocalRun.trans caller first last

theorem clear_slot_localRun (i : Fin 16) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (slotLength i D + 1) (cfg (some (clearLabel i)) regs D ctx)
      (cfg (some (nextClear i)) (occupancyRegisters false regs) (emptySlot i D) ctx) := by
  have first := drain_slot_localRun caller i D regs ctx (slotLength i D) (Nat.le_refl _)
  have last := phase_step_localRun caller
    (clear_step_nil caller i (emptySlot i D) (drainRegisters regs (slotLength i D)) ctx
      (slotLength_emptySlot i D))
  simpa only [emptySlot, occupancyRegisters_drainRegisters] using LocalRun.trans caller first last

theorem emit_localRun (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller 1 (cfg (some emitLabel) regs D ctx)
      (cfg none (fullReset regs) (emitData (answer regs) D) ctx) :=
  phase_step_localRun caller (emit_step caller D regs ctx)

omit caller [DecidableEq K] in
theorem nextClear_castSucc (i : Fin 15) :
    nextClear (Λ := Λ) i.castSucc = clearLabel i.succ := by
  have bound : i.castSucc.val + 1 < 16 := Nat.succ_lt_succ i.isLt
  rw [nextClear, dite_eq_left bound]
  rfl

omit caller [DecidableEq K] in
theorem cleanupSteps_castSucc (i : Fin 15) (D : LocalData) :
    cleanupSteps i.castSucc D = slotLength i.castSucc D + 1 +
      cleanupSteps i.succ (emptySlot i.castSucc D) := by
  fin_cases i <;> simp [cleanupSteps, suffixCells, slotLength, emptySlot, dropData] <;> omega

omit caller [DecidableEq K] in
theorem cleanupData_castSucc (i : Fin 15) (b : Bool) (D : LocalData) :
    cleanupData i.succ b (emptySlot i.castSucc D) = cleanupData i.castSucc b D := by
  fin_cases i <;> simp [cleanupData, clearSuffix, emptySlot, dropData, slotLength]

theorem cleanup_localRun (i : Fin 16) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (cleanupSteps i D) (cfg (some (clearLabel i)) regs D ctx)
      (cfg none (fullReset regs) (cleanupData i (answer regs) D) ctx) := by
  induction i using Fin.reverseInduction generalizing D regs with
  | last =>
      have first := clear_slot_localRun caller 15 D regs ctx
      have last := emit_localRun caller (emptySlot 15 D) (occupancyRegisters false regs) ctx
      have run := LocalRun.trans caller first last
      simpa [cleanupSteps, suffixCells, slotLength, nextClear, emptySlot, dropData,
        cleanupData, clearSuffix, emitData] using run
  | cast i ih =>
      have first := clear_slot_localRun caller i.castSucc D regs ctx
      rw [nextClear_castSucc] at first
      have last := ih (emptySlot i.castSucc D) (occupancyRegisters false regs)
      have run := LocalRun.trans caller first last
      rw [← cleanupSteps_castSucc] at run
      simpa only [fullReset_occupancyRegisters, answer_occupancyRegisters,
        cleanupData_castSucc] using run


omit caller [DecidableEq K] in
@[simp] theorem streamData_withStream (D : LocalData) (E : StreamMachine.LocalData) :
    streamData (withStream D E) = E := by cases E; rfl

omit caller [DecidableEq K] in
@[simp] theorem streamContext_withStream (D : LocalData) (E : StreamMachine.LocalData)
    (ctx : ∀ k, List (Γ k)) : streamContext (withStream D E) ctx = streamContext D ctx := rfl

omit caller [DecidableEq K] in
@[simp] theorem streamLabelEquiv_phase (q : StreamMachine.Phase) :
    streamLabelEquiv (StreamMachine.phaseLabel (Λ := StreamCallerLabel Λ) q) =
      phaseLabel (streamPhase q) := by
  cases q with
  | inl q => rfl
  | inr q => cases q <;> rfl

omit caller [DecidableEq K] in
@[simp] theorem streamLabelEquiv_result (b : Bool) :
    streamLabelEquiv (StreamMachine.resultLabel (Λ := StreamCallerLabel Λ) b) =
      phaseLabel (resultPhase b) := rfl

omit caller [DecidableEq K] in
@[simp] theorem frontEndLabelEquiv_dispatch :
    frontEndLabelEquiv (FrontEndMachine.dispatchLabel (Λ := FrontEndCallerLabel Λ)) =
      phaseLabel dispatchPhase := rfl

omit caller [DecidableEq K] in
@[simp] theorem frontEndLabelEquiv_reject :
    frontEndLabelEquiv (FrontEndMachine.rejectLabel (Λ := FrontEndCallerLabel Λ)) =
      phaseLabel rejectPhase := rfl

omit caller [DecidableEq K] in
def streamReset (regs : Registers R) : Registers R :=
  StreamMachine.frontEndRegisterEquiv.symm
    (StreamMachine.resetAll (StreamMachine.frontEndRegisterEquiv regs))

omit caller [DecidableEq K] in
@[simp] theorem frontEndRegisterEquiv_streamReset (regs : Registers R) :
    StreamMachine.frontEndRegisterEquiv (streamReset regs) =
      StreamMachine.resetAll (StreamMachine.frontEndRegisterEquiv regs) :=
  StreamMachine.frontEndRegisterEquiv.apply_symm_apply _

omit caller [DecidableEq K] in
@[simp] theorem fullReset_streamReset (regs : Registers R) :
    fullReset (streamReset regs) = fullReset regs := rfl

omit caller [DecidableEq K] in
@[simp] theorem answerRegisters_streamReset (b : Bool) (regs : Registers R) :
    answerRegisters b (streamReset regs) = answerRegisters b regs := rfl

omit caller [DecidableEq K] in
theorem streamCfg_phaseResult (q : StreamMachine.Phase) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    streamCfg (StreamMachine.phaseResult (Λ := StreamCallerLabel Λ) q
      (StreamMachine.frontEndRegisterEquiv regs) (streamData D) (streamContext D ctx)) =
      cfg (some (phaseLabel (resultPhase (StreamMachine.evaluate q (streamData D)).result)))
        (streamReset regs) (withStream D (StreamMachine.evaluate q (streamData D)).data) ctx := by
  have transported := streamCfg_view (Λ := Λ) (some (StreamMachine.resultLabel (StreamMachine.evaluate q (streamData D)).result))
    (streamReset regs) (withStream D (StreamMachine.evaluate q (streamData D)).data) ctx
  simpa only [streamView, streamData_withStream, streamContext_withStream,
    frontEndRegisterEquiv_streamReset, StreamMachine.phaseResult, StreamMachine.evaluationCfg,
    Option.map_some, streamLabelEquiv_result] using transported

theorem stream_phase_localRun (q : StreamMachine.Phase) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (StreamMachine.phaseSteps q (streamData D))
      (cfg (some (phaseLabel (streamPhase q))) regs D ctx)
      (cfg (some (phaseLabel (resultPhase (StreamMachine.evaluate q (streamData D)).result)))
        (streamReset regs) (withStream D (StreamMachine.evaluate q (streamData D)).data) ctx) := by
  have localRun := StreamMachine.phase_localRun
    (Γ := StreamMachine.frontEndProtectedAlphabet Γ) (Λ := StreamCallerLabel Λ)
    (fun _ => .halt) q (streamData D) (StreamMachine.frontEndRegisterEquiv regs) (streamContext D ctx)
  have transported := stream_localRun caller (fun _ => .halt) localRun
  have start := streamCfg_view (Λ := Λ) (some (StreamMachine.phaseLabel q)) regs D ctx
  simp only [Option.map_some, streamLabelEquiv_phase] at start
  change streamCfg (StreamMachine.cfg (some (StreamMachine.phaseLabel q))
    (StreamMachine.frontEndRegisterEquiv regs) (streamData D) (streamContext D ctx)) = _ at start
  rw [start, streamCfg_phaseResult] at transported
  exact transported

omit caller [DecidableEq K] in
structure Evaluation where
  steps : Nat
  data : LocalData

omit caller [DecidableEq K] in
def addSteps (n : Nat) (E : Evaluation) : Evaluation := { E with steps := n + E.steps }

omit caller [DecidableEq K] in
def answerEvaluation (b : Bool) (D : LocalData) : Evaluation :=
  ⟨1 + cleanupSteps 0 D, cleanupData 0 b D⟩

omit caller [DecidableEq K] in
def streamEvaluation (q : StreamMachine.Phase) (D : LocalData) : Evaluation :=
  let E := StreamMachine.evaluate q (streamData D)
  addSteps E.steps (answerEvaluation E.result (withStream D E.data))

omit caller [DecidableEq K] in
def dispatchEvaluation (D : LocalData) : Evaluation :=
  addSteps 1 (streamEvaluation StreamMachine.inspectPhase D)

omit caller [DecidableEq K] in
def evaluationCfg (regs : Registers R) (E : Evaluation) (ctx : ∀ k, List (Γ k)) : Cfg Γ Λ R :=
  cfg none (fullReset regs) E.data ctx

theorem result_complete_localRun (b : Bool) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (answerEvaluation b D).steps
      (cfg (some (phaseLabel (resultPhase b))) regs D ctx)
      (evaluationCfg regs (answerEvaluation b D) ctx) := by
  have first := phase_step_localRun caller (result_step caller b D regs ctx)
  have last := cleanup_localRun caller 0 D (answerRegisters b regs) ctx
  simpa only [answerEvaluation, evaluationCfg, fullReset_answerRegisters, answer_answerRegisters]
    using LocalRun.trans caller first last

theorem reject_complete_localRun (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (answerEvaluation false D).steps
      (cfg (some (phaseLabel rejectPhase)) regs D ctx)
      (evaluationCfg regs (answerEvaluation false D) ctx) := by
  have first := phase_step_localRun caller (reject_step caller D regs ctx)
  have last := cleanup_localRun caller 0 D (answerRegisters false regs) ctx
  simpa only [answerEvaluation, evaluationCfg, fullReset_answerRegisters, answer_answerRegisters]
    using LocalRun.trans caller first last

theorem stream_complete_localRun (q : StreamMachine.Phase) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (streamEvaluation q D).steps
      (cfg (some (phaseLabel (streamPhase q))) regs D ctx)
      (evaluationCfg regs (streamEvaluation q D) ctx) := by
  have first := stream_phase_localRun caller q D regs ctx
  have last := result_complete_localRun caller (StreamMachine.evaluate q (streamData D)).result
    (withStream D (StreamMachine.evaluate q (streamData D)).data) (streamReset regs) ctx
  simpa only [streamEvaluation, addSteps, StreamMachine.phaseSteps, evaluationCfg, fullReset_streamReset]
    using LocalRun.trans caller first last

theorem dispatch_complete_localRun (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (dispatchEvaluation D).steps
      (cfg (some (phaseLabel dispatchPhase)) regs D ctx)
      (evaluationCfg regs (dispatchEvaluation D) ctx) := by
  have first := phase_step_localRun caller (dispatch_step caller D regs ctx)
  have last := stream_complete_localRun caller StreamMachine.inspectPhase D (fullReset regs) ctx
  simpa only [dispatchEvaluation, addSteps, evaluationCfg, fullReset_fullReset]
    using LocalRun.trans caller first last

/-- Primitive joins have one activation and their immediate, still-owned endpoint. -/
inductive Join | reject | dispatch | result (value : Bool)
  deriving DecidableEq

omit caller [DecidableEq K] in
def joinPhase : Join → Phase
  | .reject => rejectPhase
  | .dispatch => dispatchPhase
  | .result b => resultPhase b

omit caller [DecidableEq K] in
def joinNextCfg (q : Join) (regs : Registers R) (D : LocalData)
    (ctx : ∀ k, List (Γ k)) : Cfg Γ Λ R := match q with
  | .reject => cfg (some (clearLabel 0)) (answerRegisters false regs) D ctx
  | .dispatch => cfg (some (phaseLabel (streamPhase StreamMachine.inspectPhase))) (fullReset regs) D ctx
  | .result b => cfg (some (clearLabel 0)) (answerRegisters b regs) D ctx

theorem join_step (q : Join) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel (joinPhase q))) regs D ctx) = some (joinNextCfg q regs D ctx) := by
  cases q with
  | reject => exact reject_step caller D regs ctx
  | dispatch => exact dispatch_step caller D regs ctx
  | result b => exact result_step caller b D regs ctx

def joinInTime (q : Join) (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller)
      (cfg (some (phaseLabel (joinPhase q))) regs D ctx) (some (joinNextCfg q regs D ctx)) 1 where
  steps := 1
  evals_in_steps := join_step caller q D regs ctx
  steps_le_m := Nat.le_refl _

@[simp] theorem joinInTime_steps (q : Join) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) : (joinInTime caller q D regs ctx).steps = 1 := rfl

def cleanupInTime (i : Fin 16) (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller) (cfg (some (clearLabel i)) regs D ctx)
      (some (cfg none (fullReset regs) (cleanupData i (answer regs) D) ctx)) (cleanupSteps i D) where
  steps := cleanupSteps i D
  evals_in_steps := (cleanup_localRun caller i D regs ctx).iterate caller
  steps_le_m := Nat.le_refl _

@[simp] theorem cleanupInTime_steps (i : Fin 16) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) : (cleanupInTime caller i D regs ctx).steps = cleanupSteps i D := rfl

def emitInTime (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller) (cfg (some emitLabel) regs D ctx)
      (some (cfg none (fullReset regs) (emitData (answer regs) D) ctx)) 1 where
  steps := 1
  evals_in_steps := (emit_localRun caller D regs ctx).iterate caller
  steps_le_m := Nat.le_refl _

@[simp] theorem emitInTime_steps (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) : (emitInTime caller D regs ctx).steps = 1 := rfl


/-- A property of the one actual inclusive prefix, with no chosen alternative state. -/
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

theorem PrefixProperty.mono {P Q : Cfg Γ Λ R → Prop} {start : Cfg Γ Λ R} {ticks : Nat}
    (run : PrefixProperty caller P start ticks) (implies : ∀ c, P c → Q c) :
    PrefixProperty caller Q start ticks := fun n hn reached h => implies reached (run n hn reached h)

theorem drain_slot_iterate (i : Fin 16) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (n : Nat) (within : n ≤ slotLength i D) :
    (next caller)^[n] (some (cfg (some (clearLabel i)) regs D ctx)) =
      some (cfg (some (clearLabel i)) (drainRegisters regs n) (dropData i n D) ctx) :=
  (drain_slot_localRun caller i D regs ctx n within).iterate caller

theorem clear_slot_iterate (i : Fin 16) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    (next caller)^[slotLength i D + 1] (some (cfg (some (clearLabel i)) regs D ctx)) =
      some (cfg (some (nextClear i)) (occupancyRegisters false regs) (emptySlot i D) ctx) :=
  (clear_slot_localRun caller i D regs ctx).iterate caller

theorem cleanup_iterate (i : Fin 16) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    (next caller)^[cleanupSteps i D] (some (cfg (some (clearLabel i)) regs D ctx)) =
      some (cfg none (fullReset regs) (cleanupData i (answer regs) D) ctx) :=
  (cleanup_localRun caller i D regs ctx).iterate caller

omit caller [DecidableEq K] in
theorem localCells_dropData_le (i : Fin 16) (n : Nat) (D : LocalData) :
    localCells (dropData i n D) ≤ localCells D := by
  fin_cases i <;> simp only [dropData, localCells, List.length_drop] <;> omega

omit caller [DecidableEq K] in
theorem localCells_emptySlot_le (i : Fin 16) (D : LocalData) :
    localCells (emptySlot i D) ≤ localCells D := localCells_dropData_le i (slotLength i D) D

omit caller [DecidableEq K] in
theorem prefixCells_add_suffixCells (i : Fin 16) (D : LocalData) :
    prefixCells i D + suffixCells i D = localCells D := by
  fin_cases i <;> simp [prefixCells, suffixCells, localCells]

omit caller [DecidableEq K] in
theorem localCells_clearSuffix (i : Fin 16) (D : LocalData) :
    localCells (clearSuffix i D) = prefixCells i D := by
  fin_cases i <;> simp [clearSuffix, localCells, prefixCells, suffixCells] <;> omega

omit caller [DecidableEq K] in
theorem localCells_emitData (b : Bool) (D : LocalData) :
    localCells (emitData b D) = localCells D + 1 := by
  simp only [localCells, emitData, List.length_cons]
  omega

omit caller [DecidableEq K] in
theorem localCells_cleanupData (i : Fin 16) (b : Bool) (D : LocalData) :
    localCells (cleanupData i b D) = prefixCells i D + 1 := by
  rw [cleanupData, localCells_emitData, localCells_clearSuffix]

omit caller [DecidableEq K] in
theorem prefixCells_castSucc (i : Fin 15) (D : LocalData) :
    prefixCells i.succ (emptySlot i.castSucc D) = prefixCells i.castSucc D := by
  fin_cases i <;> simp [prefixCells, suffixCells, localCells, emptySlot, dropData, slotLength] <;> omega

omit caller [DecidableEq K] in
theorem emptySlot_last_eq_clearSuffix (D : LocalData) : emptySlot 15 D = clearSuffix 15 D := by
  simp [emptySlot, dropData, slotLength, clearSuffix]

omit caller [DecidableEq K] in
/-- Read the finite local slot index without inspecting any stack contents. -/
def slotIndex : StackId K → Option (Fin 16)
  | .inl .framedRaw => some 0
  | .inl .frameFirstReverse => some 1
  | .inl .frameCertReverse => some 2
  | .inl .inputBits => some 3
  | .inl .certificateBits => some 4
  | .inl .inputRaw => some 5
  | .inl .decodeReverse => some 6
  | .inl .certificateWord => some 7
  | .inl .sourceTree => some 8
  | .inl .targetTree => some 9
  | .inl .treeReverse => some 10
  | .inl .pending => some 11
  | .inl .bitsReverse => some 12
  | .inr (.inl .moveReverse) => some 13
  | .inr (.inl .path) => some 14
  | .inl .fuel => some 15
  | .inr (.inr _) => none

omit caller [DecidableEq K] in
@[simp] theorem slotIndex_slot (i : Fin 16) : slotIndex (slot (K := K) i) = some i := by
  fin_cases i <;> rfl

omit caller [DecidableEq K] in
theorem slot_injective : Function.Injective (slot (K := K)) := by
  intro i j same
  have readback := congrArg slotIndex same
  simpa only [slotIndex_slot, Option.some.injEq] using readback

omit caller [DecidableEq K] in
theorem slot_complete (k : StackId K) :
    (∃ i, slot i = k) ∨ ∃ external, k = .inr (.inr external) := by
  cases k with
  | inl k =>
      cases k with
      | framedRaw => exact Or.inl ⟨0, rfl⟩
      | frameFirstReverse => exact Or.inl ⟨1, rfl⟩
      | frameCertReverse => exact Or.inl ⟨2, rfl⟩
      | inputBits => exact Or.inl ⟨3, rfl⟩
      | certificateBits => exact Or.inl ⟨4, rfl⟩
      | inputRaw => exact Or.inl ⟨5, rfl⟩
      | decodeReverse => exact Or.inl ⟨6, rfl⟩
      | certificateWord => exact Or.inl ⟨7, rfl⟩
      | sourceTree => exact Or.inl ⟨8, rfl⟩
      | targetTree => exact Or.inl ⟨9, rfl⟩
      | treeReverse => exact Or.inl ⟨10, rfl⟩
      | pending => exact Or.inl ⟨11, rfl⟩
      | bitsReverse => exact Or.inl ⟨12, rfl⟩
      | fuel => exact Or.inl ⟨15, rfl⟩
  | inr k => cases k with
    | inl k => cases k with
      | moveReverse => exact Or.inl ⟨13, rfl⟩
      | path => exact Or.inl ⟨14, rfl⟩
    | inr k => exact Or.inr ⟨k, rfl⟩

omit caller [DecidableEq K] in
def boundaryData (i j : Fin 16) (D : LocalData) : LocalData where
  framedRaw := if i.val ≤ 0 ∧ 0 < j.val then [] else D.framedRaw
  frameFirstReverse := if i.val ≤ 1 ∧ 1 < j.val then [] else D.frameFirstReverse
  frameCertReverse := if i.val ≤ 2 ∧ 2 < j.val then [] else D.frameCertReverse
  inputBits := if i.val ≤ 3 ∧ 3 < j.val then [] else D.inputBits
  certificateBits := if i.val ≤ 4 ∧ 4 < j.val then [] else D.certificateBits
  inputRaw := if i.val ≤ 5 ∧ 5 < j.val then [] else D.inputRaw
  decodeReverse := if i.val ≤ 6 ∧ 6 < j.val then [] else D.decodeReverse
  certificateWord := if i.val ≤ 7 ∧ 7 < j.val then [] else D.certificateWord
  sourceTree := if i.val ≤ 8 ∧ 8 < j.val then [] else D.sourceTree
  targetTree := if i.val ≤ 9 ∧ 9 < j.val then [] else D.targetTree
  treeReverse := if i.val ≤ 10 ∧ 10 < j.val then [] else D.treeReverse
  pending := if i.val ≤ 11 ∧ 11 < j.val then [] else D.pending
  bitsReverse := if i.val ≤ 12 ∧ 12 < j.val then [] else D.bitsReverse
  moveReverse := if i.val ≤ 13 ∧ 13 < j.val then [] else D.moveReverse
  path := if i.val ≤ 14 ∧ 14 < j.val then [] else D.path
  fuel := if i.val ≤ 15 ∧ 15 < j.val then [] else D.fuel

omit caller [DecidableEq K] in
def boundarySteps (i j : Fin 16) (D : LocalData) : Nat :=
  ∑ k : Fin 16, if i.val ≤ k.val ∧ k.val < j.val then slotLength k D + 1 else 0

omit caller [DecidableEq K] in
def boundaryRegisters (i j : Fin 16) (regs : Registers R) : Registers R :=
  if i = j then regs else occupancyRegisters false regs

omit caller [DecidableEq K] in
@[simp] theorem boundaryData_self (i : Fin 16) (D : LocalData) : boundaryData i i D = D := by
  have impossible (k : Nat) : ¬ (i.val ≤ k ∧ k < i.val) := by omega
  simp only [boundaryData, impossible, ite_false]

omit caller [DecidableEq K] in
@[simp] theorem boundarySteps_self (i : Fin 16) (D : LocalData) : boundarySteps i i D = 0 := by
  apply Finset.sum_eq_zero
  intro k _
  have impossible : ¬ (i.val ≤ k.val ∧ k.val < i.val) := by omega
  simp only [impossible, ite_false]

omit caller [DecidableEq K] in
@[simp] theorem boundaryRegisters_self (i : Fin 16) (regs : Registers R) :
    boundaryRegisters i i regs = regs := by simp only [boundaryRegisters, ite_true]

omit caller [DecidableEq K] in
theorem slotLength_boundaryData (i j k : Fin 16) (D : LocalData) :
    slotLength k (boundaryData i j D) =
      if i.val ≤ k.val ∧ k.val < j.val then 0 else slotLength k D := by
  have length_if {α : Type} (p : Prop) [Decidable p] (word : List α) :
      (if p then [] else word).length = if p then 0 else word.length := by
    split_ifs <;> rfl
  fin_cases k <;> simp [slotLength, boundaryData, length_if]

omit caller [DecidableEq K] in
@[simp] theorem slotLength_boundaryData_target (i j : Fin 16) (D : LocalData) :
    slotLength j (boundaryData i j D) = slotLength j D := by
  rw [slotLength_boundaryData]
  simp only [lt_self_iff_false, and_false, ite_false]

omit caller [DecidableEq K] in
theorem boundaryData_succ (i : Fin 16) (j : Fin 15) (D : LocalData)
    (ordered : i.val ≤ j.val) :
    emptySlot j.castSucc (boundaryData i j.castSucc D) = boundaryData i j.succ D := by
  fin_cases j <;> simp_all [boundaryData, emptySlot, dropData, slotLength]

omit caller [DecidableEq K] in
theorem boundarySteps_succ (i : Fin 16) (j : Fin 15) (D : LocalData)
    (ordered : i.val ≤ j.val) :
    boundarySteps i j.succ D = boundarySteps i j.castSucc D + slotLength j.castSucc D + 1 := by
  have term (k : Fin 16) :
      (if i.val ≤ k.val ∧ k.val < j.succ.val then slotLength k D + 1 else 0) =
      (if i.val ≤ k.val ∧ k.val < j.castSucc.val then slotLength k D + 1 else 0) +
        (if k = j.castSucc then slotLength k D + 1 else 0) := by
    by_cases same : k = j.castSucc
    · subst k
      simp only [Fin.val_succ, Fin.val_castSucc, ordered, Nat.lt_succ_self,
        and_self, ite_true, lt_self_iff_false, and_false, ite_false, Nat.zero_add]
    · have distinct : k.val ≠ j.val := by
        intro values
        apply same
        exact Fin.ext values
      have equivalent : (i.val ≤ k.val ∧ k.val < j.succ.val) ↔
          (i.val ≤ k.val ∧ k.val < j.castSucc.val) := by
        simp only [Fin.val_succ, Fin.val_castSucc]
        omega
      simp only [same, ite_false, Nat.add_zero, equivalent]
  unfold boundarySteps
  simp_rw [term]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  omega

omit caller [DecidableEq K] in
theorem boundaryRegisters_succ (i : Fin 16) (j : Fin 15) (regs : Registers R)
    (ordered : i.val ≤ j.val) :
    occupancyRegisters false (boundaryRegisters i j.castSucc regs) = boundaryRegisters i j.succ regs := by
  have distinct : i ≠ j.succ := by intro h; have := congrArg Fin.val h; simp only [Fin.val_succ] at this; omega
  simp only [boundaryRegisters, distinct, ite_false]
  split_ifs <;> simp only [occupancyRegisters_occupancyRegisters]

theorem boundary_localRun (i j : Fin 16) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (ordered : i.val ≤ j.val) :
    LocalRun caller (boundarySteps i j D)
      (cfg (some (clearLabel i)) regs D ctx)
      (cfg (some (clearLabel j)) (boundaryRegisters i j regs) (boundaryData i j D) ctx) := by
  induction j using Fin.induction generalizing i with
  | zero =>
      have same : i = 0 := Fin.ext (by simpa only [Fin.val_zero, Nat.le_zero] using ordered)
      subst i
      simpa only [boundarySteps_self, boundaryRegisters_self, boundaryData_self] using
        (LocalRun.refl (caller := caller) (cfg (some (clearLabel 0)) regs D ctx))
  | succ j ih =>
      by_cases same : i = j.succ
      · subst i
        simpa only [boundarySteps_self, boundaryRegisters_self, boundaryData_self] using
          (LocalRun.refl (caller := caller) (cfg (some (clearLabel j.succ)) regs D ctx))
      · have before : i.val ≤ j.val := by
          have unequal : i.val ≠ j.succ.val := by intro h; exact same (Fin.ext h)
          simp only [Fin.val_succ] at ordered unequal
          omega
        have first := ih i before
        have last := clear_slot_localRun caller j.castSucc (boundaryData i j.castSucc D)
          (boundaryRegisters i j.castSucc regs) ctx
        rw [slotLength_boundaryData_target, nextClear_castSucc,
          boundaryData_succ i j D before, boundaryRegisters_succ i j regs before] at last
        have joined := LocalRun.trans caller first last
        have count : boundarySteps i j.castSucc D + (slotLength j.castSucc D + 1) =
            boundarySteps i j.succ D := by rw [boundarySteps_succ i j D before]; omega
        simpa only [count] using joined

omit caller [DecidableEq K] in
def cleanupPrefixCfg (i j : Fin 16) (t : Nat) (regs : Registers R) (D : LocalData)
    (ctx : ∀ k, List (Γ k)) : Cfg Γ Λ R :=
  cfg (some (clearLabel j)) (drainRegisters (boundaryRegisters i j regs) t)
    (dropData j t (boundaryData i j D)) ctx

theorem cleanup_prefix_localRun (i j : Fin 16) (t : Nat) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (ordered : i.val ≤ j.val) (within : t ≤ slotLength j D) :
    LocalRun caller (boundarySteps i j D + t) (cfg (some (clearLabel i)) regs D ctx)
      (cleanupPrefixCfg i j t regs D ctx) := by
  have first := boundary_localRun caller i j D regs ctx ordered
  have last := drain_slot_localRun caller j (boundaryData i j D) (boundaryRegisters i j regs) ctx t
    (by simpa only [slotLength_boundaryData_target] using within)
  exact LocalRun.trans caller first last

theorem cleanup_prefix_iterate (i j : Fin 16) (t : Nat) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (ordered : i.val ≤ j.val) (within : t ≤ slotLength j D) :
    (next caller)^[boundarySteps i j D + t] (some (cfg (some (clearLabel i)) regs D ctx)) =
      some (cleanupPrefixCfg i j t regs D ctx) :=
  (cleanup_prefix_localRun caller i j t D regs ctx ordered within).iterate caller

omit caller [DecidableEq K] in
theorem cleanupPrefixCfg_registers (i j : Fin 16) (t : Nat) (regs : Registers R) (D : LocalData)
    (ctx : ∀ k, List (Γ k)) :
    (cleanupPrefixCfg (Λ := Λ) i j t regs D ctx).var =
      if t = 0 then (if i = j then regs else occupancyRegisters false regs)
      else occupancyRegisters true regs := by
  dsimp only [cleanupPrefixCfg, cfg, drainRegisters, boundaryRegisters]
  split_ifs <;> simp only [occupancyRegisters_occupancyRegisters]

omit caller [DecidableEq K] in
theorem boundaryData_stores (i j : Fin 16) (D : LocalData) (ctx : ∀ k, List (Γ k)) (k : StackId K) :
    stores (boundaryData i j D) ctx k =
      if ∃ index, slotIndex k = some index ∧ i.val ≤ index.val ∧ index.val < j.val
      then [] else stores D ctx k := by
  have selected (index0 : Fin 16) :
      (∃ index, index0 = index ∧ i.val ≤ index.val ∧ index.val < j.val) ↔
        i.val ≤ index0.val ∧ index0.val < j.val := by
    constructor
    · rintro ⟨index, same, bounds⟩
      subst index
      exact bounds
    · intro bounds
      exact ⟨index0, rfl, bounds⟩
  cases k with
  | inl k =>
      cases k <;>
        dsimp only [stores, frontEndData, FrontEndMachine.stores, boundaryData, slotIndex] <;>
        simp only [Option.some.injEq, selected] <;> rfl
  | inr k =>
      cases k with
      | inl k =>
          cases k <;>
            dsimp only [stores, frontEndContext, StreamMachine.frontEndAddedContext,
              FrontEndMachine.stores, boundaryData, slotIndex] <;>
            simp only [Option.some.injEq, selected] <;> rfl
      | inr k =>
          dsimp only [stores, frontEndContext, StreamMachine.frontEndAddedContext,
            FrontEndMachine.stores, slotIndex]
          simp only [reduceCtorEq, false_and, exists_false, ite_false]

omit caller [DecidableEq K] in
theorem boundarySteps_last (i : Fin 16) (D : LocalData) :
    boundarySteps i 15 D + slotLength 15 D + 1 = cleanupSteps i D - 1 := by
  let localCaller : Unit → Statement (fun _ : Empty => Unit) Unit Unit := fun _ => .halt
  let localRegisters : Registers Unit :=
    ((none, none), ⟨none, none, none, none, none⟩, (none, ()))
  let localContext : ∀ _ : Empty, List Unit := fun _ => []
  have first := boundary_localRun localCaller i 15 D localRegisters localContext (by omega)
  have finalSlot := clear_slot_localRun localCaller 15 (boundaryData i 15 D)
    (boundaryRegisters i 15 localRegisters) localContext
  have lastLabel : nextClear (Λ := Unit) 15 = emitLabel := rfl
  rw [slotLength_boundaryData_target, lastLabel] at finalSlot
  have emitted := emit_localRun localCaller (emptySlot 15 (boundaryData i 15 D))
    (occupancyRegisters false (boundaryRegisters i 15 localRegisters)) localContext
  have composite := LocalRun.trans localCaller (LocalRun.trans localCaller first finalSlot) emitted
  have canonical := cleanup_localRun localCaller i D localRegisters localContext
  have sameCount := (LocalRun.first_unique localCaller composite canonical
    not_owned_none not_owned_none).1
  omega

omit caller [DecidableEq K] in
theorem emptySlot_boundaryData_last (i : Fin 16) (D : LocalData) :
    emptySlot 15 (boundaryData i 15 D) = clearSuffix i D := by
  have bound : i.val ≤ 15 := by omega
  simp [emptySlot, slotLength, dropData, boundaryData, clearSuffix, bound]

omit caller [DecidableEq K] in
theorem boundary_prefix_cover (i j : Fin 16) (D : LocalData) (n : Nat)
    (ordered : i.val ≤ j.val)
    (within : n < boundarySteps i j D + slotLength j D + 1) :
    ∃ k : Fin 16, i.val ≤ k.val ∧ k.val ≤ j.val ∧
      ∃ t, t ≤ slotLength k D ∧ n = boundarySteps i k D + t := by
  induction j using Fin.induction generalizing i with
  | zero =>
      have same : i = 0 := Fin.ext (by simpa only [Fin.val_zero, Nat.le_zero] using ordered)
      subst i
      refine ⟨0, Nat.le_refl _, Nat.le_refl _, n, ?_, ?_⟩
      · simpa only [boundarySteps_self, Nat.zero_add, Nat.lt_succ_iff] using within
      · simp only [boundarySteps_self, Nat.zero_add]
  | succ j ih =>
      by_cases same : i = j.succ
      · subst i
        refine ⟨j.succ, Nat.le_refl _, Nat.le_refl _, n, ?_, ?_⟩
        · simpa only [boundarySteps_self, Nat.zero_add, Nat.lt_succ_iff] using within
        · simp only [boundarySteps_self, Nat.zero_add]
      · have before : i.val ≤ j.val := by
          have unequal : i.val ≠ j.succ.val := by intro h; exact same (Fin.ext h)
          simp only [Fin.val_succ] at ordered unequal
          omega
        by_cases early : n < boundarySteps i j.castSucc D + slotLength j.castSucc D + 1
        · obtain ⟨k, lower, upper, t, tBound, count⟩ := ih i before early
          refine ⟨k, lower, ?_, t, tBound, count⟩
          simp only [Fin.val_succ, Fin.val_castSucc] at upper ⊢
          omega
        · have lower : boundarySteps i j.succ D ≤ n := by
            rw [boundarySteps_succ i j D before]
            omega
          refine ⟨j.succ, ordered, Nat.le_refl _, n - boundarySteps i j.succ D, ?_, ?_⟩
          · omega
          · omega

omit caller [DecidableEq K] in
theorem cleanup_prefix_cover (i : Fin 16) (D : LocalData) (n : Nat)
    (beforeEmit : n < cleanupSteps i D - 1) :
    ∃ j : Fin 16, i.val ≤ j.val ∧ ∃ t, t ≤ slotLength j D ∧ n = boundarySteps i j D + t := by
  have within : n < boundarySteps i 15 D + slotLength 15 D + 1 := by
    rwa [boundarySteps_last]
  obtain ⟨j, lower, _, t, tBound, count⟩ :=
    boundary_prefix_cover i 15 D n (by omega) within
  exact ⟨j, lower, t, tBound, count⟩

theorem cleanup_emit_localRun (i : Fin 16) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (cleanupSteps i D - 1) (cfg (some (clearLabel i)) regs D ctx)
      (cfg (some emitLabel) (occupancyRegisters false regs) (clearSuffix i D) ctx) := by
  have first := boundary_localRun caller i 15 D regs ctx (by omega)
  have last := clear_slot_localRun caller 15 (boundaryData i 15 D) (boundaryRegisters i 15 regs) ctx
  have next : nextClear (Λ := Λ) 15 = emitLabel := rfl
  rw [slotLength_boundaryData_target, next, emptySlot_boundaryData_last] at last
  have occupied : occupancyRegisters false (boundaryRegisters i 15 regs) = occupancyRegisters false regs := by
    simp only [boundaryRegisters]
    split_ifs <;> simp only [occupancyRegisters_occupancyRegisters]
  rw [occupied] at last
  have joined := LocalRun.trans caller first last
  have count : boundarySteps i 15 D + (slotLength 15 D + 1) = cleanupSteps i D - 1 := by
    rw [← boundarySteps_last]
    omega
  simpa only [count] using joined

theorem cleanup_emit_iterate (i : Fin 16) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    (next caller)^[cleanupSteps i D - 1] (some (cfg (some (clearLabel i)) regs D ctx)) =
      some (cfg (some emitLabel) (occupancyRegisters false regs) (clearSuffix i D) ctx) :=
  (cleanup_emit_localRun caller i D regs ctx).iterate caller

include caller in
theorem cleanup_prefix_unique (i j k : Fin 16) (t u : Nat) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (jLower : i.val ≤ j.val) (kLower : i.val ≤ k.val)
    (tBound : t ≤ slotLength j D) (uBound : u ≤ slotLength k D)
    (clock : boundarySteps i j D + t = boundarySteps i k D + u) : j = k ∧ t = u := by
  have first := cleanup_prefix_iterate caller i j t D regs ctx jLower tBound
  have second := cleanup_prefix_iterate caller i k u D regs ctx kLower uBound
  rw [clock] at first
  have same := Option.some.inj (first.symm.trans second)
  have labels := congrArg (fun c : Cfg Γ Λ R => c.l) same
  have clearLabels : clearLabel (Λ := Λ) j = clearLabel k := Option.some.inj labels
  have indices : j = k := CleanupPhase.clear.inj
    (Sum.inl.inj (Sum.inr.inj (Sum.inr.inj clearLabels)))
  subst k
  exact ⟨rfl, by omega⟩

theorem clear_prefix (i : Fin 16) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (n : Nat) (beforeEmit : n < cleanupSteps i D - 1) :
    ∃ j : Fin 16, i.val ≤ j.val ∧ ∃ t, t ≤ slotLength j D ∧
      n = boundarySteps i j D + t ∧
      (next caller)^[n] (some (cfg (some (clearLabel i)) regs D ctx)) =
        some (cleanupPrefixCfg i j t regs D ctx) ∧
      ∀ k u, i.val ≤ k.val → u ≤ slotLength k D →
        n = boundarySteps i k D + u → k = j ∧ u = t := by
  obtain ⟨j, lower, t, tBound, count⟩ := cleanup_prefix_cover i D n beforeEmit
  refine ⟨j, lower, t, tBound, count, ?_, ?_⟩
  · rw [count]
    exact cleanup_prefix_iterate caller i j t D regs ctx lower tBound
  · intro k u kLower uBound otherCount
    exact cleanup_prefix_unique caller i k j u t D regs ctx kLower lower uBound tBound
      (otherCount.symm.trans count)



end Resources.RotationCertificate.FrontEndStreamMachine
