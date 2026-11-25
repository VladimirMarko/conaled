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
  FrontEndMachine.Transport.stackCells (Equiv.refl _) (fun _ => Equiv.refl _) c.stk

omit caller [DecidableEq K] in
theorem stackCells_streamCfg (c : StreamCfg Γ Λ R) :
    stackCells (streamCfg c) = StreamMachine.stackCells c :=
  FrontEndMachine.Transport.stackCells streamStackEquiv streamSymbolEquiv c.stk

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

namespace Resources.RotationCertificate.FrontEndStreamMachine.DirtyFrontEnd

open Resources.BinaryCounter (Bits)

structure TreeState (D : Type) where
  raw : Word
  rev : Word
  pending : List Unit
  outputs : D → Word

structure TreeEnd (D : Type) where
  result : TreeParserMachine.Result
  data : TreeState D

structure TreeFinish (D : Type) extends TreeEnd D where
  steps : Nat

variable {D K Λ R : Type} {Γ : K → Type}

def treeCfg (label : Option (TreeParserMachine.Label D Λ))
    (regs : TreeParserMachine.Registers R) (data : TreeState D)
    (ctx : ∀ k, List (Γ k)) : TreeParserMachine.Cfg D Γ Λ R :=
  TreeParserMachine.cfg label regs data.raw data.rev data.pending data.outputs ctx

def treeUndoEnd (data : TreeState D) : TreeEnd D :=
  ⟨.failure, { data with raw := data.rev.reverse ++ data.raw, rev := [], pending := [] }⟩

def treeDropEnd (data : TreeState D) : TreeEnd D :=
  ⟨.failure, { data with pending := [] }⟩

def treeEmitEnd [DecidableEq D] (destination : D) (data : TreeState D) : TreeEnd D :=
  { result := .success
    data := { data with
      rev := []
      outputs := Function.update data.outputs destination
        (data.rev.reverse ++ data.outputs destination) } }

/-- Structural recursion consumes the actual raw list, even on a dirty frontier. -/
def treeScanEnd [DecidableEq D] (destination : D) :
    Word → Word → List Unit → (D → Word) → TreeEnd D
  | [], rev, pending, outputs => treeUndoEnd ⟨[], rev, pending, outputs⟩
  | tag :: raw, rev, pending, outputs =>
      if tag = nodeTag then
        treeScanEnd destination raw (nodeTag :: rev) (() :: pending) outputs
      else if tag = emptyTag then
        if pending.tail = [] then
          treeEmitEnd destination ⟨raw, emptyTag :: rev, pending.tail, outputs⟩
        else treeScanEnd destination raw (emptyTag :: rev) pending.tail outputs
      else treeUndoEnd ⟨tag :: raw, rev, pending, outputs⟩

def treePhaseEnd [DecidableEq D] (destination : D)
    (phase : TreeParserMachine.Phase) (data : TreeState D) : TreeEnd D :=
  match phase with
  | .init => treeScanEnd destination data.raw data.rev (() :: data.pending) data.outputs
  | .scan => treeScanEnd destination data.raw data.rev data.pending data.outputs
  | .emit => treeEmitEnd destination data
  | .undo => treeUndoEnd data
  | .dropPending => treeDropEnd data

/-- The existing exact physical countdown is paired with the newly explicit endpoint. -/
def treePhaseFinish [DecidableEq D] (destination : D)
    (phase : TreeParserMachine.Phase) (data : TreeState D) : TreeFinish D :=
  { treePhaseEnd destination phase data with
    steps := TreeParserMachine.phaseSteps phase data.raw data.rev data.pending }

theorem treePhaseFinish_steps [DecidableEq D] (destination : D)
    (phase : TreeParserMachine.Phase) (data : TreeState D) :
    (treePhaseFinish destination phase data).steps =
      TreeParserMachine.phaseSteps phase data.raw data.rev data.pending := rfl

theorem tree_tail_empty_iff (pending : List Unit) :
    pending.tail = [] ↔ pending.length ≤ 1 := by
  cases pending with
  | nil => simp
  | cons token pending => cases pending <;> simp

theorem treePhaseFinish_steps_pos [DecidableEq D] (destination : D)
    (phase : TreeParserMachine.Phase) (data : TreeState D) :
    0 < (treePhaseFinish destination phase data).steps := by
  rw [treePhaseFinish_steps]
  cases phase with
  | init => simp [TreeParserMachine.phaseSteps]
  | scan => exact TreeParserMachine.scanSteps_pos _ _ _
  | emit => simp [TreeParserMachine.phaseSteps]
  | undo => simp [TreeParserMachine.phaseSteps]
  | dropPending => simp [TreeParserMachine.phaseSteps]

section TreeExecution
variable [DecidableEq D] [DecidableEq K]
variable (caller : TreeParserMachine.External D Λ → TreeParserMachine.Statement D Γ Λ R)

theorem treeScanEnd_iterate (destination : D) (raw rev : Word) (pending : List Unit)
    (regs : TreeParserMachine.Registers R) (outputs : D → Word) (ctx : ∀ k, List (Γ k)) :
    (TreeParserMachine.next caller)^[TreeParserMachine.scanSteps raw pending.length rev.length]
      (some (TreeParserMachine.cfg (some (TreeParserMachine.phaseLabel destination .scan))
        regs raw rev pending outputs ctx)) =
      some (treeCfg
        (some (TreeParserMachine.resultLabel destination (treeScanEnd destination raw rev pending outputs).result))
        (TreeParserMachine.reset regs) (treeScanEnd destination raw rev pending outputs).data ctx) := by
  induction raw generalizing rev pending regs with
  | nil =>
      simpa only [treeScanEnd, treeUndoEnd, treeCfg, TreeParserMachine.scanSteps_nil, List.append_nil] using
        TreeParserMachine.scan_nil_iterate caller destination rev pending regs outputs ctx
  | cons tag raw ih =>
      by_cases isNode : tag = nodeTag
      · subst tag
        rw [TreeParserMachine.scanSteps_node, Nat.add_comm 1 _,
          TreeParserMachine.iterate_step caller _ _ _
            (TreeParserMachine.scan_step_node caller destination raw rev pending regs outputs ctx)]
        simpa only [treeScanEnd, ite_true, List.length_cons, TreeParserMachine.reset_reset] using
          ih (nodeTag :: rev) (() :: pending) (TreeParserMachine.reset regs)
      · by_cases isEmpty : tag = emptyTag
        · subst tag
          have notNode : emptyTag ≠ nodeTag := by decide
          by_cases finished : pending.tail = []
          · have small := (tree_tail_empty_iff pending).mp finished
            rw [TreeParserMachine.scanSteps_empty, ite_eq_left small]
            have transition := TreeParserMachine.scan_step_empty caller destination raw rev pending regs outputs ctx
            simp only [finished, ite_true] at transition
            rw [show rev.length + 3 = ((emptyTag :: rev).length + 1) + 1 by simp,
              TreeParserMachine.iterate_step caller _ _ _ transition]
            simpa only [treeScanEnd, ite_eq_right notNode, ite_true, finished, treeEmitEnd,
              treeCfg, TreeParserMachine.reset_reset] using
              TreeParserMachine.emit_iterate caller destination raw (emptyTag :: rev) []
                (TreeParserMachine.reset regs) outputs ctx
          · have large : ¬ pending.length ≤ 1 := by
              intro small
              exact finished ((tree_tail_empty_iff pending).mpr small)
            rw [TreeParserMachine.scanSteps_empty, ite_eq_right large, Nat.add_comm 1 _]
            have transition := TreeParserMachine.scan_step_empty caller destination raw rev pending regs outputs ctx
            simp only [ite_eq_right finished] at transition
            rw [TreeParserMachine.iterate_step caller _ _ _ transition]
            simpa only [treeScanEnd, ite_eq_right notNode, ite_true, ite_eq_right finished,
              List.length_tail, List.length_cons, TreeParserMachine.reset_reset] using
              ih (emptyTag :: rev) pending.tail (TreeParserMachine.reset regs)
        · rw [TreeParserMachine.scanSteps_foreign tag raw pending.length rev.length isNode isEmpty]
          simpa only [treeScanEnd, ite_eq_right isNode, ite_eq_right isEmpty, treeUndoEnd, treeCfg] using
            TreeParserMachine.scan_foreign_iterate caller destination tag raw rev pending regs outputs ctx
              isNode isEmpty

theorem treePhaseFinish_iterate (destination : D) (phase : TreeParserMachine.Phase)
    (data : TreeState D) (regs : TreeParserMachine.Registers R) (ctx : ∀ k, List (Γ k)) :
    (TreeParserMachine.next caller)^[(treePhaseFinish destination phase data).steps]
      (some (treeCfg (some (TreeParserMachine.phaseLabel destination phase)) regs data ctx)) =
      some (treeCfg (some (TreeParserMachine.resultLabel destination
        (treePhaseFinish destination phase data).result)) (TreeParserMachine.reset regs)
        (treePhaseFinish destination phase data).data ctx) := by
  rcases data with ⟨raw, rev, pending, outputs⟩
  cases phase with
  | init =>
      simp only [treePhaseFinish, treePhaseEnd, treeCfg, TreeParserMachine.phaseSteps]
      rw [Nat.add_comm 1 _, TreeParserMachine.iterate_step caller _ _ _
        (TreeParserMachine.init_step caller destination raw rev pending regs outputs ctx)]
      simpa only [List.length_cons, TreeParserMachine.reset_reset, treeCfg] using
        treeScanEnd_iterate caller destination raw rev (() :: pending)
          (TreeParserMachine.reset regs) outputs ctx
  | scan =>
      exact treeScanEnd_iterate caller destination raw rev pending regs outputs ctx
  | emit =>
      simpa only [treePhaseFinish, treePhaseEnd, treeEmitEnd, treeCfg, TreeParserMachine.phaseSteps] using
        TreeParserMachine.emit_iterate caller destination raw rev pending regs outputs ctx
  | undo =>
      simpa only [treePhaseFinish, treePhaseEnd, treeUndoEnd, treeCfg, TreeParserMachine.phaseSteps] using
        TreeParserMachine.undo_drop_iterate caller destination raw rev pending regs outputs ctx
  | dropPending =>
      simpa only [treePhaseFinish, treePhaseEnd, treeDropEnd, treeCfg, TreeParserMachine.phaseSteps] using
        TreeParserMachine.dropPending_iterate caller destination raw rev pending regs outputs ctx

theorem treePhaseFinish_owned_prefix (destination : D) (phase : TreeParserMachine.Phase)
    (data : TreeState D) (regs : TreeParserMachine.Registers R) (ctx : ∀ k, List (Γ k))
    (n : Nat) (bound : n < (treePhaseFinish destination phase data).steps) :
    ∃ reached, (TreeParserMachine.next caller)^[n]
      (some (treeCfg (some (TreeParserMachine.phaseLabel destination phase)) regs data ctx)) =
        some reached ∧ TreeParserMachine.Owned reached.l := by
  obtain ⟨reached, executed, _, _, owned, _⟩ := TreeParserMachine.phase_prefix caller
    destination phase data.raw data.rev data.pending regs data.outputs ctx n (Nat.le_of_lt bound)
  exact ⟨reached, executed, owned.mp bound⟩

end TreeExecution

/-! Insert after the constructive dirty Tree helper, in the same namespace. -/

structure InputState extends TreeState InputParserMachine.TreeSide where
  fuel : Bits
  bitsReverse : Bits

structure InputFinish where
  result : TreeParserMachine.Result
  data : InputState
  steps : Nat

def inputCfg (label : Option (InputParserMachine.Label Λ))
    (regs : InputParserMachine.Registers R) (data : InputState)
    (ctx : ∀ k, List (Γ k)) : InputParserMachine.Cfg Γ Λ R :=
  InputParserMachine.cfg label regs data.raw data.rev data.pending data.outputs
    data.fuel data.bitsReverse ctx

def inputAdd (ticks : Nat) (finish : InputFinish) : InputFinish :=
  { finish with steps := ticks + finish.steps }

def inputSourceToRaw (data : InputState) : InputFinish :=
  ⟨.failure, { data with raw := data.rev.reverse ++ data.raw, rev := [] }, data.rev.length + 1⟩

def inputSourceToReverse (data : InputState) : InputFinish :=
  inputAdd ((data.outputs .source).length + 1)
    (inputSourceToRaw { data with
      rev := (data.outputs .source).reverse ++ data.rev
      outputs := Function.update data.outputs .source [] })

def inputRestoreSep1 (data : InputState) : InputFinish :=
  inputAdd 1 (inputSourceToReverse { data with raw := separatorTag :: data.raw })

def inputTargetToRaw (data : InputState) : InputFinish :=
  inputAdd (data.rev.length + 1)
    (inputRestoreSep1 { data with raw := data.rev.reverse ++ data.raw, rev := [] })

def inputTargetToReverse (data : InputState) : InputFinish :=
  inputAdd ((data.outputs .target).length + 1)
    (inputTargetToRaw { data with
      rev := (data.outputs .target).reverse ++ data.rev
      outputs := Function.update data.outputs .target [] })

def inputRestoreSep2 (data : InputState) : InputFinish :=
  inputAdd 1 (inputTargetToReverse { data with raw := separatorTag :: data.raw })

def inputBitsUndo (data : InputState) : InputFinish :=
  inputAdd (data.bitsReverse.length + 1)
    (inputRestoreSep2 { data with
      raw := bitTags data.bitsReverse.reverse ++ data.raw
      bitsReverse := [] })

def inputFuelUndo (data : InputState) : InputFinish :=
  inputAdd (data.fuel.length + 1)
    (inputBitsUndo { data with fuel := [], bitsReverse := data.fuel.reverse ++ data.bitsReverse })

def inputRestoreEnd (data : InputState) : InputFinish :=
  inputAdd 1 (inputFuelUndo { data with raw := endInputTag :: data.raw })

def inputEof (data : InputState) : InputFinish :=
  if data.raw = [] then ⟨.success, data, 1⟩ else inputAdd 1 (inputRestoreEnd data)

def inputBitsEmit (data : InputState) : InputFinish :=
  inputAdd (data.bitsReverse.length + 1)
    (inputEof { data with fuel := data.bitsReverse.reverse ++ data.fuel, bitsReverse := [] })

/-- Each recursion removes one actual bit tag; the terminal branch is paid too. -/
def inputBitsScanAux : Word → InputState → InputFinish
  | [], data => inputAdd 1 (inputBitsUndo { data with raw := [] })
  | tag :: raw, data =>
      if tag = bitZeroTag then
        inputAdd 1 (inputBitsScanAux raw { data with bitsReverse := false :: data.bitsReverse })
      else if tag = bitOneTag then
        inputAdd 1 (inputBitsScanAux raw { data with bitsReverse := true :: data.bitsReverse })
      else if tag = endInputTag then
        inputAdd 1 (inputBitsEmit { data with raw := raw })
      else inputAdd 1 (inputBitsUndo { data with raw := tag :: raw })

def inputLocalFinish (phase : InputParserMachine.Phase) (data : InputState) : InputFinish :=
  match phase with
  | .sourceToRaw => inputSourceToRaw data
  | .sourceToReverse => inputSourceToReverse data
  | .restoreSep1 => inputRestoreSep1 data
  | .targetToRaw => inputTargetToRaw data
  | .targetToReverse => inputTargetToReverse data
  | .restoreSep2 => inputRestoreSep2 data
  | .bitsUndo => inputBitsUndo data
  | .fuelUndo => inputFuelUndo data
  | .restoreEnd => inputRestoreEnd data
  | .eof => inputEof data
  | .bitsEmit => inputBitsEmit data
  | .bitsScan => inputBitsScanAux data.raw data

section InputExecution
variable [DecidableEq K]
variable (caller : InputParserMachine.External Λ → InputParserMachine.Statement Γ Λ R)

def InputFinish.Run (finish : InputFinish) (label : InputParserMachine.Label Λ)
    (data : InputState) (regs : InputParserMachine.Registers R) (ctx : ∀ k, List (Γ k)) : Prop :=
  InputParserMachine.Runs caller finish.steps (inputCfg (some label) regs data ctx)
    (inputCfg (some (InputParserMachine.resultLabel finish.result))
      (InputParserMachine.reset regs) finish.data ctx)

theorem InputFinish.Run.prepend {finish : InputFinish}
    {label nextLabel : InputParserMachine.Label Λ} {data nextData : InputState}
    {regs : InputParserMachine.Registers R} {ctx : ∀ k, List (Γ k)} {ticks : Nat}
    (segment : InputParserMachine.Runs caller ticks (inputCfg (some label) regs data ctx)
      (inputCfg (some nextLabel) (InputParserMachine.reset regs) nextData ctx))
    (tailRun : finish.Run caller nextLabel nextData (InputParserMachine.reset regs) ctx) :
    (inputAdd ticks finish).Run caller label data regs ctx := by
  simpa only [InputFinish.Run, inputAdd, TreeParserMachine.reset_reset] using
    segment.trans caller tailRun

theorem inputSourceToRaw_run (data : InputState) (regs : InputParserMachine.Registers R)
    (ctx : ∀ k, List (Γ k)) :
    (inputSourceToRaw data).Run caller (InputParserMachine.phaseLabel .sourceToRaw) data regs ctx := by
  exact InputParserMachine.toRaw_run caller .source data.raw data.rev data.pending regs
    data.outputs data.fuel data.bitsReverse ctx

theorem inputSourceToReverse_run (data : InputState) (regs : InputParserMachine.Registers R)
    (ctx : ∀ k, List (Γ k)) :
    (inputSourceToReverse data).Run caller (InputParserMachine.phaseLabel .sourceToReverse)
      data regs ctx := by
  apply InputFinish.Run.prepend caller (nextLabel := InputParserMachine.phaseLabel .sourceToRaw)
    (nextData := { data with rev := (data.outputs .source).reverse ++ data.rev, outputs := Function.update data.outputs .source [] })
  · simpa only [inputCfg, Function.update_eq_self, InputParserMachine.toReversePhase, InputParserMachine.toRawPhase] using
      InputParserMachine.toReverse_run caller .source (data.outputs .source) data.raw data.rev
        data.pending regs data.outputs data.fuel data.bitsReverse ctx
  · exact inputSourceToRaw_run caller _ _ _

theorem inputRestoreSep1_run (data : InputState) (regs : InputParserMachine.Registers R)
    (ctx : ∀ k, List (Γ k)) :
    (inputRestoreSep1 data).Run caller (InputParserMachine.phaseLabel .restoreSep1) data regs ctx := by
  apply InputFinish.Run.prepend caller (nextLabel := InputParserMachine.phaseLabel .sourceToReverse)
    (nextData := { data with raw := separatorTag :: data.raw })
  · exact InputParserMachine.Runs.one caller (InputParserMachine.fullOwned_phase _)
      (InputParserMachine.restoreSep1_step caller data.raw data.rev data.pending regs data.outputs
        data.fuel data.bitsReverse ctx)
  · exact inputSourceToReverse_run caller _ _ _

theorem inputTargetToRaw_run (data : InputState) (regs : InputParserMachine.Registers R)
    (ctx : ∀ k, List (Γ k)) :
    (inputTargetToRaw data).Run caller (InputParserMachine.phaseLabel .targetToRaw) data regs ctx := by
  apply InputFinish.Run.prepend caller (nextLabel := InputParserMachine.phaseLabel .restoreSep1)
    (nextData := { data with raw := data.rev.reverse ++ data.raw, rev := [] })
  · exact InputParserMachine.toRaw_run caller .target data.raw data.rev data.pending regs
      data.outputs data.fuel data.bitsReverse ctx
  · exact inputRestoreSep1_run caller _ _ _

theorem inputTargetToReverse_run (data : InputState) (regs : InputParserMachine.Registers R)
    (ctx : ∀ k, List (Γ k)) :
    (inputTargetToReverse data).Run caller (InputParserMachine.phaseLabel .targetToReverse)
      data regs ctx := by
  apply InputFinish.Run.prepend caller (nextLabel := InputParserMachine.phaseLabel .targetToRaw)
    (nextData := { data with rev := (data.outputs .target).reverse ++ data.rev, outputs := Function.update data.outputs .target [] })
  · simpa only [inputCfg, Function.update_eq_self, InputParserMachine.toReversePhase, InputParserMachine.toRawPhase] using
      InputParserMachine.toReverse_run caller .target (data.outputs .target) data.raw data.rev
        data.pending regs data.outputs data.fuel data.bitsReverse ctx
  · exact inputTargetToRaw_run caller _ _ _

theorem inputRestoreSep2_run (data : InputState) (regs : InputParserMachine.Registers R)
    (ctx : ∀ k, List (Γ k)) :
    (inputRestoreSep2 data).Run caller (InputParserMachine.phaseLabel .restoreSep2) data regs ctx := by
  apply InputFinish.Run.prepend caller (nextLabel := InputParserMachine.phaseLabel .targetToReverse)
    (nextData := { data with raw := separatorTag :: data.raw })
  · exact InputParserMachine.Runs.one caller (InputParserMachine.fullOwned_phase _)
      (InputParserMachine.restoreSep2_step caller data.raw data.rev data.pending regs data.outputs
        data.fuel data.bitsReverse ctx)
  · exact inputTargetToReverse_run caller _ _ _

theorem inputBitsUndo_run (data : InputState) (regs : InputParserMachine.Registers R)
    (ctx : ∀ k, List (Γ k)) :
    (inputBitsUndo data).Run caller (InputParserMachine.phaseLabel .bitsUndo) data regs ctx := by
  apply InputFinish.Run.prepend caller (nextLabel := InputParserMachine.phaseLabel .restoreSep2)
    (nextData := { data with raw := bitTags data.bitsReverse.reverse ++ data.raw, bitsReverse := [] })
  · exact InputParserMachine.bitsUndo_run caller data.raw data.rev data.pending regs
      data.outputs data.fuel data.bitsReverse ctx
  · exact inputRestoreSep2_run caller _ _ _

theorem inputFuelUndo_run (data : InputState) (regs : InputParserMachine.Registers R)
    (ctx : ∀ k, List (Γ k)) :
    (inputFuelUndo data).Run caller (InputParserMachine.phaseLabel .fuelUndo) data regs ctx := by
  apply InputFinish.Run.prepend caller (nextLabel := InputParserMachine.phaseLabel .bitsUndo)
    (nextData := { data with fuel := [], bitsReverse := data.fuel.reverse ++ data.bitsReverse })
  · exact InputParserMachine.fuelUndo_run caller data.raw data.rev data.pending regs
      data.outputs data.fuel data.bitsReverse ctx
  · exact inputBitsUndo_run caller _ _ _

theorem inputRestoreEnd_run (data : InputState) (regs : InputParserMachine.Registers R)
    (ctx : ∀ k, List (Γ k)) :
    (inputRestoreEnd data).Run caller (InputParserMachine.phaseLabel .restoreEnd) data regs ctx := by
  apply InputFinish.Run.prepend caller (nextLabel := InputParserMachine.phaseLabel .fuelUndo)
    (nextData := { data with raw := endInputTag :: data.raw })
  · exact InputParserMachine.Runs.one caller (InputParserMachine.fullOwned_phase _)
      (InputParserMachine.restoreEnd_step caller data.raw data.rev data.pending regs data.outputs
        data.fuel data.bitsReverse ctx)
  · exact inputFuelUndo_run caller _ _ _

theorem inputEof_run (data : InputState) (regs : InputParserMachine.Registers R)
    (ctx : ∀ k, List (Γ k)) :
    (inputEof data).Run caller (InputParserMachine.phaseLabel .eof) data regs ctx := by
  unfold inputEof
  split
  · rename_i empty
    simpa only [InputFinish.Run, inputCfg, empty] using
      InputParserMachine.Runs.one caller (InputParserMachine.fullOwned_phase _)
        (InputParserMachine.eof_step_nil caller data.rev data.pending regs data.outputs
          data.fuel data.bitsReverse ctx)
  · rename_i nonempty
    apply InputFinish.Run.prepend caller (nextLabel := InputParserMachine.phaseLabel .restoreEnd)
      (nextData := data)
    · cases rawEq : data.raw with
      | nil => exact False.elim (nonempty rawEq)
      | cons tag raw =>
          simpa only [inputCfg, rawEq] using
            InputParserMachine.Runs.one caller (InputParserMachine.fullOwned_phase _)
              (InputParserMachine.eof_step_cons caller tag raw data.rev data.pending regs
                data.outputs data.fuel data.bitsReverse ctx)
    · exact inputRestoreEnd_run caller _ _ _

theorem inputBitsEmit_run (data : InputState) (regs : InputParserMachine.Registers R)
    (ctx : ∀ k, List (Γ k)) :
    (inputBitsEmit data).Run caller (InputParserMachine.phaseLabel .bitsEmit) data regs ctx := by
  apply InputFinish.Run.prepend caller (nextLabel := InputParserMachine.phaseLabel .eof)
    (nextData := { data with fuel := data.bitsReverse.reverse ++ data.fuel, bitsReverse := [] })
  · exact InputParserMachine.bitsEmit_run caller data.raw data.rev data.pending regs
      data.outputs data.fuel data.bitsReverse ctx
  · exact inputEof_run caller _ _ _

theorem inputBitsScanAux_run (raw : Word) (data : InputState)
    (regs : InputParserMachine.Registers R) (ctx : ∀ k, List (Γ k)) :
    (inputBitsScanAux raw data).Run caller (InputParserMachine.phaseLabel .bitsScan)
      { data with raw := raw } regs ctx := by
  induction raw generalizing data regs with
  | nil =>
      apply InputFinish.Run.prepend caller (nextLabel := InputParserMachine.phaseLabel .bitsUndo) (nextData := { data with raw := [] })
      · exact InputParserMachine.Runs.one caller (InputParserMachine.fullOwned_phase _)
          (InputParserMachine.bitsScan_step_nil caller data.rev data.pending regs data.outputs
            data.fuel data.bitsReverse ctx)
      · exact inputBitsUndo_run caller _ _ _
  | cons tag raw ih =>
      unfold inputBitsScanAux
      split
      · rename_i zero
        subst tag
        apply InputFinish.Run.prepend caller (nextLabel := InputParserMachine.phaseLabel .bitsScan) (nextData := { data with raw := raw, bitsReverse := false :: data.bitsReverse })
        · exact InputParserMachine.Runs.one caller (InputParserMachine.fullOwned_phase _)
            (InputParserMachine.bitsScan_step_bit caller false raw data.rev data.pending regs
              data.outputs data.fuel data.bitsReverse ctx)
        · exact ih _ _
      · rename_i notZero
        split
        · rename_i one
          subst tag
          apply InputFinish.Run.prepend caller (nextLabel := InputParserMachine.phaseLabel .bitsScan) (nextData := { data with raw := raw, bitsReverse := true :: data.bitsReverse })
          · exact InputParserMachine.Runs.one caller (InputParserMachine.fullOwned_phase _)
              (InputParserMachine.bitsScan_step_bit caller true raw data.rev data.pending regs
                data.outputs data.fuel data.bitsReverse ctx)
          · exact ih _ _
        · rename_i notOne
          split
          · rename_i ended
            subst tag
            apply InputFinish.Run.prepend caller (nextLabel := InputParserMachine.phaseLabel .bitsEmit) (nextData := { data with raw := raw })
            · exact InputParserMachine.Runs.one caller (InputParserMachine.fullOwned_phase _)
                (InputParserMachine.bitsScan_step_end caller raw data.rev data.pending regs
                  data.outputs data.fuel data.bitsReverse ctx)
            · exact inputBitsEmit_run caller _ _ _
          · rename_i notEnd
            apply InputFinish.Run.prepend caller (nextLabel := InputParserMachine.phaseLabel .bitsUndo) (nextData := { data with raw := tag :: raw })
            · exact InputParserMachine.Runs.one caller (InputParserMachine.fullOwned_phase _)
                (InputParserMachine.bitsScan_step_foreign caller tag raw data.rev data.pending regs
                  data.outputs data.fuel data.bitsReverse ctx notEnd notZero notOne)
            · exact inputBitsUndo_run caller _ _ _

theorem inputLocalFinish_run (phase : InputParserMachine.Phase) (data : InputState)
    (regs : InputParserMachine.Registers R) (ctx : ∀ k, List (Γ k)) :
    (inputLocalFinish phase data).Run caller (InputParserMachine.phaseLabel phase) data regs ctx := by
  cases phase with
  | sourceToRaw => exact inputSourceToRaw_run caller data regs ctx
  | sourceToReverse => exact inputSourceToReverse_run caller data regs ctx
  | restoreSep1 => exact inputRestoreSep1_run caller data regs ctx
  | targetToRaw => exact inputTargetToRaw_run caller data regs ctx
  | targetToReverse => exact inputTargetToReverse_run caller data regs ctx
  | restoreSep2 => exact inputRestoreSep2_run caller data regs ctx
  | bitsUndo => exact inputBitsUndo_run caller data regs ctx
  | fuelUndo => exact inputFuelUndo_run caller data regs ctx
  | restoreEnd => exact inputRestoreEnd_run caller data regs ctx
  | eof => exact inputEof_run caller data regs ctx
  | bitsEmit => exact inputBitsEmit_run caller data regs ctx
  | bitsScan => exact inputBitsScanAux_run caller data.raw data regs ctx

end InputExecution

def inputWithTree (data : InputState) (tree : TreeState InputParserMachine.TreeSide) : InputState :=
  { data with toTreeState := tree }

def inputTargetSuccess (data : InputState) : InputFinish :=
  match data.raw with
  | [] => inputAdd 1 (inputTargetToReverse data)
  | tag :: raw =>
      if tag = separatorTag then
        inputAdd 1 (inputBitsScanAux raw { data with raw := raw })
      else inputAdd 1 (inputTargetToReverse data)

def inputTargetTree (phase : TreeParserMachine.Phase) (data : InputState) : InputFinish :=
  let tree := treePhaseFinish .target phase data.toTreeState
  let afterTree := inputWithTree data tree.data
  inputAdd tree.steps (match tree.result with
    | .success => inputTargetSuccess afterTree
    | .failure => inputRestoreSep1 afterTree)

def inputSourceSuccess (data : InputState) : InputFinish :=
  match data.raw with
  | [] => inputAdd 1 (inputSourceToReverse data)
  | tag :: raw =>
      if tag = separatorTag then
        inputAdd 1 (inputTargetTree .init { data with raw := raw })
      else inputAdd 1 (inputSourceToReverse data)

def inputSourceTree (phase : TreeParserMachine.Phase) (data : InputState) : InputFinish :=
  let tree := treePhaseFinish .source phase data.toTreeState
  let afterTree := inputWithTree data tree.data
  match tree.result with
  | .success => inputAdd tree.steps (inputSourceSuccess afterTree)
  | .failure => ⟨.failure, afterTree, tree.steps⟩

/-- All twenty-five actual Input owned controls, including the three result handlers. -/
def inputPhaseFinish (phase : InputParserMachine.OwnedLabels) (data : InputState) : InputFinish :=
  match phase with
  | .inl (.source, phase) => inputSourceTree phase data
  | .inl (.target, phase) => inputTargetTree phase data
  | .inr (.inl .source) => inputSourceSuccess data
  | .inr (.inl .target) => inputTargetSuccess data
  | .inr (.inr (.inl _)) => inputRestoreSep1 data
  | .inr (.inr (.inr phase)) => inputLocalFinish phase data

section InputFullExecution
variable [DecidableEq K]
variable (caller : InputParserMachine.External Λ → InputParserMachine.Statement Γ Λ R)

theorem inputTargetFailure_run (data : InputState) (regs : InputParserMachine.Registers R)
    (ctx : ∀ k, List (Γ k)) :
    (inputRestoreSep1 data).Run caller (InputParserMachine.treeResultLabel .target .failure)
      data regs ctx := by
  apply InputFinish.Run.prepend caller (nextLabel := InputParserMachine.phaseLabel .sourceToReverse)
    (nextData := { data with raw := separatorTag :: data.raw })
  · exact InputParserMachine.Runs.one caller True.intro
      (InputParserMachine.targetFailure_step caller data.raw data.rev data.pending regs data.outputs
        data.fuel data.bitsReverse ctx)
  · exact inputSourceToReverse_run caller _ _ _

theorem inputTargetSuccess_run (data : InputState) (regs : InputParserMachine.Registers R)
    (ctx : ∀ k, List (Γ k)) :
    (inputTargetSuccess data).Run caller (InputParserMachine.treeResultLabel .target .success)
      data regs ctx := by
  cases rawEq : data.raw with
  | nil =>
      simp only [inputTargetSuccess, rawEq]
      apply InputFinish.Run.prepend caller (nextLabel := InputParserMachine.phaseLabel .targetToReverse) (nextData := data)
      · apply InputParserMachine.Runs.one caller (by trivial)
        simpa only [inputCfg, rawEq, InputParserMachine.toReversePhase] using
          (InputParserMachine.separator_step_nil caller .target data.rev data.pending regs
            data.outputs data.fuel data.bitsReverse ctx)
      · exact inputTargetToReverse_run caller _ _ _
  | cons tag raw =>
      simp only [inputTargetSuccess, rawEq]
      split
      · rename_i separator
        subst tag
        apply InputFinish.Run.prepend caller (nextLabel := InputParserMachine.phaseLabel .bitsScan) (nextData := { data with raw := raw })
        · apply InputParserMachine.Runs.one caller (by trivial)
          simpa only [inputCfg, rawEq, InputParserMachine.afterSeparator] using
            (InputParserMachine.separator_step_separator caller .target raw data.rev data.pending regs
              data.outputs data.fuel data.bitsReverse ctx)
        · exact inputBitsScanAux_run caller _ _ _ _
      · rename_i foreign
        apply InputFinish.Run.prepend caller (nextLabel := InputParserMachine.phaseLabel .targetToReverse) (nextData := data)
        · apply InputParserMachine.Runs.one caller (by trivial)
          simpa only [inputCfg, rawEq, InputParserMachine.toReversePhase] using
            (InputParserMachine.separator_step_foreign caller .target tag raw data.rev data.pending regs
              data.outputs data.fuel data.bitsReverse ctx foreign)
        · exact inputTargetToReverse_run caller _ _ _

theorem inputTreeSegment_run (destination : InputParserMachine.TreeSide)
    (phase : TreeParserMachine.Phase) (data : InputState)
    (regs : InputParserMachine.Registers R) (ctx : ∀ k, List (Γ k)) :
    InputParserMachine.Runs caller (treePhaseFinish destination phase data.toTreeState).steps
      (inputCfg (some (InputParserMachine.treeLabel destination phase)) regs data ctx)
      (inputCfg (some (InputParserMachine.treeResultLabel destination
        (treePhaseFinish destination phase data.toTreeState).result))
        (InputParserMachine.reset regs)
        (inputWithTree data (treePhaseFinish destination phase data.toTreeState).data) ctx) := by
  apply InputParserMachine.tree_phase_run caller
  exact treePhaseFinish_iterate (InputParserMachine.handler caller) destination phase data.toTreeState
    regs (InputParserMachine.stores data.fuel data.bitsReverse ctx)

theorem inputTargetTree_run (phase : TreeParserMachine.Phase) (data : InputState)
    (regs : InputParserMachine.Registers R) (ctx : ∀ k, List (Γ k)) :
    (inputTargetTree phase data).Run caller (InputParserMachine.treeLabel .target phase)
      data regs ctx := by
  unfold inputTargetTree
  apply InputFinish.Run.prepend caller (inputTreeSegment_run caller .target phase data regs ctx)
  cases returned : (treePhaseFinish .target phase data.toTreeState).result with
  | success => exact inputTargetSuccess_run caller _ _ _
  | failure => exact inputTargetFailure_run caller _ _ _

theorem inputSourceSuccess_run (data : InputState) (regs : InputParserMachine.Registers R)
    (ctx : ∀ k, List (Γ k)) :
    (inputSourceSuccess data).Run caller (InputParserMachine.treeResultLabel .source .success)
      data regs ctx := by
  cases rawEq : data.raw with
  | nil =>
      simp only [inputSourceSuccess, rawEq]
      apply InputFinish.Run.prepend caller (nextLabel := InputParserMachine.phaseLabel .sourceToReverse) (nextData := data)
      · apply InputParserMachine.Runs.one caller (by trivial)
        simpa only [inputCfg, rawEq, InputParserMachine.toReversePhase] using
          (InputParserMachine.separator_step_nil caller .source data.rev data.pending regs
            data.outputs data.fuel data.bitsReverse ctx)
      · exact inputSourceToReverse_run caller _ _ _
  | cons tag raw =>
      simp only [inputSourceSuccess, rawEq]
      split
      · rename_i separator
        subst tag
        apply InputFinish.Run.prepend caller (nextLabel := InputParserMachine.treeLabel .target .init) (nextData := { data with raw := raw })
        · apply InputParserMachine.Runs.one caller (by trivial)
          simpa only [inputCfg, rawEq, InputParserMachine.afterSeparator] using
            (InputParserMachine.separator_step_separator caller .source raw data.rev data.pending regs
              data.outputs data.fuel data.bitsReverse ctx)
        · exact inputTargetTree_run caller _ _ _ _
      · rename_i foreign
        apply InputFinish.Run.prepend caller (nextLabel := InputParserMachine.phaseLabel .sourceToReverse) (nextData := data)
        · apply InputParserMachine.Runs.one caller (by trivial)
          simpa only [inputCfg, rawEq, InputParserMachine.toReversePhase] using
            (InputParserMachine.separator_step_foreign caller .source tag raw data.rev data.pending regs
              data.outputs data.fuel data.bitsReverse ctx foreign)
        · exact inputSourceToReverse_run caller _ _ _

theorem inputSourceTree_run (phase : TreeParserMachine.Phase) (data : InputState)
    (regs : InputParserMachine.Registers R) (ctx : ∀ k, List (Γ k)) :
    (inputSourceTree phase data).Run caller (InputParserMachine.treeLabel .source phase)
      data regs ctx := by
  dsimp only [inputSourceTree]
  cases returned : (treePhaseFinish .source phase data.toTreeState).result with
  | success =>
      apply InputFinish.Run.prepend caller
      · simpa only [returned] using inputTreeSegment_run caller .source phase data regs ctx
      · exact inputSourceSuccess_run caller _ _ _
  | failure =>
      simpa only [InputFinish.Run, returned, InputParserMachine.resultLabel, InputParserMachine.treeResultLabel] using inputTreeSegment_run caller .source phase data regs ctx

theorem inputPhaseFinish_run (phase : InputParserMachine.OwnedLabels) (data : InputState)
    (regs : InputParserMachine.Registers R) (ctx : ∀ k, List (Γ k)) :
    (inputPhaseFinish phase data).Run caller
      (InputParserMachine.ownedLabelEquiv phase).val data regs ctx := by
  cases phase with
  | inl pair =>
      rcases pair with ⟨destination, phase⟩
      cases destination with
      | source => exact inputSourceTree_run caller phase data regs ctx
      | target => exact inputTargetTree_run caller phase data regs ctx
  | inr phase =>
      cases phase with
      | inl destination =>
          cases destination with
          | source => exact inputSourceSuccess_run caller data regs ctx
          | target => exact inputTargetSuccess_run caller data regs ctx
      | inr phase =>
          cases phase with
          | inl token => exact inputTargetFailure_run caller data regs ctx
          | inr phase => exact inputLocalFinish_run caller phase data regs ctx

theorem inputPhaseFinish_iterate (phase : InputParserMachine.OwnedLabels) (data : InputState)
    (regs : InputParserMachine.Registers R) (ctx : ∀ k, List (Γ k)) :
    (InputParserMachine.next caller)^[(inputPhaseFinish phase data).steps]
      (some (inputCfg (some (InputParserMachine.ownedLabelEquiv phase).val) regs data ctx)) =
      some (inputCfg (some (InputParserMachine.resultLabel (inputPhaseFinish phase data).result))
        (InputParserMachine.reset regs) (inputPhaseFinish phase data).data ctx) :=
  (inputPhaseFinish_run caller phase data regs ctx).iterate caller

theorem inputPhaseFinish_owned_prefix (phase : InputParserMachine.OwnedLabels) (data : InputState)
    (regs : InputParserMachine.Registers R) (ctx : ∀ k, List (Γ k))
    (n : Nat) (bound : n < (inputPhaseFinish phase data).steps) :
    ∃ reached, (InputParserMachine.next caller)^[n]
      (some (inputCfg (some (InputParserMachine.ownedLabelEquiv phase).val) regs data ctx)) =
        some reached ∧ InputParserMachine.FullOwned reached.l :=
  (inputPhaseFinish_run caller phase data regs ctx).owned_prefix caller n bound

end InputFullExecution
/-! Constructive full dirty FrontEnd composition. Insert after dirty Input support. -/

inductive FrontEndMask
  | framer
  | decoder
  | input

def FrontEndMask.apply (mask : FrontEndMask) (regs : FrontEndMachine.Registers R) :
    FrontEndMachine.Registers R :=
  match mask with
  | .framer => FrontEndMachine.resetFramer regs
  | .decoder => FrontEndMachine.afterInputDecoder regs
  | .input => ((none, none), regs.2)

def frontEndMaskRegs (masks : List FrontEndMask) (regs : FrontEndMachine.Registers R) :
    FrontEndMachine.Registers R := masks.foldl (fun regs mask => mask.apply regs) regs

structure FrontEndFinish where
  result : TreeParserMachine.Result
  data : FrontEndMachine.LocalData
  steps : Nat
  masks : List FrontEndMask

def frontEndJoin (before after : FrontEndFinish) : FrontEndFinish :=
  { after with steps := before.steps + after.steps, masks := before.masks ++ after.masks }

def frontEndResultLabel (result : TreeParserMachine.Result) : FrontEndMachine.Label Λ :=
  match result with
  | .success => FrontEndMachine.dispatchLabel
  | .failure => FrontEndMachine.rejectLabel

def frontEndFinishCfg (finish : FrontEndFinish) (regs : FrontEndMachine.Registers R)
    (ctx : ∀ k, List (Γ k)) : FrontEndMachine.Cfg Γ Λ R :=
  FrontEndMachine.cfg (some (frontEndResultLabel finish.result))
    (frontEndMaskRegs finish.masks regs) finish.data ctx

def frontEndInputData (data : FrontEndMachine.LocalData) : InputState :=
  { raw := data.inputRaw
    rev := data.treeReverse
    pending := data.pending
    outputs := InputParserMachine.treeOutputs data.sourceTree data.targetTree
    fuel := data.fuel
    bitsReverse := data.bitsReverse }

def frontEndWithInput (data : FrontEndMachine.LocalData) (input : InputState) :
    FrontEndMachine.LocalData :=
  { data with
    inputRaw := input.raw
    treeReverse := input.rev
    pending := input.pending
    sourceTree := input.outputs .source
    targetTree := input.outputs .target
    fuel := input.fuel
    bitsReverse := input.bitsReverse }

def frontEndInputStage (phase : InputParserMachine.OwnedLabels)
    (data : FrontEndMachine.LocalData) : FrontEndFinish :=
  let finish := inputPhaseFinish phase (frontEndInputData data)
  ⟨finish.result, frontEndWithInput data finish.data, finish.steps, [.input]⟩

def frontEndDecoderRaw (call : FrontEndMachine.DecoderCall) (data : FrontEndMachine.LocalData) : Bits :=
  match call with
  | .input => data.inputBits
  | .certificate => data.certificateBits

def frontEndDecoderOutput (call : FrontEndMachine.DecoderCall) (data : FrontEndMachine.LocalData) : Word :=
  match call with
  | .input => data.inputRaw
  | .certificate => data.certificateWord

def frontEndWithDecoder (call : FrontEndMachine.DecoderCall) (data : FrontEndMachine.LocalData)
    (raw : Bits) (rev out : Word) : FrontEndMachine.LocalData :=
  match call with
  | .input => { data with inputBits := raw, decodeReverse := rev, inputRaw := out }
  | .certificate => { data with certificateBits := raw, decodeReverse := rev, certificateWord := out }

def frontEndDecoderStage (call : FrontEndMachine.DecoderCall) (phase : OpenDecoderMachine.Phase)
    (data : FrontEndMachine.LocalData) : FrontEndFinish :=
  let raw := frontEndDecoderRaw call data
  let rev := data.decodeReverse
  let out := frontEndDecoderOutput call data
  let steps := OpenDecoderMachine.phaseSteps phase raw rev
  match phase with
  | .emit => ⟨.success, frontEndWithDecoder call data raw [] (rev.reverse ++ out), steps, [.decoder]⟩
  | .clear => ⟨.failure, frontEndWithDecoder call data raw [] out, steps, [.decoder]⟩
  | .scan => match (unpackWordRun raw).1 with
    | none => ⟨.failure, frontEndWithDecoder call data [] [] out, steps, [.decoder]⟩
    | some word =>
        ⟨.success, frontEndWithDecoder call data [] [] (rev.reverse ++ word ++ out), steps, [.decoder]⟩

def frontEndFramerStage (phase : OpenFramingMachine.Phase) (data : FrontEndMachine.LocalData) :
    FrontEndFinish :=
  let steps := OpenFramingMachine.phaseSteps phase data.framedRaw
    data.frameFirstReverse data.frameCertReverse
  match phase with
  | .emitFirst => ⟨.success, { data with
      frameFirstReverse := []
      inputBits := data.frameFirstReverse.reverse ++ data.inputBits }, steps, [.framer]⟩
  | .clearFirst => ⟨.failure, { data with frameFirstReverse := [] }, steps, [.framer]⟩
  | .emitCert => ⟨.success, { data with
      frameFirstReverse := []
      frameCertReverse := []
      inputBits := data.frameFirstReverse.reverse ++ data.inputBits
      certificateBits := data.frameCertReverse.reverse ++ data.certificateBits }, steps, [.framer]⟩
  | .copyCert => ⟨.success, { data with
      framedRaw := []
      frameFirstReverse := []
      frameCertReverse := []
      inputBits := data.frameFirstReverse.reverse ++ data.inputBits
      certificateBits := data.frameCertReverse.reverse ++ data.framedRaw ++ data.certificateBits },
      steps, [.framer]⟩
  | .scanPrefix => match BitPairFraming.unframe data.framedRaw with
    | none => ⟨.failure, { data with framedRaw := [], frameFirstReverse := [] }, steps, [.framer]⟩
    | some pair => ⟨.success, { data with
        framedRaw := []
        frameFirstReverse := []
        frameCertReverse := []
        inputBits := data.frameFirstReverse.reverse ++ pair.1 ++ data.inputBits
        certificateBits := data.frameCertReverse.reverse ++ pair.2 ++ data.certificateBits },
        steps, [.framer]⟩

def frontEndCertificateFinish (phase : OpenDecoderMachine.Phase)
    (data : FrontEndMachine.LocalData) : FrontEndFinish :=
  frontEndDecoderStage .certificate phase data

def frontEndInputFinish (phase : InputParserMachine.OwnedLabels)
    (data : FrontEndMachine.LocalData) : FrontEndFinish :=
  let parsed := frontEndInputStage phase data
  match parsed.result with
  | .failure => parsed
  | .success => frontEndJoin parsed (frontEndCertificateFinish .scan parsed.data)

def frontEndInputDecoderFinish (phase : OpenDecoderMachine.Phase)
    (data : FrontEndMachine.LocalData) : FrontEndFinish :=
  let decoded := frontEndDecoderStage .input phase data
  match decoded.result with
  | .failure => decoded
  | .success => frontEndJoin decoded (frontEndInputFinish (.inl (.source, .init)) decoded.data)

def frontEndFramerFinish (phase : OpenFramingMachine.Phase)
    (data : FrontEndMachine.LocalData) : FrontEndFinish :=
  let framed := frontEndFramerStage phase data
  match framed.result with
  | .failure => framed
  | .success => frontEndJoin framed (frontEndInputDecoderFinish .scan framed.data)

def frontEndPhaseFinish (phase : FrontEndMachine.OwnedLabels)
    (data : FrontEndMachine.LocalData) : FrontEndFinish :=
  match phase with
  | .inl phase => frontEndInputFinish phase data
  | .inr (.inl phase) => frontEndFramerFinish phase data
  | .inr (.inr (.inl phase)) => frontEndInputDecoderFinish phase data
  | .inr (.inr (.inr phase)) => frontEndCertificateFinish phase data

def frontEndPhaseSteps (phase : FrontEndMachine.OwnedLabels)
    (data : FrontEndMachine.LocalData) : Nat := (frontEndPhaseFinish phase data).steps

def frontEndPhaseResult (phase : FrontEndMachine.OwnedLabels)
    (regs : FrontEndMachine.Registers R) (data : FrontEndMachine.LocalData)
    (ctx : ∀ k, List (Γ k)) : FrontEndMachine.Cfg Γ Λ R :=
  frontEndFinishCfg (frontEndPhaseFinish phase data) regs ctx

def frontEndStageCfg (success : FrontEndMachine.Label Λ) (finish : FrontEndFinish)
    (regs : FrontEndMachine.Registers R) (ctx : ∀ k, List (Γ k)) : FrontEndMachine.Cfg Γ Λ R :=
  FrontEndMachine.cfg (some (match finish.result with
    | .success => success
    | .failure => FrontEndMachine.rejectLabel))
    (frontEndMaskRegs finish.masks regs) finish.data ctx

def frontEndFramerResult : TreeParserMachine.Result → OpenFramingMachine.Result
  | .success => .success
  | .failure => .failure

def frontEndDecoderResult : TreeParserMachine.Result → OpenDecoderMachine.Result
  | .success => .success
  | .failure => .failure

@[simp] theorem frontEndDecoderRaw_with (call : FrontEndMachine.DecoderCall)
    (data : FrontEndMachine.LocalData) (raw : Bits) (rev out : Word) :
    frontEndDecoderRaw call (frontEndWithDecoder call data raw rev out) = raw := by
  cases call <;> rfl

@[simp] theorem frontEndDecoderOutput_with (call : FrontEndMachine.DecoderCall)
    (data : FrontEndMachine.LocalData) (raw : Bits) (rev out : Word) :
    frontEndDecoderOutput call (frontEndWithDecoder call data raw rev out) = out := by
  cases call <;> rfl

@[simp] theorem frontEndDecoderReverse_with (call : FrontEndMachine.DecoderCall)
    (data : FrontEndMachine.LocalData) (raw : Bits) (rev out : Word) :
    (frontEndWithDecoder call data raw rev out).decodeReverse = rev := by
  cases call <;> rfl

@[simp] theorem frontEndDecoderContext_with (call : FrontEndMachine.DecoderCall)
    (data : FrontEndMachine.LocalData) (raw : Bits) (rev out : Word) (ctx : ∀ k, List (Γ k)) :
    FrontEndMachine.decoderContext call (frontEndWithDecoder call data raw rev out) ctx =
      FrontEndMachine.decoderContext call data ctx := by
  cases call <;> rfl

@[simp] theorem frontEndInputContext_with (data : FrontEndMachine.LocalData) (input : InputState)
    (ctx : ∀ k, List (Γ k)) :
    FrontEndMachine.inputContext (frontEndWithInput data input) ctx =
      FrontEndMachine.inputContext data ctx := rfl

theorem frontEndInput_outputs (input : InputState) :
    InputParserMachine.treeOutputs (input.outputs .source) (input.outputs .target) = input.outputs := by
  funext side
  cases side <;> rfl

theorem frontEndFramerStage_context (phase : OpenFramingMachine.Phase)
    (data : FrontEndMachine.LocalData) (ctx : ∀ k, List (Γ k)) :
    FrontEndMachine.framerContext (frontEndFramerStage phase data).data ctx =
      FrontEndMachine.framerContext data ctx := by
  cases phase with
  | scanPrefix =>
      cases returned : BitPairFraming.unframe data.framedRaw <;>
        simp only [frontEndFramerStage, returned]
      all_goals
        funext slot
        cases slot with
        | inl slot => cases slot <;> rfl
        | inr k => rfl
  | copyCert => rfl
  | emitCert => rfl
  | emitFirst => rfl
  | clearFirst => rfl

theorem frontEndDecoderRegister_reset (regs : FrontEndMachine.Registers R) :
    FrontEndMachine.decoderRegisterEquiv
        (OpenDecoderMachine.reset (FrontEndMachine.decoderRegisterEquiv.symm regs)) =
      FrontEndMachine.afterInputDecoder regs := by
  rcases regs with ⟨tree, decoder, user⟩
  rfl

section FrontEndExecution
variable [DecidableEq K]
variable (caller : FrontEndMachine.External Λ → FrontEndMachine.Statement Γ Λ R)

theorem framer_trace_transport
    (localCaller : OpenFramingMachine.External (FrontEndMachine.FramerCaller Λ) →
      FrontEndMachine.FramerStatement Γ Λ R)
    {start finish : FrontEndMachine.FramerCfg Γ Λ R} {n : Nat}
    (executed : (OpenFramingMachine.next localCaller)^[n] (some start) = some finish)
    (owned : ∀ j, j < n → ∃ reached,
      (OpenFramingMachine.next localCaller)^[j] (some start) = some reached ∧
        OpenFramingMachine.Owned reached.l) :
    FrontEndMachine.Trace caller (FrontEndMachine.framerCfg start)
      (FrontEndMachine.framerCfg finish) n := by
  refine ⟨?_, ?_⟩
  · rw [FrontEndMachine.framer_prefix_installed caller localCaller n start owned, executed]
    rfl
  · intro j strict
    obtain ⟨reached, reachedEq, isOwned⟩ := owned j strict
    refine ⟨FrontEndMachine.framerCfg reached, ?_, FrontEndMachine.owned_framerCfg reached isOwned⟩
    rw [FrontEndMachine.framer_prefix_installed caller localCaller j start
      (fun k smaller => owned k (by omega)), reachedEq]
    rfl

theorem input_trace_transport
    (localCaller : InputParserMachine.External (FrontEndMachine.ExtraLabel Λ) →
      FrontEndMachine.InputStatement Γ Λ R)
    {start finish : FrontEndMachine.InputCfg Γ Λ R} {n : Nat}
    (run : InputParserMachine.Runs localCaller n start finish) :
    FrontEndMachine.Trace caller (FrontEndMachine.inputCfg start)
      (FrontEndMachine.inputCfg finish) n := by
  refine ⟨?_, ?_⟩
  · rw [FrontEndMachine.input_prefix_installed caller localCaller n start
      (run.owned_prefix localCaller), run.iterate localCaller]
    rfl
  · intro j strict
    obtain ⟨reached, reachedEq, isOwned⟩ := run.owned_prefix localCaller j strict
    refine ⟨FrontEndMachine.inputCfg reached, ?_, FrontEndMachine.owned_inputCfg reached isOwned⟩
    rw [FrontEndMachine.input_prefix_installed caller localCaller j start
      (fun k smaller => run.owned_prefix localCaller k (by omega)), reachedEq]
    rfl

theorem inputDecoder_trace_transport
    (localCaller : OpenDecoderMachine.External (FrontEndMachine.InputDecoderCaller Λ) →
      FrontEndMachine.InputDecoderStatement Γ Λ R)
    {start finish : FrontEndMachine.InputDecoderCfg Γ Λ R} {n : Nat}
    (executed : (OpenDecoderMachine.next localCaller)^[n] (some start) = some finish)
    (owned : ∀ j, j < n → ∃ reached,
      (OpenDecoderMachine.next localCaller)^[j] (some start) = some reached ∧
        OpenDecoderMachine.Owned reached.l) :
    FrontEndMachine.Trace caller (FrontEndMachine.inputDecoderCfg start)
      (FrontEndMachine.inputDecoderCfg finish) n := by
  refine ⟨?_, ?_⟩
  · rw [FrontEndMachine.inputDecoder_prefix_installed caller localCaller n start owned, executed]
    rfl
  · intro j strict
    obtain ⟨reached, reachedEq, isOwned⟩ := owned j strict
    refine ⟨FrontEndMachine.inputDecoderCfg reached, ?_, FrontEndMachine.owned_inputDecoderCfg reached isOwned⟩
    rw [FrontEndMachine.inputDecoder_prefix_installed caller localCaller j start
      (fun k smaller => owned k (by omega)), reachedEq]
    rfl

theorem certificateDecoder_trace_transport
    (localCaller : OpenDecoderMachine.External (FrontEndMachine.CertificateDecoderCaller Λ) →
      FrontEndMachine.CertificateDecoderStatement Γ Λ R)
    {start finish : FrontEndMachine.CertificateDecoderCfg Γ Λ R} {n : Nat}
    (executed : (OpenDecoderMachine.next localCaller)^[n] (some start) = some finish)
    (owned : ∀ j, j < n → ∃ reached,
      (OpenDecoderMachine.next localCaller)^[j] (some start) = some reached ∧
        OpenDecoderMachine.Owned reached.l) :
    FrontEndMachine.Trace caller (FrontEndMachine.certificateDecoderCfg start)
      (FrontEndMachine.certificateDecoderCfg finish) n := by
  refine ⟨?_, ?_⟩
  · rw [FrontEndMachine.certificateDecoder_prefix_installed caller localCaller n start owned, executed]
    rfl
  · intro j strict
    obtain ⟨reached, reachedEq, isOwned⟩ := owned j strict
    refine ⟨FrontEndMachine.certificateDecoderCfg reached, ?_,
      FrontEndMachine.owned_certificateDecoderCfg reached isOwned⟩
    rw [FrontEndMachine.certificateDecoder_prefix_installed caller localCaller j start
      (fun k smaller => owned k (by omega)), reachedEq]
    rfl

omit caller in
theorem frontEndFramerStage_component_iterate
    (localCaller : OpenFramingMachine.External (FrontEndMachine.FramerCaller Λ) →
      FrontEndMachine.FramerStatement Γ Λ R)
    (phase : OpenFramingMachine.Phase) (data : FrontEndMachine.LocalData)
    (regs : OpenFramingMachine.Registers (FrontEndMachine.FramerRegisterCaller R))
    (ctx : ∀ k, List (Γ k)) :
    (OpenFramingMachine.next localCaller)^[(frontEndFramerStage phase data).steps]
      (some (FrontEndMachine.framerView (some (OpenFramingMachine.phaseLabel phase)) regs data ctx)) =
      some (FrontEndMachine.framerView (some (OpenFramingMachine.resultLabel
        (frontEndFramerResult (frontEndFramerStage phase data).result)))
        (OpenFramingMachine.reset regs) (frontEndFramerStage phase data).data ctx) := by
  simp only [FrontEndMachine.framerView, frontEndFramerStage_context]
  cases phase with
  | scanPrefix =>
      have run := OpenFramingMachine.scanPrefix_iterate localCaller data.framedRaw
        data.frameFirstReverse data.frameCertReverse data.inputBits data.certificateBits regs
        (FrontEndMachine.framerContext data ctx)
      cases returned : BitPairFraming.unframe data.framedRaw <;>
        simpa only [frontEndFramerStage, OpenFramingMachine.phaseSteps,
          OpenFramingMachine.scanResult, returned, frontEndFramerResult] using run
  | copyCert =>
      exact OpenFramingMachine.copyCert_iterate localCaller data.framedRaw
        data.frameFirstReverse data.frameCertReverse data.inputBits data.certificateBits regs
        (FrontEndMachine.framerContext data ctx)
  | emitCert =>
      exact OpenFramingMachine.emitCert_iterate localCaller data.framedRaw
        data.frameFirstReverse data.frameCertReverse data.inputBits data.certificateBits regs
        (FrontEndMachine.framerContext data ctx)
  | emitFirst =>
      exact OpenFramingMachine.emitFirst_iterate localCaller data.framedRaw
        data.frameFirstReverse data.frameCertReverse data.inputBits data.certificateBits regs
        (FrontEndMachine.framerContext data ctx)
  | clearFirst =>
      exact OpenFramingMachine.clearFirst_iterate localCaller data.framedRaw
        data.frameFirstReverse data.frameCertReverse data.inputBits data.certificateBits regs
        (FrontEndMachine.framerContext data ctx)

omit caller in
theorem frontEndDecoderStage_component_iterate {ExternalLabel : Type}
    (localCaller : OpenDecoderMachine.External ExternalLabel →
      OpenDecoderMachine.Statement (FrontEndMachine.decoderProtectedAlphabet Γ) ExternalLabel
        (FrontEndMachine.DecoderRegisterCaller R))
    (call : FrontEndMachine.DecoderCall) (phase : OpenDecoderMachine.Phase)
    (data : FrontEndMachine.LocalData)
    (regs : OpenDecoderMachine.Registers (FrontEndMachine.DecoderRegisterCaller R))
    (ctx : ∀ k, List (Γ k)) :
    (OpenDecoderMachine.next localCaller)^[(frontEndDecoderStage call phase data).steps]
      (some (OpenDecoderMachine.cfg (some (OpenDecoderMachine.phaseLabel phase)) regs
        (frontEndDecoderRaw call data) data.decodeReverse (frontEndDecoderOutput call data)
        (FrontEndMachine.decoderContext call data ctx))) =
      some (OpenDecoderMachine.cfg (some (OpenDecoderMachine.resultLabel
        (frontEndDecoderResult (frontEndDecoderStage call phase data).result)))
        (OpenDecoderMachine.reset regs)
        (frontEndDecoderRaw call (frontEndDecoderStage call phase data).data)
        (frontEndDecoderStage call phase data).data.decodeReverse
        (frontEndDecoderOutput call (frontEndDecoderStage call phase data).data)
        (FrontEndMachine.decoderContext call (frontEndDecoderStage call phase data).data ctx)) := by
  cases phase with
  | scan =>
      have run := OpenDecoderMachine.scan_iterate localCaller (frontEndDecoderRaw call data)
        data.decodeReverse (frontEndDecoderOutput call data) regs
        (FrontEndMachine.decoderContext call data ctx)
      cases returned : (unpackWordRun (frontEndDecoderRaw call data)).1 <;>
        simpa only [frontEndDecoderStage, OpenDecoderMachine.phaseSteps, returned,
          OpenDecoderMachine.resultCfg, frontEndDecoderResult, frontEndDecoderRaw_with,
          frontEndDecoderOutput_with, frontEndDecoderReverse_with, frontEndDecoderContext_with] using run
  | emit =>
      simpa only [frontEndDecoderStage, OpenDecoderMachine.phaseSteps, frontEndDecoderResult,
        frontEndDecoderRaw_with, frontEndDecoderOutput_with, frontEndDecoderReverse_with,
        frontEndDecoderContext_with] using
        OpenDecoderMachine.emit_iterate localCaller data.decodeReverse (frontEndDecoderRaw call data)
          (frontEndDecoderOutput call data) regs (FrontEndMachine.decoderContext call data ctx)
  | clear =>
      simpa only [frontEndDecoderStage, OpenDecoderMachine.phaseSteps, frontEndDecoderResult,
        frontEndDecoderRaw_with, frontEndDecoderOutput_with, frontEndDecoderReverse_with,
        frontEndDecoderContext_with] using
        OpenDecoderMachine.clear_iterate localCaller data.decodeReverse (frontEndDecoderRaw call data)
          (frontEndDecoderOutput call data) regs (FrontEndMachine.decoderContext call data ctx)

end FrontEndExecution

theorem frontEndFramerStage_steps (phase : OpenFramingMachine.Phase)
    (data : FrontEndMachine.LocalData) :
    (frontEndFramerStage phase data).steps = OpenFramingMachine.phaseSteps phase
      data.framedRaw data.frameFirstReverse data.frameCertReverse := by
  cases phase <;> simp only [frontEndFramerStage]
  split <;> rfl

theorem frontEndFramerStage_masks (phase : OpenFramingMachine.Phase)
    (data : FrontEndMachine.LocalData) : (frontEndFramerStage phase data).masks = [.framer] := by
  cases phase <;> simp only [frontEndFramerStage]
  split <;> rfl

theorem frontEndDecoderStage_steps (call : FrontEndMachine.DecoderCall)
    (phase : OpenDecoderMachine.Phase) (data : FrontEndMachine.LocalData) :
    (frontEndDecoderStage call phase data).steps =
      OpenDecoderMachine.phaseSteps phase (frontEndDecoderRaw call data) data.decodeReverse := by
  cases phase <;> simp only [frontEndDecoderStage]
  split <;> rfl

theorem frontEndDecoderStage_masks (call : FrontEndMachine.DecoderCall)
    (phase : OpenDecoderMachine.Phase) (data : FrontEndMachine.LocalData) :
    (frontEndDecoderStage call phase data).masks = [.decoder] := by
  cases phase <;> simp only [frontEndDecoderStage]
  split <;> rfl

theorem frontEndFramerResult_label (r : TreeParserMachine.Result) :
    FrontEndMachine.framerLabelEquiv
      (OpenFramingMachine.resultLabel (Λ := FrontEndMachine.FramerCaller Λ) (frontEndFramerResult r)) =
    (match r with
      | .success => FrontEndMachine.inputDecoderLabel .scan
      | .failure => FrontEndMachine.rejectLabel) := by
  cases r <;> rfl

theorem frontEndInputDecoderResult_label (r : TreeParserMachine.Result) :
    FrontEndMachine.inputDecoderLabelEquiv
      (OpenDecoderMachine.resultLabel (Λ := FrontEndMachine.InputDecoderCaller Λ) (frontEndDecoderResult r)) =
    (match r with
      | .success => InputParserMachine.treeLabel .source .init
      | .failure => FrontEndMachine.rejectLabel) := by
  cases r <;> rfl

theorem frontEndCertificateDecoderResult_label (r : TreeParserMachine.Result) :
    FrontEndMachine.certificateDecoderLabelEquiv
      (OpenDecoderMachine.resultLabel (Λ := FrontEndMachine.CertificateDecoderCaller Λ) (frontEndDecoderResult r)) =
    frontEndResultLabel (Λ := Λ) r := by
  cases r <;> rfl

theorem frontEndInputResult_label (r : TreeParserMachine.Result) :
    FrontEndMachine.inputLabelEquiv (InputParserMachine.resultLabel (Λ := FrontEndMachine.ExtraLabel Λ) r) =
    (match r with
      | .success => FrontEndMachine.certificateDecoderLabel .scan
      | .failure => FrontEndMachine.rejectLabel) := by
  cases r <;> rfl

theorem frontEndInputOwned_label (phase : InputParserMachine.OwnedLabels) :
    FrontEndMachine.inputLabelEquiv
      (InputParserMachine.ownedLabelEquiv (Λ := FrontEndMachine.ExtraLabel Λ) phase).val =
        FrontEndMachine.inputOwnedLabel phase := rfl

section FrontEndStages
variable [DecidableEq K]
variable (caller : FrontEndMachine.External Λ → FrontEndMachine.Statement Γ Λ R)

theorem frontEndFramerStage_trace (phase : OpenFramingMachine.Phase)
    (data : FrontEndMachine.LocalData) (regs : FrontEndMachine.Registers R)
    (ctx : ∀ k, List (Γ k)) :
    FrontEndMachine.Trace caller
      (FrontEndMachine.cfg (some (FrontEndMachine.framerLabel phase)) regs data ctx)
      (frontEndStageCfg (FrontEndMachine.inputDecoderLabel .scan)
        (frontEndFramerStage phase data) regs ctx) (frontEndFramerStage phase data).steps := by
  let localCaller : OpenFramingMachine.External (FrontEndMachine.FramerCaller Λ) →
    FrontEndMachine.FramerStatement Γ Λ R := fun _ => .halt
  let localRegs := FrontEndMachine.framerRegisterEquiv.symm regs
  have executed := frontEndFramerStage_component_iterate localCaller phase data localRegs ctx
  have within : ∀ n, n < (frontEndFramerStage phase data).steps → ∃ reached,
      (OpenFramingMachine.next localCaller)^[n]
        (some (FrontEndMachine.framerView (some (OpenFramingMachine.phaseLabel phase)) localRegs data ctx)) =
          some reached ∧ OpenFramingMachine.Owned reached.l := by
    intro n strict
    rw [frontEndFramerStage_steps] at strict
    obtain ⟨reached, reachedEq, _, _, owned, _⟩ := OpenFramingMachine.phase_prefix localCaller
      phase data.framedRaw data.frameFirstReverse data.frameCertReverse data.inputBits
      data.certificateBits localRegs (FrontEndMachine.framerContext data ctx) n (Nat.le_of_lt strict)
    exact ⟨reached, reachedEq, owned.mp strict⟩
  have translated := framer_trace_transport caller localCaller executed within
  rw [FrontEndMachine.framerCfg_view, FrontEndMachine.framerCfg_view] at translated
  simpa only [Option.map_some, FrontEndMachine.framerLabelEquiv_phase, localRegs,
    Equiv.apply_symm_apply, frontEndFramerResult_label, FrontEndMachine.framerRegisterEquiv_reset,
    frontEndStageCfg, frontEndFramerStage_masks, frontEndMaskRegs, List.foldl_cons, List.foldl_nil,
    FrontEndMask.apply] using translated

theorem frontEndInputStage_trace (phase : InputParserMachine.OwnedLabels)
    (data : FrontEndMachine.LocalData) (regs : FrontEndMachine.Registers R)
    (ctx : ∀ k, List (Γ k)) :
    FrontEndMachine.Trace caller
      (FrontEndMachine.cfg (some (FrontEndMachine.inputOwnedLabel phase)) regs data ctx)
      (frontEndStageCfg (FrontEndMachine.certificateDecoderLabel .scan)
        (frontEndInputStage phase data) regs ctx) (frontEndInputStage phase data).steps := by
  let localCaller : InputParserMachine.External (FrontEndMachine.ExtraLabel Λ) →
    FrontEndMachine.InputStatement Γ Λ R := fun _ => .halt
  let finish := inputPhaseFinish phase (frontEndInputData data)
  have run := inputPhaseFinish_run localCaller phase (frontEndInputData data) regs
    (FrontEndMachine.inputContext data ctx)
  change InputParserMachine.Runs localCaller finish.steps
    (FrontEndMachine.inputView (some (InputParserMachine.ownedLabelEquiv phase).val) regs data ctx)
    (inputCfg (some (InputParserMachine.resultLabel finish.result))
      (InputParserMachine.reset regs) finish.data (FrontEndMachine.inputContext data ctx)) at run
  have endpoint : inputCfg (some (InputParserMachine.resultLabel (Λ := FrontEndMachine.ExtraLabel Λ) finish.result))
      (InputParserMachine.reset regs) finish.data (FrontEndMachine.inputContext data ctx) =
      FrontEndMachine.inputView (some (InputParserMachine.resultLabel finish.result))
        (InputParserMachine.reset regs) (frontEndWithInput data finish.data) ctx := by
    simp only [inputCfg, FrontEndMachine.inputView, frontEndWithInput, frontEndInput_outputs]
    rfl
  rw [endpoint] at run
  have translated := input_trace_transport caller localCaller run
  rw [FrontEndMachine.inputCfg_view, FrontEndMachine.inputCfg_view] at translated
  simpa only [Option.map_some, frontEndInputResult_label, frontEndInputOwned_label,
    frontEndStageCfg, frontEndInputStage,
    frontEndMaskRegs, List.foldl_cons, List.foldl_nil, FrontEndMask.apply,
    FrontEndMachine.inputRegisterEquiv, Equiv.refl_apply,
    InputParserMachine.reset, TreeParserMachine.reset, finish] using translated


 theorem frontEndInputDecoderStage_trace (phase : OpenDecoderMachine.Phase)
    (data : FrontEndMachine.LocalData) (regs : FrontEndMachine.Registers R)
    (ctx : ∀ k, List (Γ k)) :
    FrontEndMachine.Trace caller
      (FrontEndMachine.cfg (some (FrontEndMachine.inputDecoderLabel phase)) regs data ctx)
      (frontEndStageCfg (InputParserMachine.treeLabel .source .init)
        (frontEndDecoderStage .input phase data) regs ctx) (frontEndDecoderStage .input phase data).steps := by
  let localCaller : OpenDecoderMachine.External (FrontEndMachine.InputDecoderCaller Λ) →
    FrontEndMachine.InputDecoderStatement Γ Λ R := fun _ => .halt
  let localRegs := FrontEndMachine.decoderRegisterEquiv.symm regs
  have executed := frontEndDecoderStage_component_iterate localCaller .input phase data localRegs ctx
  have within : ∀ n, n < (frontEndDecoderStage .input phase data).steps → ∃ reached,
      (OpenDecoderMachine.next localCaller)^[n]
        (some (FrontEndMachine.inputDecoderView (some (OpenDecoderMachine.phaseLabel phase)) localRegs data ctx)) =
          some reached ∧ OpenDecoderMachine.Owned reached.l := by
    intro n strict
    rw [frontEndDecoderStage_steps] at strict
    obtain ⟨reached, reachedEq, _, _, owned, _⟩ := OpenDecoderMachine.phase_prefix localCaller
      phase (frontEndDecoderRaw .input data) data.decodeReverse (frontEndDecoderOutput .input data)
      localRegs (FrontEndMachine.decoderContext .input data ctx) n (Nat.le_of_lt strict)
    exact ⟨reached, reachedEq, owned.mp strict⟩
  have translated := inputDecoder_trace_transport caller localCaller executed within
  change FrontEndMachine.Trace caller
    (FrontEndMachine.inputDecoderCfg (FrontEndMachine.inputDecoderView
      (some (OpenDecoderMachine.phaseLabel phase)) localRegs data ctx))
    (FrontEndMachine.inputDecoderCfg (FrontEndMachine.inputDecoderView
      (some (OpenDecoderMachine.resultLabel (frontEndDecoderResult
        (frontEndDecoderStage .input phase data).result)))
      (OpenDecoderMachine.reset localRegs) (frontEndDecoderStage .input phase data).data ctx))
    (frontEndDecoderStage .input phase data).steps at translated
  rw [FrontEndMachine.inputDecoderCfg_view, FrontEndMachine.inputDecoderCfg_view] at translated
  simpa only [Option.map_some, FrontEndMachine.inputDecoderLabelEquiv_phase, localRegs,
    Equiv.apply_symm_apply, frontEndInputDecoderResult_label, frontEndStageCfg,
    frontEndDecoderRegister_reset, frontEndDecoderStage_masks, frontEndMaskRegs,
    List.foldl_cons, List.foldl_nil, FrontEndMask.apply, FrontEndMachine.afterInputDecoder] using translated

 theorem frontEndCertificateDecoderStage_trace (phase : OpenDecoderMachine.Phase)
    (data : FrontEndMachine.LocalData) (regs : FrontEndMachine.Registers R)
    (ctx : ∀ k, List (Γ k)) :
    FrontEndMachine.Trace caller
      (FrontEndMachine.cfg (some (FrontEndMachine.certificateDecoderLabel phase)) regs data ctx)
      (frontEndFinishCfg (frontEndDecoderStage .certificate phase data) regs ctx) (frontEndDecoderStage .certificate phase data).steps := by
  let localCaller : OpenDecoderMachine.External (FrontEndMachine.CertificateDecoderCaller Λ) →
    FrontEndMachine.CertificateDecoderStatement Γ Λ R := fun _ => .halt
  let localRegs := FrontEndMachine.decoderRegisterEquiv.symm regs
  have executed := frontEndDecoderStage_component_iterate localCaller .certificate phase data localRegs ctx
  have within : ∀ n, n < (frontEndDecoderStage .certificate phase data).steps → ∃ reached,
      (OpenDecoderMachine.next localCaller)^[n]
        (some (FrontEndMachine.certificateDecoderView (some (OpenDecoderMachine.phaseLabel phase)) localRegs data ctx)) =
          some reached ∧ OpenDecoderMachine.Owned reached.l := by
    intro n strict
    rw [frontEndDecoderStage_steps] at strict
    obtain ⟨reached, reachedEq, _, _, owned, _⟩ := OpenDecoderMachine.phase_prefix localCaller
      phase (frontEndDecoderRaw .certificate data) data.decodeReverse (frontEndDecoderOutput .certificate data)
      localRegs (FrontEndMachine.decoderContext .certificate data ctx) n (Nat.le_of_lt strict)
    exact ⟨reached, reachedEq, owned.mp strict⟩
  have translated := certificateDecoder_trace_transport caller localCaller executed within
  change FrontEndMachine.Trace caller
    (FrontEndMachine.certificateDecoderCfg (FrontEndMachine.certificateDecoderView
      (some (OpenDecoderMachine.phaseLabel phase)) localRegs data ctx))
    (FrontEndMachine.certificateDecoderCfg (FrontEndMachine.certificateDecoderView
      (some (OpenDecoderMachine.resultLabel (frontEndDecoderResult
        (frontEndDecoderStage .certificate phase data).result)))
      (OpenDecoderMachine.reset localRegs) (frontEndDecoderStage .certificate phase data).data ctx))
    (frontEndDecoderStage .certificate phase data).steps at translated
  rw [FrontEndMachine.certificateDecoderCfg_view, FrontEndMachine.certificateDecoderCfg_view] at translated
  simpa only [Option.map_some, FrontEndMachine.certificateDecoderLabelEquiv_phase, localRegs,
    Equiv.apply_symm_apply, frontEndCertificateDecoderResult_label, frontEndFinishCfg,
    frontEndDecoderRegister_reset, frontEndDecoderStage_masks, frontEndMaskRegs,
    List.foldl_cons, List.foldl_nil, FrontEndMask.apply, FrontEndMachine.afterInputDecoder] using translated

end FrontEndStages

theorem frontEndMaskRegs_append (first second : List FrontEndMask)
    (regs : FrontEndMachine.Registers R) :
    frontEndMaskRegs (first ++ second) regs = frontEndMaskRegs second (frontEndMaskRegs first regs) :=
  List.foldl_append

theorem frontEndFinishCfg_join (before after : FrontEndFinish) (regs : FrontEndMachine.Registers R)
    (ctx : ∀ k, List (Γ k)) :
    frontEndFinishCfg (Λ := Λ) (frontEndJoin before after) regs ctx =
      frontEndFinishCfg after (frontEndMaskRegs before.masks regs) ctx := by
  simp only [frontEndFinishCfg, frontEndJoin, frontEndMaskRegs_append]

theorem frontEndJoin_steps (before after : FrontEndFinish) :
    (frontEndJoin before after).steps = before.steps + after.steps := rfl

theorem frontEndFinishCfg_not_owned (finish : FrontEndFinish) (regs : FrontEndMachine.Registers R)
    (ctx : ∀ k, List (Γ k)) :
    ¬ FrontEndMachine.Owned (frontEndFinishCfg (Λ := Λ) finish regs ctx).l := by
  change ¬ FrontEndMachine.Owned (some (frontEndResultLabel finish.result))
  cases finish.result with
  | success => exact FrontEndMachine.not_owned_dispatch
  | failure => exact FrontEndMachine.not_owned_reject

section FrontEndComplete
variable [DecidableEq K]
variable (caller : FrontEndMachine.External Λ → FrontEndMachine.Statement Γ Λ R)

theorem frontEndInputFinish_trace (phase : InputParserMachine.OwnedLabels)
    (data : FrontEndMachine.LocalData) (regs : FrontEndMachine.Registers R)
    (ctx : ∀ k, List (Γ k)) :
    FrontEndMachine.Trace caller
      (FrontEndMachine.cfg (some (FrontEndMachine.inputOwnedLabel phase)) regs data ctx)
      (frontEndFinishCfg (frontEndInputFinish phase data) regs ctx)
      (frontEndInputFinish phase data).steps := by
  have first := frontEndInputStage_trace caller phase data regs ctx
  dsimp only [frontEndInputFinish]
  cases returned : (frontEndInputStage phase data).result with
  | failure =>
      simpa only [frontEndStageCfg, frontEndFinishCfg, returned, frontEndResultLabel] using first
  | success =>
      have first' : FrontEndMachine.Trace caller
          (FrontEndMachine.cfg (some (FrontEndMachine.inputOwnedLabel phase)) regs data ctx)
          (FrontEndMachine.cfg (some (FrontEndMachine.certificateDecoderLabel .scan))
            (frontEndMaskRegs (frontEndInputStage phase data).masks regs)
            (frontEndInputStage phase data).data ctx) (frontEndInputStage phase data).steps := by
        simpa only [frontEndStageCfg, returned] using first
      have last := frontEndCertificateDecoderStage_trace caller .scan
        (frontEndInputStage phase data).data (frontEndMaskRegs (frontEndInputStage phase data).masks regs) ctx
      change FrontEndMachine.Trace caller
        (FrontEndMachine.cfg (some (FrontEndMachine.inputOwnedLabel phase)) regs data ctx)
        (frontEndFinishCfg (frontEndJoin (frontEndInputStage phase data)
          (frontEndCertificateFinish .scan (frontEndInputStage phase data).data)) regs ctx)
        ((frontEndInputStage phase data).steps +
          (frontEndCertificateFinish .scan (frontEndInputStage phase data).data).steps)
      rw [frontEndFinishCfg_join]
      exact first'.trans caller last

theorem frontEndInputDecoderFinish_trace (phase : OpenDecoderMachine.Phase)
    (data : FrontEndMachine.LocalData) (regs : FrontEndMachine.Registers R)
    (ctx : ∀ k, List (Γ k)) :
    FrontEndMachine.Trace caller
      (FrontEndMachine.cfg (some (FrontEndMachine.inputDecoderLabel phase)) regs data ctx)
      (frontEndFinishCfg (frontEndInputDecoderFinish phase data) regs ctx)
      (frontEndInputDecoderFinish phase data).steps := by
  have first := frontEndInputDecoderStage_trace caller phase data regs ctx
  dsimp only [frontEndInputDecoderFinish]
  cases returned : (frontEndDecoderStage .input phase data).result with
  | failure =>
      simpa only [frontEndStageCfg, frontEndFinishCfg, returned, frontEndResultLabel] using first
  | success =>
      have first' : FrontEndMachine.Trace caller
          (FrontEndMachine.cfg (some (FrontEndMachine.inputDecoderLabel phase)) regs data ctx)
          (FrontEndMachine.cfg (some (InputParserMachine.treeLabel .source .init))
            (frontEndMaskRegs (frontEndDecoderStage .input phase data).masks regs)
            (frontEndDecoderStage .input phase data).data ctx)
          (frontEndDecoderStage .input phase data).steps := by
        simpa only [frontEndStageCfg, returned] using first
      have last := frontEndInputFinish_trace caller (.inl (.source, .init))
        (frontEndDecoderStage .input phase data).data
        (frontEndMaskRegs (frontEndDecoderStage .input phase data).masks regs) ctx
      change FrontEndMachine.Trace caller
        (FrontEndMachine.cfg (some (FrontEndMachine.inputDecoderLabel phase)) regs data ctx)
        (frontEndFinishCfg (frontEndJoin (frontEndDecoderStage .input phase data)
          (frontEndInputFinish (.inl (.source, .init))
            (frontEndDecoderStage .input phase data).data)) regs ctx)
        ((frontEndDecoderStage .input phase data).steps +
          (frontEndInputFinish (.inl (.source, .init))
            (frontEndDecoderStage .input phase data).data).steps)
      rw [frontEndFinishCfg_join]
      exact first'.trans caller last

theorem frontEndFramerFinish_trace (phase : OpenFramingMachine.Phase)
    (data : FrontEndMachine.LocalData) (regs : FrontEndMachine.Registers R)
    (ctx : ∀ k, List (Γ k)) :
    FrontEndMachine.Trace caller
      (FrontEndMachine.cfg (some (FrontEndMachine.framerLabel phase)) regs data ctx)
      (frontEndFinishCfg (frontEndFramerFinish phase data) regs ctx)
      (frontEndFramerFinish phase data).steps := by
  have first := frontEndFramerStage_trace caller phase data regs ctx
  dsimp only [frontEndFramerFinish]
  cases returned : (frontEndFramerStage phase data).result with
  | failure =>
      simpa only [frontEndStageCfg, frontEndFinishCfg, returned, frontEndResultLabel] using first
  | success =>
      have first' : FrontEndMachine.Trace caller
          (FrontEndMachine.cfg (some (FrontEndMachine.framerLabel phase)) regs data ctx)
          (FrontEndMachine.cfg (some (FrontEndMachine.inputDecoderLabel .scan))
            (frontEndMaskRegs (frontEndFramerStage phase data).masks regs)
            (frontEndFramerStage phase data).data ctx) (frontEndFramerStage phase data).steps := by
        simpa only [frontEndStageCfg, returned] using first
      have last := frontEndInputDecoderFinish_trace caller .scan
        (frontEndFramerStage phase data).data (frontEndMaskRegs (frontEndFramerStage phase data).masks regs) ctx
      change FrontEndMachine.Trace caller
        (FrontEndMachine.cfg (some (FrontEndMachine.framerLabel phase)) regs data ctx)
        (frontEndFinishCfg (frontEndJoin (frontEndFramerStage phase data)
          (frontEndInputDecoderFinish .scan (frontEndFramerStage phase data).data)) regs ctx)
        ((frontEndFramerStage phase data).steps +
          (frontEndInputDecoderFinish .scan (frontEndFramerStage phase data).data).steps)
      rw [frontEndFinishCfg_join]
      exact first'.trans caller last

theorem frontEnd_phase_trace (phase : FrontEndMachine.OwnedLabels)
    (data : FrontEndMachine.LocalData) (regs : FrontEndMachine.Registers R)
    (ctx : ∀ k, List (Γ k)) :
    FrontEndMachine.Trace caller
      (FrontEndMachine.cfg (some (FrontEndMachine.ownedLabelEquiv phase).val) regs data ctx)
      (frontEndPhaseResult phase regs data ctx) (frontEndPhaseSteps phase data) := by
  cases phase with
  | inl phase => exact frontEndInputFinish_trace caller phase data regs ctx
  | inr phase =>
      cases phase with
      | inl phase => exact frontEndFramerFinish_trace caller phase data regs ctx
      | inr phase =>
          cases phase with
          | inl phase => exact frontEndInputDecoderFinish_trace caller phase data regs ctx
          | inr phase =>
              cases phase with
              | scan => exact frontEndCertificateDecoderStage_trace caller .scan data regs ctx
              | emit => exact frontEndCertificateDecoderStage_trace caller .emit data regs ctx
              | clear => exact frontEndCertificateDecoderStage_trace caller .clear data regs ctx

theorem frontEnd_phase_iterate (phase : FrontEndMachine.OwnedLabels)
    (data : FrontEndMachine.LocalData) (regs : FrontEndMachine.Registers R)
    (ctx : ∀ k, List (Γ k)) :
    (FrontEndMachine.next caller)^[frontEndPhaseSteps phase data]
      (some (FrontEndMachine.cfg (some (FrontEndMachine.ownedLabelEquiv phase).val) regs data ctx)) =
      some (frontEndPhaseResult phase regs data ctx) :=
  (frontEnd_phase_trace caller phase data regs ctx).run

theorem frontEnd_phase_owned_prefix (phase : FrontEndMachine.OwnedLabels)
    (data : FrontEndMachine.LocalData) (regs : FrontEndMachine.Registers R)
    (ctx : ∀ k, List (Γ k)) (n : Nat) (bound : n < frontEndPhaseSteps phase data) :
    ∃ reached, (FrontEndMachine.next caller)^[n]
      (some (FrontEndMachine.cfg (some (FrontEndMachine.ownedLabelEquiv phase).val) regs data ctx)) =
        some reached ∧ FrontEndMachine.Owned reached.l :=
  (frontEnd_phase_trace caller phase data regs ctx).owned_prefix n bound

end FrontEndComplete


/-! Explicit one-step data and the fixed dirty Input credit. -/

abbrev InputControl := InputParserMachine.OwnedLabels ⊕ TreeParserMachine.Result

def inputControlLabel : InputControl → InputParserMachine.Label Λ
  | .inl phase => (InputParserMachine.ownedLabelEquiv phase).val
  | .inr result => InputParserMachine.resultLabel result

def inputTreeControl (side : InputParserMachine.TreeSide) (phase : TreeParserMachine.Phase) : InputControl :=
  .inl (.inl (side, phase))

def inputLocalControl (phase : InputParserMachine.Phase) : InputControl :=
  .inl (.inr (.inr (.inr phase)))

def inputTreeResultControl : InputParserMachine.TreeSide → TreeParserMachine.Result → InputControl
  | .source, .success => .inl (.inr (.inl .source))
  | .target, .success => .inl (.inr (.inl .target))
  | .source, .failure => .inr .failure
  | .target, .failure => .inl (.inr (.inr (.inl ())))

def inputTreeAdvance (side : InputParserMachine.TreeSide) (phase : TreeParserMachine.Phase)
    (data : InputState) : InputControl × InputState :=
  match phase with
  | .init => (inputTreeControl side .scan, { data with pending := () :: data.pending })
  | .scan => match data.raw with
    | [] => (inputTreeControl side .undo, data)
    | tag :: raw =>
        if tag = nodeTag then
          (inputTreeControl side .scan,
            { data with raw := raw, rev := nodeTag :: data.rev, pending := () :: data.pending })
        else if tag = emptyTag then
          (inputTreeControl side (if data.pending.tail = [] then .emit else .scan),
            { data with raw := raw, rev := emptyTag :: data.rev, pending := data.pending.tail })
        else (inputTreeControl side .undo, data)
  | .emit => match data.rev with
    | [] => (inputTreeResultControl side .success, data)
    | tag :: rev => (inputTreeControl side .emit,
        { data with rev := rev, outputs := Function.update data.outputs side (tag :: data.outputs side) })
  | .undo => match data.rev with
    | [] => (inputTreeControl side .dropPending, data)
    | tag :: rev => (inputTreeControl side .undo, { data with raw := tag :: data.raw, rev := rev })
  | .dropPending => match data.pending with
    | [] => (inputTreeResultControl side .failure, data)
    | _ :: pending => (inputTreeControl side .dropPending, { data with pending := pending })

def inputToReverseAdvance (side : InputParserMachine.TreeSide) (data : InputState) :
    InputControl × InputState :=
  match data.outputs side with
  | [] => (inputLocalControl (InputParserMachine.toRawPhase side), data)
  | tag :: word => (inputLocalControl (InputParserMachine.toReversePhase side),
      { data with rev := tag :: data.rev, outputs := Function.update data.outputs side word })

def inputToRawAdvance (side : InputParserMachine.TreeSide) (data : InputState) : InputControl × InputState :=
  match data.rev with
  | [] => (match side with | .source => .inr .failure | .target => inputLocalControl .restoreSep1, data)
  | tag :: rev => (inputLocalControl (InputParserMachine.toRawPhase side),
      { data with raw := tag :: data.raw, rev := rev })

def inputLocalAdvance (phase : InputParserMachine.Phase) (data : InputState) : InputControl × InputState :=
  match phase with
  | .sourceToRaw => inputToRawAdvance .source data
  | .sourceToReverse => inputToReverseAdvance .source data
  | .restoreSep1 => (inputLocalControl .sourceToReverse, { data with raw := separatorTag :: data.raw })
  | .targetToRaw => inputToRawAdvance .target data
  | .targetToReverse => inputToReverseAdvance .target data
  | .restoreSep2 => (inputLocalControl .targetToReverse, { data with raw := separatorTag :: data.raw })
  | .bitsUndo => match data.bitsReverse with
    | [] => (inputLocalControl .restoreSep2, data)
    | bit :: rest => (inputLocalControl .bitsUndo,
        { data with raw := bitTag bit :: data.raw, bitsReverse := rest })
  | .fuelUndo => match data.fuel with
    | [] => (inputLocalControl .bitsUndo, data)
    | bit :: fuel => (inputLocalControl .fuelUndo,
        { data with fuel := fuel, bitsReverse := bit :: data.bitsReverse })
  | .restoreEnd => (inputLocalControl .fuelUndo, { data with raw := endInputTag :: data.raw })
  | .eof => match data.raw with
    | [] => (.inr .success, data)
    | _ :: _ => (inputLocalControl .restoreEnd, data)
  | .bitsEmit => match data.bitsReverse with
    | [] => (inputLocalControl .eof, data)
    | bit :: rest => (inputLocalControl .bitsEmit,
        { data with fuel := bit :: data.fuel, bitsReverse := rest })
  | .bitsScan => match data.raw with
    | [] => (inputLocalControl .bitsUndo, data)
    | tag :: raw =>
        if tag = bitZeroTag then
          (inputLocalControl .bitsScan, { data with raw := raw, bitsReverse := false :: data.bitsReverse })
        else if tag = bitOneTag then
          (inputLocalControl .bitsScan, { data with raw := raw, bitsReverse := true :: data.bitsReverse })
        else if tag = endInputTag then (inputLocalControl .bitsEmit, { data with raw := raw })
        else (inputLocalControl .bitsUndo, data)

def inputSeparatorAdvance (side : InputParserMachine.TreeSide) (data : InputState) : InputControl × InputState :=
  match data.raw with
  | [] => (inputLocalControl (InputParserMachine.toReversePhase side), data)
  | tag :: raw =>
      if tag = separatorTag then
        (match side with
          | .source => inputTreeControl .target .init
          | .target => inputLocalControl .bitsScan, { data with raw := raw })
      else (inputLocalControl (InputParserMachine.toReversePhase side), data)

def inputAdvance (phase : InputParserMachine.OwnedLabels) (data : InputState) : InputControl × InputState :=
  match phase with
  | .inl (side, phase) => inputTreeAdvance side phase data
  | .inr (.inl side) => inputSeparatorAdvance side data
  | .inr (.inr (.inl _)) => inputLocalAdvance .restoreSep1 data
  | .inr (.inr (.inr phase)) => inputLocalAdvance phase data

/-- The full fixed credit, including old raw length and the target rollback debt. -/
def inputPhaseCredit (phase : InputParserMachine.OwnedLabels) (rawLength : Nat) : Nat :=
  match phase with
  | .inl (.source, .init) => rawLength + 1
  | .inl (.source, .scan) | .inl (.source, .emit) => rawLength
  | .inl (.source, .undo) | .inl (.source, .dropPending) => 0
  | .inl (.target, .init) => rawLength + 2
  | .inl (.target, .scan) => rawLength + 1
  | .inl (.target, .emit) => 2
  | .inl (.target, .undo) | .inl (.target, .dropPending) => 1
  | .inr (.inl .source) => rawLength
  | .inr (.inl .target) => 2
  | .inr (.inr (.inl _)) => 1
  | .inr (.inr (.inr .bitsScan)) | .inr (.inr (.inr .bitsEmit)) |
      .inr (.inr (.inr .eof)) | .inr (.inr (.inr .restoreEnd)) => 3
  | .inr (.inr (.inr .fuelUndo)) | .inr (.inr (.inr .bitsUndo)) |
      .inr (.inr (.inr .restoreSep2)) => 2
  | .inr (.inr (.inr .targetToReverse)) | .inr (.inr (.inr .targetToRaw)) |
      .inr (.inr (.inr .restoreSep1)) => 1
  | .inr (.inr (.inr .sourceToReverse)) | .inr (.inr (.inr .sourceToRaw)) => 0

def inputControlCredit (control : InputControl) (data : InputState) : Nat :=
  match control with
  | .inl phase => inputPhaseCredit phase data.raw.length
  | .inr _ => 0

def inputLocalCells (data : InputState) : Nat :=
  data.raw.length + data.rev.length + data.pending.length +
    (data.outputs .source).length + (data.outputs .target).length +
    data.fuel.length + data.bitsReverse.length

def inputPotential (control : InputControl) (data : InputState) : Nat :=
  inputLocalCells data + inputControlCredit control data

@[simp] theorem inputControlLabel_tree (side : InputParserMachine.TreeSide)
    (phase : TreeParserMachine.Phase) :
    inputControlLabel (Λ := Λ) (inputTreeControl side phase) = InputParserMachine.treeLabel side phase := rfl

@[simp] theorem inputControlLabel_local (phase : InputParserMachine.Phase) :
    inputControlLabel (Λ := Λ) (inputLocalControl phase) = InputParserMachine.phaseLabel phase := rfl

@[simp] theorem inputControlLabel_result (result : TreeParserMachine.Result) :
    inputControlLabel (Λ := Λ) (.inr result) = InputParserMachine.resultLabel result := rfl

@[simp] theorem inputControlLabel_treeResult (side : InputParserMachine.TreeSide)
    (result : TreeParserMachine.Result) :
    inputControlLabel (Λ := Λ) (inputTreeResultControl side result) =
      InputParserMachine.treeResultLabel side result := by
  cases side <;> cases result <;> rfl

section InputAdvanceExecution
variable [DecidableEq K]
variable (caller : InputParserMachine.External Λ → InputParserMachine.Statement Γ Λ R)

theorem inputTreeAdvance_step (side : InputParserMachine.TreeSide) (phase : TreeParserMachine.Phase)
    (data : InputState) (regs : InputParserMachine.Registers R) (ctx : ∀ k, List (Γ k)) :
    InputParserMachine.step caller (inputCfg (some (InputParserMachine.treeLabel side phase)) regs data ctx) =
      some (inputCfg (some (inputControlLabel (inputTreeAdvance side phase data).1))
        (InputParserMachine.reset regs) (inputTreeAdvance side phase data).2 ctx) := by
  simp only [inputCfg, InputParserMachine.step, InputParserMachine.cfg, InputParserMachine.treeLabel]
  cases phase with
  | init =>
      exact TreeParserMachine.init_step (InputParserMachine.handler caller) side
        data.raw data.rev data.pending regs data.outputs (InputParserMachine.stores data.fuel data.bitsReverse ctx)
  | scan =>
      cases rawEq : data.raw with
      | nil =>
          simpa only [inputTreeAdvance, rawEq, inputControlLabel_tree, InputParserMachine.treeLabel] using
            TreeParserMachine.scan_step_nil (InputParserMachine.handler caller) side data.rev data.pending regs
              data.outputs (InputParserMachine.stores data.fuel data.bitsReverse ctx)
      | cons tag raw =>
          by_cases node : tag = nodeTag
          · subst tag
            simpa only [inputTreeAdvance, rawEq, ite_true, inputControlLabel_tree, InputParserMachine.treeLabel] using
              TreeParserMachine.scan_step_node (InputParserMachine.handler caller) side raw data.rev data.pending regs
                data.outputs (InputParserMachine.stores data.fuel data.bitsReverse ctx)
          · by_cases empty : tag = emptyTag
            · subst tag
              simpa only [inputTreeAdvance, rawEq, ite_eq_right node, ite_true,
                inputControlLabel_tree, InputParserMachine.treeLabel] using
                TreeParserMachine.scan_step_empty (InputParserMachine.handler caller) side raw data.rev data.pending regs
                  data.outputs (InputParserMachine.stores data.fuel data.bitsReverse ctx)
            · simpa only [inputTreeAdvance, rawEq, ite_eq_right node, ite_eq_right empty,
                inputControlLabel_tree, InputParserMachine.treeLabel] using
                TreeParserMachine.scan_step_foreign (InputParserMachine.handler caller) side tag raw data.rev data.pending regs
                  data.outputs (InputParserMachine.stores data.fuel data.bitsReverse ctx) node empty
  | emit =>
      cases revEq : data.rev with
      | nil =>
          simpa only [inputTreeAdvance, revEq, inputControlLabel_treeResult, InputParserMachine.treeResultLabel] using
            TreeParserMachine.emit_step_nil (InputParserMachine.handler caller) side data.raw data.pending regs
              data.outputs (InputParserMachine.stores data.fuel data.bitsReverse ctx)
      | cons tag rev =>
          simpa only [inputTreeAdvance, revEq, inputControlLabel_tree, InputParserMachine.treeLabel] using
            TreeParserMachine.emit_step_cons (InputParserMachine.handler caller) side tag data.raw rev data.pending regs
              data.outputs (InputParserMachine.stores data.fuel data.bitsReverse ctx)
  | undo =>
      cases revEq : data.rev with
      | nil =>
          simpa only [inputTreeAdvance, revEq, inputControlLabel_tree, InputParserMachine.treeLabel] using
            TreeParserMachine.undo_step_nil (InputParserMachine.handler caller) side data.raw data.pending regs
              data.outputs (InputParserMachine.stores data.fuel data.bitsReverse ctx)
      | cons tag rev =>
          simpa only [inputTreeAdvance, revEq, inputControlLabel_tree, InputParserMachine.treeLabel] using
            TreeParserMachine.undo_step_cons (InputParserMachine.handler caller) side tag data.raw rev data.pending regs
              data.outputs (InputParserMachine.stores data.fuel data.bitsReverse ctx)
  | dropPending =>
      cases pendingEq : data.pending with
      | nil =>
          simpa only [inputTreeAdvance, pendingEq, inputControlLabel_treeResult, InputParserMachine.treeResultLabel] using
            TreeParserMachine.dropPending_step_nil (InputParserMachine.handler caller) side data.raw data.rev regs
              data.outputs (InputParserMachine.stores data.fuel data.bitsReverse ctx)
      | cons token pending =>
          cases token
          simpa only [inputTreeAdvance, pendingEq, inputControlLabel_tree, InputParserMachine.treeLabel] using
            TreeParserMachine.dropPending_step_cons (InputParserMachine.handler caller) side data.raw data.rev pending regs
              data.outputs (InputParserMachine.stores data.fuel data.bitsReverse ctx)

theorem inputToReverseAdvance_step (side : InputParserMachine.TreeSide) (data : InputState)
    (regs : InputParserMachine.Registers R) (ctx : ∀ k, List (Γ k)) :
    InputParserMachine.step caller
      (inputCfg (some (InputParserMachine.phaseLabel (InputParserMachine.toReversePhase side))) regs data ctx) =
      some (inputCfg (some (inputControlLabel (inputToReverseAdvance side data).1))
        (InputParserMachine.reset regs) (inputToReverseAdvance side data).2 ctx) := by
  cases selected : data.outputs side with
  | nil =>
      have restored : Function.update data.outputs side [] = data.outputs := by
        rw [← selected, Function.update_eq_self]
      have equation := InputParserMachine.toReverse_step_nil caller side data.raw data.rev data.pending
        regs data.outputs data.fuel data.bitsReverse ctx
      rw [restored] at equation
      simpa only [inputCfg, inputToReverseAdvance, selected, inputControlLabel_local] using equation
  | cons tag word =>
      have restored : Function.update data.outputs side (tag :: word) = data.outputs := by
        rw [← selected, Function.update_eq_self]
      have equation := InputParserMachine.toReverse_step_cons caller side tag data.raw data.rev word data.pending
        regs data.outputs data.fuel data.bitsReverse ctx
      rw [restored] at equation
      simpa only [inputCfg, inputToReverseAdvance, selected, inputControlLabel_local] using equation

theorem inputToRawAdvance_step (side : InputParserMachine.TreeSide) (data : InputState)
    (regs : InputParserMachine.Registers R) (ctx : ∀ k, List (Γ k)) :
    InputParserMachine.step caller
      (inputCfg (some (InputParserMachine.phaseLabel (InputParserMachine.toRawPhase side))) regs data ctx) =
      some (inputCfg (some (inputControlLabel (inputToRawAdvance side data).1))
        (InputParserMachine.reset regs) (inputToRawAdvance side data).2 ctx) := by
  cases revEq : data.rev with
  | nil =>
      have equation := InputParserMachine.toRaw_step_nil caller side data.raw data.pending
        regs data.outputs data.fuel data.bitsReverse ctx
      cases side <;>
        simpa only [inputCfg, inputToRawAdvance, revEq, inputControlLabel_local,
          inputControlLabel_result, InputParserMachine.afterRollback] using equation
  | cons tag rev =>
      simpa only [inputCfg, inputToRawAdvance, revEq, inputControlLabel_local] using
        InputParserMachine.toRaw_step_cons caller side tag data.raw rev data.pending
          regs data.outputs data.fuel data.bitsReverse ctx


theorem inputLocalAdvance_step (phase : InputParserMachine.Phase) (data : InputState)
    (regs : InputParserMachine.Registers R) (ctx : ∀ k, List (Γ k)) :
    InputParserMachine.step caller (inputCfg (some (InputParserMachine.phaseLabel phase)) regs data ctx) =
      some (inputCfg (some (inputControlLabel (inputLocalAdvance phase data).1))
        (InputParserMachine.reset regs) (inputLocalAdvance phase data).2 ctx) := by
  cases phase with
  | sourceToRaw => exact inputToRawAdvance_step caller .source data regs ctx
  | targetToRaw => exact inputToRawAdvance_step caller .target data regs ctx
  | sourceToReverse => exact inputToReverseAdvance_step caller .source data regs ctx
  | targetToReverse => exact inputToReverseAdvance_step caller .target data regs ctx
  | restoreSep1 =>
      exact InputParserMachine.restoreSep1_step caller data.raw data.rev data.pending
        regs data.outputs data.fuel data.bitsReverse ctx
  | restoreSep2 =>
      exact InputParserMachine.restoreSep2_step caller data.raw data.rev data.pending
        regs data.outputs data.fuel data.bitsReverse ctx
  | restoreEnd =>
      exact InputParserMachine.restoreEnd_step caller data.raw data.rev data.pending
        regs data.outputs data.fuel data.bitsReverse ctx
  | bitsUndo =>
      cases wordEq : data.bitsReverse with
      | nil =>
          simpa only [inputCfg, inputLocalAdvance, wordEq, inputControlLabel_local] using
            InputParserMachine.bitsUndo_step_nil caller data.raw data.rev data.pending
              regs data.outputs data.fuel ctx
      | cons bit rest =>
          simpa only [inputCfg, inputLocalAdvance, wordEq, inputControlLabel_local] using
            InputParserMachine.bitsUndo_step_cons caller bit data.raw data.rev data.pending
              regs data.outputs data.fuel rest ctx
  | fuelUndo =>
      cases wordEq : data.fuel with
      | nil =>
          simpa only [inputCfg, inputLocalAdvance, wordEq, inputControlLabel_local] using
            InputParserMachine.fuelUndo_step_nil caller data.raw data.rev data.pending
              regs data.outputs data.bitsReverse ctx
      | cons bit fuel =>
          simpa only [inputCfg, inputLocalAdvance, wordEq, inputControlLabel_local] using
            InputParserMachine.fuelUndo_step_cons caller bit data.raw data.rev data.pending
              regs data.outputs fuel data.bitsReverse ctx
  | bitsEmit =>
      cases wordEq : data.bitsReverse with
      | nil =>
          simpa only [inputCfg, inputLocalAdvance, wordEq, inputControlLabel_local] using
            InputParserMachine.bitsEmit_step_nil caller data.raw data.rev data.pending
              regs data.outputs data.fuel ctx
      | cons bit rest =>
          simpa only [inputCfg, inputLocalAdvance, wordEq, inputControlLabel_local] using
            InputParserMachine.bitsEmit_step_cons caller bit data.raw data.rev data.pending
              regs data.outputs data.fuel rest ctx
  | eof =>
      cases rawEq : data.raw with
      | nil =>
          simpa only [inputCfg, inputLocalAdvance, rawEq, inputControlLabel] using
            InputParserMachine.eof_step_nil caller data.rev data.pending regs data.outputs
              data.fuel data.bitsReverse ctx
      | cons tag raw =>
          simpa only [inputCfg, inputLocalAdvance, rawEq, inputControlLabel_local] using
            InputParserMachine.eof_step_cons caller tag raw data.rev data.pending regs data.outputs
              data.fuel data.bitsReverse ctx
  | bitsScan =>
      cases rawEq : data.raw with
      | nil =>
          simpa only [inputCfg, inputLocalAdvance, rawEq, inputControlLabel_local] using
            InputParserMachine.bitsScan_step_nil caller data.rev data.pending regs data.outputs
              data.fuel data.bitsReverse ctx
      | cons tag raw =>
          by_cases zero : tag = bitZeroTag
          · subst tag
            simpa only [inputCfg, inputLocalAdvance, rawEq, ite_true, inputControlLabel_local, bitTag] using
              InputParserMachine.bitsScan_step_bit caller false raw data.rev data.pending regs data.outputs
                data.fuel data.bitsReverse ctx
          · by_cases one : tag = bitOneTag
            · subst tag
              simpa only [inputCfg, inputLocalAdvance, rawEq, ite_eq_right zero, ite_true,
                inputControlLabel_local, bitTag] using
                InputParserMachine.bitsScan_step_bit caller true raw data.rev data.pending regs data.outputs
                  data.fuel data.bitsReverse ctx
            · by_cases ended : tag = endInputTag
              · subst tag
                simpa only [inputCfg, inputLocalAdvance, rawEq, ite_eq_right zero, ite_eq_right one,
                  ite_true, inputControlLabel_local] using
                  InputParserMachine.bitsScan_step_end caller raw data.rev data.pending regs data.outputs
                    data.fuel data.bitsReverse ctx
              · simpa only [inputCfg, inputLocalAdvance, rawEq, ite_eq_right zero, ite_eq_right one,
                  ite_eq_right ended, inputControlLabel_local] using
                  InputParserMachine.bitsScan_step_foreign caller tag raw data.rev data.pending regs
                    data.outputs data.fuel data.bitsReverse ctx ended zero one

theorem inputSeparatorAdvance_step (side : InputParserMachine.TreeSide) (data : InputState)
    (regs : InputParserMachine.Registers R) (ctx : ∀ k, List (Γ k)) :
    InputParserMachine.step caller (inputCfg (some (InputParserMachine.treeResultLabel side .success)) regs data ctx) =
      some (inputCfg (some (inputControlLabel (inputSeparatorAdvance side data).1))
        (InputParserMachine.reset regs) (inputSeparatorAdvance side data).2 ctx) := by
  cases rawEq : data.raw with
  | nil =>
      simpa only [inputCfg, inputSeparatorAdvance, rawEq, inputControlLabel_local] using
        InputParserMachine.separator_step_nil caller side data.rev data.pending regs data.outputs
          data.fuel data.bitsReverse ctx
  | cons tag raw =>
      by_cases separator : tag = separatorTag
      · subst tag
        have equation := InputParserMachine.separator_step_separator caller side raw data.rev data.pending regs
          data.outputs data.fuel data.bitsReverse ctx
        cases side <;>
          simpa only [inputCfg, inputSeparatorAdvance, rawEq, ite_true, inputControlLabel_tree,
            inputControlLabel_local, InputParserMachine.afterSeparator] using equation
      · simpa only [inputCfg, inputSeparatorAdvance, rawEq, ite_eq_right separator,
          inputControlLabel_local] using
          InputParserMachine.separator_step_foreign caller side tag raw data.rev data.pending regs
            data.outputs data.fuel data.bitsReverse ctx separator

theorem inputAdvance_step (phase : InputParserMachine.OwnedLabels) (data : InputState)
    (regs : InputParserMachine.Registers R) (ctx : ∀ k, List (Γ k)) :
    InputParserMachine.step caller
      (inputCfg (some (InputParserMachine.ownedLabelEquiv phase).val) regs data ctx) =
      some (inputCfg (some (inputControlLabel (inputAdvance phase data).1))
        (InputParserMachine.reset regs) (inputAdvance phase data).2 ctx) := by
  cases phase with
  | inl pair => exact inputTreeAdvance_step caller pair.1 pair.2 data regs ctx
  | inr phase =>
      cases phase with
      | inl side => exact inputSeparatorAdvance_step caller side data regs ctx
      | inr phase =>
          cases phase with
          | inl token =>
              exact InputParserMachine.targetFailure_step caller data.raw data.rev data.pending
                regs data.outputs data.fuel data.bitsReverse ctx
          | inr phase => exact inputLocalAdvance_step caller phase data regs ctx

end InputAdvanceExecution

def inputControlDebt : InputControl → Nat
  | .inl (.inl (side, _)) | .inl (.inr (.inl side)) => InputParserMachine.sideDebt side
  | .inl (.inr (.inr (.inl _))) => 1
  | .inl (.inr (.inr (.inr phase))) => InputParserMachine.phaseDebt phase
  | .inr .success => 3
  | .inr .failure => 0

theorem inputControlLabel_debt (control : InputControl) :
    InputParserMachine.debt (some (inputControlLabel (Λ := Λ) control)) = inputControlDebt control := by
  cases control with
  | inl phase =>
      cases phase with
      | inl pair => rfl
      | inr phase => cases phase with
        | inl side => rfl
        | inr phase => cases phase with
          | inl token => rfl
          | inr phase => rfl
  | inr result => cases result <;> rfl

def InputCreditBalance (before : InputControl) (data : InputState)
    (after : InputControl × InputState) : Prop :=
  after.2.pending.length + inputControlCredit after.1 after.2 + inputControlDebt before ≤
    data.pending.length + inputControlCredit before data + inputControlDebt after.1

theorem inputTreeAdvance_credit (side : InputParserMachine.TreeSide) (phase : TreeParserMachine.Phase)
    (data : InputState) :
    InputCreditBalance (inputTreeControl side phase) data (inputTreeAdvance side phase data) := by
  unfold InputCreditBalance
  cases side <;> cases phase <;> simp only [inputTreeAdvance] <;> repeat' split
  all_goals
    simp_all only [inputTreeControl, inputTreeResultControl, inputControlCredit, inputPhaseCredit,
      inputControlDebt, InputParserMachine.sideDebt, List.length_cons, List.length_nil, List.length_tail]
    omega

theorem inputLocalAdvance_credit (phase : InputParserMachine.Phase) (data : InputState) :
    InputCreditBalance (inputLocalControl phase) data (inputLocalAdvance phase data) := by
  unfold InputCreditBalance
  cases phase <;> simp only [inputLocalAdvance, inputToReverseAdvance, inputToRawAdvance] <;> repeat' split
  all_goals
    simp_all only [inputLocalControl, inputControlCredit, inputPhaseCredit,
      inputControlDebt, InputParserMachine.phaseDebt, InputParserMachine.toRawPhase,
      InputParserMachine.toReversePhase]
    omega

theorem inputSeparatorAdvance_credit (side : InputParserMachine.TreeSide) (data : InputState) :
    InputCreditBalance (inputTreeResultControl side .success) data (inputSeparatorAdvance side data) := by
  unfold InputCreditBalance
  cases side <;> simp only [inputSeparatorAdvance] <;> repeat' split
  all_goals
    simp_all only [inputTreeResultControl, inputTreeControl, inputLocalControl, inputControlCredit,
      inputPhaseCredit, inputControlDebt, InputParserMachine.sideDebt, InputParserMachine.phaseDebt,
      InputParserMachine.toReversePhase, List.length_cons]
    omega

theorem inputAdvance_credit (phase : InputParserMachine.OwnedLabels) (data : InputState) :
    InputCreditBalance (.inl phase) data (inputAdvance phase data) := by
  cases phase with
  | inl pair => exact inputTreeAdvance_credit pair.1 pair.2 data
  | inr phase =>
      cases phase with
      | inl side =>
          cases side with
          | source => exact inputSeparatorAdvance_credit .source data
          | target => exact inputSeparatorAdvance_credit .target data
      | inr phase => cases phase with
        | inl token =>
            exact inputLocalAdvance_credit .restoreSep1 data
        | inr phase => exact inputLocalAdvance_credit phase data

section InputPotentialExecution
variable [DecidableEq K]
variable (caller : InputParserMachine.External Λ → InputParserMachine.Statement Γ Λ R)

include caller in
theorem inputAdvance_potential (phase : InputParserMachine.OwnedLabels) (data : InputState)
    (regs : InputParserMachine.Registers R) (ctx : ∀ k, List (Γ k)) :
    inputPotential (inputAdvance phase data).1 (inputAdvance phase data).2 ≤
      inputPotential (.inl phase) data := by
  have mass := (InputParserMachine.step_effect caller (InputParserMachine.ownedLabelEquiv phase).property
    (inputAdvance_step caller phase data regs ctx)).mass
  change InputParserMachine.baseCells
      (inputCfg (some (inputControlLabel (inputAdvance phase data).1))
        (InputParserMachine.reset regs) (inputAdvance phase data).2 ctx) +
      InputParserMachine.debt (some (inputControlLabel (inputAdvance phase data).1)) =
    InputParserMachine.baseCells
      (inputCfg (some (inputControlLabel (.inl phase))) regs data ctx) +
      InputParserMachine.debt (some (inputControlLabel (.inl phase))) at mass
  simp only [inputCfg, InputParserMachine.baseCells_cfg, InputParserMachine.outputCells,
    inputControlLabel_debt] at mass
  have credit := inputAdvance_credit phase data
  unfold InputCreditBalance at credit
  unfold inputPotential inputLocalCells
  omega

end InputPotentialExecution

/-! Actual dirty FrontEnd prefix masks and protected stores, including zero. -/

theorem frontEndInputStage_masks (phase : InputParserMachine.OwnedLabels)
    (data : FrontEndMachine.LocalData) : (frontEndInputStage phase data).masks = [.input] := rfl

theorem frontEndInputOwned_tree_label (side : InputParserMachine.TreeSide) (phase : TreeParserMachine.Phase) :
    FrontEndMachine.inputOwnedLabel (Λ := Λ) (.inl (side, phase)) = InputParserMachine.treeLabel side phase := rfl

def frontEndComponentRegisters (mask : FrontEndMask) (regs : FrontEndMachine.Registers R) (n : Nat) :
    FrontEndMachine.Registers R := if n = 0 then regs else mask.apply regs

def frontEndCertificateRegisters (_phase : OpenDecoderMachine.Phase)
    (_data : FrontEndMachine.LocalData) (regs : FrontEndMachine.Registers R) (n : Nat) :
    FrontEndMachine.Registers R := frontEndComponentRegisters .decoder regs n

def frontEndInputRegisters (phase : InputParserMachine.OwnedLabels)
    (data : FrontEndMachine.LocalData) (regs : FrontEndMachine.Registers R) (n : Nat) :
    FrontEndMachine.Registers R :=
  let stage := frontEndInputStage phase data
  if n ≤ stage.steps then frontEndComponentRegisters .input regs n
  else frontEndCertificateRegisters .scan stage.data (FrontEndMask.input.apply regs) (n - stage.steps)

def frontEndInputDecoderRegisters (phase : OpenDecoderMachine.Phase)
    (data : FrontEndMachine.LocalData) (regs : FrontEndMachine.Registers R) (n : Nat) :
    FrontEndMachine.Registers R :=
  let stage := frontEndDecoderStage .input phase data
  if n ≤ stage.steps then frontEndComponentRegisters .decoder regs n
  else frontEndInputRegisters (.inl (.source, .init)) stage.data
    (FrontEndMask.decoder.apply regs) (n - stage.steps)

def frontEndFramerRegisters (phase : OpenFramingMachine.Phase)
    (data : FrontEndMachine.LocalData) (regs : FrontEndMachine.Registers R) (n : Nat) :
    FrontEndMachine.Registers R :=
  let stage := frontEndFramerStage phase data
  if n ≤ stage.steps then frontEndComponentRegisters .framer regs n
  else frontEndInputDecoderRegisters .scan stage.data
    (FrontEndMask.framer.apply regs) (n - stage.steps)

def frontEndPhaseRegisters (phase : FrontEndMachine.OwnedLabels)
    (data : FrontEndMachine.LocalData) (regs : FrontEndMachine.Registers R) (n : Nat) :
    FrontEndMachine.Registers R :=
  match phase with
  | .inl phase => frontEndInputRegisters phase data regs n
  | .inr (.inl phase) => frontEndFramerRegisters phase data regs n
  | .inr (.inr (.inl phase)) => frontEndInputDecoderRegisters phase data regs n
  | .inr (.inr (.inr phase)) => frontEndCertificateRegisters phase data regs n

@[simp] theorem FrontEndMask.apply_caller (mask : FrontEndMask) (regs : FrontEndMachine.Registers R) :
    (mask.apply regs).2.2 = regs.2.2 := by cases mask <;> rfl

@[simp] theorem frontEndComponentRegisters_caller (mask : FrontEndMask)
    (regs : FrontEndMachine.Registers R) (n : Nat) :
    (frontEndComponentRegisters mask regs n).2.2 = regs.2.2 := by
  unfold frontEndComponentRegisters
  split <;> simp only [FrontEndMask.apply_caller]

theorem frontEndPhaseRegisters_caller (phase : FrontEndMachine.OwnedLabels)
    (data : FrontEndMachine.LocalData) (regs : FrontEndMachine.Registers R) (n : Nat) :
    (frontEndPhaseRegisters phase data regs n).2.2 = regs.2.2 := by
  cases phase with
  | inl phase =>
      simp only [frontEndPhaseRegisters, frontEndInputRegisters, frontEndCertificateRegisters]
      split <;> simp only [frontEndComponentRegisters_caller, FrontEndMask.apply_caller]
  | inr phase =>
      cases phase with
      | inl phase =>
          simp only [frontEndPhaseRegisters, frontEndFramerRegisters, frontEndInputDecoderRegisters,
            frontEndInputRegisters, frontEndCertificateRegisters]
          repeat' split
          all_goals simp only [frontEndComponentRegisters_caller, FrontEndMask.apply_caller]
      | inr phase =>
          cases phase with
          | inl phase =>
              simp only [frontEndPhaseRegisters, frontEndInputDecoderRegisters,
                frontEndInputRegisters, frontEndCertificateRegisters]
              repeat' split
              all_goals simp only [frontEndComponentRegisters_caller, FrontEndMask.apply_caller]
          | inr phase =>
              exact frontEndComponentRegisters_caller .decoder regs n

section FrontEndPrefixExecution
variable [DecidableEq K]
variable (caller : FrontEndMachine.External Λ → FrontEndMachine.Statement Γ Λ R)

theorem frontEnd_prefix_after {start middle reached : FrontEndMachine.Cfg Γ Λ R} {first n : Nat}
    (before : (FrontEndMachine.next caller)^[first] (some start) = some middle)
    (later : first ≤ n)
    (executed : (FrontEndMachine.next caller)^[n] (some start) = some reached) :
    (FrontEndMachine.next caller)^[n - first] (some middle) = some reached := by
  have count : n = (n - first) + first := by omega
  rwa [count, Function.iterate_add_apply, before] at executed

theorem frontEndFramerStage_prefix_state (phase : OpenFramingMachine.Phase)
    (data : FrontEndMachine.LocalData) (regs : FrontEndMachine.Registers R)
    (ctx : ∀ k, List (Γ k)) (n : Nat) (bound : n ≤ (frontEndFramerStage phase data).steps)
    (reached : FrontEndMachine.Cfg Γ Λ R)
    (executed : (FrontEndMachine.next caller)^[n]
      (some (FrontEndMachine.cfg (some (FrontEndMachine.framerLabel phase)) regs data ctx)) = some reached) :
    reached.var = frontEndComponentRegisters .framer regs n ∧
      ∀ k, reached.stk (.inr k) = ctx k := by
  cases n with
  | zero =>
      have same := Option.some.inj executed
      subst reached
      exact ⟨rfl, fun _ => rfl⟩
  | succ n =>
      let localCaller : OpenFramingMachine.External (FrontEndMachine.FramerCaller Λ) →
        FrontEndMachine.FramerStatement Γ Λ R := fun _ => .halt
      let localRegs := FrontEndMachine.framerRegisterEquiv.symm regs
      rw [frontEndFramerStage_steps] at bound
      obtain ⟨localReached, localEq, _, _, _, reset⟩ := OpenFramingMachine.phase_prefix localCaller phase
        data.framedRaw data.frameFirstReverse data.frameCertReverse data.inputBits data.certificateBits
        localRegs (FrontEndMachine.framerContext data ctx) (n + 1) bound
      have preserved := OpenFramingMachine.prefix_preserves localCaller phase data.framedRaw
        data.frameFirstReverse data.frameCertReverse data.inputBits data.certificateBits localRegs
        (FrontEndMachine.framerContext data ctx) (n + 1) localReached bound localEq
      have within : ∀ j, j < n + 1 → ∃ actual,
          (OpenFramingMachine.next localCaller)^[j]
            (some (FrontEndMachine.framerView (some (OpenFramingMachine.phaseLabel phase)) localRegs data ctx)) =
              some actual ∧ OpenFramingMachine.Owned actual.l := by
        intro j strict
        obtain ⟨actual, eq, _, _, owned, _⟩ := OpenFramingMachine.phase_prefix localCaller phase
          data.framedRaw data.frameFirstReverse data.frameCertReverse data.inputBits data.certificateBits
          localRegs (FrontEndMachine.framerContext data ctx) j (by omega)
        exact ⟨actual, eq, owned.mp (by omega)⟩
      have translated := FrontEndMachine.framer_prefix_installed caller localCaller (n + 1)
        (FrontEndMachine.framerView (some (OpenFramingMachine.phaseLabel phase)) localRegs data ctx) within
      change (OpenFramingMachine.next localCaller)^[n + 1]
        (some (FrontEndMachine.framerView (some (OpenFramingMachine.phaseLabel phase)) localRegs data ctx)) =
          some localReached at localEq
      rw [localEq, FrontEndMachine.framerCfg_view] at translated
      simp only [Option.map_some, FrontEndMachine.framerLabelEquiv_phase, localRegs,
        Equiv.apply_symm_apply] at translated
      have same : reached = FrontEndMachine.framerCfg localReached :=
        Option.some.inj (executed.symm.trans translated)
      subst reached
      have localReset : localReached.var = OpenFramingMachine.reset localRegs :=
        Prod.ext (reset (by omega)) preserved.1
      refine ⟨?_, ?_⟩
      · change FrontEndMachine.framerRegisterEquiv localReached.var = FrontEndMachine.resetFramer regs
        rw [localReset]
        calc
          FrontEndMachine.framerRegisterEquiv (OpenFramingMachine.reset localRegs) =
              FrontEndMachine.resetFramer (FrontEndMachine.framerRegisterEquiv localRegs) :=
            FrontEndMachine.framerRegisterEquiv_reset localRegs
          _ = FrontEndMachine.resetFramer regs :=
            congrArg FrontEndMachine.resetFramer (FrontEndMachine.framerRegisterEquiv.apply_symm_apply regs)
      · intro k
        rw [FrontEndMachine.framerCfg_outside]
        exact preserved.2.1 (.inr k)

theorem frontEndInputStage_prefix_state (phase : InputParserMachine.OwnedLabels)
    (data : FrontEndMachine.LocalData) (regs : FrontEndMachine.Registers R)
    (ctx : ∀ k, List (Γ k)) (n : Nat) (bound : n ≤ (frontEndInputStage phase data).steps)
    (reached : FrontEndMachine.Cfg Γ Λ R)
    (executed : (FrontEndMachine.next caller)^[n]
      (some (FrontEndMachine.cfg (some (FrontEndMachine.inputOwnedLabel phase)) regs data ctx)) = some reached) :
    reached.var = frontEndComponentRegisters .input regs n ∧
      ∀ k, reached.stk (.inr k) = ctx k := by
  let localCaller : InputParserMachine.External (FrontEndMachine.ExtraLabel Λ) →
    FrontEndMachine.InputStatement Γ Λ R := fun _ => .halt
  have complete := inputPhaseFinish_run localCaller phase (frontEndInputData data) regs
    (FrontEndMachine.inputContext data ctx)
  obtain ⟨localReached, localEq, headRun, _⟩ := complete.prefix localCaller n bound
  have translated := FrontEndMachine.input_prefix_installed caller localCaller n
    (FrontEndMachine.inputView (some (InputParserMachine.ownedLabelEquiv phase).val) regs data ctx)
    (headRun.owned_prefix localCaller)
  change (InputParserMachine.next localCaller)^[n]
    (some (FrontEndMachine.inputView (some (InputParserMachine.ownedLabelEquiv phase).val) regs data ctx)) =
      some localReached at localEq
  rw [localEq, FrontEndMachine.inputCfg_view] at translated
  simp only [Option.map_some, frontEndInputOwned_label, FrontEndMachine.inputRegisterEquiv,
    Equiv.refl_apply] at translated
  have same : reached = FrontEndMachine.inputCfg localReached :=
    Option.some.inj (executed.symm.trans translated)
  subst reached
  refine ⟨?_, ?_⟩
  · change localReached.var = _
    exact headRun.registers localCaller
  · intro k
    rw [FrontEndMachine.inputCfg_outside]
    exact headRun.frame localCaller (.inr k)


theorem frontEndInputDecoderStage_prefix_state (phase : OpenDecoderMachine.Phase)
    (data : FrontEndMachine.LocalData) (regs : FrontEndMachine.Registers R)
    (ctx : ∀ k, List (Γ k)) (n : Nat) (bound : n ≤ (frontEndDecoderStage .input phase data).steps)
    (reached : FrontEndMachine.Cfg Γ Λ R)
    (executed : (FrontEndMachine.next caller)^[n]
      (some (FrontEndMachine.cfg (some (FrontEndMachine.inputDecoderLabel phase)) regs data ctx)) = some reached) :
    reached.var = frontEndComponentRegisters .decoder regs n ∧
      ∀ k, reached.stk (.inr k) = ctx k := by
  cases n with
  | zero =>
      have same := Option.some.inj executed
      subst reached
      exact ⟨rfl, fun _ => rfl⟩
  | succ n =>
      let localCaller : OpenDecoderMachine.External (FrontEndMachine.InputDecoderCaller Λ) →
        FrontEndMachine.InputDecoderStatement Γ Λ R := fun _ => .halt
      let localRegs := FrontEndMachine.decoderRegisterEquiv.symm regs
      rw [frontEndDecoderStage_steps] at bound
      obtain ⟨localReached, localEq, _, _, _, reset⟩ := OpenDecoderMachine.phase_prefix localCaller phase
        (frontEndDecoderRaw .input data) data.decodeReverse (frontEndDecoderOutput .input data)
        localRegs (FrontEndMachine.decoderContext .input data ctx) (n + 1) bound
      have preserved := OpenDecoderMachine.prefix_frame localCaller
        (FrontEndMachine.inputDecoderView (some (OpenDecoderMachine.phaseLabel phase)) localRegs data ctx)
        localReached (n + 1) bound localEq
      have within : ∀ j, j < n + 1 → ∃ actual,
          (OpenDecoderMachine.next localCaller)^[j]
            (some (FrontEndMachine.inputDecoderView (some (OpenDecoderMachine.phaseLabel phase)) localRegs data ctx)) =
              some actual ∧ OpenDecoderMachine.Owned actual.l := by
        intro j strict
        obtain ⟨actual, eq, _, _, owned, _⟩ := OpenDecoderMachine.phase_prefix localCaller phase
          (frontEndDecoderRaw .input data) data.decodeReverse (frontEndDecoderOutput .input data)
          localRegs (FrontEndMachine.decoderContext .input data ctx) j (by omega)
        exact ⟨actual, eq, owned.mp (by omega)⟩
      have translated := FrontEndMachine.inputDecoder_prefix_installed caller localCaller (n + 1)
        (FrontEndMachine.inputDecoderView (some (OpenDecoderMachine.phaseLabel phase)) localRegs data ctx) within
      change (OpenDecoderMachine.next localCaller)^[n + 1]
        (some (FrontEndMachine.inputDecoderView (some (OpenDecoderMachine.phaseLabel phase)) localRegs data ctx)) =
          some localReached at localEq
      rw [localEq, FrontEndMachine.inputDecoderCfg_view] at translated
      simp only [Option.map_some, FrontEndMachine.inputDecoderLabelEquiv_phase, localRegs,
        Equiv.apply_symm_apply] at translated
      have same : reached = FrontEndMachine.inputDecoderCfg localReached :=
        Option.some.inj (executed.symm.trans translated)
      subst reached
      have localReset : localReached.var = OpenDecoderMachine.reset localRegs :=
        Prod.ext (reset (by omega)) preserved.1
      refine ⟨?_, ?_⟩
      · change FrontEndMachine.decoderRegisterEquiv localReached.var = FrontEndMachine.afterInputDecoder regs
        rw [localReset]
        exact frontEndDecoderRegister_reset regs
      · intro k
        rw [FrontEndMachine.inputDecoderCfg_outside]
        exact preserved.2 (.inr k)

theorem frontEndCertificateDecoderStage_prefix_state (phase : OpenDecoderMachine.Phase)
    (data : FrontEndMachine.LocalData) (regs : FrontEndMachine.Registers R)
    (ctx : ∀ k, List (Γ k)) (n : Nat) (bound : n ≤ (frontEndDecoderStage .certificate phase data).steps)
    (reached : FrontEndMachine.Cfg Γ Λ R)
    (executed : (FrontEndMachine.next caller)^[n]
      (some (FrontEndMachine.cfg (some (FrontEndMachine.certificateDecoderLabel phase)) regs data ctx)) = some reached) :
    reached.var = frontEndComponentRegisters .decoder regs n ∧
      ∀ k, reached.stk (.inr k) = ctx k := by
  cases n with
  | zero =>
      have same := Option.some.inj executed
      subst reached
      exact ⟨rfl, fun _ => rfl⟩
  | succ n =>
      let localCaller : OpenDecoderMachine.External (FrontEndMachine.CertificateDecoderCaller Λ) →
        FrontEndMachine.CertificateDecoderStatement Γ Λ R := fun _ => .halt
      let localRegs := FrontEndMachine.decoderRegisterEquiv.symm regs
      rw [frontEndDecoderStage_steps] at bound
      obtain ⟨localReached, localEq, _, _, _, reset⟩ := OpenDecoderMachine.phase_prefix localCaller phase
        (frontEndDecoderRaw .certificate data) data.decodeReverse (frontEndDecoderOutput .certificate data)
        localRegs (FrontEndMachine.decoderContext .certificate data ctx) (n + 1) bound
      have preserved := OpenDecoderMachine.prefix_frame localCaller
        (FrontEndMachine.certificateDecoderView (some (OpenDecoderMachine.phaseLabel phase)) localRegs data ctx)
        localReached (n + 1) bound localEq
      have within : ∀ j, j < n + 1 → ∃ actual,
          (OpenDecoderMachine.next localCaller)^[j]
            (some (FrontEndMachine.certificateDecoderView (some (OpenDecoderMachine.phaseLabel phase)) localRegs data ctx)) =
              some actual ∧ OpenDecoderMachine.Owned actual.l := by
        intro j strict
        obtain ⟨actual, eq, _, _, owned, _⟩ := OpenDecoderMachine.phase_prefix localCaller phase
          (frontEndDecoderRaw .certificate data) data.decodeReverse (frontEndDecoderOutput .certificate data)
          localRegs (FrontEndMachine.decoderContext .certificate data ctx) j (by omega)
        exact ⟨actual, eq, owned.mp (by omega)⟩
      have translated := FrontEndMachine.certificateDecoder_prefix_installed caller localCaller (n + 1)
        (FrontEndMachine.certificateDecoderView (some (OpenDecoderMachine.phaseLabel phase)) localRegs data ctx) within
      change (OpenDecoderMachine.next localCaller)^[n + 1]
        (some (FrontEndMachine.certificateDecoderView (some (OpenDecoderMachine.phaseLabel phase)) localRegs data ctx)) =
          some localReached at localEq
      rw [localEq, FrontEndMachine.certificateDecoderCfg_view] at translated
      simp only [Option.map_some, FrontEndMachine.certificateDecoderLabelEquiv_phase, localRegs,
        Equiv.apply_symm_apply] at translated
      have same : reached = FrontEndMachine.certificateDecoderCfg localReached :=
        Option.some.inj (executed.symm.trans translated)
      subst reached
      have localReset : localReached.var = OpenDecoderMachine.reset localRegs :=
        Prod.ext (reset (by omega)) preserved.1
      refine ⟨?_, ?_⟩
      · change FrontEndMachine.decoderRegisterEquiv localReached.var = FrontEndMachine.afterInputDecoder regs
        rw [localReset]
        exact frontEndDecoderRegister_reset regs
      · intro k
        rw [FrontEndMachine.certificateDecoderCfg_outside]
        exact preserved.2 (.inr k)


theorem frontEndInputFinish_prefix_state (phase : InputParserMachine.OwnedLabels)
    (data : FrontEndMachine.LocalData) (regs : FrontEndMachine.Registers R)
    (ctx : ∀ k, List (Γ k)) (n : Nat) (bound : n ≤ (frontEndInputFinish phase data).steps)
    (reached : FrontEndMachine.Cfg Γ Λ R)
    (executed : (FrontEndMachine.next caller)^[n]
      (some (FrontEndMachine.cfg (some (FrontEndMachine.inputOwnedLabel phase)) regs data ctx)) = some reached) :
    reached.var = frontEndInputRegisters phase data regs n ∧
      ∀ k, reached.stk (.inr k) = ctx k := by
  by_cases early : n ≤ (frontEndInputStage phase data).steps
  · simpa only [frontEndInputRegisters, ite_eq_left early] using
      frontEndInputStage_prefix_state caller phase data regs ctx n early reached executed
  · cases returned : (frontEndInputStage phase data).result with
    | failure =>
        have count : (frontEndInputFinish phase data).steps = (frontEndInputStage phase data).steps := by
          simp only [frontEndInputFinish, returned]
        rw [count] at bound
        omega
    | success =>
        have count : (frontEndInputFinish phase data).steps = (frontEndInputStage phase data).steps +
            (frontEndCertificateFinish .scan (frontEndInputStage phase data).data).steps := by
          simp only [frontEndInputFinish, returned, frontEndJoin]
        have first : (FrontEndMachine.next caller)^[(frontEndInputStage phase data).steps]
            (some (FrontEndMachine.cfg (some (FrontEndMachine.inputOwnedLabel phase)) regs data ctx)) =
            some (FrontEndMachine.cfg (some (FrontEndMachine.certificateDecoderLabel .scan))
              (FrontEndMask.input.apply regs) (frontEndInputStage phase data).data ctx) := by
          simpa only [frontEndStageCfg, returned, frontEndInputStage_masks, frontEndMaskRegs,
            List.foldl_cons, List.foldl_nil] using
            (frontEndInputStage_trace caller phase data regs ctx).run
        have later := frontEnd_prefix_after caller first (Nat.le_of_lt (Nat.lt_of_not_ge early)) executed
        have laterBound : n - (frontEndInputStage phase data).steps ≤ (frontEndCertificateFinish .scan (frontEndInputStage phase data).data).steps := by
          rw [count] at bound
          omega
        have state := frontEndCertificateDecoderStage_prefix_state caller .scan (frontEndInputStage phase data).data
          (FrontEndMask.input.apply regs) ctx (n - (frontEndInputStage phase data).steps) laterBound reached later
        simpa only [frontEndInputRegisters, ite_eq_right early, frontEndCertificateRegisters] using state

theorem frontEndInputDecoderFinish_prefix_state (phase : OpenDecoderMachine.Phase)
    (data : FrontEndMachine.LocalData) (regs : FrontEndMachine.Registers R)
    (ctx : ∀ k, List (Γ k)) (n : Nat) (bound : n ≤ (frontEndInputDecoderFinish phase data).steps)
    (reached : FrontEndMachine.Cfg Γ Λ R)
    (executed : (FrontEndMachine.next caller)^[n]
      (some (FrontEndMachine.cfg (some (FrontEndMachine.inputDecoderLabel phase)) regs data ctx)) = some reached) :
    reached.var = frontEndInputDecoderRegisters phase data regs n ∧
      ∀ k, reached.stk (.inr k) = ctx k := by
  by_cases early : n ≤ (frontEndDecoderStage .input phase data).steps
  · simpa only [frontEndInputDecoderRegisters, ite_eq_left early] using
      frontEndInputDecoderStage_prefix_state caller phase data regs ctx n early reached executed
  · cases returned : (frontEndDecoderStage .input phase data).result with
    | failure =>
        have count : (frontEndInputDecoderFinish phase data).steps = (frontEndDecoderStage .input phase data).steps := by
          simp only [frontEndInputDecoderFinish, returned]
        rw [count] at bound
        omega
    | success =>
        have count : (frontEndInputDecoderFinish phase data).steps = (frontEndDecoderStage .input phase data).steps +
            (frontEndInputFinish (.inl (.source, .init)) (frontEndDecoderStage .input phase data).data).steps := by
          simp only [frontEndInputDecoderFinish, returned, frontEndJoin]
        have first : (FrontEndMachine.next caller)^[(frontEndDecoderStage .input phase data).steps]
            (some (FrontEndMachine.cfg (some (FrontEndMachine.inputDecoderLabel phase)) regs data ctx)) =
            some (FrontEndMachine.cfg (some (FrontEndMachine.inputOwnedLabel (.inl (.source, .init))))
              (FrontEndMask.decoder.apply regs) (frontEndDecoderStage .input phase data).data ctx) := by
          simpa only [frontEndStageCfg, returned, frontEndDecoderStage_masks, frontEndMaskRegs,
            List.foldl_cons, List.foldl_nil, frontEndInputOwned_tree_label] using
            (frontEndInputDecoderStage_trace caller phase data regs ctx).run
        have later := frontEnd_prefix_after caller first (Nat.le_of_lt (Nat.lt_of_not_ge early)) executed
        have laterBound : n - (frontEndDecoderStage .input phase data).steps ≤ (frontEndInputFinish (.inl (.source, .init)) (frontEndDecoderStage .input phase data).data).steps := by
          rw [count] at bound
          omega
        have state := frontEndInputFinish_prefix_state caller (.inl (.source, .init)) (frontEndDecoderStage .input phase data).data
          (FrontEndMask.decoder.apply regs) ctx (n - (frontEndDecoderStage .input phase data).steps) laterBound reached later
        simpa only [frontEndInputDecoderRegisters, ite_eq_right early] using state

theorem frontEndFramerFinish_prefix_state (phase : OpenFramingMachine.Phase)
    (data : FrontEndMachine.LocalData) (regs : FrontEndMachine.Registers R)
    (ctx : ∀ k, List (Γ k)) (n : Nat) (bound : n ≤ (frontEndFramerFinish phase data).steps)
    (reached : FrontEndMachine.Cfg Γ Λ R)
    (executed : (FrontEndMachine.next caller)^[n]
      (some (FrontEndMachine.cfg (some (FrontEndMachine.framerLabel phase)) regs data ctx)) = some reached) :
    reached.var = frontEndFramerRegisters phase data regs n ∧
      ∀ k, reached.stk (.inr k) = ctx k := by
  by_cases early : n ≤ (frontEndFramerStage phase data).steps
  · simpa only [frontEndFramerRegisters, ite_eq_left early] using
      frontEndFramerStage_prefix_state caller phase data regs ctx n early reached executed
  · cases returned : (frontEndFramerStage phase data).result with
    | failure =>
        have count : (frontEndFramerFinish phase data).steps = (frontEndFramerStage phase data).steps := by
          simp only [frontEndFramerFinish, returned]
        rw [count] at bound
        omega
    | success =>
        have count : (frontEndFramerFinish phase data).steps = (frontEndFramerStage phase data).steps +
            (frontEndInputDecoderFinish .scan (frontEndFramerStage phase data).data).steps := by
          simp only [frontEndFramerFinish, returned, frontEndJoin]
        have first : (FrontEndMachine.next caller)^[(frontEndFramerStage phase data).steps]
            (some (FrontEndMachine.cfg (some (FrontEndMachine.framerLabel phase)) regs data ctx)) =
            some (FrontEndMachine.cfg (some (FrontEndMachine.inputDecoderLabel .scan))
              (FrontEndMask.framer.apply regs) (frontEndFramerStage phase data).data ctx) := by
          simpa only [frontEndStageCfg, returned, frontEndFramerStage_masks, frontEndMaskRegs,
            List.foldl_cons, List.foldl_nil] using
            (frontEndFramerStage_trace caller phase data regs ctx).run
        have later := frontEnd_prefix_after caller first (Nat.le_of_lt (Nat.lt_of_not_ge early)) executed
        have laterBound : n - (frontEndFramerStage phase data).steps ≤ (frontEndInputDecoderFinish .scan (frontEndFramerStage phase data).data).steps := by
          rw [count] at bound
          omega
        have state := frontEndInputDecoderFinish_prefix_state caller .scan (frontEndFramerStage phase data).data
          (FrontEndMask.framer.apply regs) ctx (n - (frontEndFramerStage phase data).steps) laterBound reached later
        simpa only [frontEndFramerRegisters, ite_eq_right early] using state

theorem frontEnd_phase_prefix_state (phase : FrontEndMachine.OwnedLabels)
    (data : FrontEndMachine.LocalData) (regs : FrontEndMachine.Registers R)
    (ctx : ∀ k, List (Γ k)) (n : Nat) (bound : n ≤ frontEndPhaseSteps phase data)
    (reached : FrontEndMachine.Cfg Γ Λ R)
    (executed : (FrontEndMachine.next caller)^[n]
      (some (FrontEndMachine.cfg (some (FrontEndMachine.ownedLabelEquiv phase).val) regs data ctx)) = some reached) :
    reached.var = frontEndPhaseRegisters phase data regs n ∧
      ∀ k, reached.stk (.inr k) = ctx k := by
  cases phase with
  | inl phase => exact frontEndInputFinish_prefix_state caller phase data regs ctx n bound reached executed
  | inr phase =>
      cases phase with
      | inl phase => exact frontEndFramerFinish_prefix_state caller phase data regs ctx n bound reached executed
      | inr phase =>
          cases phase with
          | inl phase => exact frontEndInputDecoderFinish_prefix_state caller phase data regs ctx n bound reached executed
          | inr phase =>
              cases phase with
              | scan => exact frontEndCertificateDecoderStage_prefix_state caller .scan data regs ctx n bound reached executed
              | emit => exact frontEndCertificateDecoderStage_prefix_state caller .emit data regs ctx n bound reached executed
              | clear => exact frontEndCertificateDecoderStage_prefix_state caller .clear data regs ctx n bound reached executed

end FrontEndPrefixExecution

/-! The fixed all-dirty FrontEnd potential on actual physical local words. -/

abbrev FrontEndControl := FrontEndMachine.OwnedLabels ⊕ TreeParserMachine.Result

def frontEndControlLabel : FrontEndControl → FrontEndMachine.Label Λ
  | .inl phase => (FrontEndMachine.ownedLabelEquiv phase).val
  | .inr result => frontEndResultLabel result

def frontEndInputControl (control : InputControl) : FrontEndControl :=
  match control with
  | .inl phase => .inl (.inl phase)
  | .inr .success => .inl (.inr (.inr (.inr .scan)))
  | .inr .failure => .inr .failure

def frontEndFramerControl (phase : OpenFramingMachine.Phase) : FrontEndControl :=
  .inl (.inr (.inl phase))

def frontEndDecoderControl (call : FrontEndMachine.DecoderCall)
    (phase : OpenDecoderMachine.Phase) : FrontEndControl :=
  match call with
  | .input => .inl (.inr (.inr (.inl phase)))
  | .certificate => .inl (.inr (.inr (.inr phase)))

def frontEndDecoderSuccess : FrontEndMachine.DecoderCall → FrontEndControl
  | .input => .inl (.inl (.inl (.source, .init)))
  | .certificate => .inr .success

def frontEndPhaseCredit (phase : FrontEndMachine.OwnedLabels)
    (data : FrontEndMachine.LocalData) : Nat :=
  match phase with
  | .inl phase => inputPhaseCredit phase data.inputRaw.length
  | .inr (.inl .scanPrefix) => data.decodeReverse.length + data.inputRaw.length
  | .inr (.inl .copyCert) | .inr (.inl .emitCert) | .inr (.inl .emitFirst) =>
      data.decodeReverse.length + data.inputRaw.length + 1
  | .inr (.inl .clearFirst) => 0
  | .inr (.inr (.inl .scan)) | .inr (.inr (.inl .emit)) =>
      data.decodeReverse.length + data.inputRaw.length + 1
  | .inr (.inr (.inl .clear)) | .inr (.inr (.inr _)) => 0

def frontEndControlCredit (control : FrontEndControl) (data : FrontEndMachine.LocalData) : Nat :=
  match control with
  | .inl phase => frontEndPhaseCredit phase data
  | .inr _ => 0

def frontEndLocalPotential (control : FrontEndControl) (data : FrontEndMachine.LocalData) : Nat :=
  FrontEndMachine.localCells data + frontEndControlCredit control data

def frontEndFramerAdvance (phase : OpenFramingMachine.Phase) (data : FrontEndMachine.LocalData) :
    FrontEndControl × FrontEndMachine.LocalData :=
  match phase with
  | .scanPrefix => match data.framedRaw with
    | [] => (frontEndFramerControl .clearFirst, data)
    | true :: raw => (frontEndFramerControl .copyCert, { data with framedRaw := raw })
    | [false] => (frontEndFramerControl .clearFirst, { data with framedRaw := [] })
    | false :: bit :: raw => (frontEndFramerControl .scanPrefix,
        { data with framedRaw := raw, frameFirstReverse := bit :: data.frameFirstReverse })
  | .copyCert => match data.framedRaw with
    | [] => (frontEndFramerControl .emitCert, data)
    | bit :: raw => (frontEndFramerControl .copyCert,
        { data with framedRaw := raw, frameCertReverse := bit :: data.frameCertReverse })
  | .emitCert => match data.frameCertReverse with
    | [] => (frontEndFramerControl .emitFirst, data)
    | bit :: rev => (frontEndFramerControl .emitCert,
        { data with frameCertReverse := rev, certificateBits := bit :: data.certificateBits })
  | .emitFirst => match data.frameFirstReverse with
    | [] => (frontEndDecoderControl .input .scan, data)
    | bit :: rev => (frontEndFramerControl .emitFirst,
        { data with frameFirstReverse := rev, inputBits := bit :: data.inputBits })
  | .clearFirst => match data.frameFirstReverse with
    | [] => (.inr .failure, data)
    | _ :: rev => (frontEndFramerControl .clearFirst, { data with frameFirstReverse := rev })

def frontEndDecoderAdvance (call : FrontEndMachine.DecoderCall)
    (phase : OpenDecoderMachine.Phase) (data : FrontEndMachine.LocalData) :
    FrontEndControl × FrontEndMachine.LocalData :=
  let raw := frontEndDecoderRaw call data
  let rev := data.decodeReverse
  let out := frontEndDecoderOutput call data
  match phase with
  | .scan => match raw with
    | [] => (frontEndDecoderControl call .emit, data)
    | [_] | [_, _] | [_, _, _] =>
        (frontEndDecoderControl call .clear, frontEndWithDecoder call data [] rev out)
    | b0 :: b1 :: b2 :: b3 :: rest =>
        (frontEndDecoderControl call .scan,
          frontEndWithDecoder call data rest ((decodeTagRun b0 b1 b2 b3).1 :: rev) out)
  | .emit => match rev with
    | [] => (frontEndDecoderSuccess call, data)
    | tag :: rev => (frontEndDecoderControl call .emit,
        frontEndWithDecoder call data raw rev (tag :: out))
  | .clear => match rev with
    | [] => (.inr .failure, data)
    | _ :: rev => (frontEndDecoderControl call .clear,
        frontEndWithDecoder call data raw rev out)

def frontEndAdvance (phase : FrontEndMachine.OwnedLabels) (data : FrontEndMachine.LocalData) :
    FrontEndControl × FrontEndMachine.LocalData :=
  match phase with
  | .inl phase =>
      let advanced := inputAdvance phase (frontEndInputData data)
      (frontEndInputControl advanced.1, frontEndWithInput data advanced.2)
  | .inr (.inl phase) => frontEndFramerAdvance phase data
  | .inr (.inr (.inl phase)) => frontEndDecoderAdvance .input phase data
  | .inr (.inr (.inr phase)) => frontEndDecoderAdvance .certificate phase data

def frontEndPhaseMask : FrontEndMachine.OwnedLabels → FrontEndMask
  | .inl _ => .input
  | .inr (.inl _) => .framer
  | .inr (.inr _) => .decoder

theorem frontEndFramerAdvance_potential (phase : OpenFramingMachine.Phase)
    (data : FrontEndMachine.LocalData) :
    frontEndLocalPotential (frontEndFramerAdvance phase data).1 (frontEndFramerAdvance phase data).2 ≤
      frontEndLocalPotential (frontEndFramerControl phase) data := by
  cases phase <;> simp only [frontEndFramerAdvance] <;> repeat' split
  all_goals
    simp_all only [frontEndLocalPotential, FrontEndMachine.localCells, frontEndControlCredit,
      frontEndFramerControl, frontEndDecoderControl, frontEndPhaseCredit, List.length_cons, List.length_nil]
    omega

theorem frontEndDecoderAdvance_potential (call : FrontEndMachine.DecoderCall)
    (phase : OpenDecoderMachine.Phase) (data : FrontEndMachine.LocalData) :
    frontEndLocalPotential (frontEndDecoderAdvance call phase data).1
        (frontEndDecoderAdvance call phase data).2 ≤
      frontEndLocalPotential (frontEndDecoderControl call phase) data := by
  cases call <;> cases phase <;>
    simp only [frontEndDecoderAdvance, frontEndDecoderRaw, frontEndDecoderOutput] <;> repeat' split
  all_goals
    simp_all only [frontEndLocalPotential, FrontEndMachine.localCells, frontEndControlCredit,
      frontEndDecoderControl, frontEndDecoderSuccess, frontEndPhaseCredit, inputPhaseCredit,
      frontEndWithDecoder, List.length_cons, List.length_nil]
    omega

def frontEndInputOutside (data : FrontEndMachine.LocalData) : Nat :=
  data.framedRaw.length + data.frameFirstReverse.length + data.frameCertReverse.length +
    data.inputBits.length + data.certificateBits.length + data.decodeReverse.length + data.certificateWord.length

theorem frontEndLocalCells_input (data : FrontEndMachine.LocalData) :
    FrontEndMachine.localCells data = inputLocalCells (frontEndInputData data) + frontEndInputOutside data := by
  simp only [FrontEndMachine.localCells, inputLocalCells, frontEndInputData,
    InputParserMachine.treeOutputs_source, InputParserMachine.treeOutputs_target, frontEndInputOutside]
  omega

theorem frontEndLocalCells_withInput (data : FrontEndMachine.LocalData) (input : InputState) :
    FrontEndMachine.localCells (frontEndWithInput data input) = inputLocalCells input + frontEndInputOutside data := by
  simp only [FrontEndMachine.localCells, inputLocalCells, frontEndWithInput, frontEndInputOutside]
  omega

theorem frontEndInputControl_credit (control : InputControl) (data : FrontEndMachine.LocalData)
    (input : InputState) :
    frontEndControlCredit (frontEndInputControl control) (frontEndWithInput data input) =
      inputControlCredit control input := by
  cases control with
  | inl phase => rfl
  | inr result => cases result <;> rfl

@[simp] theorem frontEndControlLabel_framer (phase : OpenFramingMachine.Phase) :
    frontEndControlLabel (Λ := Λ) (frontEndFramerControl phase) = FrontEndMachine.framerLabel phase := rfl

@[simp] theorem frontEndControlLabel_decoder (call : FrontEndMachine.DecoderCall)
    (phase : OpenDecoderMachine.Phase) :
    frontEndControlLabel (Λ := Λ) (frontEndDecoderControl call phase) =
      (match call with
        | .input => FrontEndMachine.inputDecoderLabel phase
        | .certificate => FrontEndMachine.certificateDecoderLabel phase) := by
  cases call <;> cases phase <;> rfl

theorem frontEndInputControl_label (control : InputControl) :
    FrontEndMachine.inputLabelEquiv
      (inputControlLabel (Λ := FrontEndMachine.ExtraLabel Λ) control) =
      frontEndControlLabel (frontEndInputControl control) := by
  cases control with
  | inl phase => rfl
  | inr result => cases result <;> rfl

section FrontEndPotentialExecution
variable [DecidableEq K]
variable (caller : FrontEndMachine.External Λ → FrontEndMachine.Statement Γ Λ R)

theorem frontEndInputAdvance_step (phase : InputParserMachine.OwnedLabels)
    (data : FrontEndMachine.LocalData) (regs : FrontEndMachine.Registers R)
    (ctx : ∀ k, List (Γ k)) :
    FrontEndMachine.step caller
      (FrontEndMachine.cfg (some (FrontEndMachine.inputOwnedLabel phase)) regs data ctx) =
      some (FrontEndMachine.cfg (some (frontEndControlLabel
        (frontEndInputControl (inputAdvance phase (frontEndInputData data)).1)))
        (FrontEndMask.input.apply regs)
        (frontEndWithInput data (inputAdvance phase (frontEndInputData data)).2) ctx) := by
  let localCaller : InputParserMachine.External (FrontEndMachine.ExtraLabel Λ) →
    FrontEndMachine.InputStatement Γ Λ R := fun _ => .halt
  let advanced := inputAdvance phase (frontEndInputData data)
  have equation := inputAdvance_step localCaller phase (frontEndInputData data) regs
    (FrontEndMachine.inputContext data ctx)
  have run := InputParserMachine.Runs.one localCaller (InputParserMachine.ownedLabelEquiv phase).property equation
  change InputParserMachine.Runs localCaller 1
    (FrontEndMachine.inputView (some (InputParserMachine.ownedLabelEquiv phase).val) regs data ctx)
    (inputCfg (some (inputControlLabel advanced.1)) (InputParserMachine.reset regs) advanced.2
      (FrontEndMachine.inputContext data ctx)) at run
  have endpoint : inputCfg (some (inputControlLabel (Λ := FrontEndMachine.ExtraLabel Λ) advanced.1))
      (InputParserMachine.reset regs) advanced.2 (FrontEndMachine.inputContext data ctx) =
      FrontEndMachine.inputView (some (inputControlLabel advanced.1))
        (InputParserMachine.reset regs) (frontEndWithInput data advanced.2) ctx := by
    simp only [inputCfg, FrontEndMachine.inputView, frontEndWithInput, frontEndInput_outputs]
    rfl
  rw [endpoint] at run
  have translated := (input_trace_transport caller localCaller run).run
  rw [FrontEndMachine.inputCfg_view, FrontEndMachine.inputCfg_view] at translated
  have resetEq : InputParserMachine.reset regs = FrontEndMask.input.apply regs := rfl
  rw [resetEq] at translated
  simpa only [Function.iterate_one, FrontEndMachine.next, Option.bind_some, Option.map_some,
    frontEndInputOwned_label, frontEndInputControl_label, FrontEndMachine.inputRegisterEquiv,
    Equiv.refl_apply, FrontEndMask.apply, advanced] using translated

theorem frontEndInputAdvance_potential (phase : InputParserMachine.OwnedLabels)
    (data : FrontEndMachine.LocalData) (regs : FrontEndMachine.Registers R)
    (ctx : ∀ k, List (Γ k)) :
    frontEndLocalPotential (frontEndInputControl (inputAdvance phase (frontEndInputData data)).1)
        (frontEndWithInput data (inputAdvance phase (frontEndInputData data)).2) ≤
      frontEndLocalPotential (.inl (.inl phase)) data := by
  let localCaller : InputParserMachine.External Unit →
    InputParserMachine.Statement (FrontEndMachine.inputProtectedAlphabet Γ) Unit (FrontEndMachine.InputRegisterCaller R) := fun _ => .halt
  have localBound := inputAdvance_potential localCaller phase (frontEndInputData data) regs
    (FrontEndMachine.inputContext data ctx)
  unfold frontEndLocalPotential
  rw [frontEndLocalCells_withInput, frontEndInputControl_credit, frontEndLocalCells_input]
  change inputLocalCells (inputAdvance phase (frontEndInputData data)).2 + frontEndInputOutside data +
      inputControlCredit (inputAdvance phase (frontEndInputData data)).1
        (inputAdvance phase (frontEndInputData data)).2 ≤
    inputLocalCells (frontEndInputData data) + frontEndInputOutside data +
      inputControlCredit (.inl phase) (frontEndInputData data)
  unfold inputPotential at localBound
  omega

theorem frontEndFramer_transition (phase : OpenFramingMachine.Phase)
    (data afterData : FrontEndMachine.LocalData) (regs : FrontEndMachine.Registers R)
    (ctx : ∀ k, List (Γ k)) (afterLabel : OpenFramingMachine.Label (FrontEndMachine.FramerCaller Λ))
    (equation : OpenFramingMachine.step (fun _ => .halt)
      (FrontEndMachine.framerView (some (OpenFramingMachine.phaseLabel phase))
        (FrontEndMachine.framerRegisterEquiv.symm regs) data ctx) =
      some (FrontEndMachine.framerView (some afterLabel)
        (OpenFramingMachine.reset (FrontEndMachine.framerRegisterEquiv.symm regs)) afterData ctx)) :
    FrontEndMachine.step caller
      (FrontEndMachine.cfg (some (FrontEndMachine.framerLabel phase)) regs data ctx) =
      some (FrontEndMachine.cfg (some (FrontEndMachine.framerLabelEquiv afterLabel))
        (FrontEndMask.framer.apply regs) afterData ctx) := by
  have within : ∀ j, j < 1 → ∃ reached,
      (OpenFramingMachine.next (fun _ => .halt))^[j]
        (some (FrontEndMachine.framerView (Λ := Λ) (some (OpenFramingMachine.phaseLabel phase))
          (FrontEndMachine.framerRegisterEquiv.symm regs) data ctx)) = some reached ∧
          OpenFramingMachine.Owned reached.l := by
    intro j strict
    have zero : j = 0 := by omega
    subst j
    exact ⟨_, rfl, True.intro⟩
  have translated := FrontEndMachine.framer_prefix_installed caller (fun _ => .halt) 1
    (FrontEndMachine.framerView (Λ := Λ) (some (OpenFramingMachine.phaseLabel phase))
      (FrontEndMachine.framerRegisterEquiv.symm regs) data ctx) within
  simp only [Function.iterate_one, OpenFramingMachine.next_some, equation, Option.map_some,
    FrontEndMachine.framerCfg_view, FrontEndMachine.framerLabelEquiv_phase,
    FrontEndMachine.framerRegisterEquiv_reset, Equiv.apply_symm_apply,
    FrontEndMachine.next, Option.bind_some] at translated
  exact translated


theorem frontEndFramerAdvance_step (phase : OpenFramingMachine.Phase)
    (data : FrontEndMachine.LocalData) (regs : FrontEndMachine.Registers R)
    (ctx : ∀ k, List (Γ k)) :
    FrontEndMachine.step caller
      (FrontEndMachine.cfg (some (FrontEndMachine.framerLabel phase)) regs data ctx) =
      some (FrontEndMachine.cfg (some (frontEndControlLabel (frontEndFramerAdvance phase data).1))
        (FrontEndMask.framer.apply regs) (frontEndFramerAdvance phase data).2 ctx) := by
  cases phase with
  | scanPrefix =>
      cases rawEq : data.framedRaw with
      | nil =>
          simp only [frontEndFramerAdvance, rawEq, frontEndControlLabel_framer]
          apply frontEndFramer_transition caller .scanPrefix data data regs ctx
            (OpenFramingMachine.phaseLabel .clearFirst)
          simpa only [FrontEndMachine.framerView, rawEq] using
            OpenFramingMachine.scanPrefix_step_nil (fun _ => .halt)
              data.frameFirstReverse data.frameCertReverse data.inputBits data.certificateBits
              (FrontEndMachine.framerRegisterEquiv.symm regs) (FrontEndMachine.framerContext data ctx)
      | cons bit raw =>
          cases bit with
          | false =>
              cases raw with
              | nil =>
                  simp only [frontEndFramerAdvance, rawEq, frontEndControlLabel_framer]
                  apply frontEndFramer_transition caller .scanPrefix data { data with framedRaw := [] } regs ctx
                    (OpenFramingMachine.phaseLabel .clearFirst)
                  have contextEq : FrontEndMachine.framerContext ({ data with framedRaw := [] }) ctx =
                      FrontEndMachine.framerContext data ctx := rfl
                  simpa only [FrontEndMachine.framerView, contextEq, rawEq] using
                    OpenFramingMachine.scanPrefix_step_false_nil (fun _ => .halt)
                      data.frameFirstReverse data.frameCertReverse data.inputBits data.certificateBits
                      (FrontEndMachine.framerRegisterEquiv.symm regs) (FrontEndMachine.framerContext data ctx)
              | cons bit raw =>
                  simp only [frontEndFramerAdvance, rawEq, frontEndControlLabel_framer]
                  apply frontEndFramer_transition caller .scanPrefix data
                    { data with framedRaw := raw, frameFirstReverse := bit :: data.frameFirstReverse } regs ctx
                    (OpenFramingMachine.phaseLabel .scanPrefix)
                  have contextEq : FrontEndMachine.framerContext ({ data with framedRaw := raw, frameFirstReverse := bit :: data.frameFirstReverse }) ctx =
                      FrontEndMachine.framerContext data ctx := rfl
                  simpa only [FrontEndMachine.framerView, contextEq, rawEq] using
                    OpenFramingMachine.scanPrefix_step_false_cons (fun _ => .halt) bit raw
                      data.frameFirstReverse data.frameCertReverse data.inputBits data.certificateBits
                      (FrontEndMachine.framerRegisterEquiv.symm regs) (FrontEndMachine.framerContext data ctx)
          | true =>
              simp only [frontEndFramerAdvance, rawEq, frontEndControlLabel_framer]
              apply frontEndFramer_transition caller .scanPrefix data { data with framedRaw := raw } regs ctx
                (OpenFramingMachine.phaseLabel .copyCert)
              have contextEq : FrontEndMachine.framerContext ({ data with framedRaw := raw }) ctx =
                  FrontEndMachine.framerContext data ctx := rfl
              simpa only [FrontEndMachine.framerView, contextEq, rawEq] using
                OpenFramingMachine.scanPrefix_step_true (fun _ => .halt) raw
                  data.frameFirstReverse data.frameCertReverse data.inputBits data.certificateBits
                  (FrontEndMachine.framerRegisterEquiv.symm regs) (FrontEndMachine.framerContext data ctx)
  | copyCert =>
      cases wordEq : data.framedRaw with
      | nil =>
          simp only [frontEndFramerAdvance, wordEq, frontEndControlLabel_framer]
          apply frontEndFramer_transition caller .copyCert data data regs ctx (OpenFramingMachine.phaseLabel .emitCert)
          simpa only [FrontEndMachine.framerView, wordEq] using
            OpenFramingMachine.copyCert_step_nil (fun _ => .halt) data.frameFirstReverse data.frameCertReverse data.inputBits data.certificateBits
              (FrontEndMachine.framerRegisterEquiv.symm regs) (FrontEndMachine.framerContext data ctx)
      | cons bit raw =>
          simp only [frontEndFramerAdvance, wordEq, frontEndControlLabel_framer]
          apply frontEndFramer_transition caller .copyCert data { data with framedRaw := raw, frameCertReverse := bit :: data.frameCertReverse } regs ctx (OpenFramingMachine.phaseLabel .copyCert)
          have contextEq : FrontEndMachine.framerContext ({ data with framedRaw := raw, frameCertReverse := bit :: data.frameCertReverse }) ctx =
              FrontEndMachine.framerContext data ctx := rfl
          simpa only [FrontEndMachine.framerView, contextEq, wordEq] using
            OpenFramingMachine.copyCert_step_cons (fun _ => .halt) bit raw data.frameFirstReverse data.frameCertReverse data.inputBits data.certificateBits
              (FrontEndMachine.framerRegisterEquiv.symm regs) (FrontEndMachine.framerContext data ctx)
  | emitCert =>
      cases wordEq : data.frameCertReverse with
      | nil =>
          simp only [frontEndFramerAdvance, wordEq, frontEndControlLabel_framer]
          apply frontEndFramer_transition caller .emitCert data data regs ctx (OpenFramingMachine.phaseLabel .emitFirst)
          simpa only [FrontEndMachine.framerView, wordEq] using
            OpenFramingMachine.emitCert_step_nil (fun _ => .halt) data.framedRaw data.frameFirstReverse data.inputBits data.certificateBits
              (FrontEndMachine.framerRegisterEquiv.symm regs) (FrontEndMachine.framerContext data ctx)
      | cons bit rev =>
          simp only [frontEndFramerAdvance, wordEq, frontEndControlLabel_framer]
          apply frontEndFramer_transition caller .emitCert data { data with frameCertReverse := rev, certificateBits := bit :: data.certificateBits } regs ctx (OpenFramingMachine.phaseLabel .emitCert)
          have contextEq : FrontEndMachine.framerContext ({ data with frameCertReverse := rev, certificateBits := bit :: data.certificateBits }) ctx =
              FrontEndMachine.framerContext data ctx := rfl
          simpa only [FrontEndMachine.framerView, contextEq, wordEq] using
            OpenFramingMachine.emitCert_step_cons (fun _ => .halt) bit data.framedRaw data.frameFirstReverse rev data.inputBits data.certificateBits
              (FrontEndMachine.framerRegisterEquiv.symm regs) (FrontEndMachine.framerContext data ctx)
  | emitFirst =>
      cases wordEq : data.frameFirstReverse with
      | nil =>
          simp only [frontEndFramerAdvance, wordEq, frontEndControlLabel_decoder]
          apply frontEndFramer_transition caller .emitFirst data data regs ctx (OpenFramingMachine.resultLabel .success)
          simpa only [FrontEndMachine.framerView, wordEq] using
            OpenFramingMachine.emitFirst_step_nil (fun _ => .halt) data.framedRaw data.frameCertReverse data.inputBits data.certificateBits
              (FrontEndMachine.framerRegisterEquiv.symm regs) (FrontEndMachine.framerContext data ctx)
      | cons bit rev =>
          simp only [frontEndFramerAdvance, wordEq, frontEndControlLabel_framer]
          apply frontEndFramer_transition caller .emitFirst data { data with frameFirstReverse := rev, inputBits := bit :: data.inputBits } regs ctx (OpenFramingMachine.phaseLabel .emitFirst)
          have contextEq : FrontEndMachine.framerContext ({ data with frameFirstReverse := rev, inputBits := bit :: data.inputBits }) ctx =
              FrontEndMachine.framerContext data ctx := rfl
          simpa only [FrontEndMachine.framerView, contextEq, wordEq] using
            OpenFramingMachine.emitFirst_step_cons (fun _ => .halt) bit data.framedRaw rev data.frameCertReverse data.inputBits data.certificateBits
              (FrontEndMachine.framerRegisterEquiv.symm regs) (FrontEndMachine.framerContext data ctx)
  | clearFirst =>
      cases wordEq : data.frameFirstReverse with
      | nil =>
          simp only [frontEndFramerAdvance, wordEq, frontEndControlLabel, frontEndResultLabel]
          apply frontEndFramer_transition caller .clearFirst data data regs ctx (OpenFramingMachine.resultLabel .failure)
          simpa only [FrontEndMachine.framerView, wordEq] using
            OpenFramingMachine.clearFirst_step_nil (fun _ => .halt) data.framedRaw data.frameCertReverse data.inputBits data.certificateBits
              (FrontEndMachine.framerRegisterEquiv.symm regs) (FrontEndMachine.framerContext data ctx)
      | cons bit rev =>
          simp only [frontEndFramerAdvance, wordEq, frontEndControlLabel_framer]
          apply frontEndFramer_transition caller .clearFirst data { data with frameFirstReverse := rev } regs ctx (OpenFramingMachine.phaseLabel .clearFirst)
          have contextEq : FrontEndMachine.framerContext ({ data with frameFirstReverse := rev }) ctx =
              FrontEndMachine.framerContext data ctx := rfl
          simpa only [FrontEndMachine.framerView, contextEq, wordEq] using
            OpenFramingMachine.clearFirst_step_cons (fun _ => .halt) bit data.framedRaw rev data.frameCertReverse data.inputBits data.certificateBits
              (FrontEndMachine.framerRegisterEquiv.symm regs) (FrontEndMachine.framerContext data ctx)


theorem frontEndInputDecoder_transition (phase : OpenDecoderMachine.Phase)
    (data afterData : FrontEndMachine.LocalData) (regs : FrontEndMachine.Registers R)
    (ctx : ∀ k, List (Γ k)) (afterLabel : OpenDecoderMachine.Label (FrontEndMachine.InputDecoderCaller Λ))
    (equation : OpenDecoderMachine.step (fun _ => .halt)
      (FrontEndMachine.inputDecoderView (some (OpenDecoderMachine.phaseLabel phase))
        (FrontEndMachine.decoderRegisterEquiv.symm regs) data ctx) =
      some (FrontEndMachine.inputDecoderView (some afterLabel)
        (OpenDecoderMachine.reset (FrontEndMachine.decoderRegisterEquiv.symm regs)) afterData ctx)) :
    FrontEndMachine.step caller
      (FrontEndMachine.cfg (some (FrontEndMachine.inputDecoderLabel phase)) regs data ctx) =
      some (FrontEndMachine.cfg (some (FrontEndMachine.inputDecoderLabelEquiv afterLabel))
        (FrontEndMask.decoder.apply regs) afterData ctx) := by
  have within : ∀ j, j < 1 → ∃ reached,
      (OpenDecoderMachine.next (fun _ => .halt))^[j]
        (some (FrontEndMachine.inputDecoderView (Λ := Λ) (some (OpenDecoderMachine.phaseLabel phase))
          (FrontEndMachine.decoderRegisterEquiv.symm regs) data ctx)) = some reached ∧
          OpenDecoderMachine.Owned reached.l := by
    intro j strict
    have zero : j = 0 := by omega
    subst j
    exact ⟨_, rfl, True.intro⟩
  have translated := FrontEndMachine.inputDecoder_prefix_installed caller (fun _ => .halt) 1
    (FrontEndMachine.inputDecoderView (Λ := Λ) (some (OpenDecoderMachine.phaseLabel phase))
      (FrontEndMachine.decoderRegisterEquiv.symm regs) data ctx) within
  simp only [Function.iterate_one, OpenDecoderMachine.next_some, equation, Option.map_some,
    FrontEndMachine.inputDecoderCfg_view, FrontEndMachine.inputDecoderLabelEquiv_phase,
    frontEndDecoderRegister_reset, Equiv.apply_symm_apply,
    FrontEndMachine.next, Option.bind_some] at translated
  exact translated

theorem frontEndCertificateDecoder_transition (phase : OpenDecoderMachine.Phase)
    (data afterData : FrontEndMachine.LocalData) (regs : FrontEndMachine.Registers R)
    (ctx : ∀ k, List (Γ k)) (afterLabel : OpenDecoderMachine.Label (FrontEndMachine.CertificateDecoderCaller Λ))
    (equation : OpenDecoderMachine.step (fun _ => .halt)
      (FrontEndMachine.certificateDecoderView (some (OpenDecoderMachine.phaseLabel phase))
        (FrontEndMachine.decoderRegisterEquiv.symm regs) data ctx) =
      some (FrontEndMachine.certificateDecoderView (some afterLabel)
        (OpenDecoderMachine.reset (FrontEndMachine.decoderRegisterEquiv.symm regs)) afterData ctx)) :
    FrontEndMachine.step caller
      (FrontEndMachine.cfg (some (FrontEndMachine.certificateDecoderLabel phase)) regs data ctx) =
      some (FrontEndMachine.cfg (some (FrontEndMachine.certificateDecoderLabelEquiv afterLabel))
        (FrontEndMask.decoder.apply regs) afterData ctx) := by
  have within : ∀ j, j < 1 → ∃ reached,
      (OpenDecoderMachine.next (fun _ => .halt))^[j]
        (some (FrontEndMachine.certificateDecoderView (Λ := Λ) (some (OpenDecoderMachine.phaseLabel phase))
          (FrontEndMachine.decoderRegisterEquiv.symm regs) data ctx)) = some reached ∧
          OpenDecoderMachine.Owned reached.l := by
    intro j strict
    have zero : j = 0 := by omega
    subst j
    exact ⟨_, rfl, True.intro⟩
  have translated := FrontEndMachine.certificateDecoder_prefix_installed caller (fun _ => .halt) 1
    (FrontEndMachine.certificateDecoderView (Λ := Λ) (some (OpenDecoderMachine.phaseLabel phase))
      (FrontEndMachine.decoderRegisterEquiv.symm regs) data ctx) within
  simp only [Function.iterate_one, OpenDecoderMachine.next_some, equation, Option.map_some,
    FrontEndMachine.certificateDecoderCfg_view, FrontEndMachine.certificateDecoderLabelEquiv_phase,
    frontEndDecoderRegister_reset, Equiv.apply_symm_apply,
    FrontEndMachine.next, Option.bind_some] at translated
  exact translated

theorem frontEndDecoderAdvance_step (call : FrontEndMachine.DecoderCall) (phase : OpenDecoderMachine.Phase)
    (data : FrontEndMachine.LocalData) (regs : FrontEndMachine.Registers R)
    (ctx : ∀ k, List (Γ k)) :
    FrontEndMachine.step caller
      (FrontEndMachine.cfg (some (frontEndControlLabel (frontEndDecoderControl call phase))) regs data ctx) =
      some (FrontEndMachine.cfg (some (frontEndControlLabel (frontEndDecoderAdvance call phase data).1))
        (FrontEndMask.decoder.apply regs) (frontEndDecoderAdvance call phase data).2 ctx) := by
  cases call with
  | input =>
      cases phase with
      | scan =>
          cases wordEq : data.inputBits with
          | nil =>
              simp only [frontEndDecoderAdvance, frontEndDecoderRaw, frontEndControlLabel_decoder, wordEq]
              apply frontEndInputDecoder_transition caller .scan data data regs ctx (OpenDecoderMachine.phaseLabel .emit)
              simpa only [FrontEndMachine.inputDecoderView, wordEq] using
                OpenDecoderMachine.scan_step_nil (fun _ => .halt) data.decodeReverse data.inputRaw (FrontEndMachine.decoderRegisterEquiv.symm regs) (FrontEndMachine.decoderContext .input data ctx)
          | cons b0 rest =>
              cases rest with
              | nil =>
                  simp only [frontEndDecoderAdvance, frontEndDecoderRaw, frontEndControlLabel_decoder, wordEq]
                  apply frontEndInputDecoder_transition caller .scan data
                    (frontEndWithDecoder .input data [] data.decodeReverse data.inputRaw) regs ctx
                    (OpenDecoderMachine.phaseLabel .clear)
                  simp only [FrontEndMachine.inputDecoderView]
                  rw [frontEndDecoderContext_with]
                  simpa only [frontEndWithDecoder, wordEq] using
                    OpenDecoderMachine.scan_step_one (fun _ => .halt) b0 data.decodeReverse data.inputRaw (FrontEndMachine.decoderRegisterEquiv.symm regs) (FrontEndMachine.decoderContext .input data ctx)
              | cons b1 rest =>
                  cases rest with
                  | nil =>
                      simp only [frontEndDecoderAdvance, frontEndDecoderRaw, frontEndControlLabel_decoder, wordEq]
                      apply frontEndInputDecoder_transition caller .scan data
                        (frontEndWithDecoder .input data [] data.decodeReverse data.inputRaw) regs ctx
                        (OpenDecoderMachine.phaseLabel .clear)
                      simp only [FrontEndMachine.inputDecoderView]
                      rw [frontEndDecoderContext_with]
                      simpa only [frontEndWithDecoder, wordEq] using
                        OpenDecoderMachine.scan_step_two (fun _ => .halt) b0 b1 data.decodeReverse data.inputRaw (FrontEndMachine.decoderRegisterEquiv.symm regs) (FrontEndMachine.decoderContext .input data ctx)
                  | cons b2 rest =>
                      cases rest with
                      | nil =>
                          simp only [frontEndDecoderAdvance, frontEndDecoderRaw, frontEndControlLabel_decoder, wordEq]
                          apply frontEndInputDecoder_transition caller .scan data
                            (frontEndWithDecoder .input data [] data.decodeReverse data.inputRaw) regs ctx
                            (OpenDecoderMachine.phaseLabel .clear)
                          simp only [FrontEndMachine.inputDecoderView]
                          rw [frontEndDecoderContext_with]
                          simpa only [frontEndWithDecoder, wordEq] using
                            OpenDecoderMachine.scan_step_three (fun _ => .halt) b0 b1 b2 data.decodeReverse data.inputRaw (FrontEndMachine.decoderRegisterEquiv.symm regs) (FrontEndMachine.decoderContext .input data ctx)
                      | cons b3 rest =>
                          simp only [frontEndDecoderAdvance, frontEndDecoderRaw, frontEndDecoderOutput, frontEndControlLabel_decoder, wordEq]
                          apply frontEndInputDecoder_transition caller .scan data
                            (frontEndWithDecoder .input data rest ((decodeTagRun b0 b1 b2 b3).1 :: data.decodeReverse) data.inputRaw) regs ctx
                            (OpenDecoderMachine.phaseLabel .scan)
                          simp only [FrontEndMachine.inputDecoderView]
                          rw [frontEndDecoderContext_with]
                          simpa only [frontEndWithDecoder, wordEq] using
                            OpenDecoderMachine.scan_step_block (fun _ => .halt) b0 b1 b2 b3 rest data.decodeReverse data.inputRaw (FrontEndMachine.decoderRegisterEquiv.symm regs) (FrontEndMachine.decoderContext .input data ctx)
      | emit =>
          cases revEq : data.decodeReverse with
          | nil =>
              simp only [frontEndDecoderAdvance, revEq, frontEndDecoderSuccess, frontEndControlLabel, frontEndResultLabel]
              apply frontEndInputDecoder_transition caller .emit data data regs ctx (OpenDecoderMachine.resultLabel .success)
              simpa only [FrontEndMachine.inputDecoderView, revEq] using
                OpenDecoderMachine.emit_step_nil (fun _ => .halt) data.inputBits data.inputRaw (FrontEndMachine.decoderRegisterEquiv.symm regs) (FrontEndMachine.decoderContext .input data ctx)
          | cons tag rev =>
              simp only [frontEndDecoderAdvance, frontEndDecoderRaw, frontEndDecoderOutput, frontEndControlLabel_decoder, revEq]
              apply frontEndInputDecoder_transition caller .emit data
                (frontEndWithDecoder .input data data.inputBits rev (tag :: data.inputRaw)) regs ctx
                (OpenDecoderMachine.phaseLabel .emit)
              simp only [FrontEndMachine.inputDecoderView]
              rw [frontEndDecoderContext_with]
              simpa only [frontEndWithDecoder, revEq] using
                OpenDecoderMachine.emit_step_cons (fun _ => .halt) tag rev data.inputBits data.inputRaw (FrontEndMachine.decoderRegisterEquiv.symm regs) (FrontEndMachine.decoderContext .input data ctx)
      | clear =>
          cases revEq : data.decodeReverse with
          | nil =>
              simp only [frontEndDecoderAdvance, revEq, frontEndControlLabel, frontEndResultLabel]
              apply frontEndInputDecoder_transition caller .clear data data regs ctx (OpenDecoderMachine.resultLabel .failure)
              simpa only [FrontEndMachine.inputDecoderView, revEq] using
                OpenDecoderMachine.clear_step_nil (fun _ => .halt) data.inputBits data.inputRaw (FrontEndMachine.decoderRegisterEquiv.symm regs) (FrontEndMachine.decoderContext .input data ctx)
          | cons tag rev =>
              simp only [frontEndDecoderAdvance, frontEndDecoderRaw, frontEndDecoderOutput, frontEndControlLabel_decoder, revEq]
              apply frontEndInputDecoder_transition caller .clear data
                (frontEndWithDecoder .input data data.inputBits rev data.inputRaw) regs ctx
                (OpenDecoderMachine.phaseLabel .clear)
              simp only [FrontEndMachine.inputDecoderView]
              rw [frontEndDecoderContext_with]
              simpa only [frontEndWithDecoder, revEq] using
                OpenDecoderMachine.clear_step_cons (fun _ => .halt) tag rev data.inputBits data.inputRaw (FrontEndMachine.decoderRegisterEquiv.symm regs) (FrontEndMachine.decoderContext .input data ctx)
  | certificate =>
      cases phase with
      | scan =>
          cases wordEq : data.certificateBits with
          | nil =>
              simp only [frontEndDecoderAdvance, frontEndDecoderRaw, frontEndControlLabel_decoder, wordEq]
              apply frontEndCertificateDecoder_transition caller .scan data data regs ctx (OpenDecoderMachine.phaseLabel .emit)
              simpa only [FrontEndMachine.certificateDecoderView, wordEq] using
                OpenDecoderMachine.scan_step_nil (fun _ => .halt) data.decodeReverse data.certificateWord (FrontEndMachine.decoderRegisterEquiv.symm regs) (FrontEndMachine.decoderContext .certificate data ctx)
          | cons b0 rest =>
              cases rest with
              | nil =>
                  simp only [frontEndDecoderAdvance, frontEndDecoderRaw, frontEndControlLabel_decoder, wordEq]
                  apply frontEndCertificateDecoder_transition caller .scan data
                    (frontEndWithDecoder .certificate data [] data.decodeReverse data.certificateWord) regs ctx
                    (OpenDecoderMachine.phaseLabel .clear)
                  simp only [FrontEndMachine.certificateDecoderView]
                  rw [frontEndDecoderContext_with]
                  simpa only [frontEndWithDecoder, wordEq] using
                    OpenDecoderMachine.scan_step_one (fun _ => .halt) b0 data.decodeReverse data.certificateWord (FrontEndMachine.decoderRegisterEquiv.symm regs) (FrontEndMachine.decoderContext .certificate data ctx)
              | cons b1 rest =>
                  cases rest with
                  | nil =>
                      simp only [frontEndDecoderAdvance, frontEndDecoderRaw, frontEndControlLabel_decoder, wordEq]
                      apply frontEndCertificateDecoder_transition caller .scan data
                        (frontEndWithDecoder .certificate data [] data.decodeReverse data.certificateWord) regs ctx
                        (OpenDecoderMachine.phaseLabel .clear)
                      simp only [FrontEndMachine.certificateDecoderView]
                      rw [frontEndDecoderContext_with]
                      simpa only [frontEndWithDecoder, wordEq] using
                        OpenDecoderMachine.scan_step_two (fun _ => .halt) b0 b1 data.decodeReverse data.certificateWord (FrontEndMachine.decoderRegisterEquiv.symm regs) (FrontEndMachine.decoderContext .certificate data ctx)
                  | cons b2 rest =>
                      cases rest with
                      | nil =>
                          simp only [frontEndDecoderAdvance, frontEndDecoderRaw, frontEndControlLabel_decoder, wordEq]
                          apply frontEndCertificateDecoder_transition caller .scan data
                            (frontEndWithDecoder .certificate data [] data.decodeReverse data.certificateWord) regs ctx
                            (OpenDecoderMachine.phaseLabel .clear)
                          simp only [FrontEndMachine.certificateDecoderView]
                          rw [frontEndDecoderContext_with]
                          simpa only [frontEndWithDecoder, wordEq] using
                            OpenDecoderMachine.scan_step_three (fun _ => .halt) b0 b1 b2 data.decodeReverse data.certificateWord (FrontEndMachine.decoderRegisterEquiv.symm regs) (FrontEndMachine.decoderContext .certificate data ctx)
                      | cons b3 rest =>
                          simp only [frontEndDecoderAdvance, frontEndDecoderRaw, frontEndDecoderOutput, frontEndControlLabel_decoder, wordEq]
                          apply frontEndCertificateDecoder_transition caller .scan data
                            (frontEndWithDecoder .certificate data rest ((decodeTagRun b0 b1 b2 b3).1 :: data.decodeReverse) data.certificateWord) regs ctx
                            (OpenDecoderMachine.phaseLabel .scan)
                          simp only [FrontEndMachine.certificateDecoderView]
                          rw [frontEndDecoderContext_with]
                          simpa only [frontEndWithDecoder, wordEq] using
                            OpenDecoderMachine.scan_step_block (fun _ => .halt) b0 b1 b2 b3 rest data.decodeReverse data.certificateWord (FrontEndMachine.decoderRegisterEquiv.symm regs) (FrontEndMachine.decoderContext .certificate data ctx)
      | emit =>
          cases revEq : data.decodeReverse with
          | nil =>
              simp only [frontEndDecoderAdvance, revEq, frontEndDecoderSuccess, frontEndControlLabel, frontEndResultLabel]
              apply frontEndCertificateDecoder_transition caller .emit data data regs ctx (OpenDecoderMachine.resultLabel .success)
              simpa only [FrontEndMachine.certificateDecoderView, revEq] using
                OpenDecoderMachine.emit_step_nil (fun _ => .halt) data.certificateBits data.certificateWord (FrontEndMachine.decoderRegisterEquiv.symm regs) (FrontEndMachine.decoderContext .certificate data ctx)
          | cons tag rev =>
              simp only [frontEndDecoderAdvance, frontEndDecoderRaw, frontEndDecoderOutput, frontEndControlLabel_decoder, revEq]
              apply frontEndCertificateDecoder_transition caller .emit data
                (frontEndWithDecoder .certificate data data.certificateBits rev (tag :: data.certificateWord)) regs ctx
                (OpenDecoderMachine.phaseLabel .emit)
              simp only [FrontEndMachine.certificateDecoderView]
              rw [frontEndDecoderContext_with]
              simpa only [frontEndWithDecoder, revEq] using
                OpenDecoderMachine.emit_step_cons (fun _ => .halt) tag rev data.certificateBits data.certificateWord (FrontEndMachine.decoderRegisterEquiv.symm regs) (FrontEndMachine.decoderContext .certificate data ctx)
      | clear =>
          cases revEq : data.decodeReverse with
          | nil =>
              simp only [frontEndDecoderAdvance, revEq, frontEndControlLabel, frontEndResultLabel]
              apply frontEndCertificateDecoder_transition caller .clear data data regs ctx (OpenDecoderMachine.resultLabel .failure)
              simpa only [FrontEndMachine.certificateDecoderView, revEq] using
                OpenDecoderMachine.clear_step_nil (fun _ => .halt) data.certificateBits data.certificateWord (FrontEndMachine.decoderRegisterEquiv.symm regs) (FrontEndMachine.decoderContext .certificate data ctx)
          | cons tag rev =>
              simp only [frontEndDecoderAdvance, frontEndDecoderRaw, frontEndDecoderOutput, frontEndControlLabel_decoder, revEq]
              apply frontEndCertificateDecoder_transition caller .clear data
                (frontEndWithDecoder .certificate data data.certificateBits rev data.certificateWord) regs ctx
                (OpenDecoderMachine.phaseLabel .clear)
              simp only [FrontEndMachine.certificateDecoderView]
              rw [frontEndDecoderContext_with]
              simpa only [frontEndWithDecoder, revEq] using
                OpenDecoderMachine.clear_step_cons (fun _ => .halt) tag rev data.certificateBits data.certificateWord (FrontEndMachine.decoderRegisterEquiv.symm regs) (FrontEndMachine.decoderContext .certificate data ctx)

theorem frontEndAdvance_step (phase : FrontEndMachine.OwnedLabels)
    (data : FrontEndMachine.LocalData) (regs : FrontEndMachine.Registers R)
    (ctx : ∀ k, List (Γ k)) :
    FrontEndMachine.step caller
        (FrontEndMachine.cfg (some (FrontEndMachine.ownedLabelEquiv phase).val) regs data ctx) =
      some (FrontEndMachine.cfg (some (frontEndControlLabel (frontEndAdvance phase data).1))
        ((frontEndPhaseMask phase).apply regs) (frontEndAdvance phase data).2 ctx) := by
  cases phase with
  | inl phase => exact frontEndInputAdvance_step caller phase data regs ctx
  | inr phase =>
      cases phase with
      | inl phase => exact frontEndFramerAdvance_step caller phase data regs ctx
      | inr phase =>
          cases phase with
          | inl phase => exact frontEndDecoderAdvance_step caller .input phase data regs ctx
          | inr phase => exact frontEndDecoderAdvance_step caller .certificate phase data regs ctx

end FrontEndPotentialExecution

theorem frontEndAdvance_potential (phase : FrontEndMachine.OwnedLabels)
    (data : FrontEndMachine.LocalData) :
    frontEndLocalPotential (frontEndAdvance phase data).1 (frontEndAdvance phase data).2 ≤
      frontEndLocalPotential (.inl phase) data := by
  cases phase with
  | inl phase =>
      exact frontEndInputAdvance_potential (K := Unit) (Γ := fun _ => Unit) phase data
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
theorem frontEnd_phase_prefix_description (phase : FrontEndMachine.OwnedLabels)
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
        frontEnd_phase_owned_prefix caller phase data regs ctx n (by omega)
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
theorem frontEnd_phase_prefix_cells (phase : FrontEndMachine.OwnedLabels)
    (data : FrontEndMachine.LocalData) (regs : FrontEndMachine.Registers R)
    (ctx : ∀ k, List (Γ k)) (n : Nat) (bound : n ≤ frontEndPhaseSteps phase data)
    (reached : FrontEndMachine.Cfg Γ Λ R)
    (executed : (FrontEndMachine.next caller)^[n]
      (some (FrontEndMachine.cfg (some (FrontEndMachine.ownedLabelEquiv phase).val) regs data ctx)) =
        some reached) :
    FrontEndMachine.stackCells reached ≤ FrontEndMachine.localCells data +
      frontEndPhaseCredit phase data + FrontEndMachine.contextCells ctx := by
  obtain ⟨control, current, currentRegs, actual, potential⟩ :=
    frontEnd_phase_prefix_description caller phase data regs ctx n bound
  have same := Option.some.inj (executed.symm.trans actual)
  subst reached
  rw [FrontEndMachine.stackCells_cfg]
  unfold frontEndLocalPotential at potential
  change FrontEndMachine.localCells current + frontEndControlCredit control current ≤
    FrontEndMachine.localCells data + frontEndPhaseCredit phase data at potential
  omega

/-- Execution, the staged register mask, the protected context, and cells share one witness. -/
theorem frontEnd_phase_shared_prefix (phase : FrontEndMachine.OwnedLabels)
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
    frontEnd_phase_prefix_description caller phase data regs ctx n bound
  let reached : FrontEndMachine.Cfg Γ Λ R :=
    FrontEndMachine.cfg (some (frontEndControlLabel control)) currentRegs current ctx
  have state := frontEnd_phase_prefix_state caller phase data regs ctx n bound reached executed
  have atEnd : n = frontEndPhaseSteps phase data → reached = frontEndPhaseResult phase regs data ctx := by
    intro finalTime
    rw [finalTime, frontEnd_phase_iterate] at executed
    exact (Option.some.inj executed).symm
  refine ⟨reached, executed, state.1, ?_, state.2,
    frontEnd_phase_prefix_cells caller phase data regs ctx n bound reached executed, ?_, ?_, atEnd⟩
  · rw [state.1]
    exact frontEndPhaseRegisters_caller phase data regs n
  · constructor
    · intro strict
      obtain ⟨actual, actualRun, actualOwned⟩ := frontEnd_phase_owned_prefix caller phase data regs ctx n strict
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

theorem frontEnd_cfg_eta (c : FrontEndMachine.Cfg Γ Λ R) :
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

theorem frontEnd_nonowned_identity (c : FrontEndMachine.Cfg Γ Λ R)
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

theorem frontEnd_owned_view (c : FrontEndMachine.Cfg Γ Λ R) (owned : FrontEndMachine.Owned c.l) :
    ∃ phase, c = FrontEndMachine.cfg (some (FrontEndMachine.ownedLabelEquiv phase).val)
      c.var (frontEndDataOf c) (frontEndContextOf c) := by
  cases selected : frontEndPhaseOf c.l with
  | none => exact False.elim ((frontEndPhaseOf_none_iff c.l).mp selected owned)
  | some phase =>
      have control : c.l = some (FrontEndMachine.ownedLabelEquiv phase).val := by
        simpa only [selected] using frontEndPhaseOf_spec c.l
      have rebuilt := frontEnd_cfg_eta c
      rw [control] at rebuilt
      exact ⟨phase, rebuilt.symm⟩

section FrontEndCfgExecution
variable [DecidableEq K]
variable (caller : FrontEndMachine.External Λ → FrontEndMachine.Statement Γ Λ R)

theorem frontEnd_cfg_trace (c : FrontEndMachine.Cfg Γ Λ R) :
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
      have trace := frontEnd_phase_trace caller phase (frontEndDataOf c) c.var (frontEndContextOf c)
      rw [← control, frontEnd_cfg_eta] at trace
      simpa only [frontEndRemainingSteps, frontEndFinalCfg, selected] using trace

theorem frontEnd_cfg_iterate (c : FrontEndMachine.Cfg Γ Λ R) :
    (FrontEndMachine.next caller)^[frontEndRemainingSteps c] (some c) = some (frontEndFinalCfg c) :=
  (frontEnd_cfg_trace caller c).run

theorem frontEnd_trace_first_unique {start first last : FrontEndMachine.Cfg Γ Λ R} {m n : Nat}
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

theorem frontEnd_first_return_unique (start reached : FrontEndMachine.Cfg Γ Λ R) (n : Nat)
    (executed : (FrontEndMachine.next caller)^[n] (some start) = some reached)
    (outside : ¬ FrontEndMachine.Owned reached.l)
    (earlier : ∀ j, j < n → ∃ actual,
      (FrontEndMachine.next caller)^[j] (some start) = some actual ∧ FrontEndMachine.Owned actual.l) :
    n = frontEndRemainingSteps start ∧ reached = frontEndFinalCfg start :=
  frontEnd_trace_first_unique caller ⟨executed, earlier⟩ (frontEnd_cfg_trace caller start)
    outside (frontEndFinalCfg_not_owned start)

include caller in
theorem frontEndRemainingSteps_pos_iff (c : FrontEndMachine.Cfg Γ Λ R) :
    0 < frontEndRemainingSteps c ↔ FrontEndMachine.Owned c.l := by
  constructor
  · intro positive
    obtain ⟨reached, executed, owned⟩ := (frontEnd_cfg_trace caller c).owned_prefix 0 positive
    have same := Option.some.inj executed
    exact same.symm ▸ owned
  · intro owned
    by_contra notPositive
    have zero : frontEndRemainingSteps c = 0 := by omega
    have run := frontEnd_cfg_iterate caller c
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

theorem frontEnd_local_step_remaining {before after : FrontEndMachine.Cfg Γ Λ R}
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
  have joined := first.trans caller (frontEnd_cfg_trace caller after)
  have unique := frontEnd_trace_first_unique caller (frontEnd_cfg_trace caller before) joined
    (frontEndFinalCfg_not_owned before) (frontEndFinalCfg_not_owned after)
  exact ⟨by omega, unique.2⟩

theorem frontEnd_trace_after {start reached finish : FrontEndMachine.Cfg Γ Λ R} {n total : Nat}
    (whole : FrontEndMachine.Trace caller start finish total)
    (bound : n ≤ total)
    (executed : (FrontEndMachine.next caller)^[n] (some start) = some reached) :
    FrontEndMachine.Trace caller reached finish (total - n) := by
  refine ⟨frontEnd_prefix_after caller executed bound whole.run, ?_⟩
  intro j strict
  obtain ⟨actual, actualRun, actualOwned⟩ := whole.owned_prefix (n + j) (by omega)
  have after := frontEnd_prefix_after caller executed (Nat.le_add_right n j) actualRun
  have count : n + j - n = j := by omega
  exact ⟨actual, by simpa only [count] using after, actualOwned⟩

theorem frontEnd_prefix_remaining (start reached : FrontEndMachine.Cfg Γ Λ R)
    (n : Nat) (bound : n ≤ frontEndRemainingSteps start)
    (executed : (FrontEndMachine.next caller)^[n] (some start) = some reached) :
    frontEndRemainingSteps reached = frontEndRemainingSteps start - n ∧
      frontEndFinalCfg reached = frontEndFinalCfg start := by
  exact frontEnd_trace_first_unique caller (frontEnd_cfg_trace caller reached)
    (frontEnd_trace_after caller (frontEnd_cfg_trace caller start) bound executed)
    (frontEndFinalCfg_not_owned reached) (frontEndFinalCfg_not_owned start)

def FrontEndLocalStep (before after : FrontEndMachine.Cfg Γ Λ R) : Prop :=
  FrontEndMachine.Owned before.l ∧ FrontEndMachine.step caller before = some after

theorem frontEnd_prefix_reachable (start : FrontEndMachine.Cfg Γ Λ R) (n : Nat)
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
      obtain ⟨middle, first, owned⟩ := (frontEnd_cfg_trace caller start).owned_prefix n (by omega)
      have before := ih (by omega) middle first
      have transition : FrontEndMachine.step caller middle = some reached := by
        simpa only [Function.iterate_succ_apply', first, FrontEndMachine.next, Option.bind_some] using executed
      exact before.trans (.single ⟨owned, transition⟩)

theorem frontEnd_cfg_prefix_state (start reached : FrontEndMachine.Cfg Γ Λ R) (n : Nat)
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
        rw [← control, frontEnd_cfg_eta]
        exact executed
      have actualBound : n ≤ frontEndPhaseSteps phase (frontEndDataOf start) := by
        simpa only [frontEndRemainingSteps, selected] using bound
      have state := frontEnd_phase_prefix_state caller phase (frontEndDataOf start) start.var
        (frontEndContextOf start) n actualBound reached explicitRun
      refine ⟨?_, ?_, state.2⟩
      · simpa only [frontEndRegistersAt, selected] using state.1
      · rw [state.1]
        exact frontEndPhaseRegisters_caller phase (frontEndDataOf start) start.var n

theorem frontEnd_cfg_prefix_exists (start : FrontEndMachine.Cfg Γ Λ R) (n : Nat)
    (bound : n ≤ frontEndRemainingSteps start) :
    ∃ reached, (FrontEndMachine.next caller)^[n] (some start) = some reached ∧
      (n < frontEndRemainingSteps start ↔ FrontEndMachine.Owned reached.l) ∧
      (n = 0 → reached = start) ∧
      (n = frontEndRemainingSteps start → reached = frontEndFinalCfg start) := by
  by_cases strict : n < frontEndRemainingSteps start
  · obtain ⟨reached, executed, owned⟩ := (frontEnd_cfg_trace caller start).owned_prefix n strict
    refine ⟨reached, executed, iff_of_true strict owned, ?_, ?_⟩
    · intro zero
      subst n
      exact (Option.some.inj executed).symm
    · intro finalTime
      omega
  · have finalTime : n = frontEndRemainingSteps start := by omega
    subst n
    refine ⟨frontEndFinalCfg start, frontEnd_cfg_iterate caller start,
      iff_of_false (Nat.lt_irrefl _) (frontEndFinalCfg_not_owned start), ?_, fun _ => rfl⟩
    intro zero
    have actual := frontEnd_cfg_iterate caller start
    rw [zero] at actual
    exact (Option.some.inj actual).symm

def frontEndPhaseInTime (phase : FrontEndMachine.OwnedLabels)
    (data : FrontEndMachine.LocalData) (regs : FrontEndMachine.Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (FrontEndMachine.step caller)
      (FrontEndMachine.cfg (some (FrontEndMachine.ownedLabelEquiv phase).val) regs data ctx)
      (some (frontEndPhaseResult phase regs data ctx)) (frontEndPhaseSteps phase data) where
  steps := frontEndPhaseSteps phase data
  evals_in_steps := frontEnd_phase_iterate caller phase data regs ctx
  steps_le_m := Nat.le_refl _

@[simp] theorem frontEndPhaseInTime_steps (phase : FrontEndMachine.OwnedLabels)
    (data : FrontEndMachine.LocalData) (regs : FrontEndMachine.Registers R) (ctx : ∀ k, List (Γ k)) :
    (frontEndPhaseInTime caller phase data regs ctx).steps = frontEndPhaseSteps phase data := rfl

def frontEndCfgInTime (c : FrontEndMachine.Cfg Γ Λ R) :
    StateTransition.EvalsToInTime (FrontEndMachine.step caller) c
      (some (frontEndFinalCfg c)) (frontEndRemainingSteps c) where
  steps := frontEndRemainingSteps c
  evals_in_steps := frontEnd_cfg_iterate caller c
  steps_le_m := Nat.le_refl _

@[simp] theorem frontEndCfgInTime_steps (c : FrontEndMachine.Cfg Γ Λ R) :
    (frontEndCfgInTime caller c).steps = frontEndRemainingSteps c := rfl

include caller in
theorem frontEnd_clean_alignment (regs : FrontEndMachine.Registers R) (raw : Bits)
    (ctx : ∀ k, List (Γ k)) :
    frontEndRemainingSteps (FrontEndMachine.entry (Λ := Λ) regs raw ctx) = FrontEndMachine.runSteps raw ∧
      frontEndFinalCfg (FrontEndMachine.entry (Λ := Λ) regs raw ctx) =
        FrontEndMachine.resultCfg regs ctx (FrontEndMachine.sourceOutcome raw) := by
  exact frontEnd_trace_first_unique caller
    (frontEnd_cfg_trace caller (FrontEndMachine.entry regs raw ctx))
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

theorem frontEnd_phase_step_potential (phase : FrontEndMachine.OwnedLabels)
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

theorem frontEnd_local_step_potential {before after : FrontEndMachine.Cfg Γ Λ R}
    (owned : FrontEndMachine.Owned before.l)
    (executed : FrontEndMachine.step caller before = some after) :
    frontEndPotential after ≤ frontEndPotential before := by
  obtain ⟨phase, rebuilt⟩ := frontEnd_owned_view before owned
  rw [rebuilt] at executed ⊢
  exact frontEnd_phase_step_potential caller phase _ _ _ after executed

theorem frontEnd_reaches_potential {start reached : FrontEndMachine.Cfg Γ Λ R}
    (path : Relation.ReflTransGen (FrontEndLocalStep caller) start reached) :
    frontEndPotential reached ≤ frontEndPotential start := by
  induction path with
  | refl => exact Nat.le_refl _
  | @tail before after _ transition ih =>
      exact (frontEnd_local_step_potential caller transition.1 transition.2).trans ih

/-- One actual inclusive witness carries rank, ownership, masks, frame and the physical allowance. -/
theorem frontEnd_owned_prefix (start : FrontEndMachine.Cfg Γ Λ R) (n : Nat)
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
  obtain ⟨reached, executed, owned, zero, final⟩ := frontEnd_cfg_prefix_exists caller start n bound
  have remaining := frontEnd_prefix_remaining caller start reached n bound executed
  have path := frontEnd_prefix_reachable caller start n bound reached executed
  have state := frontEnd_cfg_prefix_state caller start reached n bound executed
  have potential := frontEnd_reaches_potential caller path
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

theorem LocalRun.finalCfg {n : Nat} {a b : Cfg Γ Λ R} (run : LocalRun caller n a b) :
    finalCfg a = finalCfg b := by
  induction run with
  | refl => rfl
  | cons head tail ih => exact (finalCfg_step caller head).trans ih

theorem LocalRun.phaseEndpoint {q : Phase} {D : LocalData} {regs : Registers R}
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
  have endpoints := (run_localRun localCaller regs raw ctx).phaseEndpoint localCaller rfl
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

namespace Resources.RotationCertificate.FrontEndStreamMachine

open Search.SharedTree (Branch)
open Resources.BinaryCounter (Bits)

variable {K Λ R : Type} {Γ : K → Type}

/-- The common register state with all eight temporary fields empty. -/
def initialRegisters (initial : R) : Registers R :=
  ((none, none), BitDecoderMachine.zeroRegisters, (none, initial))

@[simp] theorem user_initialRegisters (initial : R) :
    user (initialRegisters initial) = initial := rfl

@[simp] theorem fullReset_initialRegisters (initial : R) :
    fullReset (initialRegisters initial) = initialRegisters initial := rfl

theorem fullReset_eq_initialRegisters (regs : Registers R) :
    fullReset regs = initialRegisters (user regs) := rfl

section FinitePackage

variable [DecidableEq K] [Fintype K] [Fintype Λ] [Fintype R]
  [∀ k, Fintype (Γ k)]
variable (caller : Λ → Statement Γ Λ R)

/-- The actual finite controller, with raw framed input and the existing fuel
store designated as output. The program and user initial state precede input. -/
def machine (initial : R) : Turing.FinTM2 where
  K := StackId K
  k₀ := .inl .framedRaw
  k₁ := .inl .fuel
  Γ := alphabet Γ
  Λ := Label Λ
  main := phaseLabel (.inl (FrontEndMachine.framerLabel .scanPrefix))
  σ := Registers R
  initialState := initialRegisters initial
  Γk₀Fin := FrontEndMachine.alphabetFintype (.inl .framedRaw)
  m := program caller

/-- Finiteness at every actual physical alphabet, including caller stores. -/
@[instance_reducible]
def machineAlphabetFintype (initial : R) (k : (machine caller initial).K) :
    Fintype ((machine caller initial).Γ k) := FrontEndMachine.alphabetFintype k

theorem machine_alphabet_finite (initial : R) (k : (machine caller initial).K) :
    Finite ((machine caller initial).Γ k) := by
  let := machineAlphabetFintype caller initial k
  infer_instance

theorem machine_inputIndex (initial : R) :
    (machine caller initial).k₀ = Sum.inl FrontEndMachine.LocalStack.framedRaw := rfl

theorem machine_outputIndex (initial : R) :
    (machine caller initial).k₁ = Sum.inl FrontEndMachine.LocalStack.fuel := rfl

theorem machine_input_ne_output (initial : R) :
    (machine caller initial).k₀ ≠ (machine caller initial).k₁ := by
  intro h
  cases h

theorem machine_inputAlphabet (initial : R) :
    (machine caller initial).Γ (machine caller initial).k₀ = Bool := rfl

theorem machine_outputAlphabet (initial : R) :
    (machine caller initial).Γ (machine caller initial).k₁ = Bool := rfl

theorem machine_main (initial : R) :
    (machine caller initial).main =
      phaseLabel (.inl (FrontEndMachine.framerLabel .scanPrefix)) := rfl

theorem machine_initialState (initial : R) :
    (machine caller initial).initialState = initialRegisters initial := rfl

theorem machine_program (initial : R) :
    (machine caller initial).m = program caller := rfl

theorem machine_card_stackId (initial : R) :
    @Fintype.card (machine caller initial).K (machine caller initial).kFin =
      16 + Fintype.card K := card_stackId

theorem machine_card_label (initial : R) :
    @Fintype.card (machine caller initial).Λ (machine caller initial).ΛFin =
      96 + Fintype.card Λ := card_label

theorem machine_card_registers (initial : R) :
    @Fintype.card (machine caller initial).σ (machine caller initial).σFin =
      140454 * Fintype.card R := card_registers

theorem machine_step_eq (initial : R) (c : Cfg Γ Λ R) :
    (machine caller initial).step c = step caller c := rfl

/-- Genuine initialization fills only the framed input stack. -/
theorem machine_initList_eq (initial : R) (raw : Bits) :
    Turing.initList (machine caller initial) raw =
      cfg (some (phaseLabel (.inl (FrontEndMachine.framerLabel .scanPrefix))))
        (initialRegisters initial) { framedRaw := raw } (fun _ => []) := by
  apply cfg_ext
  · rfl
  · rfl
  · funext k
    cases k with
    | inl k => cases k <;> rfl
    | inr k => cases k with
      | inl k => cases k <;> rfl
      | inr k => rfl

/-- Literal package halt: initial registers, the output word in fuel, every
other physical stack empty, and a live configuration whose label is none. -/
theorem machine_haltList_eq (initial : R) (out : Bits) :
    Turing.haltList (machine caller initial) out =
      cfg none (initialRegisters initial) { fuel := out } (fun _ => []) := by
  apply cfg_ext
  · rfl
  · rfl
  · funext k
    cases k with
    | inl k => cases k <;> rfl
    | inr k => cases k with
      | inl k => cases k <;> rfl
      | inr k => rfl

theorem machine_initList_data (initial : R) (raw : Bits) :
    dataOfCfg (Turing.initList (machine caller initial) raw) = { framedRaw := raw } := by
  rw [machine_initList_eq, dataOfCfg_cfg]

theorem machine_haltList_data (initial : R) (out : Bits) :
    dataOfCfg (Turing.haltList (machine caller initial) out) = { fuel := out } := by
  rw [machine_haltList_eq, dataOfCfg_cfg]

theorem machine_initList_user (initial : R) (raw : Bits) :
    user (Turing.initList (machine caller initial) raw).var = initial := rfl

theorem machine_haltList_user (initial : R) (out : Bits) :
    user (Turing.haltList (machine caller initial) out).var = initial := rfl

theorem machine_initList_context (initial : R) (raw : Bits) :
    contextOfCfg (Turing.initList (machine caller initial) raw) = (fun _ => []) := by
  rw [machine_initList_eq, contextOfCfg_cfg]

theorem machine_haltList_context (initial : R) (out : Bits) :
    contextOfCfg (Turing.haltList (machine caller initial) out) = (fun _ => []) := by
  rw [machine_haltList_eq, contextOfCfg_cfg]

/-- A generic cleaned endpoint is the literal package halt exactly when its
preserved caller state and caller words match genuine package initialization. -/
theorem machine_haltList_eq_iff (initial : R) (out : Bits) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    cfg none (fullReset regs) { fuel := out } ctx =
      Turing.haltList (machine caller initial) out ↔
      user regs = initial ∧ ctx = (fun _ => []) := by
  rw [machine_haltList_eq]
  constructor
  · intro h
    constructor
    · exact congrArg (fun c : Cfg Γ Λ R => user c.var) h
    · simpa only [contextOfCfg_cfg] using congrArg contextOfCfg h
  · rintro ⟨huser, hctx⟩
    rw [fullReset_eq_initialRegisters, huser, hctx]

theorem machine_alphabet_framedRaw (initial : R) :
    (machine caller initial).Γ (.inl .framedRaw) = Bool := rfl

theorem machine_initList_framedRaw (initial : R) (raw : Bits) :
    (Turing.initList (machine caller initial) raw).stk (.inl .framedRaw) = raw := by
  rw [machine_initList_eq]
  rfl

theorem machine_haltList_framedRaw (initial : R) (out : Bits) :
    (Turing.haltList (machine caller initial) out).stk (.inl .framedRaw) = [] := by
  rw [machine_haltList_eq]
  rfl

theorem machine_alphabet_frameFirstReverse (initial : R) :
    (machine caller initial).Γ (.inl .frameFirstReverse) = Bool := rfl

theorem machine_initList_frameFirstReverse (initial : R) (raw : Bits) :
    (Turing.initList (machine caller initial) raw).stk (.inl .frameFirstReverse) = [] := by
  rw [machine_initList_eq]
  rfl

theorem machine_haltList_frameFirstReverse (initial : R) (out : Bits) :
    (Turing.haltList (machine caller initial) out).stk (.inl .frameFirstReverse) = [] := by
  rw [machine_haltList_eq]
  rfl

theorem machine_alphabet_frameCertReverse (initial : R) :
    (machine caller initial).Γ (.inl .frameCertReverse) = Bool := rfl

theorem machine_initList_frameCertReverse (initial : R) (raw : Bits) :
    (Turing.initList (machine caller initial) raw).stk (.inl .frameCertReverse) = [] := by
  rw [machine_initList_eq]
  rfl

theorem machine_haltList_frameCertReverse (initial : R) (out : Bits) :
    (Turing.haltList (machine caller initial) out).stk (.inl .frameCertReverse) = [] := by
  rw [machine_haltList_eq]
  rfl

theorem machine_alphabet_inputBits (initial : R) :
    (machine caller initial).Γ (.inl .inputBits) = Bool := rfl

theorem machine_initList_inputBits (initial : R) (raw : Bits) :
    (Turing.initList (machine caller initial) raw).stk (.inl .inputBits) = [] := by
  rw [machine_initList_eq]
  rfl

theorem machine_haltList_inputBits (initial : R) (out : Bits) :
    (Turing.haltList (machine caller initial) out).stk (.inl .inputBits) = [] := by
  rw [machine_haltList_eq]
  rfl

theorem machine_alphabet_certificateBits (initial : R) :
    (machine caller initial).Γ (.inl .certificateBits) = Bool := rfl

theorem machine_initList_certificateBits (initial : R) (raw : Bits) :
    (Turing.initList (machine caller initial) raw).stk (.inl .certificateBits) = [] := by
  rw [machine_initList_eq]
  rfl

theorem machine_haltList_certificateBits (initial : R) (out : Bits) :
    (Turing.haltList (machine caller initial) out).stk (.inl .certificateBits) = [] := by
  rw [machine_haltList_eq]
  rfl

theorem machine_alphabet_inputRaw (initial : R) :
    (machine caller initial).Γ (.inl .inputRaw) = Tag := rfl

theorem machine_initList_inputRaw (initial : R) (raw : Bits) :
    (Turing.initList (machine caller initial) raw).stk (.inl .inputRaw) = [] := by
  rw [machine_initList_eq]
  rfl

theorem machine_haltList_inputRaw (initial : R) (out : Bits) :
    (Turing.haltList (machine caller initial) out).stk (.inl .inputRaw) = [] := by
  rw [machine_haltList_eq]
  rfl

theorem machine_alphabet_decodeReverse (initial : R) :
    (machine caller initial).Γ (.inl .decodeReverse) = Tag := rfl

theorem machine_initList_decodeReverse (initial : R) (raw : Bits) :
    (Turing.initList (machine caller initial) raw).stk (.inl .decodeReverse) = [] := by
  rw [machine_initList_eq]
  rfl

theorem machine_haltList_decodeReverse (initial : R) (out : Bits) :
    (Turing.haltList (machine caller initial) out).stk (.inl .decodeReverse) = [] := by
  rw [machine_haltList_eq]
  rfl

theorem machine_alphabet_certificateWord (initial : R) :
    (machine caller initial).Γ (.inl .certificateWord) = Tag := rfl

theorem machine_initList_certificateWord (initial : R) (raw : Bits) :
    (Turing.initList (machine caller initial) raw).stk (.inl .certificateWord) = [] := by
  rw [machine_initList_eq]
  rfl

theorem machine_haltList_certificateWord (initial : R) (out : Bits) :
    (Turing.haltList (machine caller initial) out).stk (.inl .certificateWord) = [] := by
  rw [machine_haltList_eq]
  rfl

theorem machine_alphabet_sourceTree (initial : R) :
    (machine caller initial).Γ (.inl .sourceTree) = Tag := rfl

theorem machine_initList_sourceTree (initial : R) (raw : Bits) :
    (Turing.initList (machine caller initial) raw).stk (.inl .sourceTree) = [] := by
  rw [machine_initList_eq]
  rfl

theorem machine_haltList_sourceTree (initial : R) (out : Bits) :
    (Turing.haltList (machine caller initial) out).stk (.inl .sourceTree) = [] := by
  rw [machine_haltList_eq]
  rfl

theorem machine_alphabet_targetTree (initial : R) :
    (machine caller initial).Γ (.inl .targetTree) = Tag := rfl

theorem machine_initList_targetTree (initial : R) (raw : Bits) :
    (Turing.initList (machine caller initial) raw).stk (.inl .targetTree) = [] := by
  rw [machine_initList_eq]
  rfl

theorem machine_haltList_targetTree (initial : R) (out : Bits) :
    (Turing.haltList (machine caller initial) out).stk (.inl .targetTree) = [] := by
  rw [machine_haltList_eq]
  rfl

theorem machine_alphabet_treeReverse (initial : R) :
    (machine caller initial).Γ (.inl .treeReverse) = Tag := rfl

theorem machine_initList_treeReverse (initial : R) (raw : Bits) :
    (Turing.initList (machine caller initial) raw).stk (.inl .treeReverse) = [] := by
  rw [machine_initList_eq]
  rfl

theorem machine_haltList_treeReverse (initial : R) (out : Bits) :
    (Turing.haltList (machine caller initial) out).stk (.inl .treeReverse) = [] := by
  rw [machine_haltList_eq]
  rfl

theorem machine_alphabet_pending (initial : R) :
    (machine caller initial).Γ (.inl .pending) = Unit := rfl

theorem machine_initList_pending (initial : R) (raw : Bits) :
    (Turing.initList (machine caller initial) raw).stk (.inl .pending) = [] := by
  rw [machine_initList_eq]
  rfl

theorem machine_haltList_pending (initial : R) (out : Bits) :
    (Turing.haltList (machine caller initial) out).stk (.inl .pending) = [] := by
  rw [machine_haltList_eq]
  rfl

theorem machine_alphabet_bitsReverse (initial : R) :
    (machine caller initial).Γ (.inl .bitsReverse) = Bool := rfl

theorem machine_initList_bitsReverse (initial : R) (raw : Bits) :
    (Turing.initList (machine caller initial) raw).stk (.inl .bitsReverse) = [] := by
  rw [machine_initList_eq]
  rfl

theorem machine_haltList_bitsReverse (initial : R) (out : Bits) :
    (Turing.haltList (machine caller initial) out).stk (.inl .bitsReverse) = [] := by
  rw [machine_haltList_eq]
  rfl

theorem machine_alphabet_moveReverse (initial : R) :
    (machine caller initial).Γ (.inr (.inl .moveReverse)) = Branch := rfl

theorem machine_initList_moveReverse (initial : R) (raw : Bits) :
    (Turing.initList (machine caller initial) raw).stk (.inr (.inl .moveReverse)) = [] := by
  rw [machine_initList_eq]
  rfl

theorem machine_haltList_moveReverse (initial : R) (out : Bits) :
    (Turing.haltList (machine caller initial) out).stk (.inr (.inl .moveReverse)) = [] := by
  rw [machine_haltList_eq]
  rfl

theorem machine_alphabet_path (initial : R) :
    (machine caller initial).Γ (.inr (.inl .path)) = Branch := rfl

theorem machine_initList_path (initial : R) (raw : Bits) :
    (Turing.initList (machine caller initial) raw).stk (.inr (.inl .path)) = [] := by
  rw [machine_initList_eq]
  rfl

theorem machine_haltList_path (initial : R) (out : Bits) :
    (Turing.haltList (machine caller initial) out).stk (.inr (.inl .path)) = [] := by
  rw [machine_haltList_eq]
  rfl

theorem machine_alphabet_fuel (initial : R) :
    (machine caller initial).Γ (.inl .fuel) = Bool := rfl

theorem machine_initList_fuel (initial : R) (raw : Bits) :
    (Turing.initList (machine caller initial) raw).stk (.inl .fuel) = [] := by
  rw [machine_initList_eq]
  rfl

theorem machine_haltList_fuel (initial : R) (out : Bits) :
    (Turing.haltList (machine caller initial) out).stk (.inl .fuel) = out := by
  rw [machine_haltList_eq]
  rfl

theorem machine_alphabet_external (initial : R) (k : K) :
    (machine caller initial).Γ (.inr (.inr k)) = Γ k := rfl

theorem machine_initList_external (initial : R) (raw : Bits) (k : K) :
    (Turing.initList (machine caller initial) raw).stk (.inr (.inr k)) = [] := by
  rw [machine_initList_eq]
  rfl

theorem machine_haltList_external (initial : R) (out : Bits) (k : K) :
    (Turing.haltList (machine caller initial) out).stk (.inr (.inr k)) = [] := by
  rw [machine_haltList_eq]
  rfl

end FinitePackage

end Resources.RotationCertificate.FrontEndStreamMachine

namespace Resources.RotationCertificate.FrontEndStreamMachine

variable {K Λ R : Type} {Γ : K → Type}

section FurtherInstallation

variable {K' Λ' R' : Type} {Γ' : K' → Type}
variable (names : StackId K ≃ K') (symbols : ∀ k, alphabet Γ k ≃ Γ' (names k))
  (registers : Registers R ≃ R') (labels : Label Λ ≃ Λ')

def installedCfg (c : Cfg Γ Λ R) : Turing.TM2.Cfg Γ' Λ' R' :=
  FrontEndMachine.Transport.cfg names symbols registers labels c

theorem installedCfg_injective :
    Function.Injective (installedCfg names symbols registers labels) :=
  FrontEndMachine.Transport.cfg_injective names symbols registers labels labels.injective

/-- The inverse recovers the entire dependent stack family and every caller
register/label component, including live halt-labelled configurations. -/
def installedCfgEquiv : Cfg Γ Λ R ≃ Turing.TM2.Cfg Γ' Λ' R' where
  toFun := installedCfg names symbols registers labels
  invFun c :=
    { l := c.l.map labels.symm
      var := registers.symm c.var
      stk := (FrontEndMachine.Transport.stackEquiv names symbols).symm c.stk }
  left_inv c := by
    rcases c with ⟨label, regs, data⟩
    cases label <;> simp [installedCfg, FrontEndMachine.Transport.cfg]
  right_inv c := by
    rcases c with ⟨label, regs, data⟩
    cases label <;> simp [installedCfg, FrontEndMachine.Transport.cfg]

@[simp] theorem installedCfgEquiv_apply (c : Cfg Γ Λ R) :
    installedCfgEquiv names symbols registers labels c =
      installedCfg names symbols registers labels c := rfl

theorem installedCfg_label (c : Cfg Γ Λ R) :
    (installedCfg names symbols registers labels c).l = c.l.map labels := rfl

theorem installedCfg_registers (c : Cfg Γ Λ R) :
    (installedCfg names symbols registers labels c).var = registers c.var := rfl

theorem installedCfg_stack (c : Cfg Γ Λ R) (k : StackId K) :
    (installedCfg names symbols registers labels c).stk (names k) =
      (c.stk k).map (symbols k) :=
  FrontEndMachine.Transport.stackEquiv_apply names symbols c.stk k

theorem installedCfg_registers_readback (c : Cfg Γ Λ R) :
    registers.symm (installedCfg names symbols registers labels c).var = c.var :=
  registers.symm_apply_apply c.var

theorem installedCfg_readback (c : Cfg Γ Λ R) :
    (installedCfgEquiv names symbols registers labels).symm
      (installedCfg names symbols registers labels c) = c :=
  (installedCfgEquiv names symbols registers labels).symm_apply_apply c

def installedOwned (label : Option Λ') : Prop := Owned (label.map labels.symm)

@[simp] theorem installedCfg_owned_iff (c : Cfg Γ Λ R) :
    installedOwned labels (installedCfg names symbols registers labels c).l ↔ Owned c.l := by
  cases label : c.l <;>
    simp [installedOwned, installedCfg, FrontEndMachine.Transport.cfg, label]

theorem installedCfg_stack_readback (c : Cfg Γ Λ R) (k : StackId K) :
    ((installedCfg names symbols registers labels c).stk (names k)).map
      (symbols k).symm = c.stk k := by
  rw [installedCfg_stack]
  simp

theorem installed_stack_cells [Fintype K] [Fintype K'] (c : Cfg Γ Λ R) :
    ∑ k, ((installedCfg names symbols registers labels c).stk k).length =
      ∑ k, (c.stk k).length :=
  FrontEndMachine.Transport.stackCells names symbols c.stk

variable [DecidableEq K] [DecidableEq K']
variable (caller : Λ → Statement Γ Λ R)
variable (ambient : Λ' → Turing.TM2.Stmt Γ' Λ' R')

theorem installed_owned_step
    (installed : ∀ label, Owned (some label) →
      ambient (labels label) =
        FrontEndMachine.Transport.statement names symbols registers labels (program caller label))
    (start : Cfg Γ Λ R) (owned : Owned start.l) :
    Turing.TM2.step ambient (installedCfg names symbols registers labels start) =
      (step caller start).map (installedCfg names symbols registers labels) :=
  FrontEndMachine.Transport.step_owned names symbols registers labels
    (program caller) ambient Owned installed start owned

/-- This transport uses the supplied actual owned prefix; later caller bodies
are unconstrained. Canonical rank-bounded specializations are proved separately. -/
theorem installed_prefix_of_owned
    (installed : ∀ label, Owned (some label) →
      ambient (labels label) =
        FrontEndMachine.Transport.statement names symbols registers labels (program caller label))
    (n : Nat) (start : Cfg Γ Λ R)
    (earlier : ∀ j, j < n → ∃ reached,
      (next caller)^[j] (some start) = some reached ∧ Owned reached.l) :
    (FrontEndMachine.Transport.next ambient)^[n]
      (some (installedCfg names symbols registers labels start)) =
      ((next caller)^[n] (some start)).map (installedCfg names symbols registers labels) :=
  FrontEndMachine.Transport.iterate_owned names symbols registers labels
    (program caller) ambient Owned installed n start earlier

/-- A supplied actual owned run transports with the same activation count.
No condition is imposed on external caller bodies. -/
theorem installed_localRun
    (installed : ∀ label, Owned (some label) →
      ambient (labels label) =
        FrontEndMachine.Transport.statement names symbols registers labels (program caller label))
    {n : Nat} {start finish : Cfg Γ Λ R} (run : LocalRun caller n start finish) :
    (FrontEndMachine.Transport.next ambient)^[n]
      (some (installedCfg names symbols registers labels start)) =
      some (installedCfg names symbols registers labels finish) := by
  rw [installed_prefix_of_owned names symbols registers labels caller ambient installed n start
    (fun j strict => LocalRun.owned_prefix caller run j strict)]
  rw [LocalRun.iterate caller run]
  rfl

theorem installed_localRun_owned_prefix
    (installed : ∀ label, Owned (some label) →
      ambient (labels label) =
        FrontEndMachine.Transport.statement names symbols registers labels (program caller label))
    {n : Nat} {start finish : Cfg Γ Λ R} (run : LocalRun caller n start finish)
    (j : Nat) (strict : j < n) :
    ∃ reached, (FrontEndMachine.Transport.next ambient)^[j]
      (some (installedCfg names symbols registers labels start)) = some reached ∧
      installedOwned labels reached.l := by
  obtain ⟨reached, executed, owned⟩ := LocalRun.owned_prefix caller run j strict
  refine ⟨installedCfg names symbols registers labels reached, ?_, ?_⟩
  · rw [installed_prefix_of_owned names symbols registers labels caller ambient installed j start
      (fun k earlier => LocalRun.owned_prefix caller run k (Nat.lt_trans earlier strict))]
    rw [executed]
    rfl
  · exact (installedCfg_owned_iff names symbols registers labels reached).2 owned

/-- Arbitrary iterations, including arbitrary external caller behaviour, require
literal agreement on every label of the complete carrier. -/
theorem installed_iterate
    (installed : ∀ label, ambient (labels label) =
      FrontEndMachine.Transport.statement names symbols registers labels (program caller label))
    (n : Nat) (start : Option (Cfg Γ Λ R)) :
    (FrontEndMachine.Transport.next ambient)^[n]
      (start.map (installedCfg names symbols registers labels)) =
      ((next caller)^[n] start).map (installedCfg names symbols registers labels) :=
  FrontEndMachine.Transport.iterate names symbols registers labels
    (program caller) ambient installed n start

def installed_timed
    (installed : ∀ label, ambient (labels label) =
      FrontEndMachine.Transport.statement names symbols registers labels (program caller label))
    (start : Cfg Γ Λ R) (final : Option (Cfg Γ Λ R)) (bound : Nat)
    (run : StateTransition.EvalsToInTime (step caller) start final bound) :
    StateTransition.EvalsToInTime (Turing.TM2.step ambient)
      (installedCfg names symbols registers labels start)
      (final.map (installedCfg names symbols registers labels)) bound :=
  FrontEndMachine.Transport.timed names symbols registers labels
    (program caller) ambient installed start final bound run

@[simp] theorem installed_timed_steps
    (installed : ∀ label, ambient (labels label) =
      FrontEndMachine.Transport.statement names symbols registers labels (program caller label))
    (start : Cfg Γ Λ R) (final : Option (Cfg Γ Λ R)) (bound : Nat)
    (run : StateTransition.EvalsToInTime (step caller) start final bound) :
    (installed_timed names symbols registers labels caller ambient installed start final bound run).steps =
      run.steps := rfl

end FurtherInstallation

end Resources.RotationCertificate.FrontEndStreamMachine

namespace Resources.RotationCertificate.FrontEndStreamMachine

open Resources.BinaryCounter (Bits)

variable {K Λ R : Type} {Γ : K → Type}
variable [DecidableEq K] [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]
variable (caller : Λ → Statement Γ Λ R)

theorem init_first_halt (initial : R) (raw : Bits) :
    FirstHalt caller (Turing.initList (machine caller initial) raw) (runSteps raw)
      (Turing.haltList (machine caller initial) [BitPairFraming.verifyFramed raw]) := by
  have startEq : (Turing.initList (machine caller initial) raw : Cfg Γ Λ R) =
      entry (initialRegisters initial) raw (fun _ => []) :=
    machine_initList_eq caller initial raw
  have finishEq :
      (Turing.haltList (machine caller initial) ([BitPairFraming.verifyFramed raw] : Bits) : Cfg Γ Λ R) =
      cfg none (fullReset (initialRegisters initial)) { fuel := [BitPairFraming.verifyFramed raw] }
        (fun _ => []) :=
    (machine_haltList_eq caller initial ([BitPairFraming.verifyFramed raw] : Bits)).trans
      (congrArg (fun fields : Registers R => cfg (Γ := Γ) (Λ := Λ) none fields
        { fuel := [BitPairFraming.verifyFramed raw] } (fun _ => []))
        (fullReset_initialRegisters initial).symm)
  exact (congrArg₂ (fun start finish : Cfg Γ Λ R =>
    FirstHalt caller start (runSteps raw) finish) startEq finishEq).mpr
      (run_verifyFramed caller (initialRegisters initial) raw (fun _ => []))

theorem init_first_halt_iff (initial : R) (raw : Bits) (n : Nat) (finish : Cfg Γ Λ R) :
    FirstHalt caller (Turing.initList (machine caller initial) raw) n finish ↔
      n = runSteps raw ∧
      finish = Turing.haltList (machine caller initial) [BitPairFraming.verifyFramed raw] := by
  have startEq : (Turing.initList (machine caller initial) raw : Cfg Γ Λ R) =
      entry (initialRegisters initial) raw (fun _ => []) :=
    machine_initList_eq caller initial raw
  have finishEq :
      (Turing.haltList (machine caller initial) ([BitPairFraming.verifyFramed raw] : Bits) : Cfg Γ Λ R) =
      cfg none (fullReset (initialRegisters initial)) { fuel := [BitPairFraming.verifyFramed raw] }
        (fun _ => []) :=
    (machine_haltList_eq caller initial ([BitPairFraming.verifyFramed raw] : Bits)).trans
      (congrArg (fun fields : Registers R => cfg (Γ := Γ) (Λ := Λ) none fields
        { fuel := [BitPairFraming.verifyFramed raw] } (fun _ => []))
        (fullReset_initialRegisters initial).symm)
  exact (congrArg₂ (fun start result : Cfg Γ Λ R =>
    (FirstHalt caller start n finish ↔ n = runSteps raw ∧ finish = result)) startEq finishEq).mpr
      (run_first_halt_iff caller (initialRegisters initial) raw (fun _ => []) n finish)

theorem init_iterate (initial : R) (raw : Bits) :
    (fun c : Option (machine caller initial).Cfg => c.bind (machine caller initial).step)^[runSteps raw]
      (some (Turing.initList (machine caller initial) raw)) =
      some (Turing.haltList (machine caller initial) [BitPairFraming.verifyFramed raw]) :=
  (init_first_halt caller initial raw).1

theorem init_outer_none (initial : R) (raw : Bits) :
    (fun c : Option (machine caller initial).Cfg => c.bind (machine caller initial).step)^[runSteps raw + 1]
      (some (Turing.initList (machine caller initial) raw)) = none := by
  rw [machine_initList_eq]
  exact run_outer_none caller (initialRegisters initial) raw (fun _ => [])

theorem init_after_halt (initial : R) (raw : Bits) (n : Nat) (strict : runSteps raw < n) :
    (fun c : Option (machine caller initial).Cfg => c.bind (machine caller initial).step)^[n]
      (some (Turing.initList (machine caller initial) raw)) = none := by
  rw [machine_initList_eq]
  exact run_after_halt caller (initialRegisters initial) raw (fun _ => []) n strict

theorem init_earlier_owned (initial : R) (raw : Bits) (n : Nat) (strict : n < runSteps raw) :
    ∃ reached,
      (fun c : Option (machine caller initial).Cfg => c.bind (machine caller initial).step)^[n]
        (some (Turing.initList (machine caller initial) raw)) = some reached ∧ Owned reached.l :=
  (init_first_halt caller initial raw).2.2 n strict

def initOutputsInTimeExact (initial : R) (raw : Bits) :
    Turing.TM2OutputsInTime (machine caller initial) raw
      (some [BitPairFraming.verifyFramed raw]) (runSteps raw) where
  steps := runSteps raw
  evals_in_steps := init_iterate caller initial raw
  steps_le_m := Nat.le_refl _

def initOutputsInTimePolynomial (initial : R) (raw : Bits) :
    Turing.TM2OutputsInTime (machine caller initial) raw
      (some [BitPairFraming.verifyFramed raw]) (raw.length * raw.length + 10 * raw.length + 36) where
  steps := runSteps raw
  evals_in_steps := init_iterate caller initial raw
  steps_le_m := runSteps_le raw

@[simp] theorem initOutputsInTimeExact_steps (initial : R) (raw : Bits) :
    (initOutputsInTimeExact caller initial raw).steps = runSteps raw := rfl

@[simp] theorem initOutputsInTimePolynomial_steps (initial : R) (raw : Bits) :
    (initOutputsInTimePolynomial caller initial raw).steps = runSteps raw := rfl

def initOutputs (initial : R) (raw : Bits) :
    Turing.TM2Outputs (machine caller initial) raw (some [BitPairFraming.verifyFramed raw]) :=
  (initOutputsInTimeExact caller initial raw).toTM2Outputs

def initNoneInTime (initial : R) (raw : Bits) :
    StateTransition.EvalsToInTime (machine caller initial).step
      (Turing.initList (machine caller initial) raw) none (runSteps raw + 1) where
  steps := runSteps raw + 1
  evals_in_steps := init_outer_none caller initial raw
  steps_le_m := Nat.le_refl _

@[simp] theorem initNoneInTime_steps (initial : R) (raw : Bits) :
    (initNoneInTime caller initial raw).steps = runSteps raw + 1 := rfl

theorem init_peak (initial : R) (raw : Bits) :
    ExactPeak caller (Turing.initList (machine caller initial) raw)
      (runSteps raw) (max raw.length 1) := by
  have startEq : (Turing.initList (machine caller initial) raw : Cfg Γ Λ R) =
      entry (initialRegisters initial) raw (fun _ => []) :=
    machine_initList_eq caller initial raw
  have actual : ExactPeak caller (entry (initialRegisters initial) raw (fun _ => []))
      (runSteps raw) (max raw.length 1) := by
    simpa only [contextCells, List.length_nil, Finset.sum_const_zero, Nat.add_zero] using
      run_peak caller (initialRegisters initial) raw (fun _ => [])
  exact (congrArg (fun start : Cfg Γ Λ R =>
    ExactPeak caller start (runSteps raw) (max raw.length 1)) startEq).mpr actual

theorem init_prefix (initial : R) (raw : Bits) (n : Nat) (bound : n ≤ runSteps raw) :
    ∃ reached,
      (fun c : Option (machine caller initial).Cfg => c.bind (machine caller initial).step)^[n]
        (some (Turing.initList (machine caller initial) raw)) = some reached ∧
      remainingSteps reached = runSteps raw - n ∧
      Relation.ReflTransGen (LocalStep caller) (Turing.initList (machine caller initial) raw) reached ∧
      (n < runSteps raw ↔ Owned reached.l) ∧
      (n = 0 → reached = Turing.initList (machine caller initial) raw) ∧
      reached.var = registersAt (Turing.initList (machine caller initial) raw) n ∧
      user reached.var = initial ∧
      (∀ k, reached.stk (.inr (.inr k)) = []) ∧
      finalCfg reached = Turing.haltList (machine caller initial) [BitPairFraming.verifyFramed raw] ∧
      stackCells reached ≤ max raw.length 1 ∧
      runSteps raw ≤ raw.length * raw.length + 10 * raw.length + 36 := by
  have startEq : (Turing.initList (machine caller initial) raw : Cfg Γ Λ R) =
      entry (initialRegisters initial) raw (fun _ => []) :=
    machine_initList_eq caller initial raw
  have finishEq : runResult (Λ := Λ) (initialRegisters initial) raw (fun _ => []) =
      (Turing.haltList (machine caller initial) ([BitPairFraming.verifyFramed raw] : Bits) : Cfg Γ Λ R) :=
    (runResult_eq (initialRegisters initial) raw (fun _ => [])).trans
      ((congrArg (fun fields : Registers R => cfg (Γ := Γ) (Λ := Λ) none fields
        { fuel := [BitPairFraming.verifyFramed raw] } (fun _ => []))
        (fullReset_initialRegisters initial)).trans
          (machine_haltList_eq caller initial ([BitPairFraming.verifyFramed raw] : Bits)).symm)
  obtain ⟨reached, executed, rank, path, ownership, zero, fields, retained, frame, final, cells, time⟩ :=
    run_owned_prefix caller (initialRegisters initial) raw (fun _ => []) n bound
  refine ⟨reached, ?_, rank, ?_, ownership, ?_, ?_, ?_, frame, final.trans finishEq, ?_, time⟩
  · exact (congrArg (fun start : Cfg Γ Λ R =>
      (next caller)^[n] (some start) = some reached) startEq).mpr executed
  · exact (congrArg (fun start : Cfg Γ Λ R =>
      Relation.ReflTransGen (LocalStep caller) start reached) startEq).mpr path
  · intro isZero
    exact (zero isZero).trans startEq.symm
  · exact fields.trans (congrArg (fun start : Cfg Γ Λ R => registersAt start n) startEq).symm
  · exact retained.trans (user_initialRegisters initial)
  · simpa only [contextCells, List.length_nil, Finset.sum_const_zero, Nat.add_zero] using cells

def machine_cfgInTime (initial : R) (start : Cfg Γ Λ R) :
    StateTransition.EvalsToInTime (machine caller initial).step start
      (some (finalCfg start)) (remainingSteps start) := cfgInTime caller start

@[simp] theorem machine_cfgInTime_steps (initial : R) (start : Cfg Γ Λ R) :
    (machine_cfgInTime caller initial start).steps = remainingSteps start := rfl

def machine_phaseInTime (initial : R) (q : Phase) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (machine caller initial).step
      (cfg (some (phaseLabel q)) regs D ctx) (some (phaseResult q regs D ctx)) (phaseSteps q D) :=
  phaseInTime caller q D regs ctx

@[simp] theorem machine_phaseInTime_steps (initial : R) (q : Phase) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (machine_phaseInTime caller initial q D regs ctx).steps = phaseSteps q D := rfl

end Resources.RotationCertificate.FrontEndStreamMachine

namespace Resources.RotationCertificate.FrontEndStreamMachine

variable {K Λ R : Type} {Γ : K → Type}
variable {K' Λ' R' : Type} {Γ' : K' → Type}
variable (names : StackId K ≃ K') (symbols : ∀ k, alphabet Γ k ≃ Γ' (names k))
  (registers : Registers R ≃ R') (labels : Label Λ ≃ Λ')
variable [DecidableEq K] [DecidableEq K']
variable (caller : Λ → Statement Γ Λ R)
variable (ambient : Λ' → Turing.TM2.Stmt Γ' Λ' R')
variable (installed : ∀ label, Owned (some label) →
  ambient (labels label) =
    FrontEndMachine.Transport.statement names symbols registers labels (program caller label))

include installed in
theorem installed_owned_prefix (start : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start) :
    (FrontEndMachine.Transport.next ambient)^[n]
      (some (installedCfg names symbols registers labels start)) =
      ((next caller)^[n] (some start)).map (installedCfg names symbols registers labels) :=
  installed_prefix_of_owned names symbols registers labels caller ambient installed n start
    (fun j strict => (cfg_localRun caller start).owned_prefix caller j (Nat.lt_of_lt_of_le strict bound))

include installed in
theorem installed_cfg_iterate (start : Cfg Γ Λ R) :
    (FrontEndMachine.Transport.next ambient)^[remainingSteps start]
      (some (installedCfg names symbols registers labels start)) =
      some (installedCfg names symbols registers labels (finalCfg start)) :=
  installed_localRun names symbols registers labels caller ambient installed (cfg_localRun caller start)

include installed in
theorem installed_halt_then_none (start : Cfg Γ Λ R) (halted : (finalCfg start).l = none) :
    (FrontEndMachine.Transport.next ambient)^[remainingSteps start + 1]
      (some (installedCfg names symbols registers labels start)) = none := by
  rw [Function.iterate_succ_apply', installed_cfg_iterate names symbols registers labels caller ambient installed]
  simp only [FrontEndMachine.Transport.next, Option.bind_some, Turing.TM2.step,
    installedCfg, FrontEndMachine.Transport.cfg, halted, Option.map_none]

include installed in
theorem installed_after_halt (start : Cfg Γ Λ R) (halted : (finalCfg start).l = none)
    (n : Nat) (strict : remainingSteps start < n) :
    (FrontEndMachine.Transport.next ambient)^[n]
      (some (installedCfg names symbols registers labels start)) = none := by
  have count : n = (n - (remainingSteps start + 1)) + (remainingSteps start + 1) := by omega
  rw [count, Function.iterate_add_apply,
    installed_halt_then_none names symbols registers labels caller ambient installed start halted]
  have noneIter (j : Nat) :
      (FrontEndMachine.Transport.next ambient)^[j] (none : Option (Turing.TM2.Cfg Γ' Λ' R')) = none := by
    induction j with
    | zero => rfl
    | succ j ih => rw [Function.iterate_succ_apply', ih]; rfl
  exact noneIter _

include installed in
/-- An owned start never enters a caller body: its complete run reaches live
halt, then outer none. Agreement on the ninety-six owned bodies suffices at
every natural time, including times after that halt. -/
theorem installed_iterate_owned_start (start : Cfg Γ Λ R) (owned : Owned start.l) (n : Nat) :
    (FrontEndMachine.Transport.next ambient)^[n]
      (some (installedCfg names symbols registers labels start)) =
      ((next caller)^[n] (some start)).map (installedCfg names symbols registers labels) := by
  by_cases early : n ≤ remainingSteps start
  · exact installed_owned_prefix names symbols registers labels caller ambient installed start n early
  · have halted := finalCfg_halted_of_owned start owned
    rw [installed_after_halt names symbols registers labels caller ambient installed start halted n (by omega),
      cfg_after_halt caller start halted n (by omega), Option.map_none]

include installed in
theorem installed_first_halt (start : Cfg Γ Λ R) (owned : Owned start.l) :
    (FrontEndMachine.Transport.next ambient)^[remainingSteps start]
      (some (installedCfg names symbols registers labels start)) =
      some (installedCfg names symbols registers labels (finalCfg start)) ∧
    (installedCfg names symbols registers labels (finalCfg start)).l = none ∧
    ∀ j, j < remainingSteps start → ∃ reached,
      (FrontEndMachine.Transport.next ambient)^[j]
        (some (installedCfg names symbols registers labels start)) = some reached ∧
      installedOwned labels reached.l := by
  refine ⟨installed_cfg_iterate names symbols registers labels caller ambient installed start, ?_, ?_⟩
  · rw [installedCfg_label, finalCfg_halted_of_owned start owned]
    rfl
  · exact installed_localRun_owned_prefix names symbols registers labels caller ambient installed
      (cfg_localRun caller start)

include installed in
theorem installed_first_halt_iff (start : Cfg Γ Λ R) (owned : Owned start.l)
    (n : Nat) (finish : Turing.TM2.Cfg Γ' Λ' R') :
    ((FrontEndMachine.Transport.next ambient)^[n]
        (some (installedCfg names symbols registers labels start)) = some finish ∧
      finish.l = none ∧
      ∀ j, j < n → ∃ reached,
        (FrontEndMachine.Transport.next ambient)^[j]
          (some (installedCfg names symbols registers labels start)) = some reached ∧
        installedOwned labels reached.l) ↔
      n = remainingSteps start ∧ finish = installedCfg names symbols registers labels (finalCfg start) := by
  constructor
  · rintro ⟨executed, halted, _⟩
    have bound : n ≤ remainingSteps start := by
      by_contra later
      have gone := installed_after_halt names symbols registers labels caller ambient installed start
        (finalCfg_halted_of_owned start owned) n (by omega)
      rw [gone] at executed
      cases executed
    have exactTime : n = remainingSteps start := by
      by_contra notLast
      obtain ⟨middle, before, middleOwned⟩ :=
        installed_localRun_owned_prefix names symbols registers labels caller ambient installed
          (cfg_localRun caller start) n (by omega)
      have same : middle = finish := Option.some.inj (before.symm.trans executed)
      subst middle
      simp only [installedOwned, halted, Option.map_none, Owned] at middleOwned
    subst n
    have endpoint := installed_cfg_iterate names symbols registers labels caller ambient installed start
    exact ⟨rfl, (Option.some.inj (endpoint.symm.trans executed)).symm⟩
  · rintro ⟨rfl, rfl⟩
    exact installed_first_halt names symbols registers labels caller ambient installed start owned

include installed in
theorem installed_owned_prefix_frame (start : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start) :
    ∃ reached, (next caller)^[n] (some start) = some reached ∧
      (FrontEndMachine.Transport.next ambient)^[n]
        (some (installedCfg names symbols registers labels start)) =
        some (installedCfg names symbols registers labels reached) ∧
      remainingSteps reached = remainingSteps start - n ∧
      Relation.ReflTransGen (LocalStep caller) start reached ∧
      (n < remainingSteps start ↔ installedOwned labels (installedCfg names symbols registers labels reached).l) ∧
      (n = 0 → reached = start) ∧
      (installedCfg names symbols registers labels reached).var = registers (registersAt start n) ∧
      user reached.var = user start.var ∧
      (∀ k, (installedCfg names symbols registers labels reached).stk (names (.inr (.inr k))) =
        (start.stk (.inr (.inr k))).map (symbols (.inr (.inr k)))) ∧
      finalCfg reached = finalCfg start := by
  obtain ⟨reached, executed, rank, path, ownership, zero, reset, retained, frame, final⟩ :=
    owned_prefix_frame caller start n bound
  refine ⟨reached, executed, ?_, rank, path, ?_, zero, ?_, retained, ?_, final⟩
  · rw [installed_owned_prefix names symbols registers labels caller ambient installed start n bound, executed]
    rfl
  · simpa only [installedCfg_owned_iff] using ownership
  · rw [installedCfg_registers, reset]
  · intro k
    rw [installedCfg_stack, frame k]

include installed in
def installed_ownedInTime (start : Cfg Γ Λ R) :
    StateTransition.EvalsToInTime (Turing.TM2.step ambient)
      (installedCfg names symbols registers labels start)
      (some (installedCfg names symbols registers labels (finalCfg start))) (remainingSteps start) where
  steps := remainingSteps start
  evals_in_steps := installed_cfg_iterate names symbols registers labels caller ambient installed start
  steps_le_m := Nat.le_refl _

@[simp] theorem installed_ownedInTime_steps (start : Cfg Γ Λ R) :
    (installed_ownedInTime names symbols registers labels caller ambient installed start).steps =
      remainingSteps start := rfl

include installed in
def installed_phaseInTime (q : Phase) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (Turing.TM2.step ambient)
      (installedCfg names symbols registers labels (cfg (some (phaseLabel q)) regs D ctx))
      (some (installedCfg names symbols registers labels (phaseResult q regs D ctx))) (phaseSteps q D) where
  steps := phaseSteps q D
  evals_in_steps := installed_localRun names symbols registers labels caller ambient installed
    (phase_localRun caller q D regs ctx)
  steps_le_m := Nat.le_refl _

@[simp] theorem installed_phaseInTime_steps (q : Phase) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    (installed_phaseInTime names symbols registers labels caller ambient installed q D regs ctx).steps =
      phaseSteps q D := rfl

include installed in
def installed_haltNoneInTime (start : Cfg Γ Λ R) (halted : (finalCfg start).l = none) :
    StateTransition.EvalsToInTime (Turing.TM2.step ambient)
      (installedCfg names symbols registers labels start) none (remainingSteps start + 1) where
  steps := remainingSteps start + 1
  evals_in_steps := installed_halt_then_none names symbols registers labels caller ambient installed start halted
  steps_le_m := Nat.le_refl _

@[simp] theorem installed_haltNoneInTime_steps (start : Cfg Γ Λ R) (halted : (finalCfg start).l = none) :
    (installed_haltNoneInTime names symbols registers labels caller ambient installed start halted).steps =
      remainingSteps start + 1 := rfl

section PhysicalSpace
variable [Fintype K] [Fintype K']

include installed in
theorem installed_owned_prefix_space (start : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start) :
    ∃ reached, (next caller)^[n] (some start) = some reached ∧
      (FrontEndMachine.Transport.next ambient)^[n]
        (some (installedCfg names symbols registers labels start)) =
        some (installedCfg names symbols registers labels reached) ∧
      remainingSteps reached = remainingSteps start - n ∧
      Relation.ReflTransGen (LocalStep caller) start reached ∧
      (n < remainingSteps start ↔ installedOwned labels (installedCfg names symbols registers labels reached).l) ∧
      (n = 0 → reached = start) ∧
      (installedCfg names symbols registers labels reached).var = registers (registersAt start n) ∧
      user reached.var = user start.var ∧
      (∀ k, (installedCfg names symbols registers labels reached).stk (names (.inr (.inr k))) =
        (start.stk (.inr (.inr k))).map (symbols (.inr (.inr k)))) ∧
      finalCfg reached = finalCfg start ∧
      (∑ k, ((installedCfg names symbols registers labels reached).stk k).length) ≤ allowance start := by
  obtain ⟨reached, executed, ambientRun, rank, path, ownership, zero, reset, retained, frame, final⟩ :=
    installed_owned_prefix_frame names symbols registers labels caller ambient installed start n bound
  refine ⟨reached, executed, ambientRun, rank, path, ownership, zero, reset, retained, frame, final, ?_⟩
  rw [installed_stack_cells]
  exact prefix_stackCells_le_dirty caller start n bound reached executed

end PhysicalSpace

end Resources.RotationCertificate.FrontEndStreamMachine
