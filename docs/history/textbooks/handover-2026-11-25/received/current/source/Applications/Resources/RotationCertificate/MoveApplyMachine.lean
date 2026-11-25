import Applications.Resources.RotationCertificate.FrontEndMachine
import Applications.Resources.RotationCertificate.PositionedRotationMachine

/-!
# Physical move parsing followed by positioned rotation

The parser and positioned rotation share one forward path and seven physical
local stores. Their finite blocks are transported through complete equivalences;
each parser result dispatches in one actual activation. All source operations,
clocks and potentials occur only in proof-side declarations. This open component
does not implement the enclosing verifier's fuel, EOF or final-cleanup loop.
Correspondence: requirements13 and the fixed MoveApply preparation in
`docs/research/fdsa-rotation-certificate-preparation.md`.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.RotationCertificate.MoveApplyMachine
open Search.SharedTree (Branch)
open Trees.Rotations (RotationDirection RotationMove)

inductive LocalStack
  | certificate | moveReverse | path | source | saved | scratch | pending
  deriving DecidableEq

instance : Fintype LocalStack where
  elems := {.certificate, .moveReverse, .path, .source, .saved, .scratch, .pending}
  complete k := by cases k <;> decide

abbrev StackId (K : Type) := LocalStack ⊕ K
abbrev Temporaries := PositionedRotationMachine.Temporaries
abbrev Registers (R : Type) := PositionedRotationMachine.Registers R
abbrev FinalResult := Unit ⊕ PositionedRotationMachine.Result
abbrev Phase := MoveParserMachine.Phase ⊕
  (MoveParserMachine.Result ⊕ PositionedRotationMachine.Phase)
abbrev External (Λ : Type) := FinalResult ⊕ Λ
abbrev Label (Λ : Type) := MoveParserMachine.Phase ⊕
  (MoveParserMachine.Result ⊕ (PositionedRotationMachine.Phase ⊕ External Λ))

def parseFailure : FinalResult := .inl ()
def rotationFailure : FinalResult := .inr .failure
def success : FinalResult := .inr .success

def movePhase (q : MoveParserMachine.Phase) : Phase := .inl q
def dispatchPhase (r : MoveParserMachine.Result) : Phase := .inr (.inl r)
def positionPhase (q : PositionedRotationMachine.Phase) : Phase := .inr (.inr q)

structure LocalData where
  certificate : Word := []
  moveReverse : List Branch := []
  path : List Branch := []
  source : Word := []
  saved : Word := []
  scratch : Word := []
  pending : List Unit := []
  deriving DecidableEq

variable {K Λ R : Type} {Γ : K → Type}

abbrev alphabet (Γ : K → Type) : StackId K → Type
  | .inl .certificate | .inl .source | .inl .saved | .inl .scratch => Tag
  | .inl .moveReverse | .inl .path => Branch
  | .inl .pending => Unit
  | .inr k => Γ k

instance alphabetFintype [∀ k, Fintype (Γ k)] (k : StackId K) :
    Fintype (alphabet Γ k) := by
  cases k with
  | inl k => cases k <;> exact inferInstance
  | inr k => exact inferInstance

abbrev Statement (Γ : K → Type) (Λ R : Type) :=
  Turing.TM2.Stmt (alphabet Γ) (Label Λ) (Registers R)
abbrev Cfg (Γ : K → Type) (Λ R : Type) :=
  Turing.TM2.Cfg (alphabet Γ) (Label Λ) (Registers R)

def moveLabel (q : MoveParserMachine.Phase) : Label Λ := .inl q
def dispatchLabel (r : MoveParserMachine.Result) : Label Λ := .inr (.inl r)
def positionLabel (q : PositionedRotationMachine.Phase) : Label Λ :=
  .inr (.inr (.inl q))
def resultLabel (r : FinalResult) : Label Λ := .inr (.inr (.inr (.inl r)))
def callerLabel (label : Λ) : Label Λ := .inr (.inr (.inr (.inr label)))
def phaseLabel : Phase → Label Λ
  | .inl q => moveLabel q
  | .inr (.inl r) => dispatchLabel r
  | .inr (.inr q) => positionLabel q

def Owned : Option (Label Λ) → Prop
  | some (.inl _) | some (.inr (.inl _)) | some (.inr (.inr (.inl _))) => True
  | _ => False

def resetMove (regs : Registers R) : Registers R :=
  ((regs.1.1, (none, regs.1.2.2)), regs.2)
def reset (regs : Registers R) : Registers R := PositionedRotationMachine.reset regs

@[simp] theorem reset_reset (regs : Registers R) : reset (reset regs) = reset regs := rfl
@[simp] theorem resetMove_resetMove (regs : Registers R) :
    resetMove (resetMove regs) = resetMove regs := rfl
@[simp] theorem reset_resetMove (regs : Registers R) : reset (resetMove regs) = reset regs := rfl
@[simp] theorem resetMove_reset (regs : Registers R) : resetMove (reset regs) = reset regs := rfl

def cfg (label : Option (Label Λ)) (regs : Registers R) (D : LocalData)
    (ctx : ∀ k, List (Γ k)) : Cfg Γ Λ R where
  l := label
  var := regs
  stk := fun k => match k with
    | .inl .certificate => D.certificate
    | .inl .moveReverse => D.moveReverse
    | .inl .path => D.path
    | .inl .source => D.source
    | .inl .saved => D.saved
    | .inl .scratch => D.scratch
    | .inl .pending => D.pending
    | .inr k => ctx k

def dataOfCfg (c : Cfg Γ Λ R) : LocalData where
  certificate := c.stk (.inl .certificate)
  moveReverse := c.stk (.inl .moveReverse)
  path := c.stk (.inl .path)
  source := c.stk (.inl .source)
  saved := c.stk (.inl .saved)
  scratch := c.stk (.inl .scratch)
  pending := c.stk (.inl .pending)

def contextOfCfg (c : Cfg Γ Λ R) : ∀ k, List (Γ k) := fun k => c.stk (.inr k)


theorem cfg_ext {a b : Cfg Γ Λ R} (label : a.l = b.l) (regs : a.var = b.var)
    (stores : a.stk = b.stk) : a = b := by
  cases a
  cases b
  cases label
  cases regs
  cases stores
  rfl

theorem cfg_eta (c : Cfg Γ Λ R) :
    cfg c.l c.var (dataOfCfg c) (contextOfCfg c) = c := by
  apply cfg_ext
  · rfl
  · rfl
  · funext k
    cases k with
    | inl k => cases k <;> rfl
    | inr k => rfl

@[simp] theorem dataOfCfg_cfg (label : Option (Label Λ)) (regs : Registers R)
    (D : LocalData) (ctx : ∀ k, List (Γ k)) : dataOfCfg (cfg label regs D ctx) = D := by
  cases D
  rfl

@[simp] theorem contextOfCfg_cfg (label : Option (Label Λ)) (regs : Registers R)
    (D : LocalData) (ctx : ∀ k, List (Γ k)) : contextOfCfg (cfg label regs D ctx) = ctx := rfl

@[simp] theorem owned_phase (q : Phase) : Owned (some (phaseLabel (Λ := Λ) q)) := by
  cases q with
  | inl q => trivial
  | inr q => cases q <;> trivial

@[simp] theorem not_owned_result (r : FinalResult) :
    ¬ Owned (some (resultLabel (Λ := Λ) r)) := by simp only [Owned, resultLabel, not_false_eq_true]

abbrev OwnedLabel (Λ : Type) := {label : Label Λ // Owned (some label)}

def ownedLabelEquiv : Phase ≃ OwnedLabel Λ where
  toFun q := ⟨phaseLabel q, owned_phase q⟩
  invFun label := match label with
    | ⟨.inl q, _⟩ => movePhase q
    | ⟨.inr (.inl r), _⟩ => dispatchPhase r
    | ⟨.inr (.inr (.inl q)), _⟩ => positionPhase q
    | ⟨.inr (.inr (.inr _)), impossible⟩ => False.elim impossible
  left_inv q := by cases q with
    | inl q => rfl
    | inr q => cases q <;> rfl
  right_inv label := by
    rcases label with ⟨label, h⟩
    cases label with
    | inl q => rfl
    | inr label => cases label with
      | inl r => rfl
      | inr label => cases label with
        | inl q => rfl
        | inr external => exact False.elim h

instance : Fintype (OwnedLabel Λ) := Fintype.ofEquiv Phase ownedLabelEquiv

theorem card_localStack : Fintype.card LocalStack = 7 := by decide
theorem card_phase : Fintype.card Phase = 26 := by decide
theorem card_finalResult : Fintype.card FinalResult = 3 := by decide
theorem card_temporaries : Fintype.card Temporaries = 102 := PositionedRotationMachine.card_temporaries
theorem card_ownedLabel : Fintype.card (OwnedLabel Λ) = 26 := by
  rw [← Fintype.card_congr (ownedLabelEquiv (Λ := Λ))]
  exact card_phase

theorem card_stackId [Fintype K] : Fintype.card (StackId K) = 7 + Fintype.card K := by
  rw [Fintype.card_sum, card_localStack]

theorem card_label [Fintype Λ] : Fintype.card (Label Λ) = 29 + Fintype.card Λ := by
  rw [Fintype.card_sum, Fintype.card_sum, Fintype.card_sum, Fintype.card_sum,
    show Fintype.card MoveParserMachine.Phase = 7 by decide,
    show Fintype.card MoveParserMachine.Result = 3 by decide,
    PositionedRotationMachine.card_phase, card_finalResult]
  omega

theorem card_registers [Fintype R] : Fintype.card (Registers R) = 102 * Fintype.card R := by
  rw [Fintype.card_prod, card_temporaries]

/-! ## Complete FrontEnd physical data compatibility

These are complete physical stack, dependent-alphabet and register maps. They
do not supply a common FrontEnd/controller label map or an installed program.
The two added Branch stores and the added Branch register remain actual incoming
data until a subsequently proved machine activation changes them.
-/

inductive NewBranchStores | moveReverse | path
  deriving DecidableEq

instance : Fintype NewBranchStores where
  elems := {.moveReverse, .path}
  complete k := by cases k <;> decide

inductive FrontEndProtected
  | framedRaw | frameFirstReverse | frameCertReverse | inputBits | certificateBits
  | inputRaw | targetTree | fuel | bitsReverse
  deriving DecidableEq

instance : Fintype FrontEndProtected where
  elems := {.framedRaw, .frameFirstReverse, .frameCertReverse, .inputBits,
    .certificateBits, .inputRaw, .targetTree, .fuel, .bitsReverse}
  complete k := by cases k <;> decide

abbrev frontEndAddedAlphabet (Γ : K → Type) : NewBranchStores ⊕ K → Type
  | .inl _ => Branch
  | .inr k => Γ k

abbrev frontEndProtectedAlphabet (Γ : K → Type) : FrontEndProtected ⊕ K → Type
  | .inl .inputRaw | .inl .targetTree => Tag
  | .inl .framedRaw | .inl .frameFirstReverse | .inl .frameCertReverse
  | .inl .inputBits | .inl .certificateBits | .inl .fuel | .inl .bitsReverse => Bool
  | .inr k => Γ k

instance frontEndAddedFintype [∀ k, Fintype (Γ k)] (k : NewBranchStores ⊕ K) :
    Fintype (frontEndAddedAlphabet Γ k) := by
  cases k with
  | inl k => exact inferInstance
  | inr k => exact inferInstance

instance frontEndProtectedFintype [∀ k, Fintype (Γ k)] (k : FrontEndProtected ⊕ K) :
    Fintype (frontEndProtectedAlphabet Γ k) := by
  cases k with
  | inl k => cases k <;> exact inferInstance
  | inr k => exact inferInstance

/-- All sixteen local physical stores, including the two added Branch stores. -/
def frontEndStackEquiv : FrontEndMachine.StackId (NewBranchStores ⊕ K) ≃
    StackId (FrontEndProtected ⊕ K) where
  toFun
    | .inl .framedRaw => .inr (.inl .framedRaw)
    | .inl .frameFirstReverse => .inr (.inl .frameFirstReverse)
    | .inl .frameCertReverse => .inr (.inl .frameCertReverse)
    | .inl .inputBits => .inr (.inl .inputBits)
    | .inl .certificateBits => .inr (.inl .certificateBits)
    | .inl .inputRaw => .inr (.inl .inputRaw)
    | .inl .decodeReverse => .inl .scratch
    | .inl .certificateWord => .inl .certificate
    | .inl .sourceTree => .inl .source
    | .inl .targetTree => .inr (.inl .targetTree)
    | .inl .treeReverse => .inl .saved
    | .inl .pending => .inl .pending
    | .inl .fuel => .inr (.inl .fuel)
    | .inl .bitsReverse => .inr (.inl .bitsReverse)
    | .inr (.inl .moveReverse) => .inl .moveReverse
    | .inr (.inl .path) => .inl .path
    | .inr (.inr k) => .inr (.inr k)
  invFun
    | .inl .certificate => .inl .certificateWord
    | .inl .moveReverse => .inr (.inl .moveReverse)
    | .inl .path => .inr (.inl .path)
    | .inl .source => .inl .sourceTree
    | .inl .saved => .inl .treeReverse
    | .inl .scratch => .inl .decodeReverse
    | .inl .pending => .inl .pending
    | .inr (.inl .framedRaw) => .inl .framedRaw
    | .inr (.inl .frameFirstReverse) => .inl .frameFirstReverse
    | .inr (.inl .frameCertReverse) => .inl .frameCertReverse
    | .inr (.inl .inputBits) => .inl .inputBits
    | .inr (.inl .certificateBits) => .inl .certificateBits
    | .inr (.inl .inputRaw) => .inl .inputRaw
    | .inr (.inl .targetTree) => .inl .targetTree
    | .inr (.inl .fuel) => .inl .fuel
    | .inr (.inl .bitsReverse) => .inl .bitsReverse
    | .inr (.inr k) => .inr (.inr k)
  left_inv k := by
    cases k with
    | inl k => cases k <;> rfl
    | inr k => cases k with
      | inl k => cases k <;> rfl
      | inr k => rfl
  right_inv k := by
    cases k with
    | inl k => cases k <;> rfl
    | inr k => cases k with
      | inl k => cases k <;> rfl
      | inr k => rfl

def frontEndSymbolEquiv (k : FrontEndMachine.StackId (NewBranchStores ⊕ K)) :
    FrontEndMachine.alphabet (frontEndAddedAlphabet Γ) k ≃
      alphabet (frontEndProtectedAlphabet Γ) (frontEndStackEquiv k) := by
  cases k with
  | inl k => cases k <;> exact Equiv.refl _
  | inr k => cases k with
    | inl k => cases k <;> exact Equiv.refl _
    | inr k => exact Equiv.refl _

def frontEndRegisterEquiv : FrontEndMachine.Registers (Option Branch × R) ≃
    Registers (OpenDecoderMachine.Temporaries × R) where
  toFun regs := ((regs.2.2.1, regs.1), (regs.2.1, regs.2.2.2))
  invFun regs := (regs.1.2, (regs.2.1, (regs.1.1, regs.2.2)))
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem frontEndRegisterEquiv_reset
    (regs : FrontEndMachine.Registers (Option Branch × R)) :
    frontEndRegisterEquiv (FrontEndMachine.reset regs) =
      ((regs.2.2.1, (none, none)), (BitDecoderMachine.zeroRegisters, regs.2.2.2)) := rfl

@[simp] theorem frontEndRegisterEquiv_resetMove
    (regs : FrontEndMachine.Registers (Option Branch × R)) :
    resetMove (frontEndRegisterEquiv (FrontEndMachine.reset regs)) =
      frontEndRegisterEquiv (FrontEndMachine.reset regs) := rfl

@[simp] theorem frontEndRegisterEquiv_fullReset
    (regs : FrontEndMachine.Registers (Option Branch × R)) :
    reset (frontEndRegisterEquiv (FrontEndMachine.reset regs)) =
      ((none, (none, none)), (BitDecoderMachine.zeroRegisters, regs.2.2.2)) := rfl

theorem frontEnd_newBranch_card : Fintype.card NewBranchStores = 2 := by decide
theorem frontEnd_protected_card : Fintype.card FrontEndProtected = 9 := by decide

theorem frontEnd_stack_card [Fintype K] :
    Fintype.card (StackId (FrontEndProtected ⊕ K)) = 16 + Fintype.card K := by
  rw [card_stackId, Fintype.card_sum, frontEnd_protected_card]
  omega

theorem frontEnd_source_stack_card [Fintype K] :
    Fintype.card (FrontEndMachine.StackId (NewBranchStores ⊕ K)) =
      16 + Fintype.card K := by
  rw [Fintype.card_congr (frontEndStackEquiv (K := K))]
  exact frontEnd_stack_card

theorem frontEnd_register_card [Fintype R] :
    Fintype.card (Registers (OpenDecoderMachine.Temporaries × R)) =
      140454 * Fintype.card R := by
  rw [card_registers, Fintype.card_prod, OpenDecoderMachine.card_temporaries]
  omega

theorem frontEnd_source_register_card [Fintype R] :
    Fintype.card (FrontEndMachine.Registers (Option Branch × R)) =
      140454 * Fintype.card R := by
  rw [Fintype.card_congr (frontEndRegisterEquiv (R := R))]
  exact frontEnd_register_card

def frontEndStacks : (∀ k, List (FrontEndMachine.alphabet (frontEndAddedAlphabet Γ) k)) ≃
    (∀ k, List (alphabet (frontEndProtectedAlphabet Γ) k)) :=
  FrontEndMachine.Transport.stackEquiv frontEndStackEquiv frontEndSymbolEquiv

@[simp] theorem frontEndStacks_apply
    (data : ∀ k, List (FrontEndMachine.alphabet (frontEndAddedAlphabet Γ) k))
    (k : FrontEndMachine.StackId (NewBranchStores ⊕ K)) :
    frontEndStacks data (frontEndStackEquiv k) = (data k).map (frontEndSymbolEquiv k) :=
  FrontEndMachine.Transport.stackEquiv_apply _ _ _ _

theorem frontEnd_stack_cells [Fintype K]
    (data : ∀ k, List (FrontEndMachine.alphabet (frontEndAddedAlphabet Γ) k)) :
    ∑ k, (frontEndStacks data k).length = ∑ k, (data k).length :=
  FrontEndMachine.Transport.stackCells frontEndStackEquiv frontEndSymbolEquiv data

def frontEndAddedContext (B O : List Branch) (ctx : ∀ k, List (Γ k)) :
    ∀ k, List (frontEndAddedAlphabet Γ k)
  | .inl .moveReverse => B
  | .inl .path => O
  | .inr k => ctx k

def frontEndSuccessContext (target : BinaryTree Unit) (fuel : List Bool)
    (ctx : ∀ k, List (Γ k)) : ∀ k, List (frontEndProtectedAlphabet Γ k)
  | .inl .targetTree => treeCode target
  | .inl .fuel => fuel
  | .inl .inputRaw => []
  | .inl .framedRaw | .inl .frameFirstReverse | .inl .frameCertReverse
  | .inl .inputBits | .inl .certificateBits | .inl .bitsReverse => []
  | .inr k => ctx k

def frontEndSuccessData (source : BinaryTree Unit) (cert : Word) (B O : List Branch) :
    LocalData := { certificate := cert, moveReverse := B, path := O, source := treeCode source }

/-- The physical view intentionally has no label component. -/
def frontEndPhysicalData
    (c : FrontEndMachine.Cfg (frontEndAddedAlphabet Γ) Λ (Option Branch × R)) :
    Registers (OpenDecoderMachine.Temporaries × R) ×
      (∀ k, List (alphabet (frontEndProtectedAlphabet Γ) k)) :=
  (frontEndRegisterEquiv c.var, frontEndStacks c.stk)

theorem frontEnd_success_stores
    (regs : FrontEndMachine.Registers (Option Branch × R)) (B O : List Branch)
    (ctx : ∀ k, List (Γ k)) (source target : BinaryTree Unit) (fuel : List Bool) (cert : Word) :
    frontEndStacks (FrontEndMachine.resultCfg (Λ := Λ) regs (frontEndAddedContext B O ctx)
      (.success source target fuel cert)).stk =
      (cfg (Λ := Unit) none (frontEndRegisterEquiv (FrontEndMachine.reset regs))
        (frontEndSuccessData source cert B O) (frontEndSuccessContext target fuel ctx)).stk := by
  funext k
  obtain ⟨k, rfl⟩ := (frontEndStackEquiv (K := K)).surjective k
  rw [frontEndStacks_apply]
  cases k with
  | inl k => cases k <;> change List.map id _ = _ <;> exact List.map_id _
  | inr k => cases k with
    | inl k => cases k <;> change List.map id _ = _ <;> exact List.map_id _
    | inr k => change List.map id _ = _; exact List.map_id _

/-- Consume the real FrontEnd result, retaining both incoming Branch words and
the stale Branch register. The conclusion compares physical data, not control. -/
theorem frontEnd_success_physical_data
    (regs : FrontEndMachine.Registers (Option Branch × R)) (B O : List Branch)
    (ctx : ∀ k, List (Γ k)) (source target : BinaryTree Unit) (fuel : List Bool) (cert : Word) :
    frontEndPhysicalData (FrontEndMachine.resultCfg (Λ := Λ) regs
      (frontEndAddedContext B O ctx) (.success source target fuel cert)) =
      (((regs.2.2.1, (none, none)), (BitDecoderMachine.zeroRegisters, regs.2.2.2)),
        (cfg (Λ := Unit) none (frontEndRegisterEquiv (FrontEndMachine.reset regs))
          (frontEndSuccessData source cert B O) (frontEndSuccessContext target fuel ctx)).stk) := by
  apply Prod.ext
  · rfl
  · exact frontEnd_success_stores regs B O ctx source target fuel cert

theorem frontEnd_protected_sum (f : FrontEndProtected → Nat) :
    ∑ k, f k = f .framedRaw + f .frameFirstReverse + f .frameCertReverse +
      f .inputBits + f .certificateBits + f .inputRaw + f .targetTree + f .fuel +
      f .bitsReverse := by
  change (∑ k ∈ ({.framedRaw, .frameFirstReverse, .frameCertReverse, .inputBits,
    .certificateBits, .inputRaw, .targetTree, .fuel, .bitsReverse} : Finset FrontEndProtected), f k) = _
  simp [Nat.add_comm, Nat.add_left_comm]

theorem frontEnd_success_context_cells [Fintype K] (target : BinaryTree Unit)
    (fuel : List Bool) (ctx : ∀ k, List (Γ k)) :
    ∑ k, (frontEndSuccessContext target fuel ctx k).length =
      (treeCode target).length + fuel.length + ∑ k, (ctx k).length := by
  rw [Fintype.sum_sum_type, frontEnd_protected_sum]
  simp [frontEndSuccessContext]


inductive MoveProtected | source | saved | scratch | pending
  deriving DecidableEq

instance : Fintype MoveProtected where
  elems := {.source, .saved, .scratch, .pending}
  complete k := by cases k <;> decide

abbrev moveProtectedAlphabet (Γ : K → Type) : MoveProtected ⊕ K → Type
  | .inl .source | .inl .saved | .inl .scratch => Tag
  | .inl .pending => Unit
  | .inr k => Γ k

instance moveProtectedFintype [∀ k, Fintype (Γ k)] (k : MoveProtected ⊕ K) :
    Fintype (moveProtectedAlphabet Γ k) := by
  cases k with
  | inl k => cases k <;> exact inferInstance
  | inr k => exact inferInstance

abbrev MoveCallerRegister (R : Type) := (Option Branch × Option Unit) × R
abbrev MoveCallerLabel (Λ : Type) := PositionedRotationMachine.Phase ⊕ External Λ
abbrev MoveCfg (Γ : K → Type) (Λ R : Type) :=
  MoveParserMachine.Cfg (moveProtectedAlphabet Γ) (MoveCallerLabel Λ) (MoveCallerRegister R)
abbrev MoveStatement (Γ : K → Type) (Λ R : Type) :=
  MoveParserMachine.Statement (moveProtectedAlphabet Γ) (MoveCallerLabel Λ) (MoveCallerRegister R)

def moveStackEquiv : MoveParserMachine.StackId (MoveProtected ⊕ K) ≃ StackId K where
  toFun
    | .inl .raw => .inl .certificate
    | .inl .reverse => .inl .moveReverse
    | .inl .path => .inl .path
    | .inr (.inl .source) => .inl .source
    | .inr (.inl .saved) => .inl .saved
    | .inr (.inl .scratch) => .inl .scratch
    | .inr (.inl .pending) => .inl .pending
    | .inr (.inr k) => .inr k
  invFun
    | .inl .certificate => .inl .raw
    | .inl .moveReverse => .inl .reverse
    | .inl .path => .inl .path
    | .inl .source => .inr (.inl .source)
    | .inl .saved => .inr (.inl .saved)
    | .inl .scratch => .inr (.inl .scratch)
    | .inl .pending => .inr (.inl .pending)
    | .inr k => .inr (.inr k)
  left_inv k := by
    cases k with
    | inl k => cases k <;> rfl
    | inr k => cases k with
      | inl k => cases k <;> rfl
      | inr k => rfl
  right_inv k := by
    cases k with
    | inl k => cases k <;> rfl
    | inr k => rfl

def moveSymbolEquiv (k : MoveParserMachine.StackId (MoveProtected ⊕ K)) :
    MoveParserMachine.alphabet (moveProtectedAlphabet Γ) k ≃
      alphabet Γ (moveStackEquiv k) := by
  cases k with
  | inl k => cases k <;> exact Equiv.refl _
  | inr k => cases k with
    | inl k => cases k <;> exact Equiv.refl _
    | inr k => exact Equiv.refl _

def moveRegisterEquiv : MoveParserMachine.Registers (MoveCallerRegister R) ≃ Registers R where
  toFun regs := ((regs.2.1.1, (regs.1, regs.2.1.2)), regs.2.2)
  invFun regs := (regs.1.2.1, ((regs.1.1, regs.1.2.2), regs.2))
  left_inv regs := by rcases regs with ⟨a, ⟨⟨b, u⟩, r⟩⟩; rfl
  right_inv regs := by rcases regs with ⟨⟨b, ⟨a, u⟩⟩, r⟩; rfl

def moveLabelEquiv : MoveParserMachine.Label (MoveCallerLabel Λ) ≃ Label Λ := Equiv.refl _

@[simp] theorem moveLabelEquiv_phase (q : MoveParserMachine.Phase) :
    moveLabelEquiv (MoveParserMachine.phaseLabel q) = moveLabel (Λ := Λ) q := rfl
@[simp] theorem moveLabelEquiv_result (r : MoveParserMachine.Result) :
    moveLabelEquiv (MoveParserMachine.resultLabel r) = dispatchLabel (Λ := Λ) r := rfl
@[simp] theorem moveRegisterEquiv_reset (regs : MoveParserMachine.Registers (MoveCallerRegister R)) :
    moveRegisterEquiv (MoveParserMachine.reset regs) = resetMove (moveRegisterEquiv regs) := rfl

inductive PositionProtected | certificate | moveReverse
  deriving DecidableEq

instance : Fintype PositionProtected where
  elems := {.certificate, .moveReverse}
  complete k := by cases k <;> decide

abbrev positionProtectedAlphabet (Γ : K → Type) : PositionProtected ⊕ K → Type
  | .inl .certificate => Tag
  | .inl .moveReverse => Branch
  | .inr k => Γ k

instance positionProtectedFintype [∀ k, Fintype (Γ k)] (k : PositionProtected ⊕ K) :
    Fintype (positionProtectedAlphabet Γ k) := by
  cases k with
  | inl k => cases k <;> exact inferInstance
  | inr k => exact inferInstance

abbrev PositionCallerLabel (Λ : Type) :=
  MoveParserMachine.Phase ⊕ (MoveParserMachine.Result ⊕ (Unit ⊕ Λ))
abbrev PositionCfg (Γ : K → Type) (Λ R : Type) :=
  PositionedRotationMachine.Cfg (positionProtectedAlphabet Γ) (PositionCallerLabel Λ) R
abbrev PositionStatement (Γ : K → Type) (Λ R : Type) :=
  PositionedRotationMachine.Statement (positionProtectedAlphabet Γ) (PositionCallerLabel Λ) R

def positionStackEquiv :
    PositionedRotationMachine.StackId (PositionProtected ⊕ K) ≃ StackId K where
  toFun
    | .inl .source => .inl .source
    | .inl .saved => .inl .saved
    | .inl .scratch => .inl .scratch
    | .inl .pending => .inl .pending
    | .inl .path => .inl .path
    | .inr (.inl .certificate) => .inl .certificate
    | .inr (.inl .moveReverse) => .inl .moveReverse
    | .inr (.inr k) => .inr k
  invFun
    | .inl .source => .inl .source
    | .inl .saved => .inl .saved
    | .inl .scratch => .inl .scratch
    | .inl .pending => .inl .pending
    | .inl .path => .inl .path
    | .inl .certificate => .inr (.inl .certificate)
    | .inl .moveReverse => .inr (.inl .moveReverse)
    | .inr k => .inr (.inr k)
  left_inv k := by
    cases k with
    | inl k => cases k <;> rfl
    | inr k => cases k with
      | inl k => cases k <;> rfl
      | inr k => rfl
  right_inv k := by
    cases k with
    | inl k => cases k <;> rfl
    | inr k => rfl

def positionSymbolEquiv (k : PositionedRotationMachine.StackId (PositionProtected ⊕ K)) :
    PositionedRotationMachine.alphabet (positionProtectedAlphabet Γ) k ≃
      alphabet Γ (positionStackEquiv k) := by
  cases k with
  | inl k => cases k <;> exact Equiv.refl _
  | inr k => cases k with
    | inl k => cases k <;> exact Equiv.refl _
    | inr k => exact Equiv.refl _

def positionLabelEquiv : PositionedRotationMachine.Label (PositionCallerLabel Λ) ≃ Label Λ where
  toFun
    | .inl q => positionLabel q
    | .inr (.inl r) => resultLabel (.inr r)
    | .inr (.inr (.inl q)) => moveLabel q
    | .inr (.inr (.inr (.inl r))) => dispatchLabel r
    | .inr (.inr (.inr (.inr (.inl u)))) => resultLabel (.inl u)
    | .inr (.inr (.inr (.inr (.inr label)))) => callerLabel label
  invFun
    | .inl q => .inr (.inr (.inl q))
    | .inr (.inl r) => .inr (.inr (.inr (.inl r)))
    | .inr (.inr (.inl q)) => .inl q
    | .inr (.inr (.inr (.inl (.inl u)))) => .inr (.inr (.inr (.inr (.inl u))))
    | .inr (.inr (.inr (.inl (.inr r)))) => .inr (.inl r)
    | .inr (.inr (.inr (.inr label))) => .inr (.inr (.inr (.inr (.inr label))))
  left_inv label := by
    rcases label with q | (r | (q | (r | (u | label)))) <;> rfl
  right_inv label := by
    rcases label with q | (r | (q | ((u | r) | label))) <;> rfl

@[simp] theorem positionLabelEquiv_phase (q : PositionedRotationMachine.Phase) :
    positionLabelEquiv (PositionedRotationMachine.phaseLabel q) = positionLabel (Λ := Λ) q := rfl
@[simp] theorem positionLabelEquiv_result (r : PositionedRotationMachine.Result) :
    positionLabelEquiv (PositionedRotationMachine.resultLabel r) = resultLabel (Λ := Λ) (.inr r) := rfl

def moveContext (D : LocalData) (ctx : ∀ k, List (Γ k)) :
    ∀ k, List (moveProtectedAlphabet Γ k)
  | .inl .source => D.source
  | .inl .saved => D.saved
  | .inl .scratch => D.scratch
  | .inl .pending => D.pending
  | .inr k => ctx k

def positionData (D : LocalData) : PositionedRotationMachine.LocalData :=
  ⟨D.source, D.saved, D.scratch, D.pending, D.path⟩

def setPositionData (D : LocalData) (E : PositionedRotationMachine.LocalData) : LocalData :=
  { D with
    source := E.source
    saved := E.saved
    scratch := E.scratch
    pending := E.pending
    path := E.path }

@[simp] theorem positionData_setPositionData (D : LocalData) (E : PositionedRotationMachine.LocalData) :
    positionData (setPositionData D E) = E := by cases E; rfl
@[simp] theorem setPositionData_positionData (D : LocalData) :
    setPositionData D (positionData D) = D := by cases D; rfl

def positionContext (D : LocalData) (ctx : ∀ k, List (Γ k)) :
    ∀ k, List (positionProtectedAlphabet Γ k)
  | .inl .certificate => D.certificate
  | .inl .moveReverse => D.moveReverse
  | .inr k => ctx k

def moveView (label : Option (MoveParserMachine.Label (MoveCallerLabel Λ)))
    (regs : MoveParserMachine.Registers (MoveCallerRegister R)) (D : LocalData)
    (ctx : ∀ k, List (Γ k)) : MoveCfg Γ Λ R :=
  MoveParserMachine.cfg label regs D.certificate D.moveReverse D.path (moveContext D ctx)

def positionView (label : Option (PositionedRotationMachine.Label (PositionCallerLabel Λ)))
    (regs : Registers R) (D : LocalData) (ctx : ∀ k, List (Γ k)) : PositionCfg Γ Λ R :=
  PositionedRotationMachine.cfg label regs (positionData D) (positionContext D ctx)

def moveCfg (c : MoveCfg Γ Λ R) : Cfg Γ Λ R :=
  FrontEndMachine.Transport.cfg moveStackEquiv moveSymbolEquiv moveRegisterEquiv moveLabelEquiv c

def positionCfg (c : PositionCfg Γ Λ R) : Cfg Γ Λ R :=
  FrontEndMachine.Transport.cfg positionStackEquiv positionSymbolEquiv (Equiv.refl _) positionLabelEquiv c

theorem moveCfg_view (label : Option (MoveParserMachine.Label (MoveCallerLabel Λ)))
    (regs : MoveParserMachine.Registers (MoveCallerRegister R)) (D : LocalData)
    (ctx : ∀ k, List (Γ k)) :
    moveCfg (moveView label regs D ctx) = cfg (label.map moveLabelEquiv) (moveRegisterEquiv regs) D ctx := by
  apply cfg_ext
  · rfl
  · rfl
  · funext k
    obtain ⟨k, rfl⟩ := moveStackEquiv.surjective k
    change FrontEndMachine.Transport.stackEquiv moveStackEquiv (moveSymbolEquiv (Γ := Γ))
      (moveView label regs D ctx).stk (moveStackEquiv k) = _
    rw [FrontEndMachine.Transport.stackEquiv_apply]
    cases k with
    | inl k => cases k <;> change List.map id _ = _ <;> exact List.map_id _
    | inr k => cases k with
      | inl k => cases k <;> change List.map id _ = _ <;> exact List.map_id _
      | inr k => change List.map id _ = _; exact List.map_id _

theorem positionCfg_view (label : Option (PositionedRotationMachine.Label (PositionCallerLabel Λ)))
    (regs : Registers R) (D : LocalData) (ctx : ∀ k, List (Γ k)) :
    positionCfg (positionView label regs D ctx) = cfg (label.map positionLabelEquiv) regs D ctx := by
  apply cfg_ext
  · rfl
  · rfl
  · funext k
    obtain ⟨k, rfl⟩ := positionStackEquiv.surjective k
    change FrontEndMachine.Transport.stackEquiv positionStackEquiv (positionSymbolEquiv (Γ := Γ))
      (positionView label regs D ctx).stk (positionStackEquiv k) = _
    rw [FrontEndMachine.Transport.stackEquiv_apply]
    cases k with
    | inl k => cases k <;> change List.map id _ = _ <;> exact List.map_id _
    | inr k => cases k with
      | inl k => cases k <;> change List.map id _ = _ <;> exact List.map_id _
      | inr k => change List.map id _ = _; exact List.map_id _

def moveTranslate (body : MoveStatement Γ Λ R) : Statement Γ Λ R :=
  FrontEndMachine.Transport.statement moveStackEquiv moveSymbolEquiv moveRegisterEquiv moveLabelEquiv body

def positionTranslate (body : PositionStatement Γ Λ R) : Statement Γ Λ R :=
  FrontEndMachine.Transport.statement positionStackEquiv positionSymbolEquiv (Equiv.refl _)
    positionLabelEquiv body

def moveBlock (q : MoveParserMachine.Phase) : Statement Γ Λ R :=
  moveTranslate (MoveParserMachine.block q)

def positionBlock (q : PositionedRotationMachine.Phase) : Statement Γ Λ R :=
  positionTranslate (PositionedRotationMachine.block q)

def dispatchTarget : MoveParserMachine.Result → Label Λ
  | .failure => resultLabel parseFailure
  | .success d => positionLabel (.seek d)

/-- One paid finite activation; none of the seven physical stores is touched. -/
def dispatchBlock (r : MoveParserMachine.Result) : Statement Γ Λ R :=
  .load reset (.goto (fun _ => dispatchTarget r))

def program (caller : External Λ → Statement Γ Λ R) : Label Λ → Statement Γ Λ R
  | .inl q => moveBlock q
  | .inr (.inl r) => dispatchBlock r
  | .inr (.inr (.inl q)) => positionBlock q
  | .inr (.inr (.inr external)) => caller external

variable [DecidableEq K]

def step (caller : External Λ → Statement Γ Λ R) : Cfg Γ Λ R → Option (Cfg Γ Λ R) :=
  Turing.TM2.step (program caller)

def next (caller : External Λ → Statement Γ Λ R) (c : Option (Cfg Γ Λ R)) :
    Option (Cfg Γ Λ R) := c.bind (step caller)

variable (caller : External Λ → Statement Γ Λ R)

@[simp] theorem next_some (c : Cfg Γ Λ R) : next caller (some c) = step caller c := rfl
@[simp] theorem next_none : next caller none = none := rfl

theorem dispatch_step (r : MoveParserMachine.Result) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (dispatchLabel r)) regs D ctx) =
      some (cfg (some (dispatchTarget r)) (reset regs) D ctx) := rfl

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

omit [DecidableEq K] in
def toMoveCfg (c : Cfg Γ Λ R) : MoveCfg Γ Λ R :=
  moveView (c.l.map moveLabelEquiv.symm) (moveRegisterEquiv.symm c.var)
    (dataOfCfg c) (contextOfCfg c)

omit [DecidableEq K] in
def toPositionCfg (c : Cfg Γ Λ R) : PositionCfg Γ Λ R :=
  positionView (c.l.map positionLabelEquiv.symm) c.var (dataOfCfg c) (contextOfCfg c)

omit [DecidableEq K] in
theorem moveCfg_toMoveCfg (c : Cfg Γ Λ R) : moveCfg (toMoveCfg c) = c := by
  unfold toMoveCfg
  rw [moveCfg_view, Equiv.apply_symm_apply]
  have labelEq : (c.l.map moveLabelEquiv.symm).map moveLabelEquiv = c.l := by
    cases c.l <;> simp
  rw [labelEq]
  exact cfg_eta c

omit [DecidableEq K] in
theorem positionCfg_toPositionCfg (c : Cfg Γ Λ R) : positionCfg (toPositionCfg c) = c := by
  unfold toPositionCfg
  rw [positionCfg_view]
  have labelEq : (c.l.map positionLabelEquiv.symm).map positionLabelEquiv = c.l := by
    cases c.l <;> simp
  rw [labelEq]
  exact cfg_eta c

omit [DecidableEq K] in
theorem owned_moveCfg (c : MoveCfg Γ Λ R) (owned : MoveParserMachine.Owned c.l) :
    Owned (moveCfg c).l := by
  cases labelEq : c.l with
  | none => simp only [labelEq, MoveParserMachine.Owned] at owned
  | some label =>
      cases label with
      | inl q => change Owned (c.l.map moveLabelEquiv); rw [labelEq]; trivial
      | inr external => simp only [labelEq, MoveParserMachine.Owned] at owned

omit [DecidableEq K] in
theorem owned_positionCfg (c : PositionCfg Γ Λ R) (owned : PositionedRotationMachine.Owned c.l) :
    Owned (positionCfg c).l := by
  cases labelEq : c.l with
  | none => simp only [labelEq, PositionedRotationMachine.Owned] at owned
  | some label =>
      cases label with
      | inl q => change Owned (c.l.map positionLabelEquiv); rw [labelEq]; trivial
      | inr external => simp only [labelEq, PositionedRotationMachine.Owned] at owned

theorem move_step_transport
    (localCaller : MoveParserMachine.External (MoveCallerLabel Λ) → MoveStatement Γ Λ R)
    (c : MoveCfg Γ Λ R) (owned : MoveParserMachine.Owned c.l) :
    step caller (moveCfg c) = (MoveParserMachine.step localCaller c).map moveCfg := by
  exact FrontEndMachine.Transport.step_owned moveStackEquiv moveSymbolEquiv moveRegisterEquiv
    moveLabelEquiv (MoveParserMachine.program localCaller) (program caller) MoveParserMachine.Owned
    (by intro label h; cases label with
        | inl q => rfl
        | inr external => cases h) c owned

theorem position_step_transport
    (localCaller : PositionedRotationMachine.External (PositionCallerLabel Λ) → PositionStatement Γ Λ R)
    (c : PositionCfg Γ Λ R) (owned : PositionedRotationMachine.Owned c.l) :
    step caller (positionCfg c) = (PositionedRotationMachine.step localCaller c).map positionCfg := by
  exact FrontEndMachine.Transport.step_owned positionStackEquiv positionSymbolEquiv (Equiv.refl _)
    positionLabelEquiv (PositionedRotationMachine.program localCaller) (program caller)
    PositionedRotationMachine.Owned
    (by intro label h; cases label with
        | inl q => rfl
        | inr external => cases h) c owned

theorem move_prefix_transport
    (localCaller : MoveParserMachine.External (MoveCallerLabel Λ) → MoveStatement Γ Λ R)
    (n : Nat) (start : MoveCfg Γ Λ R)
    (earlier : ∀ j, j < n → ∃ reached,
      (MoveParserMachine.next localCaller)^[j] (some start) = some reached ∧
        MoveParserMachine.Owned reached.l) :
    (next caller)^[n] (some (moveCfg start)) =
      ((MoveParserMachine.next localCaller)^[n] (some start)).map moveCfg := by
  exact FrontEndMachine.Transport.iterate_owned moveStackEquiv moveSymbolEquiv moveRegisterEquiv
    moveLabelEquiv (MoveParserMachine.program localCaller) (program caller) MoveParserMachine.Owned
    (by intro label h; cases label with
        | inl q => rfl
        | inr external => cases h) n start earlier

theorem position_prefix_transport
    (localCaller : PositionedRotationMachine.External (PositionCallerLabel Λ) → PositionStatement Γ Λ R)
    (n : Nat) (start : PositionCfg Γ Λ R)
    (earlier : ∀ j, j < n → ∃ reached,
      (PositionedRotationMachine.next localCaller)^[j] (some start) = some reached ∧
        PositionedRotationMachine.Owned reached.l) :
    (next caller)^[n] (some (positionCfg start)) =
      ((PositionedRotationMachine.next localCaller)^[n] (some start)).map positionCfg := by
  exact FrontEndMachine.Transport.iterate_owned positionStackEquiv positionSymbolEquiv (Equiv.refl _)
    positionLabelEquiv (PositionedRotationMachine.program localCaller) (program caller)
    PositionedRotationMachine.Owned
    (by intro label h; cases label with
        | inl q => rfl
        | inr external => cases h) n start earlier

/-- Every partial Position segment transports literally, including scans and restores. -/
theorem position_localRun_transport
    (localCaller : PositionedRotationMachine.External (PositionCallerLabel Λ) → PositionStatement Γ Λ R)
    {n : Nat} {a b : PositionCfg Γ Λ R} (run : PositionedRotationMachine.LocalRun localCaller n a b) :
    LocalRun caller n (positionCfg a) (positionCfg b) := by
  induction run with
  | refl => exact .refl _
  | @cons n before middle after head tail ih =>
      refine .cons ⟨owned_positionCfg before head.1, ?_⟩ ih
      rw [position_step_transport caller localCaller before head.1, head.2]
      rfl

theorem move_phase_transport (q : MoveParserMachine.Phase) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (MoveParserMachine.phaseSteps q D.certificate D.moveReverse)
      (cfg (some (moveLabel q)) regs D ctx)
      (moveCfg (MoveParserMachine.phaseResult q (moveRegisterEquiv.symm regs)
        D.certificate D.moveReverse D.path (moveContext D ctx))) := by
  let localCaller : MoveParserMachine.External (MoveCallerLabel Λ) → MoveStatement Γ Λ R :=
    fun _ => .halt
  let start : MoveCfg Γ Λ R := moveView (some (MoveParserMachine.phaseLabel q)) (moveRegisterEquiv.symm regs) D ctx
  have startEq : moveCfg start = cfg (some (moveLabel q)) regs D ctx := by
    rw [moveCfg_view]
    simp only [Option.map_some, moveLabelEquiv_phase, Equiv.apply_symm_apply]
  have strictPrefix := (MoveParserMachine.phase_first_return localCaller q D.certificate
    D.moveReverse D.path (moveRegisterEquiv.symm regs) (moveContext D ctx)).2
  apply LocalRun.of_iterate caller
  · rw [← startEq, move_prefix_transport caller localCaller _ start strictPrefix]
    have whole : (MoveParserMachine.next localCaller)^[MoveParserMachine.phaseSteps q D.certificate D.moveReverse]
        (some start) = some (MoveParserMachine.phaseResult q (moveRegisterEquiv.symm regs)
          D.certificate D.moveReverse D.path (moveContext D ctx)) :=
      MoveParserMachine.phase_iterate localCaller q D.certificate D.moveReverse D.path
        (moveRegisterEquiv.symm regs) (moveContext D ctx)
    rw [whole]
    rfl
  · intro j strict
    obtain ⟨reached, executed, owned⟩ := strictPrefix j strict
    refine ⟨moveCfg reached, ?_, owned_moveCfg reached owned⟩
    change (MoveParserMachine.next localCaller)^[j] (some start) = some reached at executed
    rw [← startEq, move_prefix_transport caller localCaller j start
      (fun k bound => strictPrefix k (by omega)), executed]
    rfl

theorem position_phase_transport (q : PositionedRotationMachine.Phase) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (PositionedRotationMachine.phaseSteps q (positionData D))
      (cfg (some (positionLabel q)) regs D ctx)
      (positionCfg (PositionedRotationMachine.phaseResult q regs (positionData D)
        (positionContext D ctx))) := by
  let localCaller : PositionedRotationMachine.External (PositionCallerLabel Λ) → PositionStatement Γ Λ R :=
    fun _ => .halt
  have run := position_localRun_transport caller localCaller
    (PositionedRotationMachine.phase_localRun localCaller q (positionData D) regs (positionContext D ctx))
  change LocalRun caller _ (positionCfg (positionView _ regs D ctx)) _ at run
  rw [positionCfg_view] at run
  simpa only [Option.map_some, positionLabelEquiv_phase] using run

theorem dispatch_localRun (r : MoveParserMachine.Result) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    LocalRun caller 1 (cfg (some (dispatchLabel r)) regs D ctx)
      (cfg (some (dispatchTarget r)) (reset regs) D ctx) :=
  LocalRun.single caller ⟨True.intro, dispatch_step caller r D regs ctx⟩

structure MoveFinish where
  result : MoveParserMachine.Result
  data : LocalData
  deriving DecidableEq

/-- Proof-side complete parser endpoint, retaining all protected tree stores. -/
def moveScanFinish (d : RotationDirection) (D : LocalData) :
    Option (List Branch × Word) → MoveFinish
  | none => ⟨.failure, { D with
      certificate := directionTag d :: (pathTags D.moveReverse.reverse ++ D.certificate)
      moveReverse := [] }⟩
  | some (p, rest) => ⟨.success d, { D with
      certificate := rest
      moveReverse := []
      path := D.moveReverse.reverse ++ p ++ D.path }⟩

def moveFinish (q : MoveParserMachine.Phase) (D : LocalData) : MoveFinish :=
  match q with
  | .start => match D.certificate with
      | [] => ⟨.failure, D⟩
      | tag :: raw =>
          if tag = rotateLeftTag then
            moveScanFinish .left { D with certificate := raw } (parsePathRun raw).1
          else if tag = rotateRightTag then
            moveScanFinish .right { D with certificate := raw } (parsePathRun raw).1
          else ⟨.failure, D⟩
  | .scan d => moveScanFinish d D (parsePathRun D.certificate).1
  | .emit d => ⟨.success d, { D with moveReverse := [], path := D.moveReverse.reverse ++ D.path }⟩
  | .undo d => ⟨.failure, { D with
      certificate := directionTag d :: (pathTags D.moveReverse.reverse ++ D.certificate)
      moveReverse := [] }⟩

omit [DecidableEq K] in
theorem moveScanFinish_transport (d : RotationDirection) (D : LocalData)
    (regs : MoveParserMachine.Registers (MoveCallerRegister R)) (ctx : ∀ k, List (Γ k))
    (parsed : Option (List Branch × Word)) :
    moveCfg (Λ := Λ) (MoveParserMachine.scanResult d regs D.certificate D.moveReverse D.path
      (moveContext D ctx) parsed) =
      cfg (some (dispatchLabel (moveScanFinish d D parsed).result))
        (resetMove (moveRegisterEquiv regs)) (moveScanFinish d D parsed).data ctx := by
  cases parsed with
  | none =>
      change moveCfg (moveView (some (MoveParserMachine.resultLabel .failure))
        (MoveParserMachine.reset regs) (moveScanFinish d D none).data ctx) = _
      rw [moveCfg_view]
      rfl
  | some pair =>
      rcases pair with ⟨p, rest⟩
      change moveCfg (moveView (some (MoveParserMachine.resultLabel (.success d)))
        (MoveParserMachine.reset regs) (moveScanFinish d D (some (p, rest))).data ctx) = _
      rw [moveCfg_view]
      rfl

omit [DecidableEq K] in
theorem moveFinish_transport (q : MoveParserMachine.Phase) (D : LocalData)
    (regs : MoveParserMachine.Registers (MoveCallerRegister R)) (ctx : ∀ k, List (Γ k)) :
    moveCfg (Λ := Λ) (MoveParserMachine.phaseResult q regs D.certificate D.moveReverse D.path
      (moveContext D ctx)) =
      cfg (some (dispatchLabel (moveFinish q D).result))
        (resetMove (moveRegisterEquiv regs)) (moveFinish q D).data ctx := by
  cases q with
  | start =>
      rcases D with ⟨raw, rev, path, source, saved, scratch, pending⟩
      cases raw with
      | nil =>
          change moveCfg (moveView (some (MoveParserMachine.resultLabel .failure))
            (MoveParserMachine.reset regs) ⟨[], rev, path, source, saved, scratch, pending⟩ ctx) = _
          rw [moveCfg_view]
          rfl
      | cons tag raw =>
          by_cases left : tag = rotateLeftTag
          · simp only [MoveParserMachine.phaseResult, MoveParserMachine.startResult, moveFinish,
              left, ite_true]
            exact moveScanFinish_transport .left ⟨raw, rev, path, source, saved, scratch, pending⟩ regs ctx _
          · by_cases right : tag = rotateRightTag
            · simp only [MoveParserMachine.phaseResult, MoveParserMachine.startResult, moveFinish,
                right, ite_true]
              exact moveScanFinish_transport .right ⟨raw, rev, path, source, saved, scratch, pending⟩ regs ctx _
            · simp only [MoveParserMachine.phaseResult, MoveParserMachine.startResult, moveFinish,
                left, ite_false, right]
              change moveCfg (moveView (some (MoveParserMachine.resultLabel .failure))
                (MoveParserMachine.reset regs) ⟨tag :: raw, rev, path, source, saved, scratch, pending⟩ ctx) = _
              rw [moveCfg_view]
              rfl
  | scan d => exact moveScanFinish_transport d D regs ctx _
  | emit d =>
      change moveCfg (moveView (some (MoveParserMachine.resultLabel (.success d)))
        (MoveParserMachine.reset regs) (moveFinish (.emit d) D).data ctx) = _
      rw [moveCfg_view]
      rfl
  | undo d =>
      change moveCfg (moveView (some (MoveParserMachine.resultLabel .failure))
        (MoveParserMachine.reset regs) (moveFinish (.undo d) D).data ctx) = _
      rw [moveCfg_view]
      rfl

theorem move_phase_localRun (q : MoveParserMachine.Phase) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (MoveParserMachine.phaseSteps q D.certificate D.moveReverse)
      (cfg (some (moveLabel q)) regs D ctx)
      (cfg (some (dispatchLabel (moveFinish q D).result)) (resetMove regs)
        (moveFinish q D).data ctx) := by
  have run := move_phase_transport caller q D regs ctx
  rw [moveFinish_transport, Equiv.apply_symm_apply] at run
  exact run

structure Evaluation where
  result : FinalResult
  data : LocalData
  steps : Nat
  deriving DecidableEq

/-- Proof-side Position result with the complementary physical stores retained. -/
def evaluatePosition (q : PositionedRotationMachine.Phase) (D : LocalData) : Evaluation :=
  let actual := PositionedRotationMachine.evaluate (.inl q) (positionData D)
  ⟨.inr actual.result, setPositionData D actual.data, actual.steps⟩

/-- The extra activation is the literal dispatch block, not a free handoff. -/
def evaluateDispatch (r : MoveParserMachine.Result) (D : LocalData) : Evaluation :=
  match r with
  | .failure => ⟨parseFailure, D, 1⟩
  | .success d =>
      let tail := evaluatePosition (.seek d) D
      ⟨tail.result, tail.data, 1 + tail.steps⟩

/-- A finite proof-side composition of the actual total component endpoints. -/
def evaluate (q : Phase) (D : LocalData) : Evaluation :=
  match q with
  | .inl q =>
      let parsed := moveFinish q D
      let tail := evaluateDispatch parsed.result parsed.data
      ⟨tail.result, tail.data,
        MoveParserMachine.phaseSteps q D.certificate D.moveReverse + tail.steps⟩
  | .inr (.inl r) => evaluateDispatch r D
  | .inr (.inr q) => evaluatePosition q D

def phaseSteps (q : Phase) (D : LocalData) : Nat := (evaluate q D).steps

def phaseResult (q : Phase) (regs : Registers R) (D : LocalData)
    (ctx : ∀ k, List (Γ k)) : Cfg Γ Λ R :=
  cfg (some (resultLabel (evaluate q D).result)) (reset regs) (evaluate q D).data ctx

omit [DecidableEq K] in
@[simp] theorem phaseResult_reset (q : Phase) (regs : Registers R) (D : LocalData)
    (ctx : ∀ k, List (Γ k)) : phaseResult q (reset regs) D ctx = phaseResult (Λ := Λ) q regs D ctx := rfl

omit [DecidableEq K] in
@[simp] theorem phaseResult_resetMove (q : Phase) (regs : Registers R) (D : LocalData)
    (ctx : ∀ k, List (Γ k)) : phaseResult q (resetMove regs) D ctx = phaseResult (Λ := Λ) q regs D ctx := rfl

omit [DecidableEq K] in
theorem positionFinish_transport (q : PositionedRotationMachine.Phase) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    positionCfg (Λ := Λ) (PositionedRotationMachine.phaseResult q regs (positionData D) (positionContext D ctx)) =
      phaseResult (positionPhase q) regs D ctx := by
  change positionCfg (positionView
    (some (PositionedRotationMachine.resultLabel
      (PositionedRotationMachine.evaluate (.inl q) (positionData D)).result))
    (reset regs) (setPositionData D
      (PositionedRotationMachine.evaluate (.inl q) (positionData D)).data) ctx) = _
  rw [positionCfg_view]
  rfl

theorem position_phase_localRun (q : PositionedRotationMachine.Phase) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (PositionedRotationMachine.phaseSteps q (positionData D))
      (cfg (some (positionLabel q)) regs D ctx)
      (phaseResult (positionPhase q) regs D ctx) := by
  rw [← positionFinish_transport]
  exact position_phase_transport caller q D regs ctx

theorem dispatch_phase_localRun (r : MoveParserMachine.Result) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (phaseSteps (dispatchPhase r) D)
      (cfg (some (dispatchLabel r)) regs D ctx)
      (phaseResult (dispatchPhase r) regs D ctx) := by
  cases r with
  | failure => exact dispatch_localRun caller .failure D regs ctx
  | success d =>
      have run := LocalRun.trans caller (dispatch_localRun caller (.success d) D regs ctx)
        (position_phase_localRun caller (.seek d) D (reset regs) ctx)
      simpa only [phaseSteps, phaseResult, evaluate, evaluateDispatch, evaluatePosition,
        dispatchPhase, positionPhase, PositionedRotationMachine.phaseSteps, reset_reset] using run

theorem phase_localRun (q : Phase) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (phaseSteps q D) (cfg (some (phaseLabel q)) regs D ctx)
      (phaseResult q regs D ctx) := by
  cases q with
  | inl q =>
      have run := LocalRun.trans caller (move_phase_localRun caller q D regs ctx)
        (dispatch_phase_localRun caller (moveFinish q D).result (moveFinish q D).data (resetMove regs) ctx)
      simpa only [phaseSteps, phaseResult, phaseLabel, evaluate, dispatchPhase,
        reset_resetMove] using run
  | inr q =>
      cases q with
      | inl r => exact dispatch_phase_localRun caller r D regs ctx
      | inr q => exact position_phase_localRun caller q D regs ctx

theorem phase_iterate (q : Phase) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    (next caller)^[phaseSteps q D] (some (cfg (some (phaseLabel q)) regs D ctx)) =
      some (phaseResult q regs D ctx) :=
  LocalRun.iterate caller (phase_localRun caller q D regs ctx)

omit [DecidableEq K] in
theorem phaseSteps_pos (q : Phase) (D : LocalData) : 0 < phaseSteps q D := by
  have dispatchPositive (r : MoveParserMachine.Result) (D : LocalData) :
      0 < (evaluateDispatch r D).steps := by
    cases r <;> simp only [evaluateDispatch] <;> omega
  cases q with
  | inl q =>
      have positive := dispatchPositive (moveFinish q D).result (moveFinish q D).data
      change 0 < MoveParserMachine.phaseSteps q D.certificate D.moveReverse +
        (evaluateDispatch (moveFinish q D).result (moveFinish q D).data).steps
      omega
  | inr q =>
      cases q with
      | inl r => exact dispatchPositive r D
      | inr q => exact PositionedRotationMachine.phaseSteps_pos q (positionData D)

omit [DecidableEq K] in
theorem phaseResult_not_owned (q : Phase) (regs : Registers R) (D : LocalData)
    (ctx : ∀ k, List (Γ k)) : ¬ Owned (phaseResult (Λ := Λ) q regs D ctx).l :=
  not_owned_result _

theorem phase_first_return (q : Phase) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    ¬ Owned (phaseResult (Λ := Λ) q regs D ctx).l ∧
      ∀ n, n < phaseSteps q D → ∃ reached,
        (next caller)^[n] (some (cfg (some (phaseLabel q)) regs D ctx)) = some reached ∧ Owned reached.l :=
  ⟨phaseResult_not_owned q regs D ctx, LocalRun.owned_prefix caller (phase_localRun caller q D regs ctx)⟩

def remainingSteps (c : Cfg Γ Λ R) : Nat :=
  match c.l with
  | some (.inl q) => phaseSteps (movePhase q) (dataOfCfg c)
  | some (.inr (.inl r)) => phaseSteps (dispatchPhase r) (dataOfCfg c)
  | some (.inr (.inr (.inl q))) => phaseSteps (positionPhase q) (dataOfCfg c)
  | _ => 0

def finalCfg (c : Cfg Γ Λ R) : Cfg Γ Λ R :=
  match c.l with
  | some (.inl q) => phaseResult (movePhase q) c.var (dataOfCfg c) (contextOfCfg c)
  | some (.inr (.inl r)) => phaseResult (dispatchPhase r) c.var (dataOfCfg c) (contextOfCfg c)
  | some (.inr (.inr (.inl q))) => phaseResult (positionPhase q) c.var (dataOfCfg c) (contextOfCfg c)
  | _ => c

omit [DecidableEq K] in
@[simp] theorem remainingSteps_phase_cfg (q : Phase) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    remainingSteps (cfg (some (phaseLabel (Λ := Λ) q)) regs D ctx) = phaseSteps q D := by
  cases D
  cases q with
  | inl q => rfl
  | inr q => cases q <;> rfl

omit [DecidableEq K] in
@[simp] theorem finalCfg_phase_cfg (q : Phase) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    finalCfg (cfg (some (phaseLabel (Λ := Λ) q)) regs D ctx) = phaseResult q regs D ctx := by
  cases D
  cases q with
  | inl q => rfl
  | inr q => cases q <;> rfl

omit [DecidableEq K] in
theorem remainingSteps_pos_iff (c : Cfg Γ Λ R) : 0 < remainingSteps c ↔ Owned c.l := by
  cases labelEq : c.l with
  | none => simp only [remainingSteps, Owned, labelEq, Nat.lt_irrefl]
  | some label =>
      rcases label with q | (r | (q | external))
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
      rcases label with q | (r | (q | external))
      · refine ⟨movePhase q, c.var, dataOfCfg c, contextOfCfg c, ?_⟩
        simpa only [labelEq, phaseLabel, movePhase, moveLabel] using (cfg_eta c).symm
      · refine ⟨dispatchPhase r, c.var, dataOfCfg c, contextOfCfg c, ?_⟩
        simpa only [labelEq, phaseLabel, dispatchPhase, dispatchLabel] using (cfg_eta c).symm
      · refine ⟨positionPhase q, c.var, dataOfCfg c, contextOfCfg c, ?_⟩
        simpa only [labelEq, phaseLabel, positionPhase, positionLabel] using (cfg_eta c).symm
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

theorem LocalRun.finalCfg {n : Nat} {a b : Cfg Γ Λ R} (run : LocalRun caller n a b) :
    finalCfg a = finalCfg b := by
  induction run with
  | refl => rfl
  | cons head tail ih => exact (finalCfg_step caller head).trans ih

theorem LocalRun.phaseEndpoint {q : Phase} {D E : LocalData} {regs outRegs : Registers R}
    {ctx outCtx : ∀ k, List (Γ k)} {n : Nat} {r : FinalResult}
    (run : LocalRun caller n (cfg (some (phaseLabel q)) regs D ctx)
      (cfg (some (resultLabel r)) outRegs E outCtx)) :
    phaseSteps q D = n ∧
      phaseResult (Λ := Λ) q regs D ctx = cfg (some (resultLabel r)) outRegs E outCtx := by
  exact LocalRun.first_unique caller (phase_localRun caller q D regs ctx) run
    (phaseResult_not_owned q regs D ctx) (not_owned_result r)

theorem first_return_unique (q : Phase) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (n : Nat) (reached : Cfg Γ Λ R)
    (executed : (next caller)^[n] (some (cfg (some (phaseLabel q)) regs D ctx)) = some reached)
    (returned : ¬ Owned reached.l)
    (earlier : ∀ j, j < n → ∃ prior,
      (next caller)^[j] (some (cfg (some (phaseLabel q)) regs D ctx)) = some prior ∧ Owned prior.l) :
    n = phaseSteps q D ∧ reached = phaseResult q regs D ctx := by
  exact LocalRun.first_unique caller (LocalRun.of_iterate caller executed earlier)
    (phase_localRun caller q D regs ctx) returned (phaseResult_not_owned q regs D ctx)

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

theorem step_caller_independent (other : External Λ → Statement Γ Λ R)
    (c : Cfg Γ Λ R) (owned : Owned c.l) : step caller c = step other c := by
  obtain ⟨q, regs, D, ctx, rfl⟩ := owned_cases c owned
  cases q with
  | inl q => rfl
  | inr q => cases q <;> rfl

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
  · exact agrees (movePhase q)
  · exact agrees (dispatchPhase r)
  · exact agrees (positionPhase q)
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

omit [DecidableEq K] in
theorem moveCfg_context (c : MoveCfg Γ Λ R) (k : K) :
    (moveCfg c).stk (.inr k) = c.stk (.inr (.inr k)) := by
  change FrontEndMachine.Transport.stackEquiv moveStackEquiv (moveSymbolEquiv (Γ := Γ))
    c.stk (moveStackEquiv (.inr (.inr k))) = _
  rw [FrontEndMachine.Transport.stackEquiv_apply]
  change List.map id _ = _
  exact List.map_id _

omit [DecidableEq K] in
theorem positionCfg_context (c : PositionCfg Γ Λ R) (k : K) :
    (positionCfg c).stk (.inr k) = c.stk (.inr (.inr k)) := by
  change FrontEndMachine.Transport.stackEquiv positionStackEquiv (positionSymbolEquiv (Γ := Γ))
    c.stk (positionStackEquiv (.inr (.inr k))) = _
  rw [FrontEndMachine.Transport.stackEquiv_apply]
  change List.map id _ = _
  exact List.map_id _

theorem local_step_frame {before after : Cfg Γ Λ R} (transition : LocalStep caller before after) :
    after.var.2 = before.var.2 ∧ ∀ k, after.stk (.inr k) = before.stk (.inr k) := by
  obtain ⟨q, regs, D, ctx, rfl⟩ := owned_cases before transition.1
  cases q with
  | inl q =>
      let localCaller : MoveParserMachine.External (MoveCallerLabel Λ) → MoveStatement Γ Λ R :=
        fun _ => .halt
      let start : MoveCfg Γ Λ R := moveView (some (MoveParserMachine.phaseLabel q)) (moveRegisterEquiv.symm regs) D ctx
      have startEq : moveCfg start = cfg (some (moveLabel q)) regs D ctx := by
        rw [moveCfg_view]
        simp only [Option.map_some, moveLabelEquiv_phase, Equiv.apply_symm_apply]
      obtain ⟨middle, localStep, _⟩ := MoveParserMachine.local_progress localCaller start
        ((MoveParserMachine.remainingSteps_pos_iff start).mpr True.intro)
      have moved := move_step_transport caller localCaller start True.intro
      rw [localStep, Option.map_some, startEq] at moved
      have same : after = moveCfg middle := Option.some.inj (transition.2.symm.trans moved)
      obtain ⟨_, canonical, frame, _⟩ :=
        MoveParserMachine.local_step_data localCaller (before := start) ⟨True.intro, localStep⟩
      rw [same]
      refine ⟨?_, ?_⟩
      · change (moveRegisterEquiv middle.var).2 = regs.2
        rw [canonical]
        rfl
      · intro k
        rw [moveCfg_context]
        exact frame (.inr k)
  | inr q => cases q with
    | inl r =>
        have same : after = cfg (some (dispatchTarget r)) (reset regs) D ctx :=
          Option.some.inj (transition.2.symm.trans (dispatch_step caller r D regs ctx))
        rw [same]
        exact ⟨rfl, fun _ => rfl⟩
    | inr q =>
        let localCaller : PositionedRotationMachine.External (PositionCallerLabel Λ) →
            PositionStatement Γ Λ R := fun _ => .halt
        let start : PositionCfg Γ Λ R := positionView (some (PositionedRotationMachine.phaseLabel q)) regs D ctx
        have startEq : positionCfg start = cfg (some (positionLabel q)) regs D ctx := by
          rw [positionCfg_view]
          rfl
        obtain ⟨middle, localStep, _⟩ := PositionedRotationMachine.local_progress localCaller start
          ((PositionedRotationMachine.remainingSteps_pos_iff start).mpr True.intro)
        have moved := position_step_transport caller localCaller start True.intro
        rw [localStep, Option.map_some, startEq] at moved
        have same : after = positionCfg middle := Option.some.inj (transition.2.symm.trans moved)
        obtain ⟨_, canonical, frame⟩ :=
          PositionedRotationMachine.local_step_data localCaller (before := start) ⟨True.intro, localStep⟩
        rw [same]
        refine ⟨?_, ?_⟩
        · change middle.var.2 = regs.2
          rw [canonical]
          rfl
        · intro k
          rw [positionCfg_context]
          exact frame (.inr k)

theorem local_reaches_frame {start reached : Cfg Γ Λ R}
    (path : Relation.ReflTransGen (LocalStep caller) start reached) :
    reached.var.2 = start.var.2 ∧ ∀ k, reached.stk (.inr k) = start.stk (.inr k) := by
  induction path with
  | refl => exact ⟨rfl, fun _ => rfl⟩
  | @tail before after _ transition ih =>
      obtain ⟨registers, frame⟩ := local_step_frame caller transition
      exact ⟨registers.trans ih.1, fun k => (frame k).trans (ih.2 k)⟩

theorem prefix_frame (start reached : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start)
    (executed : (next caller)^[n] (some start) = some reached) :
    reached.var.2 = start.var.2 ∧ ∀ k, reached.stk (.inr k) = start.stk (.inr k) := by
  obtain ⟨actual, run, _, path, _⟩ := owned_prefix caller start n bound
  have same : actual = reached := Option.some.inj (run.symm.trans executed)
  subst actual
  exact local_reaches_frame caller path

/-- The paid dispatch is the precise boundary between Tag-only and full reset. -/
def registersAt (start : Cfg Γ Λ R) (n : Nat) : Registers R :=
  if n = 0 then start.var else
    match start.l with
    | some (.inl q) =>
        if n ≤ MoveParserMachine.phaseSteps q (dataOfCfg start).certificate (dataOfCfg start).moveReverse
        then resetMove start.var else reset start.var
    | _ => reset start.var

theorem position_prefix_reset (q : PositionedRotationMachine.Phase) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) (n : Nat) (reached : Cfg Γ Λ R)
    (bound : n ≤ PositionedRotationMachine.phaseSteps q (positionData D))
    (executed : (next caller)^[n] (some (cfg (some (positionLabel q)) regs D ctx)) = some reached) :
    reached.var = if n = 0 then regs else reset regs := by
  let localCaller : PositionedRotationMachine.External (PositionCallerLabel Λ) →
      PositionStatement Γ Λ R := fun _ => .halt
  let start : PositionCfg Γ Λ R := positionView (some (PositionedRotationMachine.phaseLabel q)) regs D ctx
  have startEq : positionCfg start = cfg (some (positionLabel q)) regs D ctx := by
    rw [positionCfg_view]
    rfl
  have strictPrefix := (PositionedRotationMachine.phase_first_return localCaller q
    (positionData D) regs (positionContext D ctx)).2.2
  obtain ⟨localReached, localRun, _, _, _⟩ :=
    PositionedRotationMachine.owned_prefix localCaller start n bound
  have actual := position_prefix_transport caller localCaller n start
    (fun j strict => strictPrefix j (by omega))
  rw [localRun, Option.map_some, startEq] at actual
  have same : reached = positionCfg localReached := Option.some.inj (executed.symm.trans actual)
  rw [same]
  exact PositionedRotationMachine.prefix_reset localCaller start localReached n bound localRun

theorem move_prefix_reset (q : MoveParserMachine.Phase) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) (n : Nat) (reached : Cfg Γ Λ R)
    (bound : n ≤ MoveParserMachine.phaseSteps q D.certificate D.moveReverse)
    (executed : (next caller)^[n] (some (cfg (some (moveLabel q)) regs D ctx)) = some reached) :
    reached.var = if n = 0 then regs else resetMove regs := by
  let localCaller : MoveParserMachine.External (MoveCallerLabel Λ) → MoveStatement Γ Λ R := fun _ => .halt
  let start : MoveCfg Γ Λ R := moveView (some (MoveParserMachine.phaseLabel q)) (moveRegisterEquiv.symm regs) D ctx
  have startEq : moveCfg start = cfg (some (moveLabel q)) regs D ctx := by
    rw [moveCfg_view]
    simp only [Option.map_some, moveLabelEquiv_phase, Equiv.apply_symm_apply]
  have strictPrefix := (MoveParserMachine.phase_first_return localCaller q D.certificate
    D.moveReverse D.path (moveRegisterEquiv.symm regs) (moveContext D ctx)).2
  obtain ⟨localReached, localRun, _, _, _, _⟩ :=
    MoveParserMachine.owned_prefix localCaller start n bound
  have actual := move_prefix_transport caller localCaller n start
    (fun j strict => strictPrefix j (by omega))
  rw [localRun, Option.map_some, startEq] at actual
  have same : reached = moveCfg localReached := Option.some.inj (executed.symm.trans actual)
  have canonical := (MoveParserMachine.prefix_preserves localCaller start localReached n bound localRun).1
  rw [same]
  change moveRegisterEquiv localReached.var = _
  rw [canonical]
  change moveRegisterEquiv (if n = 0 then moveRegisterEquiv.symm regs
    else MoveParserMachine.reset (moveRegisterEquiv.symm regs)) = _
  by_cases zero : n = 0
  · simp only [zero, ite_true, Equiv.apply_symm_apply]
  · simp only [zero, ite_false, moveRegisterEquiv_reset, Equiv.apply_symm_apply]

theorem dispatch_prefix_reset (r : MoveParserMachine.Result) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) (n : Nat) (reached : Cfg Γ Λ R)
    (bound : n ≤ phaseSteps (dispatchPhase r) D)
    (executed : (next caller)^[n] (some (cfg (some (dispatchLabel r)) regs D ctx)) = some reached) :
    reached.var = if n = 0 then regs else reset regs := by
  cases n with
  | zero =>
      have same : cfg (some (dispatchLabel r)) regs D ctx = reached := Option.some.inj executed
      rw [← same]
      rfl
  | succ n =>
      rw [iterate_step caller n _ _ (dispatch_step caller r D regs ctx)] at executed
      simp only [Nat.succ_ne_zero, ite_false]
      cases r with
      | failure =>
          change n + 1 ≤ 1 at bound
          have zero : n = 0 := by omega
          subst n
          exact congrArg Turing.TM2.Cfg.var (Option.some.inj executed).symm
      | success d =>
          have small : n ≤ PositionedRotationMachine.phaseSteps (.seek d) (positionData D) := by
            change n + 1 ≤ 1 + PositionedRotationMachine.phaseSteps (.seek d) (positionData D) at bound
            omega
          simpa only [reset_reset, ite_self] using
            position_prefix_reset caller (.seek d) D (reset regs) ctx n reached small executed

theorem prefix_reset (start reached : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start)
    (executed : (next caller)^[n] (some start) = some reached) :
    reached.var = registersAt start n := by
  by_cases zero : n = 0
  · subst n
    have same : start = reached := Option.some.inj executed
    subst reached
    rfl
  · by_cases owned : Owned start.l
    · obtain ⟨q, regs, D, ctx, rfl⟩ := owned_cases start owned
      cases q with
      | inl q =>
          change reached.var = if n = 0 then regs else
            if n ≤ MoveParserMachine.phaseSteps q D.certificate D.moveReverse then resetMove regs else reset regs
          rw [ite_eq_right zero]
          by_cases early : n ≤ MoveParserMachine.phaseSteps q D.certificate D.moveReverse
          · rw [ite_eq_left early]
            simpa only [zero, ite_false] using move_prefix_reset caller q D regs ctx n reached early executed
          · rw [ite_eq_right early]
            let m := MoveParserMachine.phaseSteps q D.certificate D.moveReverse
            have afterMove := LocalRun.iterate caller (move_phase_localRun caller q D regs ctx)
            change (next caller)^[m] (some (cfg (some (phaseLabel (.inl q))) regs D ctx)) = _ at afterMove
            have count : m + (n - m) = n := by omega
            have suffix : (next caller)^[n - m]
                (some (cfg (some (dispatchLabel (moveFinish q D).result))
                  (resetMove regs) (moveFinish q D).data ctx)) = some reached := by
              rw [← count, Nat.add_comm m, Function.iterate_add_apply, afterMove] at executed
              exact executed
            have small : n - m ≤ phaseSteps (dispatchPhase (moveFinish q D).result)
                (moveFinish q D).data := by
              change n ≤ m + phaseSteps (dispatchPhase (moveFinish q D).result)
                (moveFinish q D).data at bound
              omega
            have canonical := dispatch_prefix_reset caller (moveFinish q D).result (moveFinish q D).data
              (resetMove regs) ctx (n - m) reached small suffix
            have positive : n - m ≠ 0 := by omega
            simpa only [positive, ite_false, reset_resetMove] using canonical
      | inr q => cases q with
        | inl r =>
            simpa only [registersAt, cfg, phaseLabel, dispatchLabel, zero, ite_false] using
              dispatch_prefix_reset caller r D regs ctx n reached bound executed
        | inr q =>
            simpa only [registersAt, cfg, phaseLabel, positionLabel, zero, ite_false] using
              position_prefix_reset caller q D regs ctx n reached bound executed
    · have empty := nonowned_remaining start owned
      omega

theorem owned_prefix_frame (start : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start) :
    ∃ reached, (next caller)^[n] (some start) = some reached ∧
      remainingSteps reached = remainingSteps start - n ∧
      Relation.ReflTransGen (LocalStep caller) start reached ∧
      (n < remainingSteps start ↔ Owned reached.l) ∧
      (n = 0 → reached = start) ∧ reached.var = registersAt start n ∧
      ∀ k, reached.stk (.inr k) = start.stk (.inr k) := by
  obtain ⟨reached, executed, rank, path, ownership⟩ := owned_prefix caller start n bound
  refine ⟨reached, executed, rank, path, ownership, ?_,
    prefix_reset caller start reached n bound executed, (prefix_frame caller start reached n bound executed).2⟩
  intro zero
  subst n
  exact (Option.some.inj executed).symm

omit [DecidableEq K] in
def positionControlLabel : PositionedRotationMachine.Control → Label Λ
  | .inl q => positionLabel q
  | .inr r => resultLabel (.inr r)

omit [DecidableEq K] in
theorem positionCfg_partial (label : Option (PositionedRotationMachine.Label (PositionCallerLabel Λ)))
    (regs : Registers R) (D : LocalData) (E : PositionedRotationMachine.LocalData)
    (ctx : ∀ k, List (Γ k)) :
    positionCfg (PositionedRotationMachine.cfg label regs E (positionContext D ctx)) =
      cfg (label.map positionLabelEquiv) regs (setPositionData D E) ctx := by
  change positionCfg (positionView label regs (setPositionData D E) ctx) = _
  exact positionCfg_view label regs (setPositionData D E) ctx

theorem position_advance_step (q : PositionedRotationMachine.Phase) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (positionLabel q)) regs D ctx) =
      some (cfg (some (positionControlLabel (PositionedRotationMachine.advance q (positionData D)).1))
        (reset regs) (setPositionData D (PositionedRotationMachine.advance q (positionData D)).2) ctx) := by
  let localCaller : PositionedRotationMachine.External (PositionCallerLabel Λ) →
      PositionStatement Γ Λ R := fun _ => .halt
  have actual := position_step_transport caller localCaller
    (positionView (some (PositionedRotationMachine.phaseLabel q)) regs D ctx) True.intro
  rw [positionCfg_view] at actual
  change step caller (cfg (some (positionLabel q)) regs D ctx) = _ at actual
  simp only [positionView] at actual
  rw [PositionedRotationMachine.advance_step, Option.map_some, positionCfg_partial] at actual
  convert actual using 1
  cases (PositionedRotationMachine.advance q (positionData D)).1 <;> rfl

omit [DecidableEq K] in
theorem moveCfg_label (c : MoveCfg Γ Λ R) : (moveCfg c).l = c.l := by
  change c.l.map moveLabelEquiv = c.l
  cases c.l <;> rfl

omit [DecidableEq K] in
theorem moveCfg_source (c : MoveCfg Γ Λ R) :
    (moveCfg c).stk (.inl .source) = c.stk (.inr (.inl .source)) := by
  change FrontEndMachine.Transport.stackEquiv moveStackEquiv (moveSymbolEquiv (Γ := Γ))
    c.stk (moveStackEquiv (.inr (.inl .source))) = _
  rw [FrontEndMachine.Transport.stackEquiv_apply]
  change List.map id _ = _
  exact List.map_id _

/-- Component states through its result boundary, excluding arbitrary later caller labels. -/
def MoveBoundary (label : Option (MoveParserMachine.Label (MoveCallerLabel Λ))) : Prop :=
  MoveParserMachine.Owned label ∨ ∃ r, label = some (MoveParserMachine.resultLabel r)

theorem move_step_boundary
    (localCaller : MoveParserMachine.External (MoveCallerLabel Λ) → MoveStatement Γ Λ R)
    (q : MoveParserMachine.Phase) (D : LocalData)
    (regs : MoveParserMachine.Registers (MoveCallerRegister R)) (ctx : ∀ k, List (Γ k))
    (after : MoveCfg Γ Λ R)
    (executed : MoveParserMachine.step localCaller
      (moveView (some (MoveParserMachine.phaseLabel q)) regs D ctx) = some after) :
    MoveBoundary after.l := by
  by_cases owned : MoveParserMachine.Owned after.l
  · exact .inl owned
  · have decreased := (MoveParserMachine.local_step_data localCaller
      (before := moveView (some (MoveParserMachine.phaseLabel q)) regs D ctx) ⟨True.intro, executed⟩).1
    have zero : MoveParserMachine.remainingSteps after = 0 := by
      have notPositive : ¬ 0 < MoveParserMachine.remainingSteps after :=
        fun h => owned ((MoveParserMachine.remainingSteps_pos_iff after).mp h)
      omega
    have one : MoveParserMachine.phaseSteps q D.certificate D.moveReverse = 1 := by
      change MoveParserMachine.phaseSteps q D.certificate D.moveReverse =
        MoveParserMachine.remainingSteps after + 1 at decreased
      omega
    have complete := MoveParserMachine.phase_iterate localCaller q D.certificate
      D.moveReverse D.path regs (moveContext D ctx)
    rw [one, Function.iterate_one] at complete
    change MoveParserMachine.step localCaller
      (moveView (some (MoveParserMachine.phaseLabel q)) regs D ctx) = _ at complete
    rw [executed] at complete
    have same : after = MoveParserMachine.phaseResult q regs D.certificate D.moveReverse D.path
        (moveContext D ctx) := Option.some.inj complete
    have labelEq := congrArg Turing.TM2.Cfg.l (moveFinish_transport (Λ := Λ) q D regs ctx)
    rw [moveCfg_label] at labelEq
    refine .inr ⟨(moveFinish q D).result, ?_⟩
    rw [same]
    exact labelEq

def localCells (D : LocalData) : Nat := D.certificate.length + D.moveReverse.length + D.path.length +
  D.source.length + D.saved.length + D.scratch.length + D.pending.length

def phaseDebt : Phase → Nat
  | .inl q => MoveParserMachine.phaseDebt q
  | .inr (.inl (.success _)) => 2
  | .inr (.inl .failure) => 0
  | .inr (.inr q) => PositionedRotationMachine.phaseDebt q

def phaseCredit : Phase → LocalData → Nat
  | .inl _, D | .inr (.inl _), D => D.source.length
  | .inr (.inr q), D => PositionedRotationMachine.phaseCredit q (positionData D)

def debt : Option (Label Λ) → Nat
  | some (.inl q) => phaseDebt (movePhase q)
  | some (.inr (.inl r)) => phaseDebt (dispatchPhase r)
  | some (.inr (.inr (.inl q))) => phaseDebt (positionPhase q)
  | _ => 0

def credit (c : Cfg Γ Λ R) : Nat :=
  match c.l with
  | some (.inl q) => phaseCredit (movePhase q) (dataOfCfg c)
  | some (.inr (.inl r)) => phaseCredit (dispatchPhase r) (dataOfCfg c)
  | some (.inr (.inr (.inl q))) => phaseCredit (positionPhase q) (dataOfCfg c)
  | _ => 0

section PhysicalSpace
variable [Fintype K]

def contextCells (ctx : ∀ k, List (Γ k)) : Nat := ∑ k, (ctx k).length

/-- A genuine sum over the seven local indices and every protected physical index. -/
def stackCells (c : Cfg Γ Λ R) : Nat := ∑ k : StackId K, (c.stk k).length

omit [DecidableEq K] in
theorem stackCells_eq_sum (c : Cfg Γ Λ R) :
    stackCells c = ∑ k : StackId K, (c.stk k).length := rfl

theorem localStack_sum (f : LocalStack → Nat) :
    ∑ k, f k = f .certificate + f .moveReverse + f .path + f .source +
      f .saved + f .scratch + f .pending := by
  change (∑ k ∈ ({.certificate, .moveReverse, .path, .source, .saved, .scratch, .pending} : Finset LocalStack), f k) = _
  simp [Nat.add_comm, Nat.add_left_comm]

omit [DecidableEq K] in
theorem stackCells_cfg (label : Option (Label Λ)) (regs : Registers R) (D : LocalData)
    (ctx : ∀ k, List (Γ k)) :
    stackCells (cfg label regs D ctx) = localCells D + contextCells ctx := by
  rw [stackCells, Fintype.sum_sum_type, localStack_sum]
  rfl

omit [DecidableEq K] in
theorem stackCells_moveCfg (c : MoveCfg Γ Λ R) :
    stackCells (moveCfg c) = MoveParserMachine.stackCells c := by
  rw [MoveParserMachine.stackCells_eq_sum]
  exact FrontEndMachine.Transport.stackCells moveStackEquiv moveSymbolEquiv c.stk

omit [DecidableEq K] in
theorem stackCells_positionCfg (c : PositionCfg Γ Λ R) :
    stackCells (positionCfg c) = PositionedRotationMachine.stackCells c :=
  FrontEndMachine.Transport.stackCells positionStackEquiv positionSymbolEquiv c.stk

omit [DecidableEq K] in
theorem moveContext_cells (D : LocalData) (ctx : ∀ k, List (Γ k)) :
    MoveParserMachine.contextCells (moveContext D ctx) =
      D.source.length + D.saved.length + D.scratch.length + D.pending.length + contextCells ctx := by
  have localSum (f : MoveProtected → Nat) :
      ∑ k, f k = f .source + f .saved + f .scratch + f .pending := by
    change (∑ k ∈ ({.source, .saved, .scratch, .pending} : Finset MoveProtected), f k) = _
    simp [Nat.add_comm, Nat.add_left_comm]
  rw [MoveParserMachine.contextCells, Fintype.sum_sum_type, localSum]
  rfl

omit [DecidableEq K] in
theorem positionContext_cells (D : LocalData) (ctx : ∀ k, List (Γ k)) :
    PositionedRotationMachine.contextCells (positionContext D ctx) =
      D.certificate.length + D.moveReverse.length + contextCells ctx := by
  have localSum (f : PositionProtected → Nat) : ∑ k, f k = f .certificate + f .moveReverse := by
    change (∑ k ∈ ({.certificate, .moveReverse} : Finset PositionProtected), f k) = _
    simp
  rw [PositionedRotationMachine.contextCells, Fintype.sum_sum_type, localSum]
  rfl

def potential (c : Cfg Γ Λ R) : Nat := stackCells c + debt c.l + credit c

omit [DecidableEq K] in
theorem potential_phase_cfg (q : Phase) (regs : Registers R) (D : LocalData)
    (ctx : ∀ k, List (Γ k)) :
    potential (cfg (some (phaseLabel (Λ := Λ) q)) regs D ctx) =
      localCells D + phaseDebt q + phaseCredit q D + contextCells ctx := by
  rw [potential, stackCells_cfg]
  cases D
  cases q with
  | inl q => simp only [phaseLabel, moveLabel, cfg, debt, credit, dataOfCfg, movePhase]; omega
  | inr q => cases q <;>
      simp only [phaseLabel, dispatchLabel, positionLabel, cfg, debt, credit, dataOfCfg,
        dispatchPhase, positionPhase] <;> omega

omit [DecidableEq K] in
theorem potential_result_cfg (r : FinalResult) (regs : Registers R) (D : LocalData)
    (ctx : ∀ k, List (Γ k)) :
    potential (cfg (some (resultLabel (Λ := Λ) r)) regs D ctx) = localCells D + contextCells ctx := by
  rw [potential, stackCells_cfg]
  rfl

omit [DecidableEq K] in
theorem potential_position_control_cfg (control : PositionedRotationMachine.Control)
    (regs : Registers R) (D : LocalData) (E : PositionedRotationMachine.LocalData)
    (ctx : ∀ k, List (Γ k)) :
    potential (cfg (some (positionControlLabel (Λ := Λ) control)) regs (setPositionData D E) ctx) =
      PositionedRotationMachine.localPotential control E + D.certificate.length + D.moveReverse.length +
        contextCells ctx := by
  cases control with
  | inl q =>
      change potential (cfg (some (phaseLabel (positionPhase q))) regs (setPositionData D E) ctx) = _
      rw [potential_phase_cfg]
      simp only [phaseDebt, positionPhase, phaseCredit, positionData_setPositionData]
      simp only [localCells, setPositionData, PositionedRotationMachine.localPotential,
        PositionedRotationMachine.localCells, PositionedRotationMachine.controlDebt,
        PositionedRotationMachine.controlCredit]
      omega
  | inr r =>
      rw [positionControlLabel, potential_result_cfg]
      simp only [localCells, setPositionData, PositionedRotationMachine.localPotential,
        PositionedRotationMachine.localCells, PositionedRotationMachine.controlDebt,
        PositionedRotationMachine.controlCredit]
      omega

omit [DecidableEq K] in
theorem potential_moveCfg (c : MoveCfg Γ Λ R) (boundary : MoveBoundary c.l) :
    potential (moveCfg c) = MoveParserMachine.potential c +
      MoveParserMachine.contextCells (fun k => c.stk (.inr k)) +
        (c.stk (.inr (.inl .source))).length := by
  have debtEq : debt (moveCfg c).l = MoveParserMachine.debt c.l := by
    rw [moveCfg_label]
    rcases boundary with owned | ⟨r, returned⟩
    · cases labelEq : c.l with
      | none => simp only [labelEq, MoveParserMachine.Owned] at owned
      | some label => cases label with
        | inl q => rfl
        | inr external => simp only [labelEq, MoveParserMachine.Owned] at owned
    · rw [returned]
      cases r <;> rfl
  have creditEq : credit (moveCfg c) = (c.stk (.inr (.inl .source))).length := by
    have sourceEq := congrArg List.length (moveCfg_source c)
    rcases boundary with owned | ⟨r, returned⟩
    · cases labelEq : c.l with
      | none => simp only [labelEq, MoveParserMachine.Owned] at owned
      | some label => cases label with
        | inl q =>
            unfold credit
            rw [moveCfg_label, labelEq]
            exact sourceEq
        | inr external => simp only [labelEq, MoveParserMachine.Owned] at owned
    · unfold credit
      rw [moveCfg_label, returned]
      exact sourceEq
  rw [potential, stackCells_moveCfg, debtEq, creditEq]
  unfold MoveParserMachine.stackCells MoveParserMachine.potential
  omega

theorem move_step_potential
    (localCaller : MoveParserMachine.External (MoveCallerLabel Λ) → MoveStatement Γ Λ R)
    (q : MoveParserMachine.Phase) (D : LocalData)
    (regs : MoveParserMachine.Registers (MoveCallerRegister R)) (ctx : ∀ k, List (Γ k))
    (after : MoveCfg Γ Λ R)
    (executed : MoveParserMachine.step localCaller
      (moveView (some (MoveParserMachine.phaseLabel q)) regs D ctx) = some after) :
    potential (moveCfg after) =
      potential (moveCfg (Λ := Λ) (moveView (some (MoveParserMachine.phaseLabel q)) regs D ctx)) := by
  obtain ⟨_, _, frame, mass⟩ := MoveParserMachine.local_step_data localCaller
      (before := moveView (some (MoveParserMachine.phaseLabel q)) regs D ctx) ⟨True.intro, executed⟩
  rw [potential_moveCfg after (move_step_boundary localCaller q D regs ctx after executed),
    potential_moveCfg (moveView (Λ := Λ) (some (MoveParserMachine.phaseLabel q)) regs D ctx)
      (.inl True.intro), mass, funext frame, frame (.inl .source)]

omit [DecidableEq K] in
theorem dispatch_success_potential (d : RotationDirection) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    potential (cfg (some (dispatchLabel (Λ := Λ) (.success d))) regs D ctx) =
      potential (cfg (some (positionLabel (Λ := Λ) (.seek d))) (reset regs) D ctx) + 2 := by
  change potential (cfg (some (phaseLabel (dispatchPhase (.success d)))) regs D ctx) =
    potential (cfg (some (phaseLabel (positionPhase (.seek d)))) (reset regs) D ctx) + 2
  rw [potential_phase_cfg, potential_phase_cfg]
  simp only [phaseDebt, dispatchPhase, positionPhase, phaseCredit, PositionedRotationMachine.phaseDebt,
    PositionedRotationMachine.phaseCredit, positionData]
  omega

omit [DecidableEq K] in
theorem dispatch_failure_potential (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    potential (cfg (some (dispatchLabel (Λ := Λ) .failure)) regs D ctx) =
      potential (cfg (some (resultLabel (Λ := Λ) parseFailure)) (reset regs) D ctx) + D.source.length := by
  change potential (cfg (some (phaseLabel (dispatchPhase .failure))) regs D ctx) = _
  rw [potential_phase_cfg, potential_result_cfg]
  simp only [phaseDebt, dispatchPhase, phaseCredit]
  omega

theorem local_step_potential_le {before after : Cfg Γ Λ R} (transition : LocalStep caller before after) :
    potential after ≤ potential before := by
  obtain ⟨q, regs, D, ctx, rfl⟩ := owned_cases before transition.1
  cases q with
  | inl q =>
      let localCaller : MoveParserMachine.External (MoveCallerLabel Λ) → MoveStatement Γ Λ R :=
        fun _ => .halt
      let start : MoveCfg Γ Λ R :=
        moveView (some (MoveParserMachine.phaseLabel q)) (moveRegisterEquiv.symm regs) D ctx
      have startEq : moveCfg start = cfg (some (moveLabel q)) regs D ctx := by
        rw [moveCfg_view]
        simp only [Option.map_some, moveLabelEquiv_phase, Equiv.apply_symm_apply]
      obtain ⟨middle, localStep, _⟩ := MoveParserMachine.local_progress localCaller start
        ((MoveParserMachine.remainingSteps_pos_iff start).mpr True.intro)
      have moved := move_step_transport caller localCaller start True.intro
      rw [localStep, Option.map_some, startEq] at moved
      have same : after = moveCfg middle := Option.some.inj (transition.2.symm.trans moved)
      have mass := move_step_potential localCaller q D (moveRegisterEquiv.symm regs) ctx middle localStep
      change potential (moveCfg middle) = potential (moveCfg start) at mass
      rw [startEq] at mass
      rw [same]
      exact Nat.le_of_eq mass
  | inr q => cases q with
    | inl r =>
        have same : after = cfg (some (dispatchTarget r)) (reset regs) D ctx :=
          Option.some.inj (transition.2.symm.trans (dispatch_step caller r D regs ctx))
        rw [same]
        cases r with
        | failure => have mass := dispatch_failure_potential (Λ := Λ) D regs ctx; exact Nat.le.intro mass.symm
        | success d => have mass := dispatch_success_potential (Λ := Λ) d D regs ctx; exact Nat.le.intro mass.symm
    | inr q =>
        have same := Option.some.inj ((position_advance_step caller q D regs ctx).symm.trans transition.2)
        subst after
        change potential (cfg (some (positionControlLabel
          (PositionedRotationMachine.advance q (positionData D)).1)) (reset regs)
            (setPositionData D (PositionedRotationMachine.advance q (positionData D)).2) ctx) ≤
          potential (cfg (some (positionControlLabel (.inl q))) regs D ctx)
        have beforeEq : potential (cfg (some (positionControlLabel (Λ := Λ) (.inl q))) regs D ctx) =
            PositionedRotationMachine.localPotential (.inl q) (positionData D) +
              D.certificate.length + D.moveReverse.length + contextCells ctx := by
          simpa only [setPositionData_positionData] using
            potential_position_control_cfg (Λ := Λ) (.inl q) regs D (positionData D) ctx
        rw [potential_position_control_cfg, beforeEq]
        exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right
          (PositionedRotationMachine.advance_mass q (positionData D)).2 D.certificate.length)
          D.moveReverse.length) (contextCells ctx)

theorem local_reaches_potential_le {start reached : Cfg Γ Λ R}
    (path : Relation.ReflTransGen (LocalStep caller) start reached) : potential reached ≤ potential start := by
  induction path with
  | refl => exact Nat.le_refl _
  | @tail before after _ transition ih => exact (local_step_potential_le caller transition).trans ih

omit [DecidableEq K] in
theorem stackCells_le_potential (c : Cfg Γ Λ R) : stackCells c ≤ potential c := by
  unfold potential
  omega

theorem prefix_potential_le (start : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start)
    (reached : Cfg Γ Λ R) (executed : (next caller)^[n] (some start) = some reached) :
    potential reached ≤ potential start := by
  obtain ⟨actual, run, _, path, _⟩ := owned_prefix caller start n bound
  have same : actual = reached := Option.some.inj (run.symm.trans executed)
  subst actual
  exact local_reaches_potential_le caller path

theorem prefix_stackCells_le_dirty (start : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start)
    (reached : Cfg Γ Λ R) (executed : (next caller)^[n] (some start) = some reached) :
    stackCells reached ≤ potential start :=
  (stackCells_le_potential reached).trans (prefix_potential_le caller start n bound reached executed)

/-- Every clause refers to the same actual inclusive-prefix configuration. -/
theorem owned_prefix_space (start : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start) :
    ∃ reached, (next caller)^[n] (some start) = some reached ∧
      remainingSteps reached = remainingSteps start - n ∧
      Relation.ReflTransGen (LocalStep caller) start reached ∧
      (n < remainingSteps start ↔ Owned reached.l) ∧
      (n = 0 → reached = start) ∧ reached.var = registersAt start n ∧
      (∀ k, reached.stk (.inr k) = start.stk (.inr k)) ∧
      stackCells reached ≤ potential reached ∧ potential reached ≤ potential start := by
  obtain ⟨reached, executed, rank, path, ownership, zero, registers, frame⟩ :=
    owned_prefix_frame caller start n bound
  exact ⟨reached, executed, rank, path, ownership, zero, registers, frame,
    stackCells_le_potential reached, local_reaches_potential_le caller path⟩

end PhysicalSpace

theorem dispatch_failure_step (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (dispatchLabel .failure)) regs D ctx) =
      some (cfg (some (resultLabel parseFailure)) (reset regs) D ctx) :=
  dispatch_step caller .failure D regs ctx

theorem dispatch_left_step (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (dispatchLabel (.success .left))) regs D ctx) =
      some (cfg (some (positionLabel (.seek .left))) (reset regs) D ctx) :=
  dispatch_step caller (.success .left) D regs ctx

theorem dispatch_right_step (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (dispatchLabel (.success .right))) regs D ctx) =
      some (cfg (some (positionLabel (.seek .right))) (reset regs) D ctx) :=
  dispatch_step caller (.success .right) D regs ctx

omit [DecidableEq K] in
theorem phaseSteps_move (q : MoveParserMachine.Phase) (D : LocalData) :
    phaseSteps (movePhase q) D = MoveParserMachine.phaseSteps q D.certificate D.moveReverse +
      phaseSteps (dispatchPhase (moveFinish q D).result) (moveFinish q D).data := rfl

omit [DecidableEq K] in
theorem phaseSteps_dispatch_failure (D : LocalData) : phaseSteps (dispatchPhase .failure) D = 1 := rfl

omit [DecidableEq K] in
theorem phaseSteps_dispatch_success (d : RotationDirection) (D : LocalData) :
    phaseSteps (dispatchPhase (.success d)) D =
      1 + PositionedRotationMachine.phaseSteps (.seek d) (positionData D) := rfl

omit [DecidableEq K] in
theorem phaseSteps_position (q : PositionedRotationMachine.Phase) (D : LocalData) :
    phaseSteps (positionPhase q) D = PositionedRotationMachine.phaseSteps q (positionData D) := rfl

omit [DecidableEq K] in
theorem phaseResult_move (q : MoveParserMachine.Phase) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    phaseResult (Λ := Λ) (movePhase q) regs D ctx =
      phaseResult (dispatchPhase (moveFinish q D).result) (resetMove regs) (moveFinish q D).data ctx := rfl

omit [DecidableEq K] in
theorem phaseResult_dispatch_failure (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    phaseResult (Λ := Λ) (dispatchPhase .failure) regs D ctx =
      cfg (some (resultLabel parseFailure)) (reset regs) D ctx := rfl

omit [DecidableEq K] in
theorem phaseResult_dispatch_success (d : RotationDirection) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    phaseResult (Λ := Λ) (dispatchPhase (.success d)) regs D ctx =
      phaseResult (positionPhase (.seek d)) (reset regs) D ctx := rfl

omit [DecidableEq K] in
theorem phaseResult_position (q : PositionedRotationMachine.Phase) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    phaseResult (Λ := Λ) (positionPhase q) regs D ctx =
      cfg (some (resultLabel (.inr (PositionedRotationMachine.evaluate (.inl q) (positionData D)).result)))
        (reset regs) (setPositionData D (PositionedRotationMachine.evaluate (.inl q) (positionData D)).data) ctx := rfl

theorem move_owned_prefix_transport
    (localCaller : MoveParserMachine.External (MoveCallerLabel Λ) → MoveStatement Γ Λ R)
    (start : MoveCfg Γ Λ R) (n : Nat) (bound : n ≤ MoveParserMachine.remainingSteps start) :
    (next caller)^[n] (some (moveCfg start)) =
      ((MoveParserMachine.next localCaller)^[n] (some start)).map moveCfg := by
  apply move_prefix_transport caller localCaller n start
  intro j strict
  obtain ⟨reached, executed, _, _, owned, _⟩ :=
    MoveParserMachine.owned_prefix localCaller start j (by omega)
  exact ⟨reached, executed, owned.mp (by omega)⟩

theorem position_owned_prefix_transport
    (localCaller : PositionedRotationMachine.External (PositionCallerLabel Λ) → PositionStatement Γ Λ R)
    (start : PositionCfg Γ Λ R) (n : Nat) (bound : n ≤ PositionedRotationMachine.remainingSteps start) :
    (next caller)^[n] (some (positionCfg start)) =
      ((PositionedRotationMachine.next localCaller)^[n] (some start)).map positionCfg := by
  apply position_prefix_transport caller localCaller n start
  intro j strict
  obtain ⟨reached, executed, _, _, owned⟩ :=
    PositionedRotationMachine.owned_prefix localCaller start j (by omega)
  exact ⟨reached, executed, owned.mp (by omega)⟩

/-- Every inclusive parser prefix frames all four complementary tree stores. -/
theorem move_phase_prefix_frame (q : MoveParserMachine.Phase) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) (n : Nat) (reached : Cfg Γ Λ R)
    (bound : n ≤ MoveParserMachine.phaseSteps q D.certificate D.moveReverse)
    (executed : (next caller)^[n] (some (cfg (some (moveLabel q)) regs D ctx)) = some reached) :
    reached.var = (if n = 0 then regs else resetMove regs) ∧
      reached.var.2 = regs.2 ∧
      reached.stk (.inl .source) = D.source ∧ reached.stk (.inl .saved) = D.saved ∧
      reached.stk (.inl .scratch) = D.scratch ∧ reached.stk (.inl .pending) = D.pending ∧
      ∀ k, reached.stk (.inr k) = ctx k := by
  have canonical := move_prefix_reset caller q D regs ctx n reached bound executed
  let localCaller : MoveParserMachine.External (MoveCallerLabel Λ) → MoveStatement Γ Λ R := fun _ => .halt
  let start : MoveCfg Γ Λ R :=
    moveView (some (MoveParserMachine.phaseLabel q)) (moveRegisterEquiv.symm regs) D ctx
  have startEq : moveCfg start = cfg (some (moveLabel q)) regs D ctx := by
    rw [moveCfg_view]
    simp only [Option.map_some, moveLabelEquiv_phase, Equiv.apply_symm_apply]
  obtain ⟨localReached, localRun, _, _, _, _⟩ :=
    MoveParserMachine.owned_prefix localCaller start n bound
  have actual := move_owned_prefix_transport caller localCaller start n bound
  rw [localRun, Option.map_some, startEq] at actual
  have same : reached = moveCfg localReached := Option.some.inj (executed.symm.trans actual)
  have frame := (MoveParserMachine.prefix_preserves localCaller start localReached n bound localRun).2.1
  refine ⟨canonical, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [canonical]
    split <;> rfl
  · rw [same, moveCfg_source]
    exact frame (.inl .source)
  · rw [same]
    change FrontEndMachine.Transport.stackEquiv moveStackEquiv (moveSymbolEquiv (Γ := Γ))
      localReached.stk (moveStackEquiv (.inr (.inl .saved))) = _
    rw [FrontEndMachine.Transport.stackEquiv_apply]
    change List.map id _ = _
    rw [List.map_id]
    exact frame (.inl .saved)
  · rw [same]
    change FrontEndMachine.Transport.stackEquiv moveStackEquiv (moveSymbolEquiv (Γ := Γ))
      localReached.stk (moveStackEquiv (.inr (.inl .scratch))) = _
    rw [FrontEndMachine.Transport.stackEquiv_apply]
    change List.map id _ = _
    rw [List.map_id]
    exact frame (.inl .scratch)
  · rw [same]
    change FrontEndMachine.Transport.stackEquiv moveStackEquiv (moveSymbolEquiv (Γ := Γ))
      localReached.stk (moveStackEquiv (.inr (.inl .pending))) = _
    rw [FrontEndMachine.Transport.stackEquiv_apply]
    change List.map id _ = _
    rw [List.map_id]
    exact frame (.inl .pending)
  · intro k
    rw [same, moveCfg_context]
    exact frame (.inr k)

/-- Every inclusive Position prefix frames the certificate and reverse-path stores. -/
theorem position_phase_prefix_frame (q : PositionedRotationMachine.Phase) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) (n : Nat) (reached : Cfg Γ Λ R)
    (bound : n ≤ PositionedRotationMachine.phaseSteps q (positionData D))
    (executed : (next caller)^[n] (some (cfg (some (positionLabel q)) regs D ctx)) = some reached) :
    reached.var = (if n = 0 then regs else reset regs) ∧ reached.var.2 = regs.2 ∧
      reached.stk (.inl .certificate) = D.certificate ∧
      reached.stk (.inl .moveReverse) = D.moveReverse ∧
      ∀ k, reached.stk (.inr k) = ctx k := by
  have canonical := position_prefix_reset caller q D regs ctx n reached bound executed
  let localCaller : PositionedRotationMachine.External (PositionCallerLabel Λ) →
      PositionStatement Γ Λ R := fun _ => .halt
  let start : PositionCfg Γ Λ R := positionView (some (PositionedRotationMachine.phaseLabel q)) regs D ctx
  have startEq : positionCfg start = cfg (some (positionLabel q)) regs D ctx := by
    rw [positionCfg_view]
    rfl
  obtain ⟨localReached, localRun, _, _, _⟩ :=
    PositionedRotationMachine.owned_prefix localCaller start n bound
  have actual := position_owned_prefix_transport caller localCaller start n bound
  rw [localRun, Option.map_some, startEq] at actual
  have same : reached = positionCfg localReached := Option.some.inj (executed.symm.trans actual)
  have frame := (PositionedRotationMachine.prefix_frame localCaller start localReached n bound localRun).2
  refine ⟨canonical, ?_, ?_, ?_, ?_⟩
  · rw [canonical]
    split <;> rfl
  · rw [same]
    change FrontEndMachine.Transport.stackEquiv positionStackEquiv (positionSymbolEquiv (Γ := Γ))
      localReached.stk (positionStackEquiv (.inr (.inl .certificate))) = _
    rw [FrontEndMachine.Transport.stackEquiv_apply]
    change List.map id _ = _
    rw [List.map_id]
    exact frame (.inl .certificate)
  · rw [same]
    change FrontEndMachine.Transport.stackEquiv positionStackEquiv (positionSymbolEquiv (Γ := Γ))
      localReached.stk (positionStackEquiv (.inr (.inl .moveReverse))) = _
    rw [FrontEndMachine.Transport.stackEquiv_apply]
    change List.map id _ = _
    rw [List.map_id]
    exact frame (.inl .moveReverse)
  · intro k
    rw [same, positionCfg_context]
    exact frame (.inr k)


/-!
## Actual source observations and the physical parsed position

Scratch implementation suffix, released after the recorded scope42 baseline.
The initial source-observation prefix passed its separately recorded helper
check. The evolving complete suffix still requires its actual core-dependent
endpoint/timing/sharp-family check; no complete check is claimed by this
comment. None of these definitions is installed in a runtime callback.
-/

/-- The old physical path follows the newly parsed path without a runtime copy. -/
def physicalMove (move : RotationMove) (oldPath : List Branch) : RotationMove :=
  ⟨move.direction, move.position ++ oldPath⟩

@[simp] theorem physicalMove_direction (move : RotationMove) (oldPath : List Branch) :
    (physicalMove move oldPath).direction = move.direction := rfl

@[simp] theorem physicalMove_position (move : RotationMove) (oldPath : List Branch) :
    (physicalMove move oldPath).position = move.position ++ oldPath := rfl

@[simp] theorem physicalMove_nil (move : RotationMove) : physicalMove move [] = move := by
  cases move
  simp [physicalMove]

/-- The actual measured source result on the full physically installed position. -/
def representedValue (move : RotationMove) (oldPath : List Branch) (s : BinaryTree Unit) :
    Option (BinaryTree Unit) := (applyMoveRun (physicalMove move oldPath) s).1

/-- Literal restoration of old saved data around the represented source result. -/
def representedSource (move : RotationMove) (oldPath : List Branch) (s : BinaryTree Unit)
    (saved suffix : Word) : Word :=
  saved.reverse ++ treeCode ((representedValue move oldPath s).getD s) ++ suffix

/-- Parser activations, one paid dispatch, actual Position time and old saved pops. -/
def representedSteps (move : RotationMove) (oldPath : List Branch) (s : BinaryTree Unit)
    (saved : Word) : Nat :=
  2 * move.position.length + 4 +
    PositionedRotationMachine.representedClock move.direction (move.position ++ oldPath) s +
      saved.length

/-- Two existing source observations; this does not introduce a new runtime tariff. -/
def sourceObservationCost (raw : Word) (move : RotationMove) (oldPath : List Branch)
    (s : BinaryTree Unit) : Nat :=
  (parseMoveRun raw).2 + (applyMoveRun (physicalMove move oldPath) s).2

theorem representedValue_eq_applyMove (move : RotationMove) (oldPath : List Branch)
    (s : BinaryTree Unit) :
    representedValue move oldPath s = Trees.Rotations.applyMove? (physicalMove move oldPath) s :=
  applyMoveRun_value (physicalMove move oldPath) s

theorem representedValue_numNodes (move : RotationMove) (oldPath : List Branch)
    (s t : BinaryTree Unit) (returned : representedValue move oldPath s = some t) :
    t.numNodes = s.numNodes :=
  applyMoveRun_numNodes (physicalMove move oldPath) s t returned

theorem representedSource_length (move : RotationMove) (oldPath : List Branch)
    (s : BinaryTree Unit) (saved suffix : Word) :
    (representedSource move oldPath s saved suffix).length =
      saved.length + 2 * s.numNodes + 1 + suffix.length := by
  unfold representedSource
  cases actual : representedValue move oldPath s with
  | none =>
      simp only [Option.getD_none, List.length_append, List.length_reverse,
        treeCode_length, Nat.add_assoc]
  | some t =>
      simp only [Option.getD_some, List.length_append, List.length_reverse,
        treeCode_length, representedValue_numNodes move oldPath s t actual, Nat.add_assoc]

theorem representedSource_of_none (move : RotationMove) (oldPath : List Branch)
    (s : BinaryTree Unit) (saved suffix : Word)
    (failed : representedValue move oldPath s = none) :
    representedSource move oldPath s saved suffix = saved.reverse ++ treeCode s ++ suffix := by
  simp only [representedSource, failed, Option.getD_none]

theorem representedSource_of_some (move : RotationMove) (oldPath : List Branch)
    (s t : BinaryTree Unit) (saved suffix : Word)
    (returned : representedValue move oldPath s = some t) :
    representedSource move oldPath s saved suffix = saved.reverse ++ treeCode t ++ suffix := by
  simp only [representedSource, returned, Option.getD_some]

/-- Old saved data is cancelled before the uniquely decoded tree and suffix are compared. -/
theorem representedSource_success_injective (move : RotationMove) (oldPath : List Branch)
    (s t other : BinaryTree Unit) (saved suffix otherSuffix : Word)
    (returned : representedValue move oldPath s = some t)
    (output : representedSource move oldPath s saved suffix =
      saved.reverse ++ treeCode other ++ otherSuffix) :
    t = other ∧ suffix = otherSuffix := by
  rw [representedSource_of_some move oldPath s t saved suffix returned] at output
  have prefixed : saved.reverse ++ (treeCode t ++ suffix) =
      saved.reverse ++ (treeCode other ++ otherSuffix) := by
    simpa only [List.append_assoc] using output
  exact parseTreeRun_prefix_injective t other suffix otherSuffix
    (List.append_cancel_left prefixed)

theorem source_application_cost_of_some (move : RotationMove) (oldPath : List Branch)
    (s t : BinaryTree Unit) (returned : representedValue move oldPath s = some t) :
    (applyMoveRun (physicalMove move oldPath) s).2 =
      3 * (move.position ++ oldPath).length + 5 :=
  applyMoveRun_cost_of_some (physicalMove move oldPath) s t returned

/-- The failure tariff follows the actual stopped source cursor, separately from the physical path tail. -/
theorem source_application_cost_eq_stopped (move : RotationMove) (oldPath : List Branch)
    (s : BinaryTree Unit) :
    (applyMoveRun (physicalMove move oldPath) s).2 =
      if (representedValue move oldPath s).isSome then
        3 * PositionedRotationMachine.descentCount (move.position ++ oldPath) s + 5
      else 2 * PositionedRotationMachine.descentCount (move.position ++ oldPath) s +
        if PositionedRotationMachine.stoppedPath (move.position ++ oldPath) s = [] then 3 else 2 :=
  PositionedRotationMachine.source_cost_eq_stopped move.direction (move.position ++ oldPath) s

theorem sourceObservationCost_of_parse (raw : Word) (move : RotationMove) (rest : Word)
    (oldPath : List Branch) (s : BinaryTree Unit)
    (parsed : (parseMoveRun raw).1 = some (move, rest)) :
    sourceObservationCost raw move oldPath s =
      3 * move.position.length + 4 + (applyMoveRun (physicalMove move oldPath) s).2 := by
  unfold sourceObservationCost
  rw [parseMoveRun_cost_of_some raw move rest parsed]

/-- The certificate itself, rather than a consumed final path, fixes the parsed move and remainder. -/
theorem parsed_prefix_unique (raw : Word) (move other : RotationMove) (rest otherRest : Word)
    (first : (parseMoveRun raw).1 = some (move, rest))
    (second : (parseMoveRun raw).1 = some (other, otherRest)) :
    move = other ∧ rest = otherRest := by
  have left := (parseMoveRun_iff raw move rest).mp first
  have right := (parseMoveRun_iff raw other otherRest).mp second
  exact parseMoveRun_prefix_injective move other rest otherRest (left.symm.trans right)

theorem sourceObservationCost_of_some (raw : Word) (move : RotationMove) (rest : Word)
    (oldPath : List Branch) (s t : BinaryTree Unit)
    (parsed : (parseMoveRun raw).1 = some (move, rest))
    (returned : representedValue move oldPath s = some t) :
    sourceObservationCost raw move oldPath s =
      3 * move.position.length + 3 * (move.position ++ oldPath).length + 9 := by
  unfold sourceObservationCost
  rw [parseMoveRun_cost_of_some raw move rest parsed,
    source_application_cost_of_some move oldPath s t returned]
  omega

theorem sourceObservationCost_code (move : RotationMove) (rest : Word)
    (oldPath : List Branch) (s t : BinaryTree Unit)
    (returned : representedValue move oldPath s = some t) :
    sourceObservationCost (moveCode move ++ rest) move oldPath s =
      3 * move.position.length + 3 * (move.position ++ oldPath).length + 9 := by
  apply sourceObservationCost_of_some _ move rest oldPath s t
  · exact congrArg Prod.fst (parseMoveRun_code move rest)
  · exact returned

theorem sourceObservationCost_clean (raw : Word) (move : RotationMove) (rest : Word)
    (s t : BinaryTree Unit) (parsed : (parseMoveRun raw).1 = some (move, rest))
    (returned : representedValue move [] s = some t) :
    sourceObservationCost raw move [] s = 6 * move.position.length + 9 := by
  rw [sourceObservationCost_of_some raw move rest [] s t parsed returned, List.append_nil]
  omega

theorem parser_failure_source_cost (raw : Word) (failed : (parseMoveRun raw).1 = none) :
    (parseMoveRun raw).2 = MoveParserMachine.fullSteps raw + 1 :=
  MoveParserMachine.parseMoveRun_failure_cost raw failed

theorem representedSteps_clean (move : RotationMove) (s : BinaryTree Unit) (saved : Word) :
    representedSteps move [] s saved =
      2 * move.position.length + 4 +
        PositionedRotationMachine.representedClock move.direction move.position s + saved.length := by
  simp only [representedSteps, List.append_nil]

theorem representedSteps_saved_append (move : RotationMove) (oldPath : List Branch)
    (s : BinaryTree Unit) (left right : Word) :
    representedSteps move oldPath s (left ++ right) =
      representedSteps move oldPath s left + right.length := by
  simp only [representedSteps, List.length_append]
  omega

/-! ### Complete principal data and represented endpoint views -/

/-- Principal entry has an empty parser reverse stack and arbitrary Position stores. -/
def entryData (raw : Word) (path : List Branch) (source saved scratch : Word)
    (pending : List Unit) : LocalData where
  certificate := raw
  path := path
  source := source
  saved := saved
  scratch := scratch
  pending := pending

def entry (regs : Registers R) (raw : Word) (path : List Branch)
    (source saved scratch : Word) (pending : List Unit)
    (ctx : ∀ k, List (Γ k)) : Cfg Γ Λ R :=
  cfg (some (moveLabel .start)) regs (entryData raw path source saved scratch pending) ctx

/-- The parser's real success appends the old forward path; the other stores are retained. -/
def parsedData (move : RotationMove) (rest : Word) (D : LocalData) : LocalData :=
  { D with certificate := rest, moveReverse := [], path := move.position ++ D.path }

/-- A clean represented tree may still have arbitrary old path, saved word and two suffixes. -/
def representedEntryData (move : RotationMove) (certificateRest : Word)
    (oldPath : List Branch) (s : BinaryTree Unit) (saved suffix : Word) : LocalData :=
  entryData (moveCode move ++ certificateRest) oldPath (treeCode s ++ suffix) saved [] []

def representedFinalData (move : RotationMove) (certificateRest : Word)
    (oldPath : List Branch) (s : BinaryTree Unit) (saved suffix : Word) : LocalData where
  certificate := certificateRest
  source := representedSource move oldPath s saved suffix
  path := PositionedRotationMachine.remainingPath (move.position ++ oldPath) s

def representedResult (move : RotationMove) (oldPath : List Branch)
    (s : BinaryTree Unit) : FinalResult :=
  if (representedValue move oldPath s).isSome then success else rotationFailure

@[simp] theorem parsedData_certificate (move : RotationMove) (rest : Word) (D : LocalData) :
    (parsedData move rest D).certificate = rest := rfl

@[simp] theorem parsedData_moveReverse (move : RotationMove) (rest : Word) (D : LocalData) :
    (parsedData move rest D).moveReverse = [] := rfl

@[simp] theorem parsedData_path (move : RotationMove) (rest : Word) (D : LocalData) :
    (parsedData move rest D).path = move.position ++ D.path := rfl

@[simp] theorem representedFinalData_source_length (move : RotationMove)
    (certificateRest : Word) (oldPath : List Branch) (s : BinaryTree Unit)
    (saved suffix : Word) :
    (representedFinalData move certificateRest oldPath s saved suffix).source.length =
      saved.length + 2 * s.numNodes + 1 + suffix.length :=
  representedSource_length move oldPath s saved suffix

theorem representedResult_of_none (move : RotationMove) (oldPath : List Branch)
    (s : BinaryTree Unit) (failed : representedValue move oldPath s = none) :
    representedResult move oldPath s = rotationFailure := by
  simp only [representedResult, failed, Option.isSome_none, Bool.false_eq_true, ite_false]

theorem representedResult_of_some (move : RotationMove) (oldPath : List Branch)
    (s t : BinaryTree Unit) (returned : representedValue move oldPath s = some t) :
    representedResult move oldPath s = success := by
  simp only [representedResult, returned, Option.isSome_some, ite_true]

theorem representedResult_success_iff (move : RotationMove) (oldPath : List Branch)
    (s : BinaryTree Unit) :
    representedResult move oldPath s = success ↔
      ∃ t, representedValue move oldPath s = some t := by
  cases actual : representedValue move oldPath s with
  | none => simp [representedResult, actual, success, rotationFailure]
  | some t => simp [representedResult, actual]

theorem representedResult_failure_iff (move : RotationMove) (oldPath : List Branch)
    (s : BinaryTree Unit) :
    representedResult move oldPath s = rotationFailure ↔
      representedValue move oldPath s = none := by
  cases actual : representedValue move oldPath s with
  | none => simp [representedResult, actual]
  | some t => simp [representedResult, actual, success, rotationFailure]

theorem representedFinalData_of_some (move : RotationMove) (certificateRest : Word)
    (oldPath : List Branch) (s t : BinaryTree Unit) (saved suffix : Word)
    (returned : representedValue move oldPath s = some t) :
    representedFinalData move certificateRest oldPath s saved suffix =
      { certificate := certificateRest, source := saved.reverse ++ treeCode t ++ suffix } := by
  have path := PositionedRotationMachine.remainingPath_nil_of_source_success
    move.direction (move.position ++ oldPath) s t returned
  simp only [representedFinalData,
    representedSource_of_some move oldPath s t saved suffix returned, path]

@[simp] theorem positionData_entryData (raw : Word) (path : List Branch)
    (source saved scratch : Word) (pending : List Unit) :
    positionData (entryData raw path source saved scratch pending) =
      { source := source, saved := saved, scratch := scratch, pending := pending, path := path } := rfl

@[simp] theorem positionData_parsedData (move : RotationMove) (rest : Word) (D : LocalData) :
    positionData (parsedData move rest D) =
      { positionData D with path := move.position ++ D.path } := rfl

@[simp] theorem position_reset_reset (regs : Registers R) :
    PositionedRotationMachine.reset (reset regs) = reset regs := rfl

omit [DecidableEq K] in
@[simp] theorem positionContext_parsedData (move : RotationMove) (rest : Word)
    (D : LocalData) (ctx : ∀ k, List (Γ k)) :
    positionContext (parsedData move rest D) ctx =
      positionContext { certificate := rest } ctx := rfl

omit [DecidableEq K] in
/-- Transport a complete Position segment while retaining both parser stores literally. -/
theorem positionCfg_setPositionData
    (label : Option (PositionedRotationMachine.Label (PositionCallerLabel Λ)))
    (regs : Registers R) (D : LocalData) (E : PositionedRotationMachine.LocalData)
    (ctx : ∀ k, List (Γ k)) :
    positionCfg (PositionedRotationMachine.cfg label regs E (positionContext D ctx)) =
      cfg (label.map positionLabelEquiv) regs (setPositionData D E) ctx := by
  change positionCfg (positionView label regs (setPositionData D E) ctx) = _
  exact positionCfg_view label regs (setPositionData D E) ctx

/-! ### The actual parser segment and its paid complete handoff -/

theorem move_start_source_localRun (raw : Word) (path : List Branch)
    (source saved scratch : Word) (pending : List Unit)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (MoveParserMachine.fullSteps raw)
      (entry regs raw path source saved scratch pending ctx)
      (moveCfg (MoveParserMachine.resultCfg (moveRegisterEquiv.symm regs) raw path
        (moveContext (entryData raw path source saved scratch pending) ctx) (parseMoveRun raw).1)) := by
  let D := entryData raw path source saved scratch pending
  let localCaller : MoveParserMachine.External (MoveCallerLabel Λ) → MoveStatement Γ Λ R :=
    fun _ => .halt
  have canonical :
      (MoveParserMachine.next localCaller)^[MoveParserMachine.fullSteps raw]
        (some (MoveParserMachine.entry (moveRegisterEquiv.symm regs) raw path (moveContext D ctx))) =
      some (MoveParserMachine.phaseResult .start (moveRegisterEquiv.symm regs) raw [] path
        (moveContext D ctx)) :=
    MoveParserMachine.phase_iterate localCaller .start raw [] path
      (moveRegisterEquiv.symm regs) (moveContext D ctx)
  have observed := MoveParserMachine.run_source localCaller raw path
    (moveRegisterEquiv.symm regs) (moveContext D ctx)
  have same := Option.some.inj (canonical.symm.trans observed)
  have run := move_phase_transport caller .start D regs ctx
  change LocalRun caller (MoveParserMachine.fullSteps raw)
    (entry regs raw path source saved scratch pending ctx)
    (moveCfg (MoveParserMachine.phaseResult .start (moveRegisterEquiv.symm regs) raw [] path
      (moveContext D ctx))) at run
  rw [same] at run
  exact run

theorem parse_failure_localRun (raw : Word) (path : List Branch)
    (source saved scratch : Word) (pending : List Unit)
    (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (failed : (parseMoveRun raw).1 = none) :
    LocalRun caller (MoveParserMachine.fullSteps raw)
      (entry regs raw path source saved scratch pending ctx)
      (cfg (some (dispatchLabel .failure)) (resetMove regs)
        (entryData raw path source saved scratch pending) ctx) := by
  have run := move_start_source_localRun caller raw path source saved scratch pending regs ctx
  rw [failed] at run
  change LocalRun caller _ _
    (moveCfg (moveView (some (MoveParserMachine.resultLabel .failure))
      (MoveParserMachine.reset (moveRegisterEquiv.symm regs))
      (entryData raw path source saved scratch pending) ctx)) at run
  rw [moveCfg_view] at run
  simpa only [Option.map_some, moveLabelEquiv_result, moveRegisterEquiv_reset,
    Equiv.apply_symm_apply] using run

theorem parse_success_localRun (raw : Word) (move : RotationMove) (rest : Word)
    (path : List Branch) (source saved scratch : Word) (pending : List Unit)
    (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (parsed : (parseMoveRun raw).1 = some (move, rest)) :
    LocalRun caller (MoveParserMachine.fullSteps raw)
      (entry regs raw path source saved scratch pending ctx)
      (cfg (some (dispatchLabel (.success move.direction))) (resetMove regs)
        (parsedData move rest (entryData raw path source saved scratch pending)) ctx) := by
  have run := move_start_source_localRun caller raw path source saved scratch pending regs ctx
  rw [parsed] at run
  change LocalRun caller _ _
    (moveCfg (moveView (some (MoveParserMachine.resultLabel (.success move.direction)))
      (MoveParserMachine.reset (moveRegisterEquiv.symm regs))
      (parsedData move rest (entryData raw path source saved scratch pending)) ctx)) at run
  rw [moveCfg_view] at run
  simpa only [Option.map_some, moveLabelEquiv_result, moveRegisterEquiv_reset,
    Equiv.apply_symm_apply] using run

theorem run_of_none_localRun (raw : Word) (path : List Branch)
    (source saved scratch : Word) (pending : List Unit)
    (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (failed : (parseMoveRun raw).1 = none) :
    LocalRun caller (MoveParserMachine.fullSteps raw + 1)
      (entry regs raw path source saved scratch pending ctx)
      (cfg (some (resultLabel parseFailure)) (reset regs)
        (entryData raw path source saved scratch pending) ctx) := by
  have parsed := parse_failure_localRun caller raw path source saved scratch pending regs ctx failed
  have paid := dispatch_localRun caller .failure
    (entryData raw path source saved scratch pending) (resetMove regs) ctx
  simpa only [dispatchTarget, reset_resetMove] using LocalRun.trans caller parsed paid

theorem paid_position_entry_localRun (raw : Word) (move : RotationMove) (rest : Word)
    (path : List Branch) (source saved scratch : Word) (pending : List Unit)
    (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (parsed : (parseMoveRun raw).1 = some (move, rest)) :
    LocalRun caller (MoveParserMachine.fullSteps raw + 1)
      (entry regs raw path source saved scratch pending ctx)
      (cfg (some (positionLabel (.seek move.direction))) (reset regs)
        (parsedData move rest (entryData raw path source saved scratch pending)) ctx) := by
  have first := parse_success_localRun caller raw move rest path source saved scratch pending regs ctx parsed
  have paid := dispatch_localRun caller (.success move.direction)
    (parsedData move rest (entryData raw path source saved scratch pending)) (resetMove regs) ctx
  simpa only [dispatchTarget, reset_resetMove] using LocalRun.trans caller first paid

theorem paid_position_code_localRun (move : RotationMove) (rest : Word)
    (path : List Branch) (source saved scratch : Word) (pending : List Unit)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (2 * move.position.length + 4)
      (entry regs (moveCode move ++ rest) path source saved scratch pending ctx)
      (cfg (some (positionLabel (.seek move.direction))) (reset regs)
        { certificate := rest, path := move.position ++ path,
          source := source, saved := saved, scratch := scratch, pending := pending } ctx) := by
  have run := paid_position_entry_localRun caller (moveCode move ++ rest) move rest
    path source saved scratch pending regs ctx (congrArg Prod.fst (parseMoveRun_code move rest))
  simpa only [MoveParserMachine.fullSteps_code, show 2 * move.position.length + 3 + 1 =
      2 * move.position.length + 4 by omega, parsedData, entryData] using run

theorem parse_failure_boundary (raw : Word) (path : List Branch)
    (source saved scratch : Word) (pending : List Unit)
    (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (failed : (parseMoveRun raw).1 = none) :
    (next caller)^[MoveParserMachine.fullSteps raw]
      (some (entry regs raw path source saved scratch pending ctx)) =
      some (cfg (some (dispatchLabel .failure)) (resetMove regs)
        (entryData raw path source saved scratch pending) ctx) :=
  LocalRun.iterate caller (parse_failure_localRun caller raw path source saved scratch pending regs ctx failed)

theorem parse_success_boundary (raw : Word) (move : RotationMove) (rest : Word)
    (path : List Branch) (source saved scratch : Word) (pending : List Unit)
    (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (parsed : (parseMoveRun raw).1 = some (move, rest)) :
    (next caller)^[2 * move.position.length + 3]
      (some (entry regs raw path source saved scratch pending ctx)) =
      some (cfg (some (dispatchLabel (.success move.direction))) (resetMove regs)
        (parsedData move rest (entryData raw path source saved scratch pending)) ctx) := by
  have run := LocalRun.iterate caller
    (parse_success_localRun caller raw move rest path source saved scratch pending regs ctx parsed)
  simpa only [MoveParserMachine.fullSteps_of_some raw move rest parsed] using run

theorem paid_position_entry (raw : Word) (move : RotationMove) (rest : Word)
    (path : List Branch) (source saved scratch : Word) (pending : List Unit)
    (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (parsed : (parseMoveRun raw).1 = some (move, rest)) :
    (next caller)^[MoveParserMachine.fullSteps raw + 1]
      (some (entry regs raw path source saved scratch pending ctx)) =
      some (cfg (some (positionLabel (.seek move.direction))) (reset regs)
        (parsedData move rest (entryData raw path source saved scratch pending)) ctx) :=
  LocalRun.iterate caller
    (paid_position_entry_localRun caller raw move rest path source saved scratch pending regs ctx parsed)

/-! ### Actual composite clocks, first-result observations and typed timing -/

def runSteps (raw : Word) (path : List Branch) (source saved scratch : Word)
    (pending : List Unit) : Nat :=
  phaseSteps (movePhase .start) (entryData raw path source saved scratch pending)

def runResult (regs : Registers R) (raw : Word) (path : List Branch)
    (source saved scratch : Word) (pending : List Unit)
    (ctx : ∀ k, List (Γ k)) : Cfg Γ Λ R :=
  phaseResult (movePhase .start) regs (entryData raw path source saved scratch pending) ctx

/-- A first live result requires every actual strict earlier state to be owned. -/
def FirstResult (caller : External Λ → Statement Γ Λ R) (start : Cfg Γ Λ R)
    (result : FinalResult) : Prop :=
  ∃ n reached,
    (next caller)^[n] (some start) = some reached ∧
    reached.l = some (resultLabel result) ∧
    ∀ j, j < n → ∃ before,
      (next caller)^[j] (some start) = some before ∧ Owned before.l

theorem firstResult_iff_phaseResult (q : Phase) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) (result : FinalResult) :
    FirstResult caller (cfg (some (phaseLabel q)) regs D ctx) result ↔
      (phaseResult (Λ := Λ) q regs D ctx).l = some (resultLabel result) := by
  constructor
  · rintro ⟨n, reached, executed, label, earlier⟩
    have external : ¬ Owned reached.l := by
      rw [label]
      exact not_owned_result result
    obtain ⟨_, same⟩ := first_return_unique caller q D regs ctx n reached executed external earlier
    rw [same] at label
    exact label
  · intro label
    obtain ⟨_, earlier⟩ := phase_first_return caller q D regs ctx
    exact ⟨phaseSteps q D, phaseResult q regs D ctx,
      phase_iterate caller q D regs ctx, label, earlier⟩

theorem first_result_complete (q : Phase) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) (result : FinalResult)
    (n : Nat) (reached : Cfg Γ Λ R)
    (executed : (next caller)^[n] (some (cfg (some (phaseLabel q)) regs D ctx)) = some reached)
    (label : reached.l = some (resultLabel result))
    (earlier : ∀ j, j < n → ∃ before,
      (next caller)^[j] (some (cfg (some (phaseLabel q)) regs D ctx)) = some before ∧ Owned before.l) :
    n = phaseSteps q D ∧ reached = phaseResult q regs D ctx := by
  apply first_return_unique caller q D regs ctx n reached executed
  · rw [label]
    exact not_owned_result result
  · exact earlier

theorem run_firstResult_iff (raw : Word) (path : List Branch)
    (source saved scratch : Word) (pending : List Unit)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) (result : FinalResult) :
    FirstResult caller (entry regs raw path source saved scratch pending ctx) result ↔
      (runResult (Λ := Λ) regs raw path source saved scratch pending ctx).l =
        some (resultLabel result) :=
  firstResult_iff_phaseResult caller (movePhase .start)
    (entryData raw path source saved scratch pending) regs ctx result

def phaseInTime (q : Phase) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller)
      (cfg (some (phaseLabel q)) regs D ctx)
      (some (phaseResult q regs D ctx)) (phaseSteps q D) where
  steps := phaseSteps q D
  evals_in_steps := phase_iterate caller q D regs ctx
  steps_le_m := Nat.le_refl _

def runInTimeExact (raw : Word) (path : List Branch)
    (source saved scratch : Word) (pending : List Unit)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller)
      (entry regs raw path source saved scratch pending ctx)
      (some (runResult regs raw path source saved scratch pending ctx))
      (runSteps raw path source saved scratch pending) :=
  phaseInTime caller (movePhase .start)
    (entryData raw path source saved scratch pending) regs ctx

def cfgInTime (start : Cfg Γ Λ R) :
    StateTransition.EvalsToInTime (step caller) start (some (finalCfg start))
      (remainingSteps start) where
  steps := remainingSteps start
  evals_in_steps := cfg_iterate caller start
  steps_le_m := Nat.le_refl _

theorem run_of_none (raw : Word) (path : List Branch)
    (source saved scratch : Word) (pending : List Unit)
    (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (failed : (parseMoveRun raw).1 = none) :
    (next caller)^[MoveParserMachine.fullSteps raw + 1]
      (some (entry regs raw path source saved scratch pending ctx)) =
      some (cfg (some (resultLabel parseFailure)) (reset regs)
        (entryData raw path source saved scratch pending) ctx) :=
  LocalRun.iterate caller (run_of_none_localRun caller raw path source saved scratch pending regs ctx failed)

include caller in
theorem run_none_data (raw : Word) (path : List Branch)
    (source saved scratch : Word) (pending : List Unit)
    (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (failed : (parseMoveRun raw).1 = none) :
    runSteps raw path source saved scratch pending = MoveParserMachine.fullSteps raw + 1 ∧
      runResult (Λ := Λ) regs raw path source saved scratch pending ctx =
        cfg (some (resultLabel parseFailure)) (reset regs)
          (entryData raw path source saved scratch pending) ctx :=
  LocalRun.phaseEndpoint caller (q := movePhase .start)
    (run_of_none_localRun caller raw path source saved scratch pending regs ctx failed)

theorem runSteps_of_none (raw : Word) (path : List Branch)
    (source saved scratch : Word) (pending : List Unit)
    (failed : (parseMoveRun raw).1 = none) :
    runSteps raw path source saved scratch pending = MoveParserMachine.fullSteps raw + 1 := by
  let emptyCaller : External Unit → Statement (fun _ : Unit => Unit) Unit Unit := fun _ => .halt
  exact (run_none_data emptyCaller raw path source saved scratch pending
    ((none, (none, none)), ()) (fun _ => []) failed).1

include caller in
theorem runResult_of_none (raw : Word) (path : List Branch)
    (source saved scratch : Word) (pending : List Unit)
    (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (failed : (parseMoveRun raw).1 = none) :
    runResult (Λ := Λ) regs raw path source saved scratch pending ctx =
      cfg (some (resultLabel parseFailure)) (reset regs)
        (entryData raw path source saved scratch pending) ctx :=
  (run_none_data caller raw path source saved scratch pending regs ctx failed).2

theorem run_of_some_localRun (raw : Word) (move : RotationMove) (rest : Word)
    (path : List Branch) (source saved scratch : Word) (pending : List Unit)
    (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (parsed : (parseMoveRun raw).1 = some (move, rest)) :
    LocalRun caller (MoveParserMachine.fullSteps raw + 1 +
      PositionedRotationMachine.phaseSteps (.seek move.direction)
        (positionData (parsedData move rest (entryData raw path source saved scratch pending))))
      (entry regs raw path source saved scratch pending ctx)
      (phaseResult (positionPhase (.seek move.direction)) regs
        (parsedData move rest (entryData raw path source saved scratch pending)) ctx) := by
  have first := paid_position_entry_localRun caller raw move rest path source saved scratch pending regs ctx parsed
  have last := position_phase_localRun caller (.seek move.direction)
    (parsedData move rest (entryData raw path source saved scratch pending)) (reset regs) ctx
  simpa only [phaseResult_reset] using LocalRun.trans caller first last

include caller in
theorem run_some_data (raw : Word) (move : RotationMove) (rest : Word)
    (path : List Branch) (source saved scratch : Word) (pending : List Unit)
    (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (parsed : (parseMoveRun raw).1 = some (move, rest)) :
    runSteps raw path source saved scratch pending = MoveParserMachine.fullSteps raw + 1 +
        PositionedRotationMachine.phaseSteps (.seek move.direction)
          (positionData (parsedData move rest (entryData raw path source saved scratch pending))) ∧
      runResult (Λ := Λ) regs raw path source saved scratch pending ctx =
        phaseResult (positionPhase (.seek move.direction)) regs
          (parsedData move rest (entryData raw path source saved scratch pending)) ctx :=
  LocalRun.phaseEndpoint caller (q := movePhase .start)
    (run_of_some_localRun caller raw move rest path source saved scratch pending regs ctx parsed)

theorem runSteps_of_some (raw : Word) (move : RotationMove) (rest : Word)
    (path : List Branch) (source saved scratch : Word) (pending : List Unit)
    (parsed : (parseMoveRun raw).1 = some (move, rest)) :
    runSteps raw path source saved scratch pending = MoveParserMachine.fullSteps raw + 1 +
      PositionedRotationMachine.phaseSteps (.seek move.direction)
        { source := source, saved := saved, scratch := scratch, pending := pending,
          path := move.position ++ path } := by
  let emptyCaller : External Unit → Statement (fun _ : Unit => Unit) Unit Unit := fun _ => .halt
  exact (run_some_data emptyCaller raw move rest path source saved scratch pending
    ((none, (none, none)), ()) (fun _ => []) parsed).1

include caller in
theorem runResult_of_some (raw : Word) (move : RotationMove) (rest : Word)
    (path : List Branch) (source saved scratch : Word) (pending : List Unit)
    (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (parsed : (parseMoveRun raw).1 = some (move, rest)) :
    runResult (Λ := Λ) regs raw path source saved scratch pending ctx =
      phaseResult (positionPhase (.seek move.direction)) regs
        (parsedData move rest (entryData raw path source saved scratch pending)) ctx :=
  (run_some_data caller raw move rest path source saved scratch pending regs ctx parsed).2

theorem run_of_some (raw : Word) (move : RotationMove) (rest : Word)
    (path : List Branch) (source saved scratch : Word) (pending : List Unit)
    (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (parsed : (parseMoveRun raw).1 = some (move, rest)) :
    (next caller)^[MoveParserMachine.fullSteps raw + 1 +
      PositionedRotationMachine.phaseSteps (.seek move.direction)
        (positionData (parsedData move rest (entryData raw path source saved scratch pending)))]
      (some (entry regs raw path source saved scratch pending ctx)) =
      some (phaseResult (positionPhase (.seek move.direction)) regs
        (parsedData move rest (entryData raw path source saved scratch pending)) ctx) :=
  LocalRun.iterate caller
    (run_of_some_localRun caller raw move rest path source saved scratch pending regs ctx parsed)

theorem run_code (move : RotationMove) (rest : Word) (path : List Branch)
    (source saved scratch : Word) (pending : List Unit)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (next caller)^[2 * move.position.length + 4 +
      PositionedRotationMachine.phaseSteps (.seek move.direction)
        { source := source, saved := saved, scratch := scratch, pending := pending,
          path := move.position ++ path }]
      (some (entry regs (moveCode move ++ rest) path source saved scratch pending ctx)) =
      some (phaseResult (positionPhase (.seek move.direction)) regs
        { certificate := rest, path := move.position ++ path,
          source := source, saved := saved, scratch := scratch, pending := pending } ctx) := by
  have run := run_of_some caller (moveCode move ++ rest) move rest path source saved scratch pending
    regs ctx (congrArg Prod.fst (parseMoveRun_code move rest))
  simpa only [MoveParserMachine.fullSteps_code, show 2 * move.position.length + 3 + 1 =
    2 * move.position.length + 4 by omega, positionData, parsedData, entryData] using run

include caller in
theorem run_source (raw : Word) (path : List Branch)
    (source saved scratch : Word) (pending : List Unit)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    match (parseMoveRun raw).1 with
    | none =>
        runSteps raw path source saved scratch pending = MoveParserMachine.fullSteps raw + 1 ∧
        runResult (Λ := Λ) regs raw path source saved scratch pending ctx =
          cfg (some (resultLabel parseFailure)) (reset regs)
            (entryData raw path source saved scratch pending) ctx
    | some (move, rest) =>
        runSteps raw path source saved scratch pending = MoveParserMachine.fullSteps raw + 1 +
          PositionedRotationMachine.phaseSteps (.seek move.direction)
            (positionData (parsedData move rest (entryData raw path source saved scratch pending))) ∧
        runResult (Λ := Λ) regs raw path source saved scratch pending ctx =
          phaseResult (positionPhase (.seek move.direction)) regs
            (parsedData move rest (entryData raw path source saved scratch pending)) ctx := by
  cases parsed : (parseMoveRun raw).1 with
  | none => exact run_none_data caller raw path source saved scratch pending regs ctx parsed
  | some pair =>
      rcases pair with ⟨move, rest⟩
      exact run_some_data caller raw move rest path source saved scratch pending regs ctx parsed

/-- The source observation selects the actual complete joined iteration, including its paid dispatch. -/
theorem run_source_iterate (raw : Word) (path : List Branch)
    (source saved scratch : Word) (pending : List Unit)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    match (parseMoveRun raw).1 with
    | none =>
        (next caller)^[MoveParserMachine.fullSteps raw + 1]
          (some (entry regs raw path source saved scratch pending ctx)) =
          some (cfg (some (resultLabel parseFailure)) (reset regs)
            (entryData raw path source saved scratch pending) ctx)
    | some (move, rest) =>
        (next caller)^[MoveParserMachine.fullSteps raw + 1 +
          PositionedRotationMachine.phaseSteps (.seek move.direction)
            (positionData (parsedData move rest (entryData raw path source saved scratch pending)))]
          (some (entry regs raw path source saved scratch pending ctx)) =
          some (phaseResult (positionPhase (.seek move.direction)) regs
            (parsedData move rest (entryData raw path source saved scratch pending)) ctx) := by
  cases parsed : (parseMoveRun raw).1 with
  | none => exact run_of_none caller raw path source saved scratch pending regs ctx parsed
  | some pair =>
      rcases pair with ⟨move, rest⟩
      exact run_of_some caller raw move rest path source saved scratch pending regs ctx parsed

omit [DecidableEq K] in
theorem position_result_label_iff (q : PositionedRotationMachine.Phase) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) (r : PositionedRotationMachine.Result) :
    (phaseResult (Λ := Λ) (positionPhase q) regs D ctx).l = some (resultLabel (.inr r)) ↔
      (PositionedRotationMachine.phaseResult (Λ := PositionCallerLabel Λ) q regs
        (positionData D) (positionContext D ctx)).l = some (PositionedRotationMachine.resultLabel r) := by
  simp only [phaseResult, positionPhase, evaluate, evaluatePosition, cfg, resultLabel,
    PositionedRotationMachine.phaseResult, PositionedRotationMachine.cfg,
    PositionedRotationMachine.resultLabel, Option.some.injEq, Sum.inr.injEq, Sum.inl.injEq]

theorem first_parseFailure_iff (raw : Word) (path : List Branch)
    (source saved scratch : Word) (pending : List Unit)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    FirstResult caller (entry regs raw path source saved scratch pending ctx) parseFailure ↔
      (parseMoveRun raw).1 = none := by
  rw [run_firstResult_iff]
  cases parsed : (parseMoveRun raw).1 with
  | none =>
      rw [runResult_of_none caller raw path source saved scratch pending regs ctx parsed]
      simp [cfg]
  | some pair =>
      rcases pair with ⟨move, rest⟩
      rw [runResult_of_some caller raw move rest path source saved scratch pending regs ctx parsed]
      simp [phaseResult, positionPhase, evaluate, evaluatePosition, cfg, resultLabel, parseFailure]

theorem first_rotation_result_iff (raw : Word) (path : List Branch)
    (source saved scratch : Word) (pending : List Unit)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) (r : PositionedRotationMachine.Result) :
    FirstResult caller (entry regs raw path source saved scratch pending ctx) (.inr r) ↔
      ∃ move rest, (parseMoveRun raw).1 = some (move, rest) ∧
        (PositionedRotationMachine.phaseResult (Λ := PositionCallerLabel Λ) (.seek move.direction)
          regs
          { source := source, saved := saved, scratch := scratch, pending := pending,
            path := move.position ++ path }
          (positionContext { certificate := rest } ctx)).l =
            some (PositionedRotationMachine.resultLabel r) := by
  constructor
  · intro first
    have returned := (run_firstResult_iff caller raw path source saved scratch pending regs ctx (.inr r)).mp first
    cases parsed : (parseMoveRun raw).1 with
    | none =>
        rw [runResult_of_none caller raw path source saved scratch pending regs ctx parsed] at returned
        simp [cfg, resultLabel, parseFailure] at returned
    | some pair =>
        rcases pair with ⟨move, rest⟩
        rw [runResult_of_some caller raw move rest path source saved scratch pending regs ctx parsed] at returned
        refine ⟨move, rest, rfl, ?_⟩
        exact (position_result_label_iff (.seek move.direction)
          (parsedData move rest (entryData raw path source saved scratch pending)) regs ctx r).mp returned
  · rintro ⟨move, rest, parsed, returned⟩
    apply (run_firstResult_iff caller raw path source saved scratch pending regs ctx (.inr r)).mpr
    rw [runResult_of_some caller raw move rest path source saved scratch pending regs ctx parsed]
    exact (position_result_label_iff (.seek move.direction)
      (parsedData move rest (entryData raw path source saved scratch pending)) regs ctx r).mpr returned

theorem first_rotationFailure_iff (raw : Word) (path : List Branch)
    (source saved scratch : Word) (pending : List Unit)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    FirstResult caller (entry regs raw path source saved scratch pending ctx) rotationFailure ↔
      ∃ move rest, (parseMoveRun raw).1 = some (move, rest) ∧
        (PositionedRotationMachine.phaseResult (Λ := PositionCallerLabel Λ) (.seek move.direction)
          regs
          { source := source, saved := saved, scratch := scratch, pending := pending,
            path := move.position ++ path }
          (positionContext { certificate := rest } ctx)).l =
            some (PositionedRotationMachine.resultLabel .failure) :=
  first_rotation_result_iff caller raw path source saved scratch pending regs ctx .failure

theorem first_success_iff (raw : Word) (path : List Branch)
    (source saved scratch : Word) (pending : List Unit)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    FirstResult caller (entry regs raw path source saved scratch pending ctx) success ↔
      ∃ move rest, (parseMoveRun raw).1 = some (move, rest) ∧
        (PositionedRotationMachine.phaseResult (Λ := PositionCallerLabel Λ) (.seek move.direction)
          regs
          { source := source, saved := saved, scratch := scratch, pending := pending,
            path := move.position ++ path }
          (positionContext { certificate := rest } ctx)).l =
            some (PositionedRotationMachine.resultLabel .success) :=
  first_rotation_result_iff caller raw path source saved scratch pending regs ctx .success

/-! ### Complete Position segments on the same physical parser stores -/

theorem position_segment_localRun
    (localCaller : PositionedRotationMachine.External (PositionCallerLabel Λ) → PositionStatement Γ Λ R)
    (D : LocalData) (ctx : ∀ k, List (Γ k))
    {n : Nat} {beforeLabel afterLabel : Option (PositionedRotationMachine.Label (PositionCallerLabel Λ))}
    {beforeRegs afterRegs : Registers R} {beforeData afterData : PositionedRotationMachine.LocalData}
    (run : PositionedRotationMachine.LocalRun localCaller n
      (PositionedRotationMachine.cfg beforeLabel beforeRegs beforeData (positionContext D ctx))
      (PositionedRotationMachine.cfg afterLabel afterRegs afterData (positionContext D ctx))) :
    LocalRun caller n
      (cfg (beforeLabel.map positionLabelEquiv) beforeRegs (setPositionData D beforeData) ctx)
      (cfg (afterLabel.map positionLabelEquiv) afterRegs (setPositionData D afterData) ctx) := by
  have transported := position_localRun_transport caller localCaller run
  rw [positionCfg_setPositionData beforeLabel beforeRegs D beforeData ctx,
    positionCfg_setPositionData afterLabel afterRegs D afterData ctx] at transported
  exact transported

/-- The represented suffix is the actual parsed segment, paid dispatch and Position LocalRun. -/
theorem run_code_represented_localRun (move : RotationMove) (certificateRest : Word)
    (oldPath : List Branch) (s : BinaryTree Unit) (saved suffix : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (representedSteps move oldPath s saved)
      (entry regs (moveCode move ++ certificateRest) oldPath (treeCode s ++ suffix) saved [] [] ctx)
      (cfg (some (resultLabel (representedResult move oldPath s))) (reset regs)
        (representedFinalData move certificateRest oldPath s saved suffix) ctx) := by
  let D : LocalData := { certificate := certificateRest }
  let localCaller : PositionedRotationMachine.External (PositionCallerLabel Λ) → PositionStatement Γ Λ R :=
    fun _ => .halt
  have positionRun := PositionedRotationMachine.run_code_localRun localCaller move.direction
    (move.position ++ oldPath) s saved suffix (reset regs) (positionContext D ctx)
  have last := position_segment_localRun caller localCaller D ctx positionRun
  have first := paid_position_code_localRun caller move certificateRest oldPath
    (treeCode s ++ suffix) saved [] [] regs ctx
  have joined := LocalRun.trans caller first last
  cases actual : (applyMoveRun ⟨move.direction, move.position ++ oldPath⟩ s).1 <;>
    simpa [representedSteps, representedFinalData, representedSource, representedResult,
      representedValue, physicalMove, PositionedRotationMachine.sourceResult, success, rotationFailure,
      D, setPositionData, Option.map_some, positionLabelEquiv_phase, positionLabelEquiv_result,
      reset, PositionedRotationMachine.reset, actual, Nat.add_assoc] using joined

include caller in
theorem represented_run_data (move : RotationMove) (certificateRest : Word)
    (oldPath : List Branch) (s : BinaryTree Unit) (saved suffix : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    runSteps (moveCode move ++ certificateRest) oldPath (treeCode s ++ suffix) saved [] [] =
        representedSteps move oldPath s saved ∧
      runResult (Λ := Λ) regs (moveCode move ++ certificateRest) oldPath
        (treeCode s ++ suffix) saved [] [] ctx =
        cfg (some (resultLabel (representedResult move oldPath s))) (reset regs)
          (representedFinalData move certificateRest oldPath s saved suffix) ctx :=
  LocalRun.phaseEndpoint caller (q := movePhase .start)
    (run_code_represented_localRun caller move certificateRest oldPath s saved suffix regs ctx)

include caller in
/-- Both represented outcomes have the same actual source-store length, including the restored saved prefix. -/
theorem represented_run_source_length (move : RotationMove) (certificateRest : Word)
    (oldPath : List Branch) (s : BinaryTree Unit) (saved suffix : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ((runResult (Λ := Λ) regs (moveCode move ++ certificateRest) oldPath
      (treeCode s ++ suffix) saved [] [] ctx).stk (.inl .source)).length =
      saved.length + 2 * s.numNodes + 1 + suffix.length := by
  rw [(represented_run_data caller move certificateRest oldPath s saved suffix regs ctx).2]
  exact representedFinalData_source_length move certificateRest oldPath s saved suffix

theorem run_code_represented (move : RotationMove) (certificateRest : Word)
    (oldPath : List Branch) (s : BinaryTree Unit) (saved suffix : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (next caller)^[representedSteps move oldPath s saved]
      (some (entry regs (moveCode move ++ certificateRest) oldPath
        (treeCode s ++ suffix) saved [] [] ctx)) =
      some (cfg (some (resultLabel (representedResult move oldPath s))) (reset regs)
        (representedFinalData move certificateRest oldPath s saved suffix) ctx) :=
  LocalRun.iterate caller
    (run_code_represented_localRun caller move certificateRest oldPath s saved suffix regs ctx)

def representedInTime (move : RotationMove) (certificateRest : Word)
    (oldPath : List Branch) (s : BinaryTree Unit) (saved suffix : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller)
      (entry regs (moveCode move ++ certificateRest) oldPath (treeCode s ++ suffix) saved [] [] ctx)
      (some (cfg (some (resultLabel (representedResult move oldPath s))) (reset regs)
        (representedFinalData move certificateRest oldPath s saved suffix) ctx))
      (representedSteps move oldPath s saved) where
  steps := representedSteps move oldPath s saved
  evals_in_steps := run_code_represented caller move certificateRest oldPath s saved suffix regs ctx
  steps_le_m := Nat.le_refl _

theorem represented_first_success_iff (move : RotationMove) (certificateRest : Word)
    (oldPath : List Branch) (s : BinaryTree Unit) (saved suffix : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    FirstResult caller
      (entry regs (moveCode move ++ certificateRest) oldPath (treeCode s ++ suffix) saved [] [] ctx)
      success ↔ ∃ t, representedValue move oldPath s = some t := by
  rw [run_firstResult_iff,
    (represented_run_data caller move certificateRest oldPath s saved suffix regs ctx).2]
  simpa only [cfg, resultLabel, Option.some.injEq, Sum.inr.injEq, Sum.inl.injEq] using
    representedResult_success_iff move oldPath s

theorem represented_first_failure_iff (move : RotationMove) (certificateRest : Word)
    (oldPath : List Branch) (s : BinaryTree Unit) (saved suffix : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    FirstResult caller
      (entry regs (moveCode move ++ certificateRest) oldPath (treeCode s ++ suffix) saved [] [] ctx)
      rotationFailure ↔ representedValue move oldPath s = none := by
  rw [run_firstResult_iff,
    (represented_run_data caller move certificateRest oldPath s saved suffix regs ctx).2]
  simpa only [cfg, resultLabel, Option.some.injEq, Sum.inr.injEq, Sum.inl.injEq] using
    representedResult_failure_iff move oldPath s

include caller in
theorem represented_complete_output_success_iff (move : RotationMove)
    (certificateRest outputCertificate : Word) (oldPath : List Branch)
    (s t : BinaryTree Unit) (saved suffix outputSuffix : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    runResult (Λ := Λ) regs (moveCode move ++ certificateRest) oldPath
        (treeCode s ++ suffix) saved [] [] ctx =
      cfg (some (resultLabel success)) (reset regs)
        { certificate := outputCertificate, source := saved.reverse ++ treeCode t ++ outputSuffix } ctx ↔
      representedValue move oldPath s = some t ∧
        certificateRest = outputCertificate ∧ suffix = outputSuffix := by
  rw [(represented_run_data caller move certificateRest oldPath s saved suffix regs ctx).2]
  constructor
  · intro endpoint
    have label := congrArg (fun c : Cfg Γ Λ R => c.l) endpoint
    have certificate := congrArg (fun c : Cfg Γ Λ R => (dataOfCfg c).certificate) endpoint
    have source := congrArg (fun c : Cfg Γ Λ R => (dataOfCfg c).source) endpoint
    have certificateEq : certificateRest = outputCertificate := certificate
    have sourceEq : representedSource move oldPath s saved suffix =
        saved.reverse ++ treeCode t ++ outputSuffix := source
    cases actual : representedValue move oldPath s with
    | none =>
        simp [representedResult, actual, cfg, resultLabel, success, rotationFailure] at label
    | some u =>
        have unique := representedSource_success_injective move oldPath s u t
          saved suffix outputSuffix actual sourceEq
        exact ⟨congrArg some unique.1, certificateEq, unique.2⟩
  · rintro ⟨returned, rfl, rfl⟩
    rw [representedResult_of_some move oldPath s t returned,
      representedFinalData_of_some move certificateRest oldPath s t saved suffix returned]

theorem represented_success_localRun_iff (move : RotationMove)
    (certificateRest outputCertificate : Word) (oldPath : List Branch)
    (s t : BinaryTree Unit) (saved suffix outputSuffix : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) (n : Nat) :
    LocalRun caller n
      (entry regs (moveCode move ++ certificateRest) oldPath (treeCode s ++ suffix) saved [] [] ctx)
      (cfg (some (resultLabel success)) (reset regs)
        { certificate := outputCertificate, source := saved.reverse ++ treeCode t ++ outputSuffix } ctx) ↔
      representedValue move oldPath s = some t ∧ certificateRest = outputCertificate ∧
        suffix = outputSuffix ∧ n = representedSteps move oldPath s saved := by
  constructor
  · intro run
    have endpoint := LocalRun.phaseEndpoint caller (q := movePhase .start) run
    have output := (represented_complete_output_success_iff caller move certificateRest outputCertificate
      oldPath s t saved suffix outputSuffix regs ctx).mp endpoint.2
    exact ⟨output.1, output.2.1, output.2.2,
      endpoint.1.symm.trans (represented_run_data caller move certificateRest oldPath s saved suffix regs ctx).1⟩
  · rintro ⟨returned, rfl, rfl, rfl⟩
    have run := run_code_represented_localRun caller move certificateRest oldPath s saved suffix regs ctx
    rw [representedResult_of_some move oldPath s t returned,
      representedFinalData_of_some move certificateRest oldPath s t saved suffix returned] at run
    exact run

theorem represented_first_success_complete (move : RotationMove)
    (certificateRest outputCertificate : Word) (oldPath : List Branch)
    (s t : BinaryTree Unit) (saved suffix outputSuffix : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) (n : Nat)
    (executed : (next caller)^[n]
      (some (entry regs (moveCode move ++ certificateRest) oldPath (treeCode s ++ suffix) saved [] [] ctx)) =
      some (cfg (some (resultLabel success)) (reset regs)
        { certificate := outputCertificate, source := saved.reverse ++ treeCode t ++ outputSuffix } ctx))
    (earlier : ∀ j, j < n → ∃ before,
      (next caller)^[j]
        (some (entry regs (moveCode move ++ certificateRest) oldPath (treeCode s ++ suffix) saved [] [] ctx)) =
        some before ∧ Owned before.l) :
    representedValue move oldPath s = some t ∧ certificateRest = outputCertificate ∧
      suffix = outputSuffix ∧ n = representedSteps move oldPath s saved :=
  (represented_success_localRun_iff caller move certificateRest outputCertificate oldPath s t
    saved suffix outputSuffix regs ctx n).mp (LocalRun.of_iterate caller executed earlier)

include caller in
theorem represented_success_semantics (move : RotationMove) (certificateRest : Word)
    (oldPath : List Branch) (s t : BinaryTree Unit) (saved suffix : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (endpoint : runResult (Λ := Λ) regs (moveCode move ++ certificateRest) oldPath
      (treeCode s ++ suffix) saved [] [] ctx =
      cfg (some (resultLabel success)) (reset regs)
        { certificate := certificateRest, source := saved.reverse ++ treeCode t ++ suffix } ctx) :
    Trees.Rotations.applyMove? (physicalMove move oldPath) s = some t ∧
      t.numNodes = s.numNodes ∧
      (applyMoveRun (physicalMove move oldPath) s).2 = 3 * (move.position ++ oldPath).length + 5 ∧
      (saved.reverse ++ treeCode t ++ suffix).length =
        saved.length + 2 * s.numNodes + 1 + suffix.length := by
  have returned := ((represented_complete_output_success_iff caller move certificateRest certificateRest
    oldPath s t saved suffix suffix regs ctx).mp endpoint).1
  have nodes := representedValue_numNodes move oldPath s t returned
  refine ⟨(representedValue_eq_applyMove move oldPath s).symm.trans returned,
    nodes, source_application_cost_of_some move oldPath s t returned, ?_⟩
  simp only [List.length_append, List.length_reverse, treeCode_length, nodes, Nat.add_assoc]

/-! ### Linear bounds retain the same actual exact execution count -/

theorem runSteps_le_of_some (raw : Word) (move : RotationMove) (rest : Word)
    (path : List Branch) (source saved scratch : Word) (pending : List Unit)
    (parsed : (parseMoveRun raw).1 = some (move, rest)) :
    runSteps raw path source saved scratch pending ≤
      3 * source.length + saved.length + scratch.length + pending.length +
        3 * move.position.length + path.length + 9 := by
  rw [runSteps_of_some raw move rest path source saved scratch pending parsed,
    MoveParserMachine.fullSteps_of_some raw move rest parsed]
  have bound := PositionedRotationMachine.phaseSteps_le_countdown (.seek move.direction)
    { source := source, saved := saved, scratch := scratch, pending := pending,
      path := move.position ++ path }
  simp only [PositionedRotationMachine.countdown, List.length_append] at bound
  omega

theorem runSteps_le (raw : Word) (path : List Branch)
    (source saved scratch : Word) (pending : List Unit) :
    runSteps raw path source saved scratch pending ≤
      3 * raw.length + 3 * source.length + saved.length + scratch.length +
        pending.length + path.length + 3 := by
  cases parsed : (parseMoveRun raw).1 with
  | none =>
      rw [runSteps_of_none raw path source saved scratch pending parsed]
      have bound := MoveParserMachine.fullSteps_le raw
      omega
  | some pair =>
      rcases pair with ⟨move, rest⟩
      have bound := runSteps_le_of_some raw move rest path source saved scratch pending parsed
      have length := parseMoveRun_consumed_length raw move rest parsed
      omega

def runInLinearTime (raw : Word) (path : List Branch)
    (source saved scratch : Word) (pending : List Unit)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller)
      (entry regs raw path source saved scratch pending ctx)
      (some (runResult regs raw path source saved scratch pending ctx))
      (3 * raw.length + 3 * source.length + saved.length + scratch.length +
        pending.length + path.length + 3) where
  steps := runSteps raw path source saved scratch pending
  evals_in_steps := (runInTimeExact caller raw path source saved scratch pending regs ctx).evals_in_steps
  steps_le_m := runSteps_le raw path source saved scratch pending

def parsedRunInLinearTime (raw : Word) (move : RotationMove) (rest : Word)
    (path : List Branch) (source saved scratch : Word) (pending : List Unit)
    (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (parsed : (parseMoveRun raw).1 = some (move, rest)) :
    StateTransition.EvalsToInTime (step caller)
      (entry regs raw path source saved scratch pending ctx)
      (some (runResult regs raw path source saved scratch pending ctx))
      (3 * source.length + saved.length + scratch.length + pending.length +
        3 * move.position.length + path.length + 9) where
  steps := runSteps raw path source saved scratch pending
  evals_in_steps := (runInTimeExact caller raw path source saved scratch pending regs ctx).evals_in_steps
  steps_le_m := runSteps_le_of_some raw move rest path source saved scratch pending parsed

/-! ### Component timing retains the real internal reset boundary -/

def movePhaseInTime (q : MoveParserMachine.Phase) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller)
      (cfg (some (moveLabel q)) regs D ctx)
      (some (cfg (some (dispatchLabel (moveFinish q D).result)) (resetMove regs)
        (moveFinish q D).data ctx))
      (MoveParserMachine.phaseSteps q D.certificate D.moveReverse) where
  steps := MoveParserMachine.phaseSteps q D.certificate D.moveReverse
  evals_in_steps := LocalRun.iterate caller (move_phase_localRun caller q D regs ctx)
  steps_le_m := Nat.le_refl _

def dispatchInTime (r : MoveParserMachine.Result) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller)
      (cfg (some (dispatchLabel r)) regs D ctx)
      (some (cfg (some (dispatchTarget r)) (reset regs) D ctx)) 1 where
  steps := 1
  evals_in_steps := LocalRun.iterate caller (dispatch_localRun caller r D regs ctx)
  steps_le_m := Nat.le_refl _

def positionPhaseInTime (q : PositionedRotationMachine.Phase) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller)
      (cfg (some (positionLabel q)) regs D ctx)
      (some (phaseResult (positionPhase q) regs D ctx))
      (PositionedRotationMachine.phaseSteps q (positionData D)) where
  steps := PositionedRotationMachine.phaseSteps q (positionData D)
  evals_in_steps := LocalRun.iterate caller (position_phase_localRun caller q D regs ctx)
  steps_le_m := Nat.le_refl _

/-! ### Complete raw-word behavior after one successful parse -/

/-- Raw Position failure restores its tree input after the certificate has actually been consumed. -/
theorem run_raw (move : RotationMove) (certificateRest : Word) (oldPath : List Branch)
    (source : Word) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ∃ result output rest,
      LocalRun caller
        (2 * move.position.length + 4 +
          PositionedRotationMachine.runSteps move.direction source (move.position ++ oldPath))
        (entry regs (moveCode move ++ certificateRest) oldPath source [] [] [] ctx)
        (cfg (some (resultLabel (.inr result))) (reset regs)
          { certificate := certificateRest, source := output, path := rest } ctx) ∧
      output.length = source.length ∧
      (∃ consumed, move.position ++ oldPath = consumed ++ rest) ∧
      (result = .failure → output = source) ∧ (result = .success → rest = []) := by
  let D : LocalData := { certificate := certificateRest }
  let localCaller : PositionedRotationMachine.External (PositionCallerLabel Λ) →
      PositionStatement Γ Λ R := fun _ => .halt
  obtain ⟨result, output, rest, run, length, path, failed, succeeded⟩ :=
    PositionedRotationMachine.run_raw localCaller move.direction source
      (move.position ++ oldPath) (reset regs) (positionContext D ctx)
  have transported := position_segment_localRun caller localCaller D ctx run
  have paid := paid_position_code_localRun caller move certificateRest oldPath source [] [] [] regs ctx
  have joined := LocalRun.trans caller paid transported
  refine ⟨result, output, rest, ?_, length, path, failed, succeeded⟩
  simpa only [D, setPositionData, Option.map_some, positionLabelEquiv_phase,
    positionLabelEquiv_result, position_reset_reset] using joined

include caller in
/-- Canonical raw endpoints retain length and the physically unvisited path suffix. -/
theorem run_raw_data (move : RotationMove) (certificateRest : Word) (oldPath : List Branch)
    (source : Word) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ∃ result output rest,
      runResult (Λ := Λ) regs (moveCode move ++ certificateRest) oldPath source [] [] [] ctx =
        cfg (some (resultLabel (.inr result))) (reset regs)
          { certificate := certificateRest, source := output, path := rest } ctx ∧
      output.length = source.length ∧
      (∃ consumed, move.position ++ oldPath = consumed ++ rest) ∧
      (result = .failure → output = source) ∧ (result = .success → rest = []) := by
  obtain ⟨result, output, rest, run, length, path, failed, succeeded⟩ :=
    run_raw caller move certificateRest oldPath source regs ctx
  exact ⟨result, output, rest, (LocalRun.phaseEndpoint caller (q := movePhase .start) run).2,
    length, path, failed, succeeded⟩

/-! ### Root recognition on arbitrary literal suffixes -/

theorem root_left_pattern_localRun (A : BinaryTree Unit) (suffix saved certificateRest : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (2 * (treeCode A).length + 9 + saved.length)
      (entry regs (moveCode ⟨.left, []⟩ ++ certificateRest) []
        (nodeTag :: (treeCode A ++ nodeTag :: suffix)) saved [] [] ctx)
      (cfg (some (resultLabel success)) (reset regs)
        { certificate := certificateRest,
          source := saved.reverse ++ [nodeTag, nodeTag] ++ treeCode A ++ suffix } ctx) := by
  let D : LocalData := { certificate := certificateRest }
  let localCaller : PositionedRotationMachine.External (PositionCallerLabel Λ) →
      PositionStatement Γ Λ R := fun _ => .halt
  have run := PositionedRotationMachine.root_left_pattern_localRun localCaller A suffix saved
    (reset regs) (positionContext D ctx)
  have transported := position_segment_localRun caller localCaller D ctx run
  have paid := paid_position_code_localRun caller ⟨.left, []⟩ certificateRest []
    (nodeTag :: (treeCode A ++ nodeTag :: suffix)) saved [] [] regs ctx
  have joined := LocalRun.trans caller paid transported
  convert joined using 1 <;>
    simp [D, setPositionData, success, Nat.add_assoc]; omega

theorem root_right_pattern_localRun (A : BinaryTree Unit) (suffix saved certificateRest : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (2 * (treeCode A).length + 8 + saved.length)
      (entry regs (moveCode ⟨.right, []⟩ ++ certificateRest) []
        (nodeTag :: nodeTag :: (treeCode A ++ suffix)) saved [] [] ctx)
      (cfg (some (resultLabel success)) (reset regs)
        { certificate := certificateRest,
          source := saved.reverse ++ [nodeTag] ++ treeCode A ++ nodeTag :: suffix } ctx) := by
  let D : LocalData := { certificate := certificateRest }
  let localCaller : PositionedRotationMachine.External (PositionCallerLabel Λ) →
      PositionStatement Γ Λ R := fun _ => .halt
  have run := PositionedRotationMachine.root_right_pattern_localRun localCaller A suffix saved
    (reset regs) (positionContext D ctx)
  have transported := position_segment_localRun caller localCaller D ctx run
  have paid := paid_position_code_localRun caller ⟨.right, []⟩ certificateRest []
    (nodeTag :: nodeTag :: (treeCode A ++ suffix)) saved [] [] regs ctx
  have joined := LocalRun.trans caller paid transported
  convert joined using 1 <;>
    simp [D, setPositionData, success, Nat.add_assoc]; omega

/-- A first success recognizes only the required root prefix, including malformed suffixes. -/
theorem root_left_first_success_iff (source saved certificateRest : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    FirstResult caller
      (entry regs (moveCode ⟨.left, []⟩ ++ certificateRest) [] source saved [] [] ctx) success ↔
      ∃ A : BinaryTree Unit, ∃ suffix : Word,
        source = nodeTag :: (treeCode A ++ nodeTag :: suffix) := by
  let localCaller : PositionedRotationMachine.External (PositionCallerLabel Λ) →
      PositionStatement Γ Λ R := fun _ => .halt
  rw [run_firstResult_iff, runResult_of_some caller _ ⟨.left, []⟩ certificateRest
    [] source saved [] [] regs ctx (congrArg Prod.fst (parseMoveRun_code ⟨.left, []⟩ certificateRest))]
  change (phaseResult (positionPhase (.seek .left)) regs
    { certificate := certificateRest, source := source, saved := saved } ctx).l =
      some (resultLabel (.inr .success)) ↔ _
  rw [position_result_label_iff]
  exact PositionedRotationMachine.root_left_phaseResult_success_iff localCaller source saved regs
    (positionContext { certificate := certificateRest } ctx)

theorem root_right_first_success_iff (source saved certificateRest : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    FirstResult caller
      (entry regs (moveCode ⟨.right, []⟩ ++ certificateRest) [] source saved [] [] ctx) success ↔
      ∃ A : BinaryTree Unit, ∃ suffix : Word,
        source = nodeTag :: nodeTag :: (treeCode A ++ suffix) := by
  let localCaller : PositionedRotationMachine.External (PositionCallerLabel Λ) →
      PositionStatement Γ Λ R := fun _ => .halt
  rw [run_firstResult_iff, runResult_of_some caller _ ⟨.right, []⟩ certificateRest
    [] source saved [] [] regs ctx (congrArg Prod.fst (parseMoveRun_code ⟨.right, []⟩ certificateRest))]
  change (phaseResult (positionPhase (.seek .right)) regs
    { certificate := certificateRest, source := source, saved := saved } ctx).l =
      some (resultLabel (.inr .success)) ↔ _
  rw [position_result_label_iff]
  exact PositionedRotationMachine.root_right_phaseResult_success_iff localCaller source saved regs
    (positionContext { certificate := certificateRest } ctx)

/-! ### An arbitrary certificate's complete represented first-success converse -/

include caller in
theorem represented_output_success_iff (raw outputCertificate : Word) (oldPath : List Branch)
    (s t : BinaryTree Unit) (saved suffix outputSuffix : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    runResult (Λ := Λ) regs raw oldPath (treeCode s ++ suffix) saved [] [] ctx =
      cfg (some (resultLabel success)) (reset regs)
        { certificate := outputCertificate, source := saved.reverse ++ treeCode t ++ outputSuffix } ctx ↔
      ∃ move, (parseMoveRun raw).1 = some (move, outputCertificate) ∧
        representedValue move oldPath s = some t ∧ suffix = outputSuffix := by
  constructor
  · intro endpoint
    cases parsed : (parseMoveRun raw).1 with
    | none =>
        rw [runResult_of_none caller raw oldPath (treeCode s ++ suffix) saved [] [] regs ctx parsed] at endpoint
        have label := congrArg (fun c : Cfg Γ Λ R => c.l) endpoint
        cases label
    | some pair =>
        rcases pair with ⟨move, rest⟩
        have word := (parseMoveRun_iff raw move rest).mp parsed
        rw [word] at endpoint
        obtain ⟨returned, restEq, suffixEq⟩ :=
          (represented_complete_output_success_iff caller move rest outputCertificate oldPath
            s t saved suffix outputSuffix regs ctx).mp endpoint
        exact ⟨move, by simp only [restEq], returned, suffixEq⟩
  · rintro ⟨move, parsed, returned, suffixEq⟩
    rw [(parseMoveRun_iff raw move outputCertificate).mp parsed]
    exact (represented_complete_output_success_iff caller move outputCertificate outputCertificate
      oldPath s t saved suffix outputSuffix regs ctx).mpr ⟨returned, rfl, suffixEq⟩

theorem represented_raw_first_success_iff (raw : Word) (oldPath : List Branch)
    (s : BinaryTree Unit) (saved suffix : Word) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    FirstResult caller (entry regs raw oldPath (treeCode s ++ suffix) saved [] [] ctx) success ↔
      ∃ move rest t, (parseMoveRun raw).1 = some (move, rest) ∧
        representedValue move oldPath s = some t := by
  constructor
  · intro first
    obtain ⟨move, rest, parsed, _⟩ :=
      (first_success_iff caller raw oldPath (treeCode s ++ suffix) saved [] [] regs ctx).mp first
    have word := (parseMoveRun_iff raw move rest).mp parsed
    rw [word] at first
    obtain ⟨t, returned⟩ :=
      (represented_first_success_iff caller move rest oldPath s saved suffix regs ctx).mp first
    exact ⟨move, rest, t, parsed, returned⟩
  · rintro ⟨move, rest, t, parsed, returned⟩
    rw [(parseMoveRun_iff raw move rest).mp parsed]
    exact (represented_first_success_iff caller move rest oldPath s saved suffix regs ctx).mpr
      ⟨t, returned⟩

theorem represented_raw_first_success_complete (raw outputCertificate : Word)
    (oldPath : List Branch) (s t : BinaryTree Unit) (saved suffix outputSuffix : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) (n : Nat)
    (executed : (next caller)^[n]
      (some (entry regs raw oldPath (treeCode s ++ suffix) saved [] [] ctx)) =
      some (cfg (some (resultLabel success)) (reset regs)
        { certificate := outputCertificate, source := saved.reverse ++ treeCode t ++ outputSuffix } ctx))
    (earlier : ∀ j, j < n → ∃ before,
      (next caller)^[j] (some (entry regs raw oldPath (treeCode s ++ suffix) saved [] [] ctx)) =
        some before ∧ Owned before.l) :
    ∃ move, (parseMoveRun raw).1 = some (move, outputCertificate) ∧
      representedValue move oldPath s = some t ∧ suffix = outputSuffix ∧
      n = representedSteps move oldPath s saved := by
  have run := LocalRun.of_iterate caller executed earlier
  have endpoint := LocalRun.phaseEndpoint caller (q := movePhase .start) run
  obtain ⟨move, parsed, returned, suffixEq⟩ :=
    (represented_output_success_iff caller raw outputCertificate oldPath s t saved suffix outputSuffix regs ctx).mp
      endpoint.2
  refine ⟨move, parsed, returned, suffixEq, ?_⟩
  have word := (parseMoveRun_iff raw move outputCertificate).mp parsed
  rw [word] at endpoint
  exact endpoint.1.symm.trans
    (represented_run_data caller move outputCertificate oldPath s saved suffix regs ctx).1

theorem represented_raw_first_success_unique (raw outputCertificate : Word)
    (oldPath : List Branch) (s t : BinaryTree Unit) (saved suffix outputSuffix : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) (n : Nat)
    (executed : (next caller)^[n]
      (some (entry regs raw oldPath (treeCode s ++ suffix) saved [] [] ctx)) =
      some (cfg (some (resultLabel success)) (reset regs)
        { certificate := outputCertificate, source := saved.reverse ++ treeCode t ++ outputSuffix } ctx))
    (earlier : ∀ j, j < n → ∃ before,
      (next caller)^[j] (some (entry regs raw oldPath (treeCode s ++ suffix) saved [] [] ctx)) =
        some before ∧ Owned before.l) :
    ∃ move, (parseMoveRun raw).1 = some (move, outputCertificate) ∧
      representedValue move oldPath s = some t ∧ suffix = outputSuffix ∧
      n = representedSteps move oldPath s saved ∧
      ∀ other otherRest, (parseMoveRun raw).1 = some (other, otherRest) →
        other = move ∧ otherRest = outputCertificate := by
  obtain ⟨move, parsed, returned, suffixEq, count⟩ :=
    represented_raw_first_success_complete caller raw outputCertificate oldPath s t saved suffix
      outputSuffix regs ctx n executed earlier
  exact ⟨move, parsed, returned, suffixEq, count,
    fun other otherRest observed => parsed_prefix_unique raw other move otherRest outputCertificate observed parsed⟩

/-! ### Actual segment composition for later inclusive prefixes -/

theorem prefix_iterate_after_localRun {start middle : Cfg Γ Λ R} {first : Nat}
    (segment : LocalRun caller first start middle) (n : Nat) (after : first ≤ n)
    (reached : Cfg Γ Λ R) (executed : (next caller)^[n] (some start) = some reached) :
    (next caller)^[n - first] (some middle) = some reached := by
  have split : n = (n - first) + first := by omega
  rw [split, Function.iterate_add_apply, LocalRun.iterate caller segment] at executed
  exact executed

/-! ### Principal physical bounds keep all seven stores -/

section PrincipalSpace
variable [Fintype K]

def principalCells (raw : Word) (path : List Branch) (source saved scratch : Word)
    (pending : List Unit) (ctx : ∀ k, List (Γ k)) : Nat :=
  raw.length + path.length + source.length + saved.length + scratch.length + pending.length +
    contextCells ctx

def parsedCellsBound (move : RotationMove) (rest : Word) (path : List Branch)
    (source saved scratch : Word) (pending : List Unit) (ctx : ∀ k, List (Γ k)) : Nat :=
  rest.length + move.position.length + path.length + 2 * source.length + saved.length +
    scratch.length + pending.length + contextCells ctx

omit [DecidableEq K] in
theorem initial_stackCells (raw : Word) (path : List Branch) (source saved scratch : Word)
    (pending : List Unit) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    stackCells (entry (Λ := Λ) regs raw path source saved scratch pending ctx) =
      principalCells raw path source saved scratch pending ctx := by
  rw [entry, stackCells_cfg]
  rfl

omit [DecidableEq K] in
theorem entry_potential (raw : Word) (path : List Branch) (source saved scratch : Word)
    (pending : List Unit) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    potential (entry (Λ := Λ) regs raw path source saved scratch pending ctx) =
      principalCells raw path source saved scratch pending ctx + source.length := by
  change potential (cfg (some (phaseLabel (movePhase .start))) regs
    (entryData raw path source saved scratch pending) ctx) = _
  rw [potential_phase_cfg]
  simp only [localCells, entryData, phaseDebt, movePhase, MoveParserMachine.phaseDebt,
    phaseCredit, principalCells, List.length_nil]
  omega

omit [DecidableEq K] in
theorem parsed_entry_potential (move : RotationMove) (rest : Word) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    potential (cfg (some (positionLabel (Λ := Λ) (.seek move.direction))) regs
      (parsedData move rest D) ctx) =
      parsedCellsBound move rest D.path D.source D.saved D.scratch D.pending ctx := by
  change potential (cfg (some (phaseLabel (positionPhase (.seek move.direction)))) regs
    (parsedData move rest D) ctx) = _
  rw [potential_phase_cfg]
  simp only [parsedCellsBound, localCells, parsedData, phaseDebt, positionPhase, phaseCredit,
    PositionedRotationMachine.phaseDebt, PositionedRotationMachine.phaseCredit, positionData,
    List.length_append, List.length_nil]
  omega

theorem prefix_stackCells_le (raw : Word) (path : List Branch) (source saved scratch : Word)
    (pending : List Unit) (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (n : Nat) (bound : n ≤ runSteps raw path source saved scratch pending)
    (reached : Cfg Γ Λ R)
    (executed : (next caller)^[n] (some (entry regs raw path source saved scratch pending ctx)) = some reached) :
    stackCells reached ≤ principalCells raw path source saved scratch pending ctx + source.length := by
  have cells := prefix_stackCells_le_dirty caller
    (entry regs raw path source saved scratch pending ctx) n bound reached executed
  simpa only [entry_potential] using cells

theorem prefix_stackCells_le_after_localRun {start middle : Cfg Γ Λ R} {first : Nat}
    (segment : LocalRun caller first start middle) (n : Nat)
    (bound : n ≤ remainingSteps start) (after : first ≤ n)
    (reached : Cfg Γ Λ R) (executed : (next caller)^[n] (some start) = some reached) :
    stackCells reached ≤ potential middle := by
  have suffixBound : n - first ≤ remainingSteps middle := by
    have rank := LocalRun.remaining caller segment
    omega
  exact prefix_stackCells_le_dirty caller middle (n - first) suffixBound reached
    (prefix_iterate_after_localRun caller segment n after reached executed)

/-- The parser segment has no tree credit charge: its full physical cell bound is the initial sum. -/
theorem parser_prefix_stackCells_le (raw : Word) (path : List Branch) (source saved scratch : Word)
    (pending : List Unit) (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (n : Nat) (bound : n ≤ MoveParserMachine.fullSteps raw) (reached : Cfg Γ Λ R)
    (executed : (next caller)^[n] (some (entry regs raw path source saved scratch pending ctx)) = some reached) :
    stackCells reached ≤ principalCells raw path source saved scratch pending ctx := by
  let D := entryData raw path source saved scratch pending
  let localCaller : MoveParserMachine.External (MoveCallerLabel Λ) → MoveStatement Γ Λ R := fun _ => .halt
  let localStart : MoveCfg Γ Λ R :=
    MoveParserMachine.entry (moveRegisterEquiv.symm regs) raw path (moveContext D ctx)
  have startEq : moveCfg localStart = entry regs raw path source saved scratch pending ctx := by
    change moveCfg (moveView (some (MoveParserMachine.phaseLabel .start))
      (moveRegisterEquiv.symm regs) D ctx) = _
    rw [moveCfg_view]
    simp only [Option.map_some, moveLabelEquiv_phase, Equiv.apply_symm_apply]
    rfl
  obtain ⟨localReached, localRun, _, _, _, _⟩ :=
    MoveParserMachine.run_prefix localCaller raw path (moveRegisterEquiv.symm regs) (moveContext D ctx) n bound
  have earlier := (MoveParserMachine.run_first_return localCaller raw path
    (moveRegisterEquiv.symm regs) (moveContext D ctx)).2
  have transported := move_prefix_transport caller localCaller n localStart
    (fun j strict => earlier j (by omega))
  change (next caller)^[n] (some (moveCfg localStart)) =
    ((MoveParserMachine.next localCaller)^[n]
      (some (MoveParserMachine.entry (moveRegisterEquiv.symm regs) raw path (moveContext D ctx)))).map moveCfg
      at transported
  rw [localRun, Option.map_some, startEq] at transported
  have same : reached = moveCfg localReached := Option.some.inj (executed.symm.trans transported)
  rw [same, stackCells_moveCfg]
  have cells := MoveParserMachine.prefix_stackCells_le localCaller raw path
    (moveRegisterEquiv.symm regs) (moveContext D ctx) n bound localReached localRun
  rw [moveContext_cells] at cells
  simpa only [D, entryData, principalCells, Nat.add_assoc] using cells

theorem prefix_stackCells_le_of_none (raw : Word) (path : List Branch) (source saved scratch : Word)
    (pending : List Unit) (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (failed : (parseMoveRun raw).1 = none) (n : Nat)
    (bound : n ≤ runSteps raw path source saved scratch pending) (reached : Cfg Γ Λ R)
    (executed : (next caller)^[n] (some (entry regs raw path source saved scratch pending ctx)) = some reached) :
    stackCells reached ≤ principalCells raw path source saved scratch pending ctx := by
  by_cases before : n ≤ MoveParserMachine.fullSteps raw
  · exact parser_prefix_stackCells_le caller raw path source saved scratch pending regs ctx n before reached executed
  · rw [runSteps_of_none raw path source saved scratch pending failed] at bound
    have count : n = MoveParserMachine.fullSteps raw + 1 := by omega
    have endpoint := run_of_none caller raw path source saved scratch pending regs ctx failed
    rw [← count, executed] at endpoint
    have same := Option.some.inj endpoint
    rw [same, stackCells_cfg]
    exact Nat.le_refl _

theorem prefix_stackCells_le_of_some (raw : Word) (move : RotationMove) (rest : Word)
    (path : List Branch) (source saved scratch : Word) (pending : List Unit)
    (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (parsed : (parseMoveRun raw).1 = some (move, rest)) (n : Nat)
    (bound : n ≤ runSteps raw path source saved scratch pending) (reached : Cfg Γ Λ R)
    (executed : (next caller)^[n] (some (entry regs raw path source saved scratch pending ctx)) = some reached) :
    stackCells reached ≤ max (principalCells raw path source saved scratch pending ctx)
      (parsedCellsBound move rest path source saved scratch pending ctx) := by
  by_cases before : n ≤ MoveParserMachine.fullSteps raw
  · exact (parser_prefix_stackCells_le caller raw path source saved scratch pending regs ctx
      n before reached executed).trans (Nat.le_max_left _ _)
  · have after : MoveParserMachine.fullSteps raw + 1 ≤ n := by omega
    have segment := paid_position_entry_localRun caller raw move rest path source saved scratch pending regs ctx parsed
    have cells := prefix_stackCells_le_after_localRun caller segment n bound after reached executed
    rw [parsed_entry_potential] at cells
    exact cells.trans (Nat.le_max_right _ _)

end PrincipalSpace

/-! ### Actual malformed-family runs, drops and ranks -/

theorem left_nodes_drop (certificateRest : Word) (n : Nat) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (2 * n + 6)
      (entry regs (moveCode ⟨.left, []⟩ ++ certificateRest) [] (List.replicate n nodeTag) [] [] [] ctx)
      (cfg (some (positionLabel .dropPending)) (reset regs)
        { certificate := certificateRest, source := List.replicate n nodeTag, pending := List.replicate n () } ctx) := by
  let localCaller : PositionedRotationMachine.External (PositionCallerLabel Λ) →
      PositionStatement Γ Λ R := fun _ => .halt
  have run := PositionedRotationMachine.left_nodes_drop localCaller n (reset regs)
    (positionContext { certificate := certificateRest } ctx)
  have transported := position_segment_localRun caller localCaller { certificate := certificateRest } ctx run
  have paid := paid_position_code_localRun caller ⟨.left, []⟩ certificateRest [] (List.replicate n nodeTag) [] [] [] regs ctx
  have joined := LocalRun.trans caller paid transported
  convert joined using 1 <;> simp [setPositionData]; omega

theorem right_nodes_drop (certificateRest : Word) (m : Nat) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (2 * m + 8)
      (entry regs (moveCode ⟨.right, []⟩ ++ certificateRest) [] (List.replicate (m + 2) nodeTag) [] [] [] ctx)
      (cfg (some (positionLabel .dropPending)) (reset regs)
        { certificate := certificateRest, source := List.replicate (m + 2) nodeTag, pending := List.replicate (m + 1) () } ctx) := by
  let localCaller : PositionedRotationMachine.External (PositionCallerLabel Λ) →
      PositionStatement Γ Λ R := fun _ => .halt
  have run := PositionedRotationMachine.right_nodes_drop localCaller m (reset regs)
    (positionContext { certificate := certificateRest } ctx)
  have transported := position_segment_localRun caller localCaller { certificate := certificateRest } ctx run
  have paid := paid_position_code_localRun caller ⟨.right, []⟩ certificateRest []
    (List.replicate (m + 2) nodeTag) [] [] [] regs ctx
  have joined := LocalRun.trans caller paid transported
  convert joined using 1 <;> simp [setPositionData]; omega

theorem left_nodes_run (certificateRest : Word) (n : Nat) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (3 * n + 8)
      (entry regs (moveCode ⟨.left, []⟩ ++ certificateRest) [] (List.replicate n nodeTag) [] [] [] ctx)
      (cfg (some (resultLabel rotationFailure)) (reset regs) { certificate := certificateRest, source := List.replicate n nodeTag } ctx) := by
  let localCaller : PositionedRotationMachine.External (PositionCallerLabel Λ) →
      PositionStatement Γ Λ R := fun _ => .halt
  have run := PositionedRotationMachine.left_nodes_run localCaller n (reset regs)
    (positionContext { certificate := certificateRest } ctx)
  have transported := position_segment_localRun caller localCaller { certificate := certificateRest } ctx run
  have paid := paid_position_code_localRun caller ⟨.left, []⟩ certificateRest [] (List.replicate n nodeTag) [] [] [] regs ctx
  have joined := LocalRun.trans caller paid transported
  convert joined using 1 <;> simp [setPositionData, rotationFailure]; omega

theorem right_nodes_run (certificateRest : Word) (m : Nat) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (3 * m + 11)
      (entry regs (moveCode ⟨.right, []⟩ ++ certificateRest) [] (List.replicate (m + 2) nodeTag) [] [] [] ctx)
      (cfg (some (resultLabel rotationFailure)) (reset regs)
        { certificate := certificateRest, source := List.replicate (m + 2) nodeTag } ctx) := by
  let localCaller : PositionedRotationMachine.External (PositionCallerLabel Λ) →
      PositionStatement Γ Λ R := fun _ => .halt
  have run := PositionedRotationMachine.right_nodes_run localCaller m (reset regs)
    (positionContext { certificate := certificateRest } ctx)
  have transported := position_segment_localRun caller localCaller { certificate := certificateRest } ctx run
  have paid := paid_position_code_localRun caller ⟨.right, []⟩ certificateRest []
    (List.replicate (m + 2) nodeTag) [] [] [] regs ctx
  have joined := LocalRun.trans caller paid transported
  convert joined using 1 <;> simp [setPositionData, rotationFailure]; omega

include caller in
theorem left_nodes_exact_clock (certificateRest : Word) (n : Nat) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    runSteps (moveCode ⟨.left, []⟩ ++ certificateRest) [] (List.replicate n nodeTag) [] [] [] = 3 * n + 8 :=
  (LocalRun.phaseEndpoint caller (q := movePhase .start) (left_nodes_run caller certificateRest n regs ctx)).1

include caller in
theorem right_nodes_exact_clock (certificateRest : Word) (m : Nat) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    runSteps (moveCode ⟨.right, []⟩ ++ certificateRest) [] (List.replicate (m + 2) nodeTag) [] [] [] = 3 * m + 11 :=
  (LocalRun.phaseEndpoint caller (q := movePhase .start) (right_nodes_run caller certificateRest m regs ctx)).1

include caller in
theorem left_nodes_drop_rank (certificateRest : Word) (n : Nat) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    remainingSteps (cfg (some (positionLabel .dropPending)) (reset regs)
      { certificate := certificateRest, source := List.replicate n nodeTag, pending := List.replicate n () } ctx : Cfg Γ Λ R) = n + 2 := by
  have rank := LocalRun.remaining caller (left_nodes_drop caller certificateRest n regs ctx)
  change runSteps (moveCode ⟨.left, []⟩ ++ certificateRest) [] (List.replicate n nodeTag) [] [] [] = _ at rank
  rw [left_nodes_exact_clock caller certificateRest n regs ctx] at rank
  omega

include caller in
theorem right_nodes_drop_rank (certificateRest : Word) (m : Nat) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    remainingSteps (cfg (some (positionLabel .dropPending)) (reset regs)
      { certificate := certificateRest, source := List.replicate (m + 2) nodeTag, pending := List.replicate (m + 1) () } ctx : Cfg Γ Λ R) = m + 3 := by
  have rank := LocalRun.remaining caller (right_nodes_drop caller certificateRest m regs ctx)
  change runSteps (moveCode ⟨.right, []⟩ ++ certificateRest) [] (List.replicate (m + 2) nodeTag) [] [] [] = _ at rank
  rw [right_nodes_exact_clock caller certificateRest m regs ctx] at rank
  omega

/-- Five real activations reach right-root setup; no caller result is crossed. -/
theorem right_nodes_start (certificateRest : Word) (m : Nat) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller 5
      (entry regs (moveCode ⟨.right, []⟩ ++ certificateRest) [] (List.replicate (m + 2) nodeTag) [] [] [] ctx)
      (cfg (some (positionLabel (.start .right))) (reset regs)
        { certificate := certificateRest, source := List.replicate (m + 2) nodeTag } ctx) := by
  let localCaller : PositionedRotationMachine.External (PositionCallerLabel Λ) →
      PositionStatement Γ Λ R := fun _ => .halt
  have run := PositionedRotationMachine.phase_step_localRun localCaller
    (PositionedRotationMachine.seek_step_path_nil localCaller .right
      { source := List.replicate (m + 2) nodeTag } (reset regs) (positionContext { certificate := certificateRest } ctx))
  have transported := position_segment_localRun caller localCaller { certificate := certificateRest } ctx run
  have paid := paid_position_code_localRun caller ⟨.right, []⟩ certificateRest []
    (List.replicate (m + 2) nodeTag) [] [] [] regs ctx
  simpa only [List.length_nil, Nat.mul_zero, Nat.zero_add, List.nil_append, List.append_nil,
    setPositionData, Option.map_some, positionLabelEquiv_phase, position_reset_reset] using
      LocalRun.trans caller paid transported

/-- The sixth activation gives the sharper right-family potential at the actual scanner. -/
theorem right_nodes_scan (certificateRest : Word) (m : Nat) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller 6
      (entry regs (moveCode ⟨.right, []⟩ ++ certificateRest) [] (List.replicate (m + 2) nodeTag) [] [] [] ctx)
      (cfg (some (positionLabel (.scanScratch .right))) (reset regs)
        { certificate := certificateRest, source := List.replicate m nodeTag, pending := [()] } ctx) := by
  let localCaller : PositionedRotationMachine.External (PositionCallerLabel Λ) →
      PositionStatement Γ Λ R := fun _ => .halt
  have run := PositionedRotationMachine.phase_step_localRun localCaller
    (PositionedRotationMachine.start_right_step_nodes localCaller (List.replicate m nodeTag)
      ({} : PositionedRotationMachine.LocalData) (reset regs) (positionContext { certificate := certificateRest } ctx))
  have transported := position_segment_localRun caller localCaller { certificate := certificateRest } ctx run
  have start := right_nodes_start caller certificateRest m regs ctx
  have joined := LocalRun.trans caller start transported
  simpa only [List.replicate_succ, setPositionData, Option.map_some,
    positionLabelEquiv_phase, position_reset_reset] using joined

theorem parser_eof_run (k : Nat) (path : List Branch) (source saved scratch : Word)
    (pending : List Unit) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (2 * k + 4)
      (entry regs (rotateLeftTag :: List.replicate k pathLeftTag) path source saved scratch pending ctx)
      (cfg (some (resultLabel parseFailure)) (reset regs)
        (entryData (rotateLeftTag :: List.replicate k pathLeftTag) path source saved scratch pending) ctx) := by
  have failed := congrArg Prod.fst (MoveParserMachine.parseMoveRun_sharpRaw (k + 1))
  have run := run_of_none_localRun caller (MoveParserMachine.sharpRaw (k + 1)) path
    source saved scratch pending regs ctx failed
  rw [MoveParserMachine.fullSteps_sharpRaw, MoveParserMachine.sharpRaw_eq] at run
  convert run using 1

include caller in
theorem parser_eof_exact_clock (k : Nat) (path : List Branch) (source saved scratch : Word)
    (pending : List Unit) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    runSteps (rotateLeftTag :: List.replicate k pathLeftTag) path source saved scratch pending =
      2 * k + 4 :=
  (LocalRun.phaseEndpoint caller (q := movePhase .start) (parser_eof_run caller k path source saved scratch pending regs ctx)).1

section SharpPhysicalSpace
variable [Fintype K]

omit [DecidableEq K] in
theorem left_nodes_drop_cells (certificateRest : Word) (n : Nat) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    stackCells (cfg (some (positionLabel .dropPending)) regs
      { certificate := certificateRest, source := List.replicate n nodeTag, pending := List.replicate n () } ctx : Cfg Γ Λ R) =
      2 * n + certificateRest.length + contextCells ctx := by
  rw [stackCells_cfg]
  simp only [localCells, List.length_nil, List.length_replicate]
  omega

omit [DecidableEq K] in
theorem right_nodes_drop_cells (certificateRest : Word) (m : Nat) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    stackCells (cfg (some (positionLabel .dropPending)) regs
      { certificate := certificateRest, source := List.replicate (m + 2) nodeTag, pending := List.replicate (m + 1) () } ctx : Cfg Γ Λ R) =
      2 * m + 3 + certificateRest.length + contextCells ctx := by
  rw [stackCells_cfg]
  simp only [localCells, List.length_nil, List.length_replicate]
  omega

theorem left_nodes_prefix_cells (certificateRest : Word) (n : Nat) (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (j : Nat) (bound : j ≤ 3 * n + 8) (reached : Cfg Γ Λ R)
    (executed : (next caller)^[j]
      (some (entry regs (moveCode ⟨.left, []⟩ ++ certificateRest) [] (List.replicate n nodeTag) [] [] [] ctx)) = some reached) :
    stackCells reached ≤ max (n + 2) (2 * n) + certificateRest.length + contextCells ctx := by
  have parsed : (parseMoveRun (moveCode ⟨.left, []⟩ ++ certificateRest)).1 = some (⟨.left, []⟩, certificateRest) := by
    exact congrArg Prod.fst (parseMoveRun_code ⟨.left, []⟩ certificateRest)
  have bound' : j ≤ runSteps (moveCode ⟨.left, []⟩ ++ certificateRest) [] (List.replicate n nodeTag) [] [] [] := by
    rw [left_nodes_exact_clock caller certificateRest n regs ctx]
    exact bound
  have cells := prefix_stackCells_le_of_some caller (moveCode ⟨.left, []⟩ ++ certificateRest) ⟨.left, []⟩ certificateRest []
    (List.replicate n nodeTag) [] [] [] regs ctx parsed j bound' reached executed
  simp only [principalCells, parsedCellsBound, List.length_append, moveCode_length, List.length_nil,
    List.length_replicate, Nat.zero_add, Nat.add_zero] at cells
  omega

omit [DecidableEq K] in
theorem right_nodes_scan_potential (certificateRest : Word) (m : Nat) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    potential (cfg (some (positionLabel (.scanScratch .right))) regs
      { certificate := certificateRest, source := List.replicate m nodeTag, pending := [()] } ctx : Cfg Γ Λ R) =
      2 * m + 3 + certificateRest.length + contextCells ctx := by
  change potential (cfg (some (phaseLabel (positionPhase (.scanScratch .right)))) regs
    { certificate := certificateRest, source := List.replicate m nodeTag, pending := [()] } ctx) = _
  rw [potential_phase_cfg]
  simp only [localCells, phaseDebt, positionPhase, phaseCredit, positionData,
    PositionedRotationMachine.phaseDebt, PositionedRotationMachine.phaseCredit,
    List.length_replicate, List.length_nil, List.length_cons]
  omega

/-- The upper bound applies to every actual prefix; the sixth configuration supplies its sharp potential. -/
theorem right_nodes_prefix_cells (certificateRest : Word) (m : Nat) (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (j : Nat) (bound : j ≤ 3 * m + 11) (reached : Cfg Γ Λ R)
    (executed : (next caller)^[j]
      (some (entry regs (moveCode ⟨.right, []⟩ ++ certificateRest) [] (List.replicate (m + 2) nodeTag) [] [] [] ctx)) = some reached) :
    stackCells reached ≤ max (m + 4) (2 * m + 3) + certificateRest.length + contextCells ctx := by
  have parserClock : MoveParserMachine.fullSteps (moveCode ⟨.right, []⟩ ++ certificateRest) = 3 := by
    simpa only [List.length_nil, Nat.mul_zero, Nat.zero_add] using
      MoveParserMachine.fullSteps_code ⟨.right, []⟩ certificateRest
  by_cases parser : j ≤ 3
  · have cells := parser_prefix_stackCells_le caller (moveCode ⟨.right, []⟩ ++ certificateRest) []
      (List.replicate (m + 2) nodeTag) [] [] [] regs ctx j (by omega) reached executed
    simp only [principalCells, List.length_append, moveCode_length, List.length_nil, List.length_replicate,
      Nat.zero_add, Nat.add_zero] at cells
    omega
  · by_cases four : j = 4
    · subst j
      have actual := LocalRun.iterate caller (paid_position_code_localRun caller ⟨.right, []⟩ certificateRest []
        (List.replicate (m + 2) nodeTag) [] [] [] regs ctx)
      change (next caller)^[4]
        (some (entry regs (moveCode ⟨.right, []⟩ ++ certificateRest) [] (List.replicate (m + 2) nodeTag) [] [] [] ctx)) =
          some (cfg (some (positionLabel (.seek .right))) (reset regs)
            { certificate := certificateRest, source := List.replicate (m + 2) nodeTag } ctx) at actual
      have same := Option.some.inj (executed.symm.trans actual)
      rw [same, stackCells_cfg]
      simp only [localCells, List.length_nil, List.length_replicate]
      omega
    · by_cases five : j = 5
      · subst j
        have actual := LocalRun.iterate caller (right_nodes_start caller certificateRest m regs ctx)
        have same := Option.some.inj (executed.symm.trans actual)
        rw [same, stackCells_cfg]
        simp only [localCells, List.length_nil, List.length_replicate]
        omega
      · have bound' : j ≤ runSteps (moveCode ⟨.right, []⟩ ++ certificateRest) []
            (List.replicate (m + 2) nodeTag) [] [] [] := by
          rw [right_nodes_exact_clock caller certificateRest m regs ctx]
          exact bound
        have cells := prefix_stackCells_le_after_localRun caller (right_nodes_scan caller certificateRest m regs ctx)
          j bound' (by omega) reached executed
        rw [right_nodes_scan_potential] at cells
        omega

/-- The left-family maximum includes both the retained certificate at entry and the attained drop state. -/
theorem left_nodes_peak (certificateRest : Word) (n : Nat) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (∀ j, j ≤ 3 * n + 8 → ∀ reached,
      (next caller)^[j]
        (some (entry regs (moveCode ⟨.left, []⟩ ++ certificateRest) [] (List.replicate n nodeTag) [] [] [] ctx)) = some reached →
      stackCells reached ≤ max (n + 2) (2 * n) + certificateRest.length + contextCells ctx) ∧
    ∃ j reached, j ≤ 3 * n + 8 ∧
      (next caller)^[j]
        (some (entry regs (moveCode ⟨.left, []⟩ ++ certificateRest) [] (List.replicate n nodeTag) [] [] [] ctx)) = some reached ∧
      stackCells reached = max (n + 2) (2 * n) + certificateRest.length + contextCells ctx := by
  refine ⟨left_nodes_prefix_cells caller certificateRest n regs ctx, ?_⟩
  by_cases initial : 2 * n ≤ n + 2
  · refine ⟨0, entry regs (moveCode ⟨.left, []⟩ ++ certificateRest) [] (List.replicate n nodeTag) [] [] [] ctx,
      by omega, rfl, ?_⟩
    rw [initial_stackCells, Nat.max_eq_left initial]
    simp only [principalCells, List.length_append, moveCode_length, List.length_nil, List.length_replicate,
      Nat.zero_add, Nat.add_zero]
    omega
  · refine ⟨2 * n + 6,
      cfg (some (positionLabel .dropPending)) (reset regs)
        { certificate := certificateRest, source := List.replicate n nodeTag, pending := List.replicate n () } ctx,
      by omega, LocalRun.iterate caller (left_nodes_drop caller certificateRest n regs ctx), ?_⟩
    rw [left_nodes_drop_cells, Nat.max_eq_right (by omega)]

/-- The right-family maximum includes its small-input entry maximum and its actual later peak. -/
theorem right_nodes_peak (certificateRest : Word) (m : Nat) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (∀ j, j ≤ 3 * m + 11 → ∀ reached,
      (next caller)^[j]
        (some (entry regs (moveCode ⟨.right, []⟩ ++ certificateRest) [] (List.replicate (m + 2) nodeTag) [] [] [] ctx)) = some reached →
      stackCells reached ≤ max (m + 4) (2 * m + 3) + certificateRest.length + contextCells ctx) ∧
    ∃ j reached, j ≤ 3 * m + 11 ∧
      (next caller)^[j]
        (some (entry regs (moveCode ⟨.right, []⟩ ++ certificateRest) [] (List.replicate (m + 2) nodeTag) [] [] [] ctx)) = some reached ∧
      stackCells reached = max (m + 4) (2 * m + 3) + certificateRest.length + contextCells ctx := by
  refine ⟨right_nodes_prefix_cells caller certificateRest m regs ctx, ?_⟩
  by_cases initial : 2 * m + 3 ≤ m + 4
  · refine ⟨0, entry regs (moveCode ⟨.right, []⟩ ++ certificateRest) [] (List.replicate (m + 2) nodeTag) [] [] [] ctx,
      by omega, rfl, ?_⟩
    rw [initial_stackCells, Nat.max_eq_left initial]
    simp only [principalCells, List.length_append, moveCode_length, List.length_nil, List.length_replicate,
      Nat.zero_add, Nat.add_zero]
    omega
  · refine ⟨2 * m + 8,
      cfg (some (positionLabel .dropPending)) (reset regs)
        { certificate := certificateRest, source := List.replicate (m + 2) nodeTag, pending := List.replicate (m + 1) () } ctx,
      by omega, LocalRun.iterate caller (right_nodes_drop caller certificateRest m regs ctx), ?_⟩
    rw [right_nodes_drop_cells, Nat.max_eq_right (by omega)]

theorem parser_eof_peak (k : Nat) (path : List Branch) (source saved scratch : Word)
    (pending : List Unit) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (∀ j, j ≤ 2 * k + 4 → ∀ reached,
      (next caller)^[j]
        (some (entry regs (rotateLeftTag :: List.replicate k pathLeftTag)
          path source saved scratch pending ctx)) = some reached →
      stackCells reached ≤ k + 1 + path.length + source.length + saved.length +
        scratch.length + pending.length + contextCells ctx) ∧
    ∃ j reached, j ≤ 2 * k + 4 ∧
      (next caller)^[j]
        (some (entry regs (rotateLeftTag :: List.replicate k pathLeftTag)
          path source saved scratch pending ctx)) = some reached ∧
      stackCells reached = k + 1 + path.length + source.length + saved.length +
        scratch.length + pending.length + contextCells ctx := by
  constructor
  · intro j bound reached executed
    have failed : (parseMoveRun (rotateLeftTag :: List.replicate k pathLeftTag)).1 = none := by
      have actual := congrArg Prod.fst (MoveParserMachine.parseMoveRun_sharpRaw (k + 1))
      simpa only [MoveParserMachine.sharpRaw_eq] using actual
    have bound' : j ≤ runSteps (rotateLeftTag :: List.replicate k pathLeftTag)
        path source saved scratch pending := by
      rw [parser_eof_exact_clock caller k path source saved scratch pending regs ctx]
      exact bound
    have cells := prefix_stackCells_le_of_none caller
      (rotateLeftTag :: List.replicate k pathLeftTag) path source saved scratch pending regs ctx
      failed j bound' reached executed
    simpa only [principalCells, List.length_cons, List.length_replicate] using cells
  · refine ⟨0, entry regs (rotateLeftTag :: List.replicate k pathLeftTag)
      path source saved scratch pending ctx, by omega, rfl, ?_⟩
    rw [initial_stackCells]
    simp only [principalCells, List.length_cons, List.length_replicate]

end SharpPhysicalSpace

/-! ## Actual finite package and certificate-only initialization -/

section MoveApplyFinitePackage

variable [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]

def initialRegisters (initial : R) : Registers R := ((none, (none, none)), initial)

/-- The program, finite carrier and caller state are fixed before the input word. -/
def machine (initial : R) : Turing.FinTM2 where
  K := StackId K
  k₀ := .inl .certificate
  k₁ := .inl .source
  Γ := alphabet Γ
  Λ := Label Λ
  main := moveLabel .start
  σ := Registers R
  initialState := initialRegisters initial
  Γk₀Fin := alphabetFintype (.inl .certificate)
  m := program caller

@[instance_reducible]
def machineAlphabetFintype (initial : R) (k : (machine caller initial).K) :
    Fintype ((machine caller initial).Γ k) := alphabetFintype k

theorem machine_card_stackId (initial : R) :
    @Fintype.card (machine caller initial).K (machine caller initial).kFin =
      7 + Fintype.card K := card_stackId

theorem machine_card_label (initial : R) :
    @Fintype.card (machine caller initial).Λ (machine caller initial).ΛFin =
      29 + Fintype.card Λ := card_label

theorem machine_card_registers (initial : R) :
    @Fintype.card (machine caller initial).σ (machine caller initial).σFin =
      102 * Fintype.card R := card_registers

theorem machine_step_eq (initial : R) (c : Cfg Γ Λ R) :
    (machine caller initial).step c = step caller c := rfl

/-- The initializer installs only the certificate; source and all other stores are empty. -/
theorem initList_eq (initial : R) (raw : Word) :
    Turing.initList (machine caller initial) raw =
      cfg (some (moveLabel .start)) (initialRegisters initial) { certificate := raw }
        (fun _ => []) := by
  apply cfg_ext
  · rfl
  · rfl
  · funext k
    cases k with
    | inl k => cases k <;> rfl
    | inr k => rfl

theorem machine_phase_run (initial : R) (q : Phase) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (fun c : Option (Cfg Γ Λ R) => c.bind (machine caller initial).step)^[phaseSteps q D]
      (some (cfg (some (phaseLabel q)) regs D ctx)) = some (phaseResult q regs D ctx) :=
  phase_iterate caller q D regs ctx

/-- This package-step execution theorem accepts every physically installed configuration. -/
theorem machine_cfg_run (initial : R) (start : Cfg Γ Λ R) :
    (fun c : Option (Cfg Γ Λ R) => c.bind (machine caller initial).step)^[remainingSteps start]
      (some start) = some (finalCfg start) := cfg_iterate caller start

theorem machine_init_run (initial : R) (raw : Word) :
    (fun c : Option (Cfg Γ Λ R) => c.bind (machine caller initial).step)^[
      phaseSteps (movePhase .start) { certificate := raw }]
      (some (Turing.initList (machine caller initial) raw)) =
        some (phaseResult (movePhase .start) (initialRegisters initial)
          { certificate := raw } (fun _ => [])) := by
  rw [initList_eq]
  exact machine_phase_run caller initial (movePhase .start) { certificate := raw }
    (initialRegisters initial) (fun _ => [])

def machinePhaseInTime (initial : R) (q : Phase) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (machine caller initial).step
      (cfg (some (phaseLabel q)) regs D ctx) (some (phaseResult q regs D ctx)) (phaseSteps q D) where
  steps := phaseSteps q D
  evals_in_steps := machine_phase_run caller initial q D regs ctx
  steps_le_m := Nat.le_refl _

def machineCfgInTime (initial : R) (start : Cfg Γ Λ R) :
    StateTransition.EvalsToInTime (machine caller initial).step start
      (some (finalCfg start)) (remainingSteps start) where
  steps := remainingSteps start
  evals_in_steps := machine_cfg_run caller initial start
  steps_le_m := Nat.le_refl _

def machineInitInTimeExact (initial : R) (raw : Word) :
    StateTransition.EvalsToInTime (machine caller initial).step
      (Turing.initList (machine caller initial) raw)
      (some (phaseResult (movePhase .start) (initialRegisters initial)
        { certificate := raw } (fun _ => [])))
      (phaseSteps (movePhase .start) { certificate := raw }) where
  steps := phaseSteps (movePhase .start) { certificate := raw }
  evals_in_steps := machine_init_run caller initial raw
  steps_le_m := Nat.le_refl _

@[simp] theorem machineInitInTimeExact_steps (initial : R) (raw : Word) :
    (machineInitInTimeExact caller initial raw).steps =
      phaseSteps (movePhase .start) { certificate := raw } := rfl

theorem machine_init_first_return (initial : R) (raw : Word) :
    ¬ Owned (phaseResult (Γ := Γ) (Λ := Λ) (movePhase .start) (initialRegisters initial)
      { certificate := raw } (fun _ : K => [])).l ∧
    ∀ n, n < phaseSteps (movePhase .start) { certificate := raw } → ∃ reached,
      (fun c : Option (Cfg Γ Λ R) => c.bind (machine caller initial).step)^[n]
        (some (Turing.initList (machine caller initial) raw)) = some reached ∧ Owned reached.l := by
  rw [initList_eq]
  exact phase_first_return caller (movePhase .start) { certificate := raw }
    (initialRegisters initial) (fun _ => [])

end MoveApplyFinitePackage

/-! The next lemmas expose the actual initializer outcome, including the consumed
first path branch on empty source. They are statements about the live result,
not Boolean cleanup or haltList. -/

theorem position_empty_evaluate (d : RotationDirection) (p : List Branch) :
    PositionedRotationMachine.evaluate (.inl (.seek d)) { path := p } =
      ⟨.failure, { path := p.tail }, if p = [] then 4 else 3⟩ := by
  cases p with
  | nil =>
      cases d <;> simp only [PositionedRotationMachine.evaluate_phase,
        PositionedRotationMachine.advance, PositionedRotationMachine.evaluate_result]
      <;> rfl
  | cons b p =>
      simp only [PositionedRotationMachine.evaluate_phase, PositionedRotationMachine.advance,
        PositionedRotationMachine.evaluate_result]
      rfl

def initOutcome (raw : Word) : FinalResult :=
  match (parseMoveRun raw).1 with
  | none => parseFailure
  | some _ => rotationFailure

def initClock (raw : Word) : Nat :=
  match (parseMoveRun raw).1 with
  | none => MoveParserMachine.fullSteps raw + 1
  | some (move, _) => if move.position = [] then 8 else 2 * move.position.length + 7

def initData (raw : Word) : LocalData :=
  match (parseMoveRun raw).1 with
  | none => { certificate := raw }
  | some (move, rest) => { certificate := rest, path := move.position.tail }

theorem initClock_eq (raw : Word) :
    runSteps raw [] [] [] [] [] = initClock raw := by
  cases parsed : (parseMoveRun raw).1 with
  | none =>
      rw [runSteps_of_none raw [] [] [] [] [] parsed]
      simp only [initClock, parsed]
  | some pair =>
      rcases pair with ⟨move, rest⟩
      rw [runSteps_of_some raw move rest [] [] [] [] [] parsed,
        MoveParserMachine.fullSteps_of_some raw move rest parsed]
      simp only [List.append_nil, PositionedRotationMachine.phaseSteps, position_empty_evaluate,
        initClock, parsed]
      split_ifs with empty
      · simp only [empty, List.length_nil]
      · omega

include caller in
theorem initResult_eq (raw : Word) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    runResult (Λ := Λ) regs raw [] [] [] [] [] ctx =
      cfg (some (resultLabel (initOutcome raw))) (reset regs) (initData raw) ctx := by
  cases parsed : (parseMoveRun raw).1 with
  | none =>
      rw [runResult_of_none caller raw [] [] [] [] [] regs ctx parsed]
      simp only [initOutcome, initData, parsed, entryData]
  | some pair =>
      rcases pair with ⟨move, rest⟩
      rw [runResult_of_some caller raw move rest [] [] [] [] [] regs ctx parsed]
      simp only [phaseResult, positionPhase, evaluate, evaluatePosition, parsedData, entryData,
        positionData, List.append_nil, position_empty_evaluate, setPositionData,
        initOutcome, initData, parsed, rotationFailure]

theorem initOutcome_failure (raw : Word) :
    initOutcome raw = parseFailure ∨ initOutcome raw = rotationFailure := by
  cases parsed : (parseMoveRun raw).1 <;> simp [initOutcome, parsed]

section MoveApplyInitializerResult

variable [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]

theorem machine_init_first_result (initial : R) (raw : Word) :
    (initOutcome raw = parseFailure ∨ initOutcome raw = rotationFailure) ∧
    (fun c : Option (Cfg Γ Λ R) => c.bind (machine caller initial).step)^[initClock raw]
      (some (Turing.initList (machine caller initial) raw)) =
        some (cfg (some (resultLabel (initOutcome raw))) (initialRegisters initial)
          (initData raw) (fun _ => [])) ∧
    ∀ j, j < initClock raw → ∃ reached,
      (fun c : Option (Cfg Γ Λ R) => c.bind (machine caller initial).step)^[j]
        (some (Turing.initList (machine caller initial) raw)) = some reached ∧ Owned reached.l := by
  refine ⟨initOutcome_failure raw, ?_, ?_⟩
  · have run := machine_init_run caller initial raw
    change (fun c : Option (Cfg Γ Λ R) => c.bind (machine caller initial).step)^[
      runSteps raw [] [] [] [] []] (some (Turing.initList (machine caller initial) raw)) =
      some (runResult (initialRegisters initial) raw [] [] [] [] [] (fun _ => [])) at run
    rw [initClock_eq, initResult_eq caller] at run
    exact run
  · intro j before
    have clock : phaseSteps (movePhase .start) { certificate := raw } = initClock raw :=
      initClock_eq raw
    exact (machine_init_first_return caller initial raw).2 j (by simpa only [clock] using before)

end MoveApplyInitializerResult

/-! ## Actual package timing on physically installed principal and represented states -/

section MoveApplyPackageRepresented

variable [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]

def machineRunInTimeExact (initial : R) (raw : Word) (path : List Branch)
    (source saved scratch : Word) (pending : List Unit)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (machine caller initial).step
      (entry regs raw path source saved scratch pending ctx)
      (some (runResult regs raw path source saved scratch pending ctx))
      (runSteps raw path source saved scratch pending) :=
  runInTimeExact caller raw path source saved scratch pending regs ctx

def machineRunInLinearTime (initial : R) (raw : Word) (path : List Branch)
    (source saved scratch : Word) (pending : List Unit)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (machine caller initial).step
      (entry regs raw path source saved scratch pending ctx)
      (some (runResult regs raw path source saved scratch pending ctx))
      (3 * raw.length + 3 * source.length + saved.length + scratch.length +
        pending.length + path.length + 3) :=
  runInLinearTime caller raw path source saved scratch pending regs ctx

@[simp] theorem machineRunInLinearTime_steps (initial : R) (raw : Word) (path : List Branch)
    (source saved scratch : Word) (pending : List Unit)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (machineRunInLinearTime caller initial raw path source saved scratch pending regs ctx).steps =
      runSteps raw path source saved scratch pending := rfl

def machineRepresentedInTime (initial : R) (move : RotationMove) (certificateRest : Word)
    (oldPath : List Branch) (s : BinaryTree Unit) (saved suffix : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (machine caller initial).step
      (entry regs (moveCode move ++ certificateRest) oldPath (treeCode s ++ suffix) saved [] [] ctx)
      (some (cfg (some (resultLabel (representedResult move oldPath s))) (reset regs)
        (representedFinalData move certificateRest oldPath s saved suffix) ctx))
      (representedSteps move oldPath s saved) :=
  representedInTime caller move certificateRest oldPath s saved suffix regs ctx

@[simp] theorem machineRepresentedInTime_steps (initial : R) (move : RotationMove)
    (certificateRest : Word) (oldPath : List Branch) (s : BinaryTree Unit) (saved suffix : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (machineRepresentedInTime caller initial move certificateRest oldPath s saved suffix regs ctx).steps =
      representedSteps move oldPath s saved := rfl

/-- Branch-explicit initializer timing carries the same actual tick count. -/
def machineInitResultInTime (initial : R) (raw : Word) :
    StateTransition.EvalsToInTime (machine caller initial).step
      (Turing.initList (machine caller initial) raw)
      (some (cfg (some (resultLabel (initOutcome raw))) (initialRegisters initial)
        (initData raw) (fun _ => []))) (initClock raw) where
  steps := initClock raw
  evals_in_steps := (machine_init_first_result caller initial raw).2.1
  steps_le_m := Nat.le_refl _

@[simp] theorem machineInitResultInTime_steps (initial : R) (raw : Word) :
    (machineInitResultInTime caller initial raw).steps = initClock raw := rfl

end MoveApplyPackageRepresented

/-! ## Space contracts for the actual finite package -/

section MoveApplyPackageSpace

variable [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]

theorem machine_prefix_space (initial : R) (start : Cfg Γ Λ R) (n : Nat)
    (bound : n ≤ remainingSteps start) (reached : Cfg Γ Λ R)
    (executed : (fun c : Option (Cfg Γ Λ R) => c.bind (machine caller initial).step)^[n]
      (some start) = some reached) : stackCells reached ≤ potential start :=
  prefix_stackCells_le_dirty caller start n bound reached executed

/-- Every real initializer prefix, including the live final result, fits the input length. -/
theorem machine_init_space (initial : R) (raw : Word) (n : Nat)
    (bound : n ≤ initClock raw) (reached : Cfg Γ Λ R)
    (executed : (fun c : Option (Cfg Γ Λ R) => c.bind (machine caller initial).step)^[n]
      (some (Turing.initList (machine caller initial) raw)) = some reached) :
    stackCells reached ≤ raw.length := by
  rw [initList_eq] at executed
  have bounded : n ≤ remainingSteps
      (cfg (some (phaseLabel (Λ := Λ) (movePhase .start))) (initialRegisters initial)
        { certificate := raw } (fun k : K => ([] : List (Γ k)))) := by
    change n ≤ runSteps raw [] [] [] [] []
    rwa [initClock_eq]
  have mass := prefix_stackCells_le_dirty caller
    (cfg (some (phaseLabel (movePhase .start))) (initialRegisters initial)
      { certificate := raw } (fun _ => [])) n bounded reached executed
  rw [potential_phase_cfg] at mass
  simpa [localCells, phaseDebt, phaseCredit, movePhase, MoveParserMachine.phaseDebt,
    contextCells] using mass

@[simp] theorem machineInitInTimeExact_steps_clock (initial : R) (raw : Word) :
    (machineInitInTimeExact caller initial raw).steps = initClock raw :=
  initClock_eq raw

theorem machine_principal_prefix_space (initial : R) (raw : Word) (path : List Branch)
    (source saved scratch : Word) (pending : List Unit) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (n : Nat) (bound : n ≤ runSteps raw path source saved scratch pending)
    (reached : Cfg Γ Λ R)
    (executed : (fun c : Option (Cfg Γ Λ R) => c.bind (machine caller initial).step)^[n]
      (some (entry regs raw path source saved scratch pending ctx)) = some reached) :
    stackCells reached ≤ principalCells raw path source saved scratch pending ctx + source.length :=
  prefix_stackCells_le caller raw path source saved scratch pending regs ctx n bound reached executed

theorem machine_principal_prefix_space_of_none (initial : R) (raw : Word) (path : List Branch)
    (source saved scratch : Word) (pending : List Unit) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (failed : (parseMoveRun raw).1 = none)
    (n : Nat) (bound : n ≤ runSteps raw path source saved scratch pending) (reached : Cfg Γ Λ R)
    (executed : (fun c : Option (Cfg Γ Λ R) => c.bind (machine caller initial).step)^[n]
      (some (entry regs raw path source saved scratch pending ctx)) = some reached) :
    stackCells reached ≤ principalCells raw path source saved scratch pending ctx :=
  prefix_stackCells_le_of_none caller raw path source saved scratch pending regs ctx failed n bound reached executed

theorem machine_principal_prefix_space_of_some (initial : R) (raw : Word) (move : RotationMove)
    (rest : Word) (path : List Branch) (source saved scratch : Word) (pending : List Unit)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) (parsed : (parseMoveRun raw).1 = some (move, rest))
    (n : Nat) (bound : n ≤ runSteps raw path source saved scratch pending) (reached : Cfg Γ Λ R)
    (executed : (fun c : Option (Cfg Γ Λ R) => c.bind (machine caller initial).step)^[n]
      (some (entry regs raw path source saved scratch pending ctx)) = some reached) :
    stackCells reached ≤ max (principalCells raw path source saved scratch pending ctx)
      (parsedCellsBound move rest path source saved scratch pending ctx) :=
  prefix_stackCells_le_of_some caller raw move rest path source saved scratch pending regs ctx parsed
    n bound reached executed

end MoveApplyPackageSpace

/-! ## One-call space specialization of actual successful FrontEnd physical data -/

section FrontEndPhysicalSpace

variable [Fintype K]

theorem frontEnd_success_prefix_space
    (physicalCaller : External Λ → Statement (frontEndProtectedAlphabet Γ) Λ
      (OpenDecoderMachine.Temporaries × R))
    (regs : FrontEndMachine.Registers (Option Branch × R))
    (source target : BinaryTree Unit) (fuel : List Bool) (cert : Word)
    (ctx : ∀ k, List (Γ k)) (n : Nat)
    (bound : n ≤ phaseSteps (movePhase .start) (frontEndSuccessData source cert [] []))
    (reached : Cfg (frontEndProtectedAlphabet Γ) Λ (OpenDecoderMachine.Temporaries × R))
    (executed : (next physicalCaller)^[n]
      (some (cfg (some (moveLabel .start))
        (frontEndRegisterEquiv (FrontEndMachine.reset regs))
        (frontEndSuccessData source cert [] []) (frontEndSuccessContext target fuel ctx))) = some reached) :
    stackCells reached ≤ cert.length + 2 * (treeCode source).length +
      (treeCode target).length + fuel.length + ∑ k, (ctx k).length := by
  have mass := prefix_stackCells_le_dirty physicalCaller
    (cfg (some (phaseLabel (movePhase .start)))
      (frontEndRegisterEquiv (FrontEndMachine.reset regs))
      (frontEndSuccessData source cert [] []) (frontEndSuccessContext target fuel ctx))
    n bound reached executed
  rw [potential_phase_cfg] at mass
  change stackCells reached ≤ localCells (frontEndSuccessData source cert [] []) +
    phaseDebt (movePhase .start) + phaseCredit (movePhase .start) (frontEndSuccessData source cert [] []) +
    (∑ k, (frontEndSuccessContext target fuel ctx k).length) at mass
  rw [frontEnd_success_context_cells] at mass
  simp only [localCells, frontEndSuccessData, phaseDebt, phaseCredit, movePhase,
    MoveParserMachine.phaseDebt, List.length_nil, Nat.add_zero] at mass
  omega

end FrontEndPhysicalSpace

/-! ## Further installation through complete carrier equivalences -/

section FurtherInstallation

variable {K' Λ' R' : Type} {Γ' : K' → Type} [DecidableEq K']
variable (names : StackId K ≃ K') (symbols : ∀ k, alphabet Γ k ≃ Γ' (names k))
  (registers : Registers R ≃ R') (labels : Label Λ ≃ Λ')
variable (ambient : Λ' → Turing.TM2.Stmt Γ' Λ' R')

def installedCfg (c : Cfg Γ Λ R) : Turing.TM2.Cfg Γ' Λ' R' :=
  FrontEndMachine.Transport.cfg names symbols registers labels c

omit [DecidableEq K] [DecidableEq K'] in
theorem installedCfg_injective :
    Function.Injective (installedCfg names symbols registers labels) :=
  FrontEndMachine.Transport.cfg_injective names symbols registers labels labels.injective

/-- Every owned body, including each paid dispatch, must be literally installed. -/
theorem installed_owned_prefix
    (installed : ∀ label, Owned (some label) →
      ambient (labels label) =
        FrontEndMachine.Transport.statement names symbols registers labels (program caller label))
    (start : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start) :
    (FrontEndMachine.Transport.next ambient)^[n]
      (some (installedCfg names symbols registers labels start)) =
      ((next caller)^[n] (some start)).map (installedCfg names symbols registers labels) := by
  apply FrontEndMachine.Transport.iterate_owned names symbols registers labels
    (program caller) ambient Owned installed n start
  intro j strict
  obtain ⟨reached, executed, _, _, ownership⟩ := owned_prefix caller start j (by omega)
  exact ⟨reached, executed, ownership.mp (by omega)⟩

def installed_owned_timed
    (installed : ∀ label, Owned (some label) →
      ambient (labels label) =
        FrontEndMachine.Transport.statement names symbols registers labels (program caller label))
    (start : Cfg Γ Λ R) :
    StateTransition.EvalsToInTime (Turing.TM2.step ambient)
      (installedCfg names symbols registers labels start)
      (some (installedCfg names symbols registers labels (finalCfg start)))
      (remainingSteps start) where
  steps := remainingSteps start
  evals_in_steps := by
    change (FrontEndMachine.Transport.next ambient)^[remainingSteps start]
      (some (installedCfg names symbols registers labels start)) = _
    rw [installed_owned_prefix caller names symbols registers labels ambient installed start
      (remainingSteps start) (Nat.le_refl _), cfg_iterate caller start]
    rfl
  steps_le_m := Nat.le_refl _

@[simp] theorem installed_owned_timed_steps
    (installed : ∀ label, Owned (some label) →
      ambient (labels label) =
        FrontEndMachine.Transport.statement names symbols registers labels (program caller label))
    (start : Cfg Γ Λ R) :
    (installed_owned_timed caller names symbols registers labels ambient installed start).steps =
      remainingSteps start := rfl

def installed_owned_prefix_timed
    (installed : ∀ label, Owned (some label) →
      ambient (labels label) =
        FrontEndMachine.Transport.statement names symbols registers labels (program caller label))
    (start : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start)
    (reached : Cfg Γ Λ R) (executed : (next caller)^[n] (some start) = some reached) :
    StateTransition.EvalsToInTime (Turing.TM2.step ambient)
      (installedCfg names symbols registers labels start)
      (some (installedCfg names symbols registers labels reached)) n where
  steps := n
  evals_in_steps := by
    change (FrontEndMachine.Transport.next ambient)^[n]
      (some (installedCfg names symbols registers labels start)) = _
    rw [installed_owned_prefix caller names symbols registers labels ambient installed start n bound, executed]
    rfl
  steps_le_m := Nat.le_refl _

/-- Arbitrary later iterations require agreement on every label, including callers. -/
theorem installed_iterate
    (installed : ∀ label, ambient (labels label) =
      FrontEndMachine.Transport.statement names symbols registers labels (program caller label))
    (n : Nat) (start : Option (Cfg Γ Λ R)) :
    (FrontEndMachine.Transport.next ambient)^[n]
      (start.map (installedCfg names symbols registers labels)) =
      ((next caller)^[n] start).map (installedCfg names symbols registers labels) :=
  FrontEndMachine.Transport.iterate names symbols registers labels (program caller) ambient installed n start

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
    (installed_timed caller names symbols registers labels ambient installed start final bound run).steps =
      run.steps := rfl

omit [DecidableEq K] [DecidableEq K'] in
theorem installed_stack_cells [Fintype K] [Fintype K'] (c : Cfg Γ Λ R) :
    ∑ k, ((installedCfg names symbols registers labels c).stk k).length = stackCells c :=
  FrontEndMachine.Transport.stackCells names symbols c.stk

theorem installed_owned_prefix_space [Fintype K] [Fintype K']
    (installed : ∀ label, Owned (some label) →
      ambient (labels label) =
        FrontEndMachine.Transport.statement names symbols registers labels (program caller label))
    (start : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start)
    (reached : Turing.TM2.Cfg Γ' Λ' R')
    (executed : (FrontEndMachine.Transport.next ambient)^[n]
      (some (installedCfg names symbols registers labels start)) = some reached) :
    ∑ k, (reached.stk k).length ≤ potential start := by
  obtain ⟨before, run, _, _, _⟩ := owned_prefix caller start n bound
  have mapped := installed_owned_prefix caller names symbols registers labels ambient installed start n bound
  rw [run, Option.map_some, executed] at mapped
  have same := Option.some.inj mapped
  rw [same, installed_stack_cells]
  exact prefix_stackCells_le_dirty caller start n bound before run

end FurtherInstallation

/-! ## Principal exact timing and sharper physical bounds after complete installation -/

section InstalledPrincipal

variable {K' Λ' R' : Type} {Γ' : K' → Type} [DecidableEq K']
variable (names : StackId K ≃ K') (symbols : ∀ k, alphabet Γ k ≃ Γ' (names k))
  (registers : Registers R ≃ R') (labels : Label Λ ≃ Λ')
variable (ambient : Λ' → Turing.TM2.Stmt Γ' Λ' R')
variable (installed : ∀ label, Owned (some label) → ambient (labels label) =
  FrontEndMachine.Transport.statement names symbols registers labels (program caller label))

def installed_runInTimeExact (raw : Word) (path : List Branch)
    (source saved scratch : Word) (pending : List Unit)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (Turing.TM2.step ambient)
      (installedCfg names symbols registers labels (entry regs raw path source saved scratch pending ctx))
      (some (installedCfg names symbols registers labels
        (runResult regs raw path source saved scratch pending ctx)))
      (runSteps raw path source saved scratch pending) :=
  installed_owned_timed caller names symbols registers labels ambient installed
    (entry regs raw path source saved scratch pending ctx)

def installed_runInLinearTime (raw : Word) (path : List Branch)
    (source saved scratch : Word) (pending : List Unit)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (Turing.TM2.step ambient)
      (installedCfg names symbols registers labels (entry regs raw path source saved scratch pending ctx))
      (some (installedCfg names symbols registers labels
        (runResult regs raw path source saved scratch pending ctx)))
      (3 * raw.length + 3 * source.length + saved.length + scratch.length +
        pending.length + path.length + 3) where
  steps := runSteps raw path source saved scratch pending
  evals_in_steps := (installed_runInTimeExact caller names symbols registers labels ambient installed
    raw path source saved scratch pending regs ctx).evals_in_steps
  steps_le_m := runSteps_le raw path source saved scratch pending

def installed_parsedRunInLinearTime (raw : Word) (move : RotationMove) (rest : Word)
    (path : List Branch) (source saved scratch : Word) (pending : List Unit)
    (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (parsed : (parseMoveRun raw).1 = some (move, rest)) :
    StateTransition.EvalsToInTime (Turing.TM2.step ambient)
      (installedCfg names symbols registers labels (entry regs raw path source saved scratch pending ctx))
      (some (installedCfg names symbols registers labels
        (runResult regs raw path source saved scratch pending ctx)))
      (3 * source.length + saved.length + scratch.length + pending.length +
        3 * move.position.length + path.length + 9) where
  steps := runSteps raw path source saved scratch pending
  evals_in_steps := (installed_runInTimeExact caller names symbols registers labels ambient installed
    raw path source saved scratch pending regs ctx).evals_in_steps
  steps_le_m := runSteps_le_of_some raw move rest path source saved scratch pending parsed

def installed_representedInTime (move : RotationMove) (certificateRest : Word)
    (oldPath : List Branch) (s : BinaryTree Unit) (saved suffix : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (Turing.TM2.step ambient)
      (installedCfg names symbols registers labels
        (entry regs (moveCode move ++ certificateRest) oldPath (treeCode s ++ suffix) saved [] [] ctx))
      (some (installedCfg names symbols registers labels
        (cfg (some (resultLabel (representedResult move oldPath s))) (reset regs)
          (representedFinalData move certificateRest oldPath s saved suffix) ctx)))
      (representedSteps move oldPath s saved) := by
  have bounded : representedSteps move oldPath s saved ≤ remainingSteps
      (entry (Λ := Λ) regs (moveCode move ++ certificateRest) oldPath (treeCode s ++ suffix) saved [] [] ctx) := by
    change representedSteps move oldPath s saved ≤
      runSteps (moveCode move ++ certificateRest) oldPath (treeCode s ++ suffix) saved [] []
    rw [(represented_run_data caller move certificateRest oldPath s saved suffix regs ctx).1]
  exact installed_owned_prefix_timed caller names symbols registers labels ambient installed
    (entry regs (moveCode move ++ certificateRest) oldPath (treeCode s ++ suffix) saved [] [] ctx)
    (representedSteps move oldPath s saved) bounded _
    (run_code_represented caller move certificateRest oldPath s saved suffix regs ctx)

variable [Fintype K] [Fintype K']

include installed in
/-- The same reached source state proves the installed physical sum bound. -/
theorem installed_prefix_cells_of_source_bound (start : Cfg Γ Λ R) (n : Nat)
    (bound : n ≤ remainingSteps start) (budget : Nat)
    (sourceBound : ∀ before, (next caller)^[n] (some start) = some before → stackCells before ≤ budget)
    (reached : Turing.TM2.Cfg Γ' Λ' R')
    (executed : (FrontEndMachine.Transport.next ambient)^[n]
      (some (installedCfg names symbols registers labels start)) = some reached) :
    ∑ k, (reached.stk k).length ≤ budget := by
  obtain ⟨before, run, _, _, _⟩ := owned_prefix caller start n bound
  have mapped := installed_owned_prefix caller names symbols registers labels ambient installed start n bound
  rw [run, Option.map_some, executed] at mapped
  rw [Option.some.inj mapped, installed_stack_cells]
  exact sourceBound before run

include installed in
theorem installed_prefix_stackCells_le (raw : Word) (path : List Branch)
    (source saved scratch : Word) (pending : List Unit) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (n : Nat) (bound : n ≤ runSteps raw path source saved scratch pending)
    (reached : Turing.TM2.Cfg Γ' Λ' R')
    (executed : (FrontEndMachine.Transport.next ambient)^[n]
      (some (installedCfg names symbols registers labels
        (entry regs raw path source saved scratch pending ctx))) = some reached) :
    ∑ k, (reached.stk k).length ≤ principalCells raw path source saved scratch pending ctx + source.length :=
  installed_prefix_cells_of_source_bound caller names symbols registers labels ambient installed
    (entry regs raw path source saved scratch pending ctx) n bound _
    (fun before run => prefix_stackCells_le caller raw path source saved scratch pending regs ctx
      n bound before run) reached executed

include installed in
theorem installed_prefix_stackCells_le_of_none (raw : Word) (path : List Branch)
    (source saved scratch : Word) (pending : List Unit) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (failed : (parseMoveRun raw).1 = none)
    (n : Nat) (bound : n ≤ runSteps raw path source saved scratch pending)
    (reached : Turing.TM2.Cfg Γ' Λ' R')
    (executed : (FrontEndMachine.Transport.next ambient)^[n]
      (some (installedCfg names symbols registers labels
        (entry regs raw path source saved scratch pending ctx))) = some reached) :
    ∑ k, (reached.stk k).length ≤ principalCells raw path source saved scratch pending ctx :=
  installed_prefix_cells_of_source_bound caller names symbols registers labels ambient installed
    (entry regs raw path source saved scratch pending ctx) n bound _
    (fun before run => prefix_stackCells_le_of_none caller raw path source saved scratch pending regs ctx
      failed n bound before run) reached executed

include installed in
theorem installed_prefix_stackCells_le_of_some (raw : Word) (move : RotationMove) (rest : Word)
    (path : List Branch) (source saved scratch : Word) (pending : List Unit)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) (parsed : (parseMoveRun raw).1 = some (move, rest))
    (n : Nat) (bound : n ≤ runSteps raw path source saved scratch pending)
    (reached : Turing.TM2.Cfg Γ' Λ' R')
    (executed : (FrontEndMachine.Transport.next ambient)^[n]
      (some (installedCfg names symbols registers labels
        (entry regs raw path source saved scratch pending ctx))) = some reached) :
    ∑ k, (reached.stk k).length ≤ max (principalCells raw path source saved scratch pending ctx)
      (parsedCellsBound move rest path source saved scratch pending ctx) :=
  installed_prefix_cells_of_source_bound caller names symbols registers labels ambient installed
    (entry regs raw path source saved scratch pending ctx) n bound _
    (fun before run => prefix_stackCells_le_of_some caller raw move rest path source saved scratch pending
      regs ctx parsed n bound before run) reached executed

end InstalledPrincipal

end Resources.RotationCertificate.MoveApplyMachine
