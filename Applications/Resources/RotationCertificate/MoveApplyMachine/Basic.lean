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

abbrev Alphabet (Γ : K → Type) : StackId K → Type
  | .inl .certificate | .inl .source | .inl .saved | .inl .scratch => Tag
  | .inl .moveReverse | .inl .path => Branch
  | .inl .pending => Unit
  | .inr k => Γ k

instance alphabetFintype [∀ k, Fintype (Γ k)] (k : StackId K) :
    Fintype (Alphabet Γ k) := by
  cases k with
  | inl k => cases k <;> exact inferInstance
  | inr k => exact inferInstance

abbrev Statement (Γ : K → Type) (Λ R : Type) :=
  Turing.TM2.Stmt (Alphabet Γ) (Label Λ) (Registers R)
abbrev Cfg (Γ : K → Type) (Λ R : Type) :=
  Turing.TM2.Cfg (Alphabet Γ) (Label Λ) (Registers R)

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

abbrev FrontEndAddedAlphabet (Γ : K → Type) : NewBranchStores ⊕ K → Type
  | .inl _ => Branch
  | .inr k => Γ k

abbrev FrontEndProtectedAlphabet (Γ : K → Type) : FrontEndProtected ⊕ K → Type
  | .inl .inputRaw | .inl .targetTree => Tag
  | .inl .framedRaw | .inl .frameFirstReverse | .inl .frameCertReverse
  | .inl .inputBits | .inl .certificateBits | .inl .fuel | .inl .bitsReverse => Bool
  | .inr k => Γ k

instance frontEndAddedFintype [∀ k, Fintype (Γ k)] (k : NewBranchStores ⊕ K) :
    Fintype (FrontEndAddedAlphabet Γ k) := by
  cases k with
  | inl k => exact inferInstance
  | inr k => exact inferInstance

instance frontEndProtectedFintype [∀ k, Fintype (Γ k)] (k : FrontEndProtected ⊕ K) :
    Fintype (FrontEndProtectedAlphabet Γ k) := by
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
    FrontEndMachine.Alphabet (FrontEndAddedAlphabet Γ) k ≃
      Alphabet (FrontEndProtectedAlphabet Γ) (frontEndStackEquiv k) := by
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

@[simp] theorem reset_frontEndRegisterEquiv_reset
    (regs : FrontEndMachine.Registers (Option Branch × R)) :
    reset (frontEndRegisterEquiv (FrontEndMachine.reset regs)) =
      ((none, (none, none)), (BitDecoderMachine.zeroRegisters, regs.2.2.2)) := rfl

theorem front_end_newBranchStores_card : Fintype.card NewBranchStores = 2 := by decide
theorem front_end_protected_card : Fintype.card FrontEndProtected = 9 := by decide

theorem front_end_stack_card [Fintype K] :
    Fintype.card (StackId (FrontEndProtected ⊕ K)) = 16 + Fintype.card K := by
  rw [card_stackId, Fintype.card_sum, front_end_protected_card]
  omega

theorem front_end_source_stack_card [Fintype K] :
    Fintype.card (FrontEndMachine.StackId (NewBranchStores ⊕ K)) =
      16 + Fintype.card K := by
  rw [Fintype.card_congr (frontEndStackEquiv (K := K))]
  exact front_end_stack_card

theorem front_end_register_card [Fintype R] :
    Fintype.card (Registers (OpenDecoderMachine.Temporaries × R)) =
      140454 * Fintype.card R := by
  rw [card_registers, Fintype.card_prod, OpenDecoderMachine.card_temporaries]
  omega

theorem front_end_source_register_card [Fintype R] :
    Fintype.card (FrontEndMachine.Registers (Option Branch × R)) =
      140454 * Fintype.card R := by
  rw [Fintype.card_congr (frontEndRegisterEquiv (R := R))]
  exact front_end_register_card

def frontEndStacks : (∀ k, List (FrontEndMachine.Alphabet (FrontEndAddedAlphabet Γ) k)) ≃
    (∀ k, List (Alphabet (FrontEndProtectedAlphabet Γ) k)) :=
  FrontEndMachine.Transport.stackEquiv frontEndStackEquiv frontEndSymbolEquiv

@[simp] theorem frontEndStacks_apply
    (data : ∀ k, List (FrontEndMachine.Alphabet (FrontEndAddedAlphabet Γ) k))
    (k : FrontEndMachine.StackId (NewBranchStores ⊕ K)) :
    frontEndStacks data (frontEndStackEquiv k) = (data k).map (frontEndSymbolEquiv k) :=
  FrontEndMachine.Transport.stackEquiv_apply _ _ _ _

theorem front_end_stack_cells [Fintype K]
    (data : ∀ k, List (FrontEndMachine.Alphabet (FrontEndAddedAlphabet Γ) k)) :
    ∑ k, (frontEndStacks data k).length = ∑ k, (data k).length :=
  FrontEndMachine.Transport.stackEquiv_total_length frontEndStackEquiv frontEndSymbolEquiv data

def frontEndAddedContext (B O : List Branch) (ctx : ∀ k, List (Γ k)) :
    ∀ k, List (FrontEndAddedAlphabet Γ k)
  | .inl .moveReverse => B
  | .inl .path => O
  | .inr k => ctx k

def frontEndSuccessContext (target : BinaryTree Unit) (fuel : List Bool)
    (ctx : ∀ k, List (Γ k)) : ∀ k, List (FrontEndProtectedAlphabet Γ k)
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
    (c : FrontEndMachine.Cfg (FrontEndAddedAlphabet Γ) Λ (Option Branch × R)) :
    Registers (OpenDecoderMachine.Temporaries × R) ×
      (∀ k, List (Alphabet (FrontEndProtectedAlphabet Γ) k)) :=
  (frontEndRegisterEquiv c.var, frontEndStacks c.stk)

theorem front_end_success_stores
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
theorem front_end_success_physical_data
    (regs : FrontEndMachine.Registers (Option Branch × R)) (B O : List Branch)
    (ctx : ∀ k, List (Γ k)) (source target : BinaryTree Unit) (fuel : List Bool) (cert : Word) :
    frontEndPhysicalData (FrontEndMachine.resultCfg (Λ := Λ) regs
      (frontEndAddedContext B O ctx) (.success source target fuel cert)) =
      (((regs.2.2.1, (none, none)), (BitDecoderMachine.zeroRegisters, regs.2.2.2)),
        (cfg (Λ := Unit) none (frontEndRegisterEquiv (FrontEndMachine.reset regs))
          (frontEndSuccessData source cert B O) (frontEndSuccessContext target fuel ctx)).stk) := by
  apply Prod.ext
  · rfl
  · exact front_end_success_stores regs B O ctx source target fuel cert

theorem front_end_protected_sum (f : FrontEndProtected → Nat) :
    ∑ k, f k = f .framedRaw + f .frameFirstReverse + f .frameCertReverse +
      f .inputBits + f .certificateBits + f .inputRaw + f .targetTree + f .fuel +
      f .bitsReverse := by
  change (∑ k ∈ ({.framedRaw, .frameFirstReverse, .frameCertReverse, .inputBits,
    .certificateBits, .inputRaw, .targetTree, .fuel, .bitsReverse} : Finset FrontEndProtected), f k) = _
  simp [Nat.add_comm, Nat.add_left_comm]

theorem front_end_success_context_cells [Fintype K] (target : BinaryTree Unit)
    (fuel : List Bool) (ctx : ∀ k, List (Γ k)) :
    ∑ k, (frontEndSuccessContext target fuel ctx k).length =
      (treeCode target).length + fuel.length + ∑ k, (ctx k).length := by
  rw [Fintype.sum_sum_type, front_end_protected_sum]
  simp [frontEndSuccessContext]


inductive MoveProtected | source | saved | scratch | pending
  deriving DecidableEq

instance : Fintype MoveProtected where
  elems := {.source, .saved, .scratch, .pending}
  complete k := by cases k <;> decide

abbrev MoveProtectedAlphabet (Γ : K → Type) : MoveProtected ⊕ K → Type
  | .inl .source | .inl .saved | .inl .scratch => Tag
  | .inl .pending => Unit
  | .inr k => Γ k

instance moveProtectedFintype [∀ k, Fintype (Γ k)] (k : MoveProtected ⊕ K) :
    Fintype (MoveProtectedAlphabet Γ k) := by
  cases k with
  | inl k => cases k <;> exact inferInstance
  | inr k => exact inferInstance

abbrev MoveCallerRegister (R : Type) := (Option Branch × Option Unit) × R
abbrev MoveCallerLabel (Λ : Type) := PositionedRotationMachine.Phase ⊕ External Λ
abbrev MoveCfg (Γ : K → Type) (Λ R : Type) :=
  MoveParserMachine.Cfg (MoveProtectedAlphabet Γ) (MoveCallerLabel Λ) (MoveCallerRegister R)
abbrev MoveStatement (Γ : K → Type) (Λ R : Type) :=
  MoveParserMachine.Statement (MoveProtectedAlphabet Γ) (MoveCallerLabel Λ) (MoveCallerRegister R)

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
    MoveParserMachine.Alphabet (MoveProtectedAlphabet Γ) k ≃
      Alphabet Γ (moveStackEquiv k) := by
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

abbrev PositionProtectedAlphabet (Γ : K → Type) : PositionProtected ⊕ K → Type
  | .inl .certificate => Tag
  | .inl .moveReverse => Branch
  | .inr k => Γ k

instance positionProtectedFintype [∀ k, Fintype (Γ k)] (k : PositionProtected ⊕ K) :
    Fintype (PositionProtectedAlphabet Γ k) := by
  cases k with
  | inl k => cases k <;> exact inferInstance
  | inr k => exact inferInstance

abbrev PositionCallerLabel (Λ : Type) :=
  MoveParserMachine.Phase ⊕ (MoveParserMachine.Result ⊕ (Unit ⊕ Λ))
abbrev PositionCfg (Γ : K → Type) (Λ R : Type) :=
  PositionedRotationMachine.Cfg (PositionProtectedAlphabet Γ) (PositionCallerLabel Λ) R
abbrev PositionStatement (Γ : K → Type) (Λ R : Type) :=
  PositionedRotationMachine.Statement (PositionProtectedAlphabet Γ) (PositionCallerLabel Λ) R

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
    PositionedRotationMachine.Alphabet (PositionProtectedAlphabet Γ) k ≃
      Alphabet Γ (positionStackEquiv k) := by
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
    ∀ k, List (MoveProtectedAlphabet Γ k)
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
    ∀ k, List (PositionProtectedAlphabet Γ k)
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


end Resources.RotationCertificate.MoveApplyMachine
