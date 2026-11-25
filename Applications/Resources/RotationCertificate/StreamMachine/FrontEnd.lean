import Applications.Resources.RotationCertificate.StreamMachine.Space

/-!
# StreamMachine: FrontEnd
-/

set_option autoImplicit false
set_option warningAsError true

-- BEGIN FRONTEND PHYSICAL PASSED1
namespace Resources.RotationCertificate.StreamMachine

open Search.SharedTree (Branch)

variable {K Λ R : Type} {Γ : K → Type}

/-! ## Complete FrontEnd physical data compatibility

These maps retain all sixteen physical stores and every register field. They
contain no FrontEnd/controller label map or installed control handoff. Incoming
Branch words and the added Branch register remain actual data until a charged
machine activation changes them.
-/

inductive NewBranchStores | moveReverse | path
  deriving DecidableEq

instance : Fintype NewBranchStores where
  elems := {.moveReverse, .path}
  complete k := by cases k <;> decide

inductive FrontEndProtected
  | framedRaw | frameFirstReverse | frameCertReverse | inputBits | certificateBits
  | inputRaw | bitsReverse
  deriving DecidableEq

instance : Fintype FrontEndProtected where
  elems := {.framedRaw, .frameFirstReverse, .frameCertReverse, .inputBits,
    .certificateBits, .inputRaw, .bitsReverse}
  complete k := by cases k <;> decide

abbrev frontEndAddedAlphabet (Γ : K → Type) : NewBranchStores ⊕ K → Type
  | .inl _ => Branch
  | .inr k => Γ k

abbrev frontEndProtectedAlphabet (Γ : K → Type) : FrontEndProtected ⊕ K → Type
  | .inl .inputRaw => Tag
  | .inl .framedRaw | .inl .frameFirstReverse | .inl .frameCertReverse
  | .inl .inputBits | .inl .certificateBits | .inl .bitsReverse => Bool
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

/-- FE's fourteen local stores plus the two added Branch stores, with every
original external store retained in the complete inverse. -/
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
    | .inl .targetTree => .inl .target
    | .inl .treeReverse => .inl .saved
    | .inl .pending => .inl .units
    | .inl .fuel => .inl .fuel
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
    | .inl .units => .inl .pending
    | .inl .fuel => .inl .fuel
    | .inl .target => .inl .targetTree
    | .inr (.inl .framedRaw) => .inl .framedRaw
    | .inr (.inl .frameFirstReverse) => .inl .frameFirstReverse
    | .inr (.inl .frameCertReverse) => .inl .frameCertReverse
    | .inr (.inl .inputBits) => .inl .inputBits
    | .inr (.inl .certificateBits) => .inl .certificateBits
    | .inr (.inl .inputRaw) => .inl .inputRaw
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

/-- The decoder fields protected while its actual b0 field serves the stream's
leading Bool temporary. The user register remains an additional caller field. -/
abbrev FrontEndDecoderComplement := Option Bool × Option Bool × Option Bool × Option Tag

def frontEndDecoderZero : FrontEndDecoderComplement := (none, none, none, none)

def frontEndRegisterEquiv : FrontEndMachine.Registers (Option Branch × R) ≃
    Registers (FrontEndDecoderComplement × R) where
  toFun regs := (regs.2.1.b0,
    ((regs.2.2.1, regs.1),
      ((regs.2.1.b1, regs.2.1.b2, regs.2.1.b3, regs.2.1.tag), regs.2.2.2)))
  invFun regs := (regs.2.1.2,
    (⟨regs.1, regs.2.2.1.1, regs.2.2.1.2.1,
      regs.2.2.1.2.2.1, regs.2.2.1.2.2.2⟩, (regs.2.1.1, regs.2.2.2)))
  left_inv regs := by
    rcases regs with ⟨main, decoder, branch, user⟩
    cases decoder
    rfl
  right_inv regs := by
    rcases regs with ⟨b0, ⟨branch, main⟩, ⟨b1, b2, b3, tag⟩, user⟩
    rfl

@[simp] theorem frontEndRegisterEquiv_reset
    (regs : FrontEndMachine.Registers (Option Branch × R)) :
    frontEndRegisterEquiv (FrontEndMachine.reset regs) =
      (none, ((regs.2.2.1, (none, none)), (frontEndDecoderZero, regs.2.2.2))) := rfl

@[simp] theorem frontEndRegisterEquiv_resetMove
    (regs : FrontEndMachine.Registers (Option Branch × R)) :
    resetMove (frontEndRegisterEquiv (FrontEndMachine.reset regs)) =
      frontEndRegisterEquiv (FrontEndMachine.reset regs) := rfl

@[simp] theorem frontEndRegisterEquiv_fullReset
    (regs : FrontEndMachine.Registers (Option Branch × R)) :
    resetAll (frontEndRegisterEquiv (FrontEndMachine.reset regs)) =
      (none, ((none, (none, none)), (frontEndDecoderZero, regs.2.2.2))) := rfl

@[simp] theorem frontEndRegisterEquiv_resetAll_preserves_complement
    (regs : FrontEndMachine.Registers (Option Branch × R)) :
    (resetAll (frontEndRegisterEquiv regs)).2.2 =
      ((regs.2.1.b1, regs.2.1.b2, regs.2.1.b3, regs.2.1.tag), regs.2.2.2) := rfl

theorem frontEnd_newBranch_card : Fintype.card NewBranchStores = 2 := by decide
theorem frontEnd_protected_card : Fintype.card FrontEndProtected = 7 := by decide

theorem frontEnd_decoder_complement_card : Fintype.card FrontEndDecoderComplement = 459 := by
  simp [FrontEndDecoderComplement]

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
    Fintype.card (Registers (FrontEndDecoderComplement × R)) =
      140454 * Fintype.card R := by
  rw [card_registers, Fintype.card_prod, frontEnd_decoder_complement_card]
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
  FrontEndMachine.Transport.stackEquiv_total_length frontEndStackEquiv frontEndSymbolEquiv data

def frontEndAddedContext (B O : List Branch) (ctx : ∀ k, List (Γ k)) :
    ∀ k, List (frontEndAddedAlphabet Γ k)
  | .inl .moveReverse => B
  | .inl .path => O
  | .inr k => ctx k

def frontEndSuccessContext (ctx : ∀ k, List (Γ k)) :
    ∀ k, List (frontEndProtectedAlphabet Γ k)
  | .inl .inputRaw => []
  | .inl .framedRaw | .inl .frameFirstReverse | .inl .frameCertReverse
  | .inl .inputBits | .inl .certificateBits | .inl .bitsReverse => []
  | .inr k => ctx k

def frontEndSuccessData (source target : BinaryTree Unit) (fuel : List Bool)
    (cert : Word) (B O : List Branch) : LocalData :=
  { certificate := cert, moveReverse := B, path := O, source := treeCode source,
    fuel := fuel, target := treeCode target }

/-- The complete physical view has no label component. -/
def frontEndPhysicalData
    (c : FrontEndMachine.Cfg (frontEndAddedAlphabet Γ) Λ (Option Branch × R)) :
    Registers (FrontEndDecoderComplement × R) ×
      (∀ k, List (alphabet (frontEndProtectedAlphabet Γ) k)) :=
  (frontEndRegisterEquiv c.var, frontEndStacks c.stk)

theorem frontEnd_success_stores
    (regs : FrontEndMachine.Registers (Option Branch × R)) (B O : List Branch)
    (ctx : ∀ k, List (Γ k)) (source target : BinaryTree Unit) (fuel : List Bool) (cert : Word) :
    frontEndStacks (FrontEndMachine.resultCfg (Λ := Λ) regs (frontEndAddedContext B O ctx)
      (.success source target fuel cert)).stk =
      (cfg (Λ := Unit) none (frontEndRegisterEquiv (FrontEndMachine.reset regs))
        (frontEndSuccessData source target fuel cert B O) (frontEndSuccessContext ctx)).stk := by
  funext k
  obtain ⟨k, rfl⟩ := (frontEndStackEquiv (K := K)).surjective k
  rw [frontEndStacks_apply]
  cases k with
  | inl k => cases k <;> change List.map id _ = _ <;> exact List.map_id _
  | inr k => cases k with
    | inl k => cases k <;> change List.map id _ = _ <;> exact List.map_id _
    | inr k => change List.map id _ = _; exact List.map_id _

/-- FE's actual success endpoint retains both incoming Branch words and its
stale Branch register. The conclusion compares physical data only. -/
theorem frontEnd_success_physical_data
    (regs : FrontEndMachine.Registers (Option Branch × R)) (B O : List Branch)
    (ctx : ∀ k, List (Γ k)) (source target : BinaryTree Unit) (fuel : List Bool) (cert : Word) :
    frontEndPhysicalData (FrontEndMachine.resultCfg (Λ := Λ) regs
      (frontEndAddedContext B O ctx) (.success source target fuel cert)) =
      ((none, ((regs.2.2.1, (none, none)), (frontEndDecoderZero, regs.2.2.2))),
        (cfg (Λ := Unit) none (frontEndRegisterEquiv (FrontEndMachine.reset regs))
          (frontEndSuccessData source target fuel cert B O) (frontEndSuccessContext ctx)).stk) := by
  apply Prod.ext
  · rfl
  · exact frontEnd_success_stores regs B O ctx source target fuel cert

theorem frontEnd_protected_sum (f : FrontEndProtected → Nat) :
    ∑ k, f k = f .framedRaw + f .frameFirstReverse + f .frameCertReverse +
      f .inputBits + f .certificateBits + f .inputRaw + f .bitsReverse := by
  change (∑ k ∈ ({.framedRaw, .frameFirstReverse, .frameCertReverse, .inputBits,
    .certificateBits, .inputRaw, .bitsReverse} : Finset FrontEndProtected), f k) = _
  simp [Nat.add_comm, Nat.add_left_comm]

theorem frontEnd_success_context_cells [Fintype K] (ctx : ∀ k, List (Γ k)) :
    ∑ k, (frontEndSuccessContext ctx k).length = ∑ k, (ctx k).length := by
  rw [Fintype.sum_sum_type, frontEnd_protected_sum]
  simp [frontEndSuccessContext]

end Resources.RotationCertificate.StreamMachine

-- END FRONTEND PHYSICAL PASSED1
