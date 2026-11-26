import Applications.Resources.RotationCertificate.FrontEndStreamMachine.CompleteExecution

/-!
# FrontEndStreamMachine: Package
-/

set_option autoImplicit false
set_option warningAsError true

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
  Γ := Alphabet Γ
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

theorem machine_input_index (initial : R) :
    (machine caller initial).k₀ = Sum.inl FrontEndMachine.LocalStack.framedRaw := rfl

theorem machine_output_index (initial : R) :
    (machine caller initial).k₁ = Sum.inl FrontEndMachine.LocalStack.fuel := rfl

theorem machine_input_ne_output (initial : R) :
    (machine caller initial).k₀ ≠ (machine caller initial).k₁ := by
  intro h
  cases h

theorem machine_input_alphabet (initial : R) :
    (machine caller initial).Γ (machine caller initial).k₀ = Bool := rfl

theorem machine_output_alphabet (initial : R) :
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

