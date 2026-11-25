import Applications.Resources.BinaryCounter.FixedWidthMachine
import Mathlib.Logic.Equiv.List
import Applications.Resources.RotationCertificate.InputParserMachine
import Applications.Resources.RotationCertificate.OpenFramingMachine
import Applications.Resources.RotationCertificate.OpenDecoderMachine

/-!
# Finite open front end for framed binary rotation-certificate data

The installed finite program frames the raw bit list, decodes its input field,
parses the complete decoded input, and then decodes the certificate field.
It returns at a live rejection or decoded-certificate dispatch label. Complete
physical configuration maps connect the actual components without a runtime
conversion, omitted transfer, or skipped empty probe.

The source, exact-time and inclusive-prefix contracts describe this syntactic
front end. Fuel inspection, move parsing, rotations, equality, final Boolean
cleanup and the quantitative computational-model/NP bridge remain separate
obligations in the full rotation-certificate programme.
Correspondence: `docs/research/fdsa-rotation-certificate-preparation.md`.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.RotationCertificate.FrontEndMachine.Transport

variable {K K' Λ Λ' R R' : Type} {Γ : K → Type} {Γ' : K' → Type}
variable (names : K ≃ K') (symbols : ∀ k, Γ k ≃ Γ' (names k))
  (registers : R ≃ R') (labels : Λ → Λ')

def stackEquiv : (∀ k, List (Γ k)) ≃ (∀ j, List (Γ' j)) :=
  names.piCongr (fun k => Equiv.listEquivOfEquiv (symbols k))

@[simp] theorem stackEquiv_apply (data : ∀ k, List (Γ k)) (k : K) :
    stackEquiv names symbols data (names k) = (data k).map (symbols k) := by
  exact Equiv.piCongr_apply_apply (W := fun k => List (Γ k)) (Z := fun j => List (Γ' j))
    names (fun k => Equiv.listEquivOfEquiv (symbols k)) data k

def cfg (c : Turing.TM2.Cfg Γ Λ R) : Turing.TM2.Cfg Γ' Λ' R' where
  l := c.l.map labels
  var := registers c.var
  stk := stackEquiv names symbols c.stk

theorem cfg_injective (injective : Function.Injective labels) :
    Function.Injective (cfg names symbols registers labels) := by
  intro before after equal
  have labelEq := congrArg Turing.TM2.Cfg.l equal
  have registerEq := congrArg Turing.TM2.Cfg.var equal
  have stackEq := congrArg Turing.TM2.Cfg.stk equal
  have labelEq' := Option.map_injective injective labelEq
  have registerEq' := registers.injective registerEq
  have stackEq' := (stackEquiv names symbols).injective stackEq
  cases before
  cases after
  cases labelEq'
  cases registerEq'
  cases stackEq'
  rfl

/-- Only finite syntax and finite callbacks are translated. -/
def statement : Turing.TM2.Stmt Γ Λ R → Turing.TM2.Stmt Γ' Λ' R'
  | .push k value tail =>
      .push (names k) (fun regs => symbols k (value (registers.symm regs)))
        (statement tail)
  | .peek k store tail =>
      .peek (names k)
        (fun regs value => registers (store (registers.symm regs) (value.map (symbols k).symm)))
        (statement tail)
  | .pop k store tail =>
      .pop (names k)
        (fun regs value => registers (store (registers.symm regs) (value.map (symbols k).symm)))
        (statement tail)
  | .load update tail =>
      .load (fun regs => registers (update (registers.symm regs))) (statement tail)
  | .branch test yes no =>
      .branch (fun regs => test (registers.symm regs)) (statement yes) (statement no)
  | .goto label => .goto (fun regs => labels (label (registers.symm regs)))
  | .halt => .halt

theorem observed_head (k : K) (data : List (Γ k)) :
    ((data.map (symbols k)).head?).map (symbols k).symm = data.head? := by
  cases data <;> simp

theorem mapped_tail (k : K) (data : List (Γ k)) :
    (data.map (symbols k)).tail = data.tail.map (symbols k) := by
  cases data <;> rfl

variable [DecidableEq K] [DecidableEq K']

theorem stackEquiv_update (data : ∀ k, List (Γ k)) (k : K) (value : List (Γ k)) :
    stackEquiv names symbols (Function.update data k value) =
      Function.update (stackEquiv names symbols data) (names k) (value.map (symbols k)) := by
  funext j
  obtain ⟨other, rfl⟩ := names.surjective j
  by_cases equal : other = k
  · subst other
    simp only [stackEquiv_apply, Function.update_self]
  · have different : names other ≠ names k := fun h => equal (names.injective h)
    simp only [stackEquiv_apply, Function.update_of_ne equal, Function.update_of_ne different]

/-- The proof follows each actual primitive in the pinned TM2 evaluator. -/
theorem stepAux (body : Turing.TM2.Stmt Γ Λ R) (regs : R) (data : ∀ k, List (Γ k)) :
    Turing.TM2.stepAux (statement names symbols registers labels body)
        (registers regs) (stackEquiv names symbols data) =
      cfg names symbols registers labels (Turing.TM2.stepAux body regs data) := by
  induction body generalizing regs data with
  | push k value tail ih =>
      simp only [statement, Turing.TM2.stepAux, Equiv.symm_apply_apply, stackEquiv_apply]
      rw [← List.map_cons, ← stackEquiv_update, ih]
  | peek k store tail ih =>
      simp only [statement, Turing.TM2.stepAux, Equiv.symm_apply_apply,
        stackEquiv_apply, observed_head]
      exact ih _ _
  | pop k store tail ih =>
      simp only [statement, Turing.TM2.stepAux, Equiv.symm_apply_apply,
        stackEquiv_apply, observed_head, mapped_tail]
      rw [← stackEquiv_update, ih]
  | load update tail ih =>
      simp only [statement, Turing.TM2.stepAux, Equiv.symm_apply_apply]
      exact ih _ _
  | branch test yes no yesIH noIH =>
      simp only [statement, Turing.TM2.stepAux, Equiv.symm_apply_apply]
      cases test regs <;> first | exact yesIH _ _ | exact noIH _ _
  | goto label => simp [statement, Turing.TM2.stepAux, cfg]
  | halt => rfl

theorem step (source : Λ → Turing.TM2.Stmt Γ Λ R)
    (ambient : Λ' → Turing.TM2.Stmt Γ' Λ' R')
    (installed : ∀ label, ambient (labels label) = statement names symbols registers labels (source label))
    (c : Turing.TM2.Cfg Γ Λ R) :
    Turing.TM2.step ambient (cfg names symbols registers labels c) =
      (Turing.TM2.step source c).map (cfg names symbols registers labels) := by
  rcases c with ⟨label, regs, data⟩
  cases label with
  | none => rfl
  | some label =>
      simp only [cfg, Option.map_some, Turing.TM2.step, installed]
      exact congrArg some (stepAux names symbols registers labels (source label) regs data)

def next (program : Λ → Turing.TM2.Stmt Γ Λ R) :
    Option (Turing.TM2.Cfg Γ Λ R) → Option (Turing.TM2.Cfg Γ Λ R) :=
  fun c => c.bind (Turing.TM2.step program)

theorem next_map (source : Λ → Turing.TM2.Stmt Γ Λ R)
    (ambient : Λ' → Turing.TM2.Stmt Γ' Λ' R')
    (installed : ∀ label, ambient (labels label) = statement names symbols registers labels (source label))
    (c : Option (Turing.TM2.Cfg Γ Λ R)) :
    next ambient (c.map (cfg names symbols registers labels)) =
      (next source c).map (cfg names symbols registers labels) := by
  cases c with
  | none => rfl
  | some c => exact step names symbols registers labels source ambient installed c

theorem iterate (source : Λ → Turing.TM2.Stmt Γ Λ R)
    (ambient : Λ' → Turing.TM2.Stmt Γ' Λ' R')
    (installed : ∀ label, ambient (labels label) = statement names symbols registers labels (source label))
    (n : Nat) (c : Option (Turing.TM2.Cfg Γ Λ R)) :
    (next ambient)^[n] (c.map (cfg names symbols registers labels)) =
      ((next source)^[n] c).map (cfg names symbols registers labels) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
        next_map names symbols registers labels source ambient installed, ih]

def timed (source : Λ → Turing.TM2.Stmt Γ Λ R)
    (ambient : Λ' → Turing.TM2.Stmt Γ' Λ' R')
    (installed : ∀ label, ambient (labels label) = statement names symbols registers labels (source label))
    (start : Turing.TM2.Cfg Γ Λ R) (final : Option (Turing.TM2.Cfg Γ Λ R)) (bound : Nat)
    (run : StateTransition.EvalsToInTime (Turing.TM2.step source) start final bound) :
    StateTransition.EvalsToInTime (Turing.TM2.step ambient)
      (cfg names symbols registers labels start) (final.map (cfg names symbols registers labels)) bound where
  steps := run.steps
  evals_in_steps := by
    change (next ambient)^[run.steps] ((some start).map (cfg names symbols registers labels)) = _
    rw [iterate names symbols registers labels source ambient installed run.steps (some start)]
    have executed : (next source)^[run.steps] (some start) = final := run.evals_in_steps
    rw [executed]
  steps_le_m := run.steps_le_m

/-- Agreement only at owned labels supports only the actual owned prefix. -/
theorem step_owned (source : Λ → Turing.TM2.Stmt Γ Λ R)
    (ambient : Λ' → Turing.TM2.Stmt Γ' Λ' R') (owned : Option Λ → Prop)
    (installed : ∀ label, owned (some label) →
      ambient (labels label) = statement names symbols registers labels (source label))
    (c : Turing.TM2.Cfg Γ Λ R) (ownership : owned c.l) :
    Turing.TM2.step ambient (cfg names symbols registers labels c) =
      (Turing.TM2.step source c).map (cfg names symbols registers labels) := by
  rcases c with ⟨label, regs, data⟩
  cases label with
  | none => rfl
  | some label =>
      simp only [cfg, Option.map_some, Turing.TM2.step, installed label ownership]
      exact congrArg some (stepAux names symbols registers labels (source label) regs data)

theorem iterate_owned (source : Λ → Turing.TM2.Stmt Γ Λ R)
    (ambient : Λ' → Turing.TM2.Stmt Γ' Λ' R') (owned : Option Λ → Prop)
    (installed : ∀ label, owned (some label) →
      ambient (labels label) = statement names symbols registers labels (source label))
    (n : Nat) (start : Turing.TM2.Cfg Γ Λ R)
    (prefixRun : ∀ j, j < n → ∃ reached, (next source)^[j] (some start) = some reached ∧ owned reached.l) :
    (next ambient)^[n] (some (cfg names symbols registers labels start)) =
      ((next source)^[n] (some start)).map (cfg names symbols registers labels) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have prior := ih (fun j bound => prefixRun j (by omega))
      obtain ⟨before, executed, ownership⟩ := prefixRun n (Nat.lt_succ_self n)
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', prior, executed]
      exact step_owned names symbols registers labels source ambient owned installed before ownership

variable [Fintype K] [Fintype K']

omit [DecidableEq K] [DecidableEq K'] in
theorem stackCells (data : ∀ k, List (Γ k)) :
    ∑ j, (stackEquiv names symbols data j).length = ∑ k, (data k).length := by
  symm
  apply Fintype.sum_equiv names
  intro k
  simp only [stackEquiv_apply, List.length_map]

end Resources.RotationCertificate.FrontEndMachine.Transport

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

namespace Resources.RotationCertificate.FrontEndMachine
open Resources.BinaryCounter (Bits)

variable {K Λ R : Type} {Γ : K → Type}

abbrev External (Λ : Type) := TreeParserMachine.Result ⊕ Λ
abbrev InputStatement (Γ : K → Type) (Λ R : Type) :=
  InputParserMachine.Statement (inputProtectedAlphabet Γ) (ExtraLabel Λ) (InputRegisterCaller R)
abbrev FramerStatement (Γ : K → Type) (Λ R : Type) :=
  OpenFramingMachine.Statement (framerProtectedAlphabet Γ) (FramerCaller Λ) (FramerRegisterCaller R)
abbrev InputDecoderStatement (Γ : K → Type) (Λ R : Type) :=
  OpenDecoderMachine.Statement (decoderProtectedAlphabet Γ) (InputDecoderCaller Λ) (DecoderRegisterCaller R)
abbrev CertificateDecoderStatement (Γ : K → Type) (Λ R : Type) :=
  OpenDecoderMachine.Statement (decoderProtectedAlphabet Γ) (CertificateDecoderCaller Λ) (DecoderRegisterCaller R)

abbrev InputCfg (Γ : K → Type) (Λ R : Type) :=
  InputParserMachine.Cfg (inputProtectedAlphabet Γ) (ExtraLabel Λ) (InputRegisterCaller R)
abbrev FramerCfg (Γ : K → Type) (Λ R : Type) :=
  OpenFramingMachine.Cfg (framerProtectedAlphabet Γ) (FramerCaller Λ) (FramerRegisterCaller R)
abbrev InputDecoderCfg (Γ : K → Type) (Λ R : Type) :=
  OpenDecoderMachine.Cfg (decoderProtectedAlphabet Γ) (InputDecoderCaller Λ) (DecoderRegisterCaller R)
abbrev CertificateDecoderCfg (Γ : K → Type) (Λ R : Type) :=
  OpenDecoderMachine.Cfg (decoderProtectedAlphabet Γ) (CertificateDecoderCaller Λ) (DecoderRegisterCaller R)

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
@[simp] theorem program_inputDecoder (phase : OpenDecoderMachine.Phase) :
    program caller (inputDecoderLabel phase) = inputDecoderTranslate (OpenDecoderMachine.block phase) := rfl
@[simp] theorem program_certificateDecoder (phase : OpenDecoderMachine.Phase) :
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

theorem installed_inputDecoder_owned
    (localCaller : OpenDecoderMachine.External (InputDecoderCaller Λ) → InputDecoderStatement Γ Λ R)
    (label : OpenDecoderMachine.Label (InputDecoderCaller Λ)) (owned : OpenDecoderMachine.Owned (some label)) :
    program caller (inputDecoderLabelEquiv label) = inputDecoderTranslate (OpenDecoderMachine.program localCaller label) := by
  cases label with
  | inl phase => rfl
  | inr external => cases owned

theorem installed_certificateDecoder_owned
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

theorem inputDecoder_prefix_installed
    (localCaller : OpenDecoderMachine.External (InputDecoderCaller Λ) → InputDecoderStatement Γ Λ R)
    (n : Nat) (start : InputDecoderCfg Γ Λ R)
    (within : ∀ j, j < n → ∃ reached,
      (OpenDecoderMachine.next localCaller)^[j] (some start) = some reached ∧
        OpenDecoderMachine.Owned reached.l) :
    (next caller)^[n] (some (inputDecoderCfg start)) =
      ((OpenDecoderMachine.next localCaller)^[n] (some start)).map inputDecoderCfg := by
  exact Transport.iterate_owned (decoderStackEquiv .input) (decoderSymbolEquiv (Γ := Γ) .input)
    decoderRegisterEquiv inputDecoderLabelEquiv (OpenDecoderMachine.program localCaller)
    (program caller) OpenDecoderMachine.Owned (installed_inputDecoder_owned caller localCaller) n start within

theorem certificateDecoder_prefix_installed
    (localCaller : OpenDecoderMachine.External (CertificateDecoderCaller Λ) → CertificateDecoderStatement Γ Λ R)
    (n : Nat) (start : CertificateDecoderCfg Γ Λ R)
    (within : ∀ j, j < n → ∃ reached,
      (OpenDecoderMachine.next localCaller)^[j] (some start) = some reached ∧
        OpenDecoderMachine.Owned reached.l) :
    (next caller)^[n] (some (certificateDecoderCfg start)) =
      ((OpenDecoderMachine.next localCaller)^[n] (some start)).map certificateDecoderCfg := by
  exact Transport.iterate_owned (decoderStackEquiv .certificate) (decoderSymbolEquiv (Γ := Γ) .certificate)
    decoderRegisterEquiv certificateDecoderLabelEquiv (OpenDecoderMachine.program localCaller)
    (program caller) OpenDecoderMachine.Owned (installed_certificateDecoder_owned caller localCaller) n start within

/-- The actual complete framer execution under the one installed global program. -/
theorem framer_run_installed
    (localCaller : OpenFramingMachine.External (FramerCaller Λ) → FramerStatement Γ Λ R)
    (raw : Bits) (regs : OpenFramingMachine.Registers (FramerRegisterCaller R))
    (ctx : ∀ k, List (framerProtectedAlphabet Γ k)) :
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
    (ctx : ∀ k, List (inputProtectedAlphabet Γ k)) :
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
theorem inputDecoder_scan_installed
    (localCaller : OpenDecoderMachine.External (InputDecoderCaller Λ) → InputDecoderStatement Γ Λ R)
    (raw : Bits) (rev out : Word) (regs : OpenDecoderMachine.Registers (DecoderRegisterCaller R))
    (ctx : ∀ k, List (decoderProtectedAlphabet Γ k)) :
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
  have run := inputDecoder_prefix_installed caller localCaller (OpenDecoderMachine.runSteps raw + rev.length)
    (OpenDecoderMachine.cfg (some (OpenDecoderMachine.phaseLabel .scan)) regs raw rev out ctx) within
  rw [OpenDecoderMachine.scan_iterate] at run
  exact run

theorem certificateDecoder_scan_installed
    (localCaller : OpenDecoderMachine.External (CertificateDecoderCaller Λ) → CertificateDecoderStatement Γ Λ R)
    (raw : Bits) (rev out : Word) (regs : OpenDecoderMachine.Registers (DecoderRegisterCaller R))
    (ctx : ∀ k, List (decoderProtectedAlphabet Γ k)) :
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
  have run := certificateDecoder_prefix_installed caller localCaller (OpenDecoderMachine.runSteps raw + rev.length)
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
    ∀ k, List (alphabet Γ k)
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
    ∀ k, List (framerProtectedAlphabet Γ k)
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
    ∀ k, List (inputProtectedAlphabet Γ k)
  | .inl .framedRaw => data.framedRaw
  | .inl .frameFirstReverse => data.frameFirstReverse
  | .inl .frameCertReverse => data.frameCertReverse
  | .inl .inputBits => data.inputBits
  | .inl .certificateBits => data.certificateBits
  | .inl .decodeReverse => data.decodeReverse
  | .inl .certificateWord => data.certificateWord
  | .inr k => ctx k

def decoderContext (call : DecoderCall) (data : LocalData) (ctx : ∀ k, List (Γ k)) :
    ∀ k, List (decoderProtectedAlphabet Γ k)
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

@[simp] theorem afterInputDecoder_afterFrame (regs : Registers R) :
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
def run_timed (regs : Registers R) (raw : Bits) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller) (entry regs raw ctx)
      (some (resultCfg regs ctx (sourceOutcome raw))) (runSteps raw) where
  steps := runSteps raw
  evals_in_steps := run_source caller regs raw ctx
  steps_le_m := Nat.le_refl _

def run_timed_linear (regs : Registers R) (raw : Bits) (ctx : ∀ k, List (Γ k)) :
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
  exact Transport.stackCells framerStackEquiv (framerSymbolEquiv (Γ := Γ)) c.stk

omit [DecidableEq K] in
theorem stackCells_inputCfg (c : InputCfg Γ Λ R) :
    stackCells (inputCfg c) = InputParserMachine.stackCells c := by
  rw [inputStackCells_eq_sum]
  exact Transport.stackCells inputStackEquiv (inputSymbolEquiv (Γ := Γ)) c.stk

omit [DecidableEq K] in
theorem stackCells_inputDecoderCfg (c : InputDecoderCfg Γ Λ R) :
    stackCells (inputDecoderCfg c) = OpenDecoderMachine.stackCells c := by
  rw [decoderStackCells_eq_sum]
  exact Transport.stackCells (decoderStackEquiv .input) (decoderSymbolEquiv (Γ := Γ) .input) c.stk

omit [DecidableEq K] in
theorem stackCells_certificateDecoderCfg (c : CertificateDecoderCfg Γ Λ R) :
    stackCells (certificateDecoderCfg c) = OpenDecoderMachine.stackCells c := by
  rw [decoderStackCells_eq_sum]
  exact Transport.stackCells (decoderStackEquiv .certificate) (decoderSymbolEquiv (Γ := Γ) .certificate) c.stk

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
