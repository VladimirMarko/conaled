import Applications.Resources.RotationCertificate.FuelDispatchMachine
import Applications.Resources.RotationCertificate.MoveApplyMachine
import Applications.Resources.RotationCertificate.TreeEqualityMachine

/-!
# Physical finite stream controller

Fuel dispatch, move application and word comparison share nine physical stores.
The eight component-result joins are actual finite one-activation statements.
All evaluators, ranks, source observations and allowances below are proof-side.
The live Boolean result does not emit an output word or implement final cleanup.
Correspondence: requirements14 and the complete fixed Stream preparation.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.RotationCertificate.StreamMachine
open Search.SharedTree (Branch)
open Trees.Rotations (RotationDirection RotationMove)
open Resources.BinaryCounter (Bits)


inductive LocalStack
  | certificate | moveReverse | path | source | saved | scratch | units | fuel | target
  deriving DecidableEq

instance : Fintype LocalStack where
  elems := {.certificate, .moveReverse, .path, .source, .saved, .scratch, .units, .fuel, .target}
  complete k := by cases k <;> decide

abbrev StackId (K : Type) := LocalStack ⊕ K
abbrev Temporaries := Option Bool × MoveApplyMachine.Temporaries
abbrev Registers (R : Type) := Option Bool × MoveApplyMachine.Registers R
abbrev Phase := FuelDispatchMachine.Label Empty ⊕ (MoveApplyMachine.Label Empty ⊕ TreeEqualityMachine.Label Empty)
abbrev External (Λ : Type) := Bool ⊕ Λ
abbrev Label (Λ : Type) := FuelDispatchMachine.Label Empty ⊕ (MoveApplyMachine.Label Empty ⊕ (TreeEqualityMachine.Label Empty ⊕ External Λ))

structure LocalData where
  certificate : Word := []
  moveReverse : List Branch := []
  path : List Branch := []
  source : Word := []
  saved : Word := []
  scratch : Word := []
  units : List Unit := []
  fuel : Bits := []
  target : Word := []
  deriving DecidableEq

variable {K Λ R : Type} {Γ : K → Type}

abbrev alphabet (Γ : K → Type) : StackId K → Type
  | .inl .certificate | .inl .source | .inl .saved | .inl .scratch | .inl .target => Tag
  | .inl .moveReverse | .inl .path => Branch
  | .inl .units => Unit
  | .inl .fuel => Bool
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

def inspectPhase : Phase := .inl FuelDispatchMachine.inspectLabel
def counterPhase (q : Resources.BinaryCounter.FixedWidthMachine.Phase) : Phase := .inl (Resources.BinaryCounter.FixedWidthMachine.phaseLabel q)
def fuelJoinPhase (r : FuelDispatchMachine.Exit) : Phase := .inl (FuelDispatchMachine.exitLabel r)
def applyPhase (q : MoveApplyMachine.Phase) : Phase := .inr (.inl (MoveApplyMachine.phaseLabel q))
def applyJoinPhase (r : MoveApplyMachine.FinalResult) : Phase := .inr (.inl (MoveApplyMachine.resultLabel r))
def comparePhase : Phase := .inr (.inr (TreeEqualityMachine.phaseLabel .compare))
def equalityJoinPhase (r : TreeEqualityMachine.Result) : Phase := .inr (.inr (TreeEqualityMachine.resultLabel r))

def phaseLabel : Phase → Label Λ
  | .inl q => .inl q
  | .inr (.inl q) => .inr (.inl q)
  | .inr (.inr q) => .inr (.inr (.inl q))
def resultLabel (b : Bool) : Label Λ := .inr (.inr (.inr (.inl b)))
def callerLabel (label : Λ) : Label Λ := .inr (.inr (.inr (.inr label)))

def Owned : Option (Label Λ) → Prop
  | some (.inl _) | some (.inr (.inl _)) | some (.inr (.inr (.inl _))) => True
  | _ => False

def resetAll (regs : Registers R) : Registers R := (none, MoveApplyMachine.reset regs.2)
def resetFuel (regs : Registers R) : Registers R := (none, regs.2)
def resetApply (regs : Registers R) : Registers R := (regs.1, MoveApplyMachine.reset regs.2)
def resetMove (regs : Registers R) : Registers R := (regs.1, MoveApplyMachine.resetMove regs.2)
def resetEquality (regs : Registers R) : Registers R :=
  (regs.1, ((regs.2.1.1, (none, none)), regs.2.2))

@[simp] theorem resetAll_resetAll (regs : Registers R) :
    resetAll (resetAll regs) = resetAll regs := rfl
@[simp] theorem resetAll_resetFuel (regs : Registers R) :
    resetAll (resetFuel regs) = resetAll regs := rfl
@[simp] theorem resetAll_resetApply (regs : Registers R) :
    resetAll (resetApply regs) = resetAll regs := rfl
@[simp] theorem resetAll_resetMove (regs : Registers R) :
    resetAll (resetMove regs) = resetAll regs := rfl
@[simp] theorem resetAll_resetEquality (regs : Registers R) :
    resetAll (resetEquality regs) = resetAll regs := rfl
@[simp] theorem resetFuel_resetAll (regs : Registers R) :
    resetFuel (resetAll regs) = resetAll regs := rfl
@[simp] theorem resetApply_resetAll (regs : Registers R) :
    resetApply (resetAll regs) = resetAll regs := rfl
@[simp] theorem resetMove_resetAll (regs : Registers R) :
    resetMove (resetAll regs) = resetAll regs := rfl
@[simp] theorem resetEquality_resetAll (regs : Registers R) :
    resetEquality (resetAll regs) = resetAll regs := rfl

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
    | .inl .units => D.units
    | .inl .fuel => D.fuel
    | .inl .target => D.target
    | .inr k => ctx k

def dataOfCfg (c : Cfg Γ Λ R) : LocalData where
  certificate := c.stk (.inl .certificate)
  moveReverse := c.stk (.inl .moveReverse)
  path := c.stk (.inl .path)
  source := c.stk (.inl .source)
  saved := c.stk (.inl .saved)
  scratch := c.stk (.inl .scratch)
  units := c.stk (.inl .units)
  fuel := c.stk (.inl .fuel)
  target := c.stk (.inl .target)

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

@[simp] theorem not_owned_result (b : Bool) : ¬ Owned (some (resultLabel (Λ := Λ) b)) := by
  simp only [Owned, resultLabel, not_false_eq_true]

abbrev OwnedLabel (Λ : Type) := {label : Label Λ // Owned (some label)}

def ownedLabelEquiv : Phase ≃ OwnedLabel Λ where
  toFun q := ⟨phaseLabel q, owned_phase q⟩
  invFun label := match label with
    | ⟨.inl q, _⟩ => .inl q
    | ⟨.inr (.inl q), _⟩ => .inr (.inl q)
    | ⟨.inr (.inr (.inl q)), _⟩ => .inr (.inr q)
    | ⟨.inr (.inr (.inr _)), impossible⟩ => False.elim impossible
  left_inv q := by cases q with
    | inl q => rfl
    | inr q => cases q <;> rfl
  right_inv label := by
    rcases label with ⟨label, h⟩
    cases label with
    | inl q => rfl
    | inr label => cases label with
      | inl q => rfl
      | inr label => cases label with
        | inl q => rfl
        | inr external => exact False.elim h

instance : Fintype (OwnedLabel Λ) := Fintype.ofEquiv Phase ownedLabelEquiv

theorem card_localStack : Fintype.card LocalStack = 9 := by decide
theorem card_phase : Fintype.card Phase = 39 := by decide
theorem card_temporaries : Fintype.card Temporaries = 306 := by
  rw [Fintype.card_prod, MoveApplyMachine.card_temporaries]
  rfl
theorem card_ownedLabel : Fintype.card (OwnedLabel Λ) = 39 := by
  rw [← Fintype.card_congr (ownedLabelEquiv (Λ := Λ))]
  exact card_phase

theorem card_stackId [Fintype K] : Fintype.card (StackId K) = 9 + Fintype.card K := by
  rw [Fintype.card_sum, card_localStack]

theorem card_label [Fintype Λ] : Fintype.card (Label Λ) = 41 + Fintype.card Λ := by
  have f : Fintype.card (FuelDispatchMachine.Label Empty) = 7 := by decide
  have h : Fintype.card (MoveApplyMachine.Label Empty) = 29 := by decide
  have e : Fintype.card (TreeEqualityMachine.Label Empty) = 3 := by decide
  simp only [Label, External, Fintype.card_sum, f, h, e, Fintype.card_bool]
  omega

theorem card_registers [Fintype R] : Fintype.card (Registers R) = 306 * Fintype.card R := by
  rw [Fintype.card_prod, MoveApplyMachine.card_registers]
  have b : Fintype.card (Option Bool) = 3 := by decide
  rw [b]
  omega


/-! ## Complete component carriers and literal transports -/

inductive FuelProtected | moveReverse | path | source | saved | scratch | target
  deriving DecidableEq

instance : Fintype FuelProtected where
  elems := {.moveReverse, .path, .source, .saved, .scratch, .target}
  complete k := by cases k <;> decide

abbrev fuelProtectedAlphabet (Γ : K → Type) : FuelProtected ⊕ K → Type
  | .inl .moveReverse => Branch
  | .inl .path => Branch
  | .inl .source => Tag
  | .inl .saved => Tag
  | .inl .scratch => Tag
  | .inl .target => Tag
  | .inr k => Γ k

instance fuelProtectedFintype [∀ k, Fintype (Γ k)] (k : FuelProtected ⊕ K) :
    Fintype (fuelProtectedAlphabet Γ k) := by
  cases k with
  | inl k => cases k <;> exact inferInstance
  | inr k => exact inferInstance

inductive ApplyProtected | fuel | target
  deriving DecidableEq

instance : Fintype ApplyProtected where
  elems := {.fuel, .target}
  complete k := by cases k <;> decide

abbrev applyProtectedAlphabet (Γ : K → Type) : ApplyProtected ⊕ K → Type
  | .inl .fuel => Bool
  | .inl .target => Tag
  | .inr k => Γ k

instance applyProtectedFintype [∀ k, Fintype (Γ k)] (k : ApplyProtected ⊕ K) :
    Fintype (applyProtectedAlphabet Γ k) := by
  cases k with
  | inl k => cases k <;> exact inferInstance
  | inr k => exact inferInstance

inductive EqualityProtected | certificate | moveReverse | path | saved | scratch | units | fuel
  deriving DecidableEq

instance : Fintype EqualityProtected where
  elems := {.certificate, .moveReverse, .path, .saved, .scratch, .units, .fuel}
  complete k := by cases k <;> decide

abbrev equalityProtectedAlphabet (Γ : K → Type) : EqualityProtected ⊕ K → Type
  | .inl .certificate => Tag
  | .inl .moveReverse => Branch
  | .inl .path => Branch
  | .inl .saved => Tag
  | .inl .scratch => Tag
  | .inl .units => Unit
  | .inl .fuel => Bool
  | .inr k => Γ k

instance equalityProtectedFintype [∀ k, Fintype (Γ k)] (k : EqualityProtected ⊕ K) :
    Fintype (equalityProtectedAlphabet Γ k) := by
  cases k with
  | inl k => cases k <;> exact inferInstance
  | inr k => exact inferInstance

abbrev FuelCallerLabel (Λ : Type) := MoveApplyMachine.Label Empty ⊕ (TreeEqualityMachine.Label Empty ⊕ External Λ)
abbrev ApplyCallerLabel (Λ : Type) := FuelDispatchMachine.Label Empty ⊕ (TreeEqualityMachine.Label Empty ⊕ External Λ)
abbrev EqualityCallerLabel (Λ : Type) := FuelDispatchMachine.Label Empty ⊕ (MoveApplyMachine.Label Empty ⊕ External Λ)
abbrev ApplyCallerRegister (R : Type) := Option Bool × R
abbrev EqualityCallerRegister (R : Type) := Option Bool × (Option Branch × R)
abbrev FuelCfg (Γ : K → Type) (Λ R : Type) :=
  FuelDispatchMachine.Cfg (fuelProtectedAlphabet Γ) (FuelCallerLabel Λ) (MoveApplyMachine.Registers R)
abbrev FuelStatement (Γ : K → Type) (Λ R : Type) :=
  FuelDispatchMachine.Statement (fuelProtectedAlphabet Γ) (FuelCallerLabel Λ) (MoveApplyMachine.Registers R)
abbrev ApplyCfg (Γ : K → Type) (Λ R : Type) :=
  MoveApplyMachine.Cfg (applyProtectedAlphabet Γ) (ApplyCallerLabel Λ) (ApplyCallerRegister R)
abbrev ApplyStatement (Γ : K → Type) (Λ R : Type) :=
  MoveApplyMachine.Statement (applyProtectedAlphabet Γ) (ApplyCallerLabel Λ) (ApplyCallerRegister R)
abbrev EqualityCfg (Γ : K → Type) (Λ R : Type) :=
  TreeEqualityMachine.Cfg (equalityProtectedAlphabet Γ) (EqualityCallerLabel Λ) (EqualityCallerRegister R)
abbrev EqualityStatement (Γ : K → Type) (Λ R : Type) :=
  TreeEqualityMachine.Statement (equalityProtectedAlphabet Γ) (EqualityCallerLabel Λ) (EqualityCallerRegister R)

def fuelStackEquiv : Resources.BinaryCounter.FixedWidthMachine.StackId (FuelDispatchMachine.Protected (FuelProtected ⊕ K)) ≃ StackId K where
  toFun
    | .inl .fuel => .inl .fuel
    | .inl .borrowed => .inl .units
    | .inr (.inl ()) => .inl .certificate
    | .inr (.inr (.inl .moveReverse)) => .inl .moveReverse
    | .inr (.inr (.inl .path)) => .inl .path
    | .inr (.inr (.inl .source)) => .inl .source
    | .inr (.inr (.inl .saved)) => .inl .saved
    | .inr (.inr (.inl .scratch)) => .inl .scratch
    | .inr (.inr (.inl .target)) => .inl .target
    | .inr (.inr (.inr k)) => .inr k
  invFun
    | .inl .fuel => .inl .fuel
    | .inl .units => .inl .borrowed
    | .inl .certificate => .inr (.inl ())
    | .inl .moveReverse => .inr (.inr (.inl .moveReverse))
    | .inl .path => .inr (.inr (.inl .path))
    | .inl .source => .inr (.inr (.inl .source))
    | .inl .saved => .inr (.inr (.inl .saved))
    | .inl .scratch => .inr (.inr (.inl .scratch))
    | .inl .target => .inr (.inr (.inl .target))
    | .inr k => .inr (.inr (.inr k))
  left_inv k := by
    cases k with
    | inl k => cases k <;> rfl
    | inr k => cases k with
      | inl u => cases u; rfl
      | inr k => cases k with
        | inl k => cases k <;> rfl
        | inr k => rfl
  right_inv k := by
    cases k with
    | inl k => cases k <;> rfl
    | inr k => rfl

def fuelSymbolEquiv (k : Resources.BinaryCounter.FixedWidthMachine.StackId (FuelDispatchMachine.Protected (FuelProtected ⊕ K))) :
    Resources.BinaryCounter.FixedWidthMachine.alphabet (FuelDispatchMachine.protectedAlphabet (fuelProtectedAlphabet Γ)) k ≃ alphabet Γ (fuelStackEquiv k) := by
  cases k with
  | inl k => cases k <;> exact Equiv.refl _
  | inr k => cases k with
    | inl u => cases u; exact Equiv.refl _
    | inr k => cases k with
      | inl k => cases k <;> exact Equiv.refl _
      | inr k => exact Equiv.refl _

def applyStackEquiv : MoveApplyMachine.StackId (ApplyProtected ⊕ K) ≃ StackId K where
  toFun
    | .inl .certificate => .inl .certificate
    | .inl .moveReverse => .inl .moveReverse
    | .inl .path => .inl .path
    | .inl .source => .inl .source
    | .inl .saved => .inl .saved
    | .inl .scratch => .inl .scratch
    | .inl .pending => .inl .units
    | .inr (.inl .fuel) => .inl .fuel
    | .inr (.inl .target) => .inl .target
    | .inr (.inr k) => .inr k
  invFun
    | .inl .certificate => .inl .certificate
    | .inl .moveReverse => .inl .moveReverse
    | .inl .path => .inl .path
    | .inl .source => .inl .source
    | .inl .saved => .inl .saved
    | .inl .scratch => .inl .scratch
    | .inl .units => .inl .pending
    | .inl .fuel => .inr (.inl .fuel)
    | .inl .target => .inr (.inl .target)
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

def applySymbolEquiv (k : MoveApplyMachine.StackId (ApplyProtected ⊕ K)) :
    MoveApplyMachine.alphabet (applyProtectedAlphabet Γ) k ≃ alphabet Γ (applyStackEquiv k) := by
  cases k with
  | inl k => cases k <;> exact Equiv.refl _
  | inr k => cases k with
    | inl k => cases k <;> exact Equiv.refl _
    | inr k => exact Equiv.refl _

def equalityStackEquiv : TreeEqualityMachine.StackId (EqualityProtected ⊕ K) ≃ StackId K where
  toFun
    | .inl .source => .inl .source
    | .inl .target => .inl .target
    | .inr (.inl .certificate) => .inl .certificate
    | .inr (.inl .moveReverse) => .inl .moveReverse
    | .inr (.inl .path) => .inl .path
    | .inr (.inl .saved) => .inl .saved
    | .inr (.inl .scratch) => .inl .scratch
    | .inr (.inl .units) => .inl .units
    | .inr (.inl .fuel) => .inl .fuel
    | .inr (.inr k) => .inr k
  invFun
    | .inl .source => .inl .source
    | .inl .target => .inl .target
    | .inl .certificate => .inr (.inl .certificate)
    | .inl .moveReverse => .inr (.inl .moveReverse)
    | .inl .path => .inr (.inl .path)
    | .inl .saved => .inr (.inl .saved)
    | .inl .scratch => .inr (.inl .scratch)
    | .inl .units => .inr (.inl .units)
    | .inl .fuel => .inr (.inl .fuel)
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

def equalitySymbolEquiv (k : TreeEqualityMachine.StackId (EqualityProtected ⊕ K)) :
    TreeEqualityMachine.alphabet (equalityProtectedAlphabet Γ) k ≃ alphabet Γ (equalityStackEquiv k) := by
  cases k with
  | inl k => cases k <;> exact Equiv.refl _
  | inr k => cases k with
    | inl k => cases k <;> exact Equiv.refl _
    | inr k => exact Equiv.refl _

def fuelRegisterEquiv : FuelDispatchMachine.Registers (MoveApplyMachine.Registers R) ≃ Registers R := Equiv.refl _

def applyRegisterEquiv : MoveApplyMachine.Registers (ApplyCallerRegister R) ≃ Registers R where
  toFun regs := (regs.2.1, (regs.1, regs.2.2))
  invFun regs := (regs.2.1, (regs.1, regs.2.2))
  left_inv regs := by rcases regs with ⟨h, ⟨b, r⟩⟩; rfl
  right_inv regs := by rcases regs with ⟨b, ⟨h, r⟩⟩; rfl

def equalityRegisterEquiv : TreeEqualityMachine.Registers (EqualityCallerRegister R) ≃ Registers R where
  toFun regs := (regs.2.1, ((regs.2.2.1, regs.1), regs.2.2.2))
  invFun regs := (regs.2.1.2, (regs.1, (regs.2.1.1, regs.2.2)))
  left_inv regs := by rcases regs with ⟨⟨tag, unit⟩, ⟨b, ⟨branch, r⟩⟩⟩; rfl
  right_inv regs := by rcases regs with ⟨b, ⟨⟨branch, ⟨tag, unit⟩⟩, r⟩⟩; rfl

def fuelLabelEquiv : FuelDispatchMachine.Label (FuelCallerLabel Λ) ≃ Label Λ where
  toFun
    | .inl q => .inl (.inl q)
    | .inr (.inl r) => .inl (.inr (.inl r))
    | .inr (.inr (.inl d)) => .inl (.inr (.inr (.inl d)))
    | .inr (.inr (.inr label)) => .inr label
  invFun
    | .inl (.inl q) => .inl q
    | .inl (.inr (.inl r)) => .inr (.inl r)
    | .inl (.inr (.inr (.inl d))) => .inr (.inr (.inl d))
    | .inl (.inr (.inr (.inr impossible))) => Empty.elim impossible
    | .inr label => .inr (.inr (.inr label))
  left_inv label := by rcases label with q | (r | (d | label)) <;> rfl
  right_inv label := by
    rcases label with (q | (r | (d | impossible))) | label
    · rfl
    · rfl
    · rfl
    · exact Empty.elim impossible
    · rfl

def applyLabelEquiv : MoveApplyMachine.Label (ApplyCallerLabel Λ) ≃ Label Λ where
  toFun
    | .inl q => .inr (.inl (.inl q))
    | .inr (.inl r) => .inr (.inl (.inr (.inl r)))
    | .inr (.inr (.inl q)) => .inr (.inl (.inr (.inr (.inl q))))
    | .inr (.inr (.inr (.inl r))) => .inr (.inl (.inr (.inr (.inr (.inl r)))))
    | .inr (.inr (.inr (.inr (.inl f)))) => .inl f
    | .inr (.inr (.inr (.inr (.inr (.inl e))))) => .inr (.inr (.inl e))
    | .inr (.inr (.inr (.inr (.inr (.inr external))))) => .inr (.inr (.inr external))
  invFun
    | .inl f => .inr (.inr (.inr (.inr (.inl f))))
    | .inr (.inl (.inl q)) => .inl q
    | .inr (.inl (.inr (.inl r))) => .inr (.inl r)
    | .inr (.inl (.inr (.inr (.inl q)))) => .inr (.inr (.inl q))
    | .inr (.inl (.inr (.inr (.inr (.inl r))))) => .inr (.inr (.inr (.inl r)))
    | .inr (.inl (.inr (.inr (.inr (.inr impossible))))) => Empty.elim impossible
    | .inr (.inr (.inl e)) => .inr (.inr (.inr (.inr (.inr (.inl e)))))
    | .inr (.inr (.inr external)) => .inr (.inr (.inr (.inr (.inr (.inr external)))))
  left_inv label := by rcases label with q | (r | (q | (r | (f | (e | external))))) <;> rfl
  right_inv label := by
    rcases label with f | ((q | (r | (q | (r | impossible)))) | (e | external))
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact Empty.elim impossible
    · rfl
    · rfl

def equalityLabelEquiv : TreeEqualityMachine.Label (EqualityCallerLabel Λ) ≃ Label Λ where
  toFun
    | .inl q => .inr (.inr (.inl (.inl q)))
    | .inr (.inl r) => .inr (.inr (.inl (.inr (.inl r))))
    | .inr (.inr (.inl f)) => .inl f
    | .inr (.inr (.inr (.inl h))) => .inr (.inl h)
    | .inr (.inr (.inr (.inr external))) => .inr (.inr (.inr external))
  invFun
    | .inl f => .inr (.inr (.inl f))
    | .inr (.inl h) => .inr (.inr (.inr (.inl h)))
    | .inr (.inr (.inl (.inl q))) => .inl q
    | .inr (.inr (.inl (.inr (.inl r)))) => .inr (.inl r)
    | .inr (.inr (.inl (.inr (.inr impossible)))) => Empty.elim impossible
    | .inr (.inr (.inr external)) => .inr (.inr (.inr (.inr external)))
  left_inv label := by rcases label with q | (r | (f | (h | external))) <;> rfl
  right_inv label := by
    rcases label with f | (h | ((q | (r | impossible)) | external))
    · rfl
    · rfl
    · rfl
    · rfl
    · exact Empty.elim impossible
    · rfl

@[simp] theorem fuelLabelEquiv_counter (q : Resources.BinaryCounter.FixedWidthMachine.Phase) :
    fuelLabelEquiv (Resources.BinaryCounter.FixedWidthMachine.phaseLabel q) = phaseLabel (Λ := Λ) (counterPhase q) := rfl
@[simp] theorem fuelLabelEquiv_inspect :
    fuelLabelEquiv FuelDispatchMachine.inspectLabel = phaseLabel (Λ := Λ) inspectPhase := rfl
@[simp] theorem fuelLabelEquiv_exit (r : FuelDispatchMachine.Exit) :
    fuelLabelEquiv (FuelDispatchMachine.exitLabel r) = phaseLabel (Λ := Λ) (fuelJoinPhase r) := by cases r <;> rfl
@[simp] theorem applyLabelEquiv_phase (q : MoveApplyMachine.Phase) :
    applyLabelEquiv (MoveApplyMachine.phaseLabel q) = phaseLabel (Λ := Λ) (applyPhase q) := by
  cases q with
  | inl q => rfl
  | inr q => cases q <;> rfl
@[simp] theorem applyLabelEquiv_result (r : MoveApplyMachine.FinalResult) :
    applyLabelEquiv (MoveApplyMachine.resultLabel r) = phaseLabel (Λ := Λ) (applyJoinPhase r) := rfl
@[simp] theorem equalityLabelEquiv_phase (q : TreeEqualityMachine.Phase) :
    equalityLabelEquiv (TreeEqualityMachine.phaseLabel q) = phaseLabel (Λ := Λ) comparePhase := by cases q; rfl
@[simp] theorem equalityLabelEquiv_result (r : TreeEqualityMachine.Result) :
    equalityLabelEquiv (TreeEqualityMachine.resultLabel r) = phaseLabel (Λ := Λ) (equalityJoinPhase r) := rfl

@[simp] theorem fuelRegisterEquiv_reset (regs : FuelDispatchMachine.Registers (MoveApplyMachine.Registers R)) :
    fuelRegisterEquiv (Resources.BinaryCounter.FixedWidthMachine.reset regs) = resetFuel (fuelRegisterEquiv regs) := rfl
@[simp] theorem applyRegisterEquiv_reset (regs : MoveApplyMachine.Registers (ApplyCallerRegister R)) :
    applyRegisterEquiv (MoveApplyMachine.reset regs) = resetApply (applyRegisterEquiv regs) := rfl
@[simp] theorem equalityRegisterEquiv_reset (regs : TreeEqualityMachine.Registers (EqualityCallerRegister R)) :
    equalityRegisterEquiv (TreeEqualityMachine.reset regs) = resetEquality (equalityRegisterEquiv regs) := rfl

def fuelContext (D : LocalData) (ctx : ∀ k, List (Γ k)) :
    ∀ k, List (fuelProtectedAlphabet Γ k)
  | .inl .moveReverse => D.moveReverse
  | .inl .path => D.path
  | .inl .source => D.source
  | .inl .saved => D.saved
  | .inl .scratch => D.scratch
  | .inl .target => D.target
  | .inr k => ctx k

def applyContext (D : LocalData) (ctx : ∀ k, List (Γ k)) :
    ∀ k, List (applyProtectedAlphabet Γ k)
  | .inl .fuel => D.fuel
  | .inl .target => D.target
  | .inr k => ctx k

def equalityContext (D : LocalData) (ctx : ∀ k, List (Γ k)) :
    ∀ k, List (equalityProtectedAlphabet Γ k)
  | .inl .certificate => D.certificate
  | .inl .moveReverse => D.moveReverse
  | .inl .path => D.path
  | .inl .saved => D.saved
  | .inl .scratch => D.scratch
  | .inl .units => D.units
  | .inl .fuel => D.fuel
  | .inr k => ctx k

def applyData (D : LocalData) : MoveApplyMachine.LocalData :=
  ⟨D.certificate, D.moveReverse, D.path, D.source, D.saved, D.scratch, D.units⟩

def setApplyData (D : LocalData) (A : MoveApplyMachine.LocalData) : LocalData :=
  { D with
    certificate := A.certificate
    moveReverse := A.moveReverse
    path := A.path
    source := A.source
    saved := A.saved
    scratch := A.scratch
    units := A.pending }

@[simp] theorem applyData_setApplyData (D : LocalData) (A : MoveApplyMachine.LocalData) :
    applyData (setApplyData D A) = A := by cases A; rfl
@[simp] theorem setApplyData_applyData (D : LocalData) : setApplyData D (applyData D) = D := by
  cases D
  rfl

def fuelView (label : Option (FuelDispatchMachine.Label (FuelCallerLabel Λ)))
    (regs : FuelDispatchMachine.Registers (MoveApplyMachine.Registers R)) (D : LocalData) (ctx : ∀ k, List (Γ k)) : FuelCfg Γ Λ R :=
  FuelDispatchMachine.cfg label regs D.fuel D.units D.certificate (fuelContext D ctx)
def applyView (label : Option (MoveApplyMachine.Label (ApplyCallerLabel Λ)))
    (regs : MoveApplyMachine.Registers (ApplyCallerRegister R)) (D : LocalData) (ctx : ∀ k, List (Γ k)) : ApplyCfg Γ Λ R :=
  MoveApplyMachine.cfg label regs (applyData D) (applyContext D ctx)
def equalityView (label : Option (TreeEqualityMachine.Label (EqualityCallerLabel Λ)))
    (regs : TreeEqualityMachine.Registers (EqualityCallerRegister R)) (D : LocalData) (ctx : ∀ k, List (Γ k)) : EqualityCfg Γ Λ R :=
  TreeEqualityMachine.cfg label regs D.source D.target (equalityContext D ctx)

def fuelCfg (c : FuelCfg Γ Λ R) : Cfg Γ Λ R :=
  FrontEndMachine.Transport.cfg fuelStackEquiv fuelSymbolEquiv fuelRegisterEquiv fuelLabelEquiv c

theorem fuelCfg_view (label : Option (FuelDispatchMachine.Label (FuelCallerLabel Λ)))
    (regs : FuelDispatchMachine.Registers (MoveApplyMachine.Registers R)) (D : LocalData) (ctx : ∀ k, List (Γ k)) :
    fuelCfg (fuelView label regs D ctx) =
      cfg (label.map fuelLabelEquiv) (fuelRegisterEquiv regs) D ctx := by
  apply cfg_ext
  · rfl
  · rfl
  · funext k
    obtain ⟨k, rfl⟩ := fuelStackEquiv.surjective k
    change FrontEndMachine.Transport.stackEquiv fuelStackEquiv (fuelSymbolEquiv (Γ := Γ))
      (fuelView label regs D ctx).stk (fuelStackEquiv k) = _
    rw [FrontEndMachine.Transport.stackEquiv_apply]
    cases k with
    | inl k => cases k <;> change List.map id _ = _ <;> exact List.map_id _
    | inr k => cases k with
      | inl u => cases u; change List.map id _ = _; exact List.map_id _
      | inr k => cases k with
        | inl k => cases k <;> change List.map id _ = _ <;> exact List.map_id _
        | inr k => change List.map id _ = _; exact List.map_id _

def fuelTranslate (body : FuelStatement Γ Λ R) : Statement Γ Λ R :=
  FrontEndMachine.Transport.statement fuelStackEquiv fuelSymbolEquiv fuelRegisterEquiv fuelLabelEquiv body

def applyCfg (c : ApplyCfg Γ Λ R) : Cfg Γ Λ R :=
  FrontEndMachine.Transport.cfg applyStackEquiv applySymbolEquiv applyRegisterEquiv applyLabelEquiv c

theorem applyCfg_view (label : Option (MoveApplyMachine.Label (ApplyCallerLabel Λ)))
    (regs : MoveApplyMachine.Registers (ApplyCallerRegister R)) (D : LocalData) (ctx : ∀ k, List (Γ k)) :
    applyCfg (applyView label regs D ctx) =
      cfg (label.map applyLabelEquiv) (applyRegisterEquiv regs) D ctx := by
  apply cfg_ext
  · rfl
  · rfl
  · funext k
    obtain ⟨k, rfl⟩ := applyStackEquiv.surjective k
    change FrontEndMachine.Transport.stackEquiv applyStackEquiv (applySymbolEquiv (Γ := Γ))
      (applyView label regs D ctx).stk (applyStackEquiv k) = _
    rw [FrontEndMachine.Transport.stackEquiv_apply]
    cases k with
    | inl k => cases k <;> change List.map id _ = _ <;> exact List.map_id _
    | inr k => cases k with
      | inl k => cases k <;> change List.map id _ = _ <;> exact List.map_id _
      | inr k => change List.map id _ = _; exact List.map_id _

def applyTranslate (body : ApplyStatement Γ Λ R) : Statement Γ Λ R :=
  FrontEndMachine.Transport.statement applyStackEquiv applySymbolEquiv applyRegisterEquiv applyLabelEquiv body

def equalityCfg (c : EqualityCfg Γ Λ R) : Cfg Γ Λ R :=
  FrontEndMachine.Transport.cfg equalityStackEquiv equalitySymbolEquiv equalityRegisterEquiv equalityLabelEquiv c

theorem equalityCfg_view (label : Option (TreeEqualityMachine.Label (EqualityCallerLabel Λ)))
    (regs : TreeEqualityMachine.Registers (EqualityCallerRegister R)) (D : LocalData) (ctx : ∀ k, List (Γ k)) :
    equalityCfg (equalityView label regs D ctx) =
      cfg (label.map equalityLabelEquiv) (equalityRegisterEquiv regs) D ctx := by
  apply cfg_ext
  · rfl
  · rfl
  · funext k
    obtain ⟨k, rfl⟩ := equalityStackEquiv.surjective k
    change FrontEndMachine.Transport.stackEquiv equalityStackEquiv (equalitySymbolEquiv (Γ := Γ))
      (equalityView label regs D ctx).stk (equalityStackEquiv k) = _
    rw [FrontEndMachine.Transport.stackEquiv_apply]
    cases k with
    | inl k => cases k <;> change List.map id _ = _ <;> exact List.map_id _
    | inr k => cases k with
      | inl k => cases k <;> change List.map id _ = _ <;> exact List.map_id _
      | inr k => change List.map id _ = _; exact List.map_id _

def equalityTranslate (body : EqualityStatement Γ Λ R) : Statement Γ Λ R :=
  FrontEndMachine.Transport.statement equalityStackEquiv equalitySymbolEquiv equalityRegisterEquiv equalityLabelEquiv body

def counterBlock (q : Resources.BinaryCounter.FixedWidthMachine.Phase) : Statement Γ Λ R := fuelTranslate (Resources.BinaryCounter.FixedWidthMachine.block q)
def inspectBlock : Statement Γ Λ R := fuelTranslate FuelDispatchMachine.inspectBlock

def applyBlock (q : MoveApplyMachine.Phase) : Statement Γ Λ R :=
  applyTranslate (MoveApplyMachine.program (fun _ => .halt) (MoveApplyMachine.phaseLabel q))

def compareBlock : Statement Γ Λ R := equalityTranslate (TreeEqualityMachine.block .compare)

def fuelJoinTarget : FuelDispatchMachine.Exit → Label Λ
  | .atEnd => phaseLabel comparePhase
  | .positive => phaseLabel (applyPhase (MoveApplyMachine.movePhase .start))
  | .zero => resultLabel false

def applyJoinTarget : MoveApplyMachine.FinalResult → Label Λ
  | .inl _ | .inr .failure => resultLabel false
  | .inr .success => phaseLabel inspectPhase

def equalityResult : TreeEqualityMachine.Result → Bool
  | .equal => true
  | .different => false

def equalityJoinTarget (r : TreeEqualityMachine.Result) : Label Λ := resultLabel (equalityResult r)

/-- All eight joins are paid stack-preserving finite reset/goto blocks. -/
def fuelJoinBlock (r : FuelDispatchMachine.Exit) : Statement Γ Λ R :=
  .load resetAll (.goto (fun _ => fuelJoinTarget r))
def applyJoinBlock (r : MoveApplyMachine.FinalResult) : Statement Γ Λ R :=
  .load resetAll (.goto (fun _ => applyJoinTarget r))
def equalityJoinBlock (r : TreeEqualityMachine.Result) : Statement Γ Λ R :=
  .load resetAll (.goto (fun _ => equalityJoinTarget r))

def program (caller : External Λ → Statement Γ Λ R) : Label Λ → Statement Γ Λ R
  | .inl (.inl q) => counterBlock q
  | .inl (.inr (.inl r)) => fuelJoinBlock (FuelDispatchMachine.exitOfResult r)
  | .inl (.inr (.inr (.inl .inspectCertificate))) => inspectBlock
  | .inl (.inr (.inr (.inl .atEnd))) => fuelJoinBlock .atEnd
  | .inl (.inr (.inr (.inr impossible))) => Empty.elim impossible
  | .inr (.inl (.inl q)) => applyBlock (MoveApplyMachine.movePhase q)
  | .inr (.inl (.inr (.inl r))) => applyBlock (MoveApplyMachine.dispatchPhase r)
  | .inr (.inl (.inr (.inr (.inl q)))) => applyBlock (MoveApplyMachine.positionPhase q)
  | .inr (.inl (.inr (.inr (.inr (.inl r))))) => applyJoinBlock r
  | .inr (.inl (.inr (.inr (.inr (.inr impossible))))) => Empty.elim impossible
  | .inr (.inr (.inl (.inl .compare))) => compareBlock
  | .inr (.inr (.inl (.inr (.inl r)))) => equalityJoinBlock r
  | .inr (.inr (.inl (.inr (.inr impossible)))) => Empty.elim impossible
  | .inr (.inr (.inr external)) => caller external

-- BEGIN SOURCE BRIDGE CHECK3
/-! ### Complete parser-start success with an arbitrary reverse Branch word -/

/-- The parser's literal output prepends the old reverse word in its physical
orientation, then the newly parsed path, then the old forward path. -/
def moveStartParsedData (move : RotationMove) (rest : Word)
    (D : MoveApplyMachine.LocalData) : MoveApplyMachine.LocalData :=
  { D with
    certificate := rest
    moveReverse := []
    path := D.moveReverse.reverse ++ move.position ++ D.path }

theorem move_start_direction (d : RotationDirection) (raw : Word)
    (D : MoveApplyMachine.LocalData)
    (certificate : D.certificate = directionTag d :: raw) :
    MoveApplyMachine.moveFinish .start D =
      MoveApplyMachine.moveScanFinish d { D with certificate := raw } (parsePathRun raw).1 := by
  rw [MoveApplyMachine.moveFinish, certificate]
  cases d <;> rfl

/-- Parser success is exactly source parsing even when the reverse word is dirty.
The reverse word affects the physical output and clock, not which prefix parses. -/
theorem move_start_parse_result (D : MoveApplyMachine.LocalData) :
    (MoveApplyMachine.moveFinish .start D).result =
      match (parseMoveRun D.certificate).1 with
      | none => MoveParserMachine.Result.failure
      | some (move, _) => MoveParserMachine.Result.success move.direction := by
  cases certificate : D.certificate with
  | nil => simp only [MoveApplyMachine.moveFinish, certificate, parseMoveRun_nil]
  | cons tag raw =>
      by_cases left : tag = rotateLeftTag
      · simp only [MoveApplyMachine.moveFinish, certificate, parseMoveRun,
          ite_eq_left left, Resources.bind]
        cases parsed : (parsePathRun raw).1 <;> rfl
      · by_cases right : tag = rotateRightTag
        · simp only [MoveApplyMachine.moveFinish, certificate, parseMoveRun,
            ite_eq_right left, ite_eq_left right, Resources.bind]
          cases parsed : (parsePathRun raw).1 <;> rfl
        · simp only [MoveApplyMachine.moveFinish, certificate, parseMoveRun,
            ite_eq_right left, ite_eq_right right]

/-- Complete dirty parser endpoint: all four Position stores are preserved. -/
theorem move_start_parse_success_data (D : MoveApplyMachine.LocalData)
    (move : RotationMove) (rest : Word)
    (parsed : (parseMoveRun D.certificate).1 = some (move, rest)) :
    MoveApplyMachine.moveFinish .start D =
      ⟨.success move.direction, moveStartParsedData move rest D⟩ := by
  have certificate := (parseMoveRun_iff D.certificate move rest).mp parsed
  have shaped : D.certificate =
      directionTag move.direction :: (pathTags move.position ++ [endMoveTag] ++ rest) := by
    simpa only [moveCode, List.cons_append] using certificate
  rw [move_start_direction move.direction _ D shaped, parsePathRun_code]
  rfl

/-- The old reverse word contributes exactly its own length to the successful
parser segment. It contributes no source-code consumption. -/
theorem move_start_parse_success_steps (D : MoveApplyMachine.LocalData)
    (move : RotationMove) (rest : Word)
    (parsed : (parseMoveRun D.certificate).1 = some (move, rest)) :
    MoveParserMachine.phaseSteps .start D.certificate D.moveReverse =
      2 * move.position.length + D.moveReverse.length + 3 := by
  change MoveParserMachine.startSteps D.certificate D.moveReverse = _
  rw [(parseMoveRun_iff D.certificate move rest).mp parsed]
  change MoveParserMachine.startSteps
    (directionTag move.direction :: (pathTags move.position ++ [endMoveTag] ++ rest))
      D.moveReverse = _
  rw [MoveParserMachine.startSteps_direction, MoveParserMachine.scanSteps,
    MoveParserMachine.branchCount_code]

/-- Full MoveApply evaluation after a successful parse, including its one paid
dispatch and the complete arbitrary-data Position result. -/
theorem move_start_parse_evaluate (D : MoveApplyMachine.LocalData)
    (move : RotationMove) (rest : Word)
    (parsed : (parseMoveRun D.certificate).1 = some (move, rest)) :
    MoveApplyMachine.evaluate (MoveApplyMachine.movePhase .start) D =
      let actual := MoveApplyMachine.evaluatePosition (.seek move.direction)
        (moveStartParsedData move rest D)
      ⟨actual.result, actual.data,
        2 * move.position.length + D.moveReverse.length + 4 + actual.steps⟩ := by
  dsimp only [MoveApplyMachine.evaluate, MoveApplyMachine.movePhase]
  rw [move_start_parse_success_data D move rest parsed]
  dsimp only [MoveApplyMachine.evaluateDispatch]
  rw [move_start_parse_success_steps D move rest parsed]
  congr 1
  omega

/-- Position never changes the complementary certificate store. -/
theorem move_start_parse_success_certificate (D : MoveApplyMachine.LocalData)
    (move : RotationMove) (rest : Word)
    (parsed : (parseMoveRun D.certificate).1 = some (move, rest)) :
    (MoveApplyMachine.evaluate (MoveApplyMachine.movePhase .start) D).data.certificate = rest := by
  rw [move_start_parse_evaluate D move rest parsed]
  rfl

/-- A full H.start success exposes its actual source parse and literal remaining
certificate. No emptiness assumption is imposed on reverse/path/tree auxiliaries. -/
theorem move_start_success_has_parse (D : MoveApplyMachine.LocalData)
    (returned : (MoveApplyMachine.evaluate (MoveApplyMachine.movePhase .start) D).result =
      MoveApplyMachine.success) :
    ∃ move rest,
      (parseMoveRun D.certificate).1 = some (move, rest) ∧
      MoveApplyMachine.moveFinish .start D =
        ⟨.success move.direction, moveStartParsedData move rest D⟩ ∧
      (MoveApplyMachine.evaluate (MoveApplyMachine.movePhase .start) D).data.certificate = rest ∧
      D.certificate = moveCode move ++ rest ∧
      D.certificate.length = move.position.length + 2 + rest.length ∧
      rest.length + 2 ≤ D.certificate.length ∧
      rest.length < D.certificate.length := by
  cases parsed : (parseMoveRun D.certificate).1 with
  | none =>
      have failed : (MoveApplyMachine.moveFinish .start D).result = .failure := by
        rw [move_start_parse_result, parsed]
      have result :
          (MoveApplyMachine.evaluate (MoveApplyMachine.movePhase .start) D).result =
            MoveApplyMachine.parseFailure := by
        simp only [MoveApplyMachine.evaluate, MoveApplyMachine.movePhase, failed,
          MoveApplyMachine.evaluateDispatch]
      rw [result] at returned
      cases returned
  | some pair =>
      rcases pair with ⟨move, rest⟩
      exact ⟨move, rest, rfl, move_start_parse_success_data D move rest parsed,
        move_start_parse_success_certificate D move rest parsed,
        (parseMoveRun_iff D.certificate move rest).mp parsed,
        parseMoveRun_consumed_length D.certificate move rest parsed,
        parseMoveRun_consumes_two D.certificate move rest parsed,
        parseMoveRun_rest_length_lt D.certificate move rest parsed⟩

/-- This is the well-founded certificate measure for a genuine full parser-start
success; it makes no such claim about arbitrary partial MoveApply phases. -/
theorem move_start_success_certificate_lt (D : MoveApplyMachine.LocalData)
    (returned : (MoveApplyMachine.evaluate (MoveApplyMachine.movePhase .start) D).result =
      MoveApplyMachine.success) :
    (MoveApplyMachine.evaluate (MoveApplyMachine.movePhase .start) D).data.certificate.length <
      D.certificate.length := by
  obtain ⟨move, rest, parsed, intermediate, certificate, encoded, consumed, two, less⟩ :=
    move_start_success_has_parse D returned
  rw [certificate]
  exact less

/-- Connected intermediate case: two old reverse branches precede the parsed
branch and the old forward branch, while the source suffix remains literal. -/
theorem move_start_dirty_reverse_example (tail source saved scratch : Word) (pending : List Unit) :
    let D : MoveApplyMachine.LocalData :=
      ⟨moveCode ⟨.left, [.right]⟩ ++ tail, [.left, .right], [.left], source, saved, scratch, pending⟩
    MoveApplyMachine.moveFinish .start D =
      ⟨.success .left, ⟨tail, [], [.right, .left, .right, .left], source, saved, scratch, pending⟩⟩ ∧
      MoveParserMachine.phaseSteps .start D.certificate D.moveReverse = 7 := by
  dsimp only
  have parsed := congrArg Prod.fst (parseMoveRun_code (⟨.left, [.right]⟩ : RotationMove) tail)
  constructor
  · exact move_start_parse_success_data
        ⟨moveCode ⟨.left, [.right]⟩ ++ tail, [.left, .right], [.left], source, saved, scratch, pending⟩
        ⟨.left, [.right]⟩ tail parsed
  · exact move_start_parse_success_steps
        ⟨moveCode ⟨.left, [.right]⟩ ++ tail, [.left, .right], [.left], source, saved, scratch, pending⟩
        ⟨.left, [.right]⟩ tail parsed

-- END SOURCE BRIDGE CHECK3

variable [DecidableEq K]

def step (caller : External Λ → Statement Γ Λ R) : Cfg Γ Λ R → Option (Cfg Γ Λ R) :=
  Turing.TM2.step (program caller)

def next (caller : External Λ → Statement Γ Λ R) (c : Option (Cfg Γ Λ R)) :
    Option (Cfg Γ Λ R) := c.bind (step caller)

variable (caller : External Λ → Statement Γ Λ R)

@[simp] theorem next_some (c : Cfg Γ Λ R) : next caller (some c) = step caller c := rfl
@[simp] theorem next_none : next caller none = none := rfl

theorem next_iterate_none (n : Nat) : (next caller)^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, next_none]

theorem fuel_join_step (r : FuelDispatchMachine.Exit) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel (fuelJoinPhase r))) regs D ctx) =
      some (cfg (some (fuelJoinTarget r)) (resetAll regs) D ctx) := by cases r <;> rfl

theorem apply_join_step (r : MoveApplyMachine.FinalResult) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel (applyJoinPhase r))) regs D ctx) =
      some (cfg (some (applyJoinTarget r)) (resetAll regs) D ctx) := rfl

theorem equality_join_step (r : TreeEqualityMachine.Result) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel (equalityJoinPhase r))) regs D ctx) =
      some (cfg (some (equalityJoinTarget r)) (resetAll regs) D ctx) := rfl

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


theorem fuel_join_localRun (r : FuelDispatchMachine.Exit) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    LocalRun caller 1 (cfg (some (phaseLabel (fuelJoinPhase r))) regs D ctx)
      (cfg (some (fuelJoinTarget r)) (resetAll regs) D ctx) :=
  phase_step_localRun caller (fuel_join_step caller r D regs ctx)

theorem apply_join_localRun (r : MoveApplyMachine.FinalResult) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    LocalRun caller 1 (cfg (some (phaseLabel (applyJoinPhase r))) regs D ctx)
      (cfg (some (applyJoinTarget r)) (resetAll regs) D ctx) :=
  phase_step_localRun caller (apply_join_step caller r D regs ctx)

theorem equality_join_localRun (r : TreeEqualityMachine.Result) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    LocalRun caller 1 (cfg (some (phaseLabel (equalityJoinPhase r))) regs D ctx)
      (cfg (some (equalityJoinTarget r)) (resetAll regs) D ctx) :=
  phase_step_localRun caller (equality_join_step caller r D regs ctx)

omit [DecidableEq K] in
theorem fuel_body_agrees
    (localCaller : (FuelDispatchMachine.Exit ⊕ FuelCallerLabel Λ) → FuelStatement Γ Λ R)
    (label : FuelDispatchMachine.Label (FuelCallerLabel Λ)) (owned : FuelDispatchMachine.Owned (some label)) :
    program caller (fuelLabelEquiv label) = fuelTranslate (FuelDispatchMachine.program localCaller label) := by
  rcases owned with core | inspect
  · cases label with
    | inl q => rfl
    | inr external => cases core
  · have same : label = FuelDispatchMachine.inspectLabel := Option.some.inj inspect
    subst label
    rfl

omit [DecidableEq K] in
theorem apply_body_agrees
    (localCaller : MoveApplyMachine.External (ApplyCallerLabel Λ) → ApplyStatement Γ Λ R)
    (label : MoveApplyMachine.Label (ApplyCallerLabel Λ)) (owned : MoveApplyMachine.Owned (some label)) :
    program caller (applyLabelEquiv label) = applyTranslate (MoveApplyMachine.program localCaller label) := by
  rcases label with q | (r | (q | external))
  · rfl
  · rfl
  · rfl
  · cases owned

omit [DecidableEq K] in
theorem equality_body_agrees
    (localCaller : TreeEqualityMachine.External (EqualityCallerLabel Λ) → EqualityStatement Γ Λ R)
    (label : TreeEqualityMachine.Label (EqualityCallerLabel Λ)) (owned : TreeEqualityMachine.Owned (some label)) :
    program caller (equalityLabelEquiv label) = equalityTranslate (TreeEqualityMachine.program localCaller label) := by
  cases label with
  | inl q => cases q; rfl
  | inr external => cases owned

omit [DecidableEq K] in
theorem owned_fuelCfg (c : FuelCfg Γ Λ R) (owned : FuelDispatchMachine.Owned c.l) :
    Owned (fuelCfg c).l := by
  rcases owned with core | inspect
  · cases labelEq : c.l with
    | none => simp only [labelEq, Resources.BinaryCounter.FixedWidthMachine.Owned] at core
    | some label => cases label with
      | inl q => change Owned (c.l.map fuelLabelEquiv); rw [labelEq]; trivial
      | inr external => simp only [labelEq, Resources.BinaryCounter.FixedWidthMachine.Owned] at core
  · change Owned (c.l.map fuelLabelEquiv)
    rw [inspect]
    trivial

omit [DecidableEq K] in
theorem owned_applyCfg (c : ApplyCfg Γ Λ R) (owned : MoveApplyMachine.Owned c.l) :
    Owned (applyCfg c).l := by
  cases labelEq : c.l with
  | none => simp only [labelEq, MoveApplyMachine.Owned] at owned
  | some label =>
      rcases label with q | (r | (q | external))
      · change Owned (c.l.map applyLabelEquiv); rw [labelEq]; trivial
      · change Owned (c.l.map applyLabelEquiv); rw [labelEq]; trivial
      · change Owned (c.l.map applyLabelEquiv); rw [labelEq]; trivial
      · simp only [labelEq, MoveApplyMachine.Owned] at owned

omit [DecidableEq K] in
theorem owned_equalityCfg (c : EqualityCfg Γ Λ R) (owned : TreeEqualityMachine.Owned c.l) :
    Owned (equalityCfg c).l := by
  cases labelEq : c.l with
  | none => simp only [labelEq, TreeEqualityMachine.Owned] at owned
  | some label => cases label with
    | inl q => change Owned (c.l.map equalityLabelEquiv); rw [labelEq]; trivial
    | inr external => simp only [labelEq, TreeEqualityMachine.Owned] at owned

theorem fuel_step_transport
    (localCaller : (FuelDispatchMachine.Exit ⊕ FuelCallerLabel Λ) → FuelStatement Γ Λ R)
    (c : FuelCfg Γ Λ R) (owned : FuelDispatchMachine.Owned c.l) :
    step caller (fuelCfg c) = (FuelDispatchMachine.step localCaller c).map fuelCfg := by
  exact FrontEndMachine.Transport.step_owned fuelStackEquiv fuelSymbolEquiv fuelRegisterEquiv
    fuelLabelEquiv (FuelDispatchMachine.program localCaller) (program caller) FuelDispatchMachine.Owned
    (fuel_body_agrees caller localCaller) c owned

theorem fuel_prefix_transport
    (localCaller : (FuelDispatchMachine.Exit ⊕ FuelCallerLabel Λ) → FuelStatement Γ Λ R)
    (n : Nat) (start : FuelCfg Γ Λ R)
    (earlier : ∀ j, j < n → ∃ reached,
      (FuelDispatchMachine.next localCaller)^[j] (some start) = some reached ∧ FuelDispatchMachine.Owned reached.l) :
    (next caller)^[n] (some (fuelCfg start)) =
      ((FuelDispatchMachine.next localCaller)^[n] (some start)).map fuelCfg := by
  exact FrontEndMachine.Transport.iterate_owned fuelStackEquiv fuelSymbolEquiv fuelRegisterEquiv
    fuelLabelEquiv (FuelDispatchMachine.program localCaller) (program caller) FuelDispatchMachine.Owned
    (fuel_body_agrees caller localCaller) n start earlier

omit [DecidableEq K] in
def toFuelCfg (c : Cfg Γ Λ R) : FuelCfg Γ Λ R :=
  fuelView (c.l.map fuelLabelEquiv.symm) (fuelRegisterEquiv.symm c.var)
    (dataOfCfg c) (contextOfCfg c)

omit [DecidableEq K] in
theorem fuelCfg_toFuelCfg (c : Cfg Γ Λ R) : fuelCfg (toFuelCfg c) = c := by
  unfold toFuelCfg
  rw [fuelCfg_view, Equiv.apply_symm_apply]
  have labelEq : (c.l.map fuelLabelEquiv.symm).map fuelLabelEquiv = c.l := by
    cases c.l <;> simp
  rw [labelEq]
  exact cfg_eta c

theorem apply_step_transport
    (localCaller : MoveApplyMachine.External (ApplyCallerLabel Λ) → ApplyStatement Γ Λ R)
    (c : ApplyCfg Γ Λ R) (owned : MoveApplyMachine.Owned c.l) :
    step caller (applyCfg c) = (MoveApplyMachine.step localCaller c).map applyCfg := by
  exact FrontEndMachine.Transport.step_owned applyStackEquiv applySymbolEquiv applyRegisterEquiv
    applyLabelEquiv (MoveApplyMachine.program localCaller) (program caller) MoveApplyMachine.Owned
    (apply_body_agrees caller localCaller) c owned

theorem apply_prefix_transport
    (localCaller : MoveApplyMachine.External (ApplyCallerLabel Λ) → ApplyStatement Γ Λ R)
    (n : Nat) (start : ApplyCfg Γ Λ R)
    (earlier : ∀ j, j < n → ∃ reached,
      (MoveApplyMachine.next localCaller)^[j] (some start) = some reached ∧ MoveApplyMachine.Owned reached.l) :
    (next caller)^[n] (some (applyCfg start)) =
      ((MoveApplyMachine.next localCaller)^[n] (some start)).map applyCfg := by
  exact FrontEndMachine.Transport.iterate_owned applyStackEquiv applySymbolEquiv applyRegisterEquiv
    applyLabelEquiv (MoveApplyMachine.program localCaller) (program caller) MoveApplyMachine.Owned
    (apply_body_agrees caller localCaller) n start earlier

omit [DecidableEq K] in
def toApplyCfg (c : Cfg Γ Λ R) : ApplyCfg Γ Λ R :=
  applyView (c.l.map applyLabelEquiv.symm) (applyRegisterEquiv.symm c.var)
    (dataOfCfg c) (contextOfCfg c)

omit [DecidableEq K] in
theorem applyCfg_toApplyCfg (c : Cfg Γ Λ R) : applyCfg (toApplyCfg c) = c := by
  unfold toApplyCfg
  rw [applyCfg_view, Equiv.apply_symm_apply]
  have labelEq : (c.l.map applyLabelEquiv.symm).map applyLabelEquiv = c.l := by
    cases c.l <;> simp
  rw [labelEq]
  exact cfg_eta c

theorem equality_step_transport
    (localCaller : TreeEqualityMachine.External (EqualityCallerLabel Λ) → EqualityStatement Γ Λ R)
    (c : EqualityCfg Γ Λ R) (owned : TreeEqualityMachine.Owned c.l) :
    step caller (equalityCfg c) = (TreeEqualityMachine.step localCaller c).map equalityCfg := by
  exact FrontEndMachine.Transport.step_owned equalityStackEquiv equalitySymbolEquiv equalityRegisterEquiv
    equalityLabelEquiv (TreeEqualityMachine.program localCaller) (program caller) TreeEqualityMachine.Owned
    (equality_body_agrees caller localCaller) c owned

theorem equality_prefix_transport
    (localCaller : TreeEqualityMachine.External (EqualityCallerLabel Λ) → EqualityStatement Γ Λ R)
    (n : Nat) (start : EqualityCfg Γ Λ R)
    (earlier : ∀ j, j < n → ∃ reached,
      (TreeEqualityMachine.next localCaller)^[j] (some start) = some reached ∧ TreeEqualityMachine.Owned reached.l) :
    (next caller)^[n] (some (equalityCfg start)) =
      ((TreeEqualityMachine.next localCaller)^[n] (some start)).map equalityCfg := by
  exact FrontEndMachine.Transport.iterate_owned equalityStackEquiv equalitySymbolEquiv equalityRegisterEquiv
    equalityLabelEquiv (TreeEqualityMachine.program localCaller) (program caller) TreeEqualityMachine.Owned
    (equality_body_agrees caller localCaller) n start earlier

omit [DecidableEq K] in
def toEqualityCfg (c : Cfg Γ Λ R) : EqualityCfg Γ Λ R :=
  equalityView (c.l.map equalityLabelEquiv.symm) (equalityRegisterEquiv.symm c.var)
    (dataOfCfg c) (contextOfCfg c)

omit [DecidableEq K] in
theorem equalityCfg_toEqualityCfg (c : Cfg Γ Λ R) : equalityCfg (toEqualityCfg c) = c := by
  unfold toEqualityCfg
  rw [equalityCfg_view, Equiv.apply_symm_apply]
  have labelEq : (c.l.map equalityLabelEquiv.symm).map equalityLabelEquiv = c.l := by
    cases c.l <;> simp
  rw [labelEq]
  exact cfg_eta c

/-- Every arbitrary partial MoveApply segment transports with its full complement. -/
theorem apply_localRun_transport
    (localCaller : MoveApplyMachine.External (ApplyCallerLabel Λ) → ApplyStatement Γ Λ R)
    {n : Nat} {a b : ApplyCfg Γ Λ R} (run : MoveApplyMachine.LocalRun localCaller n a b) :
    LocalRun caller n (applyCfg a) (applyCfg b) := by
  induction run with
  | refl => exact .refl _
  | @cons n before middle after head tail ih =>
      refine .cons ⟨owned_applyCfg before head.1, ?_⟩ ih
      rw [apply_step_transport caller localCaller before head.1, head.2]
      rfl

omit [DecidableEq K] in
structure CounterFinish where
  result : Resources.BinaryCounter.FixedWidthMachine.Result
  data : LocalData
  steps : Nat
  deriving DecidableEq

omit [DecidableEq K] in
def counterFinish (q : Resources.BinaryCounter.FixedWidthMachine.Phase) (D : LocalData) : CounterFinish :=
  match q with
  | .borrow =>
      let result := Resources.BinaryCounter.FixedWidthMachine.predSpec (List.replicate D.units.length false ++ D.fuel)
      ⟨result.1, { D with fuel := result.2, units := [] }, Resources.BinaryCounter.FixedWidthMachine.runSteps D.fuel + D.units.length⟩
  | .restoreTrue =>
      ⟨.positive, { D with fuel := List.replicate D.units.length true ++ D.fuel, units := [] },
        D.units.length + 1⟩
  | .restoreFalse =>
      ⟨.zero, { D with fuel := List.replicate D.units.length false ++ D.fuel, units := [] },
        D.units.length + 1⟩

omit [DecidableEq K] in
@[simp] theorem counterFinish_steps (q : Resources.BinaryCounter.FixedWidthMachine.Phase) (D : LocalData) :
    (counterFinish q D).steps = Resources.BinaryCounter.FixedWidthMachine.phaseSteps q D.fuel D.units := by cases q <;> rfl

omit [DecidableEq K] in
@[simp] theorem counterFinish_certificate (q : Resources.BinaryCounter.FixedWidthMachine.Phase) (D : LocalData) :
    (counterFinish q D).data.certificate = D.certificate := by cases q <;> rfl

omit [DecidableEq K] in
@[simp] theorem counterFinish_context (q : Resources.BinaryCounter.FixedWidthMachine.Phase) (D : LocalData) (ctx : ∀ k, List (Γ k)) :
    fuelContext (counterFinish q D).data ctx = fuelContext D ctx := by cases q <;> rfl

theorem counter_component_iterate
    (localCaller : (FuelDispatchMachine.Exit ⊕ FuelCallerLabel Λ) → FuelStatement Γ Λ R)
    (q : Resources.BinaryCounter.FixedWidthMachine.Phase) (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (FuelDispatchMachine.next localCaller)^[(counterFinish q D).steps]
      (some (fuelView (some (Resources.BinaryCounter.FixedWidthMachine.phaseLabel q)) regs D ctx)) =
      some (fuelView (some (Resources.BinaryCounter.FixedWidthMachine.resultLabel (counterFinish q D).result))
        (Resources.BinaryCounter.FixedWidthMachine.reset regs) (counterFinish q D).data ctx) := by
  cases q with
  | borrow =>
      exact Resources.BinaryCounter.FixedWidthMachine.borrow_iterate (FuelDispatchMachine.callerHandler localCaller)
        D.fuel D.units regs (FuelDispatchMachine.stores D.certificate (fuelContext D ctx))
  | restoreTrue =>
      exact Resources.BinaryCounter.FixedWidthMachine.restoreTrue_iterate (FuelDispatchMachine.callerHandler localCaller)
        D.fuel D.units regs (FuelDispatchMachine.stores D.certificate (fuelContext D ctx))
  | restoreFalse =>
      exact Resources.BinaryCounter.FixedWidthMachine.restoreFalse_iterate (FuelDispatchMachine.callerHandler localCaller)
        D.fuel D.units regs (FuelDispatchMachine.stores D.certificate (fuelContext D ctx))

theorem counter_phase_localRun (q : Resources.BinaryCounter.FixedWidthMachine.Phase) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (counterFinish q D).steps
      (cfg (some (phaseLabel (counterPhase q))) regs D ctx)
      (cfg (some (phaseLabel (fuelJoinPhase (FuelDispatchMachine.exitOfResult (counterFinish q D).result))))
        (resetFuel regs) (counterFinish q D).data ctx) := by
  let localCaller : (FuelDispatchMachine.Exit ⊕ FuelCallerLabel Λ) → FuelStatement Γ Λ R := fun _ => .halt
  let start : FuelCfg Γ Λ R := fuelView (some (Resources.BinaryCounter.FixedWidthMachine.phaseLabel q)) regs D ctx
  have startEq : fuelCfg start = cfg (some (phaseLabel (counterPhase q))) regs D ctx := by
    rw [fuelCfg_view]
    rfl
  have earlier : ∀ j, j < (counterFinish q D).steps → ∃ reached,
      (FuelDispatchMachine.next localCaller)^[j] (some start) = some reached ∧ FuelDispatchMachine.Owned reached.l := by
    intro j strict
    have bound : j ≤ Resources.BinaryCounter.FixedWidthMachine.phaseSteps q D.fuel D.units := by rw [← counterFinish_steps]; omega
    obtain ⟨reached, executed, rank, path, owned, reset⟩ :=
      Resources.BinaryCounter.FixedWidthMachine.phase_prefix (FuelDispatchMachine.callerHandler localCaller) q D.fuel D.units regs
        (FuelDispatchMachine.stores D.certificate (fuelContext D ctx)) j bound
    exact ⟨reached, executed, Or.inl (owned.mp (by rwa [← counterFinish_steps]))⟩
  apply LocalRun.of_iterate caller
  · rw [← startEq, fuel_prefix_transport caller localCaller _ start earlier,
      counter_component_iterate localCaller q D regs ctx]
    change some (fuelCfg (fuelView _ _ _ _)) = _
    rw [fuelCfg_view]
    congr 1
    apply cfg_ext
    · cases (counterFinish q D).result <;> rfl
    · rfl
    · rfl
  · intro j strict
    obtain ⟨reached, executed, owned⟩ := earlier j strict
    refine ⟨fuelCfg reached, ?_, owned_fuelCfg reached owned⟩
    rw [← startEq, fuel_prefix_transport caller localCaller j start
      (fun k bound => earlier k (by omega)), executed]
    rfl

theorem inspect_step_nil (D : LocalData) (empty : D.certificate = []) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel inspectPhase)) regs D ctx) =
      some (cfg (some (phaseLabel (fuelJoinPhase .atEnd))) (resetFuel regs) D ctx) := by
  let localCaller : (FuelDispatchMachine.Exit ⊕ FuelCallerLabel Λ) → FuelStatement Γ Λ R := fun _ => .halt
  have view : fuelCfg (Λ := Λ) (fuelView (some FuelDispatchMachine.inspectLabel) regs D ctx) =
      cfg (some (phaseLabel inspectPhase)) regs D ctx := by
    simpa only [Option.map_some, fuelLabelEquiv_inspect, fuelRegisterEquiv, Equiv.refl_apply] using
      fuelCfg_view (some (FuelDispatchMachine.inspectLabel (Λ := FuelCallerLabel Λ))) regs D ctx
  rw [← view, fuel_step_transport caller localCaller _ (Or.inr rfl)]
  have run : FuelDispatchMachine.step localCaller
      (fuelView (some FuelDispatchMachine.inspectLabel) regs D ctx) =
      some (fuelView (some FuelDispatchMachine.atEndLabel)
        (Resources.BinaryCounter.FixedWidthMachine.reset regs) D ctx) := by
    simpa only [fuelView, empty] using
      FuelDispatchMachine.dispatch_step_nil localCaller D.fuel D.units regs (fuelContext D ctx)
  rw [run]
  change some (fuelCfg (fuelView _ _ _ _)) = _
  rw [fuelCfg_view]
  rfl

theorem inspect_step_cons (D : LocalData) (tag : Tag) (raw : Word)
    (nonempty : D.certificate = tag :: raw) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel inspectPhase)) regs D ctx) =
      some (cfg (some (phaseLabel (counterPhase .borrow))) (resetFuel regs) D ctx) := by
  let localCaller : (FuelDispatchMachine.Exit ⊕ FuelCallerLabel Λ) → FuelStatement Γ Λ R := fun _ => .halt
  have view : fuelCfg (Λ := Λ) (fuelView (some FuelDispatchMachine.inspectLabel) regs D ctx) =
      cfg (some (phaseLabel inspectPhase)) regs D ctx := by
    simpa only [Option.map_some, fuelLabelEquiv_inspect, fuelRegisterEquiv, Equiv.refl_apply] using
      fuelCfg_view (some (FuelDispatchMachine.inspectLabel (Λ := FuelCallerLabel Λ))) regs D ctx
  rw [← view, fuel_step_transport caller localCaller _ (Or.inr rfl)]
  have run : FuelDispatchMachine.step localCaller
      (fuelView (some FuelDispatchMachine.inspectLabel) regs D ctx) =
      some (fuelView (some (Resources.BinaryCounter.FixedWidthMachine.phaseLabel .borrow))
        (Resources.BinaryCounter.FixedWidthMachine.reset regs) D ctx) := by
    simpa only [fuelView, nonempty] using
      FuelDispatchMachine.dispatch_step_cons localCaller D.fuel D.units tag raw regs (fuelContext D ctx)
  rw [run]
  change some (fuelCfg (fuelView _ _ _ _)) = _
  rw [fuelCfg_view]
  rfl


omit [DecidableEq K] in
@[simp] theorem resetFuel_resetFuel (regs : Registers R) :
    resetFuel (resetFuel regs) = resetFuel regs := rfl

omit [DecidableEq K] in
structure InspectStageFinish where
  result : FuelDispatchMachine.Exit
  data : LocalData
  steps : Nat
  deriving DecidableEq

omit [DecidableEq K] in
def inspectStageFinish (D : LocalData) : InspectStageFinish :=
  match D.certificate with
  | [] => ⟨.atEnd, D, 1⟩
  | _ :: _ =>
      let actual := counterFinish .borrow D
      ⟨FuelDispatchMachine.exitOfResult actual.result, actual.data, 1 + actual.steps⟩

theorem inspect_stage_localRun (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (inspectStageFinish D).steps
      (cfg (some (phaseLabel inspectPhase)) regs D ctx)
      (cfg (some (phaseLabel (fuelJoinPhase (inspectStageFinish D).result)))
        (resetFuel regs) (inspectStageFinish D).data ctx) := by
  cases certificate : D.certificate with
  | nil =>
      simp only [inspectStageFinish, certificate]
      exact phase_step_localRun caller (inspect_step_nil caller D certificate regs ctx)
  | cons tag raw =>
      simp only [inspectStageFinish, certificate]
      have first := phase_step_localRun caller (inspect_step_cons caller D tag raw certificate regs ctx)
      have rest := counter_phase_localRun caller .borrow D (resetFuel regs) ctx
      simpa only [resetFuel_resetFuel] using LocalRun.trans caller first rest

omit [DecidableEq K] in
structure ApplyFinish where
  result : MoveApplyMachine.FinalResult
  data : LocalData
  steps : Nat
  deriving DecidableEq

omit [DecidableEq K] in
def applyFinish (q : MoveApplyMachine.Phase) (D : LocalData) : ApplyFinish :=
  let actual := MoveApplyMachine.evaluate q (applyData D)
  ⟨actual.result, setApplyData D actual.data, actual.steps⟩

omit [DecidableEq K] in
theorem applyFinish_transport (q : MoveApplyMachine.Phase) (D : LocalData)
    (regs : MoveApplyMachine.Registers (ApplyCallerRegister R)) (ctx : ∀ k, List (Γ k)) :
    applyCfg (Λ := Λ) (MoveApplyMachine.phaseResult q regs (applyData D) (applyContext D ctx)) =
      cfg (some (phaseLabel (applyJoinPhase (applyFinish q D).result)))
        (resetApply (applyRegisterEquiv regs)) (applyFinish q D).data ctx := by
  change applyCfg (applyView (some (MoveApplyMachine.resultLabel (applyFinish q D).result))
    (MoveApplyMachine.reset regs) (applyFinish q D).data ctx) = _
  rw [applyCfg_view]
  rfl

theorem apply_phase_localRun (q : MoveApplyMachine.Phase) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (applyFinish q D).steps
      (cfg (some (phaseLabel (applyPhase q))) regs D ctx)
      (cfg (some (phaseLabel (applyJoinPhase (applyFinish q D).result)))
        (resetApply regs) (applyFinish q D).data ctx) := by
  let localCaller : MoveApplyMachine.External (ApplyCallerLabel Λ) → ApplyStatement Γ Λ R := fun _ => .halt
  have run := apply_localRun_transport caller localCaller
    (MoveApplyMachine.phase_localRun localCaller q (applyData D) (applyRegisterEquiv.symm regs) (applyContext D ctx))
  change LocalRun caller _ (applyCfg (applyView _ _ D ctx)) _ at run
  rw [applyCfg_view, applyFinish_transport, Equiv.apply_symm_apply] at run
  change LocalRun caller (MoveApplyMachine.phaseSteps q (applyData D)) _ _
  simpa only [Option.map_some, applyLabelEquiv_phase] using run

omit [DecidableEq K] in
structure EqualityFinish where
  result : TreeEqualityMachine.Result
  data : LocalData
  steps : Nat
  deriving DecidableEq

omit [DecidableEq K] in
def equalityFinish (D : LocalData) : EqualityFinish :=
  let n := TreeEqualityMachine.runSteps D.source D.target
  ⟨TreeEqualityMachine.wordResult D.source D.target,
    { D with source := D.source.drop n, target := D.target.drop n }, n⟩

omit [DecidableEq K] in
theorem equalityFinish_transport (D : LocalData)
    (regs : TreeEqualityMachine.Registers (EqualityCallerRegister R)) (ctx : ∀ k, List (Γ k)) :
    equalityCfg (Λ := Λ) (TreeEqualityMachine.resultCfg D.source D.target regs (equalityContext D ctx)) =
      cfg (some (phaseLabel (equalityJoinPhase (equalityFinish D).result)))
        (resetEquality (equalityRegisterEquiv regs)) (equalityFinish D).data ctx := by
  change equalityCfg (equalityView (some (TreeEqualityMachine.resultLabel (equalityFinish D).result))
    (TreeEqualityMachine.reset regs) (equalityFinish D).data ctx) = _
  rw [equalityCfg_view]
  rfl

theorem equality_phase_localRun (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (equalityFinish D).steps
      (cfg (some (phaseLabel comparePhase)) regs D ctx)
      (cfg (some (phaseLabel (equalityJoinPhase (equalityFinish D).result)))
        (resetEquality regs) (equalityFinish D).data ctx) := by
  let localCaller : TreeEqualityMachine.External (EqualityCallerLabel Λ) → EqualityStatement Γ Λ R := fun _ => .halt
  let start : EqualityCfg Γ Λ R :=
    equalityView (some (TreeEqualityMachine.phaseLabel .compare)) (equalityRegisterEquiv.symm regs) D ctx
  have startEq : equalityCfg start = cfg (some (phaseLabel comparePhase)) regs D ctx := by
    rw [equalityCfg_view]
    simp only [Option.map_some, equalityLabelEquiv_phase, Equiv.apply_symm_apply]
  have earlier : ∀ j, j < (equalityFinish D).steps → ∃ reached,
      (TreeEqualityMachine.next localCaller)^[j] (some start) = some reached ∧ TreeEqualityMachine.Owned reached.l := by
    intro j strict
    refine ⟨TreeEqualityMachine.prefixCfg D.source D.target (equalityRegisterEquiv.symm regs) (equalityContext D ctx) j,
      TreeEqualityMachine.prefix_exact localCaller D.source D.target (equalityRegisterEquiv.symm regs)
        (equalityContext D ctx) j (Nat.le_of_lt strict), ?_⟩
    exact (TreeEqualityMachine.first_return localCaller D.source D.target (equalityRegisterEquiv.symm regs)
      (equalityContext D ctx)).2.2 j strict
  apply LocalRun.of_iterate caller
  · rw [← startEq, equality_prefix_transport caller localCaller _ start earlier]
    have whole := TreeEqualityMachine.run localCaller D.source D.target (equalityRegisterEquiv.symm regs) (equalityContext D ctx)
    change (TreeEqualityMachine.next localCaller)^[(equalityFinish D).steps] (some start) = _ at whole
    rw [whole]
    change some (equalityCfg _) = _
    rw [equalityFinish_transport, Equiv.apply_symm_apply]
  · intro j strict
    obtain ⟨reached, executed, owned⟩ := earlier j strict
    refine ⟨equalityCfg reached, ?_, owned_equalityCfg reached owned⟩
    rw [← startEq, equality_prefix_transport caller localCaller j start
      (fun k bound => earlier k (by omega)), executed]
    rfl


omit [DecidableEq K] in
theorem apply_start_certificate_lt (D : LocalData)
    (returned : (applyFinish (MoveApplyMachine.movePhase .start) D).result = MoveApplyMachine.success) :
    (applyFinish (MoveApplyMachine.movePhase .start) D).data.certificate.length < D.certificate.length :=
  move_start_success_certificate_lt (applyData D) returned

omit [DecidableEq K] in
structure Evaluation where
  result : Bool
  data : LocalData
  steps : Nat
  deriving DecidableEq

omit [DecidableEq K] in
def addSteps (n : Nat) (actual : Evaluation) : Evaluation :=
  ⟨actual.result, actual.data, n + actual.steps⟩

omit [DecidableEq K] in
def evaluateEquality (D : LocalData) : Evaluation :=
  let actual := equalityFinish D
  ⟨equalityResult actual.result, actual.data, actual.steps + 1⟩

omit [DecidableEq K] in
/-- Total proof-side inspection. Recursion occurs only after a full MoveApplyMachine.start
success, whose actual certificate suffix is strictly shorter even with dirty B. -/
def evaluateInspect (D : LocalData) : Evaluation :=
  if D.certificate = [] then
    addSteps 2 (evaluateEquality D)
  else
    let fuel := counterFinish .borrow D
    match fuel.result with
    | .zero => ⟨false, fuel.data, fuel.steps + 2⟩
    | .positive =>
        let applied := applyFinish (MoveApplyMachine.movePhase .start) fuel.data
        match returned : applied.result with
        | .inl _ => ⟨false, applied.data, fuel.steps + applied.steps + 3⟩
        | .inr .failure => ⟨false, applied.data, fuel.steps + applied.steps + 3⟩
        | .inr .success =>
            addSteps (fuel.steps + applied.steps + 3) (evaluateInspect applied.data)
termination_by D.certificate.length
decreasing_by
  simpa only [counterFinish_certificate] using
    apply_start_certificate_lt (counterFinish .borrow D).data returned

omit [DecidableEq K] in
def evaluateApplyJoin (r : MoveApplyMachine.FinalResult) (D : LocalData) : Evaluation :=
  match r with
  | .inl _ | .inr .failure => ⟨false, D, 1⟩
  | .inr .success => addSteps 1 (evaluateInspect D)

omit [DecidableEq K] in
def evaluateApply (q : MoveApplyMachine.Phase) (D : LocalData) : Evaluation :=
  let actual := applyFinish q D
  addSteps actual.steps (evaluateApplyJoin actual.result actual.data)

omit [DecidableEq K] in
def evaluateFuelJoin (r : FuelDispatchMachine.Exit) (D : LocalData) : Evaluation :=
  match r with
  | .atEnd => addSteps 1 (evaluateEquality D)
  | .positive => addSteps 1 (evaluateApply (MoveApplyMachine.movePhase .start) D)
  | .zero => ⟨false, D, 1⟩

omit [DecidableEq K] in
def evaluateCounter (q : Resources.BinaryCounter.FixedWidthMachine.Phase) (D : LocalData) : Evaluation :=
  let actual := counterFinish q D
  addSteps actual.steps (evaluateFuelJoin (FuelDispatchMachine.exitOfResult actual.result) actual.data)

omit [DecidableEq K] in
def evaluate (q : Phase) (D : LocalData) : Evaluation :=
  match q with
  | .inl (.inl q) => evaluateCounter q D
  | .inl (.inr (.inl r)) => evaluateFuelJoin (FuelDispatchMachine.exitOfResult r) D
  | .inl (.inr (.inr (.inl .inspectCertificate))) => evaluateInspect D
  | .inl (.inr (.inr (.inl .atEnd))) => evaluateFuelJoin .atEnd D
  | .inl (.inr (.inr (.inr impossible))) => Empty.elim impossible
  | .inr (.inl (.inl q)) => evaluateApply (MoveApplyMachine.movePhase q) D
  | .inr (.inl (.inr (.inl r))) => evaluateApply (MoveApplyMachine.dispatchPhase r) D
  | .inr (.inl (.inr (.inr (.inl q)))) => evaluateApply (MoveApplyMachine.positionPhase q) D
  | .inr (.inl (.inr (.inr (.inr (.inl r))))) => evaluateApplyJoin r D
  | .inr (.inl (.inr (.inr (.inr (.inr impossible))))) => Empty.elim impossible
  | .inr (.inr (.inl .compare)) => evaluateEquality D
  | .inr (.inr (.inr (.inl r))) => ⟨equalityResult r, D, 1⟩
  | .inr (.inr (.inr (.inr impossible))) => Empty.elim impossible

omit [DecidableEq K] in
def phaseSteps (q : Phase) (D : LocalData) : Nat := (evaluate q D).steps

omit [DecidableEq K] in
def evaluationCfg (regs : Registers R) (actual : Evaluation) (ctx : ∀ k, List (Γ k)) : Cfg Γ Λ R :=
  cfg (some (resultLabel actual.result)) (resetAll regs) actual.data ctx

omit [DecidableEq K] in
def phaseResult (q : Phase) (regs : Registers R) (D : LocalData)
    (ctx : ∀ k, List (Γ k)) : Cfg Γ Λ R := evaluationCfg regs (evaluate q D) ctx

omit [DecidableEq K] in
@[simp] theorem evaluationCfg_addSteps (regs : Registers R) (n : Nat) (actual : Evaluation)
    (ctx : ∀ k, List (Γ k)) :
    evaluationCfg (Λ := Λ) regs (addSteps n actual) ctx = evaluationCfg regs actual ctx := rfl

omit [DecidableEq K] in
@[simp] theorem evaluationCfg_resetAll (regs : Registers R) (actual : Evaluation)
    (ctx : ∀ k, List (Γ k)) :
    evaluationCfg (Λ := Λ) (resetAll regs) actual ctx = evaluationCfg regs actual ctx := rfl

omit [DecidableEq K] in
@[simp] theorem evaluationCfg_resetFuel (regs : Registers R) (actual : Evaluation)
    (ctx : ∀ k, List (Γ k)) :
    evaluationCfg (Λ := Λ) (resetFuel regs) actual ctx = evaluationCfg regs actual ctx := rfl

omit [DecidableEq K] in
@[simp] theorem evaluationCfg_resetApply (regs : Registers R) (actual : Evaluation)
    (ctx : ∀ k, List (Γ k)) :
    evaluationCfg (Λ := Λ) (resetApply regs) actual ctx = evaluationCfg regs actual ctx := rfl

omit [DecidableEq K] in
@[simp] theorem evaluationCfg_resetEquality (regs : Registers R) (actual : Evaluation)
    (ctx : ∀ k, List (Γ k)) :
    evaluationCfg (Λ := Λ) (resetEquality regs) actual ctx = evaluationCfg regs actual ctx := rfl

omit [DecidableEq K] in
@[simp] theorem evaluate_inspect (D : LocalData) : evaluate inspectPhase D = evaluateInspect D := rfl

omit [DecidableEq K] in
@[simp] theorem evaluate_counter (q : Resources.BinaryCounter.FixedWidthMachine.Phase) (D : LocalData) :
    evaluate (counterPhase q) D = evaluateCounter q D := rfl

omit [DecidableEq K] in
@[simp] theorem evaluate_fuelJoin (r : FuelDispatchMachine.Exit) (D : LocalData) :
    evaluate (fuelJoinPhase r) D = evaluateFuelJoin r D := by cases r <;> rfl

omit [DecidableEq K] in
@[simp] theorem evaluate_apply (q : MoveApplyMachine.Phase) (D : LocalData) :
    evaluate (applyPhase q) D = evaluateApply q D := by
  cases q with
  | inl q => rfl
  | inr q => cases q <;> rfl

omit [DecidableEq K] in
@[simp] theorem evaluate_applyJoin (r : MoveApplyMachine.FinalResult) (D : LocalData) :
    evaluate (applyJoinPhase r) D = evaluateApplyJoin r D := rfl

omit [DecidableEq K] in
@[simp] theorem evaluate_compare (D : LocalData) : evaluate comparePhase D = evaluateEquality D := rfl

omit [DecidableEq K] in
@[simp] theorem evaluate_equalityJoin (r : TreeEqualityMachine.Result) (D : LocalData) :
    evaluate (equalityJoinPhase r) D = ⟨equalityResult r, D, 1⟩ := rfl

omit [DecidableEq K] in
theorem evaluateInspect_nil (D : LocalData) (empty : D.certificate = []) :
    evaluateInspect D = addSteps 2 (evaluateEquality D) := by
  rw [evaluateInspect, ite_eq_left empty]

omit [DecidableEq K] in
theorem evaluateInspect_nonempty (D : LocalData) (nonempty : D.certificate ≠ []) :
    evaluateInspect D = addSteps 1 (evaluateCounter .borrow D) := by
  rw [evaluateInspect, ite_eq_right nonempty]
  cases fuel : (counterFinish .borrow D).result with
  | zero =>
      simp only [evaluateCounter, fuel, FuelDispatchMachine.exitOfResult, evaluateFuelJoin, addSteps]
      congr 1
      omega
  | positive =>
      simp only [evaluateCounter, fuel, FuelDispatchMachine.exitOfResult, evaluateFuelJoin, evaluateApply]
      cases applied : (applyFinish (MoveApplyMachine.movePhase .start) (counterFinish .borrow D).data).result with
      | inl u =>
          simp only [evaluateApplyJoin, addSteps]
          congr 1
          omega
      | inr r => cases r <;> simp only [evaluateApplyJoin, addSteps] <;> congr 1 <;> omega



end Resources.RotationCertificate.StreamMachine
