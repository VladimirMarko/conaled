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


/-! ## Canonical actual owned runs, before the global rank law -/

theorem equality_complete_localRun (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (evaluateEquality D).steps
      (cfg (some (phaseLabel comparePhase)) regs D ctx)
      (evaluationCfg regs (evaluateEquality D) ctx) := by
  have first := equality_phase_localRun caller D regs ctx
  have last := equality_join_localRun caller (equalityFinish D).result (equalityFinish D).data
    (resetEquality regs) ctx
  simpa only [evaluateEquality, evaluationCfg, equalityJoinTarget, resetAll_resetEquality] using
    LocalRun.trans caller first last

theorem fuel_atEnd_complete_localRun (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (evaluateFuelJoin .atEnd D).steps
      (cfg (some (phaseLabel (fuelJoinPhase .atEnd))) regs D ctx)
      (evaluationCfg regs (evaluateFuelJoin .atEnd D) ctx) := by
  have first := fuel_join_localRun caller .atEnd D regs ctx
  have last := equality_complete_localRun caller D (resetAll regs) ctx
  simpa only [evaluateFuelJoin, addSteps, evaluationCfg, resetAll_resetAll] using
    LocalRun.trans caller first last

/-- The continuation premise is required only for an actual successful endpoint.
It retains the complete dirty output rather than assuming cleanup or consumption. -/
theorem apply_complete_localRun_of_success (q : MoveApplyMachine.Phase) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (continued : (applyFinish q D).result = MoveApplyMachine.success →
      LocalRun caller (evaluateInspect (applyFinish q D).data).steps
        (cfg (some (phaseLabel inspectPhase)) (resetAll regs) (applyFinish q D).data ctx)
        (evaluationCfg regs (evaluateInspect (applyFinish q D).data) ctx)) :
    LocalRun caller (evaluateApply q D).steps
      (cfg (some (phaseLabel (applyPhase q))) regs D ctx)
      (evaluationCfg regs (evaluateApply q D) ctx) := by
  have first := apply_phase_localRun caller q D regs ctx
  cases returned : (applyFinish q D).result with
  | inl u =>
      rw [returned] at first
      have last := apply_join_localRun caller (.inl u) (applyFinish q D).data (resetApply regs) ctx
      simpa only [evaluateApply, returned, evaluateApplyJoin, addSteps, evaluationCfg,
        applyJoinTarget, resetAll_resetApply] using LocalRun.trans caller first last
  | inr r => cases r with
    | failure =>
        rw [returned] at first
        have last := apply_join_localRun caller (.inr .failure) (applyFinish q D).data (resetApply regs) ctx
        simpa only [evaluateApply, returned, evaluateApplyJoin, addSteps, evaluationCfg,
          applyJoinTarget, resetAll_resetApply] using LocalRun.trans caller first last
    | success =>
        rw [returned] at first
        have joined := apply_join_localRun caller MoveApplyMachine.success (applyFinish q D).data (resetApply regs) ctx
        simp only [applyJoinTarget, MoveApplyMachine.success, resetAll_resetApply] at joined
        have last := continued returned
        have complete := LocalRun.trans caller (LocalRun.trans caller first joined) last
        simpa only [evaluateApply, returned, evaluateApplyJoin, addSteps,
          evaluationCfg, Nat.add_assoc] using complete

/-- Well-founded actual execution through the first live Boolean result. The
recursive hypothesis is invoked only on the exact shorter full-MoveApplyMachine.start suffix. -/
theorem inspect_localRun (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (evaluateInspect D).steps
      (cfg (some (phaseLabel inspectPhase)) regs D ctx)
      (evaluationCfg regs (evaluateInspect D) ctx) := by
  revert regs
  refine (measure (fun D : LocalData => D.certificate.length)).wf.induction
    (C := fun D : LocalData => ∀ regs : Registers R,
      LocalRun caller (evaluateInspect D).steps
        (cfg (some (phaseLabel inspectPhase)) regs D ctx)
        (evaluationCfg regs (evaluateInspect D) ctx)) D ?_
  intro D ih regs
  by_cases empty : D.certificate = []
  · rw [evaluateInspect_nil D empty]
    have first := phase_step_localRun caller (inspect_step_nil caller D empty regs ctx)
    have last := fuel_atEnd_complete_localRun caller D (resetFuel regs) ctx
    have complete := LocalRun.trans caller first last
    have clock : 1 + (evaluateFuelJoin .atEnd D).steps = (addSteps 2 (evaluateEquality D)).steps := by
      simp only [evaluateFuelJoin, addSteps]
      omega
    rw [clock] at complete
    simpa only [evaluateFuelJoin, evaluationCfg, resetAll_resetFuel, addSteps] using complete
  · rw [evaluateInspect_nonempty D empty]
    have stage := inspect_stage_localRun caller D regs ctx
    have certificate : ∃ tag raw, D.certificate = tag :: raw := List.exists_cons_of_ne_nil empty
    obtain ⟨tag, raw, certificate⟩ := certificate
    simp only [inspectStageFinish, certificate] at stage
    cases fuel : (counterFinish .borrow D).result with
    | zero =>
        simp only [fuel, FuelDispatchMachine.exitOfResult] at stage
        have last := fuel_join_localRun caller .zero (counterFinish .borrow D).data (resetFuel regs) ctx
        simpa only [evaluateCounter, fuel, FuelDispatchMachine.exitOfResult, evaluateFuelJoin, addSteps,
          evaluationCfg, fuelJoinTarget, resetAll_resetFuel, Nat.add_assoc] using
          LocalRun.trans caller stage last
    | positive =>
        simp only [fuel, FuelDispatchMachine.exitOfResult] at stage
        have joined := fuel_join_localRun caller .positive (counterFinish .borrow D).data (resetFuel regs) ctx
        simp only [fuelJoinTarget, resetAll_resetFuel] at joined
        have applied := apply_complete_localRun_of_success caller (MoveApplyMachine.movePhase .start)
          (counterFinish .borrow D).data (resetAll regs) ctx (by
            intro returned
            have decrease := apply_start_certificate_lt (counterFinish .borrow D).data returned
            have lower :
                (applyFinish (MoveApplyMachine.movePhase .start) (counterFinish .borrow D).data).data.certificate.length <
                  D.certificate.length := by simpa only [counterFinish_certificate] using decrease
            simpa only [evaluationCfg, resetAll_resetAll] using
              ih (applyFinish (MoveApplyMachine.movePhase .start) (counterFinish .borrow D).data).data lower (resetAll regs))
        have complete := LocalRun.trans caller (LocalRun.trans caller stage joined) applied
        simpa only [evaluateCounter, fuel, FuelDispatchMachine.exitOfResult, evaluateFuelJoin, addSteps,
          evaluationCfg, resetAll_resetAll, Nat.add_assoc] using complete

theorem apply_complete_localRun (q : MoveApplyMachine.Phase) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (evaluateApply q D).steps
      (cfg (some (phaseLabel (applyPhase q))) regs D ctx)
      (evaluationCfg regs (evaluateApply q D) ctx) := by
  apply apply_complete_localRun_of_success caller q D regs ctx
  intro _
  simpa only [evaluationCfg, resetAll_resetAll] using inspect_localRun caller (applyFinish q D).data (resetAll regs) ctx

theorem apply_join_complete_localRun (r : MoveApplyMachine.FinalResult) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (evaluateApplyJoin r D).steps
      (cfg (some (phaseLabel (applyJoinPhase r))) regs D ctx)
      (evaluationCfg regs (evaluateApplyJoin r D) ctx) := by
  cases r with
  | inl u => exact apply_join_localRun caller (.inl u) D regs ctx
  | inr r => cases r with
    | failure => exact apply_join_localRun caller (.inr .failure) D regs ctx
    | success =>
        have first := apply_join_localRun caller MoveApplyMachine.success D regs ctx
        have last := inspect_localRun caller D (resetAll regs) ctx
        simpa only [MoveApplyMachine.success, evaluateApplyJoin, addSteps, evaluationCfg,
          resetAll_resetAll] using LocalRun.trans caller first last

theorem fuel_join_complete_localRun (r : FuelDispatchMachine.Exit) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (evaluateFuelJoin r D).steps
      (cfg (some (phaseLabel (fuelJoinPhase r))) regs D ctx)
      (evaluationCfg regs (evaluateFuelJoin r D) ctx) := by
  cases r with
  | atEnd => exact fuel_atEnd_complete_localRun caller D regs ctx
  | zero => exact fuel_join_localRun caller .zero D regs ctx
  | positive =>
      have first := fuel_join_localRun caller .positive D regs ctx
      have last := apply_complete_localRun caller (MoveApplyMachine.movePhase .start) D (resetAll regs) ctx
      simpa only [evaluateFuelJoin, addSteps, evaluationCfg, resetAll_resetAll] using
        LocalRun.trans caller first last

theorem counter_complete_localRun (q : Resources.BinaryCounter.FixedWidthMachine.Phase) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (evaluateCounter q D).steps
      (cfg (some (phaseLabel (counterPhase q))) regs D ctx)
      (evaluationCfg regs (evaluateCounter q D) ctx) := by
  have first := counter_phase_localRun caller q D regs ctx
  have last := fuel_join_complete_localRun caller (FuelDispatchMachine.exitOfResult (counterFinish q D).result)
    (counterFinish q D).data (resetFuel regs) ctx
  simpa only [evaluateCounter, addSteps, evaluationCfg, resetAll_resetFuel] using
    LocalRun.trans caller first last

/-- Canonical complete execution for every one of the 39 owned phases. -/
theorem phase_localRun (q : Phase) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (phaseSteps q D)
      (cfg (some (phaseLabel q)) regs D ctx) (phaseResult q regs D ctx) := by
  rcases q with fuel | (applied | equality)
  · rcases fuel with q | (r | (d | impossible))
    · exact counter_complete_localRun caller q D regs ctx
    · cases r with
      | positive => exact fuel_join_complete_localRun caller .positive D regs ctx
      | zero => exact fuel_join_complete_localRun caller .zero D regs ctx
    · cases d with
      | inspectCertificate => exact inspect_localRun caller D regs ctx
      | atEnd => exact fuel_join_complete_localRun caller .atEnd D regs ctx
    · exact Empty.elim impossible
  · rcases applied with q | (r | (q | (r | impossible)))
    · exact apply_complete_localRun caller (MoveApplyMachine.movePhase q) D regs ctx
    · exact apply_complete_localRun caller (MoveApplyMachine.dispatchPhase r) D regs ctx
    · exact apply_complete_localRun caller (MoveApplyMachine.positionPhase q) D regs ctx
    · exact apply_join_complete_localRun caller r D regs ctx
    · exact Empty.elim impossible
  · rcases equality with q | (r | impossible)
    · cases q; exact equality_complete_localRun caller D regs ctx
    · exact equality_join_localRun caller r D regs ctx
    · exact Empty.elim impossible

theorem phase_iterate (q : Phase) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    (next caller)^[phaseSteps q D] (some (cfg (some (phaseLabel q)) regs D ctx)) =
      some (phaseResult q regs D ctx) := (phase_localRun caller q D regs ctx).iterate caller

omit [DecidableEq K] in
theorem phaseResult_not_owned (q : Phase) (regs : Registers R) (D : LocalData)
    (ctx : ∀ k, List (Γ k)) : ¬ Owned (phaseResult (Λ := Λ) q regs D ctx).l :=
  not_owned_result (evaluate q D).result

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


omit [DecidableEq K] in
theorem phaseSteps_pos (q : Phase) (D : LocalData) : 0 < phaseSteps q D := by
  let localCaller : External Empty → Statement (fun _ : Empty => Empty) Empty Unit := fun _ => .halt
  let regs : Registers Unit := (none, ((none, (none, none)), ()))
  have executed := phase_iterate localCaller q D regs (fun k : Empty => Empty.elim k)
  have nonowned := phaseResult_not_owned (Γ := fun _ : Empty => Empty) (Λ := Empty)
    q regs D (fun k => Empty.elim k)
  by_contra failure
  have zero : phaseSteps q D = 0 := by omega
  rw [zero] at executed
  have same : cfg (some (phaseLabel q)) regs D (fun k : Empty => Empty.elim k) =
      phaseResult (Γ := fun _ : Empty => Empty) (Λ := Empty) q regs D (fun k => Empty.elim k) :=
    Option.some.inj executed
  apply nonowned
  rw [← same]
  exact owned_phase q

omit [DecidableEq K] in
def remainingSteps (c : Cfg Γ Λ R) : Nat :=
  match c.l with
  | some (.inl q) => phaseSteps (.inl q) (dataOfCfg c)
  | some (.inr (.inl q)) => phaseSteps (.inr (.inl q)) (dataOfCfg c)
  | some (.inr (.inr (.inl q))) => phaseSteps (.inr (.inr q)) (dataOfCfg c)
  | _ => 0

omit [DecidableEq K] in
def finalCfg (c : Cfg Γ Λ R) : Cfg Γ Λ R :=
  match c.l with
  | some (.inl q) => phaseResult (.inl q) c.var (dataOfCfg c) (contextOfCfg c)
  | some (.inr (.inl q)) => phaseResult (.inr (.inl q)) c.var (dataOfCfg c) (contextOfCfg c)
  | some (.inr (.inr (.inl q))) => phaseResult (.inr (.inr q)) c.var (dataOfCfg c) (contextOfCfg c)
  | _ => c

omit [DecidableEq K] in
def stateRemainingSteps : Option (Cfg Γ Λ R) → Nat
  | none => 0
  | some c => remainingSteps c

omit [DecidableEq K] in
@[simp] theorem stateRemainingSteps_none : stateRemainingSteps (Γ := Γ) (Λ := Λ) (R := R) none = 0 := rfl

omit [DecidableEq K] in
@[simp] theorem stateRemainingSteps_some (c : Cfg Γ Λ R) :
    stateRemainingSteps (some c) = remainingSteps c := rfl

omit [DecidableEq K] in
theorem remainingSteps_phase_cfg (q : Phase) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    remainingSteps (cfg (some (phaseLabel (Λ := Λ) q)) regs D ctx) = phaseSteps q D := by
  cases q with
  | inl q => rfl
  | inr q => cases q <;> rfl

omit [DecidableEq K] in
theorem finalCfg_phase_cfg (q : Phase) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    finalCfg (cfg (some (phaseLabel (Λ := Λ) q)) regs D ctx) = phaseResult q regs D ctx := by
  cases q with
  | inl q => rfl
  | inr q => cases q <;> rfl

omit [DecidableEq K] in
theorem remainingSteps_pos_iff (c : Cfg Γ Λ R) : 0 < remainingSteps c ↔ Owned c.l := by
  cases labelEq : c.l with
  | none => simp only [remainingSteps, Owned, labelEq, Nat.lt_irrefl]
  | some label =>
      rcases label with f | (h | (e | external))
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
      rcases label with f | (h | (e | external))
      · refine ⟨.inl f, c.var, dataOfCfg c, contextOfCfg c, ?_⟩
        simpa only [labelEq, phaseLabel] using (cfg_eta c).symm
      · refine ⟨.inr (.inl h), c.var, dataOfCfg c, contextOfCfg c, ?_⟩
        simpa only [labelEq, phaseLabel] using (cfg_eta c).symm
      · refine ⟨.inr (.inr e), c.var, dataOfCfg c, contextOfCfg c, ?_⟩
        simpa only [labelEq, phaseLabel] using (cfg_eta c).symm
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
    {ctx outCtx : ∀ k, List (Γ k)} {n : Nat} {r : Bool}
    (run : LocalRun caller n (cfg (some (phaseLabel q)) regs D ctx)
      (cfg (some (resultLabel r)) outRegs E outCtx)) :
    phaseSteps q D = n ∧
      phaseResult (Λ := Λ) q regs D ctx = cfg (some (resultLabel r)) outRegs E outCtx := by
  exact LocalRun.first_unique caller (phase_localRun caller q D regs ctx) run
    (phaseResult_not_owned q regs D ctx) (not_owned_result r)

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
theorem program_phase_independent (other : External Λ → Statement Γ Λ R) (q : Phase) :
    program caller (phaseLabel q) = program other (phaseLabel q) := by
  rcases q with fuel | (applied | equality)
  · rcases fuel with q | (r | (d | impossible))
    · rfl
    · rfl
    · cases d <;> rfl
    · exact Empty.elim impossible
  · rcases applied with q | (r | (q | (r | impossible)))
    · rfl
    · rfl
    · rfl
    · rfl
    · exact Empty.elim impossible
  · rcases equality with q | (r | impossible)
    · cases q; rfl
    · rfl
    · exact Empty.elim impossible

theorem step_caller_independent (other : External Λ → Statement Γ Λ R)
    (c : Cfg Γ Λ R) (owned : Owned c.l) : step caller c = step other c := by
  obtain ⟨q, regs, D, ctx, rfl⟩ := owned_cases c owned
  change some (Turing.TM2.stepAux (program caller (phaseLabel q)) regs
      (cfg (Λ := Λ) (some (phaseLabel q)) regs D ctx).stk) =
    some (Turing.TM2.stepAux (program other (phaseLabel q)) regs
      (cfg (Λ := Λ) (some (phaseLabel q)) regs D ctx).stk)
  rw [program_phase_independent caller other q]

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


def FirstRun (start : Cfg Γ Λ R) (n : Nat) (finish : Cfg Γ Λ R) : Prop :=
  (next caller)^[n] (some start) = some finish ∧ ¬ Owned finish.l ∧
    ∀ j, j < n → ∃ reached,
      (next caller)^[j] (some start) = some reached ∧ Owned reached.l

def FirstResult (start : Cfg Γ Λ R) (b : Bool) : Prop :=
  ∃ n finish, FirstRun caller start n finish ∧ finish.l = some (resultLabel b)

theorem cfg_firstRun (start : Cfg Γ Λ R) :
    FirstRun caller start (remainingSteps start) (finalCfg start) :=
  ⟨cfg_iterate caller start, finalCfg_not_owned start,
    (cfg_localRun caller start).owned_prefix caller⟩

theorem firstRun_iff (start finish : Cfg Γ Λ R) (n : Nat) :
    FirstRun caller start n finish ↔ n = remainingSteps start ∧ finish = finalCfg start := by
  constructor
  · rintro ⟨executed, nonowned, earlier⟩
    exact LocalRun.first_unique caller (LocalRun.of_iterate caller executed earlier)
      (cfg_localRun caller start) nonowned (finalCfg_not_owned start)
  · rintro ⟨rfl, rfl⟩
    exact cfg_firstRun caller start

theorem firstResult_iff_finalCfg (start : Cfg Γ Λ R) (b : Bool) :
    FirstResult caller start b ↔ (finalCfg start).l = some (resultLabel b) := by
  constructor
  · rintro ⟨n, finish, first, label⟩
    rcases (firstRun_iff caller start finish n).mp first with ⟨_, rfl⟩
    exact label
  · intro label
    exact ⟨remainingSteps start, finalCfg start, cfg_firstRun caller start, label⟩

theorem phase_firstResult_iff (q : Phase) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (b : Bool) :
    FirstResult caller (cfg (some (phaseLabel q)) regs D ctx) b ↔ (evaluate q D).result = b := by
  rw [firstResult_iff_finalCfg, finalCfg_phase_cfg]
  change some (resultLabel (evaluate q D).result) = some (resultLabel b) ↔ _
  simp only [resultLabel, Option.some.injEq, Sum.inr.injEq, Sum.inl.injEq]

theorem nonowned_firstResult_iff (start : Cfg Γ Λ R) (nonowned : ¬ Owned start.l) (b : Bool) :
    FirstResult caller start b ↔ start.l = some (resultLabel b) := by
  rw [firstResult_iff_finalCfg, nonowned_finalCfg start nonowned]

theorem phase_firstRun (q : Phase) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    FirstRun caller (cfg (some (phaseLabel q)) regs D ctx) (phaseSteps q D) (phaseResult q regs D ctx) :=
  phase_first_return caller q D regs ctx


/-! ## Complete-data one-step bridges for independent connected clients -/

omit [DecidableEq K] in
theorem fuelCfg_partial (label : Option (FuelDispatchMachine.Label (FuelCallerLabel Λ)))
    (regs : Registers R) (D : LocalData) (fuel : Bits) (units : List Unit) (certificate : Word)
    (ctx : ∀ k, List (Γ k)) :
    fuelCfg (FuelDispatchMachine.cfg label regs fuel units certificate (fuelContext D ctx)) =
      cfg (label.map fuelLabelEquiv) regs
        { D with certificate := certificate, units := units, fuel := fuel } ctx := by
  change fuelCfg (fuelView label regs
    { D with certificate := certificate, units := units, fuel := fuel } ctx) = _
  exact fuelCfg_view label regs _ ctx

omit [DecidableEq K] in
theorem applyCfg_partial (label : Option (MoveApplyMachine.Label (ApplyCallerLabel Λ)))
    (regs : MoveApplyMachine.Registers (ApplyCallerRegister R)) (D : LocalData) (output : MoveApplyMachine.LocalData)
    (ctx : ∀ k, List (Γ k)) :
    applyCfg (MoveApplyMachine.cfg label regs output (applyContext D ctx)) =
      cfg (label.map applyLabelEquiv) (applyRegisterEquiv regs) (setApplyData D output) ctx := by
  change applyCfg (applyView label regs (setApplyData D output) ctx) = _
  exact applyCfg_view label regs _ ctx

omit [DecidableEq K] in
theorem equalityCfg_partial (label : Option (TreeEqualityMachine.Label (EqualityCallerLabel Λ)))
    (regs : TreeEqualityMachine.Registers (EqualityCallerRegister R)) (D : LocalData) (source target : Word)
    (ctx : ∀ k, List (Γ k)) :
    equalityCfg (TreeEqualityMachine.cfg label regs source target (equalityContext D ctx)) =
      cfg (label.map equalityLabelEquiv) (equalityRegisterEquiv regs)
        { D with source := source, target := target } ctx := by
  change equalityCfg (equalityView label regs { D with source := source, target := target } ctx) = _
  exact equalityCfg_view label regs _ ctx

theorem counter_step_of_step
    (localCaller : (FuelDispatchMachine.Exit ⊕ FuelCallerLabel Λ) → FuelStatement Γ Λ R)
    (q : Resources.BinaryCounter.FixedWidthMachine.Phase) (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (label : Option (FuelDispatchMachine.Label (FuelCallerLabel Λ))) (outRegs : Registers R)
    (fuel : Bits) (units : List Unit)
    (executed : FuelDispatchMachine.step localCaller (fuelView (some (Resources.BinaryCounter.FixedWidthMachine.phaseLabel q)) regs D ctx) =
      some (FuelDispatchMachine.cfg label outRegs fuel units D.certificate (fuelContext D ctx))) :
    step caller (cfg (some (phaseLabel (counterPhase q))) regs D ctx) =
      some (cfg (label.map fuelLabelEquiv) outRegs { D with fuel := fuel, units := units } ctx) := by
  have actual := fuel_step_transport caller localCaller
    (fuelView (some (Resources.BinaryCounter.FixedWidthMachine.phaseLabel q)) regs D ctx) (Or.inl True.intro)
  rw [fuelCfg_view, executed] at actual
  simp only [Option.map_some] at actual
  rw [fuelCfg_partial] at actual
  simpa only [Option.map_some, fuelLabelEquiv_counter, fuelRegisterEquiv, Equiv.refl_apply] using actual

theorem apply_step_of_step
    (localCaller : MoveApplyMachine.External (ApplyCallerLabel Λ) → ApplyStatement Γ Λ R)
    (q : MoveApplyMachine.Phase) (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (label : Option (MoveApplyMachine.Label (ApplyCallerLabel Λ)))
    (outRegs : MoveApplyMachine.Registers (ApplyCallerRegister R)) (output : MoveApplyMachine.LocalData)
    (executed : MoveApplyMachine.step localCaller
      (applyView (some (MoveApplyMachine.phaseLabel q)) (applyRegisterEquiv.symm regs) D ctx) =
      some (MoveApplyMachine.cfg label outRegs output (applyContext D ctx))) :
    step caller (cfg (some (phaseLabel (applyPhase q))) regs D ctx) =
      some (cfg (label.map applyLabelEquiv) (applyRegisterEquiv outRegs) (setApplyData D output) ctx) := by
  have actual := apply_step_transport caller localCaller
    (applyView (some (MoveApplyMachine.phaseLabel q)) (applyRegisterEquiv.symm regs) D ctx) (MoveApplyMachine.owned_phase q)
  rw [applyCfg_view, executed] at actual
  simp only [Option.map_some] at actual
  rw [applyCfg_partial] at actual
  simpa only [Option.map_some, applyLabelEquiv_phase, Equiv.apply_symm_apply] using actual

theorem equality_step_of_step
    (localCaller : TreeEqualityMachine.External (EqualityCallerLabel Λ) → EqualityStatement Γ Λ R)
    (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (label : Option (TreeEqualityMachine.Label (EqualityCallerLabel Λ)))
    (outRegs : TreeEqualityMachine.Registers (EqualityCallerRegister R)) (source target : Word)
    (executed : TreeEqualityMachine.step localCaller
      (equalityView (some (TreeEqualityMachine.phaseLabel .compare)) (equalityRegisterEquiv.symm regs) D ctx) =
      some (TreeEqualityMachine.cfg label outRegs source target (equalityContext D ctx))) :
    step caller (cfg (some (phaseLabel comparePhase)) regs D ctx) =
      some (cfg (label.map equalityLabelEquiv) (equalityRegisterEquiv outRegs)
        { D with source := source, target := target } ctx) := by
  have actual := equality_step_transport caller localCaller
    (equalityView (some (TreeEqualityMachine.phaseLabel .compare)) (equalityRegisterEquiv.symm regs) D ctx) True.intro
  rw [equalityCfg_view, executed] at actual
  simp only [Option.map_some] at actual
  rw [equalityCfg_partial] at actual
  simpa only [Option.map_some, equalityLabelEquiv_phase, Equiv.apply_symm_apply] using actual

theorem apply_position_advance_step (q : PositionedRotationMachine.Phase)
    (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel (applyPhase (MoveApplyMachine.positionPhase q)))) regs D ctx) =
      some (cfg
        (some (applyLabelEquiv (MoveApplyMachine.positionControlLabel
          (PositionedRotationMachine.advance q (MoveApplyMachine.positionData (applyData D))).1)))
        (resetApply regs)
        (setApplyData D (MoveApplyMachine.setPositionData (applyData D)
          (PositionedRotationMachine.advance q (MoveApplyMachine.positionData (applyData D))).2)) ctx) := by
  let localCaller : MoveApplyMachine.External (ApplyCallerLabel Λ) → ApplyStatement Γ Λ R := fun _ => .halt
  have actual := apply_step_of_step caller localCaller (MoveApplyMachine.positionPhase q) D regs ctx _ _ _
    (MoveApplyMachine.position_advance_step localCaller q (applyData D) (applyRegisterEquiv.symm regs) (applyContext D ctx))
  simpa only [Option.map_some, applyRegisterEquiv_reset, Equiv.apply_symm_apply] using actual


omit [DecidableEq K] in
@[simp] theorem apply_move_register_reset
    (regs : MoveParserMachine.Registers (MoveApplyMachine.MoveCallerRegister (ApplyCallerRegister R))) :
    applyRegisterEquiv (MoveApplyMachine.moveRegisterEquiv (MoveParserMachine.reset regs)) =
      resetMove (applyRegisterEquiv (MoveApplyMachine.moveRegisterEquiv regs)) := rfl

/-- A literal parser activation through both complete physical transports. -/
theorem apply_move_step_of_step
    (localCaller : MoveParserMachine.External (MoveApplyMachine.MoveCallerLabel (ApplyCallerLabel Λ)) →
      MoveApplyMachine.MoveStatement (applyProtectedAlphabet Γ) (ApplyCallerLabel Λ) (ApplyCallerRegister R))
    (q : MoveParserMachine.Phase) (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (label : Option (MoveParserMachine.Label (MoveApplyMachine.MoveCallerLabel (ApplyCallerLabel Λ))))
    (outRegs : MoveParserMachine.Registers (MoveApplyMachine.MoveCallerRegister (ApplyCallerRegister R)))
    (raw : Word) (rev path : List Branch)
    (executed : MoveParserMachine.step localCaller
      (MoveApplyMachine.moveView (some (MoveParserMachine.phaseLabel q))
        (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm regs))
        (applyData D) (applyContext D ctx)) =
      some (MoveParserMachine.cfg label outRegs raw rev path
        (MoveApplyMachine.moveContext (applyData D) (applyContext D ctx)))) :
    step caller (cfg (some (phaseLabel (applyPhase (MoveApplyMachine.movePhase q)))) regs D ctx) =
      some (cfg ((label.map MoveApplyMachine.moveLabelEquiv).map applyLabelEquiv)
        (applyRegisterEquiv (MoveApplyMachine.moveRegisterEquiv outRegs))
        { D with certificate := raw, moveReverse := rev, path := path } ctx) := by
  let hCaller : MoveApplyMachine.External (ApplyCallerLabel Λ) → ApplyStatement Γ Λ R := fun _ => .halt
  let output : MoveApplyMachine.LocalData :=
    { applyData D with certificate := raw, moveReverse := rev, path := path }
  have inner := MoveApplyMachine.move_step_transport hCaller localCaller
    (MoveApplyMachine.moveView (some (MoveParserMachine.phaseLabel q))
      (MoveApplyMachine.moveRegisterEquiv.symm (applyRegisterEquiv.symm regs))
      (applyData D) (applyContext D ctx)) True.intro
  rw [MoveApplyMachine.moveCfg_view, executed] at inner
  simp only [Option.map_some] at inner
  have out : MoveApplyMachine.moveCfg
      (MoveParserMachine.cfg label outRegs raw rev path
        (MoveApplyMachine.moveContext (applyData D) (applyContext D ctx))) =
      MoveApplyMachine.cfg (label.map MoveApplyMachine.moveLabelEquiv)
        (MoveApplyMachine.moveRegisterEquiv outRegs) output (applyContext D ctx) := by
    change MoveApplyMachine.moveCfg (MoveApplyMachine.moveView label outRegs output (applyContext D ctx)) = _
    exact MoveApplyMachine.moveCfg_view label outRegs output (applyContext D ctx)
  rw [out] at inner
  have localStep : MoveApplyMachine.step hCaller
      (applyView (some (MoveApplyMachine.phaseLabel (MoveApplyMachine.movePhase q)))
        (applyRegisterEquiv.symm regs) D ctx) =
      some (MoveApplyMachine.cfg (label.map MoveApplyMachine.moveLabelEquiv)
        (MoveApplyMachine.moveRegisterEquiv outRegs) output (applyContext D ctx)) := by
    simpa only [MoveApplyMachine.moveLabelEquiv_phase, Equiv.apply_symm_apply, applyView,
      MoveApplyMachine.phaseLabel, MoveApplyMachine.movePhase, MoveApplyMachine.moveLabel] using inner
  have actual := apply_step_of_step caller hCaller (MoveApplyMachine.movePhase q) D regs ctx _ _ output localStep
  exact actual


/-! ## Arbitrary caller frame and the invariant after a paid full reset -/

omit [DecidableEq K] in
def FrameResult (before after : Cfg Γ Λ R) : Prop :=
  after.var.2.2 = before.var.2.2 ∧
    (∀ k, after.stk (.inr k) = before.stk (.inr k)) ∧
    (resetAll before.var = before.var → after.var = before.var)

omit [DecidableEq K] in
theorem fuelCfg_context (c : FuelCfg Γ Λ R) (k : K) :
    (fuelCfg c).stk (.inr k) = c.stk (.inr (.inr (.inr k))) := by
  change FrontEndMachine.Transport.stackEquiv fuelStackEquiv (fuelSymbolEquiv (Γ := Γ))
    c.stk (fuelStackEquiv (.inr (.inr (.inr k)))) = _
  rw [FrontEndMachine.Transport.stackEquiv_apply]
  change List.map id _ = _
  exact List.map_id _

omit [DecidableEq K] in
theorem applyCfg_context (c : ApplyCfg Γ Λ R) (k : K) :
    (applyCfg c).stk (.inr k) = c.stk (.inr (.inr k)) := by
  change FrontEndMachine.Transport.stackEquiv applyStackEquiv (applySymbolEquiv (Γ := Γ))
    c.stk (applyStackEquiv (.inr (.inr k))) = _
  rw [FrontEndMachine.Transport.stackEquiv_apply]
  change List.map id _ = _
  exact List.map_id _

omit [DecidableEq K] in
theorem equalityCfg_context (c : EqualityCfg Γ Λ R) (k : K) :
    (equalityCfg c).stk (.inr k) = c.stk (.inr (.inr k)) := by
  change FrontEndMachine.Transport.stackEquiv equalityStackEquiv (equalitySymbolEquiv (Γ := Γ))
    c.stk (equalityStackEquiv (.inr (.inr k))) = _
  rw [FrontEndMachine.Transport.stackEquiv_apply]
  change List.map id _ = _
  exact List.map_id _

/-- Fuel's register/frame law without imposing finiteness on the protected family. -/
theorem fuel_local_step_data
    (localCaller : (FuelDispatchMachine.Exit ⊕ FuelCallerLabel Λ) → FuelStatement Γ Λ R)
    {before after : FuelCfg Γ Λ R} (transition : FuelDispatchMachine.LocalStep localCaller before after) :
    after.var = Resources.BinaryCounter.FixedWidthMachine.reset before.var ∧
      ∀ k, after.stk (.inr k) = before.stk (.inr k) := by
  rcases transition with ⟨owned, executed⟩
  rcases owned with core | inspect
  · obtain ⟨_, bit, registers, _, frame⟩ :=
      Resources.BinaryCounter.FixedWidthMachine.local_step_data (FuelDispatchMachine.callerHandler localCaller) ⟨core, executed⟩
    refine ⟨?_, frame⟩
    apply Prod.ext
    · exact bit
    · exact registers
  · obtain ⟨regs, fuel, units, cert, ctx, rfl⟩ := FuelDispatchMachine.inspection_cases before inspect
    cases cert with
    | nil =>
        rw [FuelDispatchMachine.dispatch_step_nil] at executed
        cases Option.some.inj executed
        exact ⟨rfl, fun _ => rfl⟩
    | cons tag raw =>
        rw [FuelDispatchMachine.dispatch_step_cons] at executed
        cases Option.some.inj executed
        exact ⟨rfl, fun _ => rfl⟩

omit [DecidableEq K] in
theorem apply_registersAt_clean (c : ApplyCfg Γ Λ R) (n : Nat)
    (clean : MoveApplyMachine.reset c.var = c.var) : MoveApplyMachine.registersAt c n = c.var := by
  have parserClean : MoveApplyMachine.resetMove c.var = c.var := by rw [← clean]; rfl
  unfold MoveApplyMachine.registersAt
  split
  · rfl
  · split
    · simp only [clean, parserClean, ite_self]
    · exact clean

theorem fuel_step_frame
    (localCaller : (FuelDispatchMachine.Exit ⊕ FuelCallerLabel Λ) → FuelStatement Γ Λ R)
    (c : FuelCfg Γ Λ R) (owned : FuelDispatchMachine.Owned c.l) (after : Cfg Γ Λ R)
    (executed : step caller (fuelCfg c) = some after) : FrameResult (fuelCfg c) after := by
  obtain ⟨middle, moved, _⟩ := FuelDispatchMachine.local_progress localCaller c ((FuelDispatchMachine.remainingSteps_pos_iff c).mpr owned)
  have actual := fuel_step_transport caller localCaller c owned
  rw [moved, Option.map_some] at actual
  have same : after = fuelCfg middle := Option.some.inj (executed.symm.trans actual)
  subst after
  obtain ⟨registers, frame⟩ := fuel_local_step_data localCaller ⟨owned, moved⟩
  refine ⟨?_, ?_, ?_⟩
  · change middle.var.2.2 = c.var.2.2
    rw [registers]
    rfl
  · intro k
    rw [fuelCfg_context, fuelCfg_context]
    exact frame (.inr (.inr k))
  · intro clean
    change resetAll c.var = c.var at clean
    change middle.var = c.var
    rw [registers]
    change resetFuel c.var = c.var
    rw [← clean]
    rfl

theorem apply_step_frame
    (localCaller : MoveApplyMachine.External (ApplyCallerLabel Λ) → ApplyStatement Γ Λ R)
    (c : ApplyCfg Γ Λ R) (owned : MoveApplyMachine.Owned c.l) (after : Cfg Γ Λ R)
    (executed : step caller (applyCfg c) = some after) : FrameResult (applyCfg c) after := by
  have positive := (MoveApplyMachine.remainingSteps_pos_iff c).mpr owned
  obtain ⟨middle, moved, _⟩ := MoveApplyMachine.local_progress localCaller c positive
  have actual := apply_step_transport caller localCaller c owned
  rw [moved, Option.map_some] at actual
  have same : after = applyCfg middle := Option.some.inj (executed.symm.trans actual)
  subst after
  obtain ⟨registers, frame⟩ := MoveApplyMachine.local_step_frame localCaller ⟨owned, moved⟩
  refine ⟨?_, ?_, ?_⟩
  · change middle.var.2.2 = c.var.2.2
    exact congrArg Prod.snd registers
  · intro k
    rw [applyCfg_context, applyCfg_context]
    exact frame (.inr k)
  · intro clean
    change resetAll (applyRegisterEquiv c.var) = applyRegisterEquiv c.var at clean
    have localClean : MoveApplyMachine.reset c.var = c.var := by
      apply applyRegisterEquiv.injective
      rw [applyRegisterEquiv_reset, ← clean]
      rfl
    have reset := MoveApplyMachine.prefix_reset localCaller c middle 1 (by omega) moved
    rw [apply_registersAt_clean c 1 localClean] at reset
    change applyRegisterEquiv middle.var = applyRegisterEquiv c.var
    rw [reset]

theorem equality_step_frame
    (localCaller : TreeEqualityMachine.External (EqualityCallerLabel Λ) → EqualityStatement Γ Λ R)
    (c : EqualityCfg Γ Λ R) (owned : TreeEqualityMachine.Owned c.l) (after : Cfg Γ Λ R)
    (executed : step caller (equalityCfg c) = some after) : FrameResult (equalityCfg c) after := by
  obtain ⟨middle, moved, _⟩ := TreeEqualityMachine.local_progress localCaller c ((TreeEqualityMachine.remainingSteps_pos_iff c).mpr owned)
  have actual := equality_step_transport caller localCaller c owned
  rw [moved, Option.map_some] at actual
  have same : after = equalityCfg middle := Option.some.inj (executed.symm.trans actual)
  subst after
  obtain ⟨_, registers, _, _, frame⟩ := TreeEqualityMachine.local_step_data localCaller ⟨owned, moved⟩
  refine ⟨?_, ?_, ?_⟩
  · change middle.var.2.2.2 = c.var.2.2.2
    rw [registers]
    rfl
  · intro k
    rw [equalityCfg_context, equalityCfg_context]
    exact frame (.inr k)
  · intro clean
    change resetAll (equalityRegisterEquiv c.var) = equalityRegisterEquiv c.var at clean
    change equalityRegisterEquiv middle.var = equalityRegisterEquiv c.var
    rw [registers, equalityRegisterEquiv_reset, ← clean]
    rfl

theorem counter_step_frame (q : Resources.BinaryCounter.FixedWidthMachine.Phase) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (after : Cfg Γ Λ R)
    (executed : step caller (cfg (some (phaseLabel (counterPhase q))) regs D ctx) = some after) :
    FrameResult (cfg (some (phaseLabel (counterPhase q))) regs D ctx) after := by
  let localCaller : (FuelDispatchMachine.Exit ⊕ FuelCallerLabel Λ) → FuelStatement Γ Λ R := fun _ => .halt
  have startEq : fuelCfg (Λ := Λ) (fuelView (some (Resources.BinaryCounter.FixedWidthMachine.phaseLabel q)) regs D ctx) =
      cfg (some (phaseLabel (counterPhase q))) regs D ctx := by
    rw [fuelCfg_view]
    rfl
  rw [← startEq] at executed ⊢
  exact fuel_step_frame caller localCaller
    (fuelView (some (Resources.BinaryCounter.FixedWidthMachine.phaseLabel q)) regs D ctx)
    (Or.inl True.intro) after executed

theorem inspect_step_frame (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (after : Cfg Γ Λ R)
    (executed : step caller (cfg (some (phaseLabel inspectPhase)) regs D ctx) = some after) :
    FrameResult (cfg (some (phaseLabel inspectPhase)) regs D ctx) after := by
  let localCaller : (FuelDispatchMachine.Exit ⊕ FuelCallerLabel Λ) → FuelStatement Γ Λ R := fun _ => .halt
  have startEq : fuelCfg (Λ := Λ) (fuelView (some FuelDispatchMachine.inspectLabel) regs D ctx) =
      cfg (some (phaseLabel inspectPhase)) regs D ctx := by
    rw [fuelCfg_view]
    rfl
  rw [← startEq] at executed ⊢
  exact fuel_step_frame caller localCaller _ (Or.inr rfl) after executed

theorem apply_phase_step_frame (q : MoveApplyMachine.Phase) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (after : Cfg Γ Λ R)
    (executed : step caller (cfg (some (phaseLabel (applyPhase q))) regs D ctx) = some after) :
    FrameResult (cfg (some (phaseLabel (applyPhase q))) regs D ctx) after := by
  let localCaller : MoveApplyMachine.External (ApplyCallerLabel Λ) → ApplyStatement Γ Λ R := fun _ => .halt
  have startEq : applyCfg (Λ := Λ) (applyView (some (MoveApplyMachine.phaseLabel q)) (applyRegisterEquiv.symm regs) D ctx) =
      cfg (some (phaseLabel (applyPhase q))) regs D ctx := by
    rw [applyCfg_view]
    simp only [Option.map_some, applyLabelEquiv_phase, Equiv.apply_symm_apply]
  rw [← startEq] at executed ⊢
  exact apply_step_frame caller localCaller _ (MoveApplyMachine.owned_phase q) after executed

theorem compare_step_frame (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (after : Cfg Γ Λ R)
    (executed : step caller (cfg (some (phaseLabel comparePhase)) regs D ctx) = some after) :
    FrameResult (cfg (some (phaseLabel comparePhase)) regs D ctx) after := by
  let localCaller : TreeEqualityMachine.External (EqualityCallerLabel Λ) → EqualityStatement Γ Λ R := fun _ => .halt
  have startEq : equalityCfg (Λ := Λ) (equalityView (some (TreeEqualityMachine.phaseLabel .compare)) (equalityRegisterEquiv.symm regs) D ctx) =
      cfg (some (phaseLabel comparePhase)) regs D ctx := by
    rw [equalityCfg_view]
    simp only [Option.map_some, equalityLabelEquiv_phase, Equiv.apply_symm_apply]
  rw [← startEq] at executed ⊢
  exact equality_step_frame caller localCaller
    (equalityView (some (TreeEqualityMachine.phaseLabel .compare)) (equalityRegisterEquiv.symm regs) D ctx)
    True.intro after executed

omit [DecidableEq K] in
theorem reset_cfg_frame (label target : Option (Label Λ)) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    FrameResult (cfg label regs D ctx) (cfg target (resetAll regs) D ctx) :=
  ⟨rfl, fun _ => rfl, fun clean => clean⟩

theorem local_step_frame_data {before after : Cfg Γ Λ R} (transition : LocalStep caller before after) :
    FrameResult before after := by
  obtain ⟨q, regs, D, ctx, rfl⟩ := owned_cases before transition.1
  rcases q with fuel | (applied | equality)
  · rcases fuel with q | (r | (d | impossible))
    · exact counter_step_frame caller q D regs ctx after transition.2
    · cases r with
      | positive =>
          have same := Option.some.inj (transition.2.symm.trans (fuel_join_step caller .positive D regs ctx))
          subst after
          exact reset_cfg_frame _ _ D regs ctx
      | zero =>
          have same := Option.some.inj (transition.2.symm.trans (fuel_join_step caller .zero D regs ctx))
          subst after
          exact reset_cfg_frame _ _ D regs ctx
    · cases d with
      | inspectCertificate => exact inspect_step_frame caller D regs ctx after transition.2
      | atEnd =>
          have same := Option.some.inj (transition.2.symm.trans (fuel_join_step caller .atEnd D regs ctx))
          subst after
          exact reset_cfg_frame _ _ D regs ctx
    · exact Empty.elim impossible
  · rcases applied with q | (r | (q | (r | impossible)))
    · exact apply_phase_step_frame caller (MoveApplyMachine.movePhase q) D regs ctx after transition.2
    · exact apply_phase_step_frame caller (MoveApplyMachine.dispatchPhase r) D regs ctx after transition.2
    · exact apply_phase_step_frame caller (MoveApplyMachine.positionPhase q) D regs ctx after transition.2
    · have same := Option.some.inj (transition.2.symm.trans (apply_join_step caller r D regs ctx))
      subst after
      exact reset_cfg_frame _ _ D regs ctx
    · exact Empty.elim impossible
  · rcases equality with q | (r | impossible)
    · cases q; exact compare_step_frame caller D regs ctx after transition.2
    · have same := Option.some.inj (transition.2.symm.trans (equality_join_step caller r D regs ctx))
      subst after
      exact reset_cfg_frame _ _ D regs ctx
    · exact Empty.elim impossible

theorem local_step_frame {before after : Cfg Γ Λ R} (transition : LocalStep caller before after) :
    after.var.2.2 = before.var.2.2 ∧ ∀ k, after.stk (.inr k) = before.stk (.inr k) :=
  ⟨(local_step_frame_data caller transition).1, (local_step_frame_data caller transition).2.1⟩

theorem local_reaches_frame {start reached : Cfg Γ Λ R}
    (path : Relation.ReflTransGen (LocalStep caller) start reached) :
    reached.var.2.2 = start.var.2.2 ∧ ∀ k, reached.stk (.inr k) = start.stk (.inr k) := by
  induction path with
  | refl => exact ⟨rfl, fun _ => rfl⟩
  | @tail before after _ transition ih =>
      obtain ⟨registers, frame⟩ := local_step_frame caller transition
      exact ⟨registers.trans ih.1, fun k => (frame k).trans (ih.2 k)⟩

theorem local_reaches_resetAll {start reached : Cfg Γ Λ R}
    (path : Relation.ReflTransGen (LocalStep caller) start reached)
    (clean : resetAll start.var = start.var) : reached.var = start.var := by
  induction path with
  | refl => rfl
  | @tail before after _ transition ih =>
      have beforeClean : resetAll before.var = before.var := by rwa [ih]
      exact ((local_step_frame_data caller transition).2.2 beforeClean).trans ih

theorem prefix_frame (start reached : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start)
    (executed : (next caller)^[n] (some start) = some reached) :
    reached.var.2.2 = start.var.2.2 ∧ ∀ k, reached.stk (.inr k) = start.stk (.inr k) := by
  obtain ⟨actual, run, _, path, _⟩ := owned_prefix caller start n bound
  have same : actual = reached := Option.some.inj (run.symm.trans executed)
  subst actual
  exact local_reaches_frame caller path

theorem prefix_resetAll (start reached : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start)
    (executed : (next caller)^[n] (some start) = some reached)
    (clean : resetAll start.var = start.var) : reached.var = start.var := by
  obtain ⟨actual, run, _, path, _⟩ := owned_prefix caller start n bound
  have same : actual = reached := Option.some.inj (run.symm.trans executed)
  subst actual
  exact local_reaches_resetAll caller path clean

/-! ### Exact reindexing and prefix-bound composition for actual owned segments -/

/-- Reindex the actual Option-valued iterate after a proved complete local
segment. The continuation may include arbitrary caller behavior; this equality
itself does not extend any owned-prefix guarantee. -/
theorem prefix_iterate_after_localRun {start middle : Cfg Γ Λ R} {ticks : Nat}
    (run : LocalRun caller ticks start middle) (n : Nat) :
    (next caller)^[ticks + n] (some start) = (next caller)^[n] (some middle) := by
  rw [Nat.add_comm ticks n, Function.iterate_add_apply, LocalRun.iterate caller run]

/-- Compose two inclusive prefix properties through the literal intermediate
configuration. Both endpoint copies are retained at the shared boundary. -/
theorem prefix_property_after_localRun {start middle : Cfg Γ Λ R} {ticks tail : Nat}
    (run : LocalRun caller ticks start middle) (property : Cfg Γ Λ R → Prop)
    (first : ∀ n, n ≤ ticks → ∀ reached,
      (next caller)^[n] (some start) = some reached → property reached)
    (second : ∀ n, n ≤ tail → ∀ reached,
      (next caller)^[n] (some middle) = some reached → property reached) :
    ∀ n, n ≤ ticks + tail → ∀ reached,
      (next caller)^[n] (some start) = some reached → property reached := by
  intro n bound reached executed
  by_cases early : n ≤ ticks
  · exact first n early reached executed
  · have count : n = ticks + (n - ticks) := by omega
    apply second (n - ticks) (by omega) reached
    rw [← prefix_iterate_after_localRun caller run (n - ticks)]
    simpa only [← count] using executed

/-- Every actual prefix through the global first return lies either in the
proved component segment or in its literal continuation. The bound is an
explicit maximum of the supplied allowances, never a maximum over a trace. -/
theorem prefix_bound_after_localRun {start middle : Cfg Γ Λ R} {ticks : Nat}
    (run : LocalRun caller ticks start middle) (weight : Cfg Γ Λ R → Nat)
    (firstBound secondBound : Nat)
    (first : ∀ n, n ≤ ticks → ∀ reached,
      (next caller)^[n] (some start) = some reached → weight reached ≤ firstBound)
    (second : ∀ n, n ≤ remainingSteps middle → ∀ reached,
      (next caller)^[n] (some middle) = some reached → weight reached ≤ secondBound) :
    ∀ n, n ≤ remainingSteps start → ∀ reached,
      (next caller)^[n] (some start) = some reached →
        weight reached ≤ max firstBound secondBound := by
  have composed := prefix_property_after_localRun caller run
    (fun reached => weight reached ≤ max firstBound secondBound)
    (fun n bound reached executed => (first n bound reached executed).trans (Nat.le_max_left _ _))
    (fun n bound reached executed => (second n bound reached executed).trans (Nat.le_max_right _ _))
  simpa only [LocalRun.remaining caller run] using composed

/-! ## The genuine physical sum and endpoint-recursive dirty allowance -/

/-! ### Complete actual component prefixes and their protected complements -/

theorem fuel_owned_prefix
    (localCaller : (FuelDispatchMachine.Exit ⊕ FuelCallerLabel Λ) → FuelStatement Γ Λ R)
    (start : FuelCfg Γ Λ R) (n : Nat) (bound : n ≤ FuelDispatchMachine.remainingSteps start) :
    ∃ reached, (FuelDispatchMachine.next localCaller)^[n] (some start) = some reached ∧
      FuelDispatchMachine.remainingSteps reached = FuelDispatchMachine.remainingSteps start - n ∧
      Relation.ReflTransGen (FuelDispatchMachine.LocalStep localCaller) start reached ∧
      (n < FuelDispatchMachine.remainingSteps start ↔ FuelDispatchMachine.Owned reached.l) := by
  obtain ⟨reached, executed, rank, path⟩ := Resources.BinaryCounter.FixedWidthMachine.ranked_prefix
    (FuelDispatchMachine.step localCaller) FuelDispatchMachine.remainingSteps
    (FuelDispatchMachine.local_progress localCaller) n start bound
  refine ⟨reached, executed, rank, ?_, ?_⟩
  · exact Relation.ReflTransGen.mono
      (fun before _ h => ⟨(FuelDispatchMachine.remainingSteps_pos_iff before).mp h.1, h.2⟩) _ _ path
  · rw [← FuelDispatchMachine.remainingSteps_pos_iff, rank]
    omega

theorem fuel_prefix_lift
    (localCaller : (FuelDispatchMachine.Exit ⊕ FuelCallerLabel Λ) → FuelStatement Γ Λ R)
    (start : FuelCfg Γ Λ R) (n : Nat) (bound : n ≤ FuelDispatchMachine.remainingSteps start)
    (reached : Cfg Γ Λ R) (executed : (next caller)^[n] (some (fuelCfg start)) = some reached) :
    ∃ middle, (FuelDispatchMachine.next localCaller)^[n] (some start) = some middle ∧
      Relation.ReflTransGen (FuelDispatchMachine.LocalStep localCaller) start middle ∧
      reached = fuelCfg middle := by
  obtain ⟨middle, run, _, path, _⟩ := fuel_owned_prefix localCaller start n bound
  have earlier : ∀ j, j < n → ∃ prior,
      (FuelDispatchMachine.next localCaller)^[j] (some start) = some prior ∧ FuelDispatchMachine.Owned prior.l := by
    intro j strict
    obtain ⟨prior, arrived, _, _, live⟩ := fuel_owned_prefix localCaller start j (by omega)
    exact ⟨prior, arrived, live.mp (by omega)⟩
  have transported := fuel_prefix_transport caller localCaller n start earlier
  rw [run, Option.map_some] at transported
  exact ⟨middle, run, path, Option.some.inj (executed.symm.trans transported)⟩

theorem apply_prefix_lift
    (localCaller : MoveApplyMachine.External (ApplyCallerLabel Λ) → ApplyStatement Γ Λ R)
    (start : ApplyCfg Γ Λ R) (n : Nat) (bound : n ≤ MoveApplyMachine.remainingSteps start)
    (reached : Cfg Γ Λ R) (executed : (next caller)^[n] (some (applyCfg start)) = some reached) :
    ∃ middle, (MoveApplyMachine.next localCaller)^[n] (some start) = some middle ∧
      Relation.ReflTransGen (MoveApplyMachine.LocalStep localCaller) start middle ∧
      reached = applyCfg middle := by
  obtain ⟨middle, run, _, path, _⟩ := MoveApplyMachine.owned_prefix localCaller start n bound
  have earlier : ∀ j, j < n → ∃ prior,
      (MoveApplyMachine.next localCaller)^[j] (some start) = some prior ∧ MoveApplyMachine.Owned prior.l := by
    intro j strict
    obtain ⟨prior, arrived, _, _, live⟩ := MoveApplyMachine.owned_prefix localCaller start j (by omega)
    exact ⟨prior, arrived, live.mp (by omega)⟩
  have transported := apply_prefix_transport caller localCaller n start earlier
  rw [run, Option.map_some] at transported
  exact ⟨middle, run, path, Option.some.inj (executed.symm.trans transported)⟩

theorem equality_prefix_lift
    (localCaller : TreeEqualityMachine.External (EqualityCallerLabel Λ) → EqualityStatement Γ Λ R)
    (start : EqualityCfg Γ Λ R) (n : Nat) (bound : n ≤ TreeEqualityMachine.remainingSteps start)
    (reached : Cfg Γ Λ R) (executed : (next caller)^[n] (some (equalityCfg start)) = some reached) :
    ∃ middle, (TreeEqualityMachine.next localCaller)^[n] (some start) = some middle ∧
      Relation.ReflTransGen (TreeEqualityMachine.LocalStep localCaller) start middle ∧
      reached = equalityCfg middle := by
  obtain ⟨middle, run, _, path, _⟩ := TreeEqualityMachine.owned_prefix localCaller start n bound
  have earlier : ∀ j, j < n → ∃ prior,
      (TreeEqualityMachine.next localCaller)^[j] (some start) = some prior ∧ TreeEqualityMachine.Owned prior.l := by
    intro j strict
    obtain ⟨prior, arrived, _, _, live⟩ := TreeEqualityMachine.owned_prefix localCaller start j (by omega)
    exact ⟨prior, arrived, live.mp (by omega)⟩
  have transported := equality_prefix_transport caller localCaller n start earlier
  rw [run, Option.map_some] at transported
  exact ⟨middle, run, path, Option.some.inj (executed.symm.trans transported)⟩

theorem fuel_local_reaches_frame
    (localCaller : (FuelDispatchMachine.Exit ⊕ FuelCallerLabel Λ) → FuelStatement Γ Λ R)
    {start reached : FuelCfg Γ Λ R}
    (path : Relation.ReflTransGen (FuelDispatchMachine.LocalStep localCaller) start reached) :
    reached.var.2 = start.var.2 ∧ ∀ k, reached.stk (.inr k) = start.stk (.inr k) := by
  induction path with
  | refl => exact ⟨rfl, fun _ => rfl⟩
  | @tail before after _ transition ih =>
      obtain ⟨registers, frame⟩ := fuel_local_step_data localCaller transition
      refine ⟨?_, fun k => (frame k).trans (ih.2 k)⟩
      rw [registers]
      exact ih.1

/-- The full Fuel-protected complement includes the untouched certificate,
all six complementary local stores, and every external stack. -/
theorem fuel_prefix_frame
    (localCaller : (FuelDispatchMachine.Exit ⊕ FuelCallerLabel Λ) → FuelStatement Γ Λ R)
    (start : FuelCfg Γ Λ R) (n : Nat) (bound : n ≤ FuelDispatchMachine.remainingSteps start)
    (reached : Cfg Γ Λ R) (executed : (next caller)^[n] (some (fuelCfg start)) = some reached) :
    ∃ middle, reached = fuelCfg middle ∧ middle.var.2 = start.var.2 ∧
      ∀ k, middle.stk (.inr k) = start.stk (.inr k) := by
  obtain ⟨middle, _, path, rfl⟩ := fuel_prefix_lift caller localCaller start n bound reached executed
  exact ⟨middle, rfl, fuel_local_reaches_frame localCaller path⟩

/-- MoveApply prefixes preserve the full fuel/target/external complement and
the complete component caller register, including the borrowed Bool field. -/
theorem apply_prefix_frame
    (localCaller : MoveApplyMachine.External (ApplyCallerLabel Λ) → ApplyStatement Γ Λ R)
    (start : ApplyCfg Γ Λ R) (n : Nat) (bound : n ≤ MoveApplyMachine.remainingSteps start)
    (reached : Cfg Γ Λ R) (executed : (next caller)^[n] (some (applyCfg start)) = some reached) :
    ∃ middle, reached = applyCfg middle ∧ middle.var.2 = start.var.2 ∧
      ∀ k, middle.stk (.inr k) = start.stk (.inr k) := by
  obtain ⟨middle, _, path, rfl⟩ := apply_prefix_lift caller localCaller start n bound reached executed
  exact ⟨middle, rfl, MoveApplyMachine.local_reaches_frame localCaller path⟩

/-- Equality preserves all seven complementary local stores and every
external stack, as well as Bool/Branch/caller-register data. -/
theorem equality_prefix_frame
    (localCaller : TreeEqualityMachine.External (EqualityCallerLabel Λ) → EqualityStatement Γ Λ R)
    (start : EqualityCfg Γ Λ R) (n : Nat) (bound : n ≤ TreeEqualityMachine.remainingSteps start)
    (reached : Cfg Γ Λ R) (executed : (next caller)^[n] (some (equalityCfg start)) = some reached) :
    ∃ middle, reached = equalityCfg middle ∧ middle.var.2 = start.var.2 ∧
      ∀ k, middle.stk (.inr k) = start.stk (.inr k) := by
  obtain ⟨middle, _, path, rfl⟩ := equality_prefix_lift caller localCaller start n bound reached executed
  exact ⟨middle, rfl, TreeEqualityMachine.local_reaches_frame localCaller path⟩

/-! ### Exact Type-valued timing at every local boundary -/

omit [DecidableEq K] in
def inspectSteps (D : LocalData) : Nat := (evaluateInspect D).steps

omit [DecidableEq K] in
def inspectResult (regs : Registers R) (D : LocalData) (ctx : ∀ k, List (Γ k)) : Cfg Γ Λ R :=
  evaluationCfg regs (evaluateInspect D) ctx

def phaseInTime (q : Phase) (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller)
      (cfg (some (phaseLabel q)) regs D ctx) (some (phaseResult q regs D ctx)) (phaseSteps q D) where
  steps := phaseSteps q D
  evals_in_steps := phase_iterate caller q D regs ctx
  steps_le_m := Nat.le_refl _

def cfgInTime (start : Cfg Γ Λ R) :
    StateTransition.EvalsToInTime (step caller) start (some (finalCfg start)) (remainingSteps start) where
  steps := remainingSteps start
  evals_in_steps := cfg_iterate caller start
  steps_le_m := Nat.le_refl _

def inspectInTime (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller)
      (cfg (some (phaseLabel inspectPhase)) regs D ctx) (some (inspectResult regs D ctx)) (inspectSteps D) where
  steps := inspectSteps D
  evals_in_steps := LocalRun.iterate caller (inspect_localRun caller D regs ctx)
  steps_le_m := Nat.le_refl _

def counterStageInTime (q : Resources.BinaryCounter.FixedWidthMachine.Phase) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller)
      (cfg (some (phaseLabel (counterPhase q))) regs D ctx)
      (some (cfg (some (phaseLabel (fuelJoinPhase (FuelDispatchMachine.exitOfResult (counterFinish q D).result))))
        (resetFuel regs) (counterFinish q D).data ctx)) (counterFinish q D).steps where
  steps := (counterFinish q D).steps
  evals_in_steps := LocalRun.iterate caller (counter_phase_localRun caller q D regs ctx)
  steps_le_m := Nat.le_refl _

def fuelStageInTime (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller)
      (cfg (some (phaseLabel inspectPhase)) regs D ctx)
      (some (cfg (some (phaseLabel (fuelJoinPhase (inspectStageFinish D).result)))
        (resetFuel regs) (inspectStageFinish D).data ctx)) (inspectStageFinish D).steps where
  steps := (inspectStageFinish D).steps
  evals_in_steps := LocalRun.iterate caller (inspect_stage_localRun caller D regs ctx)
  steps_le_m := Nat.le_refl _

def applyStageInTime (q : MoveApplyMachine.Phase) (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller)
      (cfg (some (phaseLabel (applyPhase q))) regs D ctx)
      (some (cfg (some (phaseLabel (applyJoinPhase (applyFinish q D).result)))
        (resetApply regs) (applyFinish q D).data ctx)) (applyFinish q D).steps where
  steps := (applyFinish q D).steps
  evals_in_steps := LocalRun.iterate caller (apply_phase_localRun caller q D regs ctx)
  steps_le_m := Nat.le_refl _

def equalityStageInTime (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller)
      (cfg (some (phaseLabel comparePhase)) regs D ctx)
      (some (cfg (some (phaseLabel (equalityJoinPhase (equalityFinish D).result)))
        (resetEquality regs) (equalityFinish D).data ctx)) (equalityFinish D).steps where
  steps := (equalityFinish D).steps
  evals_in_steps := LocalRun.iterate caller (equality_phase_localRun caller D regs ctx)
  steps_le_m := Nat.le_refl _

def fuelJoinInTime (r : FuelDispatchMachine.Exit) (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller)
      (cfg (some (phaseLabel (fuelJoinPhase r))) regs D ctx)
      (some (cfg (some (fuelJoinTarget r)) (resetAll regs) D ctx)) 1 where
  steps := 1
  evals_in_steps := fuel_join_step caller r D regs ctx
  steps_le_m := Nat.le_refl _

def applyJoinInTime (r : MoveApplyMachine.FinalResult) (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller)
      (cfg (some (phaseLabel (applyJoinPhase r))) regs D ctx)
      (some (cfg (some (applyJoinTarget r)) (resetAll regs) D ctx)) 1 where
  steps := 1
  evals_in_steps := apply_join_step caller r D regs ctx
  steps_le_m := Nat.le_refl _

def equalityJoinInTime (r : TreeEqualityMachine.Result) (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller)
      (cfg (some (phaseLabel (equalityJoinPhase r))) regs D ctx)
      (some (cfg (some (equalityJoinTarget r)) (resetAll regs) D ctx)) 1 where
  steps := 1
  evals_in_steps := equality_join_step caller r D regs ctx
  steps_le_m := Nat.le_refl _

@[simp] theorem phaseInTime_steps (q : Phase) (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (phaseInTime caller q D regs ctx).steps = phaseSteps q D := rfl
@[simp] theorem cfgInTime_steps (start : Cfg Γ Λ R) :
    (cfgInTime caller start).steps = remainingSteps start := rfl
@[simp] theorem inspectInTime_steps (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (inspectInTime caller D regs ctx).steps = inspectSteps D := rfl
@[simp] theorem counterStageInTime_steps (q : Resources.BinaryCounter.FixedWidthMachine.Phase) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (counterStageInTime caller q D regs ctx).steps = (counterFinish q D).steps := rfl
@[simp] theorem fuelStageInTime_steps (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (fuelStageInTime caller D regs ctx).steps = (inspectStageFinish D).steps := rfl
@[simp] theorem applyStageInTime_steps (q : MoveApplyMachine.Phase) (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (applyStageInTime caller q D regs ctx).steps = (applyFinish q D).steps := rfl
@[simp] theorem equalityStageInTime_steps (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (equalityStageInTime caller D regs ctx).steps = (equalityFinish D).steps := rfl
@[simp] theorem fuelJoinInTime_steps (r : FuelDispatchMachine.Exit) (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (fuelJoinInTime caller r D regs ctx).steps = 1 := rfl
@[simp] theorem applyJoinInTime_steps (r : MoveApplyMachine.FinalResult) (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (applyJoinInTime caller r D regs ctx).steps = 1 := rfl
@[simp] theorem equalityJoinInTime_steps (r : TreeEqualityMachine.Result) (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (equalityJoinInTime caller r D regs ctx).steps = 1 := rfl

omit [DecidableEq K] in
def localCells (D : LocalData) : Nat := D.certificate.length + D.moveReverse.length + D.path.length +
  D.source.length + D.saved.length + D.scratch.length + D.units.length + D.fuel.length + D.target.length

section PhysicalSpace
variable [Fintype K]

omit [DecidableEq K] in
def contextCells (ctx : ∀ k, List (Γ k)) : Nat := ∑ k, (ctx k).length

omit [DecidableEq K] in
def mass (D : LocalData) (ctx : ∀ k, List (Γ k)) : Nat := localCells D + contextCells ctx

omit [DecidableEq K] in
def stackCells (c : Cfg Γ Λ R) : Nat := ∑ k : StackId K, (c.stk k).length

omit [DecidableEq K] in
theorem stackCells_eq_sum (c : Cfg Γ Λ R) :
    stackCells c = ∑ k : StackId K, (c.stk k).length := rfl

omit [DecidableEq K] in
theorem localStack_sum (f : LocalStack → Nat) :
    ∑ k, f k = f .certificate + f .moveReverse + f .path + f .source +
      f .saved + f .scratch + f .units + f .fuel + f .target := by
  change (∑ k ∈ ({.certificate, .moveReverse, .path, .source, .saved, .scratch,
    .units, .fuel, .target} : Finset LocalStack), f k) = _
  simp [Nat.add_comm, Nat.add_left_comm]

omit [DecidableEq K] in
theorem stackCells_cfg (label : Option (Label Λ)) (regs : Registers R) (D : LocalData)
    (ctx : ∀ k, List (Γ k)) : stackCells (cfg label regs D ctx) = mass D ctx := by
  rw [stackCells, Fintype.sum_sum_type, localStack_sum]
  rfl

omit [DecidableEq K] in
theorem stackCells_applyCfg (c : ApplyCfg Γ Λ R) :
    stackCells (applyCfg c) = MoveApplyMachine.stackCells c :=
  FrontEndMachine.Transport.stackCells applyStackEquiv applySymbolEquiv c.stk

omit [DecidableEq K] in
theorem stackCells_equalityCfg (c : EqualityCfg Γ Λ R) :
    stackCells (equalityCfg c) = TreeEqualityMachine.stackCells c := by
  rw [TreeEqualityMachine.stackCells_eq_sum]
  exact FrontEndMachine.Transport.stackCells equalityStackEquiv equalitySymbolEquiv c.stk

omit [DecidableEq K] in
theorem fuelStackCells_eq_sum (c : FuelCfg Γ Λ R) :
    FuelDispatchMachine.stackCells c = ∑ k, (c.stk k).length := by
  rw [Fintype.sum_sum_type]
  have localSum (f : Resources.BinaryCounter.FixedWidthMachine.LocalStack → Nat) : ∑ k, f k = f .fuel + f .borrowed := by
    change (∑ k ∈ ({.fuel, .borrowed} : Finset Resources.BinaryCounter.FixedWidthMachine.LocalStack), f k) = _
    simp
  rw [localSum]
  rfl

omit [DecidableEq K] in
theorem stackCells_fuelCfg (c : FuelCfg Γ Λ R) :
    stackCells (fuelCfg c) = FuelDispatchMachine.stackCells c := by
  rw [fuelStackCells_eq_sum]
  exact FrontEndMachine.Transport.stackCells fuelStackEquiv fuelSymbolEquiv c.stk

omit [DecidableEq K] in
theorem applyContext_cells (D : LocalData) (ctx : ∀ k, List (Γ k)) :
    MoveApplyMachine.contextCells (applyContext D ctx) = D.fuel.length + D.target.length + contextCells ctx := by
  have localSum (f : ApplyProtected → Nat) : ∑ k, f k = f .fuel + f .target := by
    change (∑ k ∈ ({.fuel, .target} : Finset ApplyProtected), f k) = _
    simp
  rw [MoveApplyMachine.contextCells, Fintype.sum_sum_type, localSum]
  rfl

omit [DecidableEq K] in
def hAllowance (q : MoveApplyMachine.Phase) (D : LocalData) (ctx : ∀ k, List (Γ k)) : Nat :=
  mass D ctx + MoveApplyMachine.phaseDebt q + MoveApplyMachine.phaseCredit q (applyData D)

omit [DecidableEq K] in
theorem hAllowance_eq_potential (q : MoveApplyMachine.Phase) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    hAllowance q D ctx = MoveApplyMachine.potential
      (applyView (Λ := Λ) (some (MoveApplyMachine.phaseLabel q)) (applyRegisterEquiv.symm regs) D ctx) := by
  change hAllowance q D ctx = MoveApplyMachine.potential
    (MoveApplyMachine.cfg (some (MoveApplyMachine.phaseLabel q)) (applyRegisterEquiv.symm regs)
      (applyData D) (applyContext D ctx))
  rw [MoveApplyMachine.potential_phase_cfg, applyContext_cells]
  simp only [hAllowance, mass, localCells, MoveApplyMachine.localCells, applyData]
  omega

omit [DecidableEq K] in
def inspectAllowance (D : LocalData) (ctx : ∀ k, List (Γ k)) : Nat :=
  if D.certificate = [] then mass D ctx else
    let fuel := counterFinish .borrow D
    match fuel.result with
    | .zero => mass D ctx
    | .positive =>
        let applied := applyFinish (MoveApplyMachine.movePhase .start) fuel.data
        match _returned : applied.result with
        | .inl _ | .inr .failure => max (mass D ctx) (hAllowance (MoveApplyMachine.movePhase .start) fuel.data ctx)
        | .inr .success =>
            max (mass D ctx) (max (hAllowance (MoveApplyMachine.movePhase .start) fuel.data ctx)
              (inspectAllowance applied.data ctx))
termination_by D.certificate.length
decreasing_by
  simpa only [counterFinish_certificate] using
    apply_start_certificate_lt (counterFinish .borrow D).data _returned

omit [DecidableEq K] in
def hJoinAllowance (r : MoveApplyMachine.FinalResult) (D : LocalData) (ctx : ∀ k, List (Γ k)) : Nat :=
  match r with
  | .inl _ | .inr .failure => mass D ctx
  | .inr .success => max (mass D ctx) (inspectAllowance D ctx)

omit [DecidableEq K] in
def hPhaseAllowance (q : MoveApplyMachine.Phase) (D : LocalData) (ctx : ∀ k, List (Γ k)) : Nat :=
  max (hAllowance q D ctx) (hJoinAllowance (applyFinish q D).result (applyFinish q D).data ctx)

omit [DecidableEq K] in
def fuelJoinAllowance (r : FuelDispatchMachine.Exit) (D : LocalData) (ctx : ∀ k, List (Γ k)) : Nat :=
  match r with
  | .atEnd | .zero => mass D ctx
  | .positive => max (mass D ctx) (hPhaseAllowance (MoveApplyMachine.movePhase .start) D ctx)

omit [DecidableEq K] in
def counterAllowance (q : Resources.BinaryCounter.FixedWidthMachine.Phase) (D : LocalData) (ctx : ∀ k, List (Γ k)) : Nat :=
  max (mass D ctx) (fuelJoinAllowance (FuelDispatchMachine.exitOfResult (counterFinish q D).result) (counterFinish q D).data ctx)

omit [DecidableEq K] in
def phaseAllowance (q : Phase) (D : LocalData) (ctx : ∀ k, List (Γ k)) : Nat :=
  match q with
  | .inl (.inl q) => counterAllowance q D ctx
  | .inl (.inr (.inl r)) => fuelJoinAllowance (FuelDispatchMachine.exitOfResult r) D ctx
  | .inl (.inr (.inr (.inl .inspectCertificate))) => inspectAllowance D ctx
  | .inl (.inr (.inr (.inl .atEnd))) => fuelJoinAllowance .atEnd D ctx
  | .inl (.inr (.inr (.inr impossible))) => Empty.elim impossible
  | .inr (.inl (.inl q)) => hPhaseAllowance (MoveApplyMachine.movePhase q) D ctx
  | .inr (.inl (.inr (.inl r))) => hPhaseAllowance (MoveApplyMachine.dispatchPhase r) D ctx
  | .inr (.inl (.inr (.inr (.inl q)))) => hPhaseAllowance (MoveApplyMachine.positionPhase q) D ctx
  | .inr (.inl (.inr (.inr (.inr (.inl r))))) => hJoinAllowance r D ctx
  | .inr (.inl (.inr (.inr (.inr (.inr impossible))))) => Empty.elim impossible
  | .inr (.inr (.inl .compare)) => mass D ctx
  | .inr (.inr (.inr (.inl _))) => mass D ctx
  | .inr (.inr (.inr (.inr impossible))) => Empty.elim impossible

omit [DecidableEq K] in
def allowance (c : Cfg Γ Λ R) : Nat :=
  match c.l with
  | some (.inl q) => phaseAllowance (.inl q) (dataOfCfg c) (contextOfCfg c)
  | some (.inr (.inl q)) => phaseAllowance (.inr (.inl q)) (dataOfCfg c) (contextOfCfg c)
  | some (.inr (.inr (.inl q))) => phaseAllowance (.inr (.inr q)) (dataOfCfg c) (contextOfCfg c)
  | _ => stackCells c

omit [DecidableEq K] in
theorem allowance_phase_cfg (q : Phase) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    allowance (cfg (some (phaseLabel (Λ := Λ) q)) regs D ctx) = phaseAllowance q D ctx := by
  cases q with
  | inl q => rfl
  | inr q => cases q <;> rfl

omit [DecidableEq K] in
theorem mass_le_hAllowance (q : MoveApplyMachine.Phase) (D : LocalData) (ctx : ∀ k, List (Γ k)) :
    mass D ctx ≤ hAllowance q D ctx := by unfold hAllowance; omega

omit [DecidableEq K] in
theorem mass_le_inspectAllowance (D : LocalData) (ctx : ∀ k, List (Γ k)) :
    mass D ctx ≤ inspectAllowance D ctx := by
  rw [inspectAllowance]
  split
  · exact Nat.le_refl _
  · dsimp only
    split
    · exact Nat.le_refl _
    · split <;> exact Nat.le_max_left _ _

omit [DecidableEq K] in
theorem mass_le_hJoinAllowance (r : MoveApplyMachine.FinalResult) (D : LocalData) (ctx : ∀ k, List (Γ k)) :
    mass D ctx ≤ hJoinAllowance r D ctx := by
  cases r with
  | inl u => exact Nat.le_refl _
  | inr r => cases r with
    | failure => exact Nat.le_refl _
    | success => exact Nat.le_max_left _ _

omit [DecidableEq K] in
theorem mass_le_hPhaseAllowance (q : MoveApplyMachine.Phase) (D : LocalData) (ctx : ∀ k, List (Γ k)) :
    mass D ctx ≤ hPhaseAllowance q D ctx :=
  (mass_le_hAllowance q D ctx).trans (Nat.le_max_left _ _)

omit [DecidableEq K] in
theorem mass_le_fuelJoinAllowance (r : FuelDispatchMachine.Exit) (D : LocalData) (ctx : ∀ k, List (Γ k)) :
    mass D ctx ≤ fuelJoinAllowance r D ctx := by
  cases r with
  | atEnd | zero => exact Nat.le_refl _
  | positive => exact Nat.le_max_left _ _

omit [DecidableEq K] in
theorem mass_le_phaseAllowance (q : Phase) (D : LocalData) (ctx : ∀ k, List (Γ k)) :
    mass D ctx ≤ phaseAllowance q D ctx := by
  rcases q with fuel | (applied | equality)
  · rcases fuel with q | (r | (d | impossible))
    · exact Nat.le_max_left _ _
    · exact mass_le_fuelJoinAllowance _ D ctx
    · cases d with
      | inspectCertificate => exact mass_le_inspectAllowance D ctx
      | atEnd => exact Nat.le_refl _
    · exact Empty.elim impossible
  · rcases applied with q | (r | (q | (r | impossible)))
    · exact mass_le_hPhaseAllowance _ D ctx
    · exact mass_le_hPhaseAllowance _ D ctx
    · exact mass_le_hPhaseAllowance _ D ctx
    · exact mass_le_hJoinAllowance r D ctx
    · exact Empty.elim impossible
  · rcases equality with q | (r | impossible)
    · cases q; exact Nat.le_refl _
    · exact Nat.le_refl _
    · exact Empty.elim impossible

omit [DecidableEq K] in
theorem nonowned_allowance (c : Cfg Γ Λ R) (nonowned : ¬ Owned c.l) : allowance c = stackCells c := by
  cases hLabel : c.l with
  | none => simp only [allowance, hLabel]
  | some l =>
      rcases l with q | (q | (q | external))
      · exact False.elim (nonowned (by simp only [hLabel, Owned]))
      · exact False.elim (nonowned (by simp only [hLabel, Owned]))
      · exact False.elim (nonowned (by simp only [hLabel, Owned]))
      · simp only [allowance, hLabel]

omit [DecidableEq K] in
theorem stackCells_le_allowance (c : Cfg Γ Λ R) : stackCells c ≤ allowance c := by
  by_cases owned : Owned c.l
  · obtain ⟨q, regs, D, ctx, rfl⟩ := owned_cases c owned
    rw [stackCells_cfg, allowance_phase_cfg]
    exact mass_le_phaseAllowance q D ctx
  · rw [nonowned_allowance c owned]

/-! ### Actual physical bounds of the complete transported component segments -/

theorem fuel_prefix_stackCells
    (localCaller : (FuelDispatchMachine.Exit ⊕ FuelCallerLabel Λ) → FuelStatement Γ Λ R)
    (start : FuelCfg Γ Λ R) (n : Nat) (bound : n ≤ FuelDispatchMachine.remainingSteps start)
    (reached : Cfg Γ Λ R) (executed : (next caller)^[n] (some (fuelCfg start)) = some reached) :
    stackCells reached = stackCells (fuelCfg start) := by
  obtain ⟨middle, _, path, rfl⟩ := fuel_prefix_lift caller localCaller start n bound reached executed
  rw [stackCells_fuelCfg, stackCells_fuelCfg]
  exact (FuelDispatchMachine.local_reaches_preserves localCaller path).2.2.2

theorem apply_prefix_stackCells_le
    (localCaller : MoveApplyMachine.External (ApplyCallerLabel Λ) → ApplyStatement Γ Λ R)
    (start : ApplyCfg Γ Λ R) (n : Nat) (bound : n ≤ MoveApplyMachine.remainingSteps start)
    (reached : Cfg Γ Λ R) (executed : (next caller)^[n] (some (applyCfg start)) = some reached) :
    stackCells reached ≤ MoveApplyMachine.potential start := by
  obtain ⟨middle, run, _, rfl⟩ := apply_prefix_lift caller localCaller start n bound reached executed
  rw [stackCells_applyCfg]
  exact MoveApplyMachine.prefix_stackCells_le_dirty localCaller start n bound middle run

theorem equality_prefix_stackCells_le
    (localCaller : TreeEqualityMachine.External (EqualityCallerLabel Λ) → EqualityStatement Γ Λ R)
    (start : EqualityCfg Γ Λ R) (n : Nat) (bound : n ≤ TreeEqualityMachine.remainingSteps start)
    (reached : Cfg Γ Λ R) (executed : (next caller)^[n] (some (equalityCfg start)) = some reached) :
    stackCells reached ≤ stackCells (equalityCfg start) := by
  obtain ⟨middle, _, path, rfl⟩ := equality_prefix_lift caller localCaller start n bound reached executed
  rw [stackCells_equalityCfg, stackCells_equalityCfg]
  exact (TreeEqualityMachine.local_reaches_preserves localCaller path).2.2

theorem counter_stage_stackCells (q : Resources.BinaryCounter.FixedWidthMachine.Phase) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (n : Nat) (bound : n ≤ (counterFinish q D).steps)
    (reached : Cfg Γ Λ R)
    (executed : (next caller)^[n] (some (cfg (some (phaseLabel (counterPhase q))) regs D ctx)) = some reached) :
    stackCells reached = mass D ctx := by
  let localCaller : (FuelDispatchMachine.Exit ⊕ FuelCallerLabel Λ) → FuelStatement Γ Λ R := fun _ => .halt
  let start : FuelCfg Γ Λ R := fuelView (some (Resources.BinaryCounter.FixedWidthMachine.phaseLabel q)) regs D ctx
  have startEq : fuelCfg start = cfg (some (phaseLabel (counterPhase q))) regs D ctx := by
    rw [fuelCfg_view]
    rfl
  have rank : FuelDispatchMachine.remainingSteps start = (counterFinish q D).steps := by cases q <;> rfl
  have cells := fuel_prefix_stackCells caller localCaller start n (by rwa [rank]) reached (by rwa [startEq])
  rwa [startEq, stackCells_cfg] at cells

theorem inspect_stage_stackCells (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (n : Nat) (bound : n ≤ (inspectStageFinish D).steps)
    (reached : Cfg Γ Λ R)
    (executed : (next caller)^[n] (some (cfg (some (phaseLabel inspectPhase)) regs D ctx)) = some reached) :
    stackCells reached = mass D ctx := by
  let localCaller : (FuelDispatchMachine.Exit ⊕ FuelCallerLabel Λ) → FuelStatement Γ Λ R := fun _ => .halt
  let start : FuelCfg Γ Λ R := fuelView (some FuelDispatchMachine.inspectLabel) regs D ctx
  have startEq : fuelCfg start = cfg (some (phaseLabel inspectPhase)) regs D ctx := by
    rw [fuelCfg_view]
    rfl
  have rank : FuelDispatchMachine.remainingSteps start = (inspectStageFinish D).steps := by
    cases cert : D.certificate with
    | nil => simp only [start, fuelView, FuelDispatchMachine.remainingSteps, FuelDispatchMachine.cfg, Resources.BinaryCounter.FixedWidthMachine.cfg, FuelDispatchMachine.inspectLabel,
        Resources.BinaryCounter.FixedWidthMachine.callerLabel, FuelDispatchMachine.stores, cert, inspectStageFinish]
    | cons a rest =>
        simp only [start, fuelView, FuelDispatchMachine.remainingSteps, FuelDispatchMachine.cfg, Resources.BinaryCounter.FixedWidthMachine.cfg, FuelDispatchMachine.inspectLabel,
          Resources.BinaryCounter.FixedWidthMachine.callerLabel, FuelDispatchMachine.stores, cert, inspectStageFinish, counterFinish]
        omega
  have cells := fuel_prefix_stackCells caller localCaller start n (by rwa [rank]) reached (by rwa [startEq])
  rwa [startEq, stackCells_cfg] at cells

theorem apply_stage_stackCells_le (q : MoveApplyMachine.Phase) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (n : Nat) (bound : n ≤ (applyFinish q D).steps)
    (reached : Cfg Γ Λ R)
    (executed : (next caller)^[n] (some (cfg (some (phaseLabel (applyPhase q))) regs D ctx)) = some reached) :
    stackCells reached ≤ hAllowance q D ctx := by
  let localCaller : MoveApplyMachine.External (ApplyCallerLabel Λ) → ApplyStatement Γ Λ R := fun _ => .halt
  let start : ApplyCfg Γ Λ R := applyView (some (MoveApplyMachine.phaseLabel q)) (applyRegisterEquiv.symm regs) D ctx
  have startEq : applyCfg start = cfg (some (phaseLabel (applyPhase q))) regs D ctx := by
    rw [applyCfg_view]
    simp only [Option.map_some, applyLabelEquiv_phase, Equiv.apply_symm_apply]
  have rank : MoveApplyMachine.remainingSteps start = (applyFinish q D).steps := by
    change MoveApplyMachine.remainingSteps (MoveApplyMachine.cfg _ _ _ _) = _
    rw [MoveApplyMachine.remainingSteps_phase_cfg]
    rfl
  have cells := apply_prefix_stackCells_le caller localCaller start n (by rwa [rank]) reached (by rwa [startEq])
  rwa [← hAllowance_eq_potential q D regs ctx] at cells

theorem equality_stage_stackCells_le (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (n : Nat) (bound : n ≤ (equalityFinish D).steps)
    (reached : Cfg Γ Λ R)
    (executed : (next caller)^[n] (some (cfg (some (phaseLabel comparePhase)) regs D ctx)) = some reached) :
    stackCells reached ≤ mass D ctx := by
  let localCaller : TreeEqualityMachine.External (EqualityCallerLabel Λ) → EqualityStatement Γ Λ R := fun _ => .halt
  let start : EqualityCfg Γ Λ R := equalityView (some (TreeEqualityMachine.phaseLabel .compare)) (equalityRegisterEquiv.symm regs) D ctx
  have startEq : equalityCfg start = cfg (some (phaseLabel comparePhase)) regs D ctx := by
    rw [equalityCfg_view]
    simp only [Option.map_some, equalityLabelEquiv_phase, Equiv.apply_symm_apply]
  have rank : TreeEqualityMachine.remainingSteps start = (equalityFinish D).steps := rfl
  have cells := equality_prefix_stackCells_le caller localCaller start n (by rwa [rank]) reached (by rwa [startEq])
  rwa [startEq, stackCells_cfg] at cells

omit [Fintype K] in
/-- Equality's complete store equation, including the exact residual raw words
and every protected store, at each inclusive component prefix. -/
theorem equality_prefix_cfg (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (n : Nat) (bound : n ≤ (equalityFinish D).steps) :
    (next caller)^[n] (some (cfg (some (phaseLabel comparePhase)) regs D ctx)) =
      some (cfg (some (if n < (equalityFinish D).steps then phaseLabel comparePhase
          else phaseLabel (equalityJoinPhase (equalityFinish D).result)))
        (if n = 0 then regs else resetEquality regs)
        { D with source := D.source.drop n, target := D.target.drop n } ctx) := by
  change n ≤ TreeEqualityMachine.runSteps D.source D.target at bound
  let localCaller : TreeEqualityMachine.External (EqualityCallerLabel Λ) → EqualityStatement Γ Λ R := fun _ => .halt
  let start : EqualityCfg Γ Λ R := equalityView (some (TreeEqualityMachine.phaseLabel .compare)) (equalityRegisterEquiv.symm regs) D ctx
  have startEq : equalityCfg start = cfg (some (phaseLabel comparePhase)) regs D ctx := by
    rw [equalityCfg_view]
    simp only [Option.map_some, equalityLabelEquiv_phase, Equiv.apply_symm_apply]
  have earlier : ∀ j, j < n → ∃ prior,
      (TreeEqualityMachine.next localCaller)^[j] (some start) = some prior ∧ TreeEqualityMachine.Owned prior.l := by
    intro j strict
    obtain ⟨prior, arrived, _, _, live⟩ := TreeEqualityMachine.owned_prefix localCaller start j (by change j ≤ TreeEqualityMachine.runSteps D.source D.target; omega)
    exact ⟨prior, arrived, live.mp (by change j < TreeEqualityMachine.runSteps D.source D.target; omega)⟩
  rw [← startEq, equality_prefix_transport caller localCaller n start earlier]
  have localRun := TreeEqualityMachine.prefix_exact localCaller D.source D.target (equalityRegisterEquiv.symm regs)
    (equalityContext D ctx) n bound
  change (TreeEqualityMachine.next localCaller)^[n] (some start) = _ at localRun
  rw [localRun, Option.map_some]
  unfold TreeEqualityMachine.prefixCfg
  rw [equalityCfg_partial]
  congr 1
  apply cfg_ext
  · change (some (if n < TreeEqualityMachine.runSteps D.source D.target
        then TreeEqualityMachine.phaseLabel .compare
        else TreeEqualityMachine.resultLabel (TreeEqualityMachine.wordResult D.source D.target))).map
        equalityLabelEquiv =
      some (if n < TreeEqualityMachine.runSteps D.source D.target then phaseLabel comparePhase
        else phaseLabel (equalityJoinPhase (TreeEqualityMachine.wordResult D.source D.target)))
    by_cases early : n < TreeEqualityMachine.runSteps D.source D.target
    · simp only [early, ite_true, Option.map_some, equalityLabelEquiv_phase]
    · simp only [early, ite_false, Option.map_some, equalityLabelEquiv_result]
  · change equalityRegisterEquiv (TreeEqualityMachine.prefixRegisters n (equalityRegisterEquiv.symm regs)) =
      if n = 0 then regs else resetEquality regs
    by_cases zero : n = 0
    · simp only [TreeEqualityMachine.prefixRegisters, zero, ite_true, Equiv.apply_symm_apply]
    · simp only [TreeEqualityMachine.prefixRegisters, zero, ite_false,
        equalityRegisterEquiv_reset, Equiv.apply_symm_apply]
  · rfl

theorem equality_prefix_stackCells_exact (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (n : Nat) (bound : n ≤ (equalityFinish D).steps) (reached : Cfg Γ Λ R)
    (executed : (next caller)^[n] (some (cfg (some (phaseLabel comparePhase)) regs D ctx)) = some reached) :
    stackCells reached =
      mass { D with source := D.source.drop n, target := D.target.drop n } ctx := by
  have same := Option.some.inj (executed.symm.trans (equality_prefix_cfg caller D regs ctx n bound))
  rw [same, stackCells_cfg]

include caller in
theorem counterFinish_mass (q : Resources.BinaryCounter.FixedWidthMachine.Phase) (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    mass (counterFinish q D).data ctx = mass D ctx := by
  have cells := counter_stage_stackCells caller q D regs ctx (counterFinish q D).steps (Nat.le_refl _)
    _ (LocalRun.iterate caller (counter_phase_localRun caller q D regs ctx))
  rwa [stackCells_cfg] at cells

include caller in
theorem inspectStageFinish_mass (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    mass (inspectStageFinish D).data ctx = mass D ctx := by
  have cells := inspect_stage_stackCells caller D regs ctx (inspectStageFinish D).steps (Nat.le_refl _)
    _ (LocalRun.iterate caller (inspect_stage_localRun caller D regs ctx))
  rwa [stackCells_cfg] at cells

include caller in
theorem applyFinish_mass_le (q : MoveApplyMachine.Phase) (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    mass (applyFinish q D).data ctx ≤ hAllowance q D ctx := by
  have cells := apply_stage_stackCells_le caller q D regs ctx (applyFinish q D).steps (Nat.le_refl _)
    _ (LocalRun.iterate caller (apply_phase_localRun caller q D regs ctx))
  rwa [stackCells_cfg] at cells

include caller in
theorem equalityFinish_mass_le (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    mass (equalityFinish D).data ctx ≤ mass D ctx := by
  have cells := equality_stage_stackCells_le caller D regs ctx (equalityFinish D).steps (Nat.le_refl _)
    _ (LocalRun.iterate caller (equality_phase_localRun caller D regs ctx))
  rwa [stackCells_cfg] at cells

/-- A paid join preserves the actual sum at both of its two boundary times. -/
theorem stackCells_prefix_one (label target : Label Λ) (D : LocalData) (regs outRegs : Registers R)
    (ctx : ∀ k, List (Γ k))
    (transition : step caller (cfg (some label) regs D ctx) = some (cfg (some target) outRegs D ctx))
    (n : Nat) (bound : n ≤ 1) (reached : Cfg Γ Λ R)
    (executed : (next caller)^[n] (some (cfg (some label) regs D ctx)) = some reached) :
    stackCells reached = mass D ctx := by
  have casesN : n = 0 ∨ n = 1 := by omega
  rcases casesN with rfl | rfl
  · have same : reached = cfg (some label) regs D ctx := Option.some.inj executed.symm
    rw [same, stackCells_cfg]
  · have same : reached = cfg (some target) outRegs D ctx := Option.some.inj (executed.symm.trans transition)
    rw [same, stackCells_cfg]

/-! ### All-state actual prefix bounds from explicit stage allowances -/

/-- A property of the actual inclusive owned prefix, not a maximum over an
auxiliary trace or a replacement runtime evaluator. -/
def PrefixBound (start : Cfg Γ Λ R) (limit : Nat) : Prop :=
  ∀ n, n ≤ remainingSteps start → ∀ reached,
    (next caller)^[n] (some start) = some reached → stackCells reached ≤ limit

theorem PrefixBound.mono {start : Cfg Γ Λ R} {a b : Nat}
    (bounded : PrefixBound caller start a) (larger : a ≤ b) : PrefixBound caller start b :=
  fun n bound reached executed => (bounded n bound reached executed).trans larger

theorem result_join_prefix_bound (q : Phase) (result : Bool) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k))
    (transition : step caller (cfg (some (phaseLabel q)) regs D ctx) =
      some (cfg (some (resultLabel result)) (resetAll regs) D ctx)) :
    PrefixBound caller (cfg (some (phaseLabel q)) regs D ctx) (mass D ctx) := by
  have run := phase_step_localRun caller transition
  have rank := LocalRun.remaining caller run
  have finalRank : remainingSteps (cfg (some (resultLabel (Λ := Λ) result)) (resetAll regs) D ctx) = 0 := rfl
  rw [finalRank, Nat.add_zero] at rank
  intro n bound reached executed
  exact Nat.le_of_eq (stackCells_prefix_one caller _ _ D regs (resetAll regs) ctx transition
    n (by omega) reached executed)

theorem equality_join_prefix_bound (r : TreeEqualityMachine.Result) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    PrefixBound caller (cfg (some (phaseLabel (equalityJoinPhase r))) regs D ctx) (mass D ctx) := by
  exact result_join_prefix_bound caller (equalityJoinPhase r) (equalityResult r) D regs ctx
    (equality_join_step caller r D regs ctx)

theorem equality_complete_prefix_bound (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    PrefixBound caller (cfg (some (phaseLabel comparePhase)) regs D ctx) (mass D ctx) := by
  have first := equality_phase_localRun caller D regs ctx
  have composed := prefix_bound_after_localRun caller first stackCells
    (mass D ctx) (mass (equalityFinish D).data ctx)
    (fun n bound reached executed => equality_stage_stackCells_le caller D regs ctx n bound reached executed)
    (equality_join_prefix_bound caller (equalityFinish D).result (equalityFinish D).data (resetEquality regs) ctx)
  rw [max_eq_left (equalityFinish_mass_le caller D regs ctx)] at composed
  exact composed

theorem apply_join_prefix_bound_of_success (r : MoveApplyMachine.FinalResult) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k))
    (continued : r = MoveApplyMachine.success →
      PrefixBound caller (cfg (some (phaseLabel inspectPhase)) (resetAll regs) D ctx) (inspectAllowance D ctx)) :
    PrefixBound caller (cfg (some (phaseLabel (applyJoinPhase r))) regs D ctx) (hJoinAllowance r D ctx) := by
  cases r with
  | inl token =>
      exact result_join_prefix_bound caller (applyJoinPhase (.inl token)) false D regs ctx
        (apply_join_step caller (.inl token) D regs ctx)
  | inr r => cases r with
    | failure =>
        exact result_join_prefix_bound caller (applyJoinPhase (.inr .failure)) false D regs ctx
          (apply_join_step caller (.inr .failure) D regs ctx)
    | success =>
        exact prefix_bound_after_localRun caller (apply_join_localRun caller MoveApplyMachine.success D regs ctx)
          stackCells (mass D ctx) (inspectAllowance D ctx)
          (fun n bound reached executed => Nat.le_of_eq
            (stackCells_prefix_one caller _ _ D regs (resetAll regs) ctx
              (apply_join_step caller MoveApplyMachine.success D regs ctx) n bound reached executed))
          (continued rfl)

theorem apply_phase_prefix_bound_of_success (q : MoveApplyMachine.Phase) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k))
    (continued : (applyFinish q D).result = MoveApplyMachine.success →
      PrefixBound caller
        (cfg (some (phaseLabel inspectPhase)) (resetAll regs) (applyFinish q D).data ctx)
        (inspectAllowance (applyFinish q D).data ctx)) :
    PrefixBound caller (cfg (some (phaseLabel (applyPhase q))) regs D ctx) (hPhaseAllowance q D ctx) := by
  apply prefix_bound_after_localRun caller (apply_phase_localRun caller q D regs ctx)
    stackCells (hAllowance q D ctx) (hJoinAllowance (applyFinish q D).result (applyFinish q D).data ctx)
  · exact fun n bound reached executed => apply_stage_stackCells_le caller q D regs ctx n bound reached executed
  · apply apply_join_prefix_bound_of_success caller (applyFinish q D).result (applyFinish q D).data (resetApply regs) ctx
    intro returned
    simpa only [resetAll_resetApply] using continued returned

theorem fuel_join_prefix_bound_of_success (r : FuelDispatchMachine.Exit) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k))
    (continued : (applyFinish (MoveApplyMachine.movePhase .start) D).result = MoveApplyMachine.success →
      PrefixBound caller
        (cfg (some (phaseLabel inspectPhase)) (resetAll regs) (applyFinish (MoveApplyMachine.movePhase .start) D).data ctx)
        (inspectAllowance (applyFinish (MoveApplyMachine.movePhase .start) D).data ctx)) :
    PrefixBound caller (cfg (some (phaseLabel (fuelJoinPhase r))) regs D ctx) (fuelJoinAllowance r D ctx) := by
  cases r with
  | zero =>
      exact result_join_prefix_bound caller (fuelJoinPhase .zero) false D regs ctx
        (fuel_join_step caller .zero D regs ctx)
  | atEnd =>
      have composed := prefix_bound_after_localRun caller (fuel_join_localRun caller .atEnd D regs ctx)
        stackCells (mass D ctx) (mass D ctx)
        (fun n bound reached executed => Nat.le_of_eq
          (stackCells_prefix_one caller _ _ D regs (resetAll regs) ctx
            (fuel_join_step caller .atEnd D regs ctx) n bound reached executed))
        (equality_complete_prefix_bound caller D (resetAll regs) ctx)
      simpa only [PrefixBound, fuelJoinAllowance, max_self] using composed
  | positive =>
      apply prefix_bound_after_localRun caller (fuel_join_localRun caller .positive D regs ctx)
        stackCells (mass D ctx) (hPhaseAllowance (MoveApplyMachine.movePhase .start) D ctx)
      · exact fun n bound reached executed => Nat.le_of_eq
          (stackCells_prefix_one caller _ _ D regs (resetAll regs) ctx
            (fuel_join_step caller .positive D regs ctx) n bound reached executed)
      · apply apply_phase_prefix_bound_of_success caller (MoveApplyMachine.movePhase .start) D (resetAll regs) ctx
        intro returned
        simpa only [resetAll_resetAll] using continued returned

omit [DecidableEq K] in
@[simp] theorem inspectStageFinish_certificate (D : LocalData) :
    (inspectStageFinish D).data.certificate = D.certificate := by
  cases certificate : D.certificate <;> simp only [inspectStageFinish, certificate, counterFinish_certificate]

include caller in
/-- The inspector allowance is exactly the maximum of the conserved Fuel
stage and the allowance of its literal result-join configuration. -/
theorem inspectAllowance_stage (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    inspectAllowance D ctx =
      max (mass D ctx) (fuelJoinAllowance (inspectStageFinish D).result (inspectStageFinish D).data ctx) := by
  rw [inspectAllowance]
  by_cases empty : D.certificate = []
  · simp only [empty, ite_true, inspectStageFinish, fuelJoinAllowance, max_self]
  · rw [ite_eq_right empty]
    obtain ⟨tag, rest, certificate⟩ := List.exists_cons_of_ne_nil empty
    simp only [inspectStageFinish, certificate]
    have conserved := counterFinish_mass caller .borrow D regs ctx
    have endpoint := applyFinish_mass_le caller (MoveApplyMachine.movePhase .start) (counterFinish .borrow D).data regs ctx
    cases fuel : (counterFinish .borrow D).result with
    | zero => simp only [FuelDispatchMachine.exitOfResult, fuelJoinAllowance, conserved, max_self]
    | positive =>
        simp only [FuelDispatchMachine.exitOfResult, fuelJoinAllowance, hPhaseAllowance]
        cases returned : (applyFinish (MoveApplyMachine.movePhase .start) (counterFinish .borrow D).data).result with
        | inl token =>
            simp only [hJoinAllowance, conserved]
            omega
        | inr r => cases r with
          | failure =>
              simp only [hJoinAllowance, conserved]
              omega
          | success =>
              simp only [hJoinAllowance, conserved]
              have nextMass := mass_le_inspectAllowance
                (applyFinish (MoveApplyMachine.movePhase .start) (counterFinish .borrow D).data).data ctx
              omega

/-- The universal dirty inspector space theorem. Recursion occurs only after
a genuine full MoveApplyMachine.start success on its proved shorter certificate suffix. -/
theorem inspect_prefix_bound (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    PrefixBound caller (cfg (some (phaseLabel inspectPhase)) regs D ctx) (inspectAllowance D ctx) := by
  revert regs
  refine (measure (fun D : LocalData => D.certificate.length)).wf.induction
    (C := fun D : LocalData => ∀ regs : Registers R,
      PrefixBound caller (cfg (some (phaseLabel inspectPhase)) regs D ctx) (inspectAllowance D ctx)) D ?_
  intro D ih regs
  rw [inspectAllowance_stage caller D regs ctx]
  apply prefix_bound_after_localRun caller (inspect_stage_localRun caller D regs ctx)
    stackCells (mass D ctx)
    (fuelJoinAllowance (inspectStageFinish D).result (inspectStageFinish D).data ctx)
  · exact fun n bound reached executed => Nat.le_of_eq (inspect_stage_stackCells caller D regs ctx n bound reached executed)
  · apply fuel_join_prefix_bound_of_success caller (inspectStageFinish D).result (inspectStageFinish D).data (resetFuel regs) ctx
    intro returned
    have decrease := apply_start_certificate_lt (inspectStageFinish D).data returned
    have strict : (applyFinish (MoveApplyMachine.movePhase .start) (inspectStageFinish D).data).data.certificate.length < D.certificate.length := by
      simpa only [inspectStageFinish_certificate] using decrease
    exact ih _ strict (resetAll (resetFuel regs))

theorem apply_join_prefix_bound (r : MoveApplyMachine.FinalResult) (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    PrefixBound caller (cfg (some (phaseLabel (applyJoinPhase r))) regs D ctx) (hJoinAllowance r D ctx) :=
  apply_join_prefix_bound_of_success caller r D regs ctx (fun _ => inspect_prefix_bound caller D (resetAll regs) ctx)

theorem apply_complete_prefix_bound (q : MoveApplyMachine.Phase) (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    PrefixBound caller (cfg (some (phaseLabel (applyPhase q))) regs D ctx) (hPhaseAllowance q D ctx) :=
  apply_phase_prefix_bound_of_success caller q D regs ctx
    (fun _ => inspect_prefix_bound caller (applyFinish q D).data (resetAll regs) ctx)

theorem fuel_join_prefix_bound (r : FuelDispatchMachine.Exit) (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    PrefixBound caller (cfg (some (phaseLabel (fuelJoinPhase r))) regs D ctx) (fuelJoinAllowance r D ctx) :=
  fuel_join_prefix_bound_of_success caller r D regs ctx
    (fun _ => inspect_prefix_bound caller (applyFinish (MoveApplyMachine.movePhase .start) D).data (resetAll regs) ctx)

theorem counter_complete_prefix_bound (q : Resources.BinaryCounter.FixedWidthMachine.Phase) (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    PrefixBound caller (cfg (some (phaseLabel (counterPhase q))) regs D ctx) (counterAllowance q D ctx) := by
  exact prefix_bound_after_localRun caller (counter_phase_localRun caller q D regs ctx)
    stackCells (mass D ctx)
    (fuelJoinAllowance (FuelDispatchMachine.exitOfResult (counterFinish q D).result) (counterFinish q D).data ctx)
    (fun n bound reached executed => Nat.le_of_eq (counter_stage_stackCells caller q D regs ctx n bound reached executed))
    (fuel_join_prefix_bound caller _ (counterFinish q D).data (resetFuel regs) ctx)

/-- Every owned starting phase has its explicit endpoint-recursive allowance;
this includes arbitrary partial H and W phases with arbitrary dirty stores. -/
theorem phase_prefix_bound (q : Phase) (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    PrefixBound caller (cfg (some (phaseLabel q)) regs D ctx) (phaseAllowance q D ctx) := by
  rcases q with fuel | (applied | equality)
  · rcases fuel with q | (r | (d | impossible))
    · exact counter_complete_prefix_bound caller q D regs ctx
    · cases r with
      | zero => exact fuel_join_prefix_bound caller .zero D regs ctx
      | positive => exact fuel_join_prefix_bound caller .positive D regs ctx
    · cases d with
      | inspectCertificate => exact inspect_prefix_bound caller D regs ctx
      | atEnd => exact fuel_join_prefix_bound caller .atEnd D regs ctx
    · exact Empty.elim impossible
  · rcases applied with q | (r | (q | (r | impossible)))
    · exact apply_complete_prefix_bound caller (MoveApplyMachine.movePhase q) D regs ctx
    · exact apply_complete_prefix_bound caller (MoveApplyMachine.dispatchPhase r) D regs ctx
    · exact apply_complete_prefix_bound caller (MoveApplyMachine.positionPhase q) D regs ctx
    · exact apply_join_prefix_bound caller r D regs ctx
    · exact Empty.elim impossible
  · rcases equality with q | (r | impossible)
    · cases q; exact equality_complete_prefix_bound caller D regs ctx
    · exact equality_join_prefix_bound caller r D regs ctx
    · exact Empty.elim impossible

/-- Actual total physical storage at every inclusive prefix through the first
outer result; callers may act only after that boundary. -/
theorem prefix_stackCells_le_dirty (start : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start)
    (reached : Cfg Γ Λ R) (executed : (next caller)^[n] (some start) = some reached) :
    stackCells reached ≤ allowance start := by
  by_cases owned : Owned start.l
  · obtain ⟨q, regs, D, ctx, rfl⟩ := owned_cases start owned
    rw [allowance_phase_cfg]
    exact phase_prefix_bound caller q D regs ctx n bound reached executed
  · rw [nonowned_remaining start owned] at bound
    have zero : n = 0 := by omega
    subst n
    have same : reached = start := Option.some.inj executed.symm
    rw [same, nonowned_allowance start owned]

/-- The same reached configuration carries execution, exact remaining time,
local closure, ownership, zero-time identity, caller/frame preservation, and
the universal dirty physical bound. The staged-register enrichment is supplied
by the separately proved exact prefix-reset theorem. -/
theorem owned_prefix_physical (start : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start) :
    ∃ reached, (next caller)^[n] (some start) = some reached ∧
      remainingSteps reached = remainingSteps start - n ∧
      Relation.ReflTransGen (LocalStep caller) start reached ∧
      (n < remainingSteps start ↔ Owned reached.l) ∧
      (n = 0 → reached = start) ∧ reached.var.2.2 = start.var.2.2 ∧
      (∀ k, reached.stk (.inr k) = start.stk (.inr k)) ∧ stackCells reached ≤ allowance start := by
  obtain ⟨reached, executed, rank, path, live⟩ := owned_prefix caller start n bound
  obtain ⟨registers, frame⟩ := prefix_frame caller start reached n bound executed
  refine ⟨reached, executed, rank, path, live, ?_, registers, frame,
    prefix_stackCells_le_dirty caller start n bound reached executed⟩
  intro zero
  subst n
  exact Option.some.inj executed.symm

end PhysicalSpace

end Resources.RotationCertificate.StreamMachine

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
  FrontEndMachine.Transport.stackCells frontEndStackEquiv frontEndSymbolEquiv data

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

-- BEGIN FINITE PACKAGE BASE PASSED2
namespace Resources.RotationCertificate.StreamMachine

variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
variable (caller : External Λ → Statement Γ Λ R)

/-! ## Actual finite package and certificate-only initialization

The designated output index is the existing fuel store. These carrier and
initializer equations make no output-word or halting claim.
-/

def initialRegisters (initial : R) : Registers R :=
  (none, ((none, (none, none)), initial))

@[simp] theorem resetAll_initialRegisters (initial : R) :
    resetAll (initialRegisters initial) = initialRegisters initial := rfl

section StreamFinitePackage

variable [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]

/-- The actual program and caller state are fixed before the certificate input.
The fuel word is designated k₁ without any Boolean output emission. -/
def machine (initial : R) : Turing.FinTM2 where
  K := StackId K
  k₀ := .inl .certificate
  k₁ := .inl .fuel
  Γ := alphabet Γ
  Λ := Label Λ
  main := phaseLabel inspectPhase
  σ := Registers R
  initialState := initialRegisters initial
  Γk₀Fin := alphabetFintype (.inl .certificate)
  m := program caller

@[instance_reducible]
def machineAlphabetFintype (initial : R) (k : (machine caller initial).K) :
    Fintype ((machine caller initial).Γ k) := alphabetFintype k

theorem machine_inputIndex (initial : R) :
    (machine caller initial).k₀ = Sum.inl LocalStack.certificate := rfl

theorem machine_outputIndex (initial : R) :
    (machine caller initial).k₁ = Sum.inl LocalStack.fuel := rfl

theorem machine_inputAlphabet (initial : R) :
    (machine caller initial).Γ (machine caller initial).k₀ = Tag := rfl

theorem machine_outputAlphabet (initial : R) :
    (machine caller initial).Γ (machine caller initial).k₁ = Bool := rfl

theorem machine_card_stackId (initial : R) :
    @Fintype.card (machine caller initial).K (machine caller initial).kFin =
      9 + Fintype.card K := card_stackId

theorem machine_card_label (initial : R) :
    @Fintype.card (machine caller initial).Λ (machine caller initial).ΛFin =
      41 + Fintype.card Λ := card_label

theorem machine_card_registers (initial : R) :
    @Fintype.card (machine caller initial).σ (machine caller initial).σFin =
      306 * Fintype.card R := card_registers

theorem machine_step_eq (initial : R) (c : Cfg Γ Λ R) :
    (machine caller initial).step c = step caller c := rfl

/-- Only the certificate is initialized with the supplied word. Every other
physical word, including the designated fuel/output word, is initially empty. -/
theorem initList_eq (initial : R) (raw : Word) :
    Turing.initList (machine caller initial) raw =
      cfg (some (phaseLabel inspectPhase)) (initialRegisters initial) { certificate := raw }
        (fun _ => []) := by
  apply cfg_ext
  · rfl
  · rfl
  · funext k
    cases k with
    | inl k => cases k <;> rfl
    | inr k => rfl

theorem initList_certificate (initial : R) (raw : Word) :
    (Turing.initList (machine caller initial) raw).stk (.inl .certificate) = raw := by
  rw [initList_eq]
  rfl

theorem initList_output_empty (initial : R) (raw : Word) :
    (Turing.initList (machine caller initial) raw).stk (machine caller initial).k₁ = [] := by
  rw [initList_eq]
  rfl

theorem initList_source_empty (initial : R) (raw : Word) :
    (Turing.initList (machine caller initial) raw).stk (.inl .source) = [] := by
  rw [initList_eq]
  rfl

theorem initList_target_empty (initial : R) (raw : Word) :
    (Turing.initList (machine caller initial) raw).stk (.inl .target) = [] := by
  rw [initList_eq]
  rfl

theorem initList_context_empty (initial : R) (raw : Word) (k : K) :
    (Turing.initList (machine caller initial) raw).stk (.inr k) = [] := by
  rw [initList_eq]
  rfl

end StreamFinitePackage

end Resources.RotationCertificate.StreamMachine

-- END FINITE PACKAGE BASE PASSED2

-- BEGIN INSTALLATION BASE PASSED2
namespace Resources.RotationCertificate.StreamMachine

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
variable (caller : External Λ → Statement Γ Λ R)
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

/-- Arbitrary iterations, including later Boolean/caller behaviour, require
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

end Resources.RotationCertificate.StreamMachine

-- END INSTALLATION BASE PASSED2

-- BEGIN PACKAGE EXECUTION PASSED3
namespace Resources.RotationCertificate.StreamMachine

variable {K Λ R : Type} {Γ : K → Type}

/-! ## The literal certificate-only initializer outcome

The four-step outcome is a live Boolean label. The input certificate remains
physical data, and the designated output/fuel word remains empty.
-/

theorem init_evaluate (raw : Word) :
    evaluate inspectPhase { certificate := raw } =
      ⟨raw.isEmpty, { certificate := raw }, 4⟩ := by
  cases raw with
  | nil =>
      rw [evaluate_inspect, evaluateInspect_nil _ rfl]
      rfl
  | cons tag raw =>
      rw [evaluate_inspect, evaluateInspect_nonempty _ (by simp)]
      rfl

theorem initClock_eq (raw : Word) : phaseSteps inspectPhase { certificate := raw } = 4 := by
  exact congrArg Evaluation.steps (init_evaluate raw)

theorem initResult_eq (raw : Word) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    phaseResult (Λ := Λ) inspectPhase regs { certificate := raw } ctx =
      cfg (some (resultLabel raw.isEmpty)) (resetAll regs) { certificate := raw } ctx := by
  simp only [phaseResult, init_evaluate, evaluationCfg]

variable [DecidableEq K]
variable (caller : External Λ → Statement Γ Λ R)

theorem init_input_firstRun (raw : Word) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    FirstRun caller (cfg (some (phaseLabel inspectPhase)) regs { certificate := raw } ctx)
      4 (cfg (some (resultLabel raw.isEmpty)) (resetAll regs) { certificate := raw } ctx) := by
  have actual := phase_firstRun caller inspectPhase { certificate := raw } regs ctx
  rw [initClock_eq, initResult_eq] at actual
  exact actual

section StreamPackageExecution

variable [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]

/-- The predicate uses the actual package step on the supplied installed cfg. -/
def machineFirstRun (initial : R) (start : Cfg Γ Λ R) (n : Nat) (finish : Cfg Γ Λ R) : Prop :=
  (fun c : Option (Cfg Γ Λ R) => c.bind (machine caller initial).step)^[n]
      (some start) = some finish ∧
    ¬ Owned finish.l ∧
    ∀ j, j < n → ∃ reached,
      (fun c : Option (Cfg Γ Λ R) => c.bind (machine caller initial).step)^[j]
        (some start) = some reached ∧ Owned reached.l

def machineFirstResult (initial : R) (start : Cfg Γ Λ R) (b : Bool) : Prop :=
  ∃ n finish, machineFirstRun caller initial start n finish ∧
    finish.l = some (resultLabel b)

theorem machine_phase_run (initial : R) (q : Phase) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (fun c : Option (Cfg Γ Λ R) => c.bind (machine caller initial).step)^[phaseSteps q D]
      (some (cfg (some (phaseLabel q)) regs D ctx)) = some (phaseResult q regs D ctx) :=
  phase_iterate caller q D regs ctx

theorem machine_cfg_run (initial : R) (start : Cfg Γ Λ R) :
    (fun c : Option (Cfg Γ Λ R) => c.bind (machine caller initial).step)^[remainingSteps start]
      (some start) = some (finalCfg start) := cfg_iterate caller start

theorem machine_phase_first_return (initial : R) (q : Phase) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    machineFirstRun caller initial (cfg (some (phaseLabel q)) regs D ctx)
      (phaseSteps q D) (phaseResult q regs D ctx) := phase_firstRun caller q D regs ctx

theorem machine_cfg_first_return (initial : R) (start : Cfg Γ Λ R) :
    machineFirstRun caller initial start (remainingSteps start) (finalCfg start) :=
  cfg_firstRun caller start

theorem machineFirstRun_iff (initial : R) (start finish : Cfg Γ Λ R) (n : Nat) :
    machineFirstRun caller initial start n finish ↔
      n = remainingSteps start ∧ finish = finalCfg start := firstRun_iff caller start finish n

theorem machineFirstResult_iff (initial : R) (start : Cfg Γ Λ R) (b : Bool) :
    machineFirstResult caller initial start b ↔ (finalCfg start).l = some (resultLabel b) :=
  firstResult_iff_finalCfg caller start b

theorem machine_owned_prefix (initial : R) (start : Cfg Γ Λ R) (n : Nat)
    (bound : n ≤ remainingSteps start) :
    ∃ reached,
      (fun c : Option (Cfg Γ Λ R) => c.bind (machine caller initial).step)^[n]
        (some start) = some reached ∧
      remainingSteps reached = remainingSteps start - n ∧
      Relation.ReflTransGen (LocalStep caller) start reached ∧
      (n < remainingSteps start ↔ Owned reached.l) := owned_prefix caller start n bound

def machinePhaseInTime (initial : R) (q : Phase) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (machine caller initial).step
      (cfg (some (phaseLabel q)) regs D ctx) (some (phaseResult q regs D ctx)) (phaseSteps q D) where
  steps := phaseSteps q D
  evals_in_steps := machine_phase_run caller initial q D regs ctx
  steps_le_m := Nat.le_refl _

@[simp] theorem machinePhaseInTime_steps (initial : R) (q : Phase) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (machinePhaseInTime caller initial q D regs ctx).steps = phaseSteps q D := rfl

def machineCfgInTime (initial : R) (start : Cfg Γ Λ R) :
    StateTransition.EvalsToInTime (machine caller initial).step start
      (some (finalCfg start)) (remainingSteps start) where
  steps := remainingSteps start
  evals_in_steps := machine_cfg_run caller initial start
  steps_le_m := Nat.le_refl _

@[simp] theorem machineCfgInTime_steps (initial : R) (start : Cfg Γ Λ R) :
    (machineCfgInTime caller initial start).steps = remainingSteps start := rfl

theorem machineCfgInTime_nonowned (initial : R) (start : Cfg Γ Λ R)
    (nonowned : ¬ Owned start.l) :
    (machineCfgInTime caller initial start).steps = 0 ∧ finalCfg start = start :=
  ⟨nonowned_remaining start nonowned, nonowned_finalCfg start nonowned⟩

def machinePrefixInTime (initial : R) (start reached : Cfg Γ Λ R) (n : Nat)
    (executed : (next caller)^[n] (some start) = some reached) :
    StateTransition.EvalsToInTime (machine caller initial).step start (some reached) n where
  steps := n
  evals_in_steps := executed
  steps_le_m := Nat.le_refl _

@[simp] theorem machinePrefixInTime_steps (initial : R) (start reached : Cfg Γ Λ R) (n : Nat)
    (executed : (next caller)^[n] (some start) = some reached) :
    (machinePrefixInTime caller initial start reached n executed).steps = n := rfl

theorem machine_init_run (initial : R) (raw : Word) :
    (fun c : Option (Cfg Γ Λ R) => c.bind (machine caller initial).step)^[4]
      (some (Turing.initList (machine caller initial) raw)) =
      some (cfg (some (resultLabel raw.isEmpty)) (initialRegisters initial)
        { certificate := raw } (fun _ => [])) := by
  rw [initList_eq]
  exact (init_input_firstRun caller raw (initialRegisters initial) (fun _ => [])).1

theorem machine_init_first_return (initial : R) (raw : Word) :
    machineFirstRun caller initial (Turing.initList (machine caller initial) raw) 4
      (cfg (some (resultLabel raw.isEmpty)) (initialRegisters initial)
        { certificate := raw } (fun _ => [])) := by
  rw [initList_eq]
  exact init_input_firstRun caller raw (initialRegisters initial) (fun _ => [])

theorem machine_init_exact_rank (initial : R) (raw : Word) :
    remainingSteps (Turing.initList (machine caller initial) raw) = 4 := by
  rw [initList_eq, remainingSteps_phase_cfg, initClock_eq]

theorem machine_init_finalCfg (initial : R) (raw : Word) :
    finalCfg (Turing.initList (machine caller initial) raw) =
      cfg (some (resultLabel raw.isEmpty)) (initialRegisters initial)
        { certificate := raw } (fun _ => []) := by
  rw [initList_eq, finalCfg_phase_cfg, initResult_eq, resetAll_initialRegisters]

def machineInitInTimeExact (initial : R) (raw : Word) :
    StateTransition.EvalsToInTime (machine caller initial).step
      (Turing.initList (machine caller initial) raw)
      (some (cfg (some (resultLabel raw.isEmpty)) (initialRegisters initial)
        { certificate := raw } (fun _ => []))) 4 where
  steps := 4
  evals_in_steps := machine_init_run caller initial raw
  steps_le_m := Nat.le_refl _

@[simp] theorem machineInitInTimeExact_steps (initial : R) (raw : Word) :
    (machineInitInTimeExact caller initial raw).steps = 4 := rfl

theorem machine_init_true (initial : R) :
    machineFirstResult caller initial (Turing.initList (machine caller initial) ([] : Word)) true := by
  exact ⟨4, _, machine_init_first_return caller initial ([] : Word), rfl⟩

theorem machine_init_nonempty_false (initial : R) (tag : Tag) (raw : Word) :
    machineFirstResult caller initial (Turing.initList (machine caller initial) (tag :: raw)) false := by
  exact ⟨4, _, machine_init_first_return caller initial (tag :: raw), rfl⟩

theorem machine_init_endpoint_live (initial : R) (raw : Word) :
    (finalCfg (Turing.initList (machine caller initial) raw)).l = some (resultLabel raw.isEmpty) := by
  rw [machine_init_finalCfg]
  rfl

theorem machine_init_endpoint_not_halt (initial : R) (raw : Word) :
    (finalCfg (Turing.initList (machine caller initial) raw)).l ≠ none := by
  rw [machine_init_endpoint_live]
  exact Option.some_ne_none _

theorem machine_init_final_output_empty (initial : R) (raw : Word) :
    (finalCfg (Turing.initList (machine caller initial) raw)).stk (machine caller initial).k₁ = [] := by
  rw [machine_init_finalCfg]
  rfl

theorem machine_init_final_certificate (initial : R) (raw : Word) :
    (finalCfg (Turing.initList (machine caller initial) raw)).stk (.inl .certificate) = raw := by
  rw [machine_init_finalCfg]
  rfl

end StreamPackageExecution

end Resources.RotationCertificate.StreamMachine

-- END PACKAGE EXECUTION PASSED3

-- BEGIN INSTALLATION CANONICAL PASSED3
namespace Resources.RotationCertificate.StreamMachine

variable {K Λ R K' Λ' R' : Type} {Γ : K → Type} {Γ' : K' → Type}
variable (names : StackId K ≃ K') (symbols : ∀ k, alphabet Γ k ≃ Γ' (names k))
  (registers : Registers R ≃ R') (labels : Label Λ ≃ Λ')

def installedOwned (label : Option Λ') : Prop := Owned (label.map labels.symm)

@[simp] theorem installedCfg_owned_iff (c : Cfg Γ Λ R) :
    installedOwned labels (installedCfg names symbols registers labels c).l ↔ Owned c.l := by
  cases label : c.l <;> simp [installedOwned, installedCfg, FrontEndMachine.Transport.cfg, label]

variable [DecidableEq K] [DecidableEq K']
variable (caller : External Λ → Statement Γ Λ R)
variable (ambient : Λ' → Turing.TM2.Stmt Γ' Λ' R')

def installedFirstRun (start : Turing.TM2.Cfg Γ' Λ' R') (n : Nat)
    (finish : Turing.TM2.Cfg Γ' Λ' R') : Prop :=
  (FrontEndMachine.Transport.next ambient)^[n] (some start) = some finish ∧
    ¬ installedOwned labels finish.l ∧
    ∀ j, j < n → ∃ reached,
      (FrontEndMachine.Transport.next ambient)^[j] (some start) = some reached ∧
        installedOwned labels reached.l

/-- Only the 39 owned bodies, including all eight paid joins, are installed. -/
theorem installed_owned_prefix
    (installed : ∀ label, Owned (some label) →
      ambient (labels label) =
        FrontEndMachine.Transport.statement names symbols registers labels (program caller label))
    (start : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start) :
    (FrontEndMachine.Transport.next ambient)^[n]
      (some (installedCfg names symbols registers labels start)) =
      ((next caller)^[n] (some start)).map (installedCfg names symbols registers labels) := by
  apply installed_prefix_of_owned names symbols registers labels caller ambient installed n start
  intro j strict
  obtain ⟨reached, executed, _, _, ownership⟩ := owned_prefix caller start j (by omega)
  exact ⟨reached, executed, ownership.mp (by omega)⟩

theorem installed_owned_firstRun
    (installed : ∀ label, Owned (some label) →
      ambient (labels label) =
        FrontEndMachine.Transport.statement names symbols registers labels (program caller label))
    (start : Cfg Γ Λ R) :
    installedFirstRun labels ambient (installedCfg names symbols registers labels start)
      (remainingSteps start) (installedCfg names symbols registers labels (finalCfg start)) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [installed_owned_prefix names symbols registers labels caller ambient installed start
      (remainingSteps start) (Nat.le_refl _), cfg_iterate caller start]
    rfl
  · rw [installedCfg_owned_iff]
    exact finalCfg_not_owned start
  · intro j strict
    obtain ⟨before, run, _, _, ownership⟩ := owned_prefix caller start j (by omega)
    refine ⟨installedCfg names symbols registers labels before, ?_, ?_⟩
    · rw [installed_owned_prefix names symbols registers labels caller ambient installed start j
        (by omega), run]
      rfl
    · rw [installedCfg_owned_iff]
      exact ownership.mp strict

/-- A later caller result cannot count as the first return. This converse uses
the actual strict-earlier ownership witnesses in the candidate run. -/
theorem installed_firstRun_iff
    (installed : ∀ label, Owned (some label) →
      ambient (labels label) =
        FrontEndMachine.Transport.statement names symbols registers labels (program caller label))
    (start : Cfg Γ Λ R) (n : Nat) (finish : Turing.TM2.Cfg Γ' Λ' R') :
    installedFirstRun labels ambient (installedCfg names symbols registers labels start) n finish ↔
      n = remainingSteps start ∧
        finish = installedCfg names symbols registers labels (finalCfg start) := by
  have canonical := installed_owned_firstRun names symbols registers labels caller ambient installed start
  constructor
  · rintro ⟨run, returned, earlier⟩
    have count : n = remainingSteps start := by
      rcases lt_trichotomy n (remainingSteps start) with less | equal | greater
      · obtain ⟨middle, prefixRun, owned⟩ := canonical.2.2 n less
        have same : finish = middle := Option.some.inj (run.symm.trans prefixRun)
        exact False.elim (returned (same.symm ▸ owned))
      · exact equal
      · obtain ⟨middle, prefixRun, owned⟩ := earlier (remainingSteps start) greater
        have same : middle = installedCfg names symbols registers labels (finalCfg start) :=
          Option.some.inj (prefixRun.symm.trans canonical.1)
        exact False.elim (canonical.2.1 (same ▸ owned))
    rw [count] at run
    exact ⟨count, Option.some.inj (run.symm.trans canonical.1)⟩
  · rintro ⟨rfl, rfl⟩
    exact canonical

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
  evals_in_steps :=
    (installed_owned_firstRun names symbols registers labels caller ambient installed start).1
  steps_le_m := Nat.le_refl _

@[simp] theorem installed_owned_timed_steps
    (installed : ∀ label, Owned (some label) →
      ambient (labels label) =
        FrontEndMachine.Transport.statement names symbols registers labels (program caller label))
    (start : Cfg Γ Λ R) :
    (installed_owned_timed names symbols registers labels caller ambient installed start).steps =
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
    rw [installed_owned_prefix names symbols registers labels caller ambient installed start n bound,
      executed]
    rfl
  steps_le_m := Nat.le_refl _

@[simp] theorem installed_owned_prefix_timed_steps
    (installed : ∀ label, Owned (some label) →
      ambient (labels label) =
        FrontEndMachine.Transport.statement names symbols registers labels (program caller label))
    (start : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start)
    (reached : Cfg Γ Λ R) (executed : (next caller)^[n] (some start) = some reached) :
    (installed_owned_prefix_timed names symbols registers labels caller ambient installed start n
      bound reached executed).steps = n := rfl

/-- Pull an actual source prefix bound through the complete physical map for
the same supplied ambient endpoint. No external store is omitted. -/
theorem installed_prefix_cells_of_source_bound [Fintype K] [Fintype K']
    (installed : ∀ label, Owned (some label) →
      ambient (labels label) =
        FrontEndMachine.Transport.statement names symbols registers labels (program caller label))
    (start : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start) (budget : Nat)
    (estimate : ∀ before, (next caller)^[n] (some start) = some before →
      ∑ k, (before.stk k).length ≤ budget)
    (reached : Turing.TM2.Cfg Γ' Λ' R')
    (executed : (FrontEndMachine.Transport.next ambient)^[n]
      (some (installedCfg names symbols registers labels start)) = some reached) :
    ∑ k, (reached.stk k).length ≤ budget := by
  obtain ⟨before, run, _, _, _⟩ := owned_prefix caller start n bound
  have mapped := installed_owned_prefix names symbols registers labels caller ambient installed start n bound
  rw [run, Option.map_some, executed] at mapped
  have same := Option.some.inj mapped
  rw [same, installed_stack_cells]
  exact estimate before run

end Resources.RotationCertificate.StreamMachine

-- END INSTALLATION CANONICAL PASSED3

-- BEGIN INITIALIZER PREFIX PASSED3
namespace Resources.RotationCertificate.StreamMachine

variable {K Λ R : Type} {Γ : K → Type}

/-- These five proof-side labels record only the genuine four-step initializer
path. They are not callbacks in the finite runtime program. -/
def initPrefixLabel (raw : Word) : Nat → Label Λ
  | 0 => phaseLabel inspectPhase
  | 1 => if raw.isEmpty then phaseLabel (fuelJoinPhase .atEnd) else phaseLabel (counterPhase .borrow)
  | 2 => if raw.isEmpty then phaseLabel comparePhase else phaseLabel (counterPhase .restoreFalse)
  | 3 => if raw.isEmpty then phaseLabel (equalityJoinPhase .equal) else phaseLabel (fuelJoinPhase .zero)
  | _ => resultLabel raw.isEmpty

def initPrefixCfg (initial : R) (raw : Word) (ctx : ∀ k, List (Γ k)) (n : Nat) : Cfg Γ Λ R :=
  cfg (some (initPrefixLabel raw n)) (initialRegisters initial) { certificate := raw } ctx

theorem initPrefix_data (initial : R) (raw : Word) (ctx : ∀ k, List (Γ k)) (n : Nat) :
    dataOfCfg (initPrefixCfg (Λ := Λ) initial raw ctx n) = { certificate := raw } := rfl

theorem initPrefix_registers (initial : R) (raw : Word) (ctx : ∀ k, List (Γ k)) (n : Nat) :
    (initPrefixCfg (Λ := Λ) initial raw ctx n).var = initialRegisters initial := rfl

theorem initPrefix_context (initial : R) (raw : Word) (ctx : ∀ k, List (Γ k)) (n : Nat) :
    contextOfCfg (initPrefixCfg (Λ := Λ) initial raw ctx n) = ctx := rfl

theorem initPrefix_owned_iff (initial : R) (raw : Word) (ctx : ∀ k, List (Γ k))
    (n : Nat) (bound : n ≤ 4) :
    Owned (initPrefixCfg (Λ := Λ) initial raw ctx n).l ↔ n < 4 := by
  have possibilities : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 := by omega
  rcases possibilities with rfl | rfl | rfl | rfl | rfl
  all_goals cases raw <;> simp [initPrefixCfg, initPrefixLabel, cfg]

theorem initPrefix_cells [Fintype K] (initial : R) (raw : Word)
    (ctx : ∀ k, List (Γ k)) (n : Nat) :
    ∑ k, ((initPrefixCfg (Λ := Λ) initial raw ctx n).stk k).length =
      raw.length + ∑ k, (ctx k).length := by
  rw [Fintype.sum_sum_type]
  change (∑ k ∈ ({.certificate, .moveReverse, .path, .source, .saved, .scratch,
      .units, .fuel, .target} : Finset LocalStack),
      ((initPrefixCfg (Λ := Λ) initial raw ctx n).stk (.inl k)).length) +
      (∑ k, (ctx k).length) = _
  simp [initPrefixCfg, cfg]

variable [DecidableEq K]
variable (caller : External Λ → Statement Γ Λ R)

theorem init_borrow_step (initial : R) (raw : Word) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel (counterPhase .borrow))) (initialRegisters initial)
      { certificate := raw } ctx) =
      some (cfg (some (phaseLabel (counterPhase .restoreFalse))) (initialRegisters initial)
        { certificate := raw } ctx) := by
  let D : LocalData := { certificate := raw }
  let localCaller : (FuelDispatchMachine.Exit ⊕ FuelCallerLabel Λ) → FuelStatement Γ Λ R := fun _ => .halt
  have component := Resources.BinaryCounter.FixedWidthMachine.borrow_step_nil
    (FuelDispatchMachine.callerHandler localCaller) (initialRegisters initial) []
    (FuelDispatchMachine.stores raw (fuelContext D ctx))
  have actual := counter_step_of_step caller localCaller .borrow D (initialRegisters initial) ctx
    (some (Resources.BinaryCounter.FixedWidthMachine.phaseLabel .restoreFalse))
    (initialRegisters initial) [] [] component
  simpa only [Option.map_some, fuelLabelEquiv_counter] using actual

theorem init_restoreFalse_step (initial : R) (raw : Word) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel (counterPhase .restoreFalse))) (initialRegisters initial)
      { certificate := raw } ctx) =
      some (cfg (some (phaseLabel (fuelJoinPhase .zero))) (initialRegisters initial)
        { certificate := raw } ctx) := by
  let D : LocalData := { certificate := raw }
  let localCaller : (FuelDispatchMachine.Exit ⊕ FuelCallerLabel Λ) → FuelStatement Γ Λ R := fun _ => .halt
  have component := Resources.BinaryCounter.FixedWidthMachine.restoreFalse_step_nil
    (FuelDispatchMachine.callerHandler localCaller) [] (initialRegisters initial)
    (FuelDispatchMachine.stores raw (fuelContext D ctx))
  have actual := counter_step_of_step caller localCaller .restoreFalse D (initialRegisters initial) ctx
    (some (Resources.BinaryCounter.FixedWidthMachine.resultLabel .zero))
    (initialRegisters initial) [] [] component
  have labelEq : fuelLabelEquiv (Λ := Λ) (Resources.BinaryCounter.FixedWidthMachine.resultLabel .zero) =
      phaseLabel (fuelJoinPhase .zero) := fuelLabelEquiv_exit .zero
  simpa only [Option.map_some, labelEq, D] using actual

theorem init_compare_step (initial : R) (raw : Word) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel comparePhase)) (initialRegisters initial)
      { certificate := raw } ctx) =
      some (cfg (some (phaseLabel (equalityJoinPhase .equal))) (initialRegisters initial)
        { certificate := raw } ctx) := by
  let D : LocalData := { certificate := raw }
  let localCaller : TreeEqualityMachine.External (EqualityCallerLabel Λ) → EqualityStatement Γ Λ R :=
    fun _ => .halt
  have component := TreeEqualityMachine.compare_step_nil_nil localCaller
    (equalityRegisterEquiv.symm (initialRegisters initial)) (equalityContext D ctx)
  have actual := equality_step_of_step caller localCaller D (initialRegisters initial) ctx
    (some (TreeEqualityMachine.resultLabel .equal))
    (TreeEqualityMachine.reset (equalityRegisterEquiv.symm (initialRegisters initial))) [] [] component
  simpa only [Option.map_some, equalityLabelEquiv_result, equalityRegisterEquiv_reset,
    Equiv.apply_symm_apply, D, resetEquality, initialRegisters] using actual

theorem initPrefix_step (initial : R) (raw : Word) (ctx : ∀ k, List (Γ k))
    (n : Nat) (strict : n < 4) :
    step caller (initPrefixCfg initial raw ctx n) = some (initPrefixCfg initial raw ctx (n + 1)) := by
  have possibilities : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
  rcases possibilities with rfl | rfl | rfl | rfl
  · cases raw with
    | nil => exact inspect_step_nil caller { certificate := [] } rfl (initialRegisters initial) ctx
    | cons tag raw =>
        exact inspect_step_cons caller { certificate := tag :: raw }
          tag raw rfl (initialRegisters initial) ctx
  · cases raw with
    | nil => exact fuel_join_step caller .atEnd { certificate := [] } (initialRegisters initial) ctx
    | cons tag raw => exact init_borrow_step caller initial (tag :: raw) ctx
  · cases raw with
    | nil => exact init_compare_step caller initial [] ctx
    | cons tag raw => exact init_restoreFalse_step caller initial (tag :: raw) ctx
  · cases raw with
    | nil => exact equality_join_step caller .equal { certificate := [] } (initialRegisters initial) ctx
    | cons tag raw =>
        exact fuel_join_step caller .zero { certificate := tag :: raw }
          (initialRegisters initial) ctx

theorem initPrefix_iterate (initial : R) (raw : Word) (ctx : ∀ k, List (Γ k))
    (n : Nat) (bound : n ≤ 4) :
    (next caller)^[n] (some (cfg (some (phaseLabel inspectPhase)) (initialRegisters initial)
      { certificate := raw } ctx)) = some (initPrefixCfg initial raw ctx n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih (by omega), next_some,
        initPrefix_step caller initial raw ctx n (by omega)]

/-- The inclusive prefix's exact cells, complete data and ownership describe
the same supplied reached configuration. -/
theorem initPrefix_exact [Fintype K] (initial : R) (raw : Word) (ctx : ∀ k, List (Γ k))
    (n : Nat) (bound : n ≤ 4) (reached : Cfg Γ Λ R)
    (executed : (next caller)^[n]
      (some (cfg (some (phaseLabel inspectPhase)) (initialRegisters initial)
        { certificate := raw } ctx)) = some reached) :
    reached = initPrefixCfg initial raw ctx n ∧
      dataOfCfg reached = { certificate := raw } ∧
      reached.var = initialRegisters initial ∧ contextOfCfg reached = ctx ∧
      (Owned reached.l ↔ n < 4) ∧
      (∑ k, (reached.stk k).length) = raw.length + ∑ k, (ctx k).length := by
  have same : reached = initPrefixCfg initial raw ctx n :=
    Option.some.inj (executed.symm.trans (initPrefix_iterate caller initial raw ctx n bound))
  subst reached
  exact ⟨rfl, rfl, rfl, rfl, initPrefix_owned_iff initial raw ctx n bound,
    initPrefix_cells initial raw ctx n⟩

section StreamInitializerPrefixPackage

variable [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]

theorem machine_init_prefix (initial : R) (raw : Word) (n : Nat) (bound : n ≤ 4) :
    (fun c : Option (Cfg Γ Λ R) => c.bind (machine caller initial).step)^[n]
      (some (Turing.initList (machine caller initial) raw)) =
      some (initPrefixCfg initial raw (fun _ => []) n) := by
  rw [initList_eq]
  exact initPrefix_iterate caller initial raw (fun _ => []) n bound

theorem machine_init_prefix_cells (initial : R) (raw : Word) (n : Nat) (bound : n ≤ 4)
    (reached : Cfg Γ Λ R)
    (executed : (fun c : Option (Cfg Γ Λ R) => c.bind (machine caller initial).step)^[n]
      (some (Turing.initList (machine caller initial) raw)) = some reached) :
    (∑ k, (reached.stk k).length) = raw.length := by
  have same : reached = initPrefixCfg initial raw (fun _ => []) n :=
    Option.some.inj (executed.symm.trans (machine_init_prefix caller initial raw n bound))
  rw [same, initPrefix_cells]
  simp

theorem machine_init_exact_peak (initial : R) (raw : Word) :
    (∀ n, n ≤ 4 → ∀ reached : Cfg Γ Λ R,
      (fun c : Option (Cfg Γ Λ R) => c.bind (machine caller initial).step)^[n]
        (some (Turing.initList (machine caller initial) raw)) = some reached →
      (∑ k, (reached.stk k).length) ≤ raw.length) ∧
    ∃ n reached, n ≤ 4 ∧
      (fun c : Option (Cfg Γ Λ R) => c.bind (machine caller initial).step)^[n]
        (some (Turing.initList (machine caller initial) raw)) = some reached ∧
      (∑ k, (reached.stk k).length) = raw.length := by
  constructor
  · intro n bound reached executed
    exact Nat.le_of_eq (machine_init_prefix_cells caller initial raw n bound reached executed)
  · refine ⟨0, Turing.initList (machine caller initial) raw, by omega, rfl, ?_⟩
    exact machine_init_prefix_cells caller initial raw 0 (by omega) _ rfl

end StreamInitializerPrefixPackage

end Resources.RotationCertificate.StreamMachine

-- END INITIALIZER PREFIX PASSED3

-- BEGIN STAGED REGISTERS PASSED2
namespace Resources.RotationCertificate.StreamMachine

variable {K Λ R : Type} {Γ : K → Type}

/-! ## The first paid outer join and staged temporary registers -/

/-- The first *outer* join includes the whole initial component and its paid
one-tick join. A component result label is still owned before this tick. -/
def firstJoinSteps (q : Phase) (D : LocalData) : Nat :=
  match q with
  | .inl (.inl q) => (counterFinish q D).steps + 1
  | .inl (.inr (.inl _)) => 1
  | .inl (.inr (.inr (.inl .inspectCertificate))) => (inspectStageFinish D).steps + 1
  | .inl (.inr (.inr (.inl .atEnd))) => 1
  | .inl (.inr (.inr (.inr impossible))) => Empty.elim impossible
  | .inr (.inl (.inl q)) => (applyFinish (MoveApplyMachine.movePhase q) D).steps + 1
  | .inr (.inl (.inr (.inl r))) => (applyFinish (MoveApplyMachine.dispatchPhase r) D).steps + 1
  | .inr (.inl (.inr (.inr (.inl q)))) => (applyFinish (MoveApplyMachine.positionPhase q) D).steps + 1
  | .inr (.inl (.inr (.inr (.inr (.inl _))))) => 1
  | .inr (.inl (.inr (.inr (.inr (.inr impossible))))) => Empty.elim impossible
  | .inr (.inr (.inl .compare)) => (equalityFinish D).steps + 1
  | .inr (.inr (.inr (.inl _))) => 1
  | .inr (.inr (.inr (.inr impossible))) => Empty.elim impossible

def firstJoinCfg (q : Phase) (regs : Registers R) (D : LocalData)
    (ctx : ∀ k, List (Γ k)) : Cfg Γ Λ R :=
  match q with
  | .inl (.inl q) =>
      cfg (some (fuelJoinTarget (FuelDispatchMachine.exitOfResult (counterFinish q D).result)))
        (resetAll regs) (counterFinish q D).data ctx
  | .inl (.inr (.inl r)) => cfg (some (fuelJoinTarget (FuelDispatchMachine.exitOfResult r))) (resetAll regs) D ctx
  | .inl (.inr (.inr (.inl .inspectCertificate))) =>
      cfg (some (fuelJoinTarget (inspectStageFinish D).result)) (resetAll regs) (inspectStageFinish D).data ctx
  | .inl (.inr (.inr (.inl .atEnd))) => cfg (some (fuelJoinTarget .atEnd)) (resetAll regs) D ctx
  | .inl (.inr (.inr (.inr impossible))) => Empty.elim impossible
  | .inr (.inl (.inl q)) =>
      cfg (some (applyJoinTarget (applyFinish (MoveApplyMachine.movePhase q) D).result))
        (resetAll regs) (applyFinish (MoveApplyMachine.movePhase q) D).data ctx
  | .inr (.inl (.inr (.inl r))) =>
      cfg (some (applyJoinTarget (applyFinish (MoveApplyMachine.dispatchPhase r) D).result))
        (resetAll regs) (applyFinish (MoveApplyMachine.dispatchPhase r) D).data ctx
  | .inr (.inl (.inr (.inr (.inl q)))) =>
      cfg (some (applyJoinTarget (applyFinish (MoveApplyMachine.positionPhase q) D).result))
        (resetAll regs) (applyFinish (MoveApplyMachine.positionPhase q) D).data ctx
  | .inr (.inl (.inr (.inr (.inr (.inl r))))) => cfg (some (applyJoinTarget r)) (resetAll regs) D ctx
  | .inr (.inl (.inr (.inr (.inr (.inr impossible))))) => Empty.elim impossible
  | .inr (.inr (.inl .compare)) =>
      cfg (some (equalityJoinTarget (equalityFinish D).result)) (resetAll regs) (equalityFinish D).data ctx
  | .inr (.inr (.inr (.inl r))) => cfg (some (equalityJoinTarget r)) (resetAll regs) D ctx
  | .inr (.inr (.inr (.inr impossible))) => Empty.elim impossible

@[simp] theorem firstJoinSteps_counter (q : Resources.BinaryCounter.FixedWidthMachine.Phase) (D : LocalData) :
    firstJoinSteps (counterPhase q) D = Resources.BinaryCounter.FixedWidthMachine.phaseSteps q D.fuel D.units + 1 := by
  exact congrArg (fun n => n + 1) (counterFinish_steps q D)

@[simp] theorem firstJoinSteps_apply (q : MoveApplyMachine.Phase) (D : LocalData) :
    firstJoinSteps (applyPhase q) D = MoveApplyMachine.phaseSteps q (applyData D) + 1 := by
  rcases q with q | (r | q) <;> rfl

@[simp] theorem firstJoinSteps_compare (D : LocalData) :
    firstJoinSteps comparePhase D = TreeEqualityMachine.runSteps D.source D.target + 1 := rfl

@[simp] theorem firstJoinSteps_fuel_join (r : FuelDispatchMachine.Exit) (D : LocalData) :
    firstJoinSteps (fuelJoinPhase r) D = 1 := by cases r <;> rfl

@[simp] theorem firstJoinSteps_apply_join (r : MoveApplyMachine.FinalResult) (D : LocalData) :
    firstJoinSteps (applyJoinPhase r) D = 1 := rfl

@[simp] theorem firstJoinSteps_equality_join (r : TreeEqualityMachine.Result) (D : LocalData) :
    firstJoinSteps (equalityJoinPhase r) D = 1 := rfl

theorem firstJoinSteps_inspect_nil (D : LocalData) (empty : D.certificate = []) :
    firstJoinSteps inspectPhase D = 2 := by
  change (inspectStageFinish D).steps + 1 = 2
  simp only [inspectStageFinish, empty]

theorem firstJoinSteps_inspect_cons (D : LocalData) (tag : Tag) (raw : Word)
    (nonempty : D.certificate = tag :: raw) :
    firstJoinSteps inspectPhase D = Resources.BinaryCounter.FixedWidthMachine.runSteps D.fuel + D.units.length + 2 := by
  change (inspectStageFinish D).steps + 1 = _
  simp only [inspectStageFinish, nonempty, counterFinish]
  omega

theorem firstJoinCfg_var (q : Phase) (regs : Registers R) (D : LocalData)
    (ctx : ∀ k, List (Γ k)) : (firstJoinCfg (Λ := Λ) q regs D ctx).var = resetAll regs := by
  rcases q with fuel | (applied | equality)
  · rcases fuel with q | (r | (d | impossible))
    · rfl
    · rfl
    · cases d <;> rfl
    · exact Empty.elim impossible
  · rcases applied with q | (r | (q | (r | impossible))) <;> try rfl
    exact Empty.elim impossible
  · rcases equality with q | (r | impossible)
    · cases q; rfl
    · rfl
    · exact Empty.elim impossible

variable [DecidableEq K]
variable (caller : External Λ → Statement Γ Λ R)

theorem firstJoin_localRun (q : Phase) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (firstJoinSteps q D) (cfg (some (phaseLabel q)) regs D ctx)
      (firstJoinCfg q regs D ctx) := by
  have counter (q : Resources.BinaryCounter.FixedWidthMachine.Phase) :
      LocalRun caller ((counterFinish q D).steps + 1)
        (cfg (some (phaseLabel (counterPhase q))) regs D ctx)
        (cfg (some (fuelJoinTarget (FuelDispatchMachine.exitOfResult (counterFinish q D).result)))
          (resetAll regs) (counterFinish q D).data ctx) := by
    simpa only [resetAll_resetFuel] using LocalRun.trans caller
      (counter_phase_localRun caller q D regs ctx)
      (fuel_join_localRun caller (FuelDispatchMachine.exitOfResult (counterFinish q D).result)
        (counterFinish q D).data (resetFuel regs) ctx)
  have applied (q : MoveApplyMachine.Phase) :
      LocalRun caller ((applyFinish q D).steps + 1)
        (cfg (some (phaseLabel (applyPhase q))) regs D ctx)
        (cfg (some (applyJoinTarget (applyFinish q D).result)) (resetAll regs) (applyFinish q D).data ctx) := by
    simpa only [resetAll_resetApply] using LocalRun.trans caller
      (apply_phase_localRun caller q D regs ctx)
      (apply_join_localRun caller (applyFinish q D).result (applyFinish q D).data (resetApply regs) ctx)
  rcases q with fuel | (application | equality)
  · rcases fuel with q | (r | (d | impossible))
    · exact counter q
    · cases r with
      | positive => exact fuel_join_localRun caller .positive D regs ctx
      | zero => exact fuel_join_localRun caller .zero D regs ctx
    · cases d with
      | inspectCertificate =>
          change LocalRun caller ((inspectStageFinish D).steps + 1)
            (cfg (some (phaseLabel inspectPhase)) regs D ctx)
            (cfg (some (fuelJoinTarget (inspectStageFinish D).result))
              (resetAll regs) (inspectStageFinish D).data ctx)
          simpa only [resetAll_resetFuel] using LocalRun.trans caller
            (inspect_stage_localRun caller D regs ctx)
            (fuel_join_localRun caller (inspectStageFinish D).result (inspectStageFinish D).data (resetFuel regs) ctx)
      | atEnd => exact fuel_join_localRun caller .atEnd D regs ctx
    · exact Empty.elim impossible
  · rcases application with q | (r | (q | (r | impossible)))
    · exact applied (MoveApplyMachine.movePhase q)
    · exact applied (MoveApplyMachine.dispatchPhase r)
    · exact applied (MoveApplyMachine.positionPhase q)
    · exact apply_join_localRun caller r D regs ctx
    · exact Empty.elim impossible
  · rcases equality with q | (r | impossible)
    · cases q
      change LocalRun caller ((equalityFinish D).steps + 1)
        (cfg (some (phaseLabel comparePhase)) regs D ctx)
        (cfg (some (equalityJoinTarget (equalityFinish D).result))
          (resetAll regs) (equalityFinish D).data ctx)
      simpa only [resetAll_resetEquality] using LocalRun.trans caller
        (equality_phase_localRun caller D regs ctx)
        (equality_join_localRun caller (equalityFinish D).result (equalityFinish D).data (resetEquality regs) ctx)
    · exact equality_join_localRun caller r D regs ctx
    · exact Empty.elim impossible

omit [DecidableEq K] in
theorem firstJoinSteps_le_phaseSteps (q : Phase) (D : LocalData) : firstJoinSteps q D ≤ phaseSteps q D := by
  let localCaller : External Empty → Statement (fun _ : Empty => Empty) Empty Unit := fun _ => .halt
  let regs : Registers Unit := (none, ((none, (none, none)), ()))
  have rank := LocalRun.remaining localCaller (firstJoin_localRun localCaller q D regs (fun k : Empty => Empty.elim k))
  rw [remainingSteps_phase_cfg] at rank
  omega

theorem prefix_reset_after_firstJoin (q : Phase) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (n : Nat) (reached : Cfg Γ Λ R)
    (afterJoin : firstJoinSteps q D ≤ n) (bound : n ≤ phaseSteps q D)
    (executed : (next caller)^[n] (some (cfg (some (phaseLabel q)) regs D ctx)) = some reached) :
    reached.var = resetAll regs := by
  have segment := firstJoin_localRun caller q D regs ctx
  have rank := LocalRun.remaining caller segment
  rw [remainingSteps_phase_cfg] at rank
  have count : firstJoinSteps q D + (n - firstJoinSteps q D) = n := by omega
  have rest : (next caller)^[n - firstJoinSteps q D] (some (firstJoinCfg q regs D ctx)) = some reached := by
    rw [← prefix_iterate_after_localRun caller segment, count]
    exact executed
  have clean : resetAll (firstJoinCfg (Λ := Λ) q regs D ctx).var = (firstJoinCfg (Λ := Λ) q regs D ctx).var := by
    rw [firstJoinCfg_var, resetAll_resetAll]
  have registers := prefix_resetAll caller (firstJoinCfg q regs D ctx) reached
    (n - firstJoinSteps q D) (by omega) rest clean
  rwa [firstJoinCfg_var] at registers

theorem fuel_prefix_reset
    (localCaller : (FuelDispatchMachine.Exit ⊕ FuelCallerLabel Λ) → FuelStatement Γ Λ R)
    (start : FuelCfg Γ Λ R) (n : Nat) (positive : 0 < n)
    (bound : n ≤ FuelDispatchMachine.remainingSteps start) (reached : Cfg Γ Λ R)
    (executed : (next caller)^[n] (some (fuelCfg start)) = some reached) :
    reached.var = resetFuel start.var := by
  obtain ⟨middle, run, path, rfl⟩ := fuel_prefix_lift caller localCaller start n bound reached executed
  have cleared := FuelDispatchMachine.prefix_local_register localCaller n start middle bound run positive
  have kept := (fuel_local_reaches_frame localCaller path).1
  change middle.var = (none, start.var.2)
  exact Prod.ext cleared kept

theorem counter_stage_prefix_reset (q : Resources.BinaryCounter.FixedWidthMachine.Phase) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) (n : Nat) (reached : Cfg Γ Λ R)
    (positive : 0 < n) (bound : n ≤ (counterFinish q D).steps)
    (executed : (next caller)^[n] (some (cfg (some (phaseLabel (counterPhase q))) regs D ctx)) = some reached) :
    reached.var = resetFuel regs := by
  let localCaller : (FuelDispatchMachine.Exit ⊕ FuelCallerLabel Λ) → FuelStatement Γ Λ R := fun _ => .halt
  let start : FuelCfg Γ Λ R := fuelView (some (Resources.BinaryCounter.FixedWidthMachine.phaseLabel q)) regs D ctx
  have startEq : fuelCfg start = cfg (some (phaseLabel (counterPhase q))) regs D ctx := by
    rw [fuelCfg_view]
    rfl
  have rank : FuelDispatchMachine.remainingSteps start = (counterFinish q D).steps := by cases q <;> rfl
  exact fuel_prefix_reset caller localCaller start n positive (by rwa [rank]) reached (by rwa [startEq])

theorem inspect_stage_prefix_reset (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (n : Nat) (reached : Cfg Γ Λ R) (positive : 0 < n) (bound : n ≤ (inspectStageFinish D).steps)
    (executed : (next caller)^[n] (some (cfg (some (phaseLabel inspectPhase)) regs D ctx)) = some reached) :
    reached.var = resetFuel regs := by
  let localCaller : (FuelDispatchMachine.Exit ⊕ FuelCallerLabel Λ) → FuelStatement Γ Λ R := fun _ => .halt
  let start : FuelCfg Γ Λ R := fuelView (some FuelDispatchMachine.inspectLabel) regs D ctx
  have startEq : fuelCfg start = cfg (some (phaseLabel inspectPhase)) regs D ctx := by
    rw [fuelCfg_view]
    rfl
  have rank : FuelDispatchMachine.remainingSteps start = (inspectStageFinish D).steps := by
    cases cert : D.certificate with
    | nil => simp only [start, fuelView, FuelDispatchMachine.remainingSteps, FuelDispatchMachine.cfg,
        Resources.BinaryCounter.FixedWidthMachine.cfg, FuelDispatchMachine.inspectLabel,
        Resources.BinaryCounter.FixedWidthMachine.callerLabel, FuelDispatchMachine.stores,
        cert, inspectStageFinish]
    | cons tag raw =>
        simp only [start, fuelView, FuelDispatchMachine.remainingSteps, FuelDispatchMachine.cfg,
          Resources.BinaryCounter.FixedWidthMachine.cfg, FuelDispatchMachine.inspectLabel,
          Resources.BinaryCounter.FixedWidthMachine.callerLabel, FuelDispatchMachine.stores,
          cert, inspectStageFinish, counterFinish]
        omega
  exact fuel_prefix_reset caller localCaller start n positive (by rwa [rank]) reached (by rwa [startEq])

omit [DecidableEq K] in
theorem toApplyCfg_applyCfg (start : ApplyCfg Γ Λ R) : toApplyCfg (applyCfg start) = start := by
  apply FrontEndMachine.Transport.cfg_injective applyStackEquiv applySymbolEquiv applyRegisterEquiv
    applyLabelEquiv applyLabelEquiv.injective
  exact applyCfg_toApplyCfg (applyCfg start)

theorem apply_stage_prefix_reset (q : MoveApplyMachine.Phase) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (n : Nat) (reached : Cfg Γ Λ R)
    (bound : n ≤ (applyFinish q D).steps)
    (executed : (next caller)^[n] (some (cfg (some (phaseLabel (applyPhase q))) regs D ctx)) = some reached) :
    reached.var = applyRegisterEquiv (MoveApplyMachine.registersAt
      (toApplyCfg (cfg (some (phaseLabel (Λ := Λ) (applyPhase q))) regs D ctx)) n) := by
  let localCaller : MoveApplyMachine.External (ApplyCallerLabel Λ) → ApplyStatement Γ Λ R := fun _ => .halt
  let start : ApplyCfg Γ Λ R := applyView (some (MoveApplyMachine.phaseLabel q)) (applyRegisterEquiv.symm regs) D ctx
  have startEq : applyCfg start = cfg (some (phaseLabel (applyPhase q))) regs D ctx := by
    rw [applyCfg_view]
    simp only [Option.map_some, applyLabelEquiv_phase, Equiv.apply_symm_apply]
  have rank : MoveApplyMachine.remainingSteps start = (applyFinish q D).steps := by
    change MoveApplyMachine.remainingSteps (MoveApplyMachine.cfg _ _ _ _) = _
    rw [MoveApplyMachine.remainingSteps_phase_cfg]
    rfl
  obtain ⟨middle, run, _, rfl⟩ := apply_prefix_lift caller localCaller start n
    (by rwa [rank]) reached (by rwa [startEq])
  change applyRegisterEquiv middle.var = _
  rw [MoveApplyMachine.prefix_reset localCaller start middle n (by rwa [rank]) run,
    ← startEq, toApplyCfg_applyCfg]

theorem equality_stage_prefix_reset (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (n : Nat) (reached : Cfg Γ Λ R) (positive : 0 < n) (bound : n ≤ (equalityFinish D).steps)
    (executed : (next caller)^[n] (some (cfg (some (phaseLabel comparePhase)) regs D ctx)) = some reached) :
    reached.var = resetEquality regs := by
  let localCaller : TreeEqualityMachine.External (EqualityCallerLabel Λ) → EqualityStatement Γ Λ R := fun _ => .halt
  let start : EqualityCfg Γ Λ R := equalityView (some (TreeEqualityMachine.phaseLabel .compare))
    (equalityRegisterEquiv.symm regs) D ctx
  have startEq : equalityCfg start = cfg (some (phaseLabel comparePhase)) regs D ctx := by
    rw [equalityCfg_view]
    simp only [Option.map_some, equalityLabelEquiv_phase, Equiv.apply_symm_apply]
  have rank : TreeEqualityMachine.remainingSteps start = (equalityFinish D).steps := rfl
  obtain ⟨middle, run, _, rfl⟩ := equality_prefix_lift caller localCaller start n
    (by rwa [rank]) reached (by rwa [startEq])
  have registers := TreeEqualityMachine.prefix_reset localCaller D.source D.target
    (equalityRegisterEquiv.symm regs) (equalityContext D ctx) n middle positive bound run
  change equalityRegisterEquiv middle.var = _
  rw [registers, equalityRegisterEquiv_reset, Equiv.apply_symm_apply]

omit [DecidableEq K] in
def phaseRegistersBeforeJoin (q : Phase) (regs : Registers R) (D : LocalData)
    (ctx : ∀ k, List (Γ k)) (n : Nat) : Registers R :=
  match q with
  | .inl _ => resetFuel regs
  | .inr (.inl _) => applyRegisterEquiv (MoveApplyMachine.registersAt
      (toApplyCfg (cfg (some (phaseLabel (Λ := Λ) q)) regs D ctx)) n)
  | .inr (.inr _) => resetEquality regs

omit [DecidableEq K] in
def phaseRegistersAt (q : Phase) (regs : Registers R) (D : LocalData)
    (ctx : ∀ k, List (Γ k)) (n : Nat) : Registers R :=
  if n = 0 then regs else if n < firstJoinSteps q D
    then phaseRegistersBeforeJoin (Λ := Λ) q regs D ctx n else resetAll regs

omit [DecidableEq K] in
/-- This is the register value at the same actual inclusive prefix. Before
the first paid outer join, only the active component's temporary fields clear;
after the join all four temporary fields are none. -/
def registersAt (start : Cfg Γ Λ R) (n : Nat) : Registers R :=
  match start.l with
  | some (.inl q) => phaseRegistersAt (Λ := Λ) (.inl q) start.var (dataOfCfg start) (contextOfCfg start) n
  | some (.inr (.inl q)) => phaseRegistersAt (Λ := Λ) (.inr (.inl q)) start.var (dataOfCfg start) (contextOfCfg start) n
  | some (.inr (.inr (.inl q))) => phaseRegistersAt (Λ := Λ) (.inr (.inr q)) start.var (dataOfCfg start) (contextOfCfg start) n
  | _ => start.var

omit [DecidableEq K] in
theorem registersAt_phase_cfg (q : Phase) (regs : Registers R) (D : LocalData)
    (ctx : ∀ k, List (Γ k)) (n : Nat) :
    registersAt (cfg (some (phaseLabel (Λ := Λ) q)) regs D ctx) n =
      phaseRegistersAt (Λ := Λ) q regs D ctx n := by
  rcases q with q | (q | q) <;> rfl

theorem phase_prefix_reset (q : Phase) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (n : Nat) (reached : Cfg Γ Λ R) (bound : n ≤ phaseSteps q D)
    (executed : (next caller)^[n] (some (cfg (some (phaseLabel q)) regs D ctx)) = some reached) :
    reached.var = phaseRegistersAt (Λ := Λ) q regs D ctx n := by
  by_cases zero : n = 0
  · subst n
    have same : cfg (some (phaseLabel q)) regs D ctx = reached := Option.some.inj executed
    subst reached
    rfl
  have positive : 0 < n := by omega
  by_cases early : n < firstJoinSteps q D
  · simp only [phaseRegistersAt, zero, ite_false, early, ite_true]
    rcases q with fuel | (application | equality)
    · rcases fuel with q | (r | (d | impossible))
      · exact counter_stage_prefix_reset caller q D regs ctx n reached positive (by
          change n < (counterFinish q D).steps + 1 at early
          omega) executed
      · cases r <;> change n < 1 at early <;> omega
      · cases d with
        | inspectCertificate =>
            exact inspect_stage_prefix_reset caller D regs ctx n reached positive (by
              change n < (inspectStageFinish D).steps + 1 at early
              omega) executed
        | atEnd => change n < 1 at early; omega
      · exact Empty.elim impossible
    · rcases application with q | (r | (q | (r | impossible)))
      · exact apply_stage_prefix_reset caller (MoveApplyMachine.movePhase q) D regs ctx n reached (by
          change n < (applyFinish (MoveApplyMachine.movePhase q) D).steps + 1 at early
          omega) executed
      · exact apply_stage_prefix_reset caller (MoveApplyMachine.dispatchPhase r) D regs ctx n reached (by
          change n < (applyFinish (MoveApplyMachine.dispatchPhase r) D).steps + 1 at early
          omega) executed
      · exact apply_stage_prefix_reset caller (MoveApplyMachine.positionPhase q) D regs ctx n reached (by
          change n < (applyFinish (MoveApplyMachine.positionPhase q) D).steps + 1 at early
          omega) executed
      · change n < 1 at early; omega
      · exact Empty.elim impossible
    · rcases equality with q | (r | impossible)
      · cases q
        exact equality_stage_prefix_reset caller D regs ctx n reached positive (by
          change n < (equalityFinish D).steps + 1 at early
          omega) executed
      · change n < 1 at early; omega
      · exact Empty.elim impossible
  · simp only [phaseRegistersAt, zero, ite_false, early]
    exact prefix_reset_after_firstJoin caller q D regs ctx n reached (by omega) bound executed

theorem prefix_reset (start reached : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start)
    (executed : (next caller)^[n] (some start) = some reached) : reached.var = registersAt start n := by
  by_cases owned : Owned start.l
  · obtain ⟨q, regs, D, ctx, rfl⟩ := owned_cases start owned
    rw [registersAt_phase_cfg]
    rw [remainingSteps_phase_cfg] at bound
    exact phase_prefix_reset caller q D regs ctx n reached bound executed
  · have rank : remainingSteps start = 0 := by
      have := (remainingSteps_pos_iff start).not.mpr owned
      omega
    have zero : n = 0 := by omega
    subst n
    have same : start = reached := Option.some.inj executed
    subst reached
    cases labelEq : start.l with
    | none => simp only [registersAt, labelEq]
    | some label =>
        rcases label with fuel | (applied | (equality | external))
        · exact False.elim (owned (by simp only [labelEq, Owned]))
        · exact False.elim (owned (by simp only [labelEq, Owned]))
        · exact False.elim (owned (by simp only [labelEq, Owned]))
        · simp only [registersAt, labelEq]

/-- One actual witness carries execution, exact remaining rank, local closure,
ownership at precisely the strict prefixes, zero-prefix identity, staged
registers, the caller register, and every protected stack. No finiteness of K
is needed for these operational and frame facts. -/
theorem owned_prefix_frame (start : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start) :
    ∃ reached, (next caller)^[n] (some start) = some reached ∧
      remainingSteps reached = remainingSteps start - n ∧
      Relation.ReflTransGen (LocalStep caller) start reached ∧
      (n < remainingSteps start ↔ Owned reached.l) ∧
      (n = 0 → reached = start) ∧ reached.var = registersAt start n ∧
      reached.var.2.2 = start.var.2.2 ∧ ∀ k, reached.stk (.inr k) = start.stk (.inr k) := by
  obtain ⟨reached, executed, rank, path, owned⟩ := owned_prefix caller start n bound
  refine ⟨reached, executed, rank, path, owned, ?_, prefix_reset caller start reached n bound executed,
    local_reaches_frame caller path⟩
  intro zero
  subst n
  exact (Option.some.inj executed).symm

end Resources.RotationCertificate.StreamMachine

-- END STAGED REGISTERS PASSED2

-- BEGIN SHARED DIRTY PREFIX SPACE
namespace Resources.RotationCertificate.StreamMachine

variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
variable (caller : External Λ → Statement Γ Λ R)

/-- A single actual reached configuration carries the full dirty prefix
contract, including staged registers and the literal whole physical sum. -/
theorem owned_prefix_space (start : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start) :
    ∃ reached, (next caller)^[n] (some start) = some reached ∧
      remainingSteps reached = remainingSteps start - n ∧
      Relation.ReflTransGen (LocalStep caller) start reached ∧
      (n < remainingSteps start ↔ Owned reached.l) ∧
      (n = 0 → reached = start) ∧ reached.var = registersAt start n ∧
      reached.var.2.2 = start.var.2.2 ∧
      (∀ k, reached.stk (.inr k) = start.stk (.inr k)) ∧
      stackCells reached ≤ allowance start := by
  obtain ⟨reached, executed, rank, path, live, zero, registers, callerRegister, frame⟩ :=
    owned_prefix_frame caller start n bound
  exact ⟨reached, executed, rank, path, live, zero, registers, callerRegister, frame,
    prefix_stackCells_le_dirty caller start n bound reached executed⟩

end Resources.RotationCertificate.StreamMachine

-- END SHARED DIRTY PREFIX SPACE

-- BEGIN COMPLETE SOURCE SUFFIX6
namespace Resources.RotationCertificate.StreamMachine

open Search.SharedTree (Branch)
open Trees.Rotations (RotationDirection RotationMove)
open Resources.BinaryCounter (Bits)

variable {K Λ R : Type} {Γ : K → Type} [DecidableEq K]
variable (caller : External Λ → Statement Γ Λ R)

/-! ### Pure complete MoveApply observations used by clean Stream induction -/

/-- The seven MoveApply stores at a clean Stream call; fuel and target are in
the caller complement of this component. -/
def moveCleanData (raw source : Word) : MoveApplyMachine.LocalData :=
  MoveApplyMachine.entryData raw [] source [] [] []

private theorem move_evaluation_eq (actual : MoveApplyMachine.Evaluation)
    (result : MoveApplyMachine.FinalResult) (D : MoveApplyMachine.LocalData) (ticks : Nat)
    (label : actual.result = result) (data : actual.data = D) (clock : actual.steps = ticks) :
    actual = ⟨result, D, ticks⟩ := by
  cases actual
  cases label
  cases data
  cases clock
  rfl

/-- Clean source parse failure preserves the complete component input and pays
the real parser clock plus its actual one-step failure dispatch. -/
theorem move_clean_parse_failure (raw source : Word)
    (failed : (parseMoveRun raw).1 = none) :
    MoveApplyMachine.evaluate (MoveApplyMachine.movePhase .start) (moveCleanData raw source) =
      ⟨MoveApplyMachine.parseFailure, moveCleanData raw source,
        MoveParserMachine.fullSteps raw + 1⟩ := by
  let caller : MoveApplyMachine.External Unit →
      MoveApplyMachine.Statement (fun _ : Unit => Unit) Unit Unit := fun _ => .halt
  let regs : MoveApplyMachine.Registers Unit := ((none, (none, none)), ())
  have actual := MoveApplyMachine.run_none_data caller raw [] source [] [] [] regs (fun _ => []) failed
  have label := congrArg (fun c : MoveApplyMachine.Cfg (fun _ : Unit => Unit) Unit Unit => c.l) actual.2
  have data := congrArg
    (fun c : MoveApplyMachine.Cfg (fun _ : Unit => Unit) Unit Unit => MoveApplyMachine.dataOfCfg c) actual.2
  simp only [MoveApplyMachine.runResult, MoveApplyMachine.phaseResult, MoveApplyMachine.cfg,
    MoveApplyMachine.resultLabel, Option.some.injEq, Sum.inr.injEq, Sum.inl.injEq] at label
  simp only [MoveApplyMachine.runResult, MoveApplyMachine.phaseResult,
    MoveApplyMachine.dataOfCfg_cfg] at data
  exact move_evaluation_eq _ _ _ _ label data actual.1

/-- A parsed clean raw call returns the actual output and unvisited path, with
all four temporary stacks empty. The output length is preserved even on raw
malformed words; rotation failure restores the source word literally. -/
theorem move_clean_parsed_raw (raw source : Word) (move : RotationMove) (rest : Word)
    (parsed : (parseMoveRun raw).1 = some (move, rest)) :
    ∃ result output path,
      MoveApplyMachine.evaluate (MoveApplyMachine.movePhase .start) (moveCleanData raw source) =
        ⟨.inr result, { certificate := rest, source := output, path := path },
          2 * move.position.length + 4 +
            PositionedRotationMachine.runSteps move.direction source move.position⟩ ∧
      output.length = source.length ∧
      (∃ consumed, move.position = consumed ++ path) ∧
      (result = .failure → output = source) ∧
      (result = .success → path = []) := by
  let caller : MoveApplyMachine.External Unit →
      MoveApplyMachine.Statement (fun _ : Unit => Unit) Unit Unit := fun _ => .halt
  let regs : MoveApplyMachine.Registers Unit := ((none, (none, none)), ())
  obtain ⟨result, output, path, endpoint, length, suffix, failed, succeeded⟩ :=
    MoveApplyMachine.run_raw_data caller move rest [] source regs (fun _ => [])
  rw [← (parseMoveRun_iff raw move rest).mp parsed] at endpoint
  have label := congrArg (fun c : MoveApplyMachine.Cfg (fun _ : Unit => Unit) Unit Unit => c.l) endpoint
  have data := congrArg
    (fun c : MoveApplyMachine.Cfg (fun _ : Unit => Unit) Unit Unit => MoveApplyMachine.dataOfCfg c) endpoint
  simp only [MoveApplyMachine.runResult, MoveApplyMachine.phaseResult, MoveApplyMachine.cfg,
    MoveApplyMachine.resultLabel, Option.some.injEq, Sum.inr.injEq, Sum.inl.injEq] at label
  simp only [MoveApplyMachine.runResult, MoveApplyMachine.phaseResult,
    MoveApplyMachine.dataOfCfg_cfg] at data
  have clock := MoveApplyMachine.runSteps_of_some raw move rest [] source [] [] [] parsed
  rw [MoveParserMachine.fullSteps_of_some raw move rest parsed] at clock
  simp only [List.append_nil] at clock suffix
  refine ⟨result, output, path, move_evaluation_eq _ _ _ _ label data ?_,
    length, suffix, failed, succeeded⟩
  exact clock

/-- Every clean successful raw application has a literal shorter certificate,
the actual length-preserving output word, and no auxiliary residue. -/
theorem move_clean_success (raw source : Word)
    (returned : (MoveApplyMachine.evaluate (MoveApplyMachine.movePhase .start)
      (moveCleanData raw source)).result = MoveApplyMachine.success) :
    ∃ move rest output,
      (parseMoveRun raw).1 = some (move, rest) ∧
      MoveApplyMachine.evaluate (MoveApplyMachine.movePhase .start) (moveCleanData raw source) =
        ⟨MoveApplyMachine.success, { certificate := rest, source := output },
          2 * move.position.length + 4 +
            PositionedRotationMachine.runSteps move.direction source move.position⟩ ∧
      output.length = source.length ∧
      raw.length = move.position.length + 2 + rest.length ∧
      rest.length < raw.length := by
  obtain ⟨move, rest, parsed, intermediate, certificate, encoded, consumed, two, less⟩ :=
    move_start_success_has_parse (moveCleanData raw source) returned
  obtain ⟨result, output, path, actual, length, suffix, failed, succeeded⟩ :=
    move_clean_parsed_raw raw source move rest parsed
  have isSuccess : result = .success := by
    rw [actual] at returned
    exact Sum.inr.inj returned
  have empty := succeeded isSuccess
  subst result
  subst path
  exact ⟨move, rest, output, parsed, actual, length, consumed, less⟩

/-- Both represented outcomes are the complete existing MoveApply endpoint,
with its real physical clock and without changing the source tariff. -/
theorem move_clean_represented (move : RotationMove) (rest : Word) (s : BinaryTree Unit) :
    MoveApplyMachine.evaluate (MoveApplyMachine.movePhase .start)
        (moveCleanData (moveCode move ++ rest) (treeCode s)) =
      ⟨MoveApplyMachine.representedResult move [] s,
        MoveApplyMachine.representedFinalData move rest [] s [] [],
        MoveApplyMachine.representedSteps move [] s []⟩ := by
  let caller : MoveApplyMachine.External Unit →
      MoveApplyMachine.Statement (fun _ : Unit => Unit) Unit Unit := fun _ => .halt
  let regs : MoveApplyMachine.Registers Unit := ((none, (none, none)), ())
  have actual := MoveApplyMachine.represented_run_data caller move rest [] s [] [] regs (fun _ => [])
  simp only [List.append_nil] at actual
  have label := congrArg (fun c : MoveApplyMachine.Cfg (fun _ : Unit => Unit) Unit Unit => c.l) actual.2
  have data := congrArg
    (fun c : MoveApplyMachine.Cfg (fun _ : Unit => Unit) Unit Unit => MoveApplyMachine.dataOfCfg c) actual.2
  simp only [MoveApplyMachine.runResult, MoveApplyMachine.phaseResult, MoveApplyMachine.cfg,
    MoveApplyMachine.resultLabel, Option.some.injEq, Sum.inr.injEq, Sum.inl.injEq] at label
  simp only [MoveApplyMachine.runResult, MoveApplyMachine.phaseResult,
    MoveApplyMachine.dataOfCfg_cfg] at data
  exact move_evaluation_eq _ _ _ _ label data actual.1

/-- The parser-failure branch uses its own shorter bound, not the looser parsed
Position bound that would hide the uniform clean-stream arithmetic. -/
theorem move_clean_steps_of_none (raw source : Word)
    (failed : (parseMoveRun raw).1 = none) :
    (MoveApplyMachine.evaluate (MoveApplyMachine.movePhase .start)
      (moveCleanData raw source)).steps ≤ 2 * raw.length + 2 := by
  rw [move_clean_parse_failure raw source failed]
  have bound := MoveParserMachine.fullSteps_le raw
  dsimp only
  omega

theorem move_clean_steps_of_some (raw source : Word) (move : RotationMove) (rest : Word)
    (parsed : (parseMoveRun raw).1 = some (move, rest)) :
    (MoveApplyMachine.evaluate (MoveApplyMachine.movePhase .start)
      (moveCleanData raw source)).steps ≤
      3 * source.length + 3 * move.position.length + 9 := by
  have bound := MoveApplyMachine.runSteps_le_of_some raw move rest [] source [] [] [] parsed
  change (MoveApplyMachine.evaluate (MoveApplyMachine.movePhase .start)
    (moveCleanData raw source)).steps ≤ _ at bound
  simpa only [List.length_nil, Nat.add_zero] using bound

/-- Successful represented application exposes the exact current source tree,
with the complete parser suffix and no physical path or auxiliary residue. -/
theorem move_clean_represented_of_some (move : RotationMove) (rest : Word)
    (s nextTree : BinaryTree Unit)
    (returned : (applyMoveRun move s).1 = some nextTree) :
    MoveApplyMachine.evaluate (MoveApplyMachine.movePhase .start)
      (moveCleanData (moveCode move ++ rest) (treeCode s)) =
        ⟨MoveApplyMachine.success, { certificate := rest, source := treeCode nextTree },
          MoveApplyMachine.representedSteps move [] s []⟩ := by
  have actual : MoveApplyMachine.representedValue move [] s = some nextTree := by
    simpa only [MoveApplyMachine.representedValue, MoveApplyMachine.physicalMove_nil] using returned
  rw [move_clean_represented, MoveApplyMachine.representedResult_of_some move [] s nextTree actual,
    MoveApplyMachine.representedFinalData_of_some move rest [] s nextTree [] [] actual]
  simp only [List.reverse_nil, List.nil_append, List.append_nil]

/-- Failure retains the literal unvisited represented path and restored source;
it consumes the parsed move but does not invoke a later stream activation. -/
theorem move_clean_represented_of_none (move : RotationMove) (rest : Word)
    (s : BinaryTree Unit) (failed : (applyMoveRun move s).1 = none) :
    MoveApplyMachine.evaluate (MoveApplyMachine.movePhase .start)
      (moveCleanData (moveCode move ++ rest) (treeCode s)) =
        ⟨MoveApplyMachine.rotationFailure,
          { certificate := rest, source := treeCode s,
            path := PositionedRotationMachine.remainingPath move.position s },
          MoveApplyMachine.representedSteps move [] s []⟩ := by
  have actual : MoveApplyMachine.representedValue move [] s = none := by
    simpa only [MoveApplyMachine.representedValue, MoveApplyMachine.physicalMove_nil] using failed
  rw [move_clean_represented, MoveApplyMachine.representedResult_of_none move [] s actual]
  simp only [MoveApplyMachine.representedFinalData,
    MoveApplyMachine.representedSource_of_none move [] s [] [] actual,
    List.reverse_nil, List.nil_append, List.append_nil]


/-! ### Clean raw inspection, exact paid branches and complete source endpoints -/

/-- Principal raw input. Registers and external stores remain arbitrary. -/
def cleanData (fuel : Bits) (certificate source target : Word) : LocalData where
  certificate := certificate
  source := source
  fuel := fuel
  target := target

def entry (regs : Registers R) (fuel : Bits) (certificate source target : Word)
    (ctx : ∀ k, List (Γ k)) : Cfg Γ Λ R :=
  cfg (some (phaseLabel inspectPhase)) regs (cleanData fuel certificate source target) ctx

def runEvaluation (fuel : Bits) (certificate source target : Word) : Evaluation :=
  evaluateInspect (cleanData fuel certificate source target)

def runSteps (fuel : Bits) (certificate source target : Word) : Nat :=
  (runEvaluation fuel certificate source target).steps

def runResult (regs : Registers R) (fuel : Bits) (certificate source target : Word)
    (ctx : ∀ k, List (Γ k)) : Cfg Γ Λ R :=
  evaluationCfg regs (runEvaluation fuel certificate source target) ctx

omit [DecidableEq K] in
@[simp] theorem remainingSteps_entry (regs : Registers R) (fuel : Bits)
    (certificate source target : Word) (ctx : ∀ k, List (Γ k)) :
    remainingSteps (entry (Λ := Λ) regs fuel certificate source target ctx) =
      runSteps fuel certificate source target :=
  remainingSteps_phase_cfg inspectPhase (cleanData fuel certificate source target) regs ctx

/-- Literal replacement of just the seven physical MoveApply stores. -/
def liftMoveData (fuel : Bits) (target : Word) (D : MoveApplyMachine.LocalData) : LocalData where
  certificate := D.certificate
  moveReverse := D.moveReverse
  path := D.path
  source := D.source
  saved := D.saved
  scratch := D.scratch
  units := D.pending
  fuel := fuel
  target := target

@[simp] theorem applyData_cleanData (fuel : Bits) (certificate source target : Word) :
    applyData (cleanData fuel certificate source target) = moveCleanData certificate source := rfl

@[simp] theorem setApplyData_cleanData (fuel : Bits) (certificate source target : Word)
    (D : MoveApplyMachine.LocalData) :
    setApplyData (cleanData fuel certificate source target) D = liftMoveData fuel target D := rfl

@[simp] theorem liftMoveData_clean (fuel : Bits) (certificate source target : Word) :
    liftMoveData fuel target { certificate := certificate, source := source } =
      cleanData fuel certificate source target := rfl

@[simp] theorem counterFinish_clean (fuel : Bits) (certificate source target : Word) :
    counterFinish .borrow (cleanData fuel certificate source target) =
      ⟨(Resources.BinaryCounter.FixedWidthMachine.predSpec fuel).1,
        cleanData (Resources.BinaryCounter.FixedWidthMachine.predSpec fuel).2 certificate source target,
        Resources.BinaryCounter.FixedWidthMachine.runSteps fuel⟩ := by
  simp only [counterFinish, cleanData, List.length_nil, List.replicate_zero,
    List.nil_append, Nat.add_zero]

@[simp] theorem applyFinish_clean (fuel : Bits) (certificate source target : Word) :
    applyFinish (MoveApplyMachine.movePhase .start) (cleanData fuel certificate source target) =
      let actual := MoveApplyMachine.evaluate (MoveApplyMachine.movePhase .start)
        (moveCleanData certificate source)
      ⟨actual.result, liftMoveData fuel target actual.data, actual.steps⟩ := rfl

@[simp] theorem equalityResult_wordResult (source target : Word) :
    equalityResult (TreeEqualityMachine.wordResult source target) = decide (source = target) := by
  by_cases same : source = target
  · simp only [TreeEqualityMachine.wordResult, ite_eq_left same, equalityResult, decide_eq_true same]
  · simp only [TreeEqualityMachine.wordResult, ite_eq_right same, equalityResult, decide_eq_false same]

/-- EOF precedes fuel and pays inspection, the atEnd join and the result join. -/
theorem runEvaluation_nil (fuel : Bits) (source target : Word) :
    runEvaluation fuel [] source target =
      ⟨decide (source = target),
        cleanData fuel [] (source.drop (TreeEqualityMachine.runSteps source target))
          (target.drop (TreeEqualityMachine.runSteps source target)),
        TreeEqualityMachine.runSteps source target + 3⟩ := by
  rw [runEvaluation, evaluateInspect_nil _ rfl]
  simp only [addSteps, evaluateEquality, equalityFinish, cleanData, equalityResult_wordResult]
  congr 1
  omega

/-- A nonempty certificate with no predecessor returns before parsing it. -/
theorem runEvaluation_no_fuel (fuel : Bits) (certificate source target : Word)
    (nonempty : certificate ≠ [])
    (failed : (Resources.BinaryCounter.decFixedRun fuel).1 = none) :
    runEvaluation fuel certificate source target =
      ⟨false, cleanData fuel certificate source target,
        Resources.BinaryCounter.FixedWidthMachine.runSteps fuel + 2⟩ := by
  rw [runEvaluation, evaluateInspect_nonempty _ nonempty]
  simp only [evaluateCounter, counterFinish_clean,
    Resources.BinaryCounter.FixedWidthMachine.predSpec_of_none failed,
    FuelDispatchMachine.exitOfResult, evaluateFuelJoin, addSteps]
  congr 1
  omega

/-- Complete early failure after an actual positive predecessor. The supplied
MoveApply endpoint retains every raw residual word and every paid clock. -/
theorem runEvaluation_move_failure (fuel nextFuel : Bits) (certificate source target : Word)
    (result : MoveApplyMachine.FinalResult) (D : MoveApplyMachine.LocalData) (ticks : Nat)
    (nonempty : certificate ≠ [])
    (decremented : (Resources.BinaryCounter.decFixedRun fuel).1 = some nextFuel)
    (applied : MoveApplyMachine.evaluate (MoveApplyMachine.movePhase .start)
      (moveCleanData certificate source) = ⟨result, D, ticks⟩)
    (failed : result ≠ MoveApplyMachine.success) :
    runEvaluation fuel certificate source target =
      ⟨false, liftMoveData nextFuel target D,
        Resources.BinaryCounter.FixedWidthMachine.runSteps fuel + ticks + 3⟩ := by
  rw [runEvaluation, evaluateInspect_nonempty _ nonempty]
  simp only [evaluateCounter, counterFinish_clean,
    Resources.BinaryCounter.FixedWidthMachine.predSpec_of_some decremented,
    FuelDispatchMachine.exitOfResult, evaluateFuelJoin, evaluateApply, applyFinish_clean, applied]
  cases result with
  | inl token =>
      simp only [evaluateApplyJoin, addSteps]
      congr 1
      omega
  | inr result => cases result with
    | failure =>
        simp only [evaluateApplyJoin, addSteps]
        congr 1
        omega
    | success => exact False.elim (failed rfl)

/-- Successful application pays its literal result join and reinspects the
actual complete returned data; there is no new copy, parser call or reset of words. -/
theorem runEvaluation_move_success (fuel nextFuel : Bits) (certificate source target : Word)
    (D : MoveApplyMachine.LocalData) (ticks : Nat)
    (nonempty : certificate ≠ [])
    (decremented : (Resources.BinaryCounter.decFixedRun fuel).1 = some nextFuel)
    (applied : MoveApplyMachine.evaluate (MoveApplyMachine.movePhase .start)
      (moveCleanData certificate source) = ⟨MoveApplyMachine.success, D, ticks⟩) :
    runEvaluation fuel certificate source target =
      addSteps (Resources.BinaryCounter.FixedWidthMachine.runSteps fuel + ticks + 3)
        (evaluateInspect (liftMoveData nextFuel target D)) := by
  rw [runEvaluation, evaluateInspect_nonempty _ nonempty]
  simp only [evaluateCounter, counterFinish_clean,
    Resources.BinaryCounter.FixedWidthMachine.predSpec_of_some decremented,
    FuelDispatchMachine.exitOfResult, evaluateFuelJoin, evaluateApply, applyFinish_clean, applied,
    MoveApplyMachine.success, evaluateApplyJoin, addSteps]
  congr 1
  omega

/-- Parser failure restores the current certificate suffix, after the decrement. -/
theorem runEvaluation_parse_failure (fuel nextFuel : Bits) (certificate source target : Word)
    (nonempty : certificate ≠ [])
    (decremented : (Resources.BinaryCounter.decFixedRun fuel).1 = some nextFuel)
    (failed : (parseMoveRun certificate).1 = none) :
    runEvaluation fuel certificate source target =
      ⟨false, cleanData nextFuel certificate source target,
        Resources.BinaryCounter.FixedWidthMachine.runSteps fuel +
          MoveParserMachine.fullSteps certificate + 4⟩ := by
  have actual := runEvaluation_move_failure fuel nextFuel certificate source target
    MoveApplyMachine.parseFailure (moveCleanData certificate source)
    (MoveParserMachine.fullSteps certificate + 1) nonempty decremented
    (move_clean_parse_failure certificate source failed) (by intro h; cases h)
  simpa only [moveCleanData, MoveApplyMachine.entryData, liftMoveData, cleanData, Nat.add_assoc] using actual

/-- A parsed failed rotation retains the actual unvisited path suffix and the
literal restored source, while preserving the actual certificate rest. -/
theorem runEvaluation_rotation_failure (fuel nextFuel : Bits) (certificate source target : Word)
    (move : RotationMove) (rest : Word) (path : List Branch)
    (decremented : (Resources.BinaryCounter.decFixedRun fuel).1 = some nextFuel)
    (parsed : (parseMoveRun certificate).1 = some (move, rest))
    (applied : MoveApplyMachine.evaluate (MoveApplyMachine.movePhase .start)
      (moveCleanData certificate source) =
        ⟨MoveApplyMachine.rotationFailure, { certificate := rest, source := source, path := path },
          2 * move.position.length + 4 +
            PositionedRotationMachine.runSteps move.direction source move.position⟩) :
    runEvaluation fuel certificate source target =
      ⟨false, { (cleanData nextFuel rest source target) with path := path },
        Resources.BinaryCounter.FixedWidthMachine.runSteps fuel +
          (2 * move.position.length + 4 +
            PositionedRotationMachine.runSteps move.direction source move.position) + 3⟩ := by
  have nonempty : certificate ≠ [] := by intro h; simp only [h, parseMoveRun_nil] at parsed; cases parsed
  exact runEvaluation_move_failure fuel nextFuel certificate source target
    MoveApplyMachine.rotationFailure _ _ nonempty decremented applied (by intro h; cases h)

/-- A successful clean raw call returns with all auxiliaries empty and the same
source length; this recurrence uses its actual returned raw output. -/
theorem runEvaluation_step (fuel nextFuel : Bits) (certificate source target : Word)
    (move : RotationMove) (rest output : Word)
    (decremented : (Resources.BinaryCounter.decFixedRun fuel).1 = some nextFuel)
    (parsed : (parseMoveRun certificate).1 = some (move, rest))
    (applied : MoveApplyMachine.evaluate (MoveApplyMachine.movePhase .start)
      (moveCleanData certificate source) =
        ⟨MoveApplyMachine.success, { certificate := rest, source := output },
          2 * move.position.length + 4 +
            PositionedRotationMachine.runSteps move.direction source move.position⟩) :
    runEvaluation fuel certificate source target =
      addSteps (Resources.BinaryCounter.FixedWidthMachine.runSteps fuel +
          (2 * move.position.length + 4 +
            PositionedRotationMachine.runSteps move.direction source move.position) + 3)
        (runEvaluation nextFuel rest output target) := by
  have nonempty : certificate ≠ [] := by intro h; simp only [h, parseMoveRun_nil] at parsed; cases parsed
  exact runEvaluation_move_success fuel nextFuel certificate source target _ _
    nonempty decremented applied

@[simp] theorem runSteps_nil (fuel : Bits) (source target : Word) :
    runSteps fuel [] source target = TreeEqualityMachine.runSteps source target + 3 := by
  rw [runSteps, runEvaluation_nil]

theorem runSteps_no_fuel (fuel : Bits) (certificate source target : Word)
    (nonempty : certificate ≠ [])
    (failed : (Resources.BinaryCounter.decFixedRun fuel).1 = none) :
    runSteps fuel certificate source target =
      Resources.BinaryCounter.FixedWidthMachine.runSteps fuel + 2 := by
  rw [runSteps, runEvaluation_no_fuel fuel certificate source target nonempty failed]

/-- The exact H segment clock is already inclusive of its internal parser
success/failure dispatch; the Stream controller adds its own three activations. -/
theorem runSteps_move_failure (fuel nextFuel : Bits) (certificate source target : Word)
    (decremented : (Resources.BinaryCounter.decFixedRun fuel).1 = some nextFuel)
    (nonempty : certificate ≠ [])
    (failed : (MoveApplyMachine.evaluate (MoveApplyMachine.movePhase .start)
      (moveCleanData certificate source)).result ≠ MoveApplyMachine.success) :
    runSteps fuel certificate source target =
      Resources.BinaryCounter.FixedWidthMachine.runSteps fuel +
        MoveApplyMachine.runSteps certificate [] source [] [] [] + 3 := by
  let actual := MoveApplyMachine.evaluate (MoveApplyMachine.movePhase .start)
    (moveCleanData certificate source)
  have result := runEvaluation_move_failure fuel nextFuel certificate source target
    actual.result actual.data actual.steps nonempty decremented (by change actual = _; cases actual; rfl) failed
  exact congrArg Evaluation.steps result

private theorem clean_segment_budget (fuel source path : Nat) :
    2 * fuel + 3 * source + 3 * path + 14 ≤
      (2 * fuel + 3 * source + 7) * (path + 2) := by
  have scaled := Nat.mul_le_mul_left (2 * fuel + 3 * source + 4)
    (show 2 ≤ path + 2 by omega)
  have split : (2 * fuel + 3 * source + 7) * (path + 2) =
      (2 * fuel + 3 * source + 4) * (path + 2) + 3 * (path + 2) := by
    rw [show 2 * fuel + 3 * source + 7 = (2 * fuel + 3 * source + 4) + 3 by omega,
      Nat.add_mul]
  rw [split]
  omega

private theorem clean_parse_failure_budget (fuel source certificate : Nat)
    (positive : 0 < certificate) :
    2 * fuel + 2 * certificate + 7 ≤
      (2 * fuel + 3 * source + 7) * certificate + source + 4 := by
  have scaled := Nat.mul_le_mul_left (2 * fuel + 3 * source + 5)
    (show 1 ≤ certificate by omega)
  simp only [Nat.mul_one] at scaled
  have split : (2 * fuel + 3 * source + 7) * certificate =
      (2 * fuel + 3 * source + 5) * certificate + 2 * certificate := by
    rw [show 2 * fuel + 3 * source + 7 = (2 * fuel + 3 * source + 5) + 2 by omega,
      Nat.add_mul]
  rw [split]
  omega

private theorem clean_runSteps_bound_aux (size : Nat) :
    ∀ certificate : Word, certificate.length = size → ∀ fuel : Bits, ∀ source target : Word,
      runSteps fuel certificate source target ≤
        (2 * fuel.length + 3 * source.length + 7) * certificate.length + source.length + 4 := by
  induction size using Nat.strong_induction_on with
  | h size ih =>
      intro certificate sized fuel source target
      by_cases empty : certificate = []
      · subst certificate
        rw [runSteps_nil]
        have bound := TreeEqualityMachine.runSteps_le source target
        simp only [List.length_nil, Nat.mul_zero, Nat.zero_add]
        have minimum := Nat.min_le_left source.length target.length
        omega
      · have positive : 0 < certificate.length := List.length_pos_of_ne_nil empty
        have fuelBound := Resources.BinaryCounter.FixedWidthMachine.runSteps_le fuel
        cases predecessor : (Resources.BinaryCounter.decFixedRun fuel).1 with
        | none =>
            rw [runSteps_no_fuel fuel certificate source target empty predecessor]
            have scaled := Nat.mul_le_mul_left (2 * fuel.length + 3 * source.length + 7)
              (show 1 ≤ certificate.length by omega)
            simp only [Nat.mul_one] at scaled
            omega
        | some nextFuel =>
            cases parsed : (parseMoveRun certificate).1 with
            | none =>
                have actual := congrArg Evaluation.steps
                  (runEvaluation_parse_failure fuel nextFuel certificate source target empty predecessor parsed)
                change runSteps fuel certificate source target =
                  Resources.BinaryCounter.FixedWidthMachine.runSteps fuel +
                    MoveParserMachine.fullSteps certificate + 4 at actual
                have parserBound := MoveParserMachine.fullSteps_le certificate
                have budget := clean_parse_failure_budget fuel.length source.length certificate.length positive
                omega
            | some pair =>
                rcases pair with ⟨move, rest⟩
                obtain ⟨result, output, path, applied, length, suffix, failed, succeeded⟩ :=
                  move_clean_parsed_raw certificate source move rest parsed
                have consumed := parseMoveRun_consumed_length certificate move rest parsed
                have fewer := parseMoveRun_rest_length_lt certificate move rest parsed
                have moveBound := move_clean_steps_of_some certificate source move rest parsed
                rw [applied] at moveBound
                dsimp only at moveBound
                have segmentBound := clean_segment_budget fuel.length source.length move.position.length
                cases result with
                | failure =>
                    have actual := congrArg Evaluation.steps
                      (runEvaluation_move_failure fuel nextFuel certificate source target
                        (.inr .failure) _ _ empty predecessor applied (by intro h; cases h))
                    change runSteps fuel certificate source target =
                      Resources.BinaryCounter.FixedWidthMachine.runSteps fuel +
                        (2 * move.position.length + 4 +
                          PositionedRotationMachine.runSteps move.direction source move.position) + 3 at actual
                    have scaled := Nat.mul_le_mul_left (2 * fuel.length + 3 * source.length + 7)
                      (show move.position.length + 2 ≤ certificate.length by omega)
                    omega
                | success =>
                    have pathEmpty := succeeded rfl
                    subst path
                    have actual := congrArg Evaluation.steps
                      (runEvaluation_step fuel nextFuel certificate source target move rest output
                        predecessor parsed applied)
                    change runSteps fuel certificate source target =
                      (Resources.BinaryCounter.FixedWidthMachine.runSteps fuel +
                        (2 * move.position.length + 4 +
                          PositionedRotationMachine.runSteps move.direction source move.position) + 3) +
                        runSteps nextFuel rest output target at actual
                    have later := ih rest.length (by omega) rest rfl nextFuel output target
                    have width := Resources.BinaryCounter.decFixedRun_some_length predecessor
                    rw [width, length] at later
                    have split : (2 * fuel.length + 3 * source.length + 7) * certificate.length =
                        (2 * fuel.length + 3 * source.length + 7) * (move.position.length + 2) +
                          (2 * fuel.length + 3 * source.length + 7) * rest.length := by
                      rw [consumed, Nat.mul_add]
                    rw [split]
                    omega

/-- Uniform clean raw machine bound. This counts actual TM2 activations, with
all paid joins; it makes no claim about the different source-event tariff. -/
theorem runSteps_le (fuel : Bits) (certificate source target : Word) :
    runSteps fuel certificate source target ≤
      (2 * fuel.length + 3 * source.length + 7) * certificate.length + source.length + 4 :=
  clean_runSteps_bound_aux certificate.length certificate rfl fuel source target

/-- Tree representation changes only the bound's length expression. -/
theorem runSteps_code_le (fuel : Bits) (certificate : Word) (s t : BinaryTree Unit) :
    runSteps fuel certificate (treeCode s) (treeCode t) ≤
      (2 * fuel.length + 6 * s.numNodes + 10) * certificate.length + 2 * s.numNodes + 5 := by
  have bound := runSteps_le fuel certificate (treeCode s) (treeCode t)
  rw [treeCode_length] at bound
  have coefficient : 2 * fuel.length + 3 * (2 * s.numNodes + 1) + 7 =
      2 * fuel.length + 6 * s.numNodes + 10 := by omega
  rw [coefficient] at bound
  omega

private theorem clean_accept_cleanup_aux (size : Nat) :
    ∀ certificate : Word, certificate.length = size → ∀ fuel : Bits, ∀ source target : Word,
      (runEvaluation fuel certificate source target).result = true →
        ∃ finalFuel, (runEvaluation fuel certificate source target).data =
          cleanData finalFuel [] [] [] ∧ finalFuel.length = fuel.length := by
  induction size using Nat.strong_induction_on with
  | h size ih =>
      intro certificate sized fuel source target accepted
      by_cases empty : certificate = []
      · subst certificate
        rw [runEvaluation_nil] at accepted ⊢
        have same : source = target := of_decide_eq_true accepted
        subst target
        have consumed : source.drop (TreeEqualityMachine.runSteps source source) = [] := by
          rw [TreeEqualityMachine.runSteps_self]
          exact List.drop_eq_nil_of_le (by omega)
        exact ⟨fuel, by rw [consumed], rfl⟩
      · cases predecessor : (Resources.BinaryCounter.decFixedRun fuel).1 with
        | none =>
            rw [runEvaluation_no_fuel fuel certificate source target empty predecessor] at accepted
            cases accepted
        | some nextFuel =>
            cases parsed : (parseMoveRun certificate).1 with
            | none =>
                rw [runEvaluation_parse_failure fuel nextFuel certificate source target empty predecessor parsed]
                  at accepted
                cases accepted
            | some pair =>
                rcases pair with ⟨move, rest⟩
                obtain ⟨result, output, path, applied, length, suffix, failed, succeeded⟩ :=
                  move_clean_parsed_raw certificate source move rest parsed
                cases result with
                | failure =>
                    rw [runEvaluation_move_failure fuel nextFuel certificate source target
                      (.inr .failure) _ _ empty predecessor applied (by intro h; cases h)] at accepted
                    cases accepted
                | success =>
                    have pathEmpty := succeeded rfl
                    subst path
                    have actual := runEvaluation_step fuel nextFuel certificate source target
                      move rest output predecessor parsed applied
                    rw [actual] at accepted ⊢
                    change (runEvaluation nextFuel rest output target).result = true at accepted
                    have fewer := parseMoveRun_rest_length_lt certificate move rest parsed
                    obtain ⟨finalFuel, data, width⟩ :=
                      ih rest.length (by omega) rest rfl nextFuel output target accepted
                    exact ⟨finalFuel, data,
                      width.trans (Resources.BinaryCounter.decFixedRun_some_length predecessor)⟩

/-- Acceptance actually consumes the certificate and both compared words and
leaves every auxiliary word empty. The literal returned fuel and its width remain. -/
theorem run_accept_cleanup (fuel : Bits) (certificate source target : Word)
    (accepted : (runEvaluation fuel certificate source target).result = true) :
    ∃ finalFuel, (runEvaluation fuel certificate source target).data =
      cleanData finalFuel [] [] [] ∧ finalFuel.length = fuel.length :=
  clean_accept_cleanup_aux certificate.length certificate rfl fuel source target accepted

/-- A successful source parse determines the actual raw H outcome and the
complete stopped/continued Stream data; no represented-tree premise is needed. -/
theorem runEvaluation_after_parse (fuel nextFuel : Bits) (certificate source target : Word)
    (move : RotationMove) (rest : Word)
    (decremented : (Resources.BinaryCounter.decFixedRun fuel).1 = some nextFuel)
    (parsed : (parseMoveRun certificate).1 = some (move, rest)) :
    ∃ result output path,
      MoveApplyMachine.evaluate (MoveApplyMachine.movePhase .start) (moveCleanData certificate source) =
        ⟨.inr result, { certificate := rest, source := output, path := path },
          2 * move.position.length + 4 +
            PositionedRotationMachine.runSteps move.direction source move.position⟩ ∧
      output.length = source.length ∧
      (∃ consumed, move.position = consumed ++ path) ∧
      (result = .failure → output = source) ∧
      (result = .failure →
        runEvaluation fuel certificate source target =
          ⟨false, { (cleanData nextFuel rest source target) with path := path },
            Resources.BinaryCounter.FixedWidthMachine.runSteps fuel +
              (2 * move.position.length + 4 +
                PositionedRotationMachine.runSteps move.direction source move.position) + 3⟩) ∧
      (result = .success → path = [] ∧
        runEvaluation fuel certificate source target =
          addSteps (Resources.BinaryCounter.FixedWidthMachine.runSteps fuel +
              (2 * move.position.length + 4 +
                PositionedRotationMachine.runSteps move.direction source move.position) + 3)
            (runEvaluation nextFuel rest output target)) := by
  obtain ⟨result, output, path, actual, length, suffix, failed, succeeded⟩ :=
    move_clean_parsed_raw certificate source move rest parsed
  refine ⟨result, output, path, actual, length, suffix, failed, ?_, ?_⟩
  · intro failure
    subst result
    have restored := failed rfl
    subst output
    exact runEvaluation_rotation_failure fuel nextFuel certificate source target move rest path
      decremented parsed actual
  · intro success
    subst result
    have empty := succeeded rfl
    refine ⟨empty, ?_⟩
    subst path
    exact runEvaluation_step fuel nextFuel certificate source target move rest output
      decremented parsed actual

theorem runSteps_step (fuel nextFuel : Bits) (certificate source target : Word)
    (move : RotationMove) (rest output : Word)
    (decremented : (Resources.BinaryCounter.decFixedRun fuel).1 = some nextFuel)
    (parsed : (parseMoveRun certificate).1 = some (move, rest))
    (applied : MoveApplyMachine.evaluate (MoveApplyMachine.movePhase .start)
      (moveCleanData certificate source) =
        ⟨MoveApplyMachine.success, { certificate := rest, source := output },
          2 * move.position.length + 4 +
            PositionedRotationMachine.runSteps move.direction source move.position⟩) :
    runSteps fuel certificate source target =
      Resources.BinaryCounter.FixedWidthMachine.runSteps fuel +
        (2 * move.position.length + 4 +
          PositionedRotationMachine.runSteps move.direction source move.position) + 3 +
        runSteps nextFuel rest output target :=
  congrArg Evaluation.steps
    (runEvaluation_step fuel nextFuel certificate source target move rest output decremented parsed applied)

omit [DecidableEq K] in
theorem runResult_step (regs : Registers R) (fuel nextFuel : Bits) (certificate source target : Word)
    (move : RotationMove) (rest output : Word) (ctx : ∀ k, List (Γ k))
    (decremented : (Resources.BinaryCounter.decFixedRun fuel).1 = some nextFuel)
    (parsed : (parseMoveRun certificate).1 = some (move, rest))
    (applied : MoveApplyMachine.evaluate (MoveApplyMachine.movePhase .start)
      (moveCleanData certificate source) =
        ⟨MoveApplyMachine.success, { certificate := rest, source := output },
          2 * move.position.length + 4 +
            PositionedRotationMachine.runSteps move.direction source move.position⟩) :
    runResult (Λ := Λ) regs fuel certificate source target ctx =
      runResult (resetAll regs) nextFuel rest output target ctx := by
  simp only [runResult, runEvaluation_step fuel nextFuel certificate source target move rest output
    decremented parsed applied, evaluationCfg_addSteps, evaluationCfg_resetAll]


/-! ### Exact represented source values, recognition and separate observations -/

private theorem clean_source_value_aux (size : Nat) :
    ∀ certificate : Word, certificate.length = size → ∀ fuel : Bits,
      ∀ source target : BinaryTree Unit,
        (runEvaluation fuel certificate (treeCode source) (treeCode target)).result =
          (checkStreamRun fuel source target certificate).1 := by
  induction size using Nat.strong_induction_on with
  | h size ih =>
      intro certificate sized fuel source target
      cases certificate with
      | nil =>
          rw [runEvaluation_nil, checkStreamRun_nil]
          dsimp only [Resources.CallCount.tick]
          simpa only [TreeEqualityMachine.wordResult_equal_iff] using
            TreeEqualityMachine.result_code_source source target
      | cons tag raw =>
          have nonempty : tag :: raw ≠ [] := by simp
          cases predecessor : (Resources.BinaryCounter.decFixedRun fuel).1 with
          | none =>
              rw [runEvaluation_no_fuel fuel (tag :: raw) (treeCode source) (treeCode target)
                nonempty predecessor,
                checkStreamRun_no_fuel fuel source target tag raw predecessor]
          | some nextFuel =>
              cases parsed : (parseMoveRun (tag :: raw)).1 with
              | none =>
                  rw [runEvaluation_parse_failure fuel nextFuel (tag :: raw)
                    (treeCode source) (treeCode target) nonempty predecessor parsed,
                    checkStreamRun_parse_failure fuel nextFuel source target tag raw predecessor parsed]
              | some pair =>
                  rcases pair with ⟨move, rest⟩
                  have encoded := (parseMoveRun_iff (tag :: raw) move rest).mp parsed
                  have fewer := parseMoveRun_rest_length_lt (tag :: raw) move rest parsed
                  cases executed : (applyMoveRun move source).1 with
                  | none =>
                      have actual := move_clean_represented_of_none move rest source executed
                      rw [← encoded] at actual
                      rw [runEvaluation_move_failure fuel nextFuel (tag :: raw)
                        (treeCode source) (treeCode target) MoveApplyMachine.rotationFailure _ _
                        nonempty predecessor actual (by intro h; cases h),
                        checkStreamRun_move_failure fuel nextFuel source target (tag :: raw) rest move
                          predecessor parsed executed]
                  | some nextTree =>
                      have actual := move_clean_represented_of_some move rest source nextTree executed
                      rw [← encoded] at actual
                      rw [runEvaluation_move_success fuel nextFuel (tag :: raw)
                        (treeCode source) (treeCode target) _ _ nonempty predecessor actual,
                        checkStreamRun_step fuel nextFuel source nextTree target (tag :: raw) rest move
                          predecessor parsed executed]
                      change (runEvaluation nextFuel rest (treeCode nextTree) (treeCode target)).result =
                        (checkStreamRun nextFuel nextTree target rest).1
                      exact ih rest.length (by omega) rest rfl nextFuel nextTree target

/-- The actual finite-machine Boolean is the existing measured source checker's
Boolean for every represented principal input, including all early failures. -/
theorem runEvaluation_code_value (fuel : Bits) (certificate : Word)
    (source target : BinaryTree Unit) :
    (runEvaluation fuel certificate (treeCode source) (treeCode target)).result =
      (checkStreamRun fuel source target certificate).1 :=
  clean_source_value_aux certificate.length certificate rfl fuel source target

/-- Source-success recursion keeps its actual next tree, literal certificate
suffix, complete physical endpoint and the unchanged source node count. -/
theorem represented_success_step (fuel nextFuel : Bits) (certificate rest : Word)
    (move : RotationMove) (source nextTree target : BinaryTree Unit)
    (decremented : (Resources.BinaryCounter.decFixedRun fuel).1 = some nextFuel)
    (parsed : (parseMoveRun certificate).1 = some (move, rest))
    (executed : (applyMoveRun move source).1 = some nextTree) :
    runEvaluation fuel certificate (treeCode source) (treeCode target) =
      addSteps (Resources.BinaryCounter.FixedWidthMachine.runSteps fuel +
          MoveApplyMachine.representedSteps move [] source [] + 3)
        (runEvaluation nextFuel rest (treeCode nextTree) (treeCode target)) ∧
      certificate = moveCode move ++ rest ∧
      certificate.length = move.position.length + 2 + rest.length ∧
      nextTree.numNodes = source.numNodes := by
  have encoded := (parseMoveRun_iff certificate move rest).mp parsed
  have nonempty : certificate ≠ [] := by intro h; simp only [h, parseMoveRun_nil] at parsed; cases parsed
  have actual := move_clean_represented_of_some move rest source nextTree executed
  rw [← encoded] at actual
  exact ⟨runEvaluation_move_success fuel nextFuel certificate (treeCode source) (treeCode target)
      _ _ nonempty decremented actual,
    encoded, parseMoveRun_consumed_length certificate move rest parsed,
    applyMoveRun_numNodes move source nextTree executed⟩

/-- Failed represented application consumes precisely the parsed move and
retains the actual stopped physical path; no later source check occurs. -/
theorem represented_failure_step (fuel nextFuel : Bits) (certificate rest : Word)
    (move : RotationMove) (source target : BinaryTree Unit)
    (decremented : (Resources.BinaryCounter.decFixedRun fuel).1 = some nextFuel)
    (parsed : (parseMoveRun certificate).1 = some (move, rest))
    (failed : (applyMoveRun move source).1 = none) :
    runEvaluation fuel certificate (treeCode source) (treeCode target) =
      ⟨false, { (cleanData nextFuel rest (treeCode source) (treeCode target)) with
          path := PositionedRotationMachine.remainingPath move.position source },
        Resources.BinaryCounter.FixedWidthMachine.runSteps fuel +
          MoveApplyMachine.representedSteps move [] source [] + 3⟩ := by
  have encoded := (parseMoveRun_iff certificate move rest).mp parsed
  have nonempty : certificate ≠ [] := by intro h; simp only [h, parseMoveRun_nil] at parsed; cases parsed
  have actual := move_clean_represented_of_none move rest source failed
  rw [← encoded] at actual
  exact runEvaluation_move_failure fuel nextFuel certificate (treeCode source) (treeCode target)
    MoveApplyMachine.rotationFailure _ _ nonempty decremented actual (by intro h; cases h)

/-- This observation is the unchanged measured source checker, not TM2 time. -/
def sourceObservation (fuel : Bits) (source target : BinaryTree Unit) (certificate : Word) :
    Measured Bool Nat := checkStreamRun fuel source target certificate

@[simp] theorem sourceObservation_nil (fuel : Bits) (source target : BinaryTree Unit) :
    sourceObservation fuel source target [] =
      ((eqTreeRun source target).1, (eqTreeRun source target).2 + 1) :=
  checkStreamRun_nil fuel source target

theorem sourceObservation_no_fuel (fuel : Bits) (source target : BinaryTree Unit)
    (tag : Tag) (raw : Word) (failed : (Resources.BinaryCounter.decFixedRun fuel).1 = none) :
    sourceObservation fuel source target (tag :: raw) =
      (false, (Resources.BinaryCounter.decFixedRun fuel).2 + 2) :=
  checkStreamRun_no_fuel fuel source target tag raw failed

theorem sourceObservation_parse_failure (fuel nextFuel : Bits) (source target : BinaryTree Unit)
    (tag : Tag) (raw : Word)
    (decremented : (Resources.BinaryCounter.decFixedRun fuel).1 = some nextFuel)
    (failed : (parseMoveRun (tag :: raw)).1 = none) :
    sourceObservation fuel source target (tag :: raw) =
      (false, (Resources.BinaryCounter.decFixedRun fuel).2 + (parseMoveRun (tag :: raw)).2 + 2) :=
  checkStreamRun_parse_failure fuel nextFuel source target tag raw decremented failed

theorem sourceObservation_move_failure (fuel nextFuel : Bits) (source target : BinaryTree Unit)
    (certificate rest : Word) (move : RotationMove)
    (decremented : (Resources.BinaryCounter.decFixedRun fuel).1 = some nextFuel)
    (parsed : (parseMoveRun certificate).1 = some (move, rest))
    (failed : (applyMoveRun move source).1 = none) :
    sourceObservation fuel source target certificate =
      (false, (Resources.BinaryCounter.decFixedRun fuel).2 + (parseMoveRun certificate).2 +
        (applyMoveRun move source).2 + 2) :=
  checkStreamRun_move_failure fuel nextFuel source target certificate rest move decremented parsed failed

theorem sourceObservation_step (fuel nextFuel : Bits) (source nextTree target : BinaryTree Unit)
    (certificate rest : Word) (move : RotationMove)
    (decremented : (Resources.BinaryCounter.decFixedRun fuel).1 = some nextFuel)
    (parsed : (parseMoveRun certificate).1 = some (move, rest))
    (executed : (applyMoveRun move source).1 = some nextTree) :
    sourceObservation fuel source target certificate =
      ((sourceObservation nextFuel nextTree target rest).1,
        (Resources.BinaryCounter.decFixedRun fuel).2 + (parseMoveRun certificate).2 +
          (applyMoveRun move source).2 + (sourceObservation nextFuel nextTree target rest).2 + 1) :=
  checkStreamRun_step fuel nextFuel source nextTree target certificate rest move decremented parsed executed

theorem source_success_application_cost (move : RotationMove) (source nextTree : BinaryTree Unit)
    (executed : (applyMoveRun move source).1 = some nextTree) :
    (applyMoveRun move source).2 = 3 * move.position.length + 5 :=
  applyMoveRun_cost_of_some move source nextTree executed

theorem sourceObservation_cost_le (fuel : Bits) (source target : BinaryTree Unit) (certificate : Word) :
    (sourceObservation fuel source target certificate).2 ≤
      (3 * fuel.length + 3 * source.numNodes + 12) * certificate.length + 3 * source.numNodes + 6 :=
  checkStreamRun_cost_le fuel source target certificate

/-! ### Actual first return, whole-output converse and exact typed time -/

theorem run_localRun (regs : Registers R) (fuel : Bits) (certificate source target : Word)
    (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (runSteps fuel certificate source target)
      (entry regs fuel certificate source target ctx) (runResult regs fuel certificate source target ctx) :=
  phase_localRun caller inspectPhase (cleanData fuel certificate source target) regs ctx

theorem run (regs : Registers R) (fuel : Bits) (certificate source target : Word)
    (ctx : ∀ k, List (Γ k)) :
    (next caller)^[runSteps fuel certificate source target]
      (some (entry regs fuel certificate source target ctx)) =
        some (runResult regs fuel certificate source target ctx) :=
  LocalRun.iterate caller (run_localRun caller regs fuel certificate source target ctx)

theorem run_firstRun (regs : Registers R) (fuel : Bits) (certificate source target : Word)
    (ctx : ∀ k, List (Γ k)) :
    FirstRun caller (entry regs fuel certificate source target ctx)
      (runSteps fuel certificate source target) (runResult regs fuel certificate source target ctx) :=
  phase_firstRun caller inspectPhase (cleanData fuel certificate source target) regs ctx

theorem run_firstResult_iff (regs : Registers R) (fuel : Bits) (certificate source target : Word)
    (ctx : ∀ k, List (Γ k)) (result : Bool) :
    FirstResult caller (entry regs fuel certificate source target ctx) result ↔
      (runEvaluation fuel certificate source target).result = result :=
  phase_firstResult_iff caller inspectPhase (cleanData fuel certificate source target) regs ctx result

/-- Any actual first output has the complete canonical data, original external
frame, exact physical clock and the paid full-register reset. -/
theorem run_complete_first_output (regs : Registers R) (fuel : Bits)
    (certificate source target : Word) (ctx : ∀ k, List (Γ k))
    (ticks : Nat) (finish : Cfg Γ Λ R)
    (first : FirstRun caller (entry regs fuel certificate source target ctx) ticks finish) :
    ticks = runSteps fuel certificate source target ∧
      finish = cfg (some (resultLabel (runEvaluation fuel certificate source target).result))
        (resetAll regs) (runEvaluation fuel certificate source target).data ctx := by
  have canonical := run_firstRun caller regs fuel certificate source target ctx
  exact LocalRun.first_unique caller
    (LocalRun.of_iterate caller first.1 first.2.2)
    (LocalRun.of_iterate caller canonical.1 canonical.2.2) first.2.1 canonical.2.1

/-- Both Boolean outcomes are characterized by actual first-return evidence. -/
theorem represented_firstResult_iff (regs : Registers R) (fuel : Bits) (certificate : Word)
    (source target : BinaryTree Unit) (ctx : ∀ k, List (Γ k)) (result : Bool) :
    FirstResult caller (entry regs fuel certificate (treeCode source) (treeCode target) ctx) result ↔
      (checkStreamRun fuel source target certificate).1 = result := by
  rw [run_firstResult_iff, runEvaluation_code_value]

/-- Recognition retains the literal original certificate and the actual source
move sequence, with the binary-fuel value used only in the theorem. -/
theorem represented_accepts_iff (regs : Registers R) (fuel : Bits) (certificate : Word)
    (source target : BinaryTree Unit) (ctx : ∀ k, List (Γ k)) :
    FirstResult caller (entry regs fuel certificate (treeCode source) (treeCode target) ctx) true ↔
      ∃ moves, certificate = certCode moves ∧ Trees.Rotations.applyMoves? moves source = some target ∧
        moves.length ≤ Resources.BinaryCounter.value fuel := by
  rw [represented_firstResult_iff, checkStreamRun_iff]

/-- The complete first-output converse cancels no physical information: the
source Boolean, exact machine clock and all nine returned words occur together. -/
theorem represented_complete_first_output (regs : Registers R) (fuel : Bits)
    (certificate : Word) (source target : BinaryTree Unit) (ctx : ∀ k, List (Γ k))
    (ticks : Nat) (finish : Cfg Γ Λ R)
    (first : FirstRun caller (entry regs fuel certificate (treeCode source) (treeCode target) ctx)
      ticks finish) :
    ticks = runSteps fuel certificate (treeCode source) (treeCode target) ∧
      finish = cfg (some (resultLabel (checkStreamRun fuel source target certificate).1))
        (resetAll regs) (runEvaluation fuel certificate (treeCode source) (treeCode target)).data ctx := by
  have actual := run_complete_first_output caller regs fuel certificate (treeCode source) (treeCode target)
    ctx ticks finish first
  simpa only [runEvaluation_code_value] using actual

def runInTimeExact (regs : Registers R) (fuel : Bits) (certificate source target : Word)
    (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller) (entry regs fuel certificate source target ctx)
      (some (runResult regs fuel certificate source target ctx))
      (runSteps fuel certificate source target) where
  steps := runSteps fuel certificate source target
  evals_in_steps := run caller regs fuel certificate source target ctx
  steps_le_m := Nat.le_refl _

def runInPolynomialTime (regs : Registers R) (fuel : Bits) (certificate source target : Word)
    (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller) (entry regs fuel certificate source target ctx)
      (some (runResult regs fuel certificate source target ctx))
      ((2 * fuel.length + 3 * source.length + 7) * certificate.length + source.length + 4) where
  steps := runSteps fuel certificate source target
  evals_in_steps := run caller regs fuel certificate source target ctx
  steps_le_m := runSteps_le fuel certificate source target

def representedInTimeExact (regs : Registers R) (fuel : Bits) (certificate : Word)
    (source target : BinaryTree Unit) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller)
      (entry regs fuel certificate (treeCode source) (treeCode target) ctx)
      (some (runResult regs fuel certificate (treeCode source) (treeCode target) ctx))
      (runSteps fuel certificate (treeCode source) (treeCode target)) :=
  runInTimeExact caller regs fuel certificate (treeCode source) (treeCode target) ctx

def representedInPolynomialTime (regs : Registers R) (fuel : Bits) (certificate : Word)
    (source target : BinaryTree Unit) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller)
      (entry regs fuel certificate (treeCode source) (treeCode target) ctx)
      (some (runResult regs fuel certificate (treeCode source) (treeCode target) ctx))
      ((2 * fuel.length + 6 * source.numNodes + 10) * certificate.length + 2 * source.numNodes + 5) where
  steps := runSteps fuel certificate (treeCode source) (treeCode target)
  evals_in_steps := run caller regs fuel certificate (treeCode source) (treeCode target) ctx
  steps_le_m := runSteps_code_le fuel certificate source target

@[simp] theorem runInTimeExact_steps (regs : Registers R) (fuel : Bits)
    (certificate source target : Word) (ctx : ∀ k, List (Γ k)) :
    (runInTimeExact caller regs fuel certificate source target ctx).steps =
      runSteps fuel certificate source target := rfl

@[simp] theorem runInPolynomialTime_steps (regs : Registers R) (fuel : Bits)
    (certificate source target : Word) (ctx : ∀ k, List (Γ k)) :
    (runInPolynomialTime caller regs fuel certificate source target ctx).steps =
      runSteps fuel certificate source target := rfl

@[simp] theorem representedInPolynomialTime_steps (regs : Registers R) (fuel : Bits)
    (certificate : Word) (source target : BinaryTree Unit) (ctx : ∀ k, List (Γ k)) :
    (representedInPolynomialTime caller regs fuel certificate source target ctx).steps =
      runSteps fuel certificate (treeCode source) (treeCode target) := rfl

/-- The accepting represented first return is a live Boolean label with empty
certificate/tree/auxiliary words and its actual remaining fixed-width fuel. -/
theorem represented_accepting_endpoint (regs : Registers R) (fuel : Bits)
    (certificate : Word) (source target : BinaryTree Unit) (ctx : ∀ k, List (Γ k))
    (accepted : (checkStreamRun fuel source target certificate).1 = true) :
    ∃ finalFuel,
      FirstRun caller (entry regs fuel certificate (treeCode source) (treeCode target) ctx)
        (runSteps fuel certificate (treeCode source) (treeCode target))
        (cfg (some (resultLabel true)) (resetAll regs) (cleanData finalFuel [] [] []) ctx) ∧
      finalFuel.length = fuel.length := by
  have actual : (runEvaluation fuel certificate (treeCode source) (treeCode target)).result = true :=
    (runEvaluation_code_value fuel certificate source target).trans accepted
  obtain ⟨finalFuel, data, width⟩ :=
    run_accept_cleanup fuel certificate (treeCode source) (treeCode target) actual
  refine ⟨finalFuel, ?_, width⟩
  have run := run_firstRun caller regs fuel certificate (treeCode source) (treeCode target) ctx
  simpa only [runResult, evaluationCfg, actual, data] using run


/-! ### Clean specialization of the explicit all-state physical allowance -/

section CleanSpace
variable [Fintype K]

omit [DecidableEq K] in
@[simp] theorem mass_cleanData (fuel : Bits) (certificate source target : Word)
    (ctx : ∀ k, List (Γ k)) :
    mass (cleanData fuel certificate source target) ctx =
      certificate.length + source.length + fuel.length + target.length + contextCells ctx := by
  simp only [mass, localCells, cleanData, List.length_nil, Nat.add_zero]

omit [DecidableEq K] in
@[simp] theorem hAllowance_cleanData (fuel : Bits) (certificate source target : Word)
    (ctx : ∀ k, List (Γ k)) :
    hAllowance (MoveApplyMachine.movePhase .start) (cleanData fuel certificate source target) ctx =
      certificate.length + 2 * source.length + fuel.length + target.length + contextCells ctx := by
  rw [hAllowance, mass_cleanData]
  dsimp only [MoveApplyMachine.phaseDebt, MoveApplyMachine.phaseCredit,
    MoveApplyMachine.movePhase, MoveParserMachine.phaseDebt, applyData, cleanData]
  omega

omit [DecidableEq K] in
private theorem clean_inspectAllowance_aux (size : Nat) :
    ∀ certificate : Word, certificate.length = size → ∀ fuel : Bits, ∀ source target : Word,
      ∀ ctx : ∀ k, List (Γ k),
        inspectAllowance (cleanData fuel certificate source target) ctx ≤
          certificate.length + 2 * source.length + fuel.length + target.length + contextCells ctx := by
  induction size using Nat.strong_induction_on with
  | h size ih =>
      intro certificate sized fuel source target ctx
      have initial : mass (cleanData fuel certificate source target) ctx ≤
          certificate.length + 2 * source.length + fuel.length + target.length + contextCells ctx := by
        rw [mass_cleanData]
        omega
      by_cases empty : certificate = []
      · have emptyData : (cleanData fuel certificate source target).certificate = [] := empty
        rw [inspectAllowance, ite_eq_left emptyData]
        exact initial
      · have nonemptyData : (cleanData fuel certificate source target).certificate ≠ [] := empty
        rw [inspectAllowance, ite_eq_right nonemptyData, counterFinish_clean]
        cases predecessor : (Resources.BinaryCounter.decFixedRun fuel).1 with
        | none =>
            rw [Resources.BinaryCounter.FixedWidthMachine.predSpec_of_none predecessor]
            exact initial
        | some nextFuel =>
            rw [Resources.BinaryCounter.FixedWidthMachine.predSpec_of_some predecessor]
            dsimp only
            have width := Resources.BinaryCounter.decFixedRun_some_length predecessor
            have component : hAllowance (MoveApplyMachine.movePhase .start)
                (cleanData nextFuel certificate source target) ctx ≤
                certificate.length + 2 * source.length + fuel.length + target.length + contextCells ctx := by
              rw [hAllowance_cleanData, width]
            rw [applyFinish_clean]
            dsimp only
            cases returned : (MoveApplyMachine.evaluate (MoveApplyMachine.movePhase .start)
                (moveCleanData certificate source)).result with
            | inl token =>
                exact max_le initial component
            | inr result => cases result with
              | failure =>
                  exact max_le initial component
              | success =>
                  obtain ⟨move, rest, output, parsed, actual, length, consumed, fewer⟩ :=
                    move_clean_success certificate source returned
                  rw [actual]
                  have later := ih rest.length (by omega) rest rfl nextFuel output target ctx
                  rw [length, width] at later
                  have continued : inspectAllowance (cleanData nextFuel rest output target) ctx ≤
                      certificate.length + 2 * source.length + fuel.length + target.length + contextCells ctx := by
                    omega
                  exact max_le initial (max_le component continued)

omit [DecidableEq K] in
/-- The clean closed space bound follows from the meaningful dirty allowance,
using actual returned fuel width, source length and shorter certificate data. -/
theorem inspectAllowance_clean_le (fuel : Bits) (certificate source target : Word)
    (ctx : ∀ k, List (Γ k)) :
    inspectAllowance (cleanData fuel certificate source target) ctx ≤
      certificate.length + 2 * source.length + fuel.length + target.length + contextCells ctx :=
  clean_inspectAllowance_aux certificate.length certificate rfl fuel source target ctx

/-- Every actual inclusive clean prefix has the fixed closed physical bound.
The underlying arbitrary-state theorem uses its independently defined allowance. -/
theorem run_prefix_cells (regs : Registers R) (fuel : Bits)
    (certificate source target : Word) (ctx : ∀ k, List (Γ k))
    (n : Nat) (bound : n ≤ runSteps fuel certificate source target)
    (reached : Cfg Γ Λ R)
    (executed : (next caller)^[n] (some (entry regs fuel certificate source target ctx)) =
      some reached) :
    stackCells reached ≤ certificate.length + 2 * source.length + fuel.length +
      target.length + contextCells ctx := by
  have actual := prefix_stackCells_le_dirty caller
    (entry regs fuel certificate source target ctx) n
    (by simpa only [remainingSteps_entry] using bound) reached executed
  rw [entry, allowance_phase_cfg] at actual
  exact actual.trans (inspectAllowance_clean_le fuel certificate source target ctx)

/-- The represented physical bound retains target storage and every protected
physical cell, and holds at the actual first result as well as earlier prefixes. -/
theorem represented_prefix_cells (regs : Registers R) (fuel : Bits) (certificate : Word)
    (s t : BinaryTree Unit) (ctx : ∀ k, List (Γ k))
    (n : Nat) (bound : n ≤ runSteps fuel certificate (treeCode s) (treeCode t))
    (reached : Cfg Γ Λ R)
    (executed : (next caller)^[n]
      (some (entry regs fuel certificate (treeCode s) (treeCode t) ctx)) = some reached) :
    stackCells reached ≤ certificate.length + 2 * (2 * s.numNodes + 1) + fuel.length +
      (2 * t.numNodes + 1) + contextCells ctx := by
  simpa only [treeCode_length] using
    run_prefix_cells caller regs fuel certificate (treeCode s) (treeCode t) ctx n bound reached executed

end CleanSpace


/-! ### Actual universal malformed-family prefixes, endpoints and clocks -/

/-- The complete clean Fuel stage ends at its owned positive join. -/
theorem inspectStageFinish_clean_positive (fuel nextFuel : Bits) (certificate source target : Word)
    (nonempty : certificate ≠ [])
    (decremented : (Resources.BinaryCounter.decFixedRun fuel).1 = some nextFuel) :
    inspectStageFinish (cleanData fuel certificate source target) =
      ⟨.positive, cleanData nextFuel certificate source target,
        1 + Resources.BinaryCounter.FixedWidthMachine.runSteps fuel⟩ := by
  cases certificate with
  | nil => exact False.elim (nonempty rfl)
  | cons tag raw =>
      change (let actual := counterFinish .borrow (cleanData fuel (tag :: raw) source target)
        (⟨FuelDispatchMachine.exitOfResult actual.result, actual.data, 1 + actual.steps⟩ :
          InspectStageFinish)) = _
      rw [counterFinish_clean, Resources.BinaryCounter.FixedWidthMachine.predSpec_of_some decremented]
      rfl

/-- Inspection, the actual predecessor and the paid positive join enter the
already installed MoveApply start without moving any other physical word. -/
theorem paid_apply_entry_localRun (regs : Registers R) (fuel nextFuel : Bits)
    (certificate source target : Word) (ctx : ∀ k, List (Γ k))
    (nonempty : certificate ≠ [])
    (decremented : (Resources.BinaryCounter.decFixedRun fuel).1 = some nextFuel) :
    LocalRun caller (Resources.BinaryCounter.FixedWidthMachine.runSteps fuel + 2)
      (entry regs fuel certificate source target ctx)
      (cfg (some (phaseLabel (applyPhase (MoveApplyMachine.movePhase .start))))
        (resetAll regs) (cleanData nextFuel certificate source target) ctx) := by
  have first := inspect_stage_localRun caller (cleanData fuel certificate source target) regs ctx
  rw [inspectStageFinish_clean_positive fuel nextFuel certificate source target nonempty decremented] at first
  have last := fuel_join_localRun caller .positive (cleanData nextFuel certificate source target)
    (resetFuel regs) ctx
  have combined := LocalRun.trans caller first last
  change LocalRun caller (1 + Resources.BinaryCounter.FixedWidthMachine.runSteps fuel + 1)
    (entry regs fuel certificate source target ctx)
    (cfg (some (phaseLabel (applyPhase (MoveApplyMachine.movePhase .start))))
      (resetAll regs) (cleanData nextFuel certificate source target) ctx) at combined
  convert combined using 1
  omega

/-- Four actual activations reach H.start for the fixed one-bit positive fuel. -/
theorem one_fuel_apply_entry_localRun (regs : Registers R) (certificate source target : Word)
    (ctx : ∀ k, List (Γ k)) (nonempty : certificate ≠ []) :
    LocalRun caller 4 (entry regs [true] certificate source target ctx)
      (cfg (some (phaseLabel (applyPhase (MoveApplyMachine.movePhase .start))))
        (resetAll regs) (cleanData [false] certificate source target) ctx) :=
  paid_apply_entry_localRun caller regs [true] [false] certificate source target ctx nonempty rfl

/-- The left malformed family retains an arbitrary untouched certificate suffix
and target. Its H failure is followed by the real final paid Stream join. -/
theorem left_nodes_run (certificateRest : Word) (n : Nat) (target : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (3 * n + 13)
      (entry regs [true] (moveCode ⟨.left, []⟩ ++ certificateRest)
        (List.replicate n nodeTag) target ctx)
      (cfg (some (resultLabel false)) (resetAll regs)
        (cleanData [false] certificateRest (List.replicate n nodeTag) target) ctx) := by
  let localCaller : MoveApplyMachine.External (ApplyCallerLabel Λ) → ApplyStatement Γ Λ R := fun _ => .halt
  let frame := cleanData [false] [] [] target
  have inner := MoveApplyMachine.left_nodes_run localCaller certificateRest n
    (applyRegisterEquiv.symm (resetAll regs)) (applyContext frame ctx)
  have middle := apply_localRun_transport caller localCaller inner
  simp only [MoveApplyMachine.entry, applyCfg_partial] at middle
  change LocalRun caller (3 * n + 8)
    (cfg (some (phaseLabel (applyPhase (MoveApplyMachine.movePhase .start)))) (resetAll regs)
      (cleanData [false] (moveCode ⟨.left, []⟩ ++ certificateRest) (List.replicate n nodeTag) target) ctx)
    (cfg (some (phaseLabel (applyJoinPhase MoveApplyMachine.rotationFailure))) (resetAll regs)
      (cleanData [false] certificateRest (List.replicate n nodeTag) target) ctx) at middle
  have first := one_fuel_apply_entry_localRun caller regs
    (moveCode ⟨.left, []⟩ ++ certificateRest) (List.replicate n nodeTag) target ctx (by simp [moveCode])
  have last := apply_join_localRun caller MoveApplyMachine.rotationFailure
    (cleanData [false] certificateRest (List.replicate n nodeTag) target) (resetAll regs) ctx
  have combined := LocalRun.trans caller (LocalRun.trans caller first middle) last
  simp only [MoveApplyMachine.rotationFailure, applyJoinTarget, resetAll_resetAll] at combined
  convert combined using 1
  omega

/-- The right malformed family has a distinct physical clock, including m=0. -/
theorem right_nodes_run (certificateRest : Word) (m : Nat) (target : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (3 * m + 16)
      (entry regs [true] (moveCode ⟨.right, []⟩ ++ certificateRest)
        (List.replicate (m + 2) nodeTag) target ctx)
      (cfg (some (resultLabel false)) (resetAll regs)
        (cleanData [false] certificateRest (List.replicate (m + 2) nodeTag) target) ctx) := by
  let localCaller : MoveApplyMachine.External (ApplyCallerLabel Λ) → ApplyStatement Γ Λ R := fun _ => .halt
  let frame := cleanData [false] [] [] target
  have inner := MoveApplyMachine.right_nodes_run localCaller certificateRest m
    (applyRegisterEquiv.symm (resetAll regs)) (applyContext frame ctx)
  have middle := apply_localRun_transport caller localCaller inner
  simp only [MoveApplyMachine.entry, applyCfg_partial] at middle
  change LocalRun caller (3 * m + 11)
    (cfg (some (phaseLabel (applyPhase (MoveApplyMachine.movePhase .start)))) (resetAll regs)
      (cleanData [false] (moveCode ⟨.right, []⟩ ++ certificateRest) (List.replicate (m + 2) nodeTag) target) ctx)
    (cfg (some (phaseLabel (applyJoinPhase MoveApplyMachine.rotationFailure))) (resetAll regs)
      (cleanData [false] certificateRest (List.replicate (m + 2) nodeTag) target) ctx) at middle
  have first := one_fuel_apply_entry_localRun caller regs
    (moveCode ⟨.right, []⟩ ++ certificateRest) (List.replicate (m + 2) nodeTag) target ctx (by simp [moveCode])
  have last := apply_join_localRun caller MoveApplyMachine.rotationFailure
    (cleanData [false] certificateRest (List.replicate (m + 2) nodeTag) target) (resetAll regs) ctx
  have combined := LocalRun.trans caller (LocalRun.trans caller first middle) last
  simp only [MoveApplyMachine.rotationFailure, applyJoinTarget, resetAll_resetAll] at combined
  convert combined using 1
  omega

theorem left_nodes_drop (certificateRest : Word) (n : Nat) (target : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (2 * n + 10)
      (entry regs [true] (moveCode ⟨.left, []⟩ ++ certificateRest)
        (List.replicate n nodeTag) target ctx)
      (cfg (some (phaseLabel (applyPhase (MoveApplyMachine.positionPhase .dropPending))))
        (resetAll regs)
        { (cleanData [false] certificateRest (List.replicate n nodeTag) target) with
          units := List.replicate n () } ctx) := by
  let localCaller : MoveApplyMachine.External (ApplyCallerLabel Λ) → ApplyStatement Γ Λ R := fun _ => .halt
  let frame := cleanData [false] [] [] target
  have inner := MoveApplyMachine.left_nodes_drop localCaller certificateRest n
    (applyRegisterEquiv.symm (resetAll regs)) (applyContext frame ctx)
  have middle := apply_localRun_transport caller localCaller inner
  simp only [MoveApplyMachine.entry, applyCfg_partial] at middle
  change LocalRun caller (2 * n + 6)
    (cfg (some (phaseLabel (applyPhase (MoveApplyMachine.movePhase .start)))) (resetAll regs)
      (cleanData [false] (moveCode ⟨.left, []⟩ ++ certificateRest) (List.replicate n nodeTag) target) ctx)
    (cfg (some (phaseLabel (applyPhase (MoveApplyMachine.positionPhase .dropPending)))) (resetAll regs)
      { (cleanData [false] certificateRest (List.replicate n nodeTag) target) with
        units := List.replicate n () } ctx) at middle
  have first := one_fuel_apply_entry_localRun caller regs
    (moveCode ⟨.left, []⟩ ++ certificateRest) (List.replicate n nodeTag) target ctx (by simp [moveCode])
  have combined := LocalRun.trans caller first middle
  convert combined using 1
  omega

theorem right_nodes_drop (certificateRest : Word) (m : Nat) (target : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (2 * m + 12)
      (entry regs [true] (moveCode ⟨.right, []⟩ ++ certificateRest)
        (List.replicate (m + 2) nodeTag) target ctx)
      (cfg (some (phaseLabel (applyPhase (MoveApplyMachine.positionPhase .dropPending))))
        (resetAll regs)
        { (cleanData [false] certificateRest (List.replicate (m + 2) nodeTag) target) with
          units := List.replicate (m + 1) () } ctx) := by
  let localCaller : MoveApplyMachine.External (ApplyCallerLabel Λ) → ApplyStatement Γ Λ R := fun _ => .halt
  let frame := cleanData [false] [] [] target
  have inner := MoveApplyMachine.right_nodes_drop localCaller certificateRest m
    (applyRegisterEquiv.symm (resetAll regs)) (applyContext frame ctx)
  have middle := apply_localRun_transport caller localCaller inner
  simp only [MoveApplyMachine.entry, applyCfg_partial] at middle
  change LocalRun caller (2 * m + 8)
    (cfg (some (phaseLabel (applyPhase (MoveApplyMachine.movePhase .start)))) (resetAll regs)
      (cleanData [false] (moveCode ⟨.right, []⟩ ++ certificateRest) (List.replicate (m + 2) nodeTag) target) ctx)
    (cfg (some (phaseLabel (applyPhase (MoveApplyMachine.positionPhase .dropPending)))) (resetAll regs)
      { (cleanData [false] certificateRest (List.replicate (m + 2) nodeTag) target) with
        units := List.replicate (m + 1) () } ctx) at middle
  have first := one_fuel_apply_entry_localRun caller regs
    (moveCode ⟨.right, []⟩ ++ certificateRest) (List.replicate (m + 2) nodeTag) target ctx (by simp [moveCode])
  have combined := LocalRun.trans caller first middle
  convert combined using 1
  omega

include caller in
theorem left_nodes_exact_clock (certificateRest : Word) (n : Nat) (target : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    runSteps [true] (moveCode ⟨.left, []⟩ ++ certificateRest) (List.replicate n nodeTag) target =
      3 * n + 13 :=
  (LocalRun.phaseEndpoint caller (q := inspectPhase)
    (left_nodes_run caller certificateRest n target regs ctx)).1

include caller in
theorem right_nodes_exact_clock (certificateRest : Word) (m : Nat) (target : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    runSteps [true] (moveCode ⟨.right, []⟩ ++ certificateRest) (List.replicate (m + 2) nodeTag) target =
      3 * m + 16 :=
  (LocalRun.phaseEndpoint caller (q := inspectPhase)
    (right_nodes_run caller certificateRest m target regs ctx)).1

include caller in
theorem left_nodes_drop_rank (certificateRest : Word) (n : Nat) (target : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    remainingSteps (cfg (some (phaseLabel (applyPhase (MoveApplyMachine.positionPhase .dropPending))))
      (resetAll regs) { (cleanData [false] certificateRest (List.replicate n nodeTag) target) with
        units := List.replicate n () } ctx : Cfg Γ Λ R) = n + 3 := by
  have rank := LocalRun.remaining caller (left_nodes_drop caller certificateRest n target regs ctx)
  change runSteps [true] (moveCode ⟨.left, []⟩ ++ certificateRest) (List.replicate n nodeTag) target = _ at rank
  rw [left_nodes_exact_clock caller certificateRest n target regs ctx] at rank
  omega

include caller in
theorem right_nodes_drop_rank (certificateRest : Word) (m : Nat) (target : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    remainingSteps (cfg (some (phaseLabel (applyPhase (MoveApplyMachine.positionPhase .dropPending))))
      (resetAll regs) { (cleanData [false] certificateRest (List.replicate (m + 2) nodeTag) target) with
        units := List.replicate (m + 1) () } ctx : Cfg Γ Λ R) = m + 4 := by
  have rank := LocalRun.remaining caller (right_nodes_drop caller certificateRest m target regs ctx)
  change runSteps [true] (moveCode ⟨.right, []⟩ ++ certificateRest) (List.replicate (m + 2) nodeTag) target = _ at rank
  rw [right_nodes_exact_clock caller certificateRest m target regs ctx] at rank
  omega

section SharpSpace
variable [Fintype K]

/-- The clean Fuel prefix conserves the actual sum of every physical store,
including the protected source/target and all external words. -/
theorem clean_fuel_prefix_cells (regs : Registers R) (fuel : Bits)
    (certificate source target : Word) (ctx : ∀ k, List (Γ k))
    (nonempty : certificate ≠ []) (n : Nat)
    (bound : n ≤ Resources.BinaryCounter.FixedWidthMachine.runSteps fuel + 1)
    (reached : Cfg Γ Λ R)
    (executed : (next caller)^[n] (some (entry regs fuel certificate source target ctx)) = some reached) :
    stackCells reached = mass (cleanData fuel certificate source target) ctx := by
  let D := cleanData fuel certificate source target
  let localCaller : (FuelDispatchMachine.Exit ⊕ FuelCallerLabel Λ) → FuelStatement Γ Λ R := fun _ => .halt
  let start : FuelCfg Γ Λ R := FuelDispatchMachine.cfg (some FuelDispatchMachine.inspectLabel)
    regs fuel [] certificate (fuelContext D ctx)
  have startMap : fuelCfg start = entry regs fuel certificate source target ctx := by
    change fuelCfg (fuelView (some FuelDispatchMachine.inspectLabel) regs D ctx) = _
    rw [fuelCfg_view]
    rfl
  have clock : FuelDispatchMachine.dispatchSteps fuel certificate =
      Resources.BinaryCounter.FixedWidthMachine.runSteps fuel + 1 := by
    cases certificate with
    | nil => exact False.elim (nonempty rfl)
    | cons tag raw => rfl
  obtain ⟨middle, run, rank, path, owned, reset⟩ :=
    FuelDispatchMachine.dispatch_prefix localCaller fuel certificate regs (fuelContext D ctx) n (by omega)
  have earlier : ∀ j, j < n → ∃ reached,
      (FuelDispatchMachine.next localCaller)^[j] (some start) = some reached ∧
        FuelDispatchMachine.Owned reached.l := by
    intro j strict
    obtain ⟨reached, run, rank, path, owned, reset⟩ :=
      FuelDispatchMachine.dispatch_prefix localCaller fuel certificate regs (fuelContext D ctx) j (by omega)
    exact ⟨reached, run, owned.mp (by omega)⟩
  have transported := fuel_prefix_transport caller localCaller n start earlier
  change (FuelDispatchMachine.next localCaller)^[n] (some start) = some middle at run
  rw [startMap, run] at transported
  simp only [Option.map_some] at transported
  have same : reached = fuelCfg middle := Option.some.inj (executed.symm.trans transported)
  rw [same, stackCells_fuelCfg]
  have cells := (FuelDispatchMachine.local_reaches_preserves localCaller path).2.2.2
  change FuelDispatchMachine.stackCells middle = FuelDispatchMachine.stackCells start at cells
  rw [cells, ← stackCells_fuelCfg start, startMap]
  exact stackCells_cfg _ _ _ _

/-- The paid positive join preserves cells too; the one-bit prefix has exactly
four actual activations and constant complete physical mass. -/
theorem one_fuel_prefix_cells (regs : Registers R) (certificate source target : Word)
    (ctx : ∀ k, List (Γ k)) (nonempty : certificate ≠ []) (n : Nat)
    (bound : n ≤ 4) (reached : Cfg Γ Λ R)
    (executed : (next caller)^[n] (some (entry regs [true] certificate source target ctx)) = some reached) :
    stackCells reached = mass (cleanData [true] certificate source target) ctx := by
  by_cases early : n ≤ 3
  · exact clean_fuel_prefix_cells caller regs [true] certificate source target ctx
      nonempty n early reached executed
  · have four : n = 4 := by omega
    subst n
    have actual := LocalRun.iterate caller
      (one_fuel_apply_entry_localRun caller regs certificate source target ctx nonempty)
    have same := Option.some.inj (executed.symm.trans actual)
    rw [same, stackCells_cfg, mass_cleanData, mass_cleanData]
    rfl

/-- Transport an arbitrary quantitative prefix fact of the actual installed H
program. Strict earlier ownership follows from its real remaining clock. -/
theorem apply_prefix_bound
    (localCaller : MoveApplyMachine.External (ApplyCallerLabel Λ) → ApplyStatement Γ Λ R)
    (start : ApplyCfg Γ Λ R) (ticks peak : Nat)
    (clock : ticks ≤ MoveApplyMachine.remainingSteps start)
    (cells : ∀ j, j ≤ ticks → ∀ reached,
      (MoveApplyMachine.next localCaller)^[j] (some start) = some reached →
        MoveApplyMachine.stackCells reached ≤ peak)
    (n : Nat) (bound : n ≤ ticks) (reached : Cfg Γ Λ R)
    (executed : (next caller)^[n] (some (applyCfg start)) = some reached) :
    stackCells reached ≤ peak := by
  obtain ⟨middle, run, rank, path, owned⟩ :=
    MoveApplyMachine.owned_prefix localCaller start n (by omega)
  have earlier : ∀ j, j < n → ∃ reached,
      (MoveApplyMachine.next localCaller)^[j] (some start) = some reached ∧
        MoveApplyMachine.Owned reached.l := by
    intro j strict
    exact MoveApplyMachine.LocalRun.owned_prefix localCaller
      (MoveApplyMachine.cfg_localRun localCaller start) j (by omega)
  have transported := apply_prefix_transport caller localCaller n start earlier
  rw [run] at transported
  simp only [Option.map_some] at transported
  have same : reached = applyCfg middle := Option.some.inj (executed.symm.trans transported)
  rw [same, stackCells_applyCfg]
  exact cells n bound middle run

omit [DecidableEq K] in
theorem left_nodes_drop_cells (certificateRest : Word) (n : Nat) (target : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    stackCells (cfg (some (phaseLabel (applyPhase (MoveApplyMachine.positionPhase .dropPending))))
      regs { (cleanData [false] certificateRest (List.replicate n nodeTag) target) with
        units := List.replicate n () } ctx : Cfg Γ Λ R) =
      2 * n + certificateRest.length + 1 + target.length + contextCells ctx := by
  rw [stackCells_cfg]
  simp only [mass, localCells, cleanData, List.length_nil, List.length_cons, List.length_replicate]
  omega

omit [DecidableEq K] in
theorem right_nodes_drop_cells (certificateRest : Word) (m : Nat) (target : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    stackCells (cfg (some (phaseLabel (applyPhase (MoveApplyMachine.positionPhase .dropPending))))
      regs { (cleanData [false] certificateRest (List.replicate (m + 2) nodeTag) target) with
        units := List.replicate (m + 1) () } ctx : Cfg Γ Λ R) =
      2 * m + 3 + certificateRest.length + 1 + target.length + contextCells ctx := by
  rw [stackCells_cfg]
  simp only [mass, localCells, cleanData, List.length_nil, List.length_cons, List.length_replicate]
  omega

/-- Every actual prefix, including the paid final join, satisfies the left
family's sharp physical maximum. No tree-validity assumption is introduced. -/
theorem left_nodes_prefix_cells (certificateRest : Word) (n : Nat) (target : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) (j : Nat) (bound : j ≤ 3 * n + 13)
    (reached : Cfg Γ Λ R)
    (executed : (next caller)^[j]
      (some (entry regs [true] (moveCode ⟨.left, []⟩ ++ certificateRest)
        (List.replicate n nodeTag) target ctx)) = some reached) :
    stackCells reached ≤ max (n + 2) (2 * n) + certificateRest.length + 1 + target.length + contextCells ctx := by
  have nonempty : moveCode (⟨.left, []⟩ : RotationMove) ++ certificateRest ≠ [] := by simp [moveCode]
  by_cases early : j ≤ 4
  · have cells := one_fuel_prefix_cells caller regs
      (moveCode ⟨.left, []⟩ ++ certificateRest) (List.replicate n nodeTag) target ctx nonempty j early reached executed
    rw [cells, mass_cleanData]
    simp only [List.length_append, moveCode_length, List.length_nil, List.length_cons, List.length_replicate]
    have lower := Nat.le_max_left (n + 2) (2 * n)
    omega
  · by_cases middle : j ≤ 4 + (3 * n + 8)
    · let localCaller : MoveApplyMachine.External (ApplyCallerLabel Λ) → ApplyStatement Γ Λ R := fun _ => .halt
      let frame := cleanData [false] [] [] target
      let localStart : ApplyCfg Γ Λ R := MoveApplyMachine.entry (applyRegisterEquiv.symm (resetAll regs))
        (moveCode ⟨.left, []⟩ ++ certificateRest) [] (List.replicate n nodeTag) [] [] [] (applyContext frame ctx)
      have startMap : applyCfg localStart =
          cfg (some (phaseLabel (applyPhase (MoveApplyMachine.movePhase .start)))) (resetAll regs)
            (cleanData [false] (moveCode ⟨.left, []⟩ ++ certificateRest) (List.replicate n nodeTag) target) ctx := by
        simp only [localStart, MoveApplyMachine.entry, applyCfg_partial]
        rfl
      have after : (next caller)^[j - 4] (some (applyCfg localStart)) = some reached := by
        rw [startMap, ← prefix_iterate_after_localRun caller
          (one_fuel_apply_entry_localRun caller regs (moveCode ⟨.left, []⟩ ++ certificateRest)
            (List.replicate n nodeTag) target ctx nonempty) (j - 4)]
        simpa only [show 4 + (j - 4) = j by omega] using executed
      have clock : MoveApplyMachine.remainingSteps localStart = 3 * n + 8 :=
        MoveApplyMachine.left_nodes_exact_clock localCaller certificateRest n
          (applyRegisterEquiv.symm (resetAll regs)) (applyContext frame ctx)
      have cells := apply_prefix_bound caller localCaller localStart (3 * n + 8)
        (max (n + 2) (2 * n) + certificateRest.length + MoveApplyMachine.contextCells (applyContext frame ctx))
        (by omega)
        (MoveApplyMachine.left_nodes_prefix_cells localCaller certificateRest n
          (applyRegisterEquiv.symm (resetAll regs)) (applyContext frame ctx))
        (j - 4) (by omega) reached after
      rw [applyContext_cells] at cells
      dsimp only [frame, cleanData] at cells
      simp only [List.length_cons, List.length_nil] at cells
      omega
    · have final : j = 3 * n + 13 := by omega
      subst j
      have actual := LocalRun.iterate caller (left_nodes_run caller certificateRest n target regs ctx)
      have same := Option.some.inj (executed.symm.trans actual)
      rw [same, stackCells_cfg, mass_cleanData]
      simp only [List.length_replicate, List.length_cons, List.length_nil]
      have lower := Nat.le_max_left (n + 2) (2 * n)
      omega

/-- The right upper bound uses H's proved universal sharp bound, including its
small-input entry maximum and all later marker-restoration prefixes. -/
theorem right_nodes_prefix_cells (certificateRest : Word) (m : Nat) (target : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) (j : Nat) (bound : j ≤ 3 * m + 16)
    (reached : Cfg Γ Λ R)
    (executed : (next caller)^[j]
      (some (entry regs [true] (moveCode ⟨.right, []⟩ ++ certificateRest)
        (List.replicate (m + 2) nodeTag) target ctx)) = some reached) :
    stackCells reached ≤ max (m + 4) (2 * m + 3) + certificateRest.length + 1 + target.length + contextCells ctx := by
  have nonempty : moveCode (⟨.right, []⟩ : RotationMove) ++ certificateRest ≠ [] := by simp [moveCode]
  by_cases early : j ≤ 4
  · have cells := one_fuel_prefix_cells caller regs
      (moveCode ⟨.right, []⟩ ++ certificateRest) (List.replicate (m + 2) nodeTag) target ctx nonempty j early reached executed
    rw [cells, mass_cleanData]
    simp only [List.length_append, moveCode_length, List.length_nil, List.length_cons, List.length_replicate]
    have lower := Nat.le_max_left (m + 4) (2 * m + 3)
    omega
  · by_cases middle : j ≤ 4 + (3 * m + 11)
    · let localCaller : MoveApplyMachine.External (ApplyCallerLabel Λ) → ApplyStatement Γ Λ R := fun _ => .halt
      let frame := cleanData [false] [] [] target
      let localStart : ApplyCfg Γ Λ R := MoveApplyMachine.entry (applyRegisterEquiv.symm (resetAll regs))
        (moveCode ⟨.right, []⟩ ++ certificateRest) [] (List.replicate (m + 2) nodeTag) [] [] [] (applyContext frame ctx)
      have startMap : applyCfg localStart =
          cfg (some (phaseLabel (applyPhase (MoveApplyMachine.movePhase .start)))) (resetAll regs)
            (cleanData [false] (moveCode ⟨.right, []⟩ ++ certificateRest) (List.replicate (m + 2) nodeTag) target) ctx := by
        simp only [localStart, MoveApplyMachine.entry, applyCfg_partial]
        rfl
      have after : (next caller)^[j - 4] (some (applyCfg localStart)) = some reached := by
        rw [startMap, ← prefix_iterate_after_localRun caller
          (one_fuel_apply_entry_localRun caller regs (moveCode ⟨.right, []⟩ ++ certificateRest)
            (List.replicate (m + 2) nodeTag) target ctx nonempty) (j - 4)]
        simpa only [show 4 + (j - 4) = j by omega] using executed
      have clock : MoveApplyMachine.remainingSteps localStart = 3 * m + 11 :=
        MoveApplyMachine.right_nodes_exact_clock localCaller certificateRest m
          (applyRegisterEquiv.symm (resetAll regs)) (applyContext frame ctx)
      have cells := apply_prefix_bound caller localCaller localStart (3 * m + 11)
        (max (m + 4) (2 * m + 3) + certificateRest.length + MoveApplyMachine.contextCells (applyContext frame ctx))
        (by omega)
        (MoveApplyMachine.right_nodes_prefix_cells localCaller certificateRest m
          (applyRegisterEquiv.symm (resetAll regs)) (applyContext frame ctx))
        (j - 4) (by omega) reached after
      rw [applyContext_cells] at cells
      dsimp only [frame, cleanData] at cells
      simp only [List.length_cons, List.length_nil] at cells
      omega
    · have final : j = 3 * m + 16 := by omega
      subst j
      have actual := LocalRun.iterate caller (right_nodes_run caller certificateRest m target regs ctx)
      have same := Option.some.inj (executed.symm.trans actual)
      rw [same, stackCells_cfg, mass_cleanData]
      simp only [List.length_replicate, List.length_cons, List.length_nil]
      have lower := Nat.le_max_left (m + 4) (2 * m + 3)
      omega

/-- The complete exact maximum includes a universal inclusive-prefix upper
bound and an actual attaining prefix, for every n including zero. -/
theorem left_nodes_peak (certificateRest : Word) (n : Nat) (target : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (∀ j, j ≤ 3 * n + 13 → ∀ reached,
      (next caller)^[j] (some (entry regs [true] (moveCode ⟨.left, []⟩ ++ certificateRest)
        (List.replicate n nodeTag) target ctx)) = some reached →
      stackCells reached ≤ max (n + 2) (2 * n) + certificateRest.length + 1 + target.length + contextCells ctx) ∧
    ∃ j reached, j ≤ 3 * n + 13 ∧
      (next caller)^[j] (some (entry regs [true] (moveCode ⟨.left, []⟩ ++ certificateRest)
        (List.replicate n nodeTag) target ctx)) = some reached ∧
      stackCells reached = max (n + 2) (2 * n) + certificateRest.length + 1 + target.length + contextCells ctx := by
  refine ⟨left_nodes_prefix_cells caller certificateRest n target regs ctx, ?_⟩
  by_cases initial : 2 * n ≤ n + 2
  · refine ⟨0, entry regs [true] (moveCode ⟨.left, []⟩ ++ certificateRest)
      (List.replicate n nodeTag) target ctx, by omega, rfl, ?_⟩
    rw [entry, stackCells_cfg, mass_cleanData, Nat.max_eq_left initial]
    simp only [List.length_append, moveCode_length, List.length_nil, List.length_cons, List.length_replicate]
    omega
  · refine ⟨2 * n + 10,
      cfg (some (phaseLabel (applyPhase (MoveApplyMachine.positionPhase .dropPending)))) (resetAll regs)
        { (cleanData [false] certificateRest (List.replicate n nodeTag) target) with
          units := List.replicate n () } ctx,
      by omega, LocalRun.iterate caller (left_nodes_drop caller certificateRest n target regs ctx), ?_⟩
    rw [left_nodes_drop_cells, Nat.max_eq_right (by omega)]

/-- The right exact maximum retains its m=0 small-family split and the actual
later drop attainment; a drop-state equality alone would not prove this theorem. -/
theorem right_nodes_peak (certificateRest : Word) (m : Nat) (target : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (∀ j, j ≤ 3 * m + 16 → ∀ reached,
      (next caller)^[j] (some (entry regs [true] (moveCode ⟨.right, []⟩ ++ certificateRest)
        (List.replicate (m + 2) nodeTag) target ctx)) = some reached →
      stackCells reached ≤ max (m + 4) (2 * m + 3) + certificateRest.length + 1 + target.length + contextCells ctx) ∧
    ∃ j reached, j ≤ 3 * m + 16 ∧
      (next caller)^[j] (some (entry regs [true] (moveCode ⟨.right, []⟩ ++ certificateRest)
        (List.replicate (m + 2) nodeTag) target ctx)) = some reached ∧
      stackCells reached = max (m + 4) (2 * m + 3) + certificateRest.length + 1 + target.length + contextCells ctx := by
  refine ⟨right_nodes_prefix_cells caller certificateRest m target regs ctx, ?_⟩
  by_cases initial : 2 * m + 3 ≤ m + 4
  · refine ⟨0, entry regs [true] (moveCode ⟨.right, []⟩ ++ certificateRest)
      (List.replicate (m + 2) nodeTag) target ctx, by omega, rfl, ?_⟩
    rw [entry, stackCells_cfg, mass_cleanData, Nat.max_eq_left initial]
    simp only [List.length_append, moveCode_length, List.length_nil, List.length_cons, List.length_replicate]
    omega
  · refine ⟨2 * m + 12,
      cfg (some (phaseLabel (applyPhase (MoveApplyMachine.positionPhase .dropPending)))) (resetAll regs)
        { (cleanData [false] certificateRest (List.replicate (m + 2) nodeTag) target) with
          units := List.replicate (m + 1) () } ctx,
      by omega, LocalRun.iterate caller (right_nodes_drop caller certificateRest m target regs ctx), ?_⟩
    rw [right_nodes_drop_cells, Nat.max_eq_right (by omega)]


/-- The sharper parsed-call split retains the actual certificate suffix and
path length. This is the installed H segment through its owned result join;
it is not asserted to be the peak of the entire recursive Stream run. -/
theorem apply_clean_prefix_cells_of_some (fuel : Bits) (certificate source target : Word)
    (move : RotationMove) (rest : Word) (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (parsed : (parseMoveRun certificate).1 = some (move, rest)) (n : Nat)
    (bound : n ≤ MoveApplyMachine.runSteps certificate [] source [] [] []) (reached : Cfg Γ Λ R)
    (executed : (next caller)^[n]
      (some (cfg (some (phaseLabel (applyPhase (MoveApplyMachine.movePhase .start)))) regs
        (cleanData fuel certificate source target) ctx)) = some reached) :
    stackCells reached ≤ max (certificate.length + source.length)
      (rest.length + move.position.length + 2 * source.length) +
        fuel.length + target.length + contextCells ctx := by
  let D := cleanData fuel certificate source target
  let localCaller : MoveApplyMachine.External (ApplyCallerLabel Λ) → ApplyStatement Γ Λ R := fun _ => .halt
  let start : ApplyCfg Γ Λ R := MoveApplyMachine.entry (applyRegisterEquiv.symm regs)
    certificate [] source [] [] [] (applyContext D ctx)
  have startMap : applyCfg start =
      cfg (some (phaseLabel (applyPhase (MoveApplyMachine.movePhase .start)))) regs D ctx := by
    simp only [start, MoveApplyMachine.entry, applyCfg_partial]
    rfl
  have localBound := MoveApplyMachine.prefix_stackCells_le_of_some localCaller certificate move rest []
    source [] [] [] (applyRegisterEquiv.symm regs) (applyContext D ctx) parsed
  have cells := apply_prefix_bound caller localCaller start
    (MoveApplyMachine.runSteps certificate [] source [] [] [])
    (max (MoveApplyMachine.principalCells certificate [] source [] [] [] (applyContext D ctx))
      (MoveApplyMachine.parsedCellsBound move rest [] source [] [] [] (applyContext D ctx)))
    (Nat.le_refl _) localBound n bound reached (by simpa only [startMap] using executed)
  simp only [MoveApplyMachine.principalCells, MoveApplyMachine.parsedCellsBound,
    List.length_nil, Nat.add_zero, applyContext_cells, D, cleanData] at cells
  omega

end SharpSpace


/-! ### The same clean prefix carries staged registers and physical bounds -/

@[simp] theorem representedInTimeExact_steps (regs : Registers R) (fuel : Bits)
    (certificate : Word) (source target : BinaryTree Unit) (ctx : ∀ k, List (Γ k)) :
    (representedInTimeExact caller regs fuel certificate source target ctx).steps =
      runSteps fuel certificate (treeCode source) (treeCode target) := rfl

/-- The universal left-family endpoint is its actual first result. -/
theorem left_nodes_firstRun (certificateRest : Word) (n : Nat) (target : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    FirstRun caller
      (entry regs [true] (moveCode ⟨.left, []⟩ ++ certificateRest)
        (List.replicate n nodeTag) target ctx)
      (3 * n + 13)
      (cfg (some (resultLabel false)) (resetAll regs)
        (cleanData [false] certificateRest (List.replicate n nodeTag) target) ctx) := by
  have actual := left_nodes_run caller certificateRest n target regs ctx
  exact ⟨LocalRun.iterate caller actual, not_owned_result false,
    LocalRun.owned_prefix caller actual⟩

/-- The universal right-family endpoint is its actual first result. -/
theorem right_nodes_firstRun (certificateRest : Word) (m : Nat) (target : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    FirstRun caller
      (entry regs [true] (moveCode ⟨.right, []⟩ ++ certificateRest)
        (List.replicate (m + 2) nodeTag) target ctx)
      (3 * m + 16)
      (cfg (some (resultLabel false)) (resetAll regs)
        (cleanData [false] certificateRest (List.replicate (m + 2) nodeTag) target) ctx) := by
  have actual := right_nodes_run caller certificateRest m target regs ctx
  exact ⟨LocalRun.iterate caller actual, not_owned_result false,
    LocalRun.owned_prefix caller actual⟩

section CleanSharedPrefix
variable [Fintype K]

/-- One reached configuration carries the inclusive raw execution, exact
remaining clock, local closure, ownership, zero-time identity, exact staged
registers, caller state, complete protected frame, and clean physical bound. -/
theorem run_owned_prefix (regs : Registers R) (fuel : Bits)
    (certificate source target : Word) (ctx : ∀ k, List (Γ k))
    (n : Nat) (bound : n ≤ runSteps fuel certificate source target) :
    ∃ reached, (next caller)^[n]
        (some (entry regs fuel certificate source target ctx)) = some reached ∧
      remainingSteps reached = runSteps fuel certificate source target - n ∧
      Relation.ReflTransGen (LocalStep caller)
        (entry regs fuel certificate source target ctx) reached ∧
      (n < runSteps fuel certificate source target ↔ Owned reached.l) ∧
      (n = 0 → reached = entry regs fuel certificate source target ctx) ∧
      reached.var = registersAt (entry (Λ := Λ) regs fuel certificate source target ctx) n ∧
      reached.var.2.2 = regs.2.2 ∧
      (∀ k, reached.stk (.inr k) = ctx k) ∧
      stackCells reached ≤ certificate.length + 2 * source.length + fuel.length +
        target.length + contextCells ctx := by
  obtain ⟨reached, executed, rank, path, live, zero, staged, user, frame⟩ :=
    owned_prefix_frame caller (entry regs fuel certificate source target ctx) n
      (by simpa only [remainingSteps_entry] using bound)
  refine ⟨reached, executed, ?_, path, ?_, zero, staged, user, frame,
    run_prefix_cells caller regs fuel certificate source target ctx n bound reached executed⟩
  · simpa only [remainingSteps_entry] using rank
  · simpa only [remainingSteps_entry] using live

/-- The represented specialization retains the same actual prefix witness and
the full source/target physical lengths. -/
theorem represented_owned_prefix (regs : Registers R) (fuel : Bits) (certificate : Word)
    (s t : BinaryTree Unit) (ctx : ∀ k, List (Γ k))
    (n : Nat) (bound : n ≤ runSteps fuel certificate (treeCode s) (treeCode t)) :
    ∃ reached, (next caller)^[n]
        (some (entry regs fuel certificate (treeCode s) (treeCode t) ctx)) = some reached ∧
      remainingSteps reached = runSteps fuel certificate (treeCode s) (treeCode t) - n ∧
      Relation.ReflTransGen (LocalStep caller)
        (entry regs fuel certificate (treeCode s) (treeCode t) ctx) reached ∧
      (n < runSteps fuel certificate (treeCode s) (treeCode t) ↔ Owned reached.l) ∧
      (n = 0 → reached = entry regs fuel certificate (treeCode s) (treeCode t) ctx) ∧
      reached.var = registersAt (entry (Λ := Λ) regs fuel certificate (treeCode s) (treeCode t) ctx) n ∧
      reached.var.2.2 = regs.2.2 ∧
      (∀ k, reached.stk (.inr k) = ctx k) ∧
      stackCells reached ≤ certificate.length + 2 * (2 * s.numNodes + 1) + fuel.length +
        (2 * t.numNodes + 1) + contextCells ctx := by
  simpa only [treeCode_length] using
    run_owned_prefix caller regs fuel certificate (treeCode s) (treeCode t) ctx n bound

end CleanSharedPrefix

end Resources.RotationCertificate.StreamMachine
-- END COMPLETE SOURCE SUFFIX6

-- BEGIN INSTALLED SHARED PREFIX1
namespace Resources.RotationCertificate.StreamMachine

variable {K Λ R K' Λ' R' : Type} {Γ : K → Type} {Γ' : K' → Type}
variable (names : StackId K ≃ K') (symbols : ∀ k, alphabet Γ k ≃ Γ' (names k))
  (registers : Registers R ≃ R') (labels : Label Λ ≃ Λ')
variable [DecidableEq K] [DecidableEq K']
variable (caller : External Λ → Statement Γ Λ R)
variable (ambient : Λ' → Turing.TM2.Stmt Γ' Λ' R')

/-- An actual ambient prefix is the complete physical image of one and the
same source-prefix witness. Only owned-label agreement is required. -/
theorem installed_owned_prefix_frame
    (installed : ∀ label, Owned (some label) →
      ambient (labels label) =
        FrontEndMachine.Transport.statement names symbols registers labels (program caller label))
    (start : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start)
    (reached : Turing.TM2.Cfg Γ' Λ' R')
    (executed : (FrontEndMachine.Transport.next ambient)^[n]
      (some (installedCfg names symbols registers labels start)) = some reached) :
    ∃ source, (next caller)^[n] (some start) = some source ∧
      reached = installedCfg names symbols registers labels source ∧
      remainingSteps source = remainingSteps start - n ∧
      Relation.ReflTransGen (LocalStep caller) start source ∧
      (n < remainingSteps start ↔ installedOwned labels reached.l) ∧
      (n = 0 → reached = installedCfg names symbols registers labels start) ∧
      reached.var = registers (registersAt start n) ∧
      source.var.2.2 = start.var.2.2 ∧
      ∀ k, reached.stk (names (.inr k)) = (start.stk (.inr k)).map (symbols (.inr k)) := by
  obtain ⟨source, run, rank, path, live, zero, reset, callerRegister, frame⟩ :=
    owned_prefix_frame caller start n bound
  have mapped := installed_owned_prefix names symbols registers labels caller ambient installed start n bound
  rw [run, Option.map_some, executed] at mapped
  have same : reached = installedCfg names symbols registers labels source := Option.some.inj mapped
  subst reached
  refine ⟨source, run, rfl, rank, path, ?_, ?_, ?_, callerRegister, ?_⟩
  · rwa [installedCfg_owned_iff]
  · intro empty
    rw [zero empty]
  · change registers source.var = registers (registersAt start n)
    rw [reset]
  · intro k
    rw [installedCfg_stack, frame k]

/-- The staged register value is transported at the actual supplied ambient
endpoint, including every dirty field before its own paid reset. -/
theorem installed_prefix_reset
    (installed : ∀ label, Owned (some label) →
      ambient (labels label) =
        FrontEndMachine.Transport.statement names symbols registers labels (program caller label))
    (start : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start)
    (reached : Turing.TM2.Cfg Γ' Λ' R')
    (executed : (FrontEndMachine.Transport.next ambient)^[n]
      (some (installedCfg names symbols registers labels start)) = some reached) :
    reached.var = registers (registersAt start n) := by
  obtain ⟨_, _, _, _, _, _, _, reset, _, _⟩ :=
    installed_owned_prefix_frame names symbols registers labels caller ambient installed start n bound reached executed
  exact reset

/-- The complete physical allowance includes every transported local and
protected store; the endpoint is the same actual ambient iterate. -/
theorem installed_prefix_stackCells_le_dirty [Fintype K] [Fintype K']
    (installed : ∀ label, Owned (some label) →
      ambient (labels label) =
        FrontEndMachine.Transport.statement names symbols registers labels (program caller label))
    (start : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start)
    (reached : Turing.TM2.Cfg Γ' Λ' R')
    (executed : (FrontEndMachine.Transport.next ambient)^[n]
      (some (installedCfg names symbols registers labels start)) = some reached) :
    ∑ k, (reached.stk k).length ≤ allowance start := by
  apply installed_prefix_cells_of_source_bound names symbols registers labels caller ambient installed
    start n bound (allowance start) _ reached executed
  intro source run
  exact prefix_stackCells_le_dirty caller start n bound source run

end Resources.RotationCertificate.StreamMachine

-- END INSTALLED SHARED PREFIX1
