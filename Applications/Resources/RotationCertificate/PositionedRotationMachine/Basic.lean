import Applications.Resources.RotationCertificate.Execution
import Applications.Resources.RotationCertificate.TreeParserMachine
import Applications.Resources.RotationCertificate.MoveParserMachine
import Applications.Resources.BinaryCounter.FixedWidthMachine
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Open finite positioned rotation

Five physical local stacks carry the raw tree, saved prefix, scratch subtree,
pending slots and path. The sixteen finite blocks inspect only finite temporary
fields and constants. Mathematical words, trees, clocks and potentials below
are proof-side. The first result is live; arbitrary caller behavior begins only
after that first handoff. The complete verifier and its model/NP bridge remain
separate work. Correspondence: the fixed requirements12 Position proposal/cases
in `docs/research/fdsa-rotation-certificate-preparation.md`.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.RotationCertificate.PositionedRotationMachine
open Search.SharedTree (Branch)
open Trees.Rotations (RotationDirection RotationMove)

inductive LocalStack | source | saved | scratch | pending | path
  deriving DecidableEq

instance : Fintype LocalStack where
  elems := {.source, .saved, .scratch, .pending, .path}
  complete k := by cases k <;> decide

inductive Result | success | failure
  deriving DecidableEq

instance : Fintype Result where
  elems := {.success, .failure}
  complete r := by cases r <;> decide

inductive RestoreMode | successLeft | successRight | failureLeft | failureRight
  deriving DecidableEq

instance : Fintype RestoreMode where
  elems := {.successLeft, .successRight, .failureLeft, .failureRight}
  complete mode := by cases mode <;> decide

inductive Phase
  | seek (direction : RotationDirection)
  | scanPrefix (direction : RotationDirection)
  | start (direction : RotationDirection)
  | scanScratch (direction : RotationDirection)
  | checkRight
  | restoreScratch (mode : RestoreMode)
  | dropPending
  | restorePrefix (result : Result)
  deriving DecidableEq

instance : Fintype Phase where
  elems := {.seek .left, .seek .right, .scanPrefix .left, .scanPrefix .right,
    .start .left, .start .right, .scanScratch .left, .scanScratch .right, .checkRight,
    .restoreScratch .successLeft, .restoreScratch .successRight,
    .restoreScratch .failureLeft, .restoreScratch .failureRight, .dropPending,
    .restorePrefix .success, .restorePrefix .failure}
  complete q := by
    cases q with
    | seek d => cases d <;> decide
    | scanPrefix d => cases d <;> decide
    | start d => cases d <;> decide
    | scanScratch d => cases d <;> decide
    | checkRight => decide
    | restoreScratch mode => cases mode <;> decide
    | dropPending => decide
    | restorePrefix r => cases r <;> decide

abbrev Control := Phase ⊕ Result
abbrev StackId (K : Type) := LocalStack ⊕ K
abbrev External (Λ : Type) := Result ⊕ Λ
abbrev Label (Λ : Type) := Phase ⊕ External Λ
abbrev Temporaries := Option Branch × (Option Tag × Option Unit)
abbrev Registers (R : Type) := Temporaries × R

structure LocalData where
  source : Word := []
  saved : Word := []
  scratch : Word := []
  pending : List Unit := []
  path : List Branch := []
  deriving DecidableEq

variable {K Λ R : Type} {Γ : K → Type}

abbrev Alphabet (Γ : K → Type) : StackId K → Type
  | .inl .source | .inl .saved | .inl .scratch => Tag
  | .inl .pending => Unit
  | .inl .path => Branch
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

def phaseLabel (q : Phase) : Label Λ := .inl q
def resultLabel (r : Result) : Label Λ := .inr (.inl r)
def callerLabel (label : Λ) : Label Λ := .inr (.inr label)
def controlLabel : Control → Label Λ
  | .inl q => phaseLabel q
  | .inr r => resultLabel r

def reset (regs : Registers R) : Registers R := ((none, (none, none)), regs.2)
def storeBranch (regs : Registers R) (b : Option Branch) : Registers R :=
  ((b, regs.1.2), regs.2)
def storeTag (regs : Registers R) (a : Option Tag) : Registers R :=
  ((regs.1.1, (a, regs.1.2.2)), regs.2)
def storeUnit (regs : Registers R) (u : Option Unit) : Registers R :=
  ((regs.1.1, (regs.1.2.1, u)), regs.2)

@[simp] theorem reset_reset (regs : Registers R) : reset (reset regs) = reset regs := rfl

def jump (label : Label Λ) : Statement Γ Λ R :=
  .load reset (.goto (fun _ => label))

/-- The fallback is reached only under the actual present-observation guard. -/
def restoreObserved (tail : Statement Γ Λ R) : Statement Γ Λ R :=
  .branch (fun regs => regs.1.2.1.isSome)
    (.push (.inl .source) (fun regs => regs.1.2.1.getD emptyTag) tail) tail

def scratchFailure : RotationDirection → RestoreMode
  | .left => .failureLeft
  | .right => .failureRight

def markerWord : RestoreMode → Word
  | .successLeft | .failureRight => [nodeTag, nodeTag]
  | .successRight | .failureLeft => [nodeTag]

def modeResult : RestoreMode → Result
  | .successLeft | .successRight => .success
  | .failureLeft | .failureRight => .failure

def scratchFinish (d : RotationDirection) : Statement Γ Λ R :=
  match d with
  | .left => jump (phaseLabel .checkRight)
  | .right => .push (.inl .source) (fun _ => nodeTag)
      (jump (phaseLabel (.restoreScratch .successRight)))

def scratchEmpty (mode : RestoreMode) : Statement Γ Λ R :=
  match mode with
  | .successLeft => .push (.inl .source) (fun _ => nodeTag)
      (.push (.inl .source) (fun _ => nodeTag) (jump (phaseLabel (.restorePrefix .success))))
  | .successRight => .push (.inl .source) (fun _ => nodeTag)
      (jump (phaseLabel (.restorePrefix .success)))
  | .failureLeft => .push (.inl .source) (fun _ => nodeTag) (jump (phaseLabel .dropPending))
  | .failureRight => .push (.inl .source) (fun _ => nodeTag)
      (.push (.inl .source) (fun _ => nodeTag) (jump (phaseLabel .dropPending)))

/-- Complete fixed finite syntax; callbacks inspect only finite register fields. -/
def block : Phase → Statement Γ Λ R
  | .seek d =>
      .pop (.inl .path) storeBranch (.branch (fun regs => regs.1.1.isSome)
        (.pop (.inl .source) storeTag (.branch (fun regs => decide (regs.1.2.1 = some nodeTag))
          (.push (.inl .saved) (fun _ => nodeTag)
            (.branch (fun regs => decide (regs.1.1 = some .left))
              (jump (phaseLabel (.seek d)))
              (.push (.inl .pending) (fun _ => ()) (jump (phaseLabel (.scanPrefix d))))))
          (restoreObserved (jump (phaseLabel .dropPending)))))
        (jump (phaseLabel (.start d))))
  | .scanPrefix d =>
      .pop (.inl .source) storeTag (.branch (fun regs => decide (regs.1.2.1 = some nodeTag))
        (.push (.inl .saved) (fun _ => nodeTag)
          (.push (.inl .pending) (fun _ => ()) (jump (phaseLabel (.scanPrefix d)))))
        (.branch (fun regs => decide (regs.1.2.1 = some emptyTag))
          (.push (.inl .saved) (fun _ => emptyTag)
            (.pop (.inl .pending) storeUnit (.peek (.inl .pending) storeUnit
              (.branch (fun regs => regs.1.2.2.isSome)
                (jump (phaseLabel (.scanPrefix d))) (jump (phaseLabel (.seek d)))))))
          (restoreObserved (jump (phaseLabel .dropPending)))))
  | .start .left =>
      .pop (.inl .source) storeTag (.branch (fun regs => decide (regs.1.2.1 = some nodeTag))
        (.push (.inl .pending) (fun _ => ()) (jump (phaseLabel (.scanScratch .left))))
        (restoreObserved (jump (phaseLabel .dropPending))))
  | .start .right =>
      .pop (.inl .source) storeTag (.branch (fun regs => decide (regs.1.2.1 = some nodeTag))
        (.pop (.inl .source) storeTag (.branch (fun regs => decide (regs.1.2.1 = some nodeTag))
          (.push (.inl .pending) (fun _ => ()) (jump (phaseLabel (.scanScratch .right))))
          (restoreObserved (.push (.inl .source) (fun _ => nodeTag)
            (jump (phaseLabel .dropPending))))))
        (restoreObserved (jump (phaseLabel .dropPending))))
  | .scanScratch d =>
      .pop (.inl .source) storeTag (.branch (fun regs => decide (regs.1.2.1 = some nodeTag))
        (.push (.inl .scratch) (fun _ => nodeTag)
          (.push (.inl .pending) (fun _ => ()) (jump (phaseLabel (.scanScratch d)))))
        (.branch (fun regs => decide (regs.1.2.1 = some emptyTag))
          (.push (.inl .scratch) (fun _ => emptyTag)
            (.pop (.inl .pending) storeUnit (.peek (.inl .pending) storeUnit
              (.branch (fun regs => regs.1.2.2.isSome)
                (jump (phaseLabel (.scanScratch d))) (scratchFinish d)))))
          (restoreObserved (jump (phaseLabel (.restoreScratch (scratchFailure d)))))))
  | .checkRight =>
      .pop (.inl .source) storeTag (.branch (fun regs => decide (regs.1.2.1 = some nodeTag))
        (jump (phaseLabel (.restoreScratch .successLeft)))
        (restoreObserved (jump (phaseLabel (.restoreScratch .failureLeft)))))
  | .restoreScratch mode =>
      .pop (.inl .scratch) storeTag (.branch (fun regs => regs.1.2.1.isSome)
        (.push (.inl .source) (fun regs => regs.1.2.1.getD emptyTag)
          (jump (phaseLabel (.restoreScratch mode)))) (scratchEmpty mode))
  | .dropPending =>
      .pop (.inl .pending) storeUnit (.branch (fun regs => regs.1.2.2.isSome)
        (jump (phaseLabel .dropPending)) (jump (phaseLabel (.restorePrefix .failure))))
  | .restorePrefix r =>
      .pop (.inl .saved) storeTag (.branch (fun regs => regs.1.2.1.isSome)
        (.push (.inl .source) (fun regs => regs.1.2.1.getD emptyTag)
          (jump (phaseLabel (.restorePrefix r)))) (jump (resultLabel r)))

def program (caller : External Λ → Statement Γ Λ R) : Label Λ → Statement Γ Λ R
  | .inl q => block q
  | .inr external => caller external

theorem program_eq_of_agrees (ambient : Label Λ → Statement Γ Λ R)
    (agrees : ∀ q, ambient (phaseLabel q) = block q) :
    ambient = program (fun external => ambient (.inr external)) := by
  funext label
  cases label with
  | inl q => exact agrees q
  | inr external => rfl

def cfg (label : Option (Label Λ)) (regs : Registers R) (D : LocalData)
    (ctx : ∀ k, List (Γ k)) : Cfg Γ Λ R where
  l := label
  var := regs
  stk
    | .inl .source => D.source
    | .inl .saved => D.saved
    | .inl .scratch => D.scratch
    | .inl .pending => D.pending
    | .inl .path => D.path
    | .inr k => ctx k

def dataOfCfg (c : Cfg Γ Λ R) : LocalData :=
  ⟨c.stk (.inl .source), c.stk (.inl .saved), c.stk (.inl .scratch),
    c.stk (.inl .pending), c.stk (.inl .path)⟩

theorem cfg_ext {a b : Cfg Γ Λ R} (label : a.l = b.l) (regs : a.var = b.var)
    (source : a.stk (.inl .source) = b.stk (.inl .source))
    (saved : a.stk (.inl .saved) = b.stk (.inl .saved))
    (scratch : a.stk (.inl .scratch) = b.stk (.inl .scratch))
    (pending : a.stk (.inl .pending) = b.stk (.inl .pending))
    (path : a.stk (.inl .path) = b.stk (.inl .path))
    (context : ∀ k, a.stk (.inr k) = b.stk (.inr k)) : a = b := by
  have stores : a.stk = b.stk := by
    funext k
    cases k with
    | inl k => cases k with
      | source => exact source
      | saved => exact saved
      | scratch => exact scratch
      | pending => exact pending
      | path => exact path
    | inr k => exact context k
  cases a
  cases b
  cases label
  cases regs
  cases stores
  rfl

theorem cfg_eta (c : Cfg Γ Λ R) :
    cfg c.l c.var (dataOfCfg c) (fun k => c.stk (.inr k)) = c := by
  apply cfg_ext <;> first | rfl | exact fun _ => rfl

@[simp] theorem dataOfCfg_cfg (label : Option (Label Λ)) (regs : Registers R)
    (D : LocalData) (ctx : ∀ k, List (Γ k)) : dataOfCfg (cfg label regs D ctx) = D := by
  cases D
  rfl

def entry (d : RotationDirection) (regs : Registers R) (raw : Word)
    (path : List Branch) (ctx : ∀ k, List (Γ k)) : Cfg Γ Λ R :=
  cfg (some (phaseLabel (.seek d))) regs { source := raw, path := path } ctx

def Owned : Option (Label Λ) → Prop
  | some (.inl _) => True
  | _ => False

abbrev OwnedLabel (Λ : Type) := {label : Label Λ // Owned (some label)}

def ownedLabelEquiv : Phase ≃ OwnedLabel Λ where
  toFun q := ⟨phaseLabel q, True.intro⟩
  invFun label := match label with
    | ⟨.inl q, _⟩ => q
    | ⟨.inr _, impossible⟩ => False.elim impossible
  left_inv q := rfl
  right_inv label := by
    rcases label with ⟨label, h⟩
    cases label with
    | inl q => rfl
    | inr _ => exact False.elim h

instance : Fintype (OwnedLabel Λ) := Fintype.ofEquiv Phase ownedLabelEquiv

theorem card_localStack : Fintype.card LocalStack = 5 := by decide
theorem card_phase : Fintype.card Phase = 16 := by decide
theorem card_result : Fintype.card Result = 2 := by decide
theorem card_temporaries : Fintype.card Temporaries = 102 := by decide
theorem card_ownedLabel : Fintype.card (OwnedLabel Λ) = 16 := by
  rw [← Fintype.card_congr (ownedLabelEquiv (Λ := Λ))]
  exact card_phase
theorem card_stackId [Fintype K] : Fintype.card (StackId K) = 5 + Fintype.card K := by
  rw [Fintype.card_sum, card_localStack]
theorem card_label [Fintype Λ] : Fintype.card (Label Λ) = 18 + Fintype.card Λ := by
  simp only [Fintype.card_sum, card_phase, card_result]
  omega
theorem card_registers [Fintype R] : Fintype.card (Registers R) = 102 * Fintype.card R := by
  rw [Fintype.card_prod, card_temporaries]


end Resources.RotationCertificate.PositionedRotationMachine
