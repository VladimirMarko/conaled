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

abbrev alphabet (Γ : K → Type) : StackId K → Type
  | .inl .source | .inl .saved | .inl .scratch => Tag
  | .inl .pending => Unit
  | .inl .path => Branch
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

variable [DecidableEq K]

def step (caller : External Λ → Statement Γ Λ R) : Cfg Γ Λ R → Option (Cfg Γ Λ R) :=
  Turing.TM2.step (program caller)
def next (caller : External Λ → Statement Γ Λ R) (c : Option (Cfg Γ Λ R)) :
    Option (Cfg Γ Λ R) := c.bind (step caller)

variable (caller : External Λ → Statement Γ Λ R)

@[simp] theorem next_some (c : Cfg Γ Λ R) : next caller (some c) = step caller c := rfl
@[simp] theorem next_none : next caller none = none := rfl

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
  LocalRun.single caller ⟨True.intro, executed⟩

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

theorem seek_step_path_nil (d : RotationDirection) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel (.seek d))) regs { D with path := [] } ctx) =
      some (cfg (some (phaseLabel (.start d))) (reset regs) { D with path := [] } ctx) := by
  apply congrArg some
  apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem seek_step_node_left (d : RotationDirection) (raw : Word) (p : List Branch)
    (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel (.seek d))) regs
      { D with source := nodeTag :: raw, path := .left :: p } ctx) =
      some (cfg (some (phaseLabel (.seek d))) (reset regs)
        { D with source := raw, saved := nodeTag :: D.saved, path := p } ctx) := by
  apply congrArg some
  apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem seek_step_node_right (d : RotationDirection) (raw : Word) (p : List Branch)
    (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel (.seek d))) regs
      { D with source := nodeTag :: raw, path := .right :: p } ctx) =
      some (cfg (some (phaseLabel (.scanPrefix d))) (reset regs)
        { D with source := raw, saved := nodeTag :: D.saved, pending := () :: D.pending, path := p } ctx) := by
  apply congrArg some
  apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem seek_step_source_nil (d : RotationDirection) (b : Branch) (p : List Branch)
    (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel (.seek d))) regs
      { D with source := [], path := b :: p } ctx) =
      some (cfg (some (phaseLabel .dropPending)) (reset regs)
        { D with source := [], path := p } ctx) := by
  apply congrArg some
  apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem seek_step_source_nonnode (d : RotationDirection) (b : Branch) (p : List Branch)
    (tag : Tag) (raw : Word) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (notNode : tag ≠ nodeTag) :
    step caller (cfg (some (phaseLabel (.seek d))) regs
      { D with source := tag :: raw, path := b :: p } ctx) =
      some (cfg (some (phaseLabel .dropPending)) (reset regs)
        { D with source := tag :: raw, path := p } ctx) := by
  apply congrArg some
  apply cfg_ext <;> simp [Turing.TM2.stepAux, program, block, cfg, phaseLabel,
    storeBranch, storeTag, jump, restoreObserved, reset, notNode, Function.update]

theorem scanPrefix_step_node (d : RotationDirection) (raw : Word) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel (.scanPrefix d))) regs
      { D with source := nodeTag :: raw } ctx) =
      some (cfg (some (phaseLabel (.scanPrefix d))) (reset regs)
        { D with source := raw, saved := nodeTag :: D.saved, pending := () :: D.pending } ctx) := by
  apply congrArg some
  apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem scanPrefix_step_empty_continue (d : RotationDirection) (raw : Word) (h : List Unit)
    (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel (.scanPrefix d))) regs
      { D with source := emptyTag :: raw, pending := () :: () :: h } ctx) =
      some (cfg (some (phaseLabel (.scanPrefix d))) (reset regs)
        { D with source := raw, saved := emptyTag :: D.saved, pending := () :: h } ctx) := by
  apply congrArg some
  apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem scanPrefix_step_empty_finish (d : RotationDirection) (raw : Word) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) (finished : D.pending.tail = []) :
    step caller (cfg (some (phaseLabel (.scanPrefix d))) regs
      { D with source := emptyTag :: raw } ctx) =
      some (cfg (some (phaseLabel (.seek d))) (reset regs)
        { D with source := raw, saved := emptyTag :: D.saved, pending := [] } ctx) := by
  rcases D with ⟨source, saved, scratch, pending, path⟩
  cases pending with
  | nil =>
      apply congrArg some
      apply cfg_ext <;> first | rfl | exact fun _ => rfl
  | cons token pending =>
      change pending = [] at finished
      subst pending
      apply congrArg some
      apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem scanPrefix_step_nil (d : RotationDirection) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel (.scanPrefix d))) regs { D with source := [] } ctx) =
      some (cfg (some (phaseLabel .dropPending)) (reset regs) { D with source := [] } ctx) := by
  apply congrArg some
  apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem scanPrefix_step_foreign (d : RotationDirection) (tag : Tag) (raw : Word)
    (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (notNode : tag ≠ nodeTag) (notEmpty : tag ≠ emptyTag) :
    step caller (cfg (some (phaseLabel (.scanPrefix d))) regs
      { D with source := tag :: raw } ctx) =
      some (cfg (some (phaseLabel .dropPending)) (reset regs)
        { D with source := tag :: raw } ctx) := by
  apply congrArg some
  apply cfg_ext <;> simp [Turing.TM2.stepAux, program, block, cfg, phaseLabel,
    storeTag, jump, restoreObserved, reset, notNode, notEmpty, Function.update]

theorem start_left_step_node (raw : Word) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel (.start .left))) regs
      { D with source := nodeTag :: raw } ctx) =
      some (cfg (some (phaseLabel (.scanScratch .left))) (reset regs)
        { D with source := raw, pending := () :: D.pending } ctx) := by
  apply congrArg some
  apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem start_left_step_nil (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel (.start .left))) regs { D with source := [] } ctx) =
      some (cfg (some (phaseLabel .dropPending)) (reset regs) { D with source := [] } ctx) := by
  apply congrArg some
  apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem start_left_step_nonnode (tag : Tag) (raw : Word) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) (notNode : tag ≠ nodeTag) :
    step caller (cfg (some (phaseLabel (.start .left))) regs { D with source := tag :: raw } ctx) =
      some (cfg (some (phaseLabel .dropPending)) (reset regs) { D with source := tag :: raw } ctx) := by
  apply congrArg some
  apply cfg_ext <;> simp [Turing.TM2.stepAux, program, block, cfg, phaseLabel,
    storeTag, jump, restoreObserved, reset, notNode, Function.update]

theorem start_right_step_nodes (raw : Word) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel (.start .right))) regs
      { D with source := nodeTag :: nodeTag :: raw } ctx) =
      some (cfg (some (phaseLabel (.scanScratch .right))) (reset regs)
        { D with source := raw, pending := () :: D.pending } ctx) := by
  apply congrArg some
  apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem start_right_step_first_nil (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel (.start .right))) regs { D with source := [] } ctx) =
      some (cfg (some (phaseLabel .dropPending)) (reset regs) { D with source := [] } ctx) := by
  apply congrArg some
  apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem start_right_step_first_nonnode (tag : Tag) (raw : Word) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) (notNode : tag ≠ nodeTag) :
    step caller (cfg (some (phaseLabel (.start .right))) regs { D with source := tag :: raw } ctx) =
      some (cfg (some (phaseLabel .dropPending)) (reset regs) { D with source := tag :: raw } ctx) := by
  apply congrArg some
  apply cfg_ext <;> simp [Turing.TM2.stepAux, program, block, cfg, phaseLabel,
    storeTag, jump, restoreObserved, reset, notNode, Function.update]

theorem start_right_step_second_nil (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel (.start .right))) regs { D with source := [nodeTag] } ctx) =
      some (cfg (some (phaseLabel .dropPending)) (reset regs) { D with source := [nodeTag] } ctx) := by
  apply congrArg some
  apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem start_right_step_second_nonnode (tag : Tag) (raw : Word) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) (notNode : tag ≠ nodeTag) :
    step caller (cfg (some (phaseLabel (.start .right))) regs
      { D with source := nodeTag :: tag :: raw } ctx) =
      some (cfg (some (phaseLabel .dropPending)) (reset regs)
        { D with source := nodeTag :: tag :: raw } ctx) := by
  apply congrArg some
  apply cfg_ext <;> simp [Turing.TM2.stepAux, program, block, cfg, phaseLabel,
    storeTag, jump, restoreObserved, reset, notNode, Function.update]

theorem scanScratch_step_node (d : RotationDirection) (raw : Word) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel (.scanScratch d))) regs
      { D with source := nodeTag :: raw } ctx) =
      some (cfg (some (phaseLabel (.scanScratch d))) (reset regs)
        { D with source := raw, scratch := nodeTag :: D.scratch, pending := () :: D.pending } ctx) := by
  apply congrArg some
  apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem scanScratch_step_empty_continue (d : RotationDirection) (raw : Word) (h : List Unit)
    (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel (.scanScratch d))) regs
      { D with source := emptyTag :: raw, pending := () :: () :: h } ctx) =
      some (cfg (some (phaseLabel (.scanScratch d))) (reset regs)
        { D with source := raw, scratch := emptyTag :: D.scratch, pending := () :: h } ctx) := by
  apply congrArg some
  apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem scanScratch_left_step_finish (raw : Word) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) (finished : D.pending.tail = []) :
    step caller (cfg (some (phaseLabel (.scanScratch .left))) regs
      { D with source := emptyTag :: raw } ctx) =
      some (cfg (some (phaseLabel .checkRight)) (reset regs)
        { D with source := raw, scratch := emptyTag :: D.scratch, pending := [] } ctx) := by
  rcases D with ⟨source, saved, scratch, pending, path⟩
  cases pending with
  | nil =>
      apply congrArg some
      apply cfg_ext <;> first | rfl | exact fun _ => rfl
  | cons token pending =>
      change pending = [] at finished
      subst pending
      apply congrArg some
      apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem scanScratch_right_step_finish (raw : Word) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) (finished : D.pending.tail = []) :
    step caller (cfg (some (phaseLabel (.scanScratch .right))) regs
      { D with source := emptyTag :: raw } ctx) =
      some (cfg (some (phaseLabel (.restoreScratch .successRight))) (reset regs)
        { D with source := nodeTag :: raw, scratch := emptyTag :: D.scratch, pending := [] } ctx) := by
  rcases D with ⟨source, saved, scratch, pending, path⟩
  cases pending with
  | nil =>
      apply congrArg some
      apply cfg_ext <;> first | rfl | exact fun _ => rfl
  | cons token pending =>
      change pending = [] at finished
      subst pending
      apply congrArg some
      apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem scanScratch_step_nil (d : RotationDirection) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel (.scanScratch d))) regs { D with source := [] } ctx) =
      some (cfg (some (phaseLabel (.restoreScratch (scratchFailure d)))) (reset regs)
        { D with source := [] } ctx) := by
  apply congrArg some
  apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem scanScratch_step_foreign (d : RotationDirection) (tag : Tag) (raw : Word)
    (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (notNode : tag ≠ nodeTag) (notEmpty : tag ≠ emptyTag) :
    step caller (cfg (some (phaseLabel (.scanScratch d))) regs
      { D with source := tag :: raw } ctx) =
      some (cfg (some (phaseLabel (.restoreScratch (scratchFailure d)))) (reset regs)
        { D with source := tag :: raw } ctx) := by
  apply congrArg some
  apply cfg_ext <;> simp [Turing.TM2.stepAux, program, block, cfg, phaseLabel,
    storeTag, jump, restoreObserved, reset, notNode, notEmpty, Function.update]

theorem checkRight_step_node (raw : Word) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel .checkRight)) regs { D with source := nodeTag :: raw } ctx) =
      some (cfg (some (phaseLabel (.restoreScratch .successLeft))) (reset regs)
        { D with source := raw } ctx) := by
  apply congrArg some
  apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem checkRight_step_nil (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel .checkRight)) regs { D with source := [] } ctx) =
      some (cfg (some (phaseLabel (.restoreScratch .failureLeft))) (reset regs)
        { D with source := [] } ctx) := by
  apply congrArg some
  apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem checkRight_step_nonnode (tag : Tag) (raw : Word) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) (notNode : tag ≠ nodeTag) :
    step caller (cfg (some (phaseLabel .checkRight)) regs { D with source := tag :: raw } ctx) =
      some (cfg (some (phaseLabel (.restoreScratch .failureLeft))) (reset regs)
        { D with source := tag :: raw } ctx) := by
  apply congrArg some
  apply cfg_ext <;> simp [Turing.TM2.stepAux, program, block, cfg, phaseLabel,
    storeTag, jump, restoreObserved, reset, notNode, Function.update]

theorem restoreScratch_step_cons (mode : RestoreMode) (tag : Tag) (rest : Word)
    (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel (.restoreScratch mode))) regs
      { D with scratch := tag :: rest } ctx) =
      some (cfg (some (phaseLabel (.restoreScratch mode))) (reset regs)
        { D with source := tag :: D.source, scratch := rest } ctx) := by
  apply congrArg some
  apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem restoreScratch_step_nil (mode : RestoreMode) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel (.restoreScratch mode))) regs { D with scratch := [] } ctx) =
      some (cfg (some (phaseLabel (if modeResult mode = .success then
        .restorePrefix .success else .dropPending))) (reset regs)
        { D with source := markerWord mode ++ D.source, scratch := [] } ctx) := by
  cases mode <;> apply congrArg some <;> apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem dropPending_step_cons (rest : List Unit) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel .dropPending)) regs { D with pending := () :: rest } ctx) =
      some (cfg (some (phaseLabel .dropPending)) (reset regs) { D with pending := rest } ctx) := by
  apply congrArg some
  apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem dropPending_step_nil (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel .dropPending)) regs { D with pending := [] } ctx) =
      some (cfg (some (phaseLabel (.restorePrefix .failure))) (reset regs)
        { D with pending := [] } ctx) := by
  apply congrArg some
  apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem restorePrefix_step_cons (r : Result) (tag : Tag) (rest : Word)
    (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel (.restorePrefix r))) regs { D with saved := tag :: rest } ctx) =
      some (cfg (some (phaseLabel (.restorePrefix r))) (reset regs)
        { D with source := tag :: D.source, saved := rest } ctx) := by
  apply congrArg some
  apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem restorePrefix_step_nil (r : Result) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel (.restorePrefix r))) regs { D with saved := [] } ctx) =
      some (cfg (some (resultLabel r)) (reset regs) { D with saved := [] } ctx) := by
  apply congrArg some
  apply cfg_ext <;> first | rfl | exact fun _ => rfl

@[simp] theorem emptyTag_ne_nodeTag : emptyTag ≠ nodeTag := by decide

/-- A proof-only complete local successor; it is absent from every callback. -/
def advance : Phase → LocalData → Control × LocalData
  | .seek d, D =>
      match D.path with
      | [] => (.inl (.start d), D)
      | b :: p =>
          match D.source with
          | [] => (.inl .dropPending, { D with path := p })
          | tag :: raw =>
              if tag = nodeTag then
                match b with
                | .left => (.inl (.seek d),
                    { D with source := raw, saved := nodeTag :: D.saved, path := p })
                | .right => (.inl (.scanPrefix d),
                    { D with source := raw, saved := nodeTag :: D.saved, pending := () :: D.pending, path := p })
              else (.inl .dropPending, { D with path := p })
  | .scanPrefix d, D =>
      match D.source with
      | [] => (.inl .dropPending, D)
      | tag :: raw =>
          if tag = nodeTag then
            (.inl (.scanPrefix d),
              { D with source := raw, saved := nodeTag :: D.saved, pending := () :: D.pending })
          else if tag = emptyTag then
            (.inl (if D.pending.tail = [] then .seek d else .scanPrefix d),
              { D with source := raw, saved := emptyTag :: D.saved, pending := D.pending.tail })
          else (.inl .dropPending, D)
  | .start .left, D =>
      match D.source with
      | [] => (.inl .dropPending, D)
      | tag :: raw =>
          if tag = nodeTag then
            (.inl (.scanScratch .left), { D with source := raw, pending := () :: D.pending })
          else (.inl .dropPending, D)
  | .start .right, D =>
      match D.source with
      | first :: second :: raw =>
          if first = nodeTag ∧ second = nodeTag then
            (.inl (.scanScratch .right), { D with source := raw, pending := () :: D.pending })
          else (.inl .dropPending, D)
      | _ => (.inl .dropPending, D)
  | .scanScratch d, D =>
      match D.source with
      | [] => (.inl (.restoreScratch (scratchFailure d)), D)
      | tag :: raw =>
          if tag = nodeTag then
            (.inl (.scanScratch d),
              { D with source := raw, scratch := nodeTag :: D.scratch, pending := () :: D.pending })
          else if tag = emptyTag then
            if D.pending.tail = [] then
              match d with
              | .left => (.inl .checkRight,
                  { D with source := raw, scratch := emptyTag :: D.scratch, pending := [] })
              | .right => (.inl (.restoreScratch .successRight),
                  { D with source := nodeTag :: raw, scratch := emptyTag :: D.scratch, pending := [] })
            else (.inl (.scanScratch d),
              { D with source := raw, scratch := emptyTag :: D.scratch, pending := D.pending.tail })
          else (.inl (.restoreScratch (scratchFailure d)), D)
  | .checkRight, D =>
      match D.source with
      | [] => (.inl (.restoreScratch .failureLeft), D)
      | tag :: raw =>
          if tag = nodeTag then
            (.inl (.restoreScratch .successLeft), { D with source := raw })
          else (.inl (.restoreScratch .failureLeft), D)
  | .restoreScratch mode, D =>
      match D.scratch with
      | [] => (.inl (if modeResult mode = .success then .restorePrefix .success else .dropPending),
          { D with source := markerWord mode ++ D.source })
      | tag :: rest => (.inl (.restoreScratch mode),
          { D with source := tag :: D.source, scratch := rest })
  | .dropPending, D =>
      match D.pending with
      | [] => (.inl (.restorePrefix .failure), D)
      | _ :: rest => (.inl .dropPending, { D with pending := rest })
  | .restorePrefix r, D =>
      match D.saved with
      | [] => (.inr r, D)
      | tag :: rest => (.inl (.restorePrefix r), { D with source := tag :: D.source, saved := rest })

def countdown : Control → LocalData → Nat
  | .inl (.seek _), D | .inl (.scanPrefix _), D | .inl (.scanScratch _), D =>
      3 * D.source.length + D.saved.length + D.scratch.length + D.pending.length + D.path.length + 5
  | .inl (.start _), D =>
      3 * D.source.length + D.saved.length + D.scratch.length + D.pending.length + D.path.length + 4
  | .inl .checkRight, D =>
      3 * D.source.length + D.saved.length + D.scratch.length + D.pending.length + D.path.length + 6
  | .inl (.restoreScratch .successLeft), D | .inl (.restoreScratch .successRight), D =>
      D.scratch.length + D.saved.length + 2
  | .inl (.restoreScratch .failureLeft), D | .inl (.restoreScratch .failureRight), D =>
      D.scratch.length + D.pending.length + D.saved.length + 3
  | .inl .dropPending, D => D.pending.length + D.saved.length + 2
  | .inl (.restorePrefix _), D => D.saved.length + 1
  | .inr _, _ => 0

theorem advance_step (q : Phase) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel q)) regs D ctx) =
      some (cfg (some (controlLabel (advance q D).1)) (reset regs) (advance q D).2 ctx) := by
  rcases D with ⟨raw, saved, scratch, pending, path⟩
  cases q with
  | seek d =>
      cases path with
      | nil => exact seek_step_path_nil caller d ⟨raw, saved, scratch, pending, []⟩ regs ctx
      | cons b path =>
          cases raw with
          | nil => exact seek_step_source_nil caller d b path ⟨[], saved, scratch, pending, []⟩ regs ctx
          | cons tag raw =>
              by_cases node : tag = nodeTag
              · subst tag
                cases b with
                | left => simpa [advance, controlLabel] using
                    seek_step_node_left caller d raw path ⟨[], saved, scratch, pending, []⟩ regs ctx
                | right => simpa [advance, controlLabel] using
                    seek_step_node_right caller d raw path ⟨[], saved, scratch, pending, []⟩ regs ctx
              · simpa [advance, controlLabel, node] using
                  seek_step_source_nonnode caller d b path tag raw
                    ⟨[], saved, scratch, pending, []⟩ regs ctx node
  | scanPrefix d =>
      cases raw with
      | nil => exact scanPrefix_step_nil caller d ⟨[], saved, scratch, pending, path⟩ regs ctx
      | cons tag raw =>
          by_cases node : tag = nodeTag
          · subst tag
            simpa [advance, controlLabel] using
              scanPrefix_step_node caller d raw ⟨[], saved, scratch, pending, path⟩ regs ctx
          · by_cases empty : tag = emptyTag
            · subst tag
              cases pending with
              | nil => exact scanPrefix_step_empty_finish caller d raw ⟨[], saved, scratch, [], path⟩ regs ctx rfl
              | cons token pending =>
                  cases token
                  cases pending with
                  | nil => exact scanPrefix_step_empty_finish caller d raw ⟨[], saved, scratch, [()], path⟩ regs ctx rfl
                  | cons token pending =>
                      cases token
                      simpa [advance, controlLabel] using scanPrefix_step_empty_continue caller d raw pending
                        ⟨[], saved, scratch, [], path⟩ regs ctx
            · simpa [advance, controlLabel, node, empty] using scanPrefix_step_foreign caller d tag raw
                ⟨[], saved, scratch, pending, path⟩ regs ctx node empty
  | start d =>
      cases d with
      | left =>
          cases raw with
          | nil => exact start_left_step_nil caller ⟨[], saved, scratch, pending, path⟩ regs ctx
          | cons tag raw =>
              by_cases node : tag = nodeTag
              · subst tag
                simpa [advance, controlLabel] using start_left_step_node caller raw
                  ⟨[], saved, scratch, pending, path⟩ regs ctx
              · simpa [advance, controlLabel, node] using start_left_step_nonnode caller tag raw
                  ⟨[], saved, scratch, pending, path⟩ regs ctx node
      | right =>
          cases raw with
          | nil => exact start_right_step_first_nil caller ⟨[], saved, scratch, pending, path⟩ regs ctx
          | cons first raw =>
              by_cases firstNode : first = nodeTag
              · subst first
                cases raw with
                | nil => exact start_right_step_second_nil caller ⟨[], saved, scratch, pending, path⟩ regs ctx
                | cons second raw =>
                    by_cases secondNode : second = nodeTag
                    · subst second
                      simpa [advance, controlLabel] using start_right_step_nodes caller raw
                        ⟨[], saved, scratch, pending, path⟩ regs ctx
                    · simpa [advance, controlLabel, secondNode] using
                        start_right_step_second_nonnode caller second raw
                          ⟨[], saved, scratch, pending, path⟩ regs ctx secondNode
              · have h := start_right_step_first_nonnode caller first raw
                  ⟨[], saved, scratch, pending, path⟩ regs ctx firstNode
                cases raw <;> simpa [advance, controlLabel, firstNode] using h
  | scanScratch d =>
      cases raw with
      | nil => exact scanScratch_step_nil caller d ⟨[], saved, scratch, pending, path⟩ regs ctx
      | cons tag raw =>
          by_cases node : tag = nodeTag
          · subst tag
            simpa [advance, controlLabel] using scanScratch_step_node caller d raw
              ⟨[], saved, scratch, pending, path⟩ regs ctx
          · by_cases empty : tag = emptyTag
            · subst tag
              cases pending with
              | nil => cases d with
                | left => exact scanScratch_left_step_finish caller raw ⟨[], saved, scratch, [], path⟩ regs ctx rfl
                | right => exact scanScratch_right_step_finish caller raw ⟨[], saved, scratch, [], path⟩ regs ctx rfl
              | cons token pending =>
                  cases token
                  cases pending with
                  | nil => cases d with
                    | left => exact scanScratch_left_step_finish caller raw ⟨[], saved, scratch, [()], path⟩ regs ctx rfl
                    | right => exact scanScratch_right_step_finish caller raw ⟨[], saved, scratch, [()], path⟩ regs ctx rfl
                  | cons token pending =>
                      cases token
                      simpa [advance, controlLabel] using scanScratch_step_empty_continue caller d raw pending
                        ⟨[], saved, scratch, [], path⟩ regs ctx
            · simpa [advance, controlLabel, node, empty] using scanScratch_step_foreign caller d tag raw
                ⟨[], saved, scratch, pending, path⟩ regs ctx node empty
  | checkRight =>
      cases raw with
      | nil => exact checkRight_step_nil caller ⟨[], saved, scratch, pending, path⟩ regs ctx
      | cons tag raw =>
          by_cases node : tag = nodeTag
          · subst tag
            simpa [advance, controlLabel] using checkRight_step_node caller raw
              ⟨[], saved, scratch, pending, path⟩ regs ctx
          · simpa [advance, controlLabel, node] using checkRight_step_nonnode caller tag raw
              ⟨[], saved, scratch, pending, path⟩ regs ctx node
  | restoreScratch mode =>
      cases scratch with
      | nil => exact restoreScratch_step_nil caller mode ⟨raw, saved, [], pending, path⟩ regs ctx
      | cons tag scratch => exact restoreScratch_step_cons caller mode tag scratch ⟨raw, saved, [], pending, path⟩ regs ctx
  | dropPending =>
      cases pending with
      | nil => exact dropPending_step_nil caller ⟨raw, saved, scratch, [], path⟩ regs ctx
      | cons token pending =>
          cases token
          exact dropPending_step_cons caller pending ⟨raw, saved, scratch, [], path⟩ regs ctx
  | restorePrefix r =>
      cases saved with
      | nil => exact restorePrefix_step_nil caller r ⟨raw, [], scratch, pending, path⟩ regs ctx
      | cons tag saved => exact restorePrefix_step_cons caller r tag saved ⟨raw, [], scratch, pending, path⟩ regs ctx

theorem advance_localRun (q : Phase) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    LocalRun caller 1 (cfg (some (phaseLabel q)) regs D ctx)
      (cfg (some (controlLabel (advance q D).1)) (reset regs) (advance q D).2 ctx) :=
  LocalRun.single caller ⟨True.intro, advance_step caller q D regs ctx⟩

theorem advance_countdown (q : Phase) (D : LocalData) :
    countdown (advance q D).1 (advance q D).2 + 1 ≤ countdown (.inl q) D := by
  rcases D with ⟨raw, saved, scratch, pending, path⟩
  cases q with
  | seek d =>
      cases path with
      | nil => simp [advance, countdown]
      | cons b path =>
          cases raw with
          | nil => simp [advance, countdown]; omega
          | cons tag raw =>
              by_cases node : tag = nodeTag
              · cases b <;> simp [advance, countdown, node] <;> omega
              · simp [advance, countdown, node]; omega
  | scanPrefix d =>
      cases raw with
      | nil => simp [advance, countdown]; omega
      | cons tag raw =>
          by_cases node : tag = nodeTag
          · simp [advance, countdown, node]; omega
          · by_cases empty : tag = emptyTag
            · by_cases finished : pending.tail = []
              · simp [advance, countdown, empty, finished]; omega
              · simp [advance, countdown, empty, finished, List.length_tail]; omega
            · simp [advance, countdown, node, empty]; omega
  | start d =>
      cases d with
      | left =>
          cases raw with
          | nil => simp [advance, countdown]; omega
          | cons tag raw =>
              by_cases node : tag = nodeTag <;> simp [advance, countdown, node] <;> omega
      | right =>
          cases raw with
          | nil => simp [advance, countdown]; omega
          | cons first raw =>
              cases raw with
              | nil => simp [advance, countdown]; omega
              | cons second raw =>
                  by_cases nodes : first = nodeTag ∧ second = nodeTag <;>
                    simp [advance, countdown, nodes] <;> omega
  | scanScratch d =>
      cases raw with
      | nil => cases d <;> simp [advance, countdown, scratchFailure] <;> omega
      | cons tag raw =>
          by_cases node : tag = nodeTag
          · simp [advance, countdown, node]; omega
          · by_cases empty : tag = emptyTag
            · by_cases finished : pending.tail = []
              · cases d <;> simp [advance, countdown, empty, finished] <;> omega
              · simp [advance, countdown, empty, finished, List.length_tail]; omega
            · cases d <;> simp [advance, countdown, node, empty, scratchFailure] <;> omega
  | checkRight =>
      cases raw with
      | nil => simp [advance, countdown]; omega
      | cons tag raw =>
          by_cases node : tag = nodeTag <;> simp [advance, countdown, node] <;> omega
  | restoreScratch mode =>
      cases scratch <;> cases mode <;> simp [advance, countdown, modeResult, markerWord] <;> omega
  | dropPending => cases pending <;> simp [advance, countdown]; omega
  | restorePrefix r => cases saved <;> simp [advance, countdown]

structure Evaluation where
  result : Result
  data : LocalData
  steps : Nat
  deriving DecidableEq

/-- Total mathematical evaluation, justified by the all-state countdown. -/
def evaluate (control : Control) (D : LocalData) : Evaluation :=
  match control with
  | .inr r => ⟨r, D, 0⟩
  | .inl q =>
      let actual := advance q D
      let tail := evaluate actual.1 actual.2
      ⟨tail.result, tail.data, tail.steps + 1⟩
termination_by countdown control D
decreasing_by
  have decreased := advance_countdown q D
  omega

@[simp] theorem evaluate_result (r : Result) (D : LocalData) :
    evaluate (.inr r) D = ⟨r, D, 0⟩ := by rw [evaluate]

theorem evaluate_phase (q : Phase) (D : LocalData) :
    evaluate (.inl q) D =
      let tail := evaluate (advance q D).1 (advance q D).2
      ⟨tail.result, tail.data, tail.steps + 1⟩ := by rw [evaluate]

def phaseSteps (q : Phase) (D : LocalData) : Nat := (evaluate (.inl q) D).steps

def phaseResult (q : Phase) (regs : Registers R) (D : LocalData)
    (ctx : ∀ k, List (Γ k)) : Cfg Γ Λ R :=
  cfg (some (resultLabel (evaluate (.inl q) D).result)) (reset regs)
    (evaluate (.inl q) D).data ctx

theorem phaseSteps_pos (q : Phase) (D : LocalData) : 0 < phaseSteps q D := by
  rw [phaseSteps, evaluate_phase]
  exact Nat.zero_lt_succ _

theorem evaluate_steps_le (control : Control) (D : LocalData) :
    (evaluate control D).steps ≤ countdown control D := by
  cases control with
  | inr r => simp [countdown]
  | inl q =>
      rw [evaluate_phase]
      have ih := evaluate_steps_le (advance q D).1 (advance q D).2
      have decreased := advance_countdown q D
      exact Nat.le_trans (Nat.add_le_add_right ih 1) decreased
termination_by countdown control D
decreasing_by
  have decreased := advance_countdown q D
  omega

theorem phaseSteps_le_countdown (q : Phase) (D : LocalData) :
    phaseSteps q D ≤ countdown (.inl q) D := evaluate_steps_le (.inl q) D

private theorem evaluate_reset_localRun (control : Control) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (evaluate control D).steps
      (cfg (some (controlLabel control)) (reset regs) D ctx)
      (cfg (some (resultLabel (evaluate control D).result)) (reset regs)
        (evaluate control D).data ctx) := by
  cases control with
  | inr r =>
      simpa only [evaluate_result, controlLabel] using
        LocalRun.refl (caller := caller) (cfg (some (resultLabel r)) (reset regs) D ctx)
  | inl q =>
      simp only [evaluate_phase]
      refine LocalRun.cons ⟨True.intro, ?_⟩
        (evaluate_reset_localRun (advance q D).1 (advance q D).2 regs ctx)
      simpa only [controlLabel, reset_reset] using advance_step caller q D (reset regs) ctx
termination_by countdown control D
decreasing_by
  have decreased := advance_countdown q D
  omega

theorem phase_localRun (q : Phase) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (phaseSteps q D) (cfg (some (phaseLabel q)) regs D ctx)
      (phaseResult q regs D ctx) := by
  simp only [phaseSteps, phaseResult, evaluate_phase]
  exact LocalRun.cons ⟨True.intro, advance_step caller q D regs ctx⟩
    (evaluate_reset_localRun caller (advance q D).1 (advance q D).2 regs ctx)

theorem phase_iterate (q : Phase) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    (next caller)^[phaseSteps q D] (some (cfg (some (phaseLabel q)) regs D ctx)) =
      some (phaseResult q regs D ctx) :=
  LocalRun.iterate caller (phase_localRun caller q D regs ctx)

omit [DecidableEq K] in
@[simp] theorem phaseResult_reset (q : Phase) (regs : Registers R) (D : LocalData)
    (ctx : ∀ k, List (Γ k)) :
    phaseResult q (reset regs) D ctx = phaseResult (Λ := Λ) q regs D ctx := rfl

def remainingSteps (c : Cfg Γ Λ R) : Nat :=
  match c.l with
  | some (.inl q) => phaseSteps q (dataOfCfg c)
  | _ => 0

omit [DecidableEq K] in
theorem remainingSteps_control_cfg (control : Control) (regs : Registers R)
    (D : LocalData) (ctx : ∀ k, List (Γ k)) :
    remainingSteps (cfg (some (controlLabel (Λ := Λ) control)) regs D ctx) =
      (evaluate control D).steps := by
  cases control with
  | inl q => rfl
  | inr r => simp [remainingSteps, controlLabel, resultLabel, cfg]

omit [DecidableEq K] in
@[simp] theorem remainingSteps_phaseResult (q : Phase) (regs : Registers R) (D : LocalData)
    (ctx : ∀ k, List (Γ k)) : remainingSteps (phaseResult (Λ := Λ) q regs D ctx) = 0 := rfl

omit [DecidableEq K] in
theorem remainingSteps_pos_iff (c : Cfg Γ Λ R) :
    0 < remainingSteps c ↔ Owned c.l := by
  cases label : c.l with
  | none => simp [remainingSteps, Owned, label]
  | some labelValue =>
      cases labelValue with
      | inl q => simp [remainingSteps, Owned, label, phaseSteps_pos]
      | inr external => simp [remainingSteps, Owned, label]

omit [DecidableEq K] in
theorem owned_cases (c : Cfg Γ Λ R) (owned : Owned c.l) :
    ∃ q regs D ctx, c = cfg (some (phaseLabel q)) regs D ctx := by
  cases label : c.l with
  | none => simp [Owned, label] at owned
  | some labelValue =>
      cases labelValue with
      | inl q =>
          refine ⟨q, c.var, dataOfCfg c, (fun k => c.stk (.inr k)), ?_⟩
          simpa only [label, phaseLabel] using (cfg_eta c).symm
      | inr external => simp [Owned, label] at owned

omit [DecidableEq K] in
theorem phase_remaining (q : Phase) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    remainingSteps (cfg (some (phaseLabel (Λ := Λ) q)) regs D ctx) =
      remainingSteps (cfg (some (controlLabel (Λ := Λ) (advance q D).1))
        (reset regs) (advance q D).2 ctx) + 1 := by
  change phaseSteps q D = _
  rw [remainingSteps_control_cfg, phaseSteps, evaluate_phase]

theorem local_step_data {before after : Cfg Γ Λ R}
    (transition : LocalStep caller before after) :
    remainingSteps before = remainingSteps after + 1 ∧ after.var = reset before.var ∧
      (∀ k, after.stk (.inr k) = before.stk (.inr k)) := by
  obtain ⟨q, regs, D, ctx, rfl⟩ := owned_cases before transition.1
  have same := Option.some.inj ((advance_step caller q D regs ctx).symm.trans transition.2)
  subst after
  exact ⟨phase_remaining q D regs ctx, rfl, fun _ => rfl⟩

theorem local_step_remaining {before after : Cfg Γ Λ R}
    (transition : LocalStep caller before after) :
    remainingSteps before = remainingSteps after + 1 := (local_step_data caller transition).1

theorem local_progress (before : Cfg Γ Λ R) (positive : 0 < remainingSteps before) :
    ∃ after, step caller before = some after ∧ remainingSteps before = remainingSteps after + 1 := by
  obtain ⟨q, regs, D, ctx, rfl⟩ := owned_cases before ((remainingSteps_pos_iff before).mp positive)
  exact ⟨_, advance_step caller q D regs ctx, phase_remaining q D regs ctx⟩

theorem LocalRun.remaining {n : Nat} {a b : Cfg Γ Λ R} (run : LocalRun caller n a b) :
    remainingSteps a = n + remainingSteps b := by
  induction run with
  | refl => simp
  | cons head tail ih =>
      have first := local_step_remaining caller head
      omega

def runSteps (d : RotationDirection) (raw : Word) (path : List Branch) : Nat :=
  phaseSteps (.seek d) { source := raw, path := path }

theorem runSteps_pos (d : RotationDirection) (raw : Word) (path : List Branch) :
    0 < runSteps d raw path := phaseSteps_pos _ _

theorem runSteps_le (d : RotationDirection) (raw : Word) (path : List Branch) :
    runSteps d raw path ≤ 3 * raw.length + path.length + 5 := by
  simpa only [runSteps, countdown, List.length_nil, Nat.add_zero] using
    phaseSteps_le_countdown (.seek d) { source := raw, path := path }

theorem runSteps_le_conservative (d : RotationDirection) (raw : Word) (path : List Branch) :
    runSteps d raw path ≤ 4 * raw.length + path.length + 12 := by
  have bound := runSteps_le d raw path
  omega

theorem restoreScratch_prefix_localRun (mode : RestoreMode) (accepted rest : Word)
    (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller accepted.length
      (cfg (some (phaseLabel (.restoreScratch mode))) regs { D with scratch := accepted ++ rest } ctx)
      (cfg (some (phaseLabel (.restoreScratch mode)))
        (if accepted = [] then regs else reset regs)
        { D with source := accepted.reverse ++ D.source, scratch := rest } ctx) := by
  induction accepted generalizing D regs with
  | nil =>
      simpa using LocalRun.refl (caller := caller)
        (cfg (some (phaseLabel (.restoreScratch mode))) regs { D with scratch := rest } ctx)
  | cons tag accepted ih =>
      have first := restoreScratch_step_cons caller mode tag (accepted ++ rest) D regs ctx
      have tail := ih { D with source := tag :: D.source } (reset regs)
      simpa only [List.length_cons, List.cons_append, List.reverse_cons, List.append_assoc,
        List.singleton_append, List.nil_append, List.cons_ne_nil, ite_false, reset_reset, ite_self,
        Nat.add_comm 1 accepted.length] using
        LocalRun.trans caller (phase_step_localRun caller first) tail

theorem restorePrefix_prefix_localRun (r : Result) (accepted rest : Word)
    (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller accepted.length
      (cfg (some (phaseLabel (.restorePrefix r))) regs { D with saved := accepted ++ rest } ctx)
      (cfg (some (phaseLabel (.restorePrefix r)))
        (if accepted = [] then regs else reset regs)
        { D with source := accepted.reverse ++ D.source, saved := rest } ctx) := by
  induction accepted generalizing D regs with
  | nil =>
      simpa using LocalRun.refl (caller := caller)
        (cfg (some (phaseLabel (.restorePrefix r))) regs { D with saved := rest } ctx)
  | cons tag accepted ih =>
      have first := restorePrefix_step_cons caller r tag (accepted ++ rest) D regs ctx
      have tail := ih { D with source := tag :: D.source } (reset regs)
      simpa only [List.length_cons, List.cons_append, List.reverse_cons, List.append_assoc,
        List.singleton_append, List.nil_append, List.cons_ne_nil, ite_false, reset_reset, ite_self,
        Nat.add_comm 1 accepted.length] using
        LocalRun.trans caller (phase_step_localRun caller first) tail

theorem dropPending_prefix_localRun (accepted rest : List Unit) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller accepted.length
      (cfg (some (phaseLabel .dropPending)) regs { D with pending := accepted ++ rest } ctx)
      (cfg (some (phaseLabel .dropPending)) (if accepted = [] then regs else reset regs)
        { D with pending := rest } ctx) := by
  induction accepted generalizing regs with
  | nil =>
      simpa using LocalRun.refl (caller := caller)
        (cfg (some (phaseLabel .dropPending)) regs { D with pending := rest } ctx)
  | cons token accepted ih =>
      cases token
      have first := dropPending_step_cons caller (accepted ++ rest) D regs ctx
      simpa only [List.length_cons, List.cons_append, List.cons_ne_nil, ite_false,
        reset_reset, ite_self, Nat.add_comm 1 accepted.length] using
        LocalRun.trans caller (phase_step_localRun caller first) (ih (reset regs))

theorem restoreScratch_prefix (mode : RestoreMode) (accepted rest : Word)
    (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (next caller)^[accepted.length]
      (some (cfg (some (phaseLabel (.restoreScratch mode))) regs { D with scratch := accepted ++ rest } ctx)) =
      some (cfg (some (phaseLabel (.restoreScratch mode)))
        (if accepted = [] then regs else reset regs)
        { D with source := accepted.reverse ++ D.source, scratch := rest } ctx) :=
  LocalRun.iterate caller (restoreScratch_prefix_localRun caller mode accepted rest D regs ctx)

theorem restorePrefix_prefix (r : Result) (accepted rest : Word) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (next caller)^[accepted.length]
      (some (cfg (some (phaseLabel (.restorePrefix r))) regs { D with saved := accepted ++ rest } ctx)) =
      some (cfg (some (phaseLabel (.restorePrefix r)))
        (if accepted = [] then regs else reset regs)
        { D with source := accepted.reverse ++ D.source, saved := rest } ctx) :=
  LocalRun.iterate caller (restorePrefix_prefix_localRun caller r accepted rest D regs ctx)

theorem dropPending_prefix (accepted rest : List Unit) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (next caller)^[accepted.length]
      (some (cfg (some (phaseLabel .dropPending)) regs { D with pending := accepted ++ rest } ctx)) =
      some (cfg (some (phaseLabel .dropPending)) (if accepted = [] then regs else reset regs)
        { D with pending := rest } ctx) :=
  LocalRun.iterate caller (dropPending_prefix_localRun caller accepted rest D regs ctx)

def restorePrefixData (D : LocalData) : LocalData :=
  { D with source := D.saved.reverse ++ D.source, saved := [] }

def dropPendingData (D : LocalData) : LocalData :=
  { D with source := D.saved.reverse ++ D.source, saved := [], pending := [] }

def restoreScratchData (mode : RestoreMode) (D : LocalData) : LocalData :=
  { source := D.saved.reverse ++ markerWord mode ++ D.scratch.reverse ++ D.source,
    saved := [], scratch := [],
    pending := if modeResult mode = .success then D.pending else [], path := D.path }

def restoreScratchSteps (mode : RestoreMode) (D : LocalData) : Nat :=
  if modeResult mode = .success then D.scratch.length + D.saved.length + 2
  else D.scratch.length + D.pending.length + D.saved.length + 3

theorem restorePrefix_localRun (r : Result) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (D.saved.length + 1)
      (cfg (some (phaseLabel (.restorePrefix r))) regs D ctx)
      (cfg (some (resultLabel r)) (reset regs) (restorePrefixData D) ctx) := by
  let midRegs := if D.saved = [] then regs else reset regs
  have first := restorePrefix_prefix_localRun caller r D.saved [] D regs ctx
  have last := phase_step_localRun caller
    (restorePrefix_step_nil caller r (restorePrefixData D) midRegs ctx)
  have joined := LocalRun.trans caller first last
  simpa only [restorePrefixData, midRegs, List.append_nil, apply_ite,
    reset_reset, ite_self] using joined

theorem dropPending_localRun (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (D.pending.length + D.saved.length + 2)
      (cfg (some (phaseLabel .dropPending)) regs D ctx)
      (cfg (some (resultLabel .failure)) (reset regs) (dropPendingData D) ctx) := by
  let midRegs := if D.pending = [] then regs else reset regs
  let cleared : LocalData := { D with pending := [] }
  have first := dropPending_prefix_localRun caller D.pending [] D regs ctx
  have probe := phase_step_localRun caller (dropPending_step_nil caller cleared midRegs ctx)
  have last := restorePrefix_localRun caller .failure cleared (reset midRegs) ctx
  have joined := LocalRun.trans caller (LocalRun.trans caller first probe) last
  rw [show (D.pending.length + 1) + (D.saved.length + 1) =
    D.pending.length + D.saved.length + 2 by omega] at joined
  simpa [midRegs, cleared, restorePrefixData, dropPendingData, apply_ite, reset_reset] using joined

theorem restoreScratch_localRun (mode : RestoreMode) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (restoreScratchSteps mode D)
      (cfg (some (phaseLabel (.restoreScratch mode))) regs D ctx)
      (cfg (some (resultLabel (modeResult mode))) (reset regs) (restoreScratchData mode D) ctx) := by
  let midRegs := if D.scratch = [] then regs else reset regs
  let moved : LocalData := { D with source := D.scratch.reverse ++ D.source, scratch := [] }
  let marked : LocalData := { moved with source := markerWord mode ++ moved.source }
  have first := restoreScratch_prefix_localRun caller mode D.scratch [] D regs ctx
  have probe := phase_step_localRun caller (restoreScratch_step_nil caller mode moved midRegs ctx)
  by_cases success : modeResult mode = .success
  · have probe' : LocalRun caller 1
        (cfg (some (phaseLabel (.restoreScratch mode))) midRegs moved ctx)
        (cfg (some (phaseLabel (.restorePrefix .success))) (reset midRegs) marked ctx) := by
      simpa only [success, ite_true, moved, marked] using probe
    have last := restorePrefix_localRun caller .success marked (reset midRegs) ctx
    have joined := LocalRun.trans caller (LocalRun.trans caller first probe') last
    rw [show (D.scratch.length + 1) + (D.saved.length + 1) =
      D.scratch.length + D.saved.length + 2 by omega] at joined
    simpa [restoreScratchSteps, restoreScratchData, restorePrefixData, success,
      moved, marked, midRegs, List.append_assoc, apply_ite, reset_reset] using joined
  · have failure : modeResult mode = .failure := by
      cases mode <;> simp_all [modeResult]
    have probe' : LocalRun caller 1
        (cfg (some (phaseLabel (.restoreScratch mode))) midRegs moved ctx)
        (cfg (some (phaseLabel .dropPending)) (reset midRegs) marked ctx) := by
      simpa only [success, ite_false, moved, marked] using probe
    have last := dropPending_localRun caller marked (reset midRegs) ctx
    have joined := LocalRun.trans caller (LocalRun.trans caller first probe') last
    rw [show (D.scratch.length + 1) + (D.pending.length + D.saved.length + 2) =
      D.scratch.length + D.pending.length + D.saved.length + 3 by omega] at joined
    simpa [restoreScratchSteps, restoreScratchData, dropPendingData, success, failure,
      moved, marked, midRegs, List.append_assoc, apply_ite, reset_reset] using joined

theorem restorePrefix_iterate (r : Result) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    (next caller)^[D.saved.length + 1]
      (some (cfg (some (phaseLabel (.restorePrefix r))) regs D ctx)) =
      some (cfg (some (resultLabel r)) (reset regs) (restorePrefixData D) ctx) :=
  LocalRun.iterate caller (restorePrefix_localRun caller r D regs ctx)

theorem dropPending_iterate (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (next caller)^[D.pending.length + D.saved.length + 2]
      (some (cfg (some (phaseLabel .dropPending)) regs D ctx)) =
      some (cfg (some (resultLabel .failure)) (reset regs) (dropPendingData D) ctx) :=
  LocalRun.iterate caller (dropPending_localRun caller D regs ctx)

theorem restoreScratch_iterate (mode : RestoreMode) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    (next caller)^[restoreScratchSteps mode D]
      (some (cfg (some (phaseLabel (.restoreScratch mode))) regs D ctx)) =
      some (cfg (some (resultLabel (modeResult mode))) (reset regs) (restoreScratchData mode D) ctx) :=
  LocalRun.iterate caller (restoreScratch_localRun caller mode D regs ctx)

/-! ## Scanning, represented execution and source refinement -/

/-- Exact represented first-return clock; no runtime callback evaluates it. -/
def representedClock : RotationDirection → List Branch → BinaryTree Unit → Nat
  | _, [], .nil => 4
  | .left, [], .node _ A .nil => 2 * (treeCode A).length + 6
  | .left, [], .node _ A (.node _ _ _) => 2 * (treeCode A).length + 5
  | .right, [], .node _ .nil _ => 4
  | .right, [], .node _ (.node _ A _) _ => 2 * (treeCode A).length + 4
  | _, _ :: _, .nil => 3
  | d, .left :: p, .node _ l _ => representedClock d p l + 2
  | d, .right :: p, .node _ l r =>
      representedClock d p r + 2 * (1 + (treeCode l).length)

/-- Actual physical tail: the head that fails at nil has already been popped. -/
def remainingPath : List Branch → BinaryTree Unit → List Branch
  | [], _ => []
  | _ :: p, .nil => p
  | .left :: p, .node _ l _ => remainingPath p l
  | .right :: p, .node _ _ r => remainingPath p r

/-- Successful ancestor descents, excluding a final missing-node observation. -/
def descentCount : List Branch → BinaryTree Unit → Nat
  | [], _ => 0
  | _ :: _, .nil => 0
  | .left :: p, .node _ l _ => 1 + descentCount p l
  | .right :: p, .node _ _ r => 1 + descentCount p r

/-- Number of source Tags physically moved to saved during navigation. -/
def navigationLength : List Branch → BinaryTree Unit → Nat
  | [], _ => 0
  | _ :: _, .nil => 0
  | .left :: p, .node _ l _ => 1 + navigationLength p l
  | .right :: p, .node _ l r =>
      1 + (treeCode l).length + navigationLength p r

/-- The focused tree before the final empty-path or missing-node observation. -/
def stoppedTree : List Branch → BinaryTree Unit → BinaryTree Unit
  | [], t => t
  | _ :: _, .nil => .nil
  | .left :: p, .node _ l _ => stoppedTree p l
  | .right :: p, .node _ _ r => stoppedTree p r

/-- The untested path at the stopped cursor; unlike remainingPath it keeps a failing head. -/
def stoppedPath : List Branch → BinaryTree Unit → List Branch
  | [], _ => []
  | b :: p, .nil => b :: p
  | .left :: p, .node _ l _ => stoppedPath p l
  | .right :: p, .node _ _ r => stoppedPath p r

omit [DecidableEq K] in
theorem remainingPath_suffix (p : List Branch) (s : BinaryTree Unit) :
    ∃ consumed, p = consumed ++ remainingPath p s := by
  induction p generalizing s with
  | nil => exact ⟨[], rfl⟩
  | cons b p ih =>
      cases s with
      | nil => exact ⟨[b], rfl⟩
      | node a l r =>
          cases b with
          | left =>
              obtain ⟨consumed, word⟩ := ih l
              exact ⟨.left :: consumed, congrArg (List.cons .left) word⟩
          | right =>
              obtain ⟨consumed, word⟩ := ih r
              exact ⟨.right :: consumed, congrArg (List.cons .right) word⟩

omit [DecidableEq K] in
theorem remainingPath_eq_stopped (p : List Branch) (s : BinaryTree Unit) :
    remainingPath p s =
      if stoppedPath p s = [] then [] else (stoppedPath p s).tail := by
  induction p generalizing s with
  | nil => rfl
  | cons b p ih =>
      cases s with
      | nil => simp only [remainingPath, stoppedPath, List.cons_ne_nil, ite_false,
          List.tail_cons]
      | node a l r => cases b with
        | left => exact ih l
        | right => exact ih r

omit [DecidableEq K] in
theorem stoppedTree_nil_of_path_nonempty (p : List Branch) (s : BinaryTree Unit)
    (nonempty : stoppedPath p s ≠ []) : stoppedTree p s = .nil := by
  induction p generalizing s with
  | nil => exact (nonempty rfl).elim
  | cons b p ih =>
      cases s with
      | nil => rfl
      | node a l r => cases b with
        | left => exact ih l nonempty
        | right => exact ih r nonempty

omit [DecidableEq K] in
theorem representedClock_eq_stopped (d : RotationDirection) (p : List Branch)
    (s : BinaryTree Unit) :
    representedClock d p s = 2 * navigationLength p s +
      if stoppedPath p s = [] then representedClock d [] (stoppedTree p s) else 3 := by
  induction p generalizing s with
  | nil => simp only [navigationLength, stoppedPath, stoppedTree, ite_true,
      Nat.mul_zero, Nat.zero_add]
  | cons b p ih =>
      cases s with
      | nil => simp only [representedClock, navigationLength, stoppedPath,
          List.cons_ne_nil, ite_false, Nat.mul_zero, Nat.zero_add]
      | node a l r =>
          cases b with
          | left =>
              simp only [representedClock, navigationLength, stoppedPath, stoppedTree]
              rw [ih l]
              by_cases ending : stoppedPath p l = [] <;> simp [ending] <;> omega
          | right =>
              simp only [representedClock, navigationLength, stoppedPath, stoppedTree]
              rw [ih r]
              by_cases ending : stoppedPath p r = [] <;> simp [ending] <;> omega

/-- A nearest-focus-first frame; its Unit payload is the actual encoded payload. -/
inductive PositionFrame where
  | cameLeft (right : BinaryTree Unit)
  | cameRight (left : BinaryTree Unit)

def plugFrames : List PositionFrame → BinaryTree Unit → BinaryTree Unit
  | [], focus => focus
  | .cameLeft right :: outer, focus => plugFrames outer (.node () focus right)
  | .cameRight left :: outer, focus => plugFrames outer (.node () left focus)

def contextPrefix : List PositionFrame → Word
  | [] => []
  | .cameLeft _ :: outer => contextPrefix outer ++ [nodeTag]
  | .cameRight left :: outer => contextPrefix outer ++ [nodeTag] ++ treeCode left

def contextSuffix : List PositionFrame → Word
  | [] => []
  | .cameLeft right :: outer => treeCode right ++ contextSuffix outer
  | .cameRight _ :: outer => contextSuffix outer

omit [DecidableEq K] in
theorem treeCode_plugFrames (frames : List PositionFrame) (focus : BinaryTree Unit) :
    treeCode (plugFrames frames focus) =
      contextPrefix frames ++ treeCode focus ++ contextSuffix frames := by
  induction frames generalizing focus with
  | nil => simp only [plugFrames, contextPrefix, contextSuffix, List.nil_append, List.append_nil]
  | cons frame outer ih =>
      cases frame with
      | cameLeft right =>
          rw [plugFrames, ih]
          simp only [contextPrefix, contextSuffix, treeCode, List.append_assoc,
            List.cons_append, List.nil_append]
      | cameRight left =>
          rw [plugFrames, ih]
          simp only [contextPrefix, contextSuffix, treeCode, List.append_assoc,
            List.cons_append, List.nil_append]

omit [DecidableEq K] in
theorem source_root (d : RotationDirection) (s : BinaryTree Unit) :
    applyMoveRun ⟨d, []⟩ s = ((rotateRun d s).1, (rotateRun d s).2 + 1) :=
  applyAtRun_root (rotateRun d) s

omit [DecidableEq K] in
theorem source_nil_cons (d : RotationDirection) (b : Branch) (p : List Branch) :
    applyMoveRun ⟨d, b :: p⟩ (.nil : BinaryTree Unit) = (none, 2) :=
  applyAtRun_nil_cons (rotateRun d) b p

omit [DecidableEq K] in
theorem source_left (d : RotationDirection) (p : List Branch) (l r : BinaryTree Unit) :
    applyMoveRun ⟨d, .left :: p⟩ (.node () l r) =
      let actual := applyMoveRun ⟨d, p⟩ l
      match actual.1 with
      | none => (none, actual.2 + 2)
      | some child => (some (.node () child r), actual.2 + 3) := by
  unfold applyMoveRun
  rw [applyAtRun_left]
  dsimp only
  cases result : (applyAtRun (rotateRun d) p l).1 <;> rfl

omit [DecidableEq K] in
theorem source_right (d : RotationDirection) (p : List Branch) (l r : BinaryTree Unit) :
    applyMoveRun ⟨d, .right :: p⟩ (.node () l r) =
      let actual := applyMoveRun ⟨d, p⟩ r
      match actual.1 with
      | none => (none, actual.2 + 2)
      | some child => (some (.node () l child), actual.2 + 3) := by
  unfold applyMoveRun
  rw [applyAtRun_right]
  dsimp only
  cases result : (applyAtRun (rotateRun d) p r).1 <;> rfl

omit [DecidableEq K] in
theorem source_cost_eq_stopped (d : RotationDirection) (p : List Branch)
    (s : BinaryTree Unit) :
    (applyMoveRun ⟨d, p⟩ s).2 =
      if (applyMoveRun ⟨d, p⟩ s).1.isSome then 3 * descentCount p s + 5
      else 2 * descentCount p s + if stoppedPath p s = [] then 3 else 2 := by
  induction p generalizing s with
  | nil =>
      rw [source_root]
      cases actual : (rotateRun d s).1 with
      | none =>
          rw [rotateRun_cost_of_none d s actual]
          simp only [Option.isSome_none, Bool.false_eq_true, ite_false,
            descentCount, stoppedPath, ite_true, Nat.mul_zero, Nat.zero_add]
      | some t =>
          rw [rotateRun_cost_of_some d s t actual]
          simp only [Option.isSome_some, ite_true, descentCount,
            Nat.mul_zero, Nat.zero_add]
  | cons b p ih =>
      cases s with
      | nil => simp [source_nil_cons, descentCount, stoppedPath]
      | node a l r =>
          cases a
          cases b with
          | left =>
              have child := ih l
              cases actual : (applyMoveRun ⟨d, p⟩ l).1 <;>
                by_cases ending : stoppedPath p l = [] <;>
                simp [source_left, actual, descentCount, stoppedPath, ending] at child ⊢ <;> omega
          | right =>
              have child := ih r
              cases actual : (applyMoveRun ⟨d, p⟩ r).1 <;>
                by_cases ending : stoppedPath p r = [] <;>
                simp [source_right, actual, descentCount, stoppedPath, ending] at child ⊢ <;> omega

omit [DecidableEq K] in
theorem remainingPath_nil_of_source_success (d : RotationDirection) (p : List Branch)
    (s t : BinaryTree Unit) (returned : (applyMoveRun ⟨d, p⟩ s).1 = some t) :
    remainingPath p s = [] := by
  induction p generalizing s t with
  | nil => rfl
  | cons b p ih =>
      cases s with
      | nil => simp only [source_nil_cons, reduceCtorEq] at returned
      | node a l r =>
          cases a
          cases b with
          | left =>
              cases actual : (applyMoveRun ⟨d, p⟩ l).1 with
              | none => simp only [source_left, actual, reduceCtorEq] at returned
              | some child => exact ih l child actual
          | right =>
              cases actual : (applyMoveRun ⟨d, p⟩ r).1 with
              | none => simp only [source_right, actual, reduceCtorEq] at returned
              | some child => exact ih r child actual

/-- A word whose scan does not yet discharge the last pending slot. -/
inductive Continues : Word → Nat → Nat → Prop where
  | nil (h : Nat) : Continues [] h h
  | node {accepted : Word} {h k : Nat} :
      Continues accepted h k → Continues (accepted ++ [nodeTag]) h (k + 1)
  | empty {accepted : Word} {h k : Nat} :
      Continues accepted h (k + 2) → Continues (accepted ++ [emptyTag]) h (k + 1)

omit [DecidableEq K] in
theorem continues_of_openPrefix {accepted : Word} {p : Nat}
    (opened : TreeParserMachine.OpenPrefix accepted p) : Continues accepted 1 p := by
  induction opened with
  | nil => exact .nil 1
  | node opened ih => exact .node ih
  | empty opened ih => exact .empty ih

/-- Zero accepted symbols preserve stale fields; positive scan prefixes reset them. -/
def afterScanRegisters (accepted : Word) (regs : Registers R) : Registers R :=
  if accepted = [] then regs else reset regs

omit [DecidableEq K] in
@[simp] theorem reset_afterScanRegisters (accepted : Word) (regs : Registers R) :
    reset (afterScanRegisters accepted regs) = reset regs := by
  cases accepted <;> rfl

omit [DecidableEq K] in
@[simp] theorem afterScanRegisters_append (accepted : Word) (tag : Tag)
    (regs : Registers R) : afterScanRegisters (accepted ++ [tag]) regs = reset regs := by
  simp only [afterScanRegisters, List.append_eq_nil_iff, List.cons_ne_nil, and_false, ite_false]

/-- Every continued prefix is an actual owned segment in the saved-word scanner. -/
theorem scanPrefix_continues_localRun {accepted : Word} {h k : Nat}
    (continued : Continues accepted h k) (d : RotationDirection) (raw : Word)
    (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller accepted.length
      (cfg (some (phaseLabel (.scanPrefix d))) regs
        { D with source := accepted ++ raw, pending := List.replicate h () } ctx)
      (cfg (some (phaseLabel (.scanPrefix d))) (afterScanRegisters accepted regs)
        { D with
          source := raw,
          saved := accepted.reverse ++ D.saved,
          pending := List.replicate k () } ctx) := by
  induction continued generalizing raw D regs with
  | nil h =>
      simpa only [List.length_nil, List.nil_append, List.reverse_nil,
        afterScanRegisters, ite_true] using
        (LocalRun.refl (caller := caller)
          (cfg (some (phaseLabel (.scanPrefix d))) regs
            { D with source := raw, pending := List.replicate h () } ctx))
  | @node accepted h k continued ih =>
      let middle : LocalData := { D with
        source := nodeTag :: raw,
        saved := accepted.reverse ++ D.saved,
        pending := List.replicate k () }
      have first := ih (nodeTag :: raw) D regs
      have last : LocalRun caller 1
          (cfg (some (phaseLabel (.scanPrefix d))) (afterScanRegisters accepted regs) middle ctx)
          (cfg (some (phaseLabel (.scanPrefix d))) (reset regs)
            { D with
              source := raw,
              saved := nodeTag :: (accepted.reverse ++ D.saved),
              pending := List.replicate (k + 1) () } ctx) := by
        apply LocalRun.single caller
        refine ⟨True.intro, ?_⟩
        simpa only [middle, reset_afterScanRegisters, List.replicate_succ] using
          scanPrefix_step_node caller d raw middle (afterScanRegisters accepted regs) ctx
      have joined := LocalRun.trans caller first last
      simpa only [middle, List.length_append, List.length_singleton, List.append_assoc,
        List.singleton_append, List.reverse_append, List.reverse_cons, List.reverse_nil,
        List.nil_append, List.cons_append, afterScanRegisters_append] using joined
  | @empty accepted h k continued ih =>
      let middle : LocalData := { D with
        source := emptyTag :: raw,
        saved := accepted.reverse ++ D.saved,
        pending := List.replicate (k + 2) () }
      have first := ih (emptyTag :: raw) D regs
      have last : LocalRun caller 1
          (cfg (some (phaseLabel (.scanPrefix d))) (afterScanRegisters accepted regs) middle ctx)
          (cfg (some (phaseLabel (.scanPrefix d))) (reset regs)
            { D with
              source := raw,
              saved := emptyTag :: (accepted.reverse ++ D.saved),
              pending := List.replicate (k + 1) () } ctx) := by
        apply LocalRun.single caller
        refine ⟨True.intro, ?_⟩
        simpa only [middle, List.replicate_succ, reset_afterScanRegisters] using
          scanPrefix_step_empty_continue caller d raw (List.replicate k ()) middle
            (afterScanRegisters accepted regs) ctx
      have joined := LocalRun.trans caller first last
      simpa only [middle, List.length_append, List.length_singleton, List.append_assoc,
        List.singleton_append, List.reverse_append, List.reverse_cons, List.reverse_nil,
        List.nil_append, List.cons_append, afterScanRegisters_append] using joined

/-- Every continued prefix is an actual owned segment in either scratch scanner. -/
theorem scanScratch_continues_localRun {accepted : Word} {h k : Nat}
    (continued : Continues accepted h k) (d : RotationDirection) (raw : Word)
    (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller accepted.length
      (cfg (some (phaseLabel (.scanScratch d))) regs
        { D with source := accepted ++ raw, pending := List.replicate h () } ctx)
      (cfg (some (phaseLabel (.scanScratch d))) (afterScanRegisters accepted regs)
        { D with
          source := raw,
          scratch := accepted.reverse ++ D.scratch,
          pending := List.replicate k () } ctx) := by
  induction continued generalizing raw D regs with
  | nil h =>
      simpa only [List.length_nil, List.nil_append, List.reverse_nil,
        afterScanRegisters, ite_true] using
        (LocalRun.refl (caller := caller)
          (cfg (some (phaseLabel (.scanScratch d))) regs
            { D with source := raw, pending := List.replicate h () } ctx))
  | @node accepted h k continued ih =>
      let middle : LocalData := { D with
        source := nodeTag :: raw,
        scratch := accepted.reverse ++ D.scratch,
        pending := List.replicate k () }
      have first := ih (nodeTag :: raw) D regs
      have last : LocalRun caller 1
          (cfg (some (phaseLabel (.scanScratch d))) (afterScanRegisters accepted regs) middle ctx)
          (cfg (some (phaseLabel (.scanScratch d))) (reset regs)
            { D with
              source := raw,
              scratch := nodeTag :: (accepted.reverse ++ D.scratch),
              pending := List.replicate (k + 1) () } ctx) := by
        apply LocalRun.single caller
        refine ⟨True.intro, ?_⟩
        simpa only [middle, reset_afterScanRegisters, List.replicate_succ] using
          scanScratch_step_node caller d raw middle (afterScanRegisters accepted regs) ctx
      have joined := LocalRun.trans caller first last
      simpa only [middle, List.length_append, List.length_singleton, List.append_assoc,
        List.singleton_append, List.reverse_append, List.reverse_cons, List.reverse_nil,
        List.nil_append, List.cons_append, afterScanRegisters_append] using joined
  | @empty accepted h k continued ih =>
      let middle : LocalData := { D with
        source := emptyTag :: raw,
        scratch := accepted.reverse ++ D.scratch,
        pending := List.replicate (k + 2) () }
      have first := ih (emptyTag :: raw) D regs
      have last : LocalRun caller 1
          (cfg (some (phaseLabel (.scanScratch d))) (afterScanRegisters accepted regs) middle ctx)
          (cfg (some (phaseLabel (.scanScratch d))) (reset regs)
            { D with
              source := raw,
              scratch := emptyTag :: (accepted.reverse ++ D.scratch),
              pending := List.replicate (k + 1) () } ctx) := by
        apply LocalRun.single caller
        refine ⟨True.intro, ?_⟩
        simpa only [middle, List.replicate_succ, reset_afterScanRegisters] using
          scanScratch_step_empty_continue caller d raw (List.replicate k ()) middle
            (afterScanRegisters accepted regs) ctx
      have joined := LocalRun.trans caller first last
      simpa only [middle, List.length_append, List.length_singleton, List.append_assoc,
        List.singleton_append, List.reverse_append, List.reverse_cons, List.reverse_nil,
        List.nil_append, List.cons_append, afterScanRegisters_append] using joined

/-- A completed subtree consumes one pending slot and chooses this saved-scanner phase. -/
def prefixScanEnd (d : RotationDirection) (outer : List Unit) : Phase :=
  if outer = [] then .seek d else .scanPrefix d

/-- Scratch completion can finish the left scan or perform the right marker insertion. -/
def scratchScanEnd (d : RotationDirection) (outer : List Unit) : Phase :=
  if outer = [] then
    match d with
    | .left => .checkRight
    | .right => .restoreScratch .successRight
  else .scanScratch d

/-- The right scanner has already pushed its node in the last scanning activation. -/
def scratchScanSource (d : RotationDirection) (outer : List Unit) (raw : Word) : Word :=
  if outer = [] then
    match d with
    | .left => raw
    | .right => nodeTag :: raw
  else raw

/-- One represented tree is scanned into an arbitrary saved accumulator, with every outer slot. -/
theorem scanPrefix_treeCode_localRun (d : RotationDirection) (t : BinaryTree Unit)
    (raw : Word) (outer : List Unit) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (treeCode t).length
      (cfg (some (phaseLabel (.scanPrefix d))) regs
        { D with source := treeCode t ++ raw, pending := () :: outer } ctx)
      (cfg (some (phaseLabel (prefixScanEnd d outer))) (reset regs)
        { D with
          source := raw,
          saved := (treeCode t).reverse ++ D.saved,
          pending := outer } ctx) := by
  induction t generalizing raw outer D regs with
  | nil =>
      cases outer with
      | nil =>
          apply LocalRun.single caller
          refine ⟨True.intro, ?_⟩
          simpa only [treeCode, List.singleton_append, List.reverse_cons, List.reverse_nil,
            List.nil_append, prefixScanEnd, ite_true] using
            scanPrefix_step_empty_finish caller d raw { D with pending := [()] } regs ctx rfl
      | cons token outer =>
          cases token
          apply LocalRun.single caller
          refine ⟨True.intro, ?_⟩
          simpa only [treeCode, List.singleton_append, List.reverse_cons, List.reverse_nil,
            List.nil_append, prefixScanEnd, List.cons_ne_nil, ite_false] using
            scanPrefix_step_empty_continue caller d raw outer D regs ctx
  | node a l r ihl ihr =>
      cases a
      have head : LocalRun caller 1
          (cfg (some (phaseLabel (.scanPrefix d))) regs
            { D with source := treeCode (.node () l r) ++ raw, pending := () :: outer } ctx)
          (cfg (some (phaseLabel (.scanPrefix d))) (reset regs)
            { D with
              source := treeCode l ++ (treeCode r ++ raw),
              saved := nodeTag :: D.saved,
              pending := () :: () :: outer } ctx) := by
        apply LocalRun.single caller
        refine ⟨True.intro, ?_⟩
        simpa only [treeCode, List.cons_append, List.append_assoc] using
          scanPrefix_step_node caller d (treeCode l ++ (treeCode r ++ raw))
            { D with pending := () :: outer } regs ctx
      have left := ihl (treeCode r ++ raw) (() :: outer)
        { D with saved := nodeTag :: D.saved } (reset regs)
      simp only [prefixScanEnd, List.cons_ne_nil, ite_false, reset_reset] at left
      have right := ihr raw outer
        { D with saved := (treeCode l).reverse ++ nodeTag :: D.saved } (reset regs)
      have joined := LocalRun.trans caller head (LocalRun.trans caller left right)
      simpa only [treeCode, List.length_cons, List.length_append, List.reverse_cons,
        List.reverse_append, List.append_assoc, List.singleton_append, reset_reset,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using joined

/-- One represented tree is scanned into arbitrary scratch, with a literal untouched suffix. -/
theorem scanScratch_treeCode_localRun (d : RotationDirection) (t : BinaryTree Unit)
    (raw : Word) (outer : List Unit) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (treeCode t).length
      (cfg (some (phaseLabel (.scanScratch d))) regs
        { D with source := treeCode t ++ raw, pending := () :: outer } ctx)
      (cfg (some (phaseLabel (scratchScanEnd d outer))) (reset regs)
        { D with
          source := scratchScanSource d outer raw,
          scratch := (treeCode t).reverse ++ D.scratch,
          pending := outer } ctx) := by
  induction t generalizing raw outer D regs with
  | nil =>
      cases outer with
      | nil =>
          cases d with
          | left =>
              apply LocalRun.single caller
              refine ⟨True.intro, ?_⟩
              simpa only [treeCode, List.singleton_append, List.reverse_cons,
                List.reverse_nil, List.nil_append, scratchScanEnd, scratchScanSource,
                ite_true] using
                scanScratch_left_step_finish caller raw { D with pending := [()] } regs ctx rfl
          | right =>
              apply LocalRun.single caller
              refine ⟨True.intro, ?_⟩
              simpa only [treeCode, List.singleton_append, List.reverse_cons,
                List.reverse_nil, List.nil_append, scratchScanEnd, scratchScanSource,
                ite_true] using
                scanScratch_right_step_finish caller raw { D with pending := [()] } regs ctx rfl
      | cons token outer =>
          cases token
          apply LocalRun.single caller
          refine ⟨True.intro, ?_⟩
          simpa only [treeCode, List.singleton_append, List.reverse_cons, List.reverse_nil,
            List.nil_append, scratchScanEnd, scratchScanSource, List.cons_ne_nil, ite_false] using
            scanScratch_step_empty_continue caller d raw outer D regs ctx
  | node a l r ihl ihr =>
      cases a
      have head : LocalRun caller 1
          (cfg (some (phaseLabel (.scanScratch d))) regs
            { D with source := treeCode (.node () l r) ++ raw, pending := () :: outer } ctx)
          (cfg (some (phaseLabel (.scanScratch d))) (reset regs)
            { D with
              source := treeCode l ++ (treeCode r ++ raw),
              scratch := nodeTag :: D.scratch,
              pending := () :: () :: outer } ctx) := by
        apply LocalRun.single caller
        refine ⟨True.intro, ?_⟩
        simpa only [treeCode, List.cons_append, List.append_assoc] using
          scanScratch_step_node caller d (treeCode l ++ (treeCode r ++ raw))
            { D with pending := () :: outer } regs ctx
      have left := ihl (treeCode r ++ raw) (() :: outer)
        { D with scratch := nodeTag :: D.scratch } (reset regs)
      simp only [scratchScanEnd, scratchScanSource, List.cons_ne_nil, ite_false, reset_reset] at left
      have right := ihr raw outer
        { D with scratch := (treeCode l).reverse ++ nodeTag :: D.scratch } (reset regs)
      have joined := LocalRun.trans caller head (LocalRun.trans caller left right)
      simpa only [treeCode, List.length_cons, List.length_append, List.reverse_cons,
        List.reverse_append, List.append_assoc, List.singleton_append, reset_reset,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using joined


/-- A continued saved scan pays for the blocked probe, pending cleanup and saved restoration. -/
theorem scanPrefix_blocked_localRun {accepted raw : Word} {h k : Nat}
    (continued : Continues accepted h k) (blocked : TreeParserMachine.Blocked raw)
    (d : RotationDirection) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (2 * accepted.length + k + D.saved.length + 3)
      (cfg (some (phaseLabel (.scanPrefix d))) regs
        { D with source := accepted ++ raw, pending := List.replicate h () } ctx)
      (cfg (some (resultLabel .failure)) (reset regs)
        { D with
          source := D.saved.reverse ++ accepted ++ raw,
          saved := [], pending := [] } ctx) := by
  let middle : LocalData := { D with
    source := raw, saved := accepted.reverse ++ D.saved, pending := List.replicate k () }
  have first := scanPrefix_continues_localRun caller continued d raw D regs ctx
  have probe : LocalRun caller 1
      (cfg (some (phaseLabel (.scanPrefix d))) (afterScanRegisters accepted regs) middle ctx)
      (cfg (some (phaseLabel .dropPending)) (reset regs) middle ctx) := by
    apply LocalRun.single caller
    refine ⟨True.intro, ?_⟩
    cases raw with
    | nil =>
        simpa only [middle, reset_afterScanRegisters] using
          scanPrefix_step_nil caller d middle (afterScanRegisters accepted regs) ctx
    | cons tag raw =>
        simpa only [middle, reset_afterScanRegisters] using
          scanPrefix_step_foreign caller d tag raw middle (afterScanRegisters accepted regs)
            ctx blocked.1 blocked.2
  have cleanup := dropPending_localRun caller middle (reset regs) ctx
  have joined := LocalRun.trans caller first (LocalRun.trans caller probe cleanup)
  convert joined using 1 <;>
    simp [middle, dropPendingData, List.reverse_append, List.append_assoc]; omega

/-- A continued scratch scan restores both accumulators and the exact missing root markers. -/
theorem scanScratch_blocked_localRun {accepted raw : Word} {h k : Nat}
    (continued : Continues accepted h k) (blocked : TreeParserMachine.Blocked raw)
    (d : RotationDirection) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (2 * accepted.length + k + D.scratch.length + D.saved.length + 4)
      (cfg (some (phaseLabel (.scanScratch d))) regs
        { D with source := accepted ++ raw, pending := List.replicate h () } ctx)
      (cfg (some (resultLabel .failure)) (reset regs)
        { source := D.saved.reverse ++ markerWord (scratchFailure d) ++
            D.scratch.reverse ++ accepted ++ raw,
          saved := [], scratch := [], pending := [], path := D.path } ctx) := by
  let middle : LocalData := { D with
    source := raw, scratch := accepted.reverse ++ D.scratch, pending := List.replicate k () }
  have first := scanScratch_continues_localRun caller continued d raw D regs ctx
  have probe : LocalRun caller 1
      (cfg (some (phaseLabel (.scanScratch d))) (afterScanRegisters accepted regs) middle ctx)
      (cfg (some (phaseLabel (.restoreScratch (scratchFailure d)))) (reset regs) middle ctx) := by
    apply LocalRun.single caller
    refine ⟨True.intro, ?_⟩
    cases raw with
    | nil =>
        simpa only [middle, reset_afterScanRegisters] using
          scanScratch_step_nil caller d middle (afterScanRegisters accepted regs) ctx
    | cons tag raw =>
        simpa only [middle, reset_afterScanRegisters] using
          scanScratch_step_foreign caller d tag raw middle (afterScanRegisters accepted regs)
            ctx blocked.1 blocked.2
  have cleanup := restoreScratch_localRun caller (scratchFailure d) middle (reset regs) ctx
  have joined := LocalRun.trans caller first (LocalRun.trans caller probe cleanup)
  cases d <;> convert joined using 1 <;>
    simp [middle, restoreScratchSteps, restoreScratchData, scratchFailure, modeResult,
      List.reverse_append, List.append_assoc] <;> omega

/-- A clean left-root pattern returns after the actual scan, check and marker restoration. -/
theorem root_left_pattern_localRun (A : BinaryTree Unit) (z f : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (2 * (treeCode A).length + 5 + f.length)
      (cfg (some (phaseLabel (.seek .left))) regs
        { source := nodeTag :: (treeCode A ++ nodeTag :: z), saved := f } ctx)
      (cfg (some (resultLabel .success)) (reset regs)
        { source := f.reverse ++ [nodeTag, nodeTag] ++ treeCode A ++ z } ctx) := by
  let base : LocalData := { saved := f }
  let scanned : LocalData := { source := nodeTag :: z, saved := f, scratch := (treeCode A).reverse }
  have seek := phase_step_localRun caller (
    seek_step_path_nil caller .left
      { base with source := nodeTag :: (treeCode A ++ nodeTag :: z) } regs ctx)
  have start := phase_step_localRun caller (
    start_left_step_node caller (treeCode A ++ nodeTag :: z) base (reset regs) ctx)
  have scan := scanScratch_treeCode_localRun caller .left A (nodeTag :: z) [] base
    (reset regs) ctx
  simp only [scratchScanEnd, scratchScanSource, ite_true, reset_reset] at scan
  have check := phase_step_localRun caller (
    checkRight_step_node caller z scanned (reset regs) ctx)
  have restore := restoreScratch_localRun caller .successLeft
    { scanned with source := z } (reset regs) ctx
  simp only [base, scanned, List.append_nil, reset_reset] at seek start scan check restore
  have joined := LocalRun.trans caller seek (LocalRun.trans caller start
    (LocalRun.trans caller scan (LocalRun.trans caller check restore)))
  convert joined using 1 <;>
    simp [restoreScratchSteps, restoreScratchData, modeResult, markerWord,
      List.append_assoc]; omega

/-- Right-root scanning performs its first marker push before successful restoration starts. -/
theorem root_right_pattern_localRun (A : BinaryTree Unit) (z f : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (2 * (treeCode A).length + 4 + f.length)
      (cfg (some (phaseLabel (.seek .right))) regs
        { source := nodeTag :: nodeTag :: (treeCode A ++ z), saved := f } ctx)
      (cfg (some (resultLabel .success)) (reset regs)
        { source := f.reverse ++ [nodeTag] ++ treeCode A ++ nodeTag :: z } ctx) := by
  let base : LocalData := { saved := f }
  let scanned : LocalData := { source := nodeTag :: z, saved := f, scratch := (treeCode A).reverse }
  have seek := phase_step_localRun caller (
    seek_step_path_nil caller .right
      { base with source := nodeTag :: nodeTag :: (treeCode A ++ z) } regs ctx)
  have start := phase_step_localRun caller (
    start_right_step_nodes caller (treeCode A ++ z) base (reset regs) ctx)
  have scan := scanScratch_treeCode_localRun caller .right A z [] base (reset regs) ctx
  simp only [scratchScanEnd, scratchScanSource, ite_true, reset_reset] at scan
  have restore := restoreScratch_localRun caller .successRight scanned (reset regs) ctx
  simp only [base, scanned, List.append_nil, reset_reset] at seek start scan restore
  have joined := LocalRun.trans caller seek
    (LocalRun.trans caller start (LocalRun.trans caller scan restore))
  convert joined using 1 <;>
    simp [restoreScratchSteps, restoreScratchData, modeResult, markerWord,
      List.append_assoc]; omega

/-- A source whose next pop cannot produce the required node marker. -/
def NoNodeHead : Word → Prop
  | [] => True
  | tag :: _ => tag ≠ nodeTag

/-- Failed first-node probes restore the complete literal input before returning. -/
theorem root_nonnode_localRun (d : RotationDirection) (w f : Word)
    (notNode : NoNodeHead w) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (f.length + 4)
      (cfg (some (phaseLabel (.seek d))) regs { source := w, saved := f } ctx)
      (cfg (some (resultLabel .failure)) (reset regs) { source := f.reverse ++ w } ctx) := by
  let D : LocalData := { source := w, saved := f }
  have seek := phase_step_localRun caller (
    seek_step_path_nil caller d D regs ctx)
  have start : LocalRun caller 1
      (cfg (some (phaseLabel (.start d))) (reset regs) D ctx)
      (cfg (some (phaseLabel .dropPending)) (reset regs) D ctx) := by
    apply LocalRun.single caller
    refine ⟨True.intro, ?_⟩
    cases d with
    | left =>
        cases w with
        | nil => simpa only [D, reset_reset] using start_left_step_nil caller D (reset regs) ctx
        | cons tag raw => simpa only [D, reset_reset] using
            start_left_step_nonnode caller tag raw D (reset regs) ctx notNode
    | right =>
        cases w with
        | nil => simpa only [D, reset_reset] using start_right_step_first_nil caller D (reset regs) ctx
        | cons tag raw => simpa only [D, reset_reset] using
            start_right_step_first_nonnode caller tag raw D (reset regs) ctx notNode
  have cleanup := dropPending_localRun caller D (reset regs) ctx
  have joined := LocalRun.trans caller seek (LocalRun.trans caller start cleanup)
  convert joined using 1 <;> simp [D, dropPendingData]; omega

/-- A right-root failure after its second pop restores both popped observations. -/
theorem root_right_second_nonnode_localRun (w f : Word) (notNode : NoNodeHead w)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (f.length + 4)
      (cfg (some (phaseLabel (.seek .right))) regs
        { source := nodeTag :: w, saved := f } ctx)
      (cfg (some (resultLabel .failure)) (reset regs)
        { source := f.reverse ++ nodeTag :: w } ctx) := by
  let D : LocalData := { source := nodeTag :: w, saved := f }
  have seek := phase_step_localRun caller (
    seek_step_path_nil caller .right D regs ctx)
  have start : LocalRun caller 1
      (cfg (some (phaseLabel (.start .right))) (reset regs) D ctx)
      (cfg (some (phaseLabel .dropPending)) (reset regs) D ctx) := by
    apply LocalRun.single caller
    refine ⟨True.intro, ?_⟩
    cases w with
    | nil => simpa only [D, reset_reset] using
        start_right_step_second_nil caller D (reset regs) ctx
    | cons tag raw => simpa only [D, reset_reset] using
        start_right_step_second_nonnode caller tag raw D (reset regs) ctx notNode
  have cleanup := dropPending_localRun caller D (reset regs) ctx
  have joined := LocalRun.trans caller seek (LocalRun.trans caller start cleanup)
  convert joined using 1 <;> simp [D, dropPendingData]; omega

/-- A left-root scan may finish normally and then fail its required following-node check. -/
theorem root_left_after_nonnode_localRun (A : BinaryTree Unit) (w f : Word)
    (notNode : NoNodeHead w) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (2 * (treeCode A).length + 6 + f.length)
      (cfg (some (phaseLabel (.seek .left))) regs
        { source := nodeTag :: (treeCode A ++ w), saved := f } ctx)
      (cfg (some (resultLabel .failure)) (reset regs)
        { source := f.reverse ++ nodeTag :: (treeCode A ++ w) } ctx) := by
  let base : LocalData := { saved := f }
  let scanned : LocalData := { source := w, saved := f, scratch := (treeCode A).reverse }
  have seek := phase_step_localRun caller (
    seek_step_path_nil caller .left
      { base with source := nodeTag :: (treeCode A ++ w) } regs ctx)
  have start := phase_step_localRun caller (
    start_left_step_node caller (treeCode A ++ w) base (reset regs) ctx)
  have scan := scanScratch_treeCode_localRun caller .left A w [] base (reset regs) ctx
  simp only [scratchScanEnd, scratchScanSource, ite_true, reset_reset] at scan
  have check : LocalRun caller 1
      (cfg (some (phaseLabel .checkRight)) (reset regs) scanned ctx)
      (cfg (some (phaseLabel (.restoreScratch .failureLeft))) (reset regs) scanned ctx) := by
    apply LocalRun.single caller
    refine ⟨True.intro, ?_⟩
    cases w with
    | nil => simpa only [scanned, reset_reset] using checkRight_step_nil caller scanned (reset regs) ctx
    | cons tag raw => simpa only [scanned, reset_reset] using
        checkRight_step_nonnode caller tag raw scanned (reset regs) ctx notNode
  have cleanup := restoreScratch_localRun caller .failureLeft scanned (reset regs) ctx
  simp only [base, scanned, List.append_nil, reset_reset] at seek start scan check cleanup
  have joined := LocalRun.trans caller seek (LocalRun.trans caller start
    (LocalRun.trans caller scan (LocalRun.trans caller check cleanup)))
  convert joined using 1 <;>
    simp [restoreScratchSteps, restoreScratchData, modeResult, markerWord,
      List.append_assoc]; omega

/-- Open one-slot scans that meet EOF or a foreign tag restore their complete raw root. -/
theorem root_blocked_localRun (d : RotationDirection) {accepted raw : Word} {p : Nat}
    (opened : TreeParserMachine.OpenPrefix accepted p) (blocked : TreeParserMachine.Blocked raw)
    (f : Word) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (2 * accepted.length + p + f.length + 6)
      (cfg (some (phaseLabel (.seek d))) regs
        { source := markerWord (scratchFailure d) ++ accepted ++ raw, saved := f } ctx)
      (cfg (some (resultLabel .failure)) (reset regs)
        { source := f.reverse ++ markerWord (scratchFailure d) ++ accepted ++ raw } ctx) := by
  let base : LocalData := { saved := f }
  have scan := scanScratch_blocked_localRun caller (continues_of_openPrefix opened) blocked
    d base (reset regs) ctx
  have seek := phase_step_localRun caller (
    seek_step_path_nil caller d
      { base with source := markerWord (scratchFailure d) ++ accepted ++ raw } regs ctx)
  have start : LocalRun caller 1
      (cfg (some (phaseLabel (.start d))) (reset regs)
        { base with source := markerWord (scratchFailure d) ++ accepted ++ raw } ctx)
      (cfg (some (phaseLabel (.scanScratch d))) (reset regs)
        { base with source := accepted ++ raw, pending := [()] } ctx) := by
    apply LocalRun.single caller
    refine ⟨True.intro, ?_⟩
    cases d with
    | left => simpa [base, scratchFailure, markerWord] using
        start_left_step_node caller (accepted ++ raw) base (reset regs) ctx
    | right => simpa [base, scratchFailure, markerWord] using
        start_right_step_nodes caller (accepted ++ raw) base (reset regs) ctx
  simp only [base, List.length_nil, reset_reset, List.replicate_one] at scan
  have joined := LocalRun.trans caller seek (LocalRun.trans caller start scan)
  convert joined using 1 <;> simp; omega

/-- The source observation chooses the first owned return label. -/
def sourceResult (value : Option (BinaryTree Unit)) : Result :=
  if value.isSome then .success else .failure

/-- The strengthened represented theorem retains arbitrary old saved data and literal suffix. -/
theorem run_code_localRun (d : RotationDirection) (p : List Branch) (s : BinaryTree Unit)
    (f z : Word) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (representedClock d p s + f.length)
      (cfg (some (phaseLabel (.seek d))) regs
        { source := treeCode s ++ z, saved := f, path := p } ctx)
      (cfg (some (resultLabel (sourceResult (applyMoveRun ⟨d, p⟩ s).1))) (reset regs)
        { source := f.reverse ++ treeCode ((applyMoveRun ⟨d, p⟩ s).1.getD s) ++ z,
          path := remainingPath p s } ctx) := by
  induction p generalizing s f z regs with
  | nil =>
      cases s with
      | nil =>
          have run := root_nonnode_localRun caller d (emptyTag :: z) f (by change emptyTag ≠ nodeTag; decide) regs ctx
          simpa [representedClock, remainingPath, sourceResult, source_root, rotateRun, treeCode,
            Nat.add_comm] using run
      | node a l r =>
          cases a
          cases d with
          | left =>
              cases r with
              | nil =>
                  have run := root_left_after_nonnode_localRun caller l (emptyTag :: z) f
                    (by change emptyTag ≠ nodeTag; decide) regs ctx
                  simpa [representedClock, remainingPath, sourceResult, source_root, rotateRun,
                    treeCode, List.append_assoc] using run
              | node b B C =>
                  cases b
                  have run := root_left_pattern_localRun caller l (treeCode B ++ treeCode C ++ z)
                    f regs ctx
                  simpa [representedClock, remainingPath, sourceResult, source_root, rotateRun,
                    treeCode, List.append_assoc] using run
          | right =>
              cases l with
              | nil =>
                  have run := root_right_second_nonnode_localRun caller (emptyTag :: (treeCode r ++ z))
                    f (by change emptyTag ≠ nodeTag; decide) regs ctx
                  simpa [representedClock, remainingPath, sourceResult, source_root, rotateRun,
                    treeCode, List.append_assoc, Nat.add_comm] using run
              | node a A B =>
                  cases a
                  have run := root_right_pattern_localRun caller A (treeCode B ++ treeCode r ++ z)
                    f regs ctx
                  simpa [representedClock, remainingPath, sourceResult, source_root, rotateRun,
                    treeCode, List.append_assoc] using run
  | cons b p ih =>
      cases s with
      | nil =>
          let D : LocalData := { source := emptyTag :: z, saved := f, path := p }
          have head := phase_step_localRun caller (
            seek_step_source_nonnode caller d b p emptyTag z D regs ctx (by decide))
          have cleanup := dropPending_localRun caller D (reset regs) ctx
          have joined := LocalRun.trans caller head cleanup
          convert joined using 1 <;>
            simp [D, representedClock, remainingPath, sourceResult, source_nil_cons,
              treeCode, dropPendingData]; omega
      | node a l r =>
          cases a
          cases b with
          | left =>
              let D : LocalData := { saved := f }
              have head := phase_step_localRun caller (
                seek_step_node_left caller d (treeCode l ++ (treeCode r ++ z)) p D regs ctx)
              have tail := ih l (nodeTag :: f) (treeCode r ++ z) (reset regs)
              have joined := LocalRun.trans caller head tail
              cases actual : (applyMoveRun ⟨d, p⟩ l).1 <;> convert joined using 1 <;>
                simp [D, representedClock, remainingPath, sourceResult, source_left, actual,
                  treeCode, List.reverse_cons, List.append_assoc] <;> omega
          | right =>
              let D : LocalData := { saved := f }
              let scanned : LocalData := { saved := nodeTag :: f, path := p }
              have head := phase_step_localRun caller (
                seek_step_node_right caller d (treeCode l ++ (treeCode r ++ z)) p D regs ctx)
              have scan := scanPrefix_treeCode_localRun caller d l (treeCode r ++ z) [] scanned
                (reset regs) ctx
              simp only [prefixScanEnd, ite_true, reset_reset] at scan
              have tail := ih r ((treeCode l).reverse ++ nodeTag :: f) z (reset regs)
              have joined := LocalRun.trans caller head (LocalRun.trans caller scan tail)
              cases actual : (applyMoveRun ⟨d, p⟩ r).1 <;> convert joined using 1 <;>
                simp [D, representedClock, remainingPath, sourceResult, source_right,
                  actual, treeCode, List.reverse_cons, List.reverse_append, List.append_assoc] <;> omega

/-- An owned segment to a live result determines the evaluator's exact count and endpoint. -/
theorem LocalRun.phaseEndpoint {q : Phase} {D E : LocalData} {regs outRegs : Registers R}
    {ctx outCtx : ∀ k, List (Γ k)} {n : Nat} {r : Result}
    (run : LocalRun caller n (cfg (some (phaseLabel q)) regs D ctx)
      (cfg (some (resultLabel r)) outRegs E outCtx)) :
    phaseSteps q D = n ∧
      phaseResult (Λ := Λ) q regs D ctx = cfg (some (resultLabel r)) outRegs E outCtx := by
  have count := LocalRun.remaining caller run
  change phaseSteps q D = n + 0 at count
  rw [Nat.add_zero] at count
  refine ⟨count, ?_⟩
  have canonical := phase_iterate caller q D regs ctx
  rw [count] at canonical
  exact Option.some.inj (canonical.symm.trans (LocalRun.iterate caller run))

/-- The represented result is the complete first endpoint chosen by the finite evaluator. -/
theorem phaseResult_code (caller : External Λ → Statement Γ Λ R) (d : RotationDirection) (p : List Branch) (s : BinaryTree Unit)
    (f z : Word) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    phaseSteps (.seek d) { source := treeCode s ++ z, saved := f, path := p } =
        representedClock d p s + f.length ∧
      phaseResult (Λ := Λ) (.seek d) regs { source := treeCode s ++ z, saved := f, path := p } ctx =
        cfg (some (resultLabel (sourceResult (applyMoveRun ⟨d, p⟩ s).1))) (reset regs)
          { source := f.reverse ++ treeCode ((applyMoveRun ⟨d, p⟩ s).1.getD s) ++ z,
            path := remainingPath p s } ctx :=
  LocalRun.phaseEndpoint caller (run_code_localRun caller d p s f z regs ctx)

/-- Exact ordinary iteration, retaining the old saved word, suffix and actual residual path. -/
theorem run_code (d : RotationDirection) (p : List Branch) (s : BinaryTree Unit)
    (f z : Word) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (next caller)^[representedClock d p s + f.length]
      (some (cfg (some (phaseLabel (.seek d))) regs
        { source := treeCode s ++ z, saved := f, path := p } ctx)) =
      some (cfg (some (resultLabel (sourceResult (applyMoveRun ⟨d, p⟩ s).1))) (reset regs)
        { source := f.reverse ++ treeCode ((applyMoveRun ⟨d, p⟩ s).1.getD s) ++ z,
          path := remainingPath p s } ctx) :=
  LocalRun.iterate caller (run_code_localRun caller d p s f z regs ctx)

/-- A successful source move produces its actual rotated tree and consumes the whole path. -/
theorem run_code_of_some (d : RotationDirection) (p : List Branch) (s t : BinaryTree Unit)
    (returned : (applyMoveRun ⟨d, p⟩ s).1 = some t) (f z : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (next caller)^[representedClock d p s + f.length]
      (some (cfg (some (phaseLabel (.seek d))) regs
        { source := treeCode s ++ z, saved := f, path := p } ctx)) =
      some (cfg (some (resultLabel .success)) (reset regs)
        { source := f.reverse ++ treeCode t ++ z } ctx) := by
  simpa only [returned, sourceResult, Option.isSome_some, ite_true, Option.getD_some,
    remainingPath_nil_of_source_success d p s t returned] using
    run_code caller d p s f z regs ctx

/-- Failed source moves restore the original tree while retaining the physically unvisited path tail. -/
theorem run_code_of_none (d : RotationDirection) (p : List Branch) (s : BinaryTree Unit)
    (failed : (applyMoveRun ⟨d, p⟩ s).1 = none) (f z : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (next caller)^[representedClock d p s + f.length]
      (some (cfg (some (phaseLabel (.seek d))) regs
        { source := treeCode s ++ z, saved := f, path := p } ctx)) =
      some (cfg (some (resultLabel .failure)) (reset regs)
        { source := f.reverse ++ treeCode s ++ z, path := remainingPath p s } ctx) := by
  simpa only [failed, sourceResult, Option.isSome_none, Bool.false_eq_true, ite_false,
    Option.getD_none] using run_code caller d p s f z regs ctx

/-- Source success is equivalent to the first live result, before arbitrary caller code runs. -/
theorem represented_first_success_iff (caller : External Λ → Statement Γ Λ R) (d : RotationDirection) (p : List Branch)
    (s : BinaryTree Unit) (f z : Word) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (phaseResult (Λ := Λ) (.seek d) regs { source := treeCode s ++ z, saved := f, path := p } ctx).l =
        some (resultLabel .success) ↔ ∃ t, (applyMoveRun ⟨d, p⟩ s).1 = some t := by
  rw [(phaseResult_code caller d p s f z regs ctx).2]
  cases actual : (applyMoveRun ⟨d, p⟩ s).1 <;>
    simp [sourceResult, cfg, resultLabel]

/-- A Type-valued timed witness with its actual exact represented count and complete endpoint. -/
def representedInTime (d : RotationDirection) (p : List Branch) (s : BinaryTree Unit)
    (f z : Word) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller)
      (cfg (some (phaseLabel (.seek d))) regs
        { source := treeCode s ++ z, saved := f, path := p } ctx)
      (some (cfg (some (resultLabel (sourceResult (applyMoveRun ⟨d, p⟩ s).1))) (reset regs)
        { source := f.reverse ++ treeCode ((applyMoveRun ⟨d, p⟩ s).1.getD s) ++ z,
          path := remainingPath p s } ctx))
      (representedClock d p s + f.length) where
  steps := representedClock d p s + f.length
  evals_in_steps := run_code caller d p s f z regs ctx
  steps_le_m := Nat.le_refl _

/-- A constructed failure segment excludes success at the canonical first live return. -/
theorem LocalRun.not_phaseSuccess {q : Phase} {D E : LocalData} {regs outRegs : Registers R}
    {ctx outCtx : ∀ k, List (Γ k)} {n : Nat}
    (run : LocalRun caller n (cfg (some (phaseLabel q)) regs D ctx)
      (cfg (some (resultLabel .failure)) outRegs E outCtx)) :
    (phaseResult (Λ := Λ) q regs D ctx).l ≠ some (resultLabel .success) := by
  rw [(LocalRun.phaseEndpoint caller run).2]
  intro impossible
  cases impossible

/-- Literal left-root recognition; the suffix is arbitrary and need not be tree syntax. -/
theorem root_left_phaseResult_success_iff (caller : External Λ → Statement Γ Λ R) (w f : Word) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    (phaseResult (Λ := Λ) (.seek .left) regs { source := w, saved := f } ctx).l =
        some (resultLabel .success) ↔
      ∃ A : BinaryTree Unit, ∃ z : Word, w = nodeTag :: (treeCode A ++ nodeTag :: z) := by
  constructor
  · intro success
    cases w with
    | nil =>
        have blocked := LocalRun.not_phaseSuccess caller
          (root_nonnode_localRun caller .left [] f True.intro regs ctx)
        exact (blocked success).elim
    | cons tag raw =>
        by_cases node : tag = nodeTag
        · subst tag
          cases parsed : (parseTreeRun raw).1 with
          | none =>
              obtain ⟨accepted, rest, p, word, opened, stopped⟩ :=
                (TreeParserMachine.parseTreeRun_none_iff_openPrefix raw).mp parsed
              have blocked := LocalRun.not_phaseSuccess caller
                (root_blocked_localRun caller .left opened stopped f regs ctx)
              apply False.elim (blocked ?_)
              simpa [scratchFailure, markerWord, word, List.append_assoc] using success
          | some result =>
              rcases result with ⟨A, rest⟩
              have word := (parseTreeRun_iff raw A rest).mp parsed
              cases rest with
              | nil =>
                  have blocked := LocalRun.not_phaseSuccess caller
                    (root_left_after_nonnode_localRun caller A [] f True.intro regs ctx)
                  apply False.elim (blocked ?_)
                  simpa only [word] using success
              | cons required z =>
                  by_cases node : required = nodeTag
                  · exact ⟨A, z, by simp only [word, node]⟩
                  · have blocked := LocalRun.not_phaseSuccess caller
                      (root_left_after_nonnode_localRun caller A (required :: z) f node regs ctx)
                    apply False.elim (blocked ?_)
                    simpa only [word] using success
        · have blocked := LocalRun.not_phaseSuccess caller
            (root_nonnode_localRun caller .left (tag :: raw) f node regs ctx)
          exact (blocked success).elim
  · rintro ⟨A, z, rfl⟩
    rw [(LocalRun.phaseEndpoint caller (root_left_pattern_localRun caller A z f regs ctx)).2]
    rfl

/-- Literal right-root recognition includes the scanner's final in-block marker insertion. -/
theorem root_right_phaseResult_success_iff (caller : External Λ → Statement Γ Λ R) (w f : Word) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    (phaseResult (Λ := Λ) (.seek .right) regs { source := w, saved := f } ctx).l =
        some (resultLabel .success) ↔
      ∃ A : BinaryTree Unit, ∃ z : Word, w = nodeTag :: nodeTag :: (treeCode A ++ z) := by
  constructor
  · intro success
    cases w with
    | nil =>
        have blocked := LocalRun.not_phaseSuccess caller
          (root_nonnode_localRun caller .right [] f True.intro regs ctx)
        exact (blocked success).elim
    | cons first raw =>
        by_cases node : first = nodeTag
        · subst first
          cases raw with
          | nil =>
              have blocked := LocalRun.not_phaseSuccess caller
                (root_right_second_nonnode_localRun caller [] f True.intro regs ctx)
              exact (blocked success).elim
          | cons second raw =>
              by_cases node : second = nodeTag
              · subst second
                cases parsed : (parseTreeRun raw).1 with
                | none =>
                    obtain ⟨accepted, rest, p, word, opened, stopped⟩ :=
                      (TreeParserMachine.parseTreeRun_none_iff_openPrefix raw).mp parsed
                    have blocked := LocalRun.not_phaseSuccess caller
                      (root_blocked_localRun caller .right opened stopped f regs ctx)
                    apply False.elim (blocked ?_)
                    simpa [scratchFailure, markerWord, word, List.append_assoc] using success
                | some result =>
                    rcases result with ⟨A, z⟩
                    exact ⟨A, z, by rw [(parseTreeRun_iff raw A z).mp parsed]⟩
              · have blocked := LocalRun.not_phaseSuccess caller
                  (root_right_second_nonnode_localRun caller (second :: raw) f node regs ctx)
                exact (blocked success).elim
        · have blocked := LocalRun.not_phaseSuccess caller
            (root_nonnode_localRun caller .right (first :: raw) f node regs ctx)
          exact (blocked success).elim
  · rintro ⟨A, z, rfl⟩
    rw [(LocalRun.phaseEndpoint caller (root_right_pattern_localRun caller A z f regs ctx)).2]
    rfl

/-- All strict earlier steps are owned: LocalRun cannot continue through an external caller. -/
theorem firstSuccess_iff_phaseResult (q : Phase) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (∃ n reached, LocalRun caller n (cfg (some (phaseLabel q)) regs D ctx) reached ∧
      reached.l = some (resultLabel .success)) ↔
        (phaseResult (Λ := Λ) q regs D ctx).l = some (resultLabel .success) := by
  constructor
  · rintro ⟨n, reached, run, label⟩
    have count := LocalRun.remaining caller run
    have terminal : remainingSteps reached = 0 := by
      simp only [remainingSteps, label, resultLabel]
    change phaseSteps q D = n + remainingSteps reached at count
    rw [terminal, Nat.add_zero] at count
    have canonical := phase_iterate caller q D regs ctx
    rw [count] at canonical
    have same := Option.some.inj (canonical.symm.trans (LocalRun.iterate caller run))
    rw [same]
    exact label
  · intro label
    exact ⟨phaseSteps q D, phaseResult (Λ := Λ) q regs D ctx, phase_localRun caller q D regs ctx, label⟩

/-- Exact left raw-root success iff, expressed through actual owned transitions. -/
theorem root_left_first_success_iff (w f : Word) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    (∃ n reached, LocalRun caller n
      (cfg (some (phaseLabel (.seek .left))) regs { source := w, saved := f } ctx) reached ∧
        reached.l = some (resultLabel .success)) ↔
      ∃ A : BinaryTree Unit, ∃ z : Word, w = nodeTag :: (treeCode A ++ nodeTag :: z) := by
  rw [firstSuccess_iff_phaseResult caller, root_left_phaseResult_success_iff caller]

/-- Exact right raw-root success iff; no whole-input parser premise is imposed. -/
theorem root_right_first_success_iff (w f : Word) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    (∃ n reached, LocalRun caller n
      (cfg (some (phaseLabel (.seek .right))) regs { source := w, saved := f } ctx) reached ∧
        reached.l = some (resultLabel .success)) ↔
      ∃ A : BinaryTree Unit, ∃ z : Word, w = nodeTag :: nodeTag :: (treeCode A ++ z) := by
  rw [firstSuccess_iff_phaseResult caller, root_right_phaseResult_success_iff caller]

/-- Actual successful navigation frames, ordered from the focused subtree outwards. -/
def navigationFrames : List Branch → BinaryTree Unit → List PositionFrame
  | [], _ => []
  | _ :: _, .nil => []
  | .left :: p, .node _ l r => navigationFrames p l ++ [.cameLeft r]
  | .right :: p, .node _ l r => navigationFrames p r ++ [.cameRight l]

omit [DecidableEq K] in
theorem plugFrames_append (inner outer : List PositionFrame) (focus : BinaryTree Unit) :
    plugFrames (inner ++ outer) focus = plugFrames outer (plugFrames inner focus) := by
  induction inner generalizing focus with
  | nil => rfl
  | cons frame inner ih => cases frame <;> exact ih _

omit [DecidableEq K] in
theorem contextPrefix_append (inner outer : List PositionFrame) :
    contextPrefix (inner ++ outer) = contextPrefix outer ++ contextPrefix inner := by
  induction inner with
  | nil => simp only [List.nil_append, contextPrefix, List.append_nil]
  | cons frame inner ih => cases frame <;>
      simp only [List.cons_append, contextPrefix, ih, List.append_assoc]

omit [DecidableEq K] in
theorem contextSuffix_append (inner outer : List PositionFrame) :
    contextSuffix (inner ++ outer) = contextSuffix inner ++ contextSuffix outer := by
  induction inner with
  | nil => rfl
  | cons frame inner ih => cases frame <;>
      simp only [List.cons_append, contextSuffix, ih, List.append_assoc]

omit [DecidableEq K] in
theorem navigationFrames_plug (p : List Branch) (s : BinaryTree Unit) :
    plugFrames (navigationFrames p s) (stoppedTree p s) = s := by
  induction p generalizing s with
  | nil => rfl
  | cons b p ih =>
      cases s with
      | nil => rfl
      | node a l r =>
          cases a
          cases b with
          | left => simp only [navigationFrames, stoppedTree, plugFrames_append, ih, plugFrames]
          | right => simp only [navigationFrames, stoppedTree, plugFrames_append, ih, plugFrames]

omit [DecidableEq K] in
theorem treeCode_cursor (p : List Branch) (s : BinaryTree Unit) :
    treeCode s = contextPrefix (navigationFrames p s) ++ treeCode (stoppedTree p s) ++
      contextSuffix (navigationFrames p s) := by
  have encoded := treeCode_plugFrames (navigationFrames p s) (stoppedTree p s)
  rw [navigationFrames_plug] at encoded
  exact encoded

omit [DecidableEq K] in
theorem navigationLength_eq_prefix (p : List Branch) (s : BinaryTree Unit) :
    navigationLength p s = (contextPrefix (navigationFrames p s)).length := by
  induction p generalizing s with
  | nil => rfl
  | cons b p ih =>
      cases s with
      | nil => rfl
      | node a l r =>
          cases b with
          | left => simp only [navigationLength, navigationFrames, contextPrefix_append,
              contextPrefix, List.nil_append, List.length_append, List.length_singleton, ih]
          | right => simp only [navigationLength, navigationFrames, contextPrefix_append,
              contextPrefix, List.nil_append, List.length_append, List.length_singleton, ih]

omit [DecidableEq K] in
@[simp] theorem afterScanRegisters_reset (accepted : Word) (regs : Registers R) :
    afterScanRegisters accepted (reset regs) = reset regs := by
  cases accepted <;> rfl

/-- The physical cursor before the final observation has moved exactly the context prefix. -/
theorem seek_cursor_localRun (d : RotationDirection) (p : List Branch) (s : BinaryTree Unit)
    (f z : Word) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (navigationLength p s)
      (cfg (some (phaseLabel (.seek d))) regs
        { source := treeCode s ++ z, saved := f, path := p } ctx)
      (cfg (some (phaseLabel (.seek d)))
        (afterScanRegisters (contextPrefix (navigationFrames p s)) regs)
        { source := treeCode (stoppedTree p s) ++ contextSuffix (navigationFrames p s) ++ z,
          saved := (contextPrefix (navigationFrames p s)).reverse ++ f,
          path := stoppedPath p s } ctx) := by
  induction p generalizing s f z regs with
  | nil =>
      simpa only [navigationLength, navigationFrames, stoppedTree, stoppedPath,
        contextPrefix, contextSuffix, afterScanRegisters, ite_true, List.reverse_nil,
        List.nil_append, List.append_nil] using
        LocalRun.refl (caller := caller)
          (cfg (some (phaseLabel (.seek d))) regs { source := treeCode s ++ z, saved := f } ctx)
  | cons b p ih =>
      cases s with
      | nil =>
          simpa only [navigationLength, navigationFrames, stoppedTree, stoppedPath,
            contextPrefix, contextSuffix, afterScanRegisters, ite_true, List.reverse_nil,
            List.nil_append, List.append_nil] using
            LocalRun.refl (caller := caller)
              (cfg (some (phaseLabel (.seek d))) regs
                { source := treeCode .nil ++ z, saved := f, path := b :: p } ctx)
      | node a l r =>
          cases a
          cases b with
          | left =>
              let D : LocalData := { saved := f }
              have head := phase_step_localRun caller
                (seek_step_node_left caller d (treeCode l ++ (treeCode r ++ z)) p D regs ctx)
              have tail := ih l (nodeTag :: f) (treeCode r ++ z) (reset regs)
              simp only [afterScanRegisters_reset] at tail
              have joined := LocalRun.trans caller head tail
              simpa only [D, navigationLength, navigationFrames, stoppedTree, stoppedPath,
                treeCode, contextPrefix_append, contextSuffix_append, contextPrefix, contextSuffix,
                List.append_assoc, List.cons_append, List.nil_append, List.append_nil,
                List.reverse_cons, List.reverse_append, List.reverse_nil,
                afterScanRegisters, List.cons_ne_nil, ite_false] using joined
          | right =>
              let D : LocalData := { saved := f }
              let scanned : LocalData := { saved := nodeTag :: f, path := p }
              have head := phase_step_localRun caller
                (seek_step_node_right caller d (treeCode l ++ (treeCode r ++ z)) p D regs ctx)
              have scan := scanPrefix_treeCode_localRun caller d l (treeCode r ++ z) [] scanned
                (reset regs) ctx
              simp only [prefixScanEnd, ite_true, reset_reset] at scan
              have tail := ih r ((treeCode l).reverse ++ nodeTag :: f) z (reset regs)
              simp only [afterScanRegisters_reset] at tail
              have joined := LocalRun.trans caller head (LocalRun.trans caller scan tail)
              simpa only [D, scanned, navigationLength, navigationFrames, stoppedTree, stoppedPath,
                treeCode, contextPrefix_append, contextSuffix_append, contextPrefix, contextSuffix,
                List.append_assoc, List.cons_append, List.nil_append, List.append_nil,
                List.reverse_cons, List.reverse_append, List.reverse_nil, List.reverse_reverse,
                afterScanRegisters, List.cons_ne_nil, ite_false,
                Nat.add_assoc] using joined

/-- Ordinary iteration to the actual cursor retains a failing head until its next activation. -/
theorem seek_cursor_iterate (d : RotationDirection) (p : List Branch) (s : BinaryTree Unit)
    (f z : Word) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (next caller)^[navigationLength p s]
      (some (cfg (some (phaseLabel (.seek d))) regs
        { source := treeCode s ++ z, saved := f, path := p } ctx)) =
      some (cfg (some (phaseLabel (.seek d)))
        (afterScanRegisters (contextPrefix (navigationFrames p s)) regs)
        { source := treeCode (stoppedTree p s) ++ contextSuffix (navigationFrames p s) ++ z,
          saved := (contextPrefix (navigationFrames p s)).reverse ++ f,
          path := stoppedPath p s } ctx) :=
  LocalRun.iterate caller (seek_cursor_localRun caller d p s f z regs ctx)

/-- Ordinary iteration for every continued prefix of the saved-word scan. -/
theorem scanPrefix_continues {accepted : Word} {h k : Nat}
    (continued : Continues accepted h k) (d : RotationDirection) (raw : Word)
    (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (next caller)^[accepted.length]
      (some (cfg (some (phaseLabel (.scanPrefix d))) regs
        { D with source := accepted ++ raw, pending := List.replicate h () } ctx)) =
      some (cfg (some (phaseLabel (.scanPrefix d))) (afterScanRegisters accepted regs)
        { D with
          source := raw,
          saved := accepted.reverse ++ D.saved,
          pending := List.replicate k () } ctx) :=
  LocalRun.iterate caller (scanPrefix_continues_localRun caller continued d raw D regs ctx)

/-- Ordinary iteration for every continued prefix of the scratch scan. -/
theorem scanScratch_continues {accepted : Word} {h k : Nat}
    (continued : Continues accepted h k) (d : RotationDirection) (raw : Word)
    (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (next caller)^[accepted.length]
      (some (cfg (some (phaseLabel (.scanScratch d))) regs
        { D with source := accepted ++ raw, pending := List.replicate h () } ctx)) =
      some (cfg (some (phaseLabel (.scanScratch d))) (afterScanRegisters accepted regs)
        { D with
          source := raw,
          scratch := accepted.reverse ++ D.scratch,
          pending := List.replicate k () } ctx) :=
  LocalRun.iterate caller (scanScratch_continues_localRun caller continued d raw D regs ctx)

/-- A represented prefix scan with its complete ordinary-iteration endpoint. -/
theorem scanPrefix_treeCode (d : RotationDirection) (t : BinaryTree Unit)
    (raw : Word) (outer : List Unit) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    (next caller)^[(treeCode t).length]
      (some (cfg (some (phaseLabel (.scanPrefix d))) regs
        { D with source := treeCode t ++ raw, pending := () :: outer } ctx)) =
      some (cfg (some (phaseLabel (prefixScanEnd d outer))) (reset regs)
        { D with
          source := raw,
          saved := (treeCode t).reverse ++ D.saved,
          pending := outer } ctx) :=
  LocalRun.iterate caller (scanPrefix_treeCode_localRun caller d t raw outer D regs ctx)

/-- A represented scratch scan includes the right mode's final same-activation push. -/
theorem scanScratch_treeCode (d : RotationDirection) (t : BinaryTree Unit)
    (raw : Word) (outer : List Unit) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    (next caller)^[(treeCode t).length]
      (some (cfg (some (phaseLabel (.scanScratch d))) regs
        { D with source := treeCode t ++ raw, pending := () :: outer } ctx)) =
      some (cfg (some (phaseLabel (scratchScanEnd d outer))) (reset regs)
        { D with
          source := scratchScanSource d outer raw,
          scratch := (treeCode t).reverse ++ D.scratch,
          pending := outer } ctx) :=
  LocalRun.iterate caller (scanScratch_treeCode_localRun caller d t raw outer D regs ctx)

/-- Saved-scan blocked cleanup, with its exact paid probes and dirty scratch retained. -/
theorem scanPrefix_blocked {accepted raw : Word} {h k : Nat}
    (continued : Continues accepted h k) (blocked : TreeParserMachine.Blocked raw)
    (d : RotationDirection) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    (next caller)^[2 * accepted.length + k + D.saved.length + 3]
      (some (cfg (some (phaseLabel (.scanPrefix d))) regs
        { D with source := accepted ++ raw, pending := List.replicate h () } ctx)) =
      some (cfg (some (resultLabel .failure)) (reset regs)
        { D with
          source := D.saved.reverse ++ accepted ++ raw,
          saved := [], pending := [] } ctx) :=
  LocalRun.iterate caller (scanPrefix_blocked_localRun caller continued blocked d D regs ctx)

/-- Scratch-scan blocked cleanup restores every old accumulator and required missing marker. -/
theorem scanScratch_blocked {accepted raw : Word} {h k : Nat}
    (continued : Continues accepted h k) (blocked : TreeParserMachine.Blocked raw)
    (d : RotationDirection) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    (next caller)^[2 * accepted.length + k + D.scratch.length + D.saved.length + 4]
      (some (cfg (some (phaseLabel (.scanScratch d))) regs
        { D with source := accepted ++ raw, pending := List.replicate h () } ctx)) =
      some (cfg (some (resultLabel .failure)) (reset regs)
        { source := D.saved.reverse ++ markerWord (scratchFailure d) ++
            D.scratch.reverse ++ accepted ++ raw,
          saved := [], scratch := [], pending := [], path := D.path } ctx) :=
  LocalRun.iterate caller (scanScratch_blocked_localRun caller continued blocked d D regs ctx)

/-- Complete first-success endpoints identify both tree and suffix after cancelling old saved data. -/
theorem phaseResult_code_success_iff (caller : External Λ → Statement Γ Λ R)
    (d : RotationDirection) (p : List Branch) (s t : BinaryTree Unit) (f z outSuffix : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    phaseResult (Λ := Λ) (.seek d) regs { source := treeCode s ++ z, saved := f, path := p } ctx =
        cfg (some (resultLabel .success)) (reset regs)
          { source := f.reverse ++ treeCode t ++ outSuffix } ctx ↔
      (applyMoveRun ⟨d, p⟩ s).1 = some t ∧ z = outSuffix := by
  constructor
  · intro endpoint
    have canonical := (phaseResult_code caller d p s f z regs ctx).2
    have same := canonical.symm.trans endpoint
    have label := congrArg (fun c : Cfg Γ Λ R => c.l) same
    cases actual : (applyMoveRun ⟨d, p⟩ s).1 with
    | none => simp [actual, sourceResult, cfg, resultLabel] at label
    | some u =>
        have source := congrArg (fun c : Cfg Γ Λ R => (dataOfCfg c).source) same
        have prefixed : f.reverse ++ (treeCode u ++ z) =
            f.reverse ++ (treeCode t ++ outSuffix) := by
          simpa only [dataOfCfg_cfg, actual, Option.getD_some, List.append_assoc] using source
        have codes : treeCode u ++ z = treeCode t ++ outSuffix :=
          List.append_cancel_left prefixed
        obtain ⟨tree, suffix⟩ := parseTreeRun_prefix_injective u t z outSuffix codes
        exact ⟨congrArg some tree, suffix⟩
  · rintro ⟨returned, rfl⟩
    simpa only [returned, sourceResult, Option.isSome_some, ite_true, Option.getD_some,
      remainingPath_nil_of_source_success d p s t returned] using
      (phaseResult_code caller d p s f z regs ctx).2

/-- An actual owned successful segment fixes the source result, raw suffix and exact duration. -/
theorem run_code_success_iff (d : RotationDirection) (p : List Branch) (s t : BinaryTree Unit)
    (f z outSuffix : Word) (regs : Registers R) (ctx : ∀ k, List (Γ k)) (n : Nat) :
    LocalRun caller n
      (cfg (some (phaseLabel (.seek d))) regs
        { source := treeCode s ++ z, saved := f, path := p } ctx)
      (cfg (some (resultLabel .success)) (reset regs)
        { source := f.reverse ++ treeCode t ++ outSuffix } ctx) ↔
      (applyMoveRun ⟨d, p⟩ s).1 = some t ∧ z = outSuffix ∧
        n = representedClock d p s + f.length := by
  constructor
  · intro run
    have endpoint := LocalRun.phaseEndpoint caller run
    have decoded := (phaseResult_code_success_iff caller d p s t f z outSuffix regs ctx).mp endpoint.2
    exact ⟨decoded.1, decoded.2,
      endpoint.1.symm.trans (phaseResult_code caller d p s f z regs ctx).1⟩
  · rintro ⟨returned, rfl, rfl⟩
    simpa only [returned, sourceResult, Option.isSome_some, ite_true, Option.getD_some,
      remainingPath_nil_of_source_success d p s t returned] using
      run_code_localRun caller d p s f z regs ctx

/-- The actual source semantics, node preservation and tariff follow from the complete first endpoint. -/
theorem represented_success_semantics (caller : External Λ → Statement Γ Λ R)
    (d : RotationDirection) (p : List Branch) (s t : BinaryTree Unit) (f z : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (endpoint : phaseResult (Λ := Λ) (.seek d) regs
      { source := treeCode s ++ z, saved := f, path := p } ctx =
        cfg (some (resultLabel .success)) (reset regs)
          { source := f.reverse ++ treeCode t ++ z } ctx) :
    Trees.Rotations.applyMove? ⟨d, p⟩ s = some t ∧
      t.numNodes = s.numNodes ∧
      (applyMoveRun ⟨d, p⟩ s).2 = 3 * p.length + 5 ∧
      (f.reverse ++ treeCode t ++ z).length = f.length + 2 * s.numNodes + 1 + z.length := by
  have returned := ((phaseResult_code_success_iff caller d p s t f z z regs ctx).mp endpoint).1
  have nodes := applyMoveRun_numNodes ⟨d, p⟩ s t returned
  refine ⟨(applyMoveRun_value ⟨d, p⟩ s).symm.trans returned, nodes,
    applyMoveRun_cost_of_some ⟨d, p⟩ s t returned, ?_⟩
  simp only [List.length_append, List.length_reverse, treeCode_length, nodes, Nat.add_assoc]

/-- Failure restoration and successful rotation have the same represented output length. -/
theorem represented_output_length (caller : External Λ → Statement Γ Λ R)
    (d : RotationDirection) (p : List Branch) (s : BinaryTree Unit) (f z : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (dataOfCfg (phaseResult (Λ := Λ) (.seek d) regs
      { source := treeCode s ++ z, saved := f, path := p } ctx)).source.length =
        f.length + 2 * s.numNodes + 1 + z.length := by
  rw [(phaseResult_code caller d p s f z regs ctx).2]
  change (f.reverse ++ treeCode ((applyMoveRun ⟨d, p⟩ s).1.getD s) ++ z).length = _
  cases actual : (applyMoveRun ⟨d, p⟩ s).1 with
  | none => simp only [Option.getD_none, List.length_append, List.length_reverse,
      treeCode_length, Nat.add_assoc]
  | some t => simp only [Option.getD_some, List.length_append, List.length_reverse,
      treeCode_length, applyMoveRun_numNodes ⟨d, p⟩ s t actual, Nat.add_assoc]

omit [DecidableEq K] in
/-- Success descends through the entire installed position; its source tariff is independently fixed. -/
theorem descentCount_eq_length_of_source_success (d : RotationDirection) (p : List Branch)
    (s t : BinaryTree Unit) (returned : (applyMoveRun ⟨d, p⟩ s).1 = some t) :
    descentCount p s = p.length := by
  have measured := source_cost_eq_stopped d p s
  rw [returned] at measured
  simp only [Option.isSome_some, ite_true] at measured
  have cost := applyMoveRun_cost_of_some ⟨d, p⟩ s t returned
  change (applyMoveRun ⟨d, p⟩ s).2 = 3 * p.length + 5 at cost
  omega


def localTagCells (D : LocalData) : Nat := D.source.length + D.saved.length + D.scratch.length
def localCells (D : LocalData) : Nat :=
  D.source.length + D.saved.length + D.scratch.length + D.pending.length + D.path.length

def phaseDebt : Phase → Nat
  | .scanScratch .left | .checkRight | .restoreScratch .successRight | .restoreScratch .failureLeft => 1
  | .scanScratch .right | .restoreScratch .successLeft | .restoreScratch .failureRight => 2
  | _ => 0

def controlDebt : Control → Nat
  | .inl q => phaseDebt q
  | .inr _ => 0

def phaseCredit : Phase → LocalData → Nat
  | .seek _, D | .scanPrefix _, D | .start _, D | .scanScratch _, D | .checkRight, D => D.source.length
  | _, _ => 0

def controlCredit : Control → LocalData → Nat
  | .inl q, D => phaseCredit q D
  | .inr _, _ => 0

def localPotential (control : Control) (D : LocalData) : Nat :=
  localCells D + controlDebt control + controlCredit control D

theorem advance_mass (q : Phase) (D : LocalData) :
    localTagCells (advance q D).2 + controlDebt (advance q D).1 = localTagCells D + phaseDebt q ∧
      localPotential (advance q D).1 (advance q D).2 ≤ localPotential (.inl q) D := by
  rcases D with ⟨raw, saved, scratch, pending, path⟩
  cases q with
  | seek d =>
      cases path with
      | nil => constructor <;> simp [advance, localTagCells, localPotential, localCells,
          controlDebt, phaseDebt, controlCredit, phaseCredit]
      | cons b path =>
          cases raw with
          | nil => constructor <;> simp [advance, localTagCells, localPotential, localCells,
              controlDebt, phaseDebt, controlCredit, phaseCredit]
          | cons tag raw =>
              by_cases node : tag = nodeTag
              · cases b <;> constructor <;> simp [advance, localTagCells, localPotential, localCells,
                  controlDebt, phaseDebt, controlCredit, phaseCredit, node] <;> omega
              · constructor <;> simp [advance, localTagCells, localPotential, localCells,
                  controlDebt, phaseDebt, controlCredit, phaseCredit, node]; omega
  | scanPrefix d =>
      cases raw with
      | nil => constructor <;> simp [advance, localTagCells, localPotential, localCells,
          controlDebt, phaseDebt, controlCredit, phaseCredit]
      | cons tag raw =>
          by_cases node : tag = nodeTag
          · constructor <;> simp [advance, localTagCells, localPotential, localCells,
              controlDebt, phaseDebt, controlCredit, phaseCredit, node] <;> omega
          · by_cases empty : tag = emptyTag
            · by_cases finished : pending.tail = []
              · constructor <;> simp [advance, localTagCells, localPotential, localCells,
                  controlDebt, phaseDebt, controlCredit, phaseCredit, empty, finished] <;> omega
              · constructor <;> simp [advance, localTagCells, localPotential, localCells,
                  controlDebt, phaseDebt, controlCredit, phaseCredit, empty, finished,
                  List.length_tail] <;> omega
            · constructor <;> simp [advance, localTagCells, localPotential, localCells,
                controlDebt, phaseDebt, controlCredit, phaseCredit, node, empty]
  | start d =>
      cases d with
      | left =>
          cases raw with
          | nil => constructor <;> simp [advance, localTagCells, localPotential, localCells,
              controlDebt, phaseDebt, controlCredit, phaseCredit]
          | cons tag raw =>
              by_cases node : tag = nodeTag <;> constructor <;>
                simp [advance, localTagCells, localPotential, localCells,
                  controlDebt, phaseDebt, controlCredit, phaseCredit, node] <;> omega
      | right =>
          cases raw with
          | nil => constructor <;> simp [advance, localTagCells, localPotential, localCells,
              controlDebt, phaseDebt, controlCredit, phaseCredit]
          | cons first raw =>
              cases raw with
              | nil => constructor <;> simp [advance, localTagCells, localPotential, localCells,
                  controlDebt, phaseDebt, controlCredit, phaseCredit]
              | cons second raw =>
                  by_cases nodes : first = nodeTag ∧ second = nodeTag <;> constructor <;>
                    simp [advance, localTagCells, localPotential, localCells,
                      controlDebt, phaseDebt, controlCredit, phaseCredit, nodes] <;> omega
  | scanScratch d =>
      cases raw with
      | nil => cases d <;> constructor <;>
          simp [advance, localTagCells, localPotential, localCells,
            controlDebt, phaseDebt, controlCredit, phaseCredit, scratchFailure]
      | cons tag raw =>
          by_cases node : tag = nodeTag
          · constructor <;> simp [advance, localTagCells, localPotential, localCells,
              controlDebt, phaseDebt, controlCredit, phaseCredit, node] <;> omega
          · by_cases empty : tag = emptyTag
            · by_cases finished : pending.tail = []
              · cases d <;> constructor <;> simp [advance, localTagCells, localPotential, localCells,
                  controlDebt, phaseDebt, controlCredit, phaseCredit, empty, finished] <;> omega
              · constructor <;> simp [advance, localTagCells, localPotential, localCells,
                  controlDebt, phaseDebt, controlCredit, phaseCredit, empty, finished,
                  List.length_tail] <;> omega
            · cases d <;> constructor <;> simp [advance, localTagCells, localPotential, localCells,
                controlDebt, phaseDebt, controlCredit, phaseCredit, node, empty, scratchFailure]
  | checkRight =>
      cases raw with
      | nil => constructor <;> simp [advance, localTagCells, localPotential, localCells,
          controlDebt, phaseDebt, controlCredit, phaseCredit]
      | cons tag raw =>
          by_cases node : tag = nodeTag <;> constructor <;>
            simp [advance, localTagCells, localPotential, localCells,
              controlDebt, phaseDebt, controlCredit, phaseCredit, node] <;> omega
  | restoreScratch mode =>
      cases scratch <;> cases mode <;> constructor <;>
        simp [advance, localTagCells, localPotential, localCells,
          controlDebt, phaseDebt, controlCredit, phaseCredit, markerWord, modeResult] <;> omega
  | dropPending => cases pending <;> constructor <;>
      simp [advance, localTagCells, localPotential, localCells,
        controlDebt, phaseDebt, controlCredit, phaseCredit]
  | restorePrefix r => cases saved <;> constructor <;>
      simp [advance, localTagCells, localPotential, localCells,
        controlDebt, phaseDebt, controlCredit, phaseCredit] <;> omega

def tagCells (c : Cfg Γ Λ R) : Nat := localTagCells (dataOfCfg c)
def ownedCells (c : Cfg Γ Λ R) : Nat := localCells (dataOfCfg c)

def debt : Option (Label Λ) → Nat
  | some (.inl q) => phaseDebt q
  | _ => 0

def credit (c : Cfg Γ Λ R) : Nat :=
  match c.l with
  | some (.inl q) => phaseCredit q (dataOfCfg c)
  | _ => 0

omit [DecidableEq K] in
@[simp] theorem tagCells_cfg (label : Option (Label Λ)) (regs : Registers R)
    (D : LocalData) (ctx : ∀ k, List (Γ k)) : tagCells (cfg label regs D ctx) = localTagCells D := rfl

@[simp] theorem debt_controlLabel (control : Control) :
    debt (some (controlLabel (Λ := Λ) control)) = controlDebt control := by
  cases control <;> rfl

omit [DecidableEq K] in
@[simp] theorem credit_control_cfg (control : Control) (regs : Registers R)
    (D : LocalData) (ctx : ∀ k, List (Γ k)) :
    credit (cfg (some (controlLabel (Λ := Λ) control)) regs D ctx) = controlCredit control D := by
  cases control <;> rfl

theorem local_step_tag_debt {before after : Cfg Γ Λ R}
    (transition : LocalStep caller before after) :
    tagCells after + debt after.l = tagCells before + debt before.l := by
  obtain ⟨q, regs, D, ctx, rfl⟩ := owned_cases before transition.1
  have same := Option.some.inj ((advance_step caller q D regs ctx).symm.trans transition.2)
  subst after
  change localTagCells (advance q D).2 + debt (some (controlLabel (Λ := Λ) (advance q D).1)) =
    localTagCells D + phaseDebt q
  rw [debt_controlLabel]
  exact (advance_mass q D).1

theorem local_reaches_tag_debt {start reached : Cfg Γ Λ R}
    (path : Relation.ReflTransGen (LocalStep caller) start reached) :
    tagCells reached + debt reached.l = tagCells start + debt start.l := by
  induction path with
  | refl => rfl
  | @tail before after _ transition ih => exact (local_step_tag_debt caller transition).trans ih

/-! ## Inclusive prefixes, first return, frame and timed data -/

section PrefixBoundary

theorem step_caller_independent (other : External Λ → Statement Γ Λ R)
    (c : Cfg Γ Λ R) (owned : Owned c.l) : step caller c = step other c := by
  obtain ⟨q, regs, D, ctx, rfl⟩ := owned_cases c owned
  rfl

/-- One actual reached configuration, including the first live handoff. -/
theorem owned_prefix (start : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start) :
    ∃ reached,
      (next caller)^[n] (some start) = some reached ∧
      remainingSteps reached = remainingSteps start - n ∧
      Relation.ReflTransGen (LocalStep caller) start reached ∧
      (n < remainingSteps start ↔ Owned reached.l) := by
  obtain ⟨reached, executed, rank, path⟩ := BinaryCounter.FixedWidthMachine.ranked_prefix
    (step caller) remainingSteps (local_progress caller) n start bound
  refine ⟨reached, executed, rank, ?_, ?_⟩
  · exact Relation.ReflTransGen.mono
      (fun before _ h => ⟨(remainingSteps_pos_iff before).mp h.1, h.2⟩) _ _ path
  · rw [← remainingSteps_pos_iff, rank]
    omega

theorem prefix_caller_independent (other : External Λ → Statement Γ Λ R)
    (start : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start) :
    (next caller)^[n] (some start) = (next other)^[n] (some start) := by
  exact BinaryCounter.FixedWidthMachine.ranked_prefix_eq (step caller) (step other) remainingSteps
    (local_progress caller)
    (fun c positive => step_caller_independent caller other c ((remainingSteps_pos_iff c).mp positive))
    n start bound

theorem ambient_prefix_eq (ambient : Label Λ → Statement Γ Λ R)
    (agrees : ∀ q, ambient (phaseLabel q) = block q)
    (start : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start) :
    (next caller)^[n] (some start) =
      (fun c : Option (Cfg Γ Λ R) => c.bind (Turing.TM2.step ambient))^[n] (some start) := by
  rw [program_eq_of_agrees ambient agrees]
  exact prefix_caller_independent caller (fun external => ambient (.inr external)) start n bound

theorem local_reaches_frame {start reached : Cfg Γ Λ R}
    (path : Relation.ReflTransGen (LocalStep caller) start reached) :
    reached.var.2 = start.var.2 ∧ ∀ k, reached.stk (.inr k) = start.stk (.inr k) := by
  induction path with
  | refl => exact ⟨rfl, fun _ => rfl⟩
  | @tail before after _ transition ih =>
      obtain ⟨_, registers, frame⟩ := local_step_data caller transition
      refine ⟨?_, fun k => (frame k).trans (ih.2 k)⟩
      rw [registers]
      exact ih.1

theorem prefix_frame (start reached : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start)
    (executed : (next caller)^[n] (some start) = some reached) :
    reached.var.2 = start.var.2 ∧ ∀ k, reached.stk (.inr k) = start.stk (.inr k) := by
  obtain ⟨actual, run, _, path, _⟩ := owned_prefix caller start n bound
  have equal : actual = reached := Option.some.inj (run.symm.trans executed)
  subst actual
  exact local_reaches_frame caller path

/-- At zero the entire original register survives; positive owned prefixes reset it. -/
theorem prefix_reset (start reached : Cfg Γ Λ R) (n : Nat)
    (bound : n ≤ remainingSteps start)
    (executed : (next caller)^[n] (some start) = some reached) :
    reached.var = if n = 0 then start.var else reset start.var := by
  induction n generalizing start reached with
  | zero =>
      have equal : start = reached := Option.some.inj executed
      subst reached
      rfl
  | succ n ih =>
      have positive : 0 < remainingSteps start := by omega
      obtain ⟨middle, first, decreased⟩ := local_progress caller start positive
      have owned := (remainingSteps_pos_iff start).mp positive
      have registers := (local_step_data caller ⟨owned, first⟩).2.1
      rw [Function.iterate_succ_apply, next_some, first] at executed
      simp only [Nat.succ_ne_zero, ite_false]
      simpa only [registers, reset_reset, ite_self] using
        ih middle reached (by omega) executed

theorem prefix_reset_of_pos (start reached : Cfg Γ Λ R) (n : Nat)
    (positive : 0 < n) (bound : n ≤ remainingSteps start)
    (executed : (next caller)^[n] (some start) = some reached) :
    reached.var = reset start.var := by
  simpa only [Nat.ne_of_gt positive, ite_false] using prefix_reset caller start reached n bound executed

/-- The reset and protected frame refer to the same inclusive-prefix witness. -/
theorem owned_prefix_frame (start : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start) :
    ∃ reached,
      (next caller)^[n] (some start) = some reached ∧
      remainingSteps reached = remainingSteps start - n ∧
      Relation.ReflTransGen (LocalStep caller) start reached ∧
      (n < remainingSteps start ↔ Owned reached.l) ∧
      (n = 0 → reached = start) ∧
      reached.var = (if n = 0 then start.var else reset start.var) ∧
      ∀ k, reached.stk (.inr k) = start.stk (.inr k) := by
  obtain ⟨reached, executed, rank, path, ownership⟩ := owned_prefix caller start n bound
  refine ⟨reached, executed, rank, path, ownership, ?_,
    prefix_reset caller start reached n bound executed,
    (prefix_frame caller start reached n bound executed).2⟩
  intro zero
  subst n
  exact (Option.some.inj executed).symm

omit [DecidableEq K] in
theorem phaseResult_not_owned (q : Phase) (regs : Registers R) (D : LocalData)
    (ctx : ∀ k, List (Γ k)) : ¬ Owned (phaseResult (Λ := Λ) q regs D ctx).l := by
  simp [phaseResult, cfg, resultLabel, Owned]

/-- An owned entry ends at its specified live result before its caller runs. -/
theorem phase_first_return (q : Phase) (D : LocalData)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (next caller)^[phaseSteps q D]
        (some (cfg (some (phaseLabel q)) regs D ctx)) = some (phaseResult q regs D ctx) ∧
      ¬ Owned (phaseResult (Λ := Λ) q regs D ctx).l ∧
      ∀ n, n < phaseSteps q D → ∃ reached,
        (next caller)^[n] (some (cfg (some (phaseLabel q)) regs D ctx)) = some reached ∧
          Owned reached.l := by
  refine ⟨phase_iterate caller q D regs ctx, phaseResult_not_owned q regs D ctx, ?_⟩
  intro n strict
  have bound : n ≤ remainingSteps (cfg (some (phaseLabel q)) regs D ctx : Cfg Γ Λ R) := by
    change n ≤ phaseSteps q D
    omega
  obtain ⟨reached, executed, _, _, ownership⟩ :=
    owned_prefix caller (cfg (some (phaseLabel q)) regs D ctx) n bound
  exact ⟨reached, executed, ownership.mp strict⟩

theorem first_return_exact (start : Cfg Γ Λ R) (n : Nat) (reached : Cfg Γ Λ R)
    (bound : n ≤ remainingSteps start)
    (executed : (next caller)^[n] (some start) = some reached)
    (external : ¬ Owned reached.l) : n = remainingSteps start := by
  obtain ⟨actual, run, _, _, ownership⟩ := owned_prefix caller start n bound
  have equal : actual = reached := Option.some.inj (run.symm.trans executed)
  subst actual
  by_contra different
  have strict : n < remainingSteps start := by omega
  exact external (ownership.mp strict)

/-- Strict earlier ownership excludes a later caller-created or reentered result. -/
theorem first_return_unique (q : Phase) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (n : Nat) (reached : Cfg Γ Λ R)
    (executed : (next caller)^[n]
      (some (cfg (some (phaseLabel q)) regs D ctx)) = some reached)
    (external : ¬ Owned reached.l)
    (earlier : ∀ k, k < n → ∃ before,
      (next caller)^[k] (some (cfg (some (phaseLabel q)) regs D ctx)) = some before ∧
        Owned before.l) :
    n = phaseSteps q D ∧ reached = phaseResult q regs D ctx := by
  have bound : n ≤ phaseSteps q D := by
    by_contra bad
    have strict : phaseSteps q D < n := by omega
    obtain ⟨before, arrived, owned⟩ := earlier (phaseSteps q D) strict
    have same : before = phaseResult q regs D ctx :=
      Option.some.inj (arrived.symm.trans (phase_iterate caller q D regs ctx))
    rw [same] at owned
    exact phaseResult_not_owned q regs D ctx owned
  have exactCount : n = phaseSteps q D :=
    first_return_exact caller (cfg (some (phaseLabel q)) regs D ctx) n reached bound executed external
  refine ⟨exactCount, ?_⟩
  rw [exactCount] at executed
  exact Option.some.inj (executed.symm.trans (phase_iterate caller q D regs ctx))

def phaseInTime (q : Phase) (D : LocalData) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller)
      (cfg (some (phaseLabel q)) regs D ctx) (some (phaseResult q regs D ctx)) (phaseSteps q D) where
  steps := phaseSteps q D
  evals_in_steps := phase_iterate caller q D regs ctx
  steps_le_m := Nat.le_refl _

def runInTimeExact (d : RotationDirection) (raw : Word) (path : List Branch)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller) (entry d regs raw path ctx)
      (some (phaseResult (.seek d) regs { source := raw, path := path } ctx))
      (runSteps d raw path) where
  steps := runSteps d raw path
  evals_in_steps := phase_iterate caller (.seek d) { source := raw, path := path } regs ctx
  steps_le_m := Nat.le_refl _

def runInLinearTime (d : RotationDirection) (raw : Word) (path : List Branch)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller) (entry d regs raw path ctx)
      (some (phaseResult (.seek d) regs { source := raw, path := path } ctx))
      (3 * raw.length + path.length + 5) where
  steps := runSteps d raw path
  evals_in_steps := phase_iterate caller (.seek d) { source := raw, path := path } regs ctx
  steps_le_m := runSteps_le d raw path

def runInConservativeTime (d : RotationDirection) (raw : Word) (path : List Branch)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller) (entry d regs raw path ctx)
      (some (phaseResult (.seek d) regs { source := raw, path := path } ctx))
      (4 * raw.length + path.length + 12) where
  steps := runSteps d raw path
  evals_in_steps := phase_iterate caller (.seek d) { source := raw, path := path } regs ctx
  steps_le_m := runSteps_le_conservative d raw path

end PrefixBoundary

/-! ## All-raw provenance, cleanup and literal rollback -/

/-- Literal provenance is retained until failure has restored the original word.
Successful rewriting keeps its cleanup conditions and uses tag conservation. -/
def RawOrigin (original : Word) : Control → LocalData → Prop
  | .inl (.seek _), D =>
      D.scratch = [] ∧ D.pending = [] ∧ original = D.saved.reverse ++ D.source
  | .inl (.scanPrefix _), D =>
      D.scratch = [] ∧ original = D.saved.reverse ++ D.source
  | .inl (.start _), D =>
      D.scratch = [] ∧ D.pending = [] ∧ D.path = [] ∧
        original = D.saved.reverse ++ D.source
  | .inl (.scanScratch d), D =>
      D.path = [] ∧ original =
        D.saved.reverse ++ markerWord (scratchFailure d) ++ D.scratch.reverse ++ D.source
  | .inl .checkRight, D =>
      D.pending = [] ∧ D.path = [] ∧ original =
        D.saved.reverse ++ [nodeTag] ++ D.scratch.reverse ++ D.source
  | .inl (.restoreScratch .failureLeft), D =>
      D.path = [] ∧ original =
        D.saved.reverse ++ [nodeTag] ++ D.scratch.reverse ++ D.source
  | .inl (.restoreScratch .failureRight), D =>
      D.path = [] ∧ original =
        D.saved.reverse ++ [nodeTag, nodeTag] ++ D.scratch.reverse ++ D.source
  | .inl (.restoreScratch .successLeft), D
  | .inl (.restoreScratch .successRight), D => D.pending = [] ∧ D.path = []
  | .inl .dropPending, D =>
      D.scratch = [] ∧ original = D.saved.reverse ++ D.source
  | .inl (.restorePrefix .failure), D =>
      D.scratch = [] ∧ D.pending = [] ∧ original = D.saved.reverse ++ D.source
  | .inl (.restorePrefix .success), D =>
      D.scratch = [] ∧ D.pending = [] ∧ D.path = []
  | .inr .failure, D =>
      D.saved = [] ∧ D.scratch = [] ∧ D.pending = [] ∧ D.source = original
  | .inr .success, D =>
      D.saved = [] ∧ D.scratch = [] ∧ D.pending = [] ∧ D.path = []

theorem advance_rawOrigin (original : Word) (q : Phase) (D : LocalData)
    (origin : RawOrigin original (.inl q) D) :
    RawOrigin original (advance q D).1 (advance q D).2 := by
  rcases D with ⟨raw, saved, scratch, pending, path⟩
  cases q
  case' seek d =>
    cases path
    case' cons b path =>
      cases raw
      case' cons tag raw =>
        by_cases node : tag = nodeTag
        case' pos => cases b
  case' scanPrefix d =>
    cases raw
    case' cons tag raw =>
      by_cases node : tag = nodeTag
      case' neg =>
        by_cases empty : tag = emptyTag
        case' pos => by_cases finished : pending.tail = []
  case' start d =>
    cases d
    case' left =>
      cases raw
      case' cons tag raw => by_cases node : tag = nodeTag
    case' right =>
      cases raw
      case' cons first raw =>
        cases raw
        case' cons second raw =>
          by_cases firstNode : first = nodeTag <;> by_cases secondNode : second = nodeTag
  case' scanScratch d =>
    cases d
    case' left =>
      cases raw
      case' cons tag raw =>
        by_cases node : tag = nodeTag
        case' neg =>
          by_cases empty : tag = emptyTag
          case' pos => by_cases finished : pending.tail = []
    case' right =>
      cases raw
      case' cons tag raw =>
        by_cases node : tag = nodeTag
        case' neg =>
          by_cases empty : tag = emptyTag
          case' pos => by_cases finished : pending.tail = []
  case' checkRight =>
    cases raw
    case' cons tag raw => by_cases node : tag = nodeTag
  case' restoreScratch mode => cases mode <;> cases scratch
  case' dropPending => cases pending
  case' restorePrefix r => cases r <;> cases saved
  all_goals simp_all [RawOrigin, advance, markerWord, modeResult, scratchFailure,
    List.reverse_cons, List.append_assoc]

/-- A local activation only removes path heads. This holds in arbitrary dirty data. -/
theorem advance_path_suffix (q : Phase) (D : LocalData) :
    ∃ consumed, D.path = consumed ++ (advance q D).2.path := by
  rcases D with ⟨raw, saved, scratch, pending, path⟩
  cases q with
  | seek d =>
      cases path with
      | nil => exact ⟨[], rfl⟩
      | cons b path =>
          refine ⟨[b], ?_⟩
          cases raw with
          | nil => rfl
          | cons tag raw =>
              by_cases node : tag = nodeTag
              · cases b <;> simp [advance, node]
              · simp [advance, node]
  | scanPrefix d =>
      refine ⟨[], ?_⟩
      cases raw with
      | nil => rfl
      | cons tag raw =>
          by_cases node : tag = nodeTag
          · simp [advance, node]
          · by_cases empty : tag = emptyTag <;> simp [advance, node, empty]
  | start d =>
      refine ⟨[], ?_⟩
      cases d with
      | left =>
          cases raw with
          | nil => rfl
          | cons tag raw => by_cases node : tag = nodeTag <;> simp [advance, node]
      | right =>
          cases raw with
          | nil => rfl
          | cons first raw =>
              cases raw with
              | nil => rfl
              | cons second raw =>
                  by_cases nodes : first = nodeTag ∧ second = nodeTag <;> simp [advance, nodes]
  | scanScratch d =>
      refine ⟨[], ?_⟩
      cases raw with
      | nil => rfl
      | cons tag raw =>
          by_cases node : tag = nodeTag
          · simp [advance, node]
          · by_cases empty : tag = emptyTag
            · by_cases finished : pending.tail = []
              · cases d <;> simp [advance, empty, finished]
              · simp [advance, empty, finished]
            · simp [advance, node, empty]
  | checkRight =>
      refine ⟨[], ?_⟩
      cases raw with
      | nil => rfl
      | cons tag raw => by_cases node : tag = nodeTag <;> simp [advance, node]
  | restoreScratch mode =>
      refine ⟨[], ?_⟩
      cases scratch <;> rfl
  | dropPending =>
      refine ⟨[], ?_⟩
      cases pending <;> rfl
  | restorePrefix r =>
      refine ⟨[], ?_⟩
      cases saved <;> rfl

def RawInvariant (original : Word) (c : Cfg Γ Λ R) : Prop :=
  match c.l with
  | some (.inl q) => RawOrigin original (.inl q) (dataOfCfg c)
  | some (.inr (.inl r)) => RawOrigin original (.inr r) (dataOfCfg c)
  | _ => False

omit [DecidableEq K] in
@[simp] theorem rawInvariant_control_cfg (original : Word) (control : Control)
    (regs : Registers R) (D : LocalData) (ctx : ∀ k, List (Γ k)) :
    RawInvariant original (cfg (some (controlLabel (Λ := Λ) control)) regs D ctx) ↔
      RawOrigin original control D := by
  cases control <;> rfl

theorem local_step_rawInvariant (original : Word) {before after : Cfg Γ Λ R}
    (transition : LocalStep caller before after) (origin : RawInvariant original before) :
    RawInvariant original after := by
  obtain ⟨q, regs, D, ctx, rfl⟩ := owned_cases before transition.1
  have same := Option.some.inj ((advance_step caller q D regs ctx).symm.trans transition.2)
  subst after
  rw [rawInvariant_control_cfg]
  exact advance_rawOrigin original q D origin

theorem local_reaches_rawInvariant (original : Word) {start reached : Cfg Γ Λ R}
    (path : Relation.ReflTransGen (LocalStep caller) start reached)
    (origin : RawInvariant original start) : RawInvariant original reached := by
  induction path with
  | refl => exact origin
  | @tail before after _ transition ih => exact local_step_rawInvariant caller original transition ih

theorem local_step_path_suffix {before after : Cfg Γ Λ R}
    (transition : LocalStep caller before after) :
    ∃ consumed, before.stk (.inl .path) = consumed ++ after.stk (.inl .path) := by
  obtain ⟨q, regs, D, ctx, rfl⟩ := owned_cases before transition.1
  have same := Option.some.inj ((advance_step caller q D regs ctx).symm.trans transition.2)
  subst after
  exact advance_path_suffix q D

theorem local_reaches_path_suffix {start reached : Cfg Γ Λ R}
    (path : Relation.ReflTransGen (LocalStep caller) start reached) :
    ∃ consumed, start.stk (.inl .path) = consumed ++ reached.stk (.inl .path) := by
  induction path with
  | refl => exact ⟨[], rfl⟩
  | @tail before after _ transition ih =>
      obtain ⟨first, hfirst⟩ := ih
      obtain ⟨last, hlast⟩ := local_step_path_suffix caller transition
      exact ⟨first ++ last, by rw [hfirst, hlast, List.append_assoc]⟩

/-- The clean all-raw result has no saved, scratch or pending residue. -/
theorem run_raw_clean (caller : External Λ → Statement Γ Λ R) (d : RotationDirection) (raw : Word) (path : List Branch)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    let finish : Cfg Γ Λ R := phaseResult (Λ := Λ) (.seek d) regs { source := raw, path := path } ctx
    finish.stk (.inl .saved) = [] ∧ finish.stk (.inl .scratch) = [] ∧
      finish.stk (.inl .pending) = [] := by
  have origin := local_reaches_rawInvariant caller raw
    (LocalRun.reaches caller (phase_localRun caller (.seek d)
      { source := raw, path := path } regs ctx))
    (show RawInvariant raw (entry d regs raw path ctx) from ⟨rfl, rfl, rfl⟩)
  change RawOrigin raw (.inr (evaluate (.inl (.seek d))
    { source := raw, path := path }).result)
    (evaluate (.inl (.seek d)) { source := raw, path := path }).data at origin
  cases result : (evaluate (.inl (.seek d)) { source := raw, path := path }).result <;>
    simp only [result, RawOrigin] at origin <;>
    exact ⟨origin.1, origin.2.1, origin.2.2.1⟩

theorem run_raw_failure (caller : External Λ → Statement Γ Λ R) (d : RotationDirection) (raw : Word) (path : List Branch)
    (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (failure : (phaseResult (Λ := Λ) (.seek d) regs { source := raw, path := path } ctx : Cfg Γ Λ R).l =
      some (resultLabel .failure)) :
    (phaseResult (Λ := Λ) (.seek d) regs { source := raw, path := path } ctx : Cfg Γ Λ R).stk (.inl .source) = raw := by
  have origin := local_reaches_rawInvariant caller raw
    (LocalRun.reaches caller (phase_localRun caller (.seek d)
      { source := raw, path := path } regs ctx))
    (show RawInvariant raw (entry d regs raw path ctx) from ⟨rfl, rfl, rfl⟩)
  simp only [RawInvariant, failure, resultLabel, RawOrigin] at origin
  exact origin.2.2.2

theorem run_raw_success (caller : External Λ → Statement Γ Λ R) (d : RotationDirection) (raw : Word) (path : List Branch)
    (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (success : (phaseResult (Λ := Λ) (.seek d) regs { source := raw, path := path } ctx : Cfg Γ Λ R).l =
      some (resultLabel .success)) :
    (phaseResult (Λ := Λ) (.seek d) regs { source := raw, path := path } ctx : Cfg Γ Λ R).stk (.inl .path) = [] := by
  have origin := local_reaches_rawInvariant caller raw
    (LocalRun.reaches caller (phase_localRun caller (.seek d)
      { source := raw, path := path } regs ctx))
    (show RawInvariant raw (entry d regs raw path ctx) from ⟨rfl, rfl, rfl⟩)
  simp only [RawInvariant, success, resultLabel, RawOrigin] at origin
  exact origin.2.2.2

theorem run_raw_path_suffix (caller : External Λ → Statement Γ Λ R) (d : RotationDirection) (raw : Word) (path : List Branch)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ∃ consumed, path = consumed ++
      (phaseResult (Λ := Λ) (.seek d) regs { source := raw, path := path } ctx : Cfg Γ Λ R).stk (.inl .path) :=
  local_reaches_path_suffix caller (LocalRun.reaches caller
    (phase_localRun caller (.seek d) { source := raw, path := path } regs ctx))

theorem run_raw_length (caller : External Λ → Statement Γ Λ R) (d : RotationDirection) (raw : Word) (path : List Branch)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ((phaseResult (Λ := Λ) (.seek d) regs { source := raw, path := path } ctx : Cfg Γ Λ R).stk (.inl .source)).length =
      raw.length := by
  have conserved := local_reaches_tag_debt caller (LocalRun.reaches caller
    (phase_localRun caller (.seek d) { source := raw, path := path } regs ctx))
  have clean := run_raw_clean caller d raw path regs ctx
  change ((phaseResult (Λ := Λ) (.seek d) regs { source := raw, path := path } ctx).stk (.inl .source)).length +
      ((phaseResult (Λ := Λ) (.seek d) regs { source := raw, path := path } ctx).stk (.inl .saved)).length +
      ((phaseResult (Λ := Λ) (.seek d) regs { source := raw, path := path } ctx).stk (.inl .scratch)).length + 0 =
      raw.length + 0 + 0 + 0 at conserved
  simpa only [clean.1, clean.2.1, List.length_nil, Nat.add_zero] using conserved

/-- Actual first-result execution for every raw word and every path. -/
theorem run_raw (d : RotationDirection) (raw : Word) (path : List Branch)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ∃ result output rest,
      LocalRun caller (runSteps d raw path) (entry d regs raw path ctx)
        (cfg (some (resultLabel result)) (reset regs) { source := output, path := rest } ctx) ∧
      output.length = raw.length ∧ (∃ consumed, path = consumed ++ rest) ∧
      (result = .failure → output = raw) ∧ (result = .success → rest = []) := by
  let E := evaluate (.inl (.seek d)) { source := raw, path := path }
  have cleaned := run_raw_clean caller d raw path regs ctx
  change E.data.saved = [] ∧ E.data.scratch = [] ∧ E.data.pending = [] at cleaned
  have data_eq : E.data = { source := E.data.source, path := E.data.path } := by
    cases data : E.data
    simp_all only
  refine ⟨E.result, E.data.source, E.data.path, ?_, run_raw_length caller d raw path regs ctx,
    run_raw_path_suffix caller d raw path regs ctx, ?_, ?_⟩
  · have run := phase_localRun caller (.seek d) { source := raw, path := path } regs ctx
    change LocalRun caller (runSteps d raw path) (entry d regs raw path ctx)
      (cfg (some (resultLabel E.result)) (reset regs) E.data ctx) at run
    rw [data_eq] at run
    exact run
  · intro failed
    apply run_raw_failure caller d raw path regs ctx
    exact congrArg (fun r => some (resultLabel r)) failed
  · intro succeeded
    apply run_raw_success caller d raw path regs ctx
    exact congrArg (fun r => some (resultLabel r)) succeeded


section PhysicalSpace

variable [Fintype K]

def contextCells (ctx : ∀ k, List (Γ k)) : Nat := ∑ k, (ctx k).length

/-- The actual dependent sum over every physical stack index. -/
def stackCells (c : Cfg Γ Λ R) : Nat := ∑ k : StackId K, (c.stk k).length

omit [DecidableEq K] in
theorem stackCells_eq_sum (c : Cfg Γ Λ R) :
    stackCells c = ∑ k : StackId K, (c.stk k).length := rfl

theorem localStack_sum (f : LocalStack → Nat) :
    ∑ k, f k = f .source + f .saved + f .scratch + f .pending + f .path := by
  change (∑ k ∈ ({.source, .saved, .scratch, .pending, .path} : Finset LocalStack), f k) = _
  simp [Nat.add_comm, Nat.add_left_comm]

omit [DecidableEq K] in
theorem stackCells_cfg (label : Option (Label Λ)) (regs : Registers R)
    (D : LocalData) (ctx : ∀ k, List (Γ k)) :
    stackCells (cfg label regs D ctx) = localCells D + contextCells ctx := by
  rw [stackCells, Fintype.sum_sum_type, localStack_sum]
  rfl

def potential (c : Cfg Γ Λ R) : Nat := stackCells c + debt c.l + credit c

omit [DecidableEq K] in
theorem potential_cfg (control : Control) (regs : Registers R)
    (D : LocalData) (ctx : ∀ k, List (Γ k)) :
    potential (cfg (some (controlLabel (Λ := Λ) control)) regs D ctx) =
      localPotential control D + contextCells ctx := by
  rw [potential, stackCells_cfg, credit_control_cfg]
  change localCells D + contextCells ctx + debt (some (controlLabel (Λ := Λ) control)) +
    controlCredit control D = _
  rw [debt_controlLabel]
  simp only [localPotential]
  omega

omit [DecidableEq K] in
theorem stackCells_le_potential (c : Cfg Γ Λ R) : stackCells c ≤ potential c := by
  unfold potential
  omega

theorem local_step_potential_le {before after : Cfg Γ Λ R}
    (transition : LocalStep caller before after) : potential after ≤ potential before := by
  obtain ⟨q, regs, D, ctx, rfl⟩ := owned_cases before transition.1
  have same := Option.some.inj ((advance_step caller q D regs ctx).symm.trans transition.2)
  subst after
  change potential (cfg (some (controlLabel (Λ := Λ) (advance q D).1)) (reset regs) (advance q D).2 ctx) ≤
    potential (cfg (some (controlLabel (Λ := Λ) (.inl q))) regs D ctx)
  rw [potential_cfg, potential_cfg]
  exact Nat.add_le_add_right (advance_mass q D).2 _

theorem local_reaches_potential_le {start reached : Cfg Γ Λ R}
    (path : Relation.ReflTransGen (LocalStep caller) start reached) : potential reached ≤ potential start := by
  induction path with
  | refl => exact Nat.le_refl _
  | @tail before after _ transition ih => exact (local_step_potential_le caller transition).trans ih

theorem prefix_potential_le (start : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start)
    (reached : Cfg Γ Λ R) (executed : (next caller)^[n] (some start) = some reached) :
    potential reached ≤ potential start := by
  obtain ⟨actual, run, _, path⟩ := Resources.BinaryCounter.FixedWidthMachine.ranked_prefix
    (step caller) remainingSteps (local_progress caller) n start bound
  have same := Option.some.inj (run.symm.trans executed)
  subst reached
  apply local_reaches_potential_le caller
  exact Relation.ReflTransGen.mono
    (fun before _ h => ⟨(remainingSteps_pos_iff before).mp h.1, h.2⟩) _ _ path

theorem prefix_stackCells_le_dirty (start : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start)
    (reached : Cfg Γ Λ R) (executed : (next caller)^[n] (some start) = some reached) :
    stackCells reached ≤ potential start :=
  (stackCells_le_potential reached).trans (prefix_potential_le caller start n bound reached executed)

omit [DecidableEq K] in
theorem entry_potential (d : RotationDirection) (raw : Word) (path : List Branch)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    potential (entry (Λ := Λ) d regs raw path ctx) =
      2 * raw.length + path.length + contextCells ctx := by
  change potential (cfg (some (controlLabel (Λ := Λ) (.inl (.seek d)))) regs
    { source := raw, path := path } ctx) = _
  rw [potential_cfg]
  simp [localPotential, localCells, controlDebt, phaseDebt, controlCredit, phaseCredit]; omega

theorem prefix_stackCells_le (d : RotationDirection) (raw : Word) (path : List Branch)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) (n : Nat) (bound : n ≤ runSteps d raw path)
    (reached : Cfg Γ Λ R) (executed : (next caller)^[n] (some (entry d regs raw path ctx)) = some reached) :
    stackCells reached ≤ 2 * raw.length + path.length + contextCells ctx := by
  have bounded := prefix_stackCells_le_dirty caller (entry d regs raw path ctx) n bound reached executed
  simpa only [entry_potential] using bounded

end PhysicalSpace

/-! ## Sharp malformed-input and path-stop families -/

section MalformedFamilies

omit [DecidableEq K] in
theorem continues_nodes (n h : Nat) :
    Continues (List.replicate n nodeTag) h (h + n) := by
  induction n with
  | zero => simpa using Continues.nil h
  | succ n ih =>
      simpa only [List.replicate_succ', Nat.add_assoc] using Continues.node ih

/-- The scanner prefix really consumes every node and creates every pending cell. -/
theorem scanScratch_nodes_localRun (d : RotationDirection) (n : Nat)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller n
      (cfg (some (phaseLabel (.scanScratch d))) (reset regs)
        { source := List.replicate n nodeTag, pending := [()] } ctx)
      (cfg (some (phaseLabel (.scanScratch d))) (reset regs)
        { scratch := List.replicate n nodeTag, pending := List.replicate (n + 1) () } ctx) := by
  simpa [afterScanRegisters, reset_reset, Nat.add_comm] using
    scanScratch_continues_localRun caller (continues_nodes n 1) d []
      ({} : LocalData) (reset regs) ctx

/-- Left all-node input attains its maximal physical size at this actual drop phase. -/
theorem left_nodes_drop (n : Nat) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (2 * n + 2)
      (cfg (some (phaseLabel (.seek .left))) regs { source := List.replicate n nodeTag } ctx)
      (cfg (some (phaseLabel .dropPending)) (reset regs)
        { source := List.replicate n nodeTag, pending := List.replicate n () } ctx) := by
  cases n with
  | zero =>
      have seek := phase_step_localRun caller
        (seek_step_path_nil caller .left ({} : LocalData) regs ctx)
      have start := phase_step_localRun caller
        (start_left_step_nil caller ({} : LocalData) (reset regs) ctx)
      simpa only [List.replicate_zero, reset_reset] using LocalRun.trans caller seek start
  | succ n =>
      let scanned : LocalData :=
        { scratch := List.replicate n nodeTag, pending := List.replicate (n + 1) () }
      let restored : LocalData :=
        { source := List.replicate n nodeTag, pending := List.replicate (n + 1) () }
      have seek := phase_step_localRun caller
        (seek_step_path_nil caller .left { source := nodeTag :: List.replicate n nodeTag } regs ctx)
      have start := phase_step_localRun caller
        (start_left_step_node caller (List.replicate n nodeTag) ({} : LocalData) (reset regs) ctx)
      have scan := scanScratch_nodes_localRun caller .left n regs ctx
      have failed := phase_step_localRun caller
        (scanScratch_step_nil caller .left scanned (reset regs) ctx)
      have moved : LocalRun caller n
          (cfg (some (phaseLabel (.restoreScratch .failureLeft))) (reset regs) scanned ctx)
          (cfg (some (phaseLabel (.restoreScratch .failureLeft))) (reset regs) restored ctx) := by
        simpa [scanned, restored, reset_reset] using
          restoreScratch_prefix_localRun caller .failureLeft (List.replicate n nodeTag) []
            { pending := List.replicate (n + 1) () } (reset regs) ctx
      have probe := phase_step_localRun caller
        (restoreScratch_step_nil caller .failureLeft restored (reset regs) ctx)
      have joined := LocalRun.trans caller seek (LocalRun.trans caller start
        (LocalRun.trans caller scan (LocalRun.trans caller failed (LocalRun.trans caller moved probe))))
      simpa [scanned, restored, scratchFailure, reset_reset, markerWord, modeResult,
        List.replicate_succ, Nat.mul_add, two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using joined

theorem left_nodes_run (n : Nat) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (3 * n + 4)
      (cfg (some (phaseLabel (.seek .left))) regs { source := List.replicate n nodeTag } ctx)
      (cfg (some (resultLabel .failure)) (reset regs) { source := List.replicate n nodeTag } ctx) := by
  have first := left_nodes_drop caller n regs ctx
  have last := dropPending_localRun caller
    { source := List.replicate n nodeTag, pending := List.replicate n () } (reset regs) ctx
  simpa [dropPendingData, reset_reset, Nat.succ_mul, two_mul,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using LocalRun.trans caller first last

/-- The right-root two-node setup creates one fewer cell than the clean bound. -/
theorem right_nodes_drop (m : Nat) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (2 * m + 4)
      (cfg (some (phaseLabel (.seek .right))) regs
        { source := List.replicate (m + 2) nodeTag } ctx)
      (cfg (some (phaseLabel .dropPending)) (reset regs)
        { source := List.replicate (m + 2) nodeTag,
          pending := List.replicate (m + 1) () } ctx) := by
  let scanned : LocalData :=
    { scratch := List.replicate m nodeTag, pending := List.replicate (m + 1) () }
  let restored : LocalData :=
    { source := List.replicate m nodeTag, pending := List.replicate (m + 1) () }
  have seek := phase_step_localRun caller
    (seek_step_path_nil caller .right
      { source := nodeTag :: nodeTag :: List.replicate m nodeTag } regs ctx)
  have start := phase_step_localRun caller
    (start_right_step_nodes caller (List.replicate m nodeTag) ({} : LocalData) (reset regs) ctx)
  have scan := scanScratch_nodes_localRun caller .right m regs ctx
  have failed := phase_step_localRun caller
    (scanScratch_step_nil caller .right scanned (reset regs) ctx)
  have moved : LocalRun caller m
      (cfg (some (phaseLabel (.restoreScratch .failureRight))) (reset regs) scanned ctx)
      (cfg (some (phaseLabel (.restoreScratch .failureRight))) (reset regs) restored ctx) := by
    simpa [scanned, restored, reset_reset] using
      restoreScratch_prefix_localRun caller .failureRight (List.replicate m nodeTag) []
        { pending := List.replicate (m + 1) () } (reset regs) ctx
  have probe := phase_step_localRun caller
    (restoreScratch_step_nil caller .failureRight restored (reset regs) ctx)
  have joined := LocalRun.trans caller seek (LocalRun.trans caller start
    (LocalRun.trans caller scan (LocalRun.trans caller failed (LocalRun.trans caller moved probe))))
  simpa [scanned, restored, scratchFailure, reset_reset, markerWord, modeResult,
    List.replicate_succ, two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using joined

theorem right_nodes_run (m : Nat) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (3 * m + 7)
      (cfg (some (phaseLabel (.seek .right))) regs
        { source := List.replicate (m + 2) nodeTag } ctx)
      (cfg (some (resultLabel .failure)) (reset regs)
        { source := List.replicate (m + 2) nodeTag } ctx) := by
  have first := right_nodes_drop caller m regs ctx
  have last := dropPending_localRun caller
    { source := List.replicate (m + 2) nodeTag,
      pending := List.replicate (m + 1) () } (reset regs) ctx
  simpa [dropPendingData, reset_reset, Nat.succ_mul, two_mul,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using LocalRun.trans caller first last

/-- Every successful left descent moves one literal marker to saved and pops one Branch. -/
theorem seek_left_nodes_localRun (d : RotationDirection) (n : Nat)
    (raw : Word) (p : List Branch) (f : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller n
      (cfg (some (phaseLabel (.seek d))) regs
        { source := List.replicate n nodeTag ++ raw,
          saved := f, path := List.replicate n Branch.left ++ p } ctx)
      (cfg (some (phaseLabel (.seek d))) (if n = 0 then regs else reset regs)
        { source := raw, saved := (List.replicate n nodeTag).reverse ++ f, path := p } ctx) := by
  induction n generalizing f regs with
  | zero =>
      simpa using LocalRun.refl (caller := caller)
        (cfg (some (phaseLabel (.seek d))) regs { source := raw, saved := f, path := p } ctx)
  | succ n ih =>
      have first := phase_step_localRun caller
        (seek_step_node_left caller d (List.replicate n nodeTag ++ raw)
          (List.replicate n Branch.left ++ p) { saved := f } regs ctx)
      have tail := ih (nodeTag :: f) (reset regs)
      simpa only [List.replicate_succ, List.cons_append, List.reverse_cons,
        List.append_assoc, List.singleton_append, List.nil_append, Nat.succ_ne_zero, ite_false,
        reset_reset, ite_self, Nat.add_comm 1 n] using LocalRun.trans caller first tail

/-- The failed head is consumed, while every remaining overlong path cell survives. -/
theorem left_path_overrun (d : RotationDirection) (n k : Nat) (positive : 0 < k)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (2 * n + 3)
      (cfg (some (phaseLabel (.seek d))) regs
        { source := List.replicate n nodeTag,
          path := List.replicate (n + k) Branch.left } ctx)
      (cfg (some (resultLabel .failure)) (reset regs)
        { source := List.replicate n nodeTag,
          path := List.replicate (k - 1) Branch.left } ctx) := by
  cases k with
  | zero => omega
  | succ k =>
      let midRegs := if n = 0 then regs else reset regs
      let stopped : LocalData :=
        { saved := List.replicate n nodeTag, path := List.replicate k Branch.left }
      have navigate : LocalRun caller n
          (cfg (some (phaseLabel (.seek d))) regs
            { source := List.replicate n nodeTag,
              path := List.replicate (n + (k + 1)) Branch.left } ctx)
          (cfg (some (phaseLabel (.seek d))) midRegs
            { stopped with path := Branch.left :: List.replicate k Branch.left } ctx) := by
        simpa [midRegs, stopped, List.replicate_add, List.replicate_succ] using
          seek_left_nodes_localRun caller d n []
            (Branch.left :: List.replicate k Branch.left) [] regs ctx
      have failed := phase_step_localRun caller
        (seek_step_source_nil caller d .left (List.replicate k Branch.left) stopped midRegs ctx)
      have cleanup := dropPending_localRun caller stopped (reset midRegs) ctx
      have joined := LocalRun.trans caller navigate (LocalRun.trans caller failed cleanup)
      simpa [midRegs, stopped, dropPendingData, apply_ite, reset_reset,
        List.replicate_add, List.replicate_succ, two_mul,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using joined

/-- Exhausting the path first takes the distinct paid empty-root route. -/
theorem left_path_exhausted (d : RotationDirection) (n : Nat)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    LocalRun caller (2 * n + 4)
      (cfg (some (phaseLabel (.seek d))) regs
        { source := List.replicate n nodeTag, path := List.replicate n Branch.left } ctx)
      (cfg (some (resultLabel .failure)) (reset regs)
        { source := List.replicate n nodeTag } ctx) := by
  let midRegs := if n = 0 then regs else reset regs
  have navigate : LocalRun caller n
      (cfg (some (phaseLabel (.seek d))) regs
        { source := List.replicate n nodeTag, path := List.replicate n Branch.left } ctx)
      (cfg (some (phaseLabel (.seek d))) midRegs { saved := List.replicate n nodeTag } ctx) := by
    simpa [midRegs] using seek_left_nodes_localRun caller d n [] [] [] regs ctx
  have root := root_nonnode_localRun caller d [] (List.replicate n nodeTag)
    True.intro midRegs ctx
  simpa [midRegs, apply_ite, reset_reset, two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    LocalRun.trans caller navigate root

theorem left_nodes_exact_clock (caller : External Λ → Statement Γ Λ R) (n : Nat) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    runSteps .left (List.replicate n nodeTag) [] = 3 * n + 4 := by
  simpa only [remainingSteps, cfg, phaseLabel, resultLabel, dataOfCfg, Nat.add_zero, runSteps] using
    LocalRun.remaining caller (left_nodes_run caller n regs ctx)

theorem right_nodes_exact_clock (caller : External Λ → Statement Γ Λ R) (m : Nat) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    runSteps .right (List.replicate (m + 2) nodeTag) [] = 3 * m + 7 := by
  simpa only [remainingSteps, cfg, phaseLabel, resultLabel, dataOfCfg, Nat.add_zero, runSteps] using
    LocalRun.remaining caller (right_nodes_run caller m regs ctx)

theorem left_nodes_drop_rank (caller : External Λ → Statement Γ Λ R) (n : Nat) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    remainingSteps (cfg (some (phaseLabel .dropPending)) regs
      { source := List.replicate n nodeTag, pending := List.replicate n () } ctx : Cfg Γ Λ R) = n + 2 := by
  simpa only [remainingSteps, cfg, phaseLabel, resultLabel, dataOfCfg, Nat.add_zero,
    List.length_replicate, List.length_nil] using
    LocalRun.remaining caller (dropPending_localRun caller
      { source := List.replicate n nodeTag, pending := List.replicate n () } regs ctx)

theorem right_nodes_drop_rank (caller : External Λ → Statement Γ Λ R) (m : Nat) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    remainingSteps (cfg (some (phaseLabel .dropPending)) regs
      { source := List.replicate (m + 2) nodeTag,
        pending := List.replicate (m + 1) () } ctx : Cfg Γ Λ R) = m + 3 := by
  have exact := LocalRun.remaining caller (dropPending_localRun caller
    { source := List.replicate (m + 2) nodeTag,
      pending := List.replicate (m + 1) () } regs ctx)
  simpa only [remainingSteps, cfg, phaseLabel, resultLabel, dataOfCfg, Nat.add_zero,
    List.length_replicate, List.length_nil, Nat.add_assoc] using exact

variable [Fintype K]

omit [DecidableEq K] in
theorem left_nodes_drop_cells (n : Nat) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    stackCells (cfg (some (phaseLabel .dropPending)) regs
      { source := List.replicate n nodeTag, pending := List.replicate n () } ctx : Cfg Γ Λ R) =
        2 * n + contextCells ctx := by
  rw [stackCells_cfg]
  simp [localCells, two_mul]

omit [DecidableEq K] in
theorem right_nodes_drop_cells (m : Nat) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    stackCells (cfg (some (phaseLabel .dropPending)) regs
      { source := List.replicate (m + 2) nodeTag,
        pending := List.replicate (m + 1) () } ctx : Cfg Γ Λ R) =
        2 * m + 3 + contextCells ctx := by
  rw [stackCells_cfg]
  simp [localCells]
  omega

end MalformedFamilies


/-! ## Finite package and genuine initializer -/

section PositionFinitePackage

variable [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]

def initialRegisters (initial : R) : Registers R := ((none, (none, none)), initial)

/-- Caller, direction and initial caller state are fixed before the raw input. -/
def machine (d : RotationDirection) (initial : R) : Turing.FinTM2 where
  K := StackId K
  k₀ := .inl .source
  k₁ := .inl .source
  Γ := alphabet Γ
  Λ := Label Λ
  main := phaseLabel (.seek d)
  σ := Registers R
  initialState := initialRegisters initial
  Γk₀Fin := alphabetFintype (.inl .source)
  m := program caller

/-- The stronger finite alphabet evidence is exhibited at every actual index. -/
@[instance_reducible]
def machineAlphabetFintype (d : RotationDirection) (initial : R)
    (k : (machine caller d initial).K) :
    Fintype ((machine caller d initial).Γ k) := alphabetFintype k

theorem machine_card_stackId (d : RotationDirection) (initial : R) :
    @Fintype.card (machine caller d initial).K (machine caller d initial).kFin = 5 + Fintype.card K :=
  card_stackId

theorem machine_card_label (d : RotationDirection) (initial : R) :
    @Fintype.card (machine caller d initial).Λ (machine caller d initial).ΛFin = 18 + Fintype.card Λ :=
  card_label

theorem machine_card_registers (d : RotationDirection) (initial : R) :
    @Fintype.card (machine caller d initial).σ (machine caller d initial).σFin = 102 * Fintype.card R :=
  card_registers

theorem machine_step_eq (d : RotationDirection) (initial : R) (c : Cfg Γ Λ R) :
    (machine caller d initial).step c = step caller c := rfl

/-- A real one-input initializer: every store other than source is empty. -/
theorem initList_eq (d : RotationDirection) (initial : R) (raw : Word) :
    Turing.initList (machine caller d initial) raw =
      entry d (initialRegisters initial) raw [] (fun _ => []) := by
  apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem machine_phase_run (d : RotationDirection) (initial : R) (q : Phase)
    (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (fun c : Option (Cfg Γ Λ R) => c.bind (machine caller d initial).step)^[phaseSteps q D]
        (some (cfg (some (phaseLabel q)) regs D ctx)) = some (phaseResult q regs D ctx) :=
  phase_iterate caller q D regs ctx

theorem machine_cfg_run (d : RotationDirection) (initial : R)
    (raw : Word) (path : List Branch) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (fun c : Option (Cfg Γ Λ R) => c.bind (machine caller d initial).step)^[runSteps d raw path]
        (some (entry d regs raw path ctx)) =
      some (phaseResult (.seek d) regs { source := raw, path := path } ctx) :=
  phase_iterate caller (.seek d) { source := raw, path := path } regs ctx

theorem machine_init_run (d : RotationDirection) (initial : R) (raw : Word) :
    (fun c : Option (Cfg Γ Λ R) => c.bind (machine caller d initial).step)^[runSteps d raw []]
        (some (Turing.initList (machine caller d initial) raw)) =
      some (phaseResult (.seek d) (initialRegisters initial) { source := raw } (fun _ => [])) := by
  rw [initList_eq]
  exact machine_cfg_run caller d initial raw [] (initialRegisters initial) (fun _ => [])

def machinePhaseInTime (d : RotationDirection) (initial : R) (q : Phase)
    (D : LocalData) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (machine caller d initial).step
      (cfg (some (phaseLabel q)) regs D ctx) (some (phaseResult q regs D ctx)) (phaseSteps q D) where
  steps := phaseSteps q D
  evals_in_steps := machine_phase_run caller d initial q D regs ctx
  steps_le_m := Nat.le_refl _

def machineCfgInTime (d : RotationDirection) (initial : R)
    (raw : Word) (path : List Branch) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (machine caller d initial).step (entry d regs raw path ctx)
      (some (phaseResult (.seek d) regs { source := raw, path := path } ctx))
      (runSteps d raw path) where
  steps := runSteps d raw path
  evals_in_steps := machine_cfg_run caller d initial raw path regs ctx
  steps_le_m := Nat.le_refl _

def machineInitInTime (d : RotationDirection) (initial : R) (raw : Word) :
    StateTransition.EvalsToInTime (machine caller d initial).step
      (Turing.initList (machine caller d initial) raw)
      (some (phaseResult (.seek d) (initialRegisters initial) { source := raw } (fun _ => [])))
      (runSteps d raw []) where
  steps := runSteps d raw []
  evals_in_steps := machine_init_run caller d initial raw
  steps_le_m := Nat.le_refl _

def machineInitInLinearTime (d : RotationDirection) (initial : R) (raw : Word) :
    StateTransition.EvalsToInTime (machine caller d initial).step
      (Turing.initList (machine caller d initial) raw)
      (some (phaseResult (.seek d) (initialRegisters initial) { source := raw } (fun _ => [])))
      (3 * raw.length + 5) where
  steps := runSteps d raw []
  evals_in_steps := machine_init_run caller d initial raw
  steps_le_m := by simpa using runSteps_le d raw []

def machineInitInConservativeTime (d : RotationDirection) (initial : R) (raw : Word) :
    StateTransition.EvalsToInTime (machine caller d initial).step
      (Turing.initList (machine caller d initial) raw)
      (some (phaseResult (.seek d) (initialRegisters initial) { source := raw } (fun _ => [])))
      (4 * raw.length + 12) where
  steps := runSteps d raw []
  evals_in_steps := machine_init_run caller d initial raw
  steps_le_m := by simpa using runSteps_le_conservative d raw []

/-- The installed-path contract is distinct from source-only initialization. -/
theorem machine_cfg_prefix_stackCells_le (d : RotationDirection) (initial : R)
    (raw : Word) (path : List Branch) (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (n : Nat) (bound : n ≤ runSteps d raw path) (reached : Cfg Γ Λ R)
    (executed :
      (fun c : Option (Cfg Γ Λ R) => c.bind (machine caller d initial).step)^[n]
        (some (entry d regs raw path ctx)) = some reached) :
    stackCells reached ≤ 2 * raw.length + path.length + contextCells ctx :=
  prefix_stackCells_le caller d raw path regs ctx n bound reached executed

theorem machine_prefix_stackCells_le (d : RotationDirection) (initial : R)
    (raw : Word) (n : Nat) (bound : n ≤ runSteps d raw []) (reached : Cfg Γ Λ R)
    (executed :
      (fun c : Option (Cfg Γ Λ R) => c.bind (machine caller d initial).step)^[n]
        (some (Turing.initList (machine caller d initial) raw)) = some reached) :
    stackCells reached ≤ 2 * raw.length := by
  rw [initList_eq] at executed
  have cells := machine_cfg_prefix_stackCells_le caller d initial raw [] (initialRegisters initial)
    (fun _ => []) n bound reached executed
  simpa [contextCells] using cells

end PositionFinitePackage

end Resources.RotationCertificate.PositionedRotationMachine
