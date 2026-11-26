import Applications.Resources.RotationCertificate.InputParser
import Applications.Resources.RotationCertificate.TreeParserMachine

/-!
# An open finite-stack machine for complete rotation-certificate inputs

The two tree calls share the actual raw and scratch stacks of the unchanged
tree core. Its three nonterminal result labels execute the separator and
restoration bodies directly. Every unbounded transfer is an actual goto;
source values, counts, and invariants below are proof-side objects.
Correspondence: `docs/research/fdsa-rotation-certificate-preparation.md`.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.RotationCertificate.InputParserMachine
open Resources.BinaryCounter (Bits)

inductive TreeSide | source | target
  deriving DecidableEq

instance : Fintype TreeSide where
  elems := {.source, .target}
  complete side := by cases side <;> decide

inductive ExtraStack | fuel | bitsReverse
  deriving DecidableEq

instance : Fintype ExtraStack where
  elems := {.fuel, .bitsReverse}
  complete slot := by cases slot <;> decide

inductive Phase
  | bitsScan | bitsEmit | eof | restoreEnd | fuelUndo | bitsUndo
  | restoreSep2 | targetToReverse | targetToRaw | restoreSep1
  | sourceToReverse | sourceToRaw
  deriving DecidableEq

instance : Fintype Phase where
  elems := {.bitsScan, .bitsEmit, .eof, .restoreEnd, .fuelUndo, .bitsUndo,
    .restoreSep2, .targetToReverse, .targetToRaw, .restoreSep1,
    .sourceToReverse, .sourceToRaw}
  complete phase := by cases phase <;> decide

abbrev StackId (K : Type) := TreeParserMachine.StackId TreeSide (ExtraStack ⊕ K)
abbrev Label (Λ : Type) := TreeParserMachine.Label TreeSide (Phase ⊕ (Unit ⊕ Λ))
abbrev Registers (R : Type) := TreeParserMachine.Registers R
abbrev External (Λ : Type) := TreeParserMachine.Result ⊕ Λ

variable {K Λ R : Type} {Γ : K → Type}

abbrev ExtraAlphabet (Γ : K → Type) : ExtraStack ⊕ K → Type
  | .inl _ => Bool
  | .inr k => Γ k

instance extraAlphabetFintype [∀ k, Fintype (Γ k)] (k : ExtraStack ⊕ K) :
    Fintype (ExtraAlphabet Γ k) := by
  cases k with
  | inl slot => exact inferInstance
  | inr k => exact inferInstance

abbrev Alphabet (Γ : K → Type) := TreeParserMachine.Alphabet TreeSide (ExtraAlphabet Γ)
abbrev Statement (Γ : K → Type) (Λ R : Type) :=
  TreeParserMachine.Statement TreeSide (ExtraAlphabet Γ) (Phase ⊕ (Unit ⊕ Λ)) R
abbrev Cfg (Γ : K → Type) (Λ R : Type) :=
  TreeParserMachine.Cfg TreeSide (ExtraAlphabet Γ) (Phase ⊕ (Unit ⊕ Λ)) R

abbrev rawStack : StackId K := .inl .raw
abbrev reverseStack : StackId K := .inl .reverse
abbrev pendingStack : StackId K := .inl .pending
abbrev outputStack (d : TreeSide) : StackId K := .inl (.output d)
abbrev fuelStack : StackId K := .inr (.inl .fuel)
abbrev bitsReverseStack : StackId K := .inr (.inl .bitsReverse)
abbrev protectedStack (k : K) : StackId K := .inr (.inr k)

def treeLabel (d : TreeSide) (phase : TreeParserMachine.Phase) : Label Λ := TreeParserMachine.phaseLabel d phase
def treeResultLabel (d : TreeSide) (result : TreeParserMachine.Result) : Label Λ := TreeParserMachine.resultLabel d result
def phaseLabel (phase : Phase) : Label Λ := TreeParserMachine.callerLabel (.inl phase)
def resultLabel : TreeParserMachine.Result → Label Λ
  | .success => TreeParserMachine.callerLabel (.inr (.inl ()))
  | .failure => TreeParserMachine.resultLabel .source .failure
def callerLabel (label : Λ) : Label Λ := TreeParserMachine.callerLabel (.inr (.inr label))

abbrev reset (regs : Registers R) := TreeParserMachine.reset regs
abbrev jump (label : Label Λ) : Statement Γ Λ R := TreeParserMachine.jump label

def treeOutputs (source target : Word) : TreeSide → Word
  | .source => source
  | .target => target

def stores (fuel bitsReverse : Bits) (ctx : ∀ k, List (Γ k)) :
    ∀ k, List (ExtraAlphabet Γ k)
  | .inl .fuel => fuel
  | .inl .bitsReverse => bitsReverse
  | .inr k => ctx k

def cfg (label : Option (Label Λ)) (regs : Registers R) (raw rev : Word)
    (pending : List Unit) (outputs : TreeSide → Word) (fuel bitsReverse : Bits)
    (ctx : ∀ k, List (Γ k)) : Cfg Γ Λ R :=
  TreeParserMachine.cfg label regs raw rev pending outputs (stores fuel bitsReverse ctx)

theorem cfg_ext {left right : Cfg Γ Λ R}
    (label : left.l = right.l) (regs : left.var = right.var)
    (raw : left.stk rawStack = right.stk rawStack)
    (rev : left.stk reverseStack = right.stk reverseStack)
    (pending : left.stk pendingStack = right.stk pendingStack)
    (outputs : ∀ d, left.stk (outputStack d) = right.stk (outputStack d))
    (fuel : left.stk fuelStack = right.stk fuelStack)
    (bitsReverse : left.stk bitsReverseStack = right.stk bitsReverseStack)
    (ctx : ∀ k, left.stk (protectedStack k) = right.stk (protectedStack k)) : left = right := by
  apply TreeParserMachine.cfg_ext label regs raw rev pending outputs
  intro k
  cases k with
  | inl slot => cases slot with
    | fuel => exact fuel
    | bitsReverse => exact bitsReverse
  | inr k => exact ctx k

theorem cfg_eta (c : Cfg Γ Λ R) :
    cfg c.l c.var (c.stk rawStack) (c.stk reverseStack) (c.stk pendingStack)
      (fun d => c.stk (outputStack d)) (c.stk fuelStack) (c.stk bitsReverseStack)
      (fun k => c.stk (protectedStack k)) = c := by
  apply cfg_ext <;> first | rfl | exact fun _ => rfl

def storeBit (regs : Registers R) (observed : Option Bool) : Registers R :=
  TreeParserMachine.storeTag regs (observed.map bitTag)

def observedBit (regs : Registers R) : Bool := decide (regs.1.1 = some bitOneTag)

def toReversePhase : TreeSide → Phase
  | .source => .sourceToReverse
  | .target => .targetToReverse

def toRawPhase : TreeSide → Phase
  | .source => .sourceToRaw
  | .target => .targetToRaw

def afterRollback : TreeSide → Label Λ
  | .source => resultLabel .failure
  | .target => phaseLabel .restoreSep1

def separatorBlock (accepted rejected : Label Λ) : Statement Γ Λ R :=
  .peek rawStack TreeParserMachine.storeTag (.branch (fun regs => decide (regs.1.1 = some separatorTag))
    (.pop rawStack TreeParserMachine.storeTag (jump accepted)) (jump rejected))

def toReverseBlock (d : TreeSide) : Statement Γ Λ R :=
  .pop (outputStack d) TreeParserMachine.storeTag (.branch (fun regs => regs.1.1.isSome)
    (.push reverseStack (fun regs => regs.1.1.getD emptyTag) (jump (phaseLabel (toReversePhase d))))
    (jump (phaseLabel (toRawPhase d))))

def toRawBlock (d : TreeSide) : Statement Γ Λ R :=
  .pop reverseStack TreeParserMachine.storeTag (.branch (fun regs => regs.1.1.isSome)
    (.push rawStack (fun regs => regs.1.1.getD emptyTag) (jump (phaseLabel (toRawPhase d))))
    (jump (afterRollback d)))

/-- These finite blocks inspect only actual stack observations in finite registers. -/
def block : Phase → Statement Γ Λ R
  | .bitsScan =>
      .peek rawStack TreeParserMachine.storeTag
        (.branch (fun regs => decide (regs.1.1 = some bitZeroTag ∨ regs.1.1 = some bitOneTag))
          (.pop rawStack TreeParserMachine.storeTag
            (.push bitsReverseStack observedBit (jump (phaseLabel .bitsScan))))
          (.branch (fun regs => decide (regs.1.1 = some endInputTag))
            (.pop rawStack TreeParserMachine.storeTag (jump (phaseLabel .bitsEmit)))
            (jump (phaseLabel .bitsUndo))))
  | .bitsEmit =>
      .pop bitsReverseStack storeBit (.branch (fun regs => regs.1.1.isSome)
        (.push fuelStack observedBit (jump (phaseLabel .bitsEmit)))
        (jump (phaseLabel .eof)))
  | .eof =>
      .peek rawStack TreeParserMachine.storeTag (.branch (fun regs => regs.1.1.isSome)
        (jump (phaseLabel .restoreEnd)) (jump (resultLabel .success)))
  | .restoreEnd => .push rawStack (fun _ => endInputTag) (jump (phaseLabel .fuelUndo))
  | .fuelUndo =>
      .pop fuelStack storeBit (.branch (fun regs => regs.1.1.isSome)
        (.push bitsReverseStack observedBit (jump (phaseLabel .fuelUndo)))
        (jump (phaseLabel .bitsUndo)))
  | .bitsUndo =>
      .pop bitsReverseStack storeBit (.branch (fun regs => regs.1.1.isSome)
        (.push rawStack (fun regs => regs.1.1.getD bitZeroTag) (jump (phaseLabel .bitsUndo)))
        (jump (phaseLabel .restoreSep2)))
  | .restoreSep2 => .push rawStack (fun _ => separatorTag) (jump (phaseLabel .targetToReverse))
  | .targetToReverse => toReverseBlock .target
  | .targetToRaw => toRawBlock .target
  | .restoreSep1 => .push rawStack (fun _ => separatorTag) (jump (phaseLabel .sourceToReverse))
  | .sourceToReverse => toReverseBlock .source
  | .sourceToRaw => toRawBlock .source

def handler (caller : External Λ → Statement Γ Λ R) :
    TreeParserMachine.External TreeSide (Phase ⊕ (Unit ⊕ Λ)) → Statement Γ Λ R
  | .inl (.source, .success) => separatorBlock (treeLabel .target .init) (phaseLabel .sourceToReverse)
  | .inl (.target, .success) => separatorBlock (phaseLabel .bitsScan) (phaseLabel .targetToReverse)
  | .inl (.target, .failure) => block .restoreSep1
  | .inl (.source, .failure) => caller (.inl .failure)
  | .inr (.inl phase) => block phase
  | .inr (.inr (.inl _)) => caller (.inl .success)
  | .inr (.inr (.inr label)) => caller (.inr label)

def program (caller : External Λ → Statement Γ Λ R) : Label Λ → Statement Γ Λ R :=
  TreeParserMachine.program (handler caller)

def FullOwned : Option (Label Λ) → Prop
  | some (.inl _) => True
  | some (.inr (.inl (.source, .failure))) => False
  | some (.inr (.inl _)) => True
  | some (.inr (.inr (.inl _))) => True
  | _ => False

@[simp] theorem fullOwned_tree (d : TreeSide) (phase : TreeParserMachine.Phase) :
    FullOwned (some (treeLabel (Λ := Λ) d phase)) := True.intro

@[simp] theorem fullOwned_phase (phase : Phase) :
    FullOwned (some (phaseLabel (Λ := Λ) phase)) := True.intro

@[simp] theorem not_fullOwned_result (result : TreeParserMachine.Result) :
    ¬ FullOwned (some (resultLabel (Λ := Λ) result)) := by cases result <;> exact id

theorem fullOwned_of_treeParserMachineOwned (label : Option (Label Λ)) (owned : TreeParserMachine.Owned label) :
    FullOwned label := by
  cases label with
  | none => cases owned
  | some label => cases label with
    | inl pair => trivial
    | inr external => cases owned

variable [DecidableEq K]

def step (caller : External Λ → Statement Γ Λ R) : Cfg Γ Λ R → Option (Cfg Γ Λ R) :=
  TreeParserMachine.step (handler caller)

def next (caller : External Λ → Statement Γ Λ R) : Option (Cfg Γ Λ R) → Option (Cfg Γ Λ R) :=
  TreeParserMachine.next (handler caller)

@[simp] theorem next_none (caller : External Λ → Statement Γ Λ R) : next caller none = none := rfl
@[simp] theorem next_some (caller : External Λ → Statement Γ Λ R) (c : Cfg Γ Λ R) :
    next caller (some c) = step caller c := rfl

variable (caller : External Λ → Statement Γ Λ R)

theorem iterate_step (n : Nat) (c e : Cfg Γ Λ R) (transition : step caller c = some e) :
    (next caller)^[n + 1] (some c) = (next caller)^[n] (some e) :=
  TreeParserMachine.iterate_step (handler caller) n c e transition

/-- An indexed proof of actual owned transitions, not a runtime evaluator. -/
inductive Runs : Nat → Cfg Γ Λ R → Cfg Γ Λ R → Prop
  | refl (c) : Runs 0 c c
  | cons {n c middle final} : FullOwned c.l → step caller c = some middle →
      Runs n middle final → Runs (n + 1) c final

theorem Runs.iterate {n : Nat} {start final : Cfg Γ Λ R}
    (run : Runs caller n start final) : (next caller)^[n] (some start) = some final := by
  induction run with
  | refl c => rfl
  | @cons n c middle final owned transition run ih =>
      rw [iterate_step caller n c middle transition, ih]

theorem Runs.trans {n m : Nat} {start middle final : Cfg Γ Λ R}
    (first : Runs caller n start middle) (second : Runs caller m middle final) :
    Runs caller (n + m) start final := by
  induction first with
  | refl c => simpa only [Nat.zero_add] using second
  | @cons n c after middle owned transition run ih =>
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        Runs.cons owned transition (ih second)

theorem Runs.one {start final : Cfg Γ Λ R} (owned : FullOwned start.l)
    (transition : step caller start = some final) : Runs caller 1 start final :=
  .cons owned transition (.refl final)

theorem Runs.prefix {n : Nat} {start final : Cfg Γ Λ R}
    (run : Runs caller n start final) (j : Nat) (bound : j ≤ n) :
    ∃ reached, (next caller)^[j] (some start) = some reached ∧
      Runs caller j start reached ∧ Runs caller (n - j) reached final := by
  induction run generalizing j with
  | refl c =>
      have zero : j = 0 := by omega
      subst j
      exact ⟨c, rfl, .refl c, .refl c⟩
  | @cons n c middle final owned transition run ih =>
      cases j with
      | zero => exact ⟨c, rfl, .refl c, .cons owned transition run⟩
      | succ j =>
          obtain ⟨reached, executed, before, after⟩ := ih j (by omega)
          refine ⟨reached, ?_, .cons owned transition before, ?_⟩
          · rw [iterate_step caller j c middle transition, executed]
          · simpa only [Nat.add_sub_add_right] using after

theorem Runs.owned_start {n : Nat} {start final : Cfg Γ Λ R}
    (run : Runs caller n start final) (positive : 0 < n) : FullOwned start.l := by
  cases run with
  | refl c => omega
  | cons owned transition run => exact owned

theorem Runs.owned_prefix {n : Nat} {start final : Cfg Γ Λ R}
    (run : Runs caller n start final) (j : Nat) (bound : j < n) :
    ∃ reached, (next caller)^[j] (some start) = some reached ∧ FullOwned reached.l := by
  obtain ⟨reached, executed, _, after⟩ := run.prefix caller j (by omega)
  exact ⟨reached, executed, after.owned_start caller (by omega)⟩

def afterSeparator : TreeSide → Label Λ
  | .source => treeLabel .target .init
  | .target => phaseLabel .bitsScan

theorem separator_step_separator (d : TreeSide) (raw rev : Word) (pending : List Unit)
    (regs : Registers R) (outputs : TreeSide → Word) (fuel bitsReverse : Bits)
    (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (treeResultLabel d .success)) regs (separatorTag :: raw)
        rev pending outputs fuel bitsReverse ctx) =
      some (cfg (some (afterSeparator d)) (reset regs) raw rev pending outputs fuel bitsReverse ctx) := by
  cases d <;> apply congrArg some <;> apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem separator_step_nil (d : TreeSide) (rev : Word) (pending : List Unit)
    (regs : Registers R) (outputs : TreeSide → Word) (fuel bitsReverse : Bits)
    (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (treeResultLabel d .success)) regs [] rev pending outputs fuel bitsReverse ctx) =
      some (cfg (some (phaseLabel (toReversePhase d))) (reset regs) []
        rev pending outputs fuel bitsReverse ctx) := by
  cases d <;> apply congrArg some <;> apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem separator_step_foreign (d : TreeSide) (tag : Tag) (raw rev : Word)
    (pending : List Unit) (regs : Registers R) (outputs : TreeSide → Word)
    (fuel bitsReverse : Bits) (ctx : ∀ k, List (Γ k)) (different : tag ≠ separatorTag) :
    step caller (cfg (some (treeResultLabel d .success)) regs (tag :: raw)
        rev pending outputs fuel bitsReverse ctx) =
      some (cfg (some (phaseLabel (toReversePhase d))) (reset regs) (tag :: raw)
        rev pending outputs fuel bitsReverse ctx) := by
  cases d <;>
    simp only [step, TreeParserMachine.step, Turing.TM2.step, TreeParserMachine.program,
      handler, treeResultLabel, TreeParserMachine.resultLabel, separatorBlock,
      Turing.TM2.stepAux, rawStack, cfg, TreeParserMachine.cfg, TreeParserMachine.storeTag,
      List.head?_cons, jump, TreeParserMachine.jump, reset, TreeParserMachine.reset,
      phaseLabel, TreeParserMachine.callerLabel, toReversePhase]
  all_goals simp only [Bool.cond_decide, Option.some.injEq, different, ite_false]

theorem bitsScan_step_bit (b : Bool) (raw rev : Word) (pending : List Unit)
    (regs : Registers R) (outputs : TreeSide → Word) (fuel bitsReverse : Bits)
    (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel .bitsScan)) regs (bitTag b :: raw)
        rev pending outputs fuel bitsReverse ctx) =
      some (cfg (some (phaseLabel .bitsScan)) (reset regs) raw rev pending
        outputs fuel (b :: bitsReverse) ctx) := by
  cases b <;> apply congrArg some <;> apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem bitsScan_step_end (raw rev : Word) (pending : List Unit) (regs : Registers R)
    (outputs : TreeSide → Word) (fuel bitsReverse : Bits) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel .bitsScan)) regs (endInputTag :: raw)
        rev pending outputs fuel bitsReverse ctx) =
      some (cfg (some (phaseLabel .bitsEmit)) (reset regs) raw rev pending
        outputs fuel bitsReverse ctx) := by
  apply congrArg some
  apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem bitsScan_step_nil (rev : Word) (pending : List Unit) (regs : Registers R)
    (outputs : TreeSide → Word) (fuel bitsReverse : Bits) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel .bitsScan)) regs [] rev pending outputs fuel bitsReverse ctx) =
      some (cfg (some (phaseLabel .bitsUndo)) (reset regs) [] rev pending outputs fuel bitsReverse ctx) := by
  apply congrArg some
  apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem bitsScan_step_foreign (tag : Tag) (raw rev : Word) (pending : List Unit)
    (regs : Registers R) (outputs : TreeSide → Word) (fuel bitsReverse : Bits)
    (ctx : ∀ k, List (Γ k)) (notEnd : tag ≠ endInputTag)
    (notZero : tag ≠ bitZeroTag) (notOne : tag ≠ bitOneTag) :
    step caller (cfg (some (phaseLabel .bitsScan)) regs (tag :: raw)
        rev pending outputs fuel bitsReverse ctx) =
      some (cfg (some (phaseLabel .bitsUndo)) (reset regs) (tag :: raw)
        rev pending outputs fuel bitsReverse ctx) := by
  simp only [step, TreeParserMachine.step, Turing.TM2.step, TreeParserMachine.program,
    handler, phaseLabel, TreeParserMachine.callerLabel, block, Turing.TM2.stepAux,
    rawStack, cfg, TreeParserMachine.cfg, TreeParserMachine.storeTag, List.head?_cons,
    jump, TreeParserMachine.jump, reset, TreeParserMachine.reset]
  simp only [Bool.cond_decide, Option.some.injEq, notEnd, notZero, notOne, or_self, ite_false]

theorem bitsEmit_step_cons (b : Bool) (raw rev : Word) (pending : List Unit)
    (regs : Registers R) (outputs : TreeSide → Word) (fuel bitsReverse : Bits)
    (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel .bitsEmit)) regs raw rev pending
        outputs fuel (b :: bitsReverse) ctx) =
      some (cfg (some (phaseLabel .bitsEmit)) (reset regs) raw rev pending
        outputs (b :: fuel) bitsReverse ctx) := by
  cases b <;> apply congrArg some <;> apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem bitsEmit_step_nil (raw rev : Word) (pending : List Unit) (regs : Registers R)
    (outputs : TreeSide → Word) (fuel : Bits) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel .bitsEmit)) regs raw rev pending outputs fuel [] ctx) =
      some (cfg (some (phaseLabel .eof)) (reset regs) raw rev pending outputs fuel [] ctx) := by
  apply congrArg some
  apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem eof_step_nil (rev : Word) (pending : List Unit) (regs : Registers R)
    (outputs : TreeSide → Word) (fuel bitsReverse : Bits) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel .eof)) regs [] rev pending outputs fuel bitsReverse ctx) =
      some (cfg (some (resultLabel .success)) (reset regs) [] rev pending outputs fuel bitsReverse ctx) := by
  apply congrArg some
  apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem eof_step_cons (tag : Tag) (raw rev : Word) (pending : List Unit)
    (regs : Registers R) (outputs : TreeSide → Word) (fuel bitsReverse : Bits)
    (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel .eof)) regs (tag :: raw)
        rev pending outputs fuel bitsReverse ctx) =
      some (cfg (some (phaseLabel .restoreEnd)) (reset regs) (tag :: raw)
        rev pending outputs fuel bitsReverse ctx) := by
  apply congrArg some
  apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem restoreEnd_step (raw rev : Word) (pending : List Unit) (regs : Registers R)
    (outputs : TreeSide → Word) (fuel bitsReverse : Bits) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel .restoreEnd)) regs raw rev pending outputs fuel bitsReverse ctx) =
      some (cfg (some (phaseLabel .fuelUndo)) (reset regs) (endInputTag :: raw)
        rev pending outputs fuel bitsReverse ctx) := by
  apply congrArg some
  apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem fuelUndo_step_cons (b : Bool) (raw rev : Word) (pending : List Unit)
    (regs : Registers R) (outputs : TreeSide → Word) (fuel bitsReverse : Bits)
    (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel .fuelUndo)) regs raw rev pending
        outputs (b :: fuel) bitsReverse ctx) =
      some (cfg (some (phaseLabel .fuelUndo)) (reset regs) raw rev pending
        outputs fuel (b :: bitsReverse) ctx) := by
  cases b <;> apply congrArg some <;> apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem fuelUndo_step_nil (raw rev : Word) (pending : List Unit) (regs : Registers R)
    (outputs : TreeSide → Word) (bitsReverse : Bits) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel .fuelUndo)) regs raw rev pending outputs [] bitsReverse ctx) =
      some (cfg (some (phaseLabel .bitsUndo)) (reset regs) raw rev pending outputs [] bitsReverse ctx) := by
  apply congrArg some
  apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem bitsUndo_step_cons (b : Bool) (raw rev : Word) (pending : List Unit)
    (regs : Registers R) (outputs : TreeSide → Word) (fuel bitsReverse : Bits)
    (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel .bitsUndo)) regs raw rev pending
        outputs fuel (b :: bitsReverse) ctx) =
      some (cfg (some (phaseLabel .bitsUndo)) (reset regs) (bitTag b :: raw)
        rev pending outputs fuel bitsReverse ctx) := by
  apply congrArg some
  apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem bitsUndo_step_nil (raw rev : Word) (pending : List Unit) (regs : Registers R)
    (outputs : TreeSide → Word) (fuel : Bits) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel .bitsUndo)) regs raw rev pending outputs fuel [] ctx) =
      some (cfg (some (phaseLabel .restoreSep2)) (reset regs) raw rev pending outputs fuel [] ctx) := by
  apply congrArg some
  apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem restoreSep2_step (raw rev : Word) (pending : List Unit) (regs : Registers R)
    (outputs : TreeSide → Word) (fuel bitsReverse : Bits) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel .restoreSep2)) regs raw rev pending outputs fuel bitsReverse ctx) =
      some (cfg (some (phaseLabel .targetToReverse)) (reset regs) (separatorTag :: raw)
        rev pending outputs fuel bitsReverse ctx) := by
  apply congrArg some
  apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem restoreSep1_step (raw rev : Word) (pending : List Unit) (regs : Registers R)
    (outputs : TreeSide → Word) (fuel bitsReverse : Bits) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel .restoreSep1)) regs raw rev pending outputs fuel bitsReverse ctx) =
      some (cfg (some (phaseLabel .sourceToReverse)) (reset regs) (separatorTag :: raw)
        rev pending outputs fuel bitsReverse ctx) := by
  apply congrArg some
  apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem target_failure_step (raw rev : Word) (pending : List Unit) (regs : Registers R)
    (outputs : TreeSide → Word) (fuel bitsReverse : Bits) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (treeResultLabel .target .failure)) regs raw
        rev pending outputs fuel bitsReverse ctx) =
      some (cfg (some (phaseLabel .sourceToReverse)) (reset regs) (separatorTag :: raw)
        rev pending outputs fuel bitsReverse ctx) := by
  apply congrArg some
  apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem toReversePhase_step_cons (d : TreeSide) (tag : Tag) (raw rev remaining : Word)
    (pending : List Unit) (regs : Registers R) (outputs : TreeSide → Word)
    (fuel bitsReverse : Bits) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel (toReversePhase d))) regs raw rev pending
        (Function.update outputs d (tag :: remaining)) fuel bitsReverse ctx) =
      some (cfg (some (phaseLabel (toReversePhase d))) (reset regs) raw (tag :: rev) pending
        (Function.update outputs d remaining) fuel bitsReverse ctx) := by
  cases d <;> apply congrArg some <;> apply cfg_ext <;>
    first | rfl | exact fun _ => rfl | intro side; cases side <;> rfl

theorem toReversePhase_step_nil (d : TreeSide) (raw rev : Word) (pending : List Unit)
    (regs : Registers R) (outputs : TreeSide → Word) (fuel bitsReverse : Bits)
    (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel (toReversePhase d))) regs raw rev pending
        (Function.update outputs d []) fuel bitsReverse ctx) =
      some (cfg (some (phaseLabel (toRawPhase d))) (reset regs) raw rev pending
        (Function.update outputs d []) fuel bitsReverse ctx) := by
  cases d <;> apply congrArg some <;> apply cfg_ext <;>
    first | rfl | exact fun _ => rfl | intro side; cases side <;> rfl

theorem toRawPhase_step_cons (d : TreeSide) (tag : Tag) (raw rev : Word) (pending : List Unit)
    (regs : Registers R) (outputs : TreeSide → Word) (fuel bitsReverse : Bits)
    (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel (toRawPhase d))) regs raw (tag :: rev)
        pending outputs fuel bitsReverse ctx) =
      some (cfg (some (phaseLabel (toRawPhase d))) (reset regs) (tag :: raw) rev
        pending outputs fuel bitsReverse ctx) := by
  cases d <;> apply congrArg some <;> apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem toRawPhase_step_nil (d : TreeSide) (raw : Word) (pending : List Unit)
    (regs : Registers R) (outputs : TreeSide → Word) (fuel bitsReverse : Bits)
    (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel (toRawPhase d))) regs raw []
        pending outputs fuel bitsReverse ctx) =
      some (cfg (some (afterRollback d)) (reset regs) raw []
        pending outputs fuel bitsReverse ctx) := by
  cases d <;> apply congrArg some <;> apply cfg_ext <;> first | rfl | exact fun _ => rfl


theorem next_iterate_none (n : Nat) : (next caller)^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, next_none, ih]

theorem runs_of_prefix (n : Nat) (start final : Cfg Γ Λ R)
    (executed : (next caller)^[n] (some start) = some final)
    (owned : ∀ j < n, ∃ reached,
      (next caller)^[j] (some start) = some reached ∧ FullOwned reached.l) :
    Runs caller n start final := by
  induction n generalizing start with
  | zero =>
      have equal : start = final := Option.some.inj executed
      subst final
      exact .refl start
  | succ n ih =>
      have startOwned : FullOwned start.l := by
        obtain ⟨reached, prefixEq, isOwned⟩ := owned 0 (by omega)
        have equal : start = reached := Option.some.inj prefixEq
        rw [equal]
        exact isOwned
      cases transition : step caller start with
      | none =>
          rw [Function.iterate_succ_apply, next_some, transition, next_iterate_none] at executed
          cases executed
      | some middle =>
          apply Runs.cons startOwned transition
          apply ih middle
          · rwa [iterate_step caller n start middle transition] at executed
          · intro j bound
            obtain ⟨reached, prefixEq, isOwned⟩ := owned (j + 1) (by omega)
            rw [iterate_step caller j start middle transition] at prefixEq
            exact ⟨reached, prefixEq, isOwned⟩

/-- The reused tree endpoint and every earlier tree prefix run in this same program. -/
theorem tree_phase_run (d : TreeSide) (phase : TreeParserMachine.Phase) (raw rev : Word)
    (pending : List Unit) (regs : Registers R) (outputs : TreeSide → Word)
    (fuel bitsReverse : Bits) (ctx : ∀ k, List (Γ k)) (final : Cfg Γ Λ R)
    (executed : (next caller)^[TreeParserMachine.phaseSteps phase raw rev pending]
      (some (cfg (some (treeLabel d phase)) regs raw rev pending outputs fuel bitsReverse ctx)) =
        some final) :
    Runs caller (TreeParserMachine.phaseSteps phase raw rev pending)
      (cfg (some (treeLabel d phase)) regs raw rev pending outputs fuel bitsReverse ctx) final := by
  apply runs_of_prefix caller _ _ _ executed
  intro j bound
  obtain ⟨reached, prefixEq, _, _, owned, _⟩ := TreeParserMachine.phase_prefix
    (handler caller) d phase raw rev pending regs outputs (stores fuel bitsReverse ctx) j (by omega)
  exact ⟨reached, prefixEq, fullOwned_of_treeParserMachineOwned reached.l (owned.mp bound)⟩

theorem tree_run_source (d : TreeSide) (raw : Word) (regs : Registers R)
    (outputs : TreeSide → Word) (fuel bitsReverse : Bits) (ctx : ∀ k, List (Γ k)) :
    Runs caller (TreeParserMachine.runSteps raw)
      (cfg (some (treeLabel d .init)) regs raw [] [] outputs fuel bitsReverse ctx)
      (TreeParserMachine.resultCfg d regs raw outputs (stores fuel bitsReverse ctx)
        (parseTreeRun raw).1) := by
  exact tree_phase_run caller d .init raw [] [] regs outputs fuel bitsReverse ctx _
    (TreeParserMachine.run_source (handler caller) d raw regs outputs (stores fuel bitsReverse ctx))

theorem tree_run_of_some (d : TreeSide) (raw : Word) (t : BinaryTree Unit) (rest : Word)
    (regs : Registers R) (outputs : TreeSide → Word) (fuel bitsReverse : Bits)
    (ctx : ∀ k, List (Γ k)) (returned : (parseTreeRun raw).1 = some (t, rest)) :
    Runs caller (TreeParserMachine.runSteps raw)
      (cfg (some (treeLabel d .init)) regs raw [] [] outputs fuel bitsReverse ctx)
      (cfg (some (treeResultLabel d .success)) (reset regs) rest [] []
        (Function.update outputs d (treeCode t ++ outputs d)) fuel bitsReverse ctx) := by
  simpa only [returned, TreeParserMachine.resultCfg, cfg, treeResultLabel, reset] using
    tree_run_source caller d raw regs outputs fuel bitsReverse ctx

theorem tree_run_of_none (d : TreeSide) (raw : Word) (regs : Registers R)
    (outputs : TreeSide → Word) (fuel bitsReverse : Bits) (ctx : ∀ k, List (Γ k))
    (returned : (parseTreeRun raw).1 = none) :
    Runs caller (TreeParserMachine.runSteps raw)
      (cfg (some (treeLabel d .init)) regs raw [] [] outputs fuel bitsReverse ctx)
      (cfg (some (treeResultLabel d .failure)) (reset regs) raw [] [] outputs fuel bitsReverse ctx) := by
  simpa only [returned, TreeParserMachine.resultCfg, cfg, treeResultLabel, reset] using
    tree_run_source caller d raw regs outputs fuel bitsReverse ctx

theorem tree_run_code (d : TreeSide) (t : BinaryTree Unit) (rest : Word)
    (regs : Registers R) (outputs : TreeSide → Word) (fuel bitsReverse : Bits)
    (ctx : ∀ k, List (Γ k)) :
    Runs caller (2 * (treeCode t).length + 2)
      (cfg (some (treeLabel d .init)) regs (treeCode t ++ rest) [] [] outputs fuel bitsReverse ctx)
      (cfg (some (treeResultLabel d .success)) (reset regs) rest [] []
        (Function.update outputs d (treeCode t ++ outputs d)) fuel bitsReverse ctx) := by
  simpa only [TreeParserMachine.runSteps_code] using
    tree_run_of_some caller d (treeCode t ++ rest) t rest regs outputs fuel bitsReverse ctx
      (congrArg Prod.fst (parseTreeRun_code t rest))

theorem bitTags_append (bs cs : Bits) : bitTags (bs ++ cs) = bitTags bs ++ bitTags cs :=
  List.map_append

@[simp] theorem treeOutputs_update_source (source target newSource : Word) :
    Function.update (treeOutputs source target) .source newSource = treeOutputs newSource target := by
  funext d
  cases d <;> rfl

@[simp] theorem treeOutputs_update_target (source target newTarget : Word) :
    Function.update (treeOutputs source target) .target newTarget = treeOutputs source newTarget := by
  funext d
  cases d <;> rfl

theorem bitsEmit_run (raw rev : Word) (pending : List Unit) (regs : Registers R)
    (outputs : TreeSide → Word) (fuel bitsReverse : Bits) (ctx : ∀ k, List (Γ k)) :
    Runs caller (bitsReverse.length + 1)
      (cfg (some (phaseLabel .bitsEmit)) regs raw rev pending outputs fuel bitsReverse ctx)
      (cfg (some (phaseLabel .eof)) (reset regs) raw rev pending
        outputs (bitsReverse.reverse ++ fuel) [] ctx) := by
  induction bitsReverse generalizing fuel regs with
  | nil => exact Runs.one caller (fullOwned_phase _) (bitsEmit_step_nil caller raw rev pending regs outputs fuel ctx)
  | cons b bs ih =>
      have tailRun := ih (fuel := b :: fuel) (regs := reset regs)
      have run := Runs.cons (fullOwned_phase _) (bitsEmit_step_cons caller b raw rev pending regs outputs fuel bs ctx) tailRun
      simpa only [List.length_cons, TreeParserMachine.reset_reset, List.reverse_cons,
        List.append_assoc, List.singleton_append] using run

theorem fuelUndo_run (raw rev : Word) (pending : List Unit) (regs : Registers R)
    (outputs : TreeSide → Word) (fuel bitsReverse : Bits) (ctx : ∀ k, List (Γ k)) :
    Runs caller (fuel.length + 1)
      (cfg (some (phaseLabel .fuelUndo)) regs raw rev pending outputs fuel bitsReverse ctx)
      (cfg (some (phaseLabel .bitsUndo)) (reset regs) raw rev pending
        outputs [] (fuel.reverse ++ bitsReverse) ctx) := by
  induction fuel generalizing bitsReverse regs with
  | nil => exact Runs.one caller (fullOwned_phase _) (fuelUndo_step_nil caller raw rev pending regs outputs bitsReverse ctx)
  | cons b bs ih =>
      have tailRun := ih (bitsReverse := b :: bitsReverse) (regs := reset regs)
      have run := Runs.cons (fullOwned_phase _) (fuelUndo_step_cons caller b raw rev pending regs outputs bs bitsReverse ctx) tailRun
      simpa only [List.length_cons, TreeParserMachine.reset_reset, List.reverse_cons,
        List.append_assoc, List.singleton_append] using run

theorem bitsUndo_run (raw rev : Word) (pending : List Unit) (regs : Registers R)
    (outputs : TreeSide → Word) (fuel bitsReverse : Bits) (ctx : ∀ k, List (Γ k)) :
    Runs caller (bitsReverse.length + 1)
      (cfg (some (phaseLabel .bitsUndo)) regs raw rev pending outputs fuel bitsReverse ctx)
      (cfg (some (phaseLabel .restoreSep2)) (reset regs) (bitTags bitsReverse.reverse ++ raw)
        rev pending outputs fuel [] ctx) := by
  induction bitsReverse generalizing raw regs with
  | nil => exact Runs.one caller (fullOwned_phase _) (bitsUndo_step_nil caller raw rev pending regs outputs fuel ctx)
  | cons b bs ih =>
      have tailRun := ih (raw := bitTag b :: raw) (regs := reset regs)
      have run := Runs.cons (fullOwned_phase _) (bitsUndo_step_cons caller b raw rev pending regs outputs fuel bs ctx) tailRun
      simpa only [List.length_cons, TreeParserMachine.reset_reset, List.reverse_cons,
        bitTags_append, bitTags_cons, bitTags_nil, List.append_assoc, List.singleton_append] using run

theorem fuel_bits_undo_run (raw rev : Word) (pending : List Unit) (regs : Registers R)
    (outputs : TreeSide → Word) (fuel bitsReverse : Bits) (ctx : ∀ k, List (Γ k)) :
    Runs caller (2 * fuel.length + bitsReverse.length + 2)
      (cfg (some (phaseLabel .fuelUndo)) regs raw rev pending outputs fuel bitsReverse ctx)
      (cfg (some (phaseLabel .restoreSep2)) (reset regs)
        (bitTags (bitsReverse.reverse ++ fuel) ++ raw) rev pending outputs [] [] ctx) := by
  have combined := (fuelUndo_run caller raw rev pending regs outputs fuel bitsReverse ctx).trans caller
    (bitsUndo_run caller raw rev pending (reset regs) outputs [] (fuel.reverse ++ bitsReverse) ctx)
  have count : fuel.length + 1 + ((fuel.reverse ++ bitsReverse).length + 1) =
      2 * fuel.length + bitsReverse.length + 2 := by
    simp only [List.length_append, List.length_reverse]
    omega
  rw [count] at combined
  simpa only [TreeParserMachine.reset_reset, List.reverse_append, List.reverse_reverse] using combined

theorem toReversePhase_run (d : TreeSide) (word raw rev : Word) (pending : List Unit)
    (regs : Registers R) (outputs : TreeSide → Word) (fuel bitsReverse : Bits)
    (ctx : ∀ k, List (Γ k)) :
    Runs caller (word.length + 1)
      (cfg (some (phaseLabel (toReversePhase d))) regs raw rev pending
        (Function.update outputs d word) fuel bitsReverse ctx)
      (cfg (some (phaseLabel (toRawPhase d))) (reset regs) raw (word.reverse ++ rev) pending
        (Function.update outputs d []) fuel bitsReverse ctx) := by
  induction word generalizing rev regs with
  | nil => exact Runs.one caller (fullOwned_phase _) (toReversePhase_step_nil caller d raw rev pending regs outputs fuel bitsReverse ctx)
  | cons tag word ih =>
      have tailRun := ih (rev := tag :: rev) (regs := reset regs)
      have run := Runs.cons (fullOwned_phase _)
        (toReversePhase_step_cons caller d tag raw rev word pending regs outputs fuel bitsReverse ctx) tailRun
      simpa only [List.length_cons, TreeParserMachine.reset_reset, List.reverse_cons,
        List.append_assoc, List.singleton_append] using run

theorem toRawPhase_run (d : TreeSide) (raw rev : Word) (pending : List Unit)
    (regs : Registers R) (outputs : TreeSide → Word) (fuel bitsReverse : Bits)
    (ctx : ∀ k, List (Γ k)) :
    Runs caller (rev.length + 1)
      (cfg (some (phaseLabel (toRawPhase d))) regs raw rev pending outputs fuel bitsReverse ctx)
      (cfg (some (afterRollback d)) (reset regs) (rev.reverse ++ raw) [] pending outputs fuel bitsReverse ctx) := by
  induction rev generalizing raw regs with
  | nil => exact Runs.one caller (fullOwned_phase _) (toRawPhase_step_nil caller d raw pending regs outputs fuel bitsReverse ctx)
  | cons tag rev ih =>
      have tailRun := ih (raw := tag :: raw) (regs := reset regs)
      have run := Runs.cons (fullOwned_phase _)
        (toRawPhase_step_cons caller d tag raw rev pending regs outputs fuel bitsReverse ctx) tailRun
      simpa only [List.length_cons, TreeParserMachine.reset_reset, List.reverse_cons,
        List.append_assoc, List.singleton_append] using run

theorem rollback_run (d : TreeSide) (word raw rev : Word) (pending : List Unit)
    (regs : Registers R) (outputs : TreeSide → Word) (fuel bitsReverse : Bits)
    (ctx : ∀ k, List (Γ k)) :
    Runs caller (2 * word.length + rev.length + 2)
      (cfg (some (phaseLabel (toReversePhase d))) regs raw rev pending
        (Function.update outputs d word) fuel bitsReverse ctx)
      (cfg (some (afterRollback d)) (reset regs) (rev.reverse ++ word ++ raw) [] pending
        (Function.update outputs d []) fuel bitsReverse ctx) := by
  have combined := (toReversePhase_run caller d word raw rev pending regs outputs fuel bitsReverse ctx).trans caller
    (toRawPhase_run caller d raw (word.reverse ++ rev) pending (reset regs)
      (Function.update outputs d []) fuel bitsReverse ctx)
  have count : word.length + 1 + ((word.reverse ++ rev).length + 1) =
      2 * word.length + rev.length + 2 := by
    simp only [List.length_append, List.length_reverse]
    omega
  rw [count] at combined
  simpa only [TreeParserMachine.reset_reset, List.reverse_append, List.reverse_reverse] using combined

omit [DecidableEq K] in
def entry (regs : Registers R) (raw : Word) (ctx : ∀ k, List (Γ k)) : Cfg Γ Λ R :=
  cfg (some (treeLabel .source .init)) regs raw [] [] (treeOutputs [] []) [] [] ctx

omit [DecidableEq K] in
def resultCfg (regs : Registers R) (original : Word) (ctx : ∀ k, List (Γ k)) :
    Option ParsedInput → Cfg Γ Λ R
  | none => cfg (some (resultLabel .failure)) (reset regs) original [] [] (treeOutputs [] []) [] [] ctx
  | some (source, target, bs) => cfg (some (resultLabel .success)) (reset regs) [] [] []
      (treeOutputs (treeCode source) (treeCode target)) bs [] ctx

/-- Proof-side length of the accepted bit prefix; absent from all finite callbacks. -/
def bitsConsumed : Word → Nat
  | [] => 0
  | tag :: raw => if tag = bitZeroTag ∨ tag = bitOneTag then 1 + bitsConsumed raw else 0

@[simp] theorem bitsConsumed_nil : bitsConsumed [] = 0 := rfl

theorem bitsConsumed_bit (b : Bool) (raw : Word) :
    bitsConsumed (bitTag b :: raw) = 1 + bitsConsumed raw := by cases b <;> rfl

@[simp] theorem bitsConsumed_end (raw : Word) : bitsConsumed (endInputTag :: raw) = 0 := rfl

theorem bitsConsumed_bits (bs : Bits) (raw : Word) :
    bitsConsumed (bitTags bs ++ raw) = bs.length + bitsConsumed raw := by
  induction bs with
  | nil => simp only [bitTags_nil, List.nil_append, List.length_nil, Nat.zero_add]
  | cons b bs ih =>
      simp only [bitTags_cons, List.cons_append, bitsConsumed_bit, ih, List.length_cons]
      omega

theorem bitsConsumed_le (raw : Word) : bitsConsumed raw ≤ raw.length := by
  induction raw with
  | nil => exact le_rfl
  | cons tag raw ih =>
      simp only [bitsConsumed, List.length_cons]
      split <;> omega

def BitsBlocked : Word → Prop
  | [] => True
  | tag :: _ => tag ≠ endInputTag ∧ tag ≠ bitZeroTag ∧ tag ≠ bitOneTag

theorem bitsConsumed_blocked (raw : Word) (blocked : BitsBlocked raw) : bitsConsumed raw = 0 := by
  cases raw with
  | nil => rfl
  | cons tag raw =>
      simp only [bitsConsumed, blocked.2.1, blocked.2.2, or_self, ite_false]

theorem bitsConsumed_of_blocked (bs : Bits) (rest : Word) (blocked : BitsBlocked rest) :
    bitsConsumed (bitTags bs ++ rest) = bs.length := by
  rw [bitsConsumed_bits, bitsConsumed_blocked rest blocked, Nat.add_zero]

theorem bitsConsumed_of_some (raw : Word) (bs : Bits) (rest : Word)
    (returned : (parseBitsRun raw).1 = some (bs, rest)) : bitsConsumed raw = bs.length := by
  rw [(parseBitsRun_iff raw bs rest).mp returned, List.append_assoc,
    List.singleton_append, bitsConsumed_bits, bitsConsumed_end, Nat.add_zero]

theorem parseBitsRun_bit_none_iff (b : Bool) (raw : Word) :
    (parseBitsRun (bitTag b :: raw)).1 = none ↔ (parseBitsRun raw).1 = none := by
  rw [parseBitsRun_bit]
  simp only [Resources.bind]
  cases observed : (parseBitsRun raw).1 with
  | none => rfl
  | some pair => rcases pair with ⟨bs, rest⟩; simp only [reduceCtorEq]

theorem parseBitsRun_none_decomposition (raw : Word) (returned : (parseBitsRun raw).1 = none) :
    ∃ bs rest, raw = bitTags bs ++ rest ∧ BitsBlocked rest := by
  induction raw with
  | nil => exact ⟨[], [], rfl, True.intro⟩
  | cons tag raw ih =>
      by_cases ended : tag = endInputTag
      · subst tag
        rw [parseBitsRun_end] at returned
        cases returned
      · by_cases zero : tag = bitZeroTag
        · subst tag
          obtain ⟨bs, rest, word, blocked⟩ := ih ((parseBitsRun_bit_none_iff false raw).mp returned)
          refine ⟨false :: bs, rest, ?_, blocked⟩
          change bitTag false :: raw = bitTag false :: (bitTags bs ++ rest)
          rw [word]
        · by_cases one : tag = bitOneTag
          · subst tag
            obtain ⟨bs, rest, word, blocked⟩ := ih ((parseBitsRun_bit_none_iff true raw).mp returned)
            refine ⟨true :: bs, rest, ?_, blocked⟩
            change bitTag true :: raw = bitTag true :: (bitTags bs ++ rest)
            rw [word]
          · exact ⟨[], tag :: raw, rfl, ended, zero, one⟩

theorem parseBitsRun_none_of_blocked (bs : Bits) (rest : Word) (blocked : BitsBlocked rest) :
    (parseBitsRun (bitTags bs ++ rest)).1 = none := by
  induction bs with
  | nil =>
      cases rest with
      | nil => rfl
      | cons tag rest =>
          exact congrArg Prod.fst (parseBitsRun_foreign tag rest blocked.1 blocked.2.1 blocked.2.2)
  | cons b bs ih => exact (parseBitsRun_bit_none_iff b _).mpr ih

theorem parseBitsRun_none_iff_blocked (raw : Word) :
    (parseBitsRun raw).1 = none ↔ ∃ bs rest, raw = bitTags bs ++ rest ∧ BitsBlocked rest := by
  constructor
  · exact parseBitsRun_none_decomposition raw
  · rintro ⟨bs, rest, rfl, blocked⟩
    exact parseBitsRun_none_of_blocked bs rest blocked

omit [DecidableEq K] in
theorem reset_cond (regs : Registers R) (condition : Prop) [Decidable condition] :
    reset (if condition then regs else reset regs) = reset regs := by split <;> rfl

/-- Every accepted bit is scanned once and retained in its physical reverse orientation. -/
theorem bitsScan_prefix_run (bs : Bits) (raw rev : Word) (pending : List Unit)
    (regs : Registers R) (outputs : TreeSide → Word) (fuel bitsReverse : Bits)
    (ctx : ∀ k, List (Γ k)) :
    Runs caller bs.length
      (cfg (some (phaseLabel .bitsScan)) regs (bitTags bs ++ raw)
        rev pending outputs fuel bitsReverse ctx)
      (cfg (some (phaseLabel .bitsScan)) (if bs = [] then regs else reset regs) raw
        rev pending outputs fuel (bs.reverse ++ bitsReverse) ctx) := by
  induction bs generalizing regs bitsReverse with
  | nil => exact .refl _
  | cons b bs ih =>
      have tailRun := ih (regs := reset regs) (bitsReverse := b :: bitsReverse)
      have run := Runs.cons (fullOwned_phase _)
        (bitsScan_step_bit caller b (bitTags bs ++ raw) rev pending regs outputs fuel bitsReverse ctx) tailRun
      simpa only [bitTags_cons, List.cons_append, List.length_cons, List.cons_ne_nil,
        ite_false, TreeParserMachine.reset_reset, ite_self, List.reverse_cons,
        List.append_assoc, List.singleton_append, List.nil_append] using run

theorem bitsScan_terminated_run (bs : Bits) (raw rev : Word) (pending : List Unit)
    (regs : Registers R) (outputs : TreeSide → Word) (fuel bitsReverse : Bits)
    (ctx : ∀ k, List (Γ k)) :
    Runs caller (bs.length + 1)
      (cfg (some (phaseLabel .bitsScan)) regs (bitTags bs ++ endInputTag :: raw)
        rev pending outputs fuel bitsReverse ctx)
      (cfg (some (phaseLabel .bitsEmit)) (reset regs) raw rev pending
        outputs fuel (bs.reverse ++ bitsReverse) ctx) := by
  have combined := (bitsScan_prefix_run caller bs (endInputTag :: raw) rev pending regs
    outputs fuel bitsReverse ctx).trans caller
      (Runs.one caller (fullOwned_phase _)
        (bitsScan_step_end caller raw rev pending (if bs = [] then regs else reset regs)
          outputs fuel (bs.reverse ++ bitsReverse) ctx))
  simpa only [reset_cond] using combined

theorem bitsScan_blocked_step (raw rev : Word) (pending : List Unit) (regs : Registers R)
    (outputs : TreeSide → Word) (fuel bitsReverse : Bits) (ctx : ∀ k, List (Γ k))
    (blocked : BitsBlocked raw) :
    step caller (cfg (some (phaseLabel .bitsScan)) regs raw rev pending outputs fuel bitsReverse ctx) =
      some (cfg (some (phaseLabel .bitsUndo)) (reset regs) raw rev pending outputs fuel bitsReverse ctx) := by
  cases raw with
  | nil => exact bitsScan_step_nil caller rev pending regs outputs fuel bitsReverse ctx
  | cons tag raw =>
      exact bitsScan_step_foreign caller tag raw rev pending regs outputs fuel bitsReverse ctx
        blocked.1 blocked.2.1 blocked.2.2

theorem bitsScan_blocked_run (bs : Bits) (raw rev : Word) (pending : List Unit)
    (regs : Registers R) (outputs : TreeSide → Word) (fuel bitsReverse : Bits)
    (ctx : ∀ k, List (Γ k)) (blocked : BitsBlocked raw) :
    Runs caller (bs.length + 1)
      (cfg (some (phaseLabel .bitsScan)) regs (bitTags bs ++ raw)
        rev pending outputs fuel bitsReverse ctx)
      (cfg (some (phaseLabel .bitsUndo)) (reset regs) raw rev pending
        outputs fuel (bs.reverse ++ bitsReverse) ctx) := by
  have combined := (bitsScan_prefix_run caller bs raw rev pending regs outputs fuel bitsReverse ctx).trans caller
    (Runs.one caller (fullOwned_phase _)
      (bitsScan_blocked_step caller raw rev pending (if bs = [] then regs else reset regs)
        outputs fuel (bs.reverse ++ bitsReverse) ctx blocked))
  simpa only [reset_cond] using combined


@[simp] theorem treeOutputs_source (source target : Word) :
    treeOutputs source target .source = source := rfl

@[simp] theorem treeOutputs_target (source target : Word) :
    treeOutputs source target .target = target := rfl

theorem source_rollback_run (word raw : Word) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    Runs caller (2 * word.length + 2)
      (cfg (some (phaseLabel .sourceToReverse)) regs raw [] [] (treeOutputs word []) [] [] ctx)
      (cfg (some (resultLabel .failure)) (reset regs) (word ++ raw) [] [] (treeOutputs [] []) [] [] ctx) := by
  simpa only [treeOutputs_update_source, toReversePhase, afterRollback,
    List.length_nil, Nat.add_zero, List.reverse_nil, List.nil_append] using
      rollback_run caller .source word raw [] [] regs (treeOutputs [] []) [] [] ctx

theorem restore_source_run (word raw : Word) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    Runs caller (2 * word.length + 3)
      (cfg (some (phaseLabel .restoreSep1)) regs raw [] [] (treeOutputs word []) [] [] ctx)
      (cfg (some (resultLabel .failure)) (reset regs) (word ++ separatorTag :: raw)
        [] [] (treeOutputs [] []) [] [] ctx) := by
  have combined := (Runs.one caller (fullOwned_phase _)
    (restoreSep1_step caller raw [] [] regs (treeOutputs word []) [] [] ctx)).trans caller
      (source_rollback_run caller word (separatorTag :: raw) (reset regs) ctx)
  have count : 1 + (2 * word.length + 2) = 2 * word.length + 3 := by omega
  rw [count] at combined
  simpa only [TreeParserMachine.reset_reset] using combined

theorem target_failure_run (word raw : Word) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    Runs caller (2 * word.length + 3)
      (cfg (some (treeResultLabel .target .failure)) regs raw [] [] (treeOutputs word []) [] [] ctx)
      (cfg (some (resultLabel .failure)) (reset regs) (word ++ separatorTag :: raw)
        [] [] (treeOutputs [] []) [] [] ctx) := by
  have combined := (Runs.one caller (by trivial)
    (target_failure_step caller raw [] [] regs (treeOutputs word []) [] [] ctx)).trans caller
      (source_rollback_run caller word (separatorTag :: raw) (reset regs) ctx)
  have count : 1 + (2 * word.length + 2) = 2 * word.length + 3 := by omega
  rw [count] at combined
  simpa only [TreeParserMachine.reset_reset] using combined

theorem target_rollback_run (source target raw : Word) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    Runs caller (2 * source.length + 2 * target.length + 5)
      (cfg (some (phaseLabel .targetToReverse)) regs raw [] [] (treeOutputs source target) [] [] ctx)
      (cfg (some (resultLabel .failure)) (reset regs) (source ++ separatorTag :: (target ++ raw))
        [] [] (treeOutputs [] []) [] [] ctx) := by
  have first : Runs caller (2 * target.length + 2)
      (cfg (some (phaseLabel .targetToReverse)) regs raw [] [] (treeOutputs source target) [] [] ctx)
      (cfg (some (phaseLabel .restoreSep1)) (reset regs) (target ++ raw) [] [] (treeOutputs source []) [] [] ctx) := by
    simpa only [treeOutputs_update_target, toReversePhase, afterRollback,
      List.length_nil, Nat.add_zero, List.reverse_nil, List.nil_append] using
        rollback_run caller .target target raw [] [] regs (treeOutputs source []) [] [] ctx
  have combined := first.trans caller (restore_source_run caller source (target ++ raw) (reset regs) ctx)
  have count : 2 * target.length + 2 + (2 * source.length + 3) =
      2 * source.length + 2 * target.length + 5 := by omega
  rw [count] at combined
  simpa only [TreeParserMachine.reset_reset] using combined

theorem restore_target_run (source target raw : Word) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    Runs caller (2 * source.length + 2 * target.length + 6)
      (cfg (some (phaseLabel .restoreSep2)) regs raw [] [] (treeOutputs source target) [] [] ctx)
      (cfg (some (resultLabel .failure)) (reset regs)
        (source ++ separatorTag :: (target ++ separatorTag :: raw)) [] [] (treeOutputs [] []) [] [] ctx) := by
  have combined := (Runs.one caller (fullOwned_phase _)
    (restoreSep2_step caller raw [] [] regs (treeOutputs source target) [] [] ctx)).trans caller
      (target_rollback_run caller source target (separatorTag :: raw) (reset regs) ctx)
  have count : 1 + (2 * source.length + 2 * target.length + 5) =
      2 * source.length + 2 * target.length + 6 := by omega
  rw [count] at combined
  simpa only [TreeParserMachine.reset_reset] using combined

theorem source_separator_run (source : BinaryTree Unit) (raw : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    Runs caller (2 * (treeCode source).length + 3)
      (entry regs (treeCode source ++ separatorTag :: raw) ctx)
      (cfg (some (treeLabel .target .init)) (reset regs) raw [] []
        (treeOutputs (treeCode source) []) [] [] ctx) := by
  have first : Runs caller (2 * (treeCode source).length + 2)
      (entry regs (treeCode source ++ separatorTag :: raw) ctx)
      (cfg (some (treeResultLabel .source .success)) (reset regs) (separatorTag :: raw)
        [] [] (treeOutputs (treeCode source) []) [] [] ctx) := by
    simpa only [entry, treeOutputs_source, List.append_nil, treeOutputs_update_source] using
      tree_run_code caller .source source (separatorTag :: raw) regs (treeOutputs [] []) [] [] ctx
  have combined := first.trans caller (Runs.one caller (by trivial)
    (separator_step_separator caller .source raw [] [] (reset regs)
      (treeOutputs (treeCode source) []) [] [] ctx))
  have count : 2 * (treeCode source).length + 2 + 1 = 2 * (treeCode source).length + 3 := by omega
  rw [count] at combined
  simpa only [afterSeparator, TreeParserMachine.reset_reset] using combined

theorem two_trees_run (source target : BinaryTree Unit) (raw : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    Runs caller (2 * (treeCode source).length + 2 * (treeCode target).length + 5)
      (entry regs (treeCode source ++ separatorTag :: (treeCode target ++ raw)) ctx)
      (cfg (some (treeResultLabel .target .success)) (reset regs) raw [] []
        (treeOutputs (treeCode source) (treeCode target)) [] [] ctx) := by
  have second : Runs caller (2 * (treeCode target).length + 2)
      (cfg (some (treeLabel .target .init)) (reset regs) (treeCode target ++ raw) [] []
        (treeOutputs (treeCode source) []) [] [] ctx)
      (cfg (some (treeResultLabel .target .success)) (reset regs) raw [] []
        (treeOutputs (treeCode source) (treeCode target)) [] [] ctx) := by
    simpa only [treeOutputs_target, List.append_nil, treeOutputs_update_target,
      TreeParserMachine.reset_reset] using
        tree_run_code caller .target target raw (reset regs) (treeOutputs (treeCode source) []) [] [] ctx
  have combined := (source_separator_run caller source (treeCode target ++ raw) regs ctx).trans caller second
  have count : 2 * (treeCode source).length + 3 + (2 * (treeCode target).length + 2) =
      2 * (treeCode source).length + 2 * (treeCode target).length + 5 := by omega
  rwa [count] at combined

theorem before_bits_run (source target : BinaryTree Unit) (raw : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    Runs caller (2 * (treeCode source).length + 2 * (treeCode target).length + 6)
      (entry regs (treeCode source ++ separatorTag :: (treeCode target ++ separatorTag :: raw)) ctx)
      (cfg (some (phaseLabel .bitsScan)) (reset regs) raw [] []
        (treeOutputs (treeCode source) (treeCode target)) [] [] ctx) := by
  have combined := (two_trees_run caller source target (separatorTag :: raw) regs ctx).trans caller
    (Runs.one caller (by trivial) (separator_step_separator caller .target raw [] [] (reset regs)
      (treeOutputs (treeCode source) (treeCode target)) [] [] ctx))
  have count : 2 * (treeCode source).length + 2 * (treeCode target).length + 5 + 1 =
      2 * (treeCode source).length + 2 * (treeCode target).length + 6 := by omega
  rw [count] at combined
  simpa only [afterSeparator, TreeParserMachine.reset_reset] using combined


theorem separator_failure_step (d : TreeSide) (raw rev : Word) (pending : List Unit)
    (regs : Registers R) (outputs : TreeSide → Word) (fuel bitsReverse : Bits)
    (ctx : ∀ k, List (Γ k)) (returned : (parseSeparatorRun raw).1 = none) :
    step caller (cfg (some (treeResultLabel d .success)) regs raw rev pending outputs fuel bitsReverse ctx) =
      some (cfg (some (phaseLabel (toReversePhase d))) (reset regs) raw rev pending outputs fuel bitsReverse ctx) := by
  cases raw with
  | nil => exact separator_step_nil caller d rev pending regs outputs fuel bitsReverse ctx
  | cons tag raw =>
      by_cases same : tag = separatorTag
      · subst tag
        rw [parseSeparatorRun_separator] at returned
        cases returned
      · exact separator_step_foreign caller d tag raw rev pending regs outputs fuel bitsReverse ctx same

theorem run_tree_failure_trace (raw : Word) (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (returned : (parseTreeRun raw).1 = none) :
    Runs caller (TreeParserMachine.runSteps raw) (entry regs raw ctx) (resultCfg regs raw ctx none) := by
  simpa only [entry, resultCfg, resultLabel, treeResultLabel] using
    tree_run_of_none caller .source raw regs (treeOutputs [] []) [] [] ctx returned

theorem run_first_separator_failure_trace (source : BinaryTree Unit) (raw : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) (returned : (parseSeparatorRun raw).1 = none) :
    Runs caller (4 * (treeCode source).length + 5)
      (entry regs (treeCode source ++ raw) ctx)
      (resultCfg regs (treeCode source ++ raw) ctx none) := by
  have first : Runs caller (2 * (treeCode source).length + 2)
      (entry regs (treeCode source ++ raw) ctx)
      (cfg (some (treeResultLabel .source .success)) (reset regs) raw [] []
        (treeOutputs (treeCode source) []) [] [] ctx) := by
    simpa only [entry, treeOutputs_source, List.append_nil, treeOutputs_update_source] using
      tree_run_code caller .source source raw regs (treeOutputs [] []) [] [] ctx
  have throughProbe := first.trans caller (Runs.one caller (by trivial)
    (separator_failure_step caller .source raw [] [] (reset regs)
      (treeOutputs (treeCode source) []) [] [] ctx returned))
  simp only [TreeParserMachine.reset_reset, toReversePhase] at throughProbe
  have combined := throughProbe.trans caller (source_rollback_run caller (treeCode source) raw (reset regs) ctx)
  have count : (2 * (treeCode source).length + 2 + 1) + (2 * (treeCode source).length + 2) =
      4 * (treeCode source).length + 5 := by omega
  rw [count] at combined
  simpa only [resultCfg, TreeParserMachine.reset_reset] using combined

theorem run_target_failure_trace (source : BinaryTree Unit) (raw : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) (returned : (parseTreeRun raw).1 = none) :
    Runs caller (4 * (treeCode source).length + TreeParserMachine.runSteps raw + 6)
      (entry regs (treeCode source ++ separatorTag :: raw) ctx)
      (resultCfg regs (treeCode source ++ separatorTag :: raw) ctx none) := by
  have targetRun := tree_run_of_none caller .target raw (reset regs)
    (treeOutputs (treeCode source) []) [] [] ctx returned
  simp only [TreeParserMachine.reset_reset] at targetRun
  have combined := ((source_separator_run caller source raw regs ctx).trans caller targetRun).trans caller
    (target_failure_run caller (treeCode source) raw (reset regs) ctx)
  have count : (2 * (treeCode source).length + 3 + TreeParserMachine.runSteps raw) +
      (2 * (treeCode source).length + 3) =
      4 * (treeCode source).length + TreeParserMachine.runSteps raw + 6 := by omega
  rw [count] at combined
  simpa only [resultCfg, TreeParserMachine.reset_reset] using combined

theorem run_second_separator_failure_trace (source target : BinaryTree Unit) (raw : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) (returned : (parseSeparatorRun raw).1 = none) :
    Runs caller (4 * (treeCode source).length + 4 * (treeCode target).length + 11)
      (entry regs (treeCode source ++ separatorTag :: (treeCode target ++ raw)) ctx)
      (resultCfg regs (treeCode source ++ separatorTag :: (treeCode target ++ raw)) ctx none) := by
  have throughProbe := (two_trees_run caller source target raw regs ctx).trans caller
    (Runs.one caller (by trivial) (separator_failure_step caller .target raw [] [] (reset regs)
      (treeOutputs (treeCode source) (treeCode target)) [] [] ctx returned))
  simp only [TreeParserMachine.reset_reset, toReversePhase] at throughProbe
  have combined := throughProbe.trans caller
    (target_rollback_run caller (treeCode source) (treeCode target) raw (reset regs) ctx)
  have count : (2 * (treeCode source).length + 2 * (treeCode target).length + 5 + 1) +
      (2 * (treeCode source).length + 2 * (treeCode target).length + 5) =
      4 * (treeCode source).length + 4 * (treeCode target).length + 11 := by omega
  rw [count] at combined
  simpa only [resultCfg, TreeParserMachine.reset_reset] using combined

theorem run_bits_failure_trace (source target : BinaryTree Unit) (bs : Bits) (raw : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) (blocked : BitsBlocked raw) :
    Runs caller (4 * (treeCode source).length + 4 * (treeCode target).length + 2 * bs.length + 14)
      (entry regs (treeCode source ++ separatorTag :: (treeCode target ++ separatorTag :: (bitTags bs ++ raw))) ctx)
      (resultCfg regs (treeCode source ++ separatorTag :: (treeCode target ++ separatorTag :: (bitTags bs ++ raw))) ctx none) := by
  have scan := bitsScan_blocked_run caller bs raw [] [] (reset regs)
    (treeOutputs (treeCode source) (treeCode target)) [] [] ctx blocked
  simp only [List.append_nil, TreeParserMachine.reset_reset] at scan
  have undo := bitsUndo_run caller raw [] [] (reset regs)
    (treeOutputs (treeCode source) (treeCode target)) [] bs.reverse ctx
  simp only [List.length_reverse, List.reverse_reverse, TreeParserMachine.reset_reset] at undo
  have combined := (((before_bits_run caller source target (bitTags bs ++ raw) regs ctx).trans caller scan).trans caller undo).trans caller
    (restore_target_run caller (treeCode source) (treeCode target) (bitTags bs ++ raw) (reset regs) ctx)
  have count : ((2 * (treeCode source).length + 2 * (treeCode target).length + 6 + (bs.length + 1)) +
      (bs.length + 1)) + (2 * (treeCode source).length + 2 * (treeCode target).length + 6) =
      4 * (treeCode source).length + 4 * (treeCode target).length + 2 * bs.length + 14 := by omega
  rw [count] at combined
  simpa only [resultCfg, TreeParserMachine.reset_reset] using combined

theorem before_eof_run (source target : BinaryTree Unit) (bs : Bits) (raw : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    Runs caller (2 * (treeCode source).length + 2 * (treeCode target).length + 2 * bs.length + 8)
      (entry regs (treeCode source ++ separatorTag ::
        (treeCode target ++ separatorTag :: (bitTags bs ++ endInputTag :: raw))) ctx)
      (cfg (some (phaseLabel .eof)) (reset regs) raw [] []
        (treeOutputs (treeCode source) (treeCode target)) bs [] ctx) := by
  have scan := bitsScan_terminated_run caller bs raw [] [] (reset regs)
    (treeOutputs (treeCode source) (treeCode target)) [] [] ctx
  simp only [List.append_nil, TreeParserMachine.reset_reset] at scan
  have emit := bitsEmit_run caller raw [] [] (reset regs)
    (treeOutputs (treeCode source) (treeCode target)) [] bs.reverse ctx
  simp only [List.length_reverse, List.reverse_reverse, List.append_nil, TreeParserMachine.reset_reset] at emit
  have combined := ((before_bits_run caller source target (bitTags bs ++ endInputTag :: raw) regs ctx).trans caller scan).trans caller emit
  have count : (2 * (treeCode source).length + 2 * (treeCode target).length + 6 + (bs.length + 1)) +
      (bs.length + 1) =
      2 * (treeCode source).length + 2 * (treeCode target).length + 2 * bs.length + 8 := by omega
  rwa [count] at combined

theorem run_code_trace (source target : BinaryTree Unit) (bs : Bits) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    Runs caller (2 * (treeCode source).length + 2 * (treeCode target).length + 2 * bs.length + 9)
      (entry regs (inputCode source target bs) ctx)
      (resultCfg regs (inputCode source target bs) ctx (some (source, target, bs))) := by
  have combined := (before_eof_run caller source target bs [] regs ctx).trans caller
    (Runs.one caller (fullOwned_phase _) (eof_step_nil caller [] [] (reset regs)
      (treeOutputs (treeCode source) (treeCode target)) bs [] ctx))
  have count : 2 * (treeCode source).length + 2 * (treeCode target).length + 2 * bs.length + 8 + 1 =
      2 * (treeCode source).length + 2 * (treeCode target).length + 2 * bs.length + 9 := by omega
  rw [count] at combined
  simpa only [resultCfg, inputCode, List.append_assoc, List.cons_append, List.nil_append,
    TreeParserMachine.reset_reset] using combined

theorem eof_nonempty_step (raw rev : Word) (pending : List Unit) (regs : Registers R)
    (outputs : TreeSide → Word) (fuel bitsReverse : Bits) (ctx : ∀ k, List (Γ k))
    (nonempty : raw ≠ []) :
    step caller (cfg (some (phaseLabel .eof)) regs raw rev pending outputs fuel bitsReverse ctx) =
      some (cfg (some (phaseLabel .restoreEnd)) (reset regs) raw rev pending outputs fuel bitsReverse ctx) := by
  cases raw with
  | nil => exact False.elim (nonempty rfl)
  | cons tag raw => exact eof_step_cons caller tag raw rev pending regs outputs fuel bitsReverse ctx

theorem eof_failure_run (source target raw : Word) (bs : Bits) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (nonempty : raw ≠ []) :
    Runs caller (2 * source.length + 2 * target.length + 2 * bs.length + 10)
      (cfg (some (phaseLabel .eof)) regs raw [] [] (treeOutputs source target) bs [] ctx)
      (cfg (some (resultLabel .failure)) (reset regs)
        (source ++ separatorTag :: (target ++ separatorTag :: (bitTags bs ++ endInputTag :: raw)))
        [] [] (treeOutputs [] []) [] [] ctx) := by
  have first := (Runs.one caller (fullOwned_phase _)
    (eof_nonempty_step caller raw [] [] regs (treeOutputs source target) bs [] ctx nonempty)).trans caller
      (Runs.one caller (fullOwned_phase _)
        (restoreEnd_step caller raw [] [] (reset regs) (treeOutputs source target) bs [] ctx))
  simp only [TreeParserMachine.reset_reset] at first
  have undo := fuel_bits_undo_run caller (endInputTag :: raw) [] [] (reset regs)
    (treeOutputs source target) bs [] ctx
  simp only [List.length_nil, Nat.add_zero, List.reverse_nil, List.nil_append, TreeParserMachine.reset_reset] at undo
  have combined := (first.trans caller undo).trans caller
    (restore_target_run caller source target (bitTags bs ++ endInputTag :: raw) (reset regs) ctx)
  have count : (1 + 1 + (2 * bs.length + 2)) + (2 * source.length + 2 * target.length + 6) =
      2 * source.length + 2 * target.length + 2 * bs.length + 10 := by omega
  rw [count] at combined
  simpa only [TreeParserMachine.reset_reset] using combined

theorem run_trailing_trace (source target : BinaryTree Unit) (bs : Bits) (raw : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) (nonempty : raw ≠ []) :
    Runs caller (4 * (treeCode source).length + 4 * (treeCode target).length + 4 * bs.length + 18)
      (entry regs (inputCode source target bs ++ raw) ctx)
      (resultCfg regs (inputCode source target bs ++ raw) ctx none) := by
  have combined := (before_eof_run caller source target bs raw regs ctx).trans caller
    (eof_failure_run caller (treeCode source) (treeCode target) raw bs (reset regs) ctx nonempty)
  have count : (2 * (treeCode source).length + 2 * (treeCode target).length + 2 * bs.length + 8) +
      (2 * (treeCode source).length + 2 * (treeCode target).length + 2 * bs.length + 10) =
      4 * (treeCode source).length + 4 * (treeCode target).length + 4 * bs.length + 18 := by omega
  rw [count] at combined
  simpa only [resultCfg, inputCode, List.append_assoc, List.cons_append, List.nil_append,
    TreeParserMachine.reset_reset] using combined


/-- Exact first-return count, following the actual source results; never called by a block. -/
def inputSteps (raw : Word) : Nat :=
  match (parseTreeRun raw).1 with
  | none => TreeParserMachine.runSteps raw
  | some (source, afterSource) =>
    match (parseSeparatorRun afterSource).1 with
    | none => 4 * (treeCode source).length + 5
    | some beforeTarget =>
      match (parseTreeRun beforeTarget).1 with
      | none => 4 * (treeCode source).length + TreeParserMachine.runSteps beforeTarget + 6
      | some (target, afterTarget) =>
        match (parseSeparatorRun afterTarget).1 with
        | none => 4 * (treeCode source).length + 4 * (treeCode target).length + 11
        | some beforeBits =>
          match (parseBitsRun beforeBits).1 with
          | none => 4 * (treeCode source).length + 4 * (treeCode target).length +
              2 * bitsConsumed beforeBits + 14
          | some (bs, rest) =>
            if rest = [] then 2 * (treeCode source).length + 2 * (treeCode target).length + 2 * bs.length + 9
            else 4 * (treeCode source).length + 4 * (treeCode target).length + 4 * bs.length + 18

/-- Every raw word follows its actual source-return sequence to the first full live result. -/
theorem run_source_trace (raw : Word) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    Runs caller (inputSteps raw) (entry regs raw ctx) (resultCfg regs raw ctx (parseInputRun raw).1) := by
  simp only [inputSteps, parseInputRun, CallCount.tick, Resources.bind]
  cases first : (parseTreeRun raw).1 with
  | none => exact run_tree_failure_trace caller raw regs ctx first
  | some pair =>
      rcases pair with ⟨source, afterSource⟩
      dsimp only
      have rawEq := (parseTreeRun_iff raw source afterSource).mp first
      cases firstSep : (parseSeparatorRun afterSource).1 with
      | none =>
          simpa only [rawEq] using
            run_first_separator_failure_trace caller source afterSource regs ctx firstSep
      | some beforeTarget =>
          dsimp only
          have firstSepEq := (parseSeparatorRun_iff afterSource beforeTarget).mp firstSep
          cases second : (parseTreeRun beforeTarget).1 with
          | none =>
              simpa only [rawEq, firstSepEq] using
                run_target_failure_trace caller source beforeTarget regs ctx second
          | some pair =>
              rcases pair with ⟨target, afterTarget⟩
              dsimp only
              have targetEq := (parseTreeRun_iff beforeTarget target afterTarget).mp second
              cases secondSep : (parseSeparatorRun afterTarget).1 with
              | none =>
                  simpa only [rawEq, firstSepEq, targetEq] using
                    run_second_separator_failure_trace caller source target afterTarget regs ctx secondSep
              | some beforeBits =>
                  dsimp only
                  have secondSepEq := (parseSeparatorRun_iff afterTarget beforeBits).mp secondSep
                  cases threshold : (parseBitsRun beforeBits).1 with
                  | none =>
                      dsimp only
                      obtain ⟨bs, rest, word, blocked⟩ := parseBitsRun_none_decomposition beforeBits threshold
                      have count : bitsConsumed beforeBits = bs.length := by
                        rw [word, bitsConsumed_of_blocked bs rest blocked]
                      rw [count]
                      simpa only [rawEq, firstSepEq, targetEq, secondSepEq, word] using
                        run_bits_failure_trace caller source target bs rest regs ctx blocked
                  | some pair =>
                      rcases pair with ⟨bs, rest⟩
                      dsimp only
                      have bitsEq := (parseBitsRun_iff beforeBits bs rest).mp threshold
                      have encoded : raw = inputCode source target bs ++ rest := by
                        rw [rawEq, firstSepEq, targetEq, secondSepEq, bitsEq]
                        simp only [inputCode, List.append_assoc, List.cons_append, List.nil_append]
                      cases rest with
                      | nil =>
                          simp only [List.append_nil] at encoded
                          simpa only [finishInputRun, ite_true, encoded] using
                            run_code_trace caller source target bs regs ctx
                      | cons tag rest =>
                          simpa only [finishInputRun, List.cons_ne_nil, ite_false, encoded] using
                            run_trailing_trace caller source target bs (tag :: rest) regs ctx (by simp)

theorem run_source (raw : Word) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (next caller)^[inputSteps raw] (some (entry regs raw ctx)) =
      some (resultCfg regs raw ctx (parseInputRun raw).1) :=
  (run_source_trace caller raw regs ctx).iterate caller

theorem run_of_some (raw : Word) (source target : BinaryTree Unit) (bs : Bits)
    (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (returned : (parseInputRun raw).1 = some (source, target, bs)) :
    (next caller)^[inputSteps raw] (some (entry regs raw ctx)) =
      some (cfg (some (resultLabel .success)) (reset regs) [] [] []
        (treeOutputs (treeCode source) (treeCode target)) bs [] ctx) := by
  rw [run_source, returned]
  rfl

theorem run_of_none (raw : Word) (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (returned : (parseInputRun raw).1 = none) :
    (next caller)^[inputSteps raw] (some (entry regs raw ctx)) =
      some (cfg (some (resultLabel .failure)) (reset regs) raw [] [] (treeOutputs [] []) [] [] ctx) := by
  rw [run_source, returned]
  rfl

theorem run_code (source target : BinaryTree Unit) (bs : Bits) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    (next caller)^[2 * (treeCode source).length + 2 * (treeCode target).length + 2 * bs.length + 9]
      (some (entry regs (inputCode source target bs) ctx)) =
        some (resultCfg regs (inputCode source target bs) ctx (some (source, target, bs))) :=
  (run_code_trace caller source target bs regs ctx).iterate caller

theorem inputSteps_le (raw : Word) : inputSteps raw ≤ 4 * raw.length + 7 := by
  have firstBound := TreeParserMachine.runSteps_le raw
  unfold inputSteps
  cases first : (parseTreeRun raw).1 with
  | none => dsimp only; omega
  | some pair =>
      rcases pair with ⟨source, afterSource⟩
      dsimp only
      have sourceLength : raw.length = (treeCode source).length + afterSource.length := by
        rw [(parseTreeRun_iff raw source afterSource).mp first, List.length_append]
      cases firstSep : (parseSeparatorRun afterSource).1 with
      | none => dsimp only; omega
      | some beforeTarget =>
          dsimp only
          have firstSepLength := parseSeparatorRun_consumed_length afterSource beforeTarget firstSep
          have targetBound := TreeParserMachine.runSteps_le beforeTarget
          cases second : (parseTreeRun beforeTarget).1 with
          | none => dsimp only; omega
          | some pair =>
              rcases pair with ⟨target, afterTarget⟩
              dsimp only
              have targetLength : beforeTarget.length = (treeCode target).length + afterTarget.length := by
                rw [(parseTreeRun_iff beforeTarget target afterTarget).mp second, List.length_append]
              cases secondSep : (parseSeparatorRun afterTarget).1 with
              | none => dsimp only; omega
              | some beforeBits =>
                  dsimp only
                  have secondSepLength := parseSeparatorRun_consumed_length afterTarget beforeBits secondSep
                  have bitsBound := bitsConsumed_le beforeBits
                  cases threshold : (parseBitsRun beforeBits).1 with
                  | none => dsimp only; omega
                  | some pair =>
                      rcases pair with ⟨bs, rest⟩
                      dsimp only
                      have bitsLength := parseBitsRun_consumed_length beforeBits bs rest threshold
                      split <;> omega

theorem inputSteps_pos (raw : Word) : 0 < inputSteps raw := by
  have firstPositive := TreeParserMachine.runSteps_pos raw
  unfold inputSteps
  split
  · exact firstPositive
  · split
    · omega
    · split
      · omega
      · split
        · omega
        · split
          · omega
          · split <;> omega

def runInTime (raw : Word) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller) (entry regs raw ctx)
      (some (resultCfg regs raw ctx (parseInputRun raw).1)) (inputSteps raw) where
  steps := inputSteps raw
  evals_in_steps := run_source caller raw regs ctx
  steps_le_m := Nat.le_refl _

def runInLinearTime (raw : Word) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller) (entry regs raw ctx)
      (some (resultCfg regs raw ctx (parseInputRun raw).1)) (4 * raw.length + 7) where
  steps := inputSteps raw
  evals_in_steps := run_source caller raw regs ctx
  steps_le_m := inputSteps_le raw


theorem bitsEmit_prefix_run (moved rest : Bits) (raw rev : Word) (pending : List Unit)
    (regs : Registers R) (outputs : TreeSide → Word) (fuel : Bits) (ctx : ∀ k, List (Γ k)) :
    Runs caller moved.length
      (cfg (some (phaseLabel .bitsEmit)) regs raw rev pending outputs fuel (moved ++ rest) ctx)
      (cfg (some (phaseLabel .bitsEmit)) (if moved = [] then regs else reset regs)
        raw rev pending outputs (moved.reverse ++ fuel) rest ctx) := by
  induction moved generalizing regs fuel with
  | nil => exact .refl _
  | cons b moved ih =>
      rw [List.length_cons, List.cons_append]
      have tailRun := ih (regs := reset regs) (fuel := b :: fuel)
      have run := Runs.cons (fullOwned_phase _)
        (bitsEmit_step_cons caller b raw rev pending regs outputs fuel (moved ++ rest) ctx) tailRun
      simpa only [List.cons_ne_nil, ite_false, TreeParserMachine.reset_reset, ite_self,
        List.reverse_cons, List.append_assoc, List.singleton_append] using run

theorem fuelUndo_prefix_run (moved rest : Bits) (raw rev : Word) (pending : List Unit)
    (regs : Registers R) (outputs : TreeSide → Word) (bitsReverse : Bits) (ctx : ∀ k, List (Γ k)) :
    Runs caller moved.length
      (cfg (some (phaseLabel .fuelUndo)) regs raw rev pending outputs (moved ++ rest) bitsReverse ctx)
      (cfg (some (phaseLabel .fuelUndo)) (if moved = [] then regs else reset regs)
        raw rev pending outputs rest (moved.reverse ++ bitsReverse) ctx) := by
  induction moved generalizing regs bitsReverse with
  | nil => exact .refl _
  | cons b moved ih =>
      rw [List.length_cons, List.cons_append]
      have tailRun := ih (regs := reset regs) (bitsReverse := b :: bitsReverse)
      have run := Runs.cons (fullOwned_phase _)
        (fuelUndo_step_cons caller b raw rev pending regs outputs (moved ++ rest) bitsReverse ctx) tailRun
      simpa only [List.cons_ne_nil, ite_false, TreeParserMachine.reset_reset, ite_self,
        List.reverse_cons, List.append_assoc, List.singleton_append] using run

theorem bitsUndo_prefix_run (moved rest : Bits) (raw rev : Word) (pending : List Unit)
    (regs : Registers R) (outputs : TreeSide → Word) (fuel : Bits) (ctx : ∀ k, List (Γ k)) :
    Runs caller moved.length
      (cfg (some (phaseLabel .bitsUndo)) regs raw rev pending outputs fuel (moved ++ rest) ctx)
      (cfg (some (phaseLabel .bitsUndo)) (if moved = [] then regs else reset regs)
        (bitTags moved.reverse ++ raw) rev pending outputs fuel rest ctx) := by
  induction moved generalizing regs raw with
  | nil => exact .refl _
  | cons b moved ih =>
      rw [List.length_cons, List.cons_append]
      have tailRun := ih (regs := reset regs) (raw := bitTag b :: raw)
      have run := Runs.cons (fullOwned_phase _)
        (bitsUndo_step_cons caller b raw rev pending regs outputs fuel (moved ++ rest) ctx) tailRun
      simpa only [List.cons_ne_nil, ite_false, TreeParserMachine.reset_reset, ite_self,
        List.reverse_cons, bitTags_append, bitTags_cons, bitTags_nil,
        List.append_assoc, List.singleton_append] using run

theorem toReversePhase_prefix_run (d : TreeSide) (moved rest raw rev : Word) (pending : List Unit)
    (regs : Registers R) (outputs : TreeSide → Word) (fuel bitsReverse : Bits)
    (ctx : ∀ k, List (Γ k)) :
    Runs caller moved.length
      (cfg (some (phaseLabel (toReversePhase d))) regs raw rev pending
        (Function.update outputs d (moved ++ rest)) fuel bitsReverse ctx)
      (cfg (some (phaseLabel (toReversePhase d))) (if moved = [] then regs else reset regs)
        raw (moved.reverse ++ rev) pending (Function.update outputs d rest) fuel bitsReverse ctx) := by
  induction moved generalizing regs rev with
  | nil => exact .refl _
  | cons tag moved ih =>
      rw [List.length_cons, List.cons_append]
      have tailRun := ih (regs := reset regs) (rev := tag :: rev)
      have run := Runs.cons (fullOwned_phase _)
        (toReversePhase_step_cons caller d tag raw rev (moved ++ rest) pending regs outputs fuel bitsReverse ctx) tailRun
      simpa only [List.cons_ne_nil, ite_false, TreeParserMachine.reset_reset, ite_self,
        List.reverse_cons, List.append_assoc, List.singleton_append] using run

theorem toRawPhase_prefix_run (d : TreeSide) (moved rest raw : Word) (pending : List Unit)
    (regs : Registers R) (outputs : TreeSide → Word) (fuel bitsReverse : Bits)
    (ctx : ∀ k, List (Γ k)) :
    Runs caller moved.length
      (cfg (some (phaseLabel (toRawPhase d))) regs raw (moved ++ rest) pending outputs fuel bitsReverse ctx)
      (cfg (some (phaseLabel (toRawPhase d))) (if moved = [] then regs else reset regs)
        (moved.reverse ++ raw) rest pending outputs fuel bitsReverse ctx) := by
  induction moved generalizing regs raw with
  | nil => exact .refl _
  | cons tag moved ih =>
      rw [List.length_cons, List.cons_append]
      have tailRun := ih (regs := reset regs) (raw := tag :: raw)
      have run := Runs.cons (fullOwned_phase _)
        (toRawPhase_step_cons caller d tag raw (moved ++ rest) pending regs outputs fuel bitsReverse ctx) tailRun
      simpa only [List.cons_ne_nil, ite_false, TreeParserMachine.reset_reset, ite_self,
        List.reverse_cons, List.append_assoc, List.singleton_append] using run

theorem bitsEmit_prefix (raw rev : Word) (pending : List Unit) (regs : Registers R)
    (outputs : TreeSide → Word) (fuel bitsReverse : Bits) (ctx : ∀ k, List (Γ k))
    (j : Nat) (bound : j ≤ bitsReverse.length) :
    (next caller)^[j]
      (some (cfg (some (phaseLabel .bitsEmit)) regs raw rev pending outputs fuel bitsReverse ctx)) =
        some (cfg (some (phaseLabel .bitsEmit)) (if j = 0 then regs else reset regs)
          raw rev pending outputs ((bitsReverse.take j).reverse ++ fuel) (bitsReverse.drop j) ctx) := by
  have run := bitsEmit_prefix_run caller (bitsReverse.take j) (bitsReverse.drop j) raw rev pending regs outputs fuel ctx
  have length : (bitsReverse.take j).length = j := by
    rw [List.length_take, Nat.min_eq_left bound]
  have empty : bitsReverse.take j = [] ↔ j = 0 := by
    constructor
    · intro equal
      have lengths := congrArg List.length equal
      simpa only [length, List.length_nil] using lengths
    · intro equal
      subst j
      rfl
  simpa only [List.take_append_drop, length, empty] using run.iterate caller


omit [DecidableEq K] in
theorem entry_owned (raw : Word) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    FullOwned (entry (Λ := Λ) regs raw ctx).l := fullOwned_tree .source .init

omit [DecidableEq K] in
theorem resultCfg_not_owned (raw : Word) (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (result : Option ParsedInput) : ¬ FullOwned (resultCfg (Λ := Λ) regs raw ctx result).l := by
  cases result with
  | none => exact not_fullOwned_result .failure
  | some pair => rcases pair with ⟨source, target, bs⟩; exact not_fullOwned_result .success

theorem run_prefix (raw : Word) (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (n : Nat) (bound : n ≤ inputSteps raw) :
    ∃ reached,
      (next caller)^[n] (some (entry regs raw ctx)) = some reached ∧
      Runs caller n (entry regs raw ctx) reached ∧
      Runs caller (inputSteps raw - n) reached (resultCfg regs raw ctx (parseInputRun raw).1) ∧
      (n < inputSteps raw ↔ FullOwned reached.l) := by
  obtain ⟨reached, executed, before, after⟩ := (run_source_trace caller raw regs ctx).prefix caller n bound
  refine ⟨reached, executed, before, after, ?_⟩
  constructor
  · intro strict
    exact after.owned_start caller (by omega)
  · intro owned
    by_contra notStrict
    have equal : n = inputSteps raw := by omega
    subst n
    have endpoints : reached = resultCfg regs raw ctx (parseInputRun raw).1 :=
      Option.some.inj (executed.symm.trans (run_source caller raw regs ctx))
    exact resultCfg_not_owned raw regs ctx (parseInputRun raw).1 (endpoints ▸ owned)

theorem step_caller_independent (other : External Λ → Statement Γ Λ R)
    (c : Cfg Γ Λ R) (owned : FullOwned c.l) : step caller c = step other c := by
  rcases c with ⟨label, regs, storeState⟩
  cases label with
  | none => cases owned
  | some label =>
      cases label with
      | inl pair => rcases pair with ⟨d, phase⟩; rfl
      | inr external =>
          cases external with
          | inl pair =>
              rcases pair with ⟨side, result⟩
              cases side with
              | source =>
                  cases result with
                  | success => rfl
                  | failure => cases owned
              | target => cases result <;> rfl
          | inr extra =>
              cases extra with
              | inl phase => rfl
              | inr exit => cases owned

theorem Runs.caller_independent {n : Nat} {start final : Cfg Γ Λ R}
    (run : Runs caller n start final) (other : External Λ → Statement Γ Λ R) :
    Runs other n start final := by
  induction run with
  | refl c => exact .refl c
  | cons owned transition run ih =>
      apply Runs.cons owned
      · rw [← step_caller_independent caller other _ owned]
        exact transition
      · exact ih

theorem run_prefix_caller_independent (other : External Λ → Statement Γ Λ R)
    (raw : Word) (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (n : Nat) (bound : n ≤ inputSteps raw) :
    (next caller)^[n] (some (entry regs raw ctx)) =
      (next other)^[n] (some (entry regs raw ctx)) := by
  obtain ⟨reached, executed, before, _, _⟩ := run_prefix caller raw regs ctx n bound
  exact executed.trans ((before.caller_independent caller other).iterate other).symm

omit [DecidableEq K] in
theorem resultCfg_injective (raw : Word) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    Function.Injective (resultCfg (Λ := Λ) regs raw ctx) := by
  intro left right equal
  cases left with
  | none =>
      cases right with
      | none => rfl
      | some pair =>
          rcases pair with ⟨source, target, bs⟩
          have labels := congrArg (fun c : Cfg Γ Λ R => c.l) equal
          cases labels
  | some left =>
      rcases left with ⟨source, target, bs⟩
      cases right with
      | none =>
          have labels := congrArg (fun c : Cfg Γ Λ R => c.l) equal
          cases labels
      | some right =>
          rcases right with ⟨otherSource, otherTarget, otherBits⟩
          have sourceEq := congrArg (fun c : Cfg Γ Λ R => c.stk (outputStack .source)) equal
          have targetEq := congrArg (fun c : Cfg Γ Λ R => c.stk (outputStack .target)) equal
          have bitsEq := congrArg (fun c : Cfg Γ Λ R => c.stk fuelStack) equal
          change treeCode source = treeCode otherSource at sourceEq
          change treeCode target = treeCode otherTarget at targetEq
          change bs = otherBits at bitsEq
          have encoded : inputCode source target bs = inputCode otherSource otherTarget otherBits := by
            simp only [inputCode, sourceEq, targetEq, bitsEq]
          obtain ⟨rfl, rfl, rfl⟩ := inputCode_injective source target bs otherSource otherTarget otherBits encoded
          rfl

theorem iterate_inputSteps_eq_resultCfg_iff (raw : Word) (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (observed : Option ParsedInput) :
    (next caller)^[inputSteps raw] (some (entry regs raw ctx)) = some (resultCfg regs raw ctx observed) ↔
      (parseInputRun raw).1 = observed := by
  rw [run_source, Option.some.injEq]
  exact (resultCfg_injective raw regs ctx).eq_iff

def FirstSuccess (raw : Word) (source target : BinaryTree Unit) (bs : Bits)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) : Prop :=
  (next caller)^[inputSteps raw] (some (entry regs raw ctx)) =
    some (resultCfg regs raw ctx (some (source, target, bs)))

theorem firstSuccess_iff (raw : Word) (source target : BinaryTree Unit) (bs : Bits)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    FirstSuccess caller raw source target bs regs ctx ↔
      (parseInputRun raw).1 = some (source, target, bs) :=
  iterate_inputSteps_eq_resultCfg_iff caller raw regs ctx (some (source, target, bs))

theorem firstSuccess_code_iff (raw : Word) (source target : BinaryTree Unit) (bs : Bits)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    FirstSuccess caller raw source target bs regs ctx ↔ raw = inputCode source target bs := by
  rw [firstSuccess_iff, parseInputRun_iff]


/-- Two owned traces with unowned endpoints stop at the same first handoff. -/
theorem Runs.first_length_eq {n m : Nat} {start left right : Cfg Γ Λ R}
    (first : Runs caller n start left) (second : Runs caller m start right)
    (leftExit : ¬ FullOwned left.l) (rightExit : ¬ FullOwned right.l) : n = m := by
  apply Nat.le_antisymm
  · by_contra larger
    have strict : m < n := by omega
    obtain ⟨reached, executed, owned⟩ := first.owned_prefix caller m strict
    have equal : reached = right := Option.some.inj (executed.symm.trans (second.iterate caller))
    exact rightExit (equal ▸ owned)
  · by_contra larger
    have strict : n < m := by omega
    obtain ⟨reached, executed, owned⟩ := second.owned_prefix caller n strict
    have equal : reached = left := Option.some.inj (executed.symm.trans (first.iterate caller))
    exact leftExit (equal ▸ owned)

theorem inputSteps_eq_of_trace (raw : Word) (regs : Registers R) (ctx : ∀ k, List (Γ k))
    {n : Nat} {final : Cfg Γ Λ R} (trace : Runs caller n (entry regs raw ctx) final)
    (exit : ¬ FullOwned final.l) : inputSteps raw = n :=
  (run_source_trace caller raw regs ctx).first_length_eq caller trace
    (resultCfg_not_owned raw regs ctx (parseInputRun raw).1) exit

theorem inputSteps_code_append (source target : BinaryTree Unit) (bs : Bits) (rest : Word) :
    inputSteps (inputCode source target bs ++ rest) =
      if rest = [] then 2 * (treeCode source).length + 2 * (treeCode target).length + 2 * bs.length + 9
      else 4 * (treeCode source).length + 4 * (treeCode target).length + 4 * bs.length + 18 := by
  have word : inputCode source target bs ++ rest =
      treeCode source ++ separatorTag :: (treeCode target ++ separatorTag :: (bitTags bs ++ endInputTag :: rest)) := by
    simp only [inputCode, List.append_assoc, List.cons_append, List.nil_append]
  have bits : (parseBitsRun (bitTags bs ++ endInputTag :: rest)).1 = some (bs, rest) := by
    simpa only [List.append_assoc, List.singleton_append] using congrArg Prod.fst (parseBitsRun_code bs rest)
  rw [word]
  simp only [inputSteps, parseTreeRun_code, parseSeparatorRun_separator, bits]

theorem inputSteps_code (source target : BinaryTree Unit) (bs : Bits) :
    inputSteps (inputCode source target bs) =
      2 * (treeCode source).length + 2 * (treeCode target).length + 2 * bs.length + 9 := by
  simpa only [List.append_nil, ite_true] using inputSteps_code_append source target bs []

theorem inputSteps_trailing (source target : BinaryTree Unit) (bs : Bits) (rest : Word)
    (nonempty : rest ≠ []) : inputSteps (inputCode source target bs ++ rest) =
      4 * (treeCode source).length + 4 * (treeCode target).length + 4 * bs.length + 18 := by
  rw [inputSteps_code_append, ite_eq_right nonempty]

theorem inputSteps_of_some (raw : Word) (source target : BinaryTree Unit) (bs : Bits)
    (returned : (parseInputRun raw).1 = some (source, target, bs)) :
    inputSteps raw = 2 * raw.length + 3 := by
  rw [(parseInputRun_iff raw source target bs).mp returned, inputSteps_code,
    inputCode_length, treeCode_length, treeCode_length]
  omega

theorem inputSteps_code_nodes (source target : BinaryTree Unit) (bs : Bits) :
    inputSteps (inputCode source target bs) =
      4 * source.numNodes + 4 * target.numNodes + 2 * bs.length + 13 := by
  rw [inputSteps_code, treeCode_length, treeCode_length]
  omega

theorem run_emit (source target : BinaryTree Unit) (bs : Bits) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    (next caller)^[2 * (treeCode source).length + 2 * (treeCode target).length + 2 * bs.length + 9]
      (some (entry regs (emitInputRun source target bs).1 ctx)) =
        some (resultCfg regs (emitInputRun source target bs).1 ctx (some (source, target, bs))) := by
  rw [emitInputRun_value]
  exact run_code caller source target bs regs ctx

theorem run_openPrefix_failure_trace (accepted rest : Word) (p : Nat) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (opened : TreeParserMachine.OpenPrefix accepted p)
    (blocked : TreeParserMachine.Blocked rest) :
    Runs caller (2 * accepted.length + p + 4) (entry regs (accepted ++ rest) ctx)
      (resultCfg regs (accepted ++ rest) ctx none) := by
  simpa only [TreeParserMachine.runSteps_openPrefix opened blocked] using
    run_tree_failure_trace caller (accepted ++ rest) regs ctx
      (TreeParserMachine.parseTreeRun_none_of_openPrefix opened blocked)

theorem run_target_openPrefix_failure_trace (source : BinaryTree Unit) (accepted rest : Word)
    (p : Nat) (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (opened : TreeParserMachine.OpenPrefix accepted p) (blocked : TreeParserMachine.Blocked rest) :
    Runs caller (4 * (treeCode source).length + 2 * accepted.length + p + 10)
      (entry regs (treeCode source ++ separatorTag :: (accepted ++ rest)) ctx)
      (resultCfg regs (treeCode source ++ separatorTag :: (accepted ++ rest)) ctx none) := by
  have trace := run_target_failure_trace caller source (accepted ++ rest) regs ctx
    (TreeParserMachine.parseTreeRun_none_of_openPrefix opened blocked)
  rw [TreeParserMachine.runSteps_openPrefix opened blocked] at trace
  convert trace using 1; omega

theorem nodes_openPrefix (count : Nat) :
    TreeParserMachine.OpenPrefix (List.replicate count nodeTag) (count + 1) := by
  induction count with
  | zero => exact .nil
  | succ count ih =>
      simpa only [List.replicate_add, List.replicate_one] using TreeParserMachine.OpenPrefix.node ih

theorem parseTreeRun_nodes_none (count : Nat) : (parseTreeRun (List.replicate count nodeTag)).1 = none := by
  simpa only [List.append_nil] using
    TreeParserMachine.parseTreeRun_none_of_openPrefix (nodes_openPrefix count) (rest := []) True.intro

theorem inputSteps_nodes (count : Nat) : inputSteps (List.replicate count nodeTag) = 3 * count + 5 := by
  simp only [inputSteps, parseTreeRun_nodes_none, TreeParserMachine.runSteps_nodes]

theorem nodes_prefix (count : Nat) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (next caller)^[count + 1] (some (entry regs (List.replicate count nodeTag) ctx)) =
      some (cfg (some (treeLabel .source .scan)) (reset regs) [] (List.replicate count nodeTag)
        (List.replicate (count + 1) ()) (treeOutputs [] []) [] [] ctx) :=
  TreeParserMachine.nodes_prefix (handler caller) .source count regs (treeOutputs [] []) (stores [] [] ctx)

theorem missing_target_sharp_trace (source : BinaryTree Unit) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    Runs caller (4 * (treeCode source ++ [separatorTag]).length + 7)
      (entry regs (treeCode source ++ [separatorTag]) ctx)
      (resultCfg regs (treeCode source ++ [separatorTag]) ctx none) := by
  have trace := run_target_failure_trace caller source [] regs ctx (by rfl)
  have count : 4 * (treeCode source).length + TreeParserMachine.runSteps [] + 6 =
      4 * (treeCode source ++ [separatorTag]).length + 7 := by
    change 4 * (treeCode source).length + 5 + 6 = _
    rw [List.length_append, List.length_singleton]
    omega
  rw [count] at trace
  exact trace

theorem missing_second_separator_sharp_trace (source target : BinaryTree Unit) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    Runs caller (4 * (treeCode source ++ separatorTag :: treeCode target).length + 7)
      (entry regs (treeCode source ++ separatorTag :: treeCode target) ctx)
      (resultCfg regs (treeCode source ++ separatorTag :: treeCode target) ctx none) := by
  have trace := run_second_separator_failure_trace caller source target [] regs ctx (by rfl)
  simp only [List.append_nil] at trace
  have count : 4 * (treeCode source).length + 4 * (treeCode target).length + 11 =
      4 * (treeCode source ++ separatorTag :: treeCode target).length + 7 := by
    rw [List.length_append, List.length_cons]
    omega
  rw [count] at trace
  exact trace


/-- Cells outside the pending stack, including both destination outputs and both Boolean stacks. -/
def outputCells (outputs : TreeSide → Word) : Nat :=
  (outputs .source).length + (outputs .target).length

def baseCells (c : Cfg Γ Λ R) : Nat :=
  (c.stk rawStack).length + (c.stk reverseStack).length +
    outputCells (fun d => c.stk (outputStack d)) +
    (c.stk fuelStack).length + (c.stk bitsReverseStack).length

def sideDebt : TreeSide → Nat | .source => 0 | .target => 1

def phaseDebt : Phase → Nat
  | .bitsScan | .fuelUndo | .bitsUndo | .restoreSep2 => 2
  | .bitsEmit | .eof | .restoreEnd => 3
  | .targetToReverse | .targetToRaw | .restoreSep1 => 1
  | .sourceToReverse | .sourceToRaw => 0

/-- Delimiters consumed but not yet physically restored; purely a control-label annotation. -/
def debt : Option (Label Λ) → Nat
  | some (.inl (d, _)) | some (.inr (.inl (d, _))) => sideDebt d
  | some (.inr (.inr (.inl phase))) => phaseDebt phase
  | some (.inr (.inr (.inr (.inl _)))) => 3
  | _ => 0

@[simp] theorem debt_tree (d : TreeSide) (phase : TreeParserMachine.Phase) :
    debt (some (treeLabel (Λ := Λ) d phase)) = sideDebt d := rfl
@[simp] theorem debt_treeResultLabel (d : TreeSide) (result : TreeParserMachine.Result) :
    debt (some (treeResultLabel (Λ := Λ) d result)) = sideDebt d := rfl
@[simp] theorem debt_phase (phase : Phase) :
    debt (some (phaseLabel (Λ := Λ) phase)) = phaseDebt phase := rfl

/-- The scan has one slot credit per unread symbol. Rollback needs only the absolute slot bound. -/
def PendingCondition (M : Nat) (label : Option (Label Λ)) (rawLength : Nat) (pending : List Unit) : Prop :=
  match label with
  | some (.inl (_, .scan)) => pending.length + rawLength ≤ M + 1
  | some (.inl (_, .undo)) | some (.inl (_, .dropPending)) => pending.length ≤ M + 1
  | _ => pending = []

def PendingControl (M : Nat) (c : Cfg Γ Λ R) : Prop :=
  PendingCondition M c.l (c.stk rawStack).length (c.stk pendingStack)

omit [DecidableEq K] in
@[simp] theorem baseCells_cfg (label : Option (Label Λ)) (regs : Registers R)
    (raw rev : Word) (pending : List Unit) (outputs : TreeSide → Word)
    (fuel bitsReverse : Bits) (ctx : ∀ k, List (Γ k)) :
    baseCells (cfg label regs raw rev pending outputs fuel bitsReverse ctx) =
      raw.length + rev.length + outputCells outputs + fuel.length + bitsReverse.length := rfl

omit [DecidableEq K] in
@[simp] theorem pendingControl_cfg (M : Nat) (label : Option (Label Λ)) (regs : Registers R)
    (raw rev : Word) (pending : List Unit) (outputs : TreeSide → Word)
    (fuel bitsReverse : Bits) (ctx : ∀ k, List (Γ k)) :
    PendingControl M (cfg label regs raw rev pending outputs fuel bitsReverse ctx) =
      PendingCondition M label raw.length pending := rfl

theorem outputCells_update_cons (outputs : TreeSide → Word) (d : TreeSide) (tag : Tag) :
    outputCells (Function.update outputs d (tag :: outputs d)) = outputCells outputs + 1 := by
  cases d <;> simp [outputCells, Function.update, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem outputCells_update_transfer (outputs : TreeSide → Word) (d : TreeSide) (tag : Tag) (word : Word) :
    outputCells (Function.update outputs d (tag :: word)) =
      outputCells (Function.update outputs d word) + 1 := by
  cases d <;> simp [outputCells, Function.update, Nat.add_assoc, Nat.add_comm]

/-- A property of an actual owned transition. The pending clause is conditional on the entry invariant. -/
structure Effect (before after : Cfg Γ Λ R) : Prop where
  registers : after.var = reset before.var
  frame : ∀ k, after.stk (protectedStack k) = before.stk (protectedStack k)
  mass : baseCells after + debt after.l = baseCells before + debt before.l
  pending : ∀ M, baseCells before + debt before.l = M →
    PendingControl M before → PendingControl M after

omit [DecidableEq K] in
private theorem cfg_effect
    {label nextLabel : Option (Label Λ)} {regs : Registers R}
    {raw rev nextRaw nextRev : Word} {pending nextPending : List Unit}
    {outputs nextOutputs : TreeSide → Word} {fuel bitsReverse nextFuel nextBitsReverse : Bits}
    {ctx : ∀ k, List (Γ k)}
    (mass : nextRaw.length + nextRev.length + outputCells nextOutputs + nextFuel.length +
        nextBitsReverse.length + debt nextLabel =
      raw.length + rev.length + outputCells outputs + fuel.length + bitsReverse.length + debt label)
    (slots : ∀ M, raw.length + rev.length + outputCells outputs + fuel.length + bitsReverse.length +
        debt label = M → PendingCondition M label raw.length pending →
      PendingCondition M nextLabel nextRaw.length nextPending) :
    Effect (cfg label regs raw rev pending outputs fuel bitsReverse ctx)
      (cfg nextLabel (reset regs) nextRaw nextRev nextPending nextOutputs nextFuel nextBitsReverse ctx) :=
  ⟨rfl, fun _ => rfl, mass, slots⟩

private theorem effect_of_step_eq {before after expected : Cfg Γ Λ R}
    (executed : step caller before = some after)
    (equation : step caller before = some expected) (effect : Effect before expected) :
    Effect before after := by
  have equal := Option.some.inj (equation.symm.trans executed)
  exact equal ▸ effect

/-- The unchanged tree blocks preserve delimiter-adjusted mass even in corrupted scratch states. -/
theorem tree_step_effect (d : TreeSide) (phase : TreeParserMachine.Phase)
    (raw rev : Word) (pending : List Unit) (regs : Registers R) (outputs : TreeSide → Word)
    (fuel bitsReverse : Bits) (ctx : ∀ k, List (Γ k)) {after : Cfg Γ Λ R}
    (executed : step caller (cfg (some (treeLabel d phase)) regs raw rev pending outputs fuel bitsReverse ctx) =
      some after) :
    Effect (cfg (some (treeLabel d phase)) regs raw rev pending outputs fuel bitsReverse ctx) after := by
  cases phase with
  | init =>
      apply effect_of_step_eq caller executed
        (TreeParserMachine.init_step (handler caller) d raw rev pending regs outputs (stores fuel bitsReverse ctx))
      apply cfg_effect
      · rfl
      · intro M mass slots
        change pending = [] at slots
        subst pending
        change 1 + raw.length ≤ M + 1
        omega
  | scan =>
      cases raw with
      | nil =>
          apply effect_of_step_eq caller executed
            (TreeParserMachine.scan_step_nil (handler caller) d rev pending regs outputs (stores fuel bitsReverse ctx))
          apply cfg_effect
          · rfl
          · intro M _ slots
            simpa only [PendingCondition, treeLabel, TreeParserMachine.phaseLabel, List.length_nil, Nat.add_zero] using slots
      | cons tag raw =>
          by_cases node : tag = nodeTag
          · subst tag
            apply effect_of_step_eq caller executed
              (TreeParserMachine.scan_step_node (handler caller) d raw rev pending regs outputs (stores fuel bitsReverse ctx))
            apply cfg_effect
            · simp only [treeLabel, TreeParserMachine.phaseLabel, debt, List.length_cons]; omega
            · intro M _ slots
              change pending.length + (raw.length + 1) ≤ M + 1 at slots
              change pending.length + 1 + raw.length ≤ M + 1
              omega
          · by_cases empty : tag = emptyTag
            · subst tag
              apply effect_of_step_eq caller executed
                (TreeParserMachine.scan_step_empty (handler caller) d raw rev pending regs outputs (stores fuel bitsReverse ctx))
              apply cfg_effect
              · simp only [treeLabel, TreeParserMachine.phaseLabel, debt, List.length_cons]; omega
              · intro M _ slots
                change pending.length + (raw.length + 1) ≤ M + 1 at slots
                by_cases done : pending.tail = []
                · simpa only [ite_eq_left done, PendingCondition, treeLabel, TreeParserMachine.phaseLabel] using done
                · simp only [ite_eq_right done, PendingCondition, TreeParserMachine.phaseLabel]
                  have length : pending.tail.length ≤ pending.length := by cases pending <;> simp
                  omega
            · apply effect_of_step_eq caller executed
                (TreeParserMachine.scan_step_foreign (handler caller) d tag raw rev pending regs outputs
                  (stores fuel bitsReverse ctx) node empty)
              apply cfg_effect
              · rfl
              · intro M _ slots
                change pending.length + (raw.length + 1) ≤ M + 1 at slots
                change pending.length ≤ M + 1
                omega
  | emit =>
      cases rev with
      | nil =>
          apply effect_of_step_eq caller executed
            (TreeParserMachine.emit_step_nil (handler caller) d raw pending regs outputs (stores fuel bitsReverse ctx))
          apply cfg_effect
          · rfl
          · intro M _ slots
            exact slots
      | cons tag rev =>
          apply effect_of_step_eq caller executed
            (TreeParserMachine.emit_step_cons (handler caller) d tag raw rev pending regs outputs (stores fuel bitsReverse ctx))
          apply cfg_effect
          · simp only [treeLabel, TreeParserMachine.phaseLabel, debt, List.length_cons, outputCells_update_cons]; omega
          · intro M _ slots
            exact slots
  | undo =>
      cases rev with
      | nil =>
          apply effect_of_step_eq caller executed
            (TreeParserMachine.undo_step_nil (handler caller) d raw pending regs outputs (stores fuel bitsReverse ctx))
          apply cfg_effect
          · rfl
          · intro M _ slots
            exact slots
      | cons tag rev =>
          apply effect_of_step_eq caller executed
            (TreeParserMachine.undo_step_cons (handler caller) d tag raw rev pending regs outputs (stores fuel bitsReverse ctx))
          apply cfg_effect
          · simp only [treeLabel, TreeParserMachine.phaseLabel, debt, List.length_cons]; omega
          · intro M _ slots
            exact slots
  | dropPending =>
      cases pending with
      | nil =>
          apply effect_of_step_eq caller executed
            (TreeParserMachine.dropPending_step_nil (handler caller) d raw rev regs outputs (stores fuel bitsReverse ctx))
          apply cfg_effect
          · rfl
          · intro M _ _
            rfl
      | cons token pending =>
          cases token
          apply effect_of_step_eq caller executed
            (TreeParserMachine.dropPending_step_cons (handler caller) d raw rev pending regs outputs (stores fuel bitsReverse ctx))
          apply cfg_effect
          · rfl
          · intro M _ slots
            change pending.length + 1 ≤ M + 1 at slots
            change pending.length ≤ M + 1
            omega

private theorem toReversePhase_step_effect (d : TreeSide) (raw rev : Word) (pending : List Unit)
    (regs : Registers R) (outputs : TreeSide → Word) (fuel bitsReverse : Bits)
    (ctx : ∀ k, List (Γ k)) {after : Cfg Γ Λ R}
    (executed : step caller (cfg (some (phaseLabel (toReversePhase d))) regs raw rev pending
      outputs fuel bitsReverse ctx) = some after) :
    Effect (cfg (some (phaseLabel (toReversePhase d))) regs raw rev pending outputs fuel bitsReverse ctx) after := by
  cases selected : outputs d with
  | nil =>
      have restored : Function.update outputs d [] = outputs := by
        rw [← selected, Function.update_eq_self]
      have equation := toReversePhase_step_nil caller d raw rev pending regs outputs fuel bitsReverse ctx
      rw [restored] at equation
      apply effect_of_step_eq caller executed equation
      apply cfg_effect
      · cases d <;> rfl
      · intro M _ slots
        cases d <;> exact slots
  | cons tag word =>
      have restored : Function.update outputs d (tag :: word) = outputs := by
        rw [← selected, Function.update_eq_self]
      have equation := toReversePhase_step_cons caller d tag raw rev word pending regs outputs fuel bitsReverse ctx
      rw [restored] at equation
      apply effect_of_step_eq caller executed equation
      apply cfg_effect
      · have cells := outputCells_update_transfer outputs d tag word
        rw [restored] at cells
        simp only [debt_phase, List.length_cons]
        omega
      · intro M _ slots
        exact slots

private theorem toRawPhase_step_effect (d : TreeSide) (raw rev : Word) (pending : List Unit)
    (regs : Registers R) (outputs : TreeSide → Word) (fuel bitsReverse : Bits)
    (ctx : ∀ k, List (Γ k)) {after : Cfg Γ Λ R}
    (executed : step caller (cfg (some (phaseLabel (toRawPhase d))) regs raw rev pending
      outputs fuel bitsReverse ctx) = some after) :
    Effect (cfg (some (phaseLabel (toRawPhase d))) regs raw rev pending outputs fuel bitsReverse ctx) after := by
  cases rev with
  | nil =>
      apply effect_of_step_eq caller executed
        (toRawPhase_step_nil caller d raw pending regs outputs fuel bitsReverse ctx)
      apply cfg_effect
      · cases d <;> rfl
      · intro M _ slots
        cases d <;> exact slots
  | cons tag rev =>
      apply effect_of_step_eq caller executed
        (toRawPhase_step_cons caller d tag raw rev pending regs outputs fuel bitsReverse ctx)
      apply cfg_effect
      · simp only [List.length_cons]; omega
      · intro M _ slots
        cases d <;> exact slots

private theorem separator_step_effect (d : TreeSide) (raw rev : Word) (pending : List Unit)
    (regs : Registers R) (outputs : TreeSide → Word) (fuel bitsReverse : Bits)
    (ctx : ∀ k, List (Γ k)) {after : Cfg Γ Λ R}
    (executed : step caller (cfg (some (treeResultLabel d .success)) regs raw rev pending
      outputs fuel bitsReverse ctx) = some after) :
    Effect (cfg (some (treeResultLabel d .success)) regs raw rev pending outputs fuel bitsReverse ctx) after := by
  cases raw with
  | nil =>
      apply effect_of_step_eq caller executed
        (separator_step_nil caller d rev pending regs outputs fuel bitsReverse ctx)
      apply cfg_effect
      · cases d <;> rfl
      · intro M _ slots
        cases d <;> exact slots
  | cons tag raw =>
      by_cases accepted : tag = separatorTag
      · subst tag
        apply effect_of_step_eq caller executed
          (separator_step_separator caller d raw rev pending regs outputs fuel bitsReverse ctx)
        apply cfg_effect
        · cases d <;> simp only [debt, treeResultLabel, TreeParserMachine.resultLabel,
            afterSeparator, treeLabel, TreeParserMachine.phaseLabel, phaseLabel,
            TreeParserMachine.callerLabel, sideDebt, phaseDebt, List.length_cons] <;> omega
        · intro M _ slots
          cases d <;> exact slots
      · apply effect_of_step_eq caller executed
          (separator_step_foreign caller d tag raw rev pending regs outputs fuel bitsReverse ctx accepted)
        apply cfg_effect
        · cases d <;> rfl
        · intro M _ slots
          cases d <;> exact slots

/-- Every additional literal body has an exact mass effect and preserves the protected frame. -/
theorem phase_step_effect (phase : Phase) (raw rev : Word) (pending : List Unit)
    (regs : Registers R) (outputs : TreeSide → Word) (fuel bitsReverse : Bits)
    (ctx : ∀ k, List (Γ k)) {after : Cfg Γ Λ R}
    (executed : step caller (cfg (some (phaseLabel phase)) regs raw rev pending
      outputs fuel bitsReverse ctx) = some after) :
    Effect (cfg (some (phaseLabel phase)) regs raw rev pending outputs fuel bitsReverse ctx) after := by
  cases phase with
  | bitsScan =>
      cases raw with
      | nil =>
          apply effect_of_step_eq caller executed
            (bitsScan_step_nil caller rev pending regs outputs fuel bitsReverse ctx)
          apply cfg_effect
          · rfl
          · intro M _ slots; exact slots
      | cons tag raw =>
          by_cases zero : tag = bitZeroTag
          · subst tag
            apply effect_of_step_eq caller executed
              (bitsScan_step_bit caller false raw rev pending regs outputs fuel bitsReverse ctx)
            apply cfg_effect
            · simp only [List.length_cons]; omega
            · intro M _ slots; exact slots
          · by_cases one : tag = bitOneTag
            · subst tag
              apply effect_of_step_eq caller executed
                (bitsScan_step_bit caller true raw rev pending regs outputs fuel bitsReverse ctx)
              apply cfg_effect
              · simp only [List.length_cons]; omega
              · intro M _ slots; exact slots
            · by_cases finished : tag = endInputTag
              · subst tag
                apply effect_of_step_eq caller executed
                  (bitsScan_step_end caller raw rev pending regs outputs fuel bitsReverse ctx)
                apply cfg_effect
                · simp only [debt_phase, phaseDebt, List.length_cons]; omega
                · intro M _ slots; exact slots
              · apply effect_of_step_eq caller executed
                  (bitsScan_step_foreign caller tag raw rev pending regs outputs fuel bitsReverse ctx finished zero one)
                apply cfg_effect
                · rfl
                · intro M _ slots; exact slots
  | bitsEmit =>
      cases bitsReverse with
      | nil =>
          apply effect_of_step_eq caller executed
            (bitsEmit_step_nil caller raw rev pending regs outputs fuel ctx)
          apply cfg_effect
          · rfl
          · intro M _ slots; exact slots
      | cons b bitsReverse =>
          apply effect_of_step_eq caller executed
            (bitsEmit_step_cons caller b raw rev pending regs outputs fuel bitsReverse ctx)
          apply cfg_effect
          · simp only [List.length_cons]; omega
          · intro M _ slots; exact slots
  | eof =>
      cases raw with
      | nil =>
          apply effect_of_step_eq caller executed
            (eof_step_nil caller rev pending regs outputs fuel bitsReverse ctx)
          apply cfg_effect
          · rfl
          · intro M _ slots; exact slots
      | cons tag raw =>
          apply effect_of_step_eq caller executed
            (eof_step_cons caller tag raw rev pending regs outputs fuel bitsReverse ctx)
          apply cfg_effect
          · rfl
          · intro M _ slots; exact slots
  | restoreEnd =>
      apply effect_of_step_eq caller executed
        (restoreEnd_step caller raw rev pending regs outputs fuel bitsReverse ctx)
      apply cfg_effect
      · simp only [debt_phase, phaseDebt, List.length_cons]; omega
      · intro M _ slots; exact slots
  | fuelUndo =>
      cases fuel with
      | nil =>
          apply effect_of_step_eq caller executed
            (fuelUndo_step_nil caller raw rev pending regs outputs bitsReverse ctx)
          apply cfg_effect
          · rfl
          · intro M _ slots; exact slots
      | cons b fuel =>
          apply effect_of_step_eq caller executed
            (fuelUndo_step_cons caller b raw rev pending regs outputs fuel bitsReverse ctx)
          apply cfg_effect
          · simp only [List.length_cons]; omega
          · intro M _ slots; exact slots
  | bitsUndo =>
      cases bitsReverse with
      | nil =>
          apply effect_of_step_eq caller executed
            (bitsUndo_step_nil caller raw rev pending regs outputs fuel ctx)
          apply cfg_effect
          · rfl
          · intro M _ slots; exact slots
      | cons b bitsReverse =>
          apply effect_of_step_eq caller executed
            (bitsUndo_step_cons caller b raw rev pending regs outputs fuel bitsReverse ctx)
          apply cfg_effect
          · simp only [List.length_cons]; omega
          · intro M _ slots; exact slots
  | restoreSep2 =>
      apply effect_of_step_eq caller executed
        (restoreSep2_step caller raw rev pending regs outputs fuel bitsReverse ctx)
      apply cfg_effect
      · simp only [debt_phase, phaseDebt, List.length_cons]; omega
      · intro M _ slots; exact slots
  | targetToReverse => exact toReversePhase_step_effect caller .target raw rev pending regs outputs fuel bitsReverse ctx executed
  | sourceToReverse => exact toReversePhase_step_effect caller .source raw rev pending regs outputs fuel bitsReverse ctx executed
  | targetToRaw => exact toRawPhase_step_effect caller .target raw rev pending regs outputs fuel bitsReverse ctx executed
  | sourceToRaw => exact toRawPhase_step_effect caller .source raw rev pending regs outputs fuel bitsReverse ctx executed
  | restoreSep1 =>
      apply effect_of_step_eq caller executed
        (restoreSep1_step caller raw rev pending regs outputs fuel bitsReverse ctx)
      apply cfg_effect
      · simp only [debt_phase, phaseDebt, List.length_cons]; omega
      · intro M _ slots; exact slots

private theorem cfg_step_effect (label : Option (Label Λ)) (raw rev : Word) (pending : List Unit)
    (regs : Registers R) (outputs : TreeSide → Word) (fuel bitsReverse : Bits)
    (ctx : ∀ k, List (Γ k)) {after : Cfg Γ Λ R} (owned : FullOwned label)
    (executed : step caller (cfg label regs raw rev pending outputs fuel bitsReverse ctx) = some after) :
    Effect (cfg label regs raw rev pending outputs fuel bitsReverse ctx) after := by
  cases label with
  | none => cases owned
  | some label =>
      cases label with
      | inl pair =>
          rcases pair with ⟨d, phase⟩
          exact tree_step_effect caller d phase raw rev pending regs outputs fuel bitsReverse ctx executed
      | inr external =>
          cases external with
          | inl pair =>
              rcases pair with ⟨d, result⟩
              cases result with
              | success => exact separator_step_effect caller d raw rev pending regs outputs fuel bitsReverse ctx executed
              | failure =>
                  cases d with
                  | source => cases owned
                  | target =>
                      apply effect_of_step_eq caller executed
                        (target_failure_step caller raw rev pending regs outputs fuel bitsReverse ctx)
                      apply cfg_effect
                      · change (raw.length + 1) + rev.length + outputCells outputs + fuel.length +
                          bitsReverse.length + 0 =
                            raw.length + rev.length + outputCells outputs + fuel.length + bitsReverse.length + 1
                        omega
                      · intro M _ slots; exact slots
          | inr extra =>
              cases extra with
              | inl phase => exact phase_step_effect caller phase raw rev pending regs outputs fuel bitsReverse ctx executed
              | inr exit => cases owned

/-- A local theorem about actual full-owned steps, including states with dirty accumulators. -/
theorem step_effect {before after : Cfg Γ Λ R} (owned : FullOwned before.l)
    (executed : step caller before = some after) : Effect before after := by
  have reconstructed := cfg_eta before
  have explicitStep : step caller
      (cfg before.l before.var (before.stk rawStack) (before.stk reverseStack) (before.stk pendingStack)
        (fun d => before.stk (outputStack d)) (before.stk fuelStack) (before.stk bitsReverseStack)
        (fun k => before.stk (protectedStack k))) = some after := by
    rw [reconstructed]
    exact executed
  have effect := cfg_step_effect caller before.l (before.stk rawStack) (before.stk reverseStack)
    (before.stk pendingStack) before.var (fun d => before.stk (outputStack d))
    (before.stk fuelStack) (before.stk bitsReverseStack) (fun k => before.stk (protectedStack k)) owned explicitStep
  simpa only [reconstructed] using effect

theorem Runs.mass {n : Nat} {start final : Cfg Γ Λ R} (run : Runs caller n start final) :
    baseCells final + debt final.l = baseCells start + debt start.l := by
  induction run with
  | refl c => rfl
  | cons owned executed run ih => exact ih.trans (step_effect caller owned executed).mass

theorem Runs.frame {n : Nat} {start final : Cfg Γ Λ R} (run : Runs caller n start final) :
    ∀ k, final.stk (protectedStack k) = start.stk (protectedStack k) := by
  induction run with
  | refl c => exact fun _ => rfl
  | cons owned executed run ih =>
      intro k
      exact (ih k).trans ((step_effect caller owned executed).frame k)

theorem Runs.registers {n : Nat} {start final : Cfg Γ Λ R} (run : Runs caller n start final) :
    final.var = if n = 0 then start.var else reset start.var := by
  induction run with
  | refl c => rfl
  | @cons n start middle final owned executed run ih =>
      change final.var = reset start.var
      rw [ih, (step_effect caller owned executed).registers]
      split <;> rfl

theorem Runs.pending {n : Nat} {start final : Cfg Γ Λ R} (run : Runs caller n start final)
    {M : Nat} (mass : baseCells start + debt start.l = M) (slots : PendingControl M start) :
    PendingControl M final := by
  induction run generalizing M with
  | refl c => exact slots
  | cons owned executed run ih =>
      have effect := step_effect caller owned executed
      exact ih (effect.mass.trans mass) (effect.pending M mass slots)

/-- Exact preserved state at every prefix, including the first live handoff and the unreset zero prefix. -/
theorem prefix_preserves (raw : Word) (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (n : Nat) (bound : n ≤ inputSteps raw) (reached : Cfg Γ Λ R)
    (executed : (next caller)^[n] (some (entry regs raw ctx)) = some reached) :
    reached.var = (if n = 0 then regs else reset regs) ∧
      (∀ k, reached.stk (protectedStack k) = ctx k) ∧
      baseCells reached + debt reached.l = raw.length ∧ PendingControl raw.length reached := by
  obtain ⟨actual, equation, before, _, _⟩ := run_prefix caller raw regs ctx n bound
  have equal : actual = reached := Option.some.inj (equation.symm.trans executed)
  subst reached
  have initialMass : baseCells (entry (Λ := Λ) regs raw ctx) + debt (entry (Λ := Λ) regs raw ctx).l = raw.length := rfl
  refine ⟨before.registers caller, before.frame caller, (before.mass caller).trans initialMass, ?_⟩
  exact before.pending caller initialMass rfl

omit [DecidableEq K] in
theorem pendingControl_bound (M : Nat) (c : Cfg Γ Λ R) (slots : PendingControl M c) :
    (c.stk pendingStack).length ≤ M + 1 := by
  unfold PendingControl PendingCondition at slots
  split at slots
  · omega
  · exact slots
  · exact slots
  · rw [slots]
    exact Nat.zero_le _

omit [DecidableEq K] in
theorem pendingControl_empty (M : Nat) (c : Cfg Γ Λ R) (slots : PendingControl M c)
    (outside : ¬ TreeParserMachine.Owned c.l) : c.stk pendingStack = [] := by
  cases labelEq : c.l with
  | none => simpa only [PendingControl, PendingCondition, labelEq] using slots
  | some label =>
      cases label with
      | inl pair => exact False.elim (outside (by simp only [labelEq, TreeParserMachine.Owned]))
      | inr external => simpa only [PendingControl, PendingCondition, labelEq] using slots

theorem prefix_pending_empty (raw : Word) (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (n : Nat) (bound : n ≤ inputSteps raw) (reached : Cfg Γ Λ R)
    (executed : (next caller)^[n] (some (entry regs raw ctx)) = some reached)
    (outside : ¬ TreeParserMachine.Owned reached.l) : reached.stk pendingStack = [] :=
  pendingControl_empty raw.length reached (prefix_preserves caller raw regs ctx n bound reached executed).2.2.2 outside

section Space
variable [Fintype K]

def contextCells (ctx : ∀ k, List (Γ k)) : Nat := ∑ k, (ctx k).length

/-- The cells of all seven owned stacks plus every protected caller stack. -/
def stackCells (c : Cfg Γ Λ R) : Nat :=
  baseCells c + (c.stk pendingStack).length + contextCells (fun k => c.stk (protectedStack k))

theorem prefix_stackCells_le (raw : Word) (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (n : Nat) (bound : n ≤ inputSteps raw) (reached : Cfg Γ Λ R)
    (executed : (next caller)^[n] (some (entry regs raw ctx)) = some reached) :
    stackCells reached ≤ 2 * raw.length + contextCells ctx + 1 := by
  obtain ⟨_, frame, mass, slots⟩ := prefix_preserves caller raw regs ctx n bound reached executed
  have pendingBound := pendingControl_bound raw.length reached slots
  have sameContext : (fun k => reached.stk (protectedStack k)) = ctx := funext frame
  have baseBound : baseCells reached ≤ raw.length := by omega
  calc
    stackCells reached = baseCells reached + (reached.stk pendingStack).length + contextCells ctx := by
      unfold stackCells
      rw [sameContext]
    _ ≤ raw.length + (raw.length + 1) + contextCells ctx :=
      Nat.add_le_add_right (Nat.add_le_add baseBound pendingBound) _
    _ = 2 * raw.length + contextCells ctx + 1 := by omega

end Space

section SharpSpace
variable [Fintype K]

/-- An actual prefix attains the universal cell bound for every raw length. -/
theorem nodes_prefix_sharp (count : Nat) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ∃ reached,
      (next caller)^[count + 1] (some (entry regs (List.replicate count nodeTag) ctx)) = some reached ∧
      count + 1 < inputSteps (List.replicate count nodeTag) ∧
      stackCells reached = 2 * count + contextCells ctx + 1 := by
  refine ⟨_, nodes_prefix caller count regs ctx, ?_, ?_⟩
  · rw [inputSteps_nodes]
    omega
  · change 0 + (List.replicate count nodeTag).length + 0 + 0 + 0 +
      (List.replicate (count + 1) ()).length + contextCells ctx = _
    simp only [List.length_replicate]
    omega

end SharpSpace


section FinitePackage

/-- A finite presentation of exactly the owned labels; external callers are absent. -/
abbrev OwnedLabels := (TreeSide × TreeParserMachine.Phase) ⊕ (TreeSide ⊕ (Unit ⊕ Phase))

def ownedLabelEquiv : OwnedLabels ≃ {label : Label Λ // FullOwned (some label)} where
  toFun
    | .inl (d, phase) => ⟨treeLabel d phase, fullOwned_tree d phase⟩
    | .inr (.inl d) => ⟨treeResultLabel d .success, by cases d <;> trivial⟩
    | .inr (.inr (.inl _)) => ⟨treeResultLabel .target .failure, True.intro⟩
    | .inr (.inr (.inr phase)) => ⟨phaseLabel phase, fullOwned_phase phase⟩
  invFun
    | ⟨.inl (d, phase), _⟩ => .inl (d, phase)
    | ⟨.inr (.inl (d, .success)), _⟩ => .inr (.inl d)
    | ⟨.inr (.inl (.target, .failure)), _⟩ => .inr (.inr (.inl ()))
    | ⟨.inr (.inr (.inl phase)), _⟩ => .inr (.inr (.inr phase))
    | ⟨.inr (.inl (.source, .failure)), bad⟩ => False.elim bad
    | ⟨.inr (.inr (.inr _)), bad⟩ => False.elim bad
  left_inv label := by
    cases label with
    | inl pair => rcases pair with ⟨d, phase⟩; rfl
    | inr external =>
        cases external with
        | inl d => cases d <;> rfl
        | inr extra => cases extra with
          | inl token => cases token; rfl
          | inr phase => rfl
  right_inv label := by
    rcases label with ⟨label, owned⟩
    cases label with
    | inl pair => rcases pair with ⟨d, phase⟩; rfl
    | inr external =>
        cases external with
        | inl pair =>
            rcases pair with ⟨d, result⟩
            cases d with
            | source => cases result with
              | success => rfl
              | failure => cases owned
            | target => cases result <;> rfl
        | inr extra => cases extra with
          | inl phase => rfl
          | inr exit => cases owned

instance fullOwnedFintype : Fintype {label : Label Λ // FullOwned (some label)} :=
  Fintype.ofEquiv OwnedLabels ownedLabelEquiv

theorem fullOwned_card : Fintype.card {label : Label Λ // FullOwned (some label)} = 25 := by
  calc
    _ = Fintype.card OwnedLabels := (Fintype.card_congr ownedLabelEquiv).symm
    _ = 25 := by decide

omit [DecidableEq K] in
theorem stackId_card [Fintype K] : Fintype.card (StackId K) = 7 + Fintype.card K := by
  have localCard : Fintype.card (TreeParserMachine.LocalStack TreeSide) = 5 := by decide
  have extraCard : Fintype.card ExtraStack = 2 := by decide
  simp only [StackId, TreeParserMachine.StackId, Fintype.card_sum, localCard, extraCard]
  omega

theorem label_card [Fintype Λ] : Fintype.card (Label Λ) = 27 + Fintype.card Λ := by
  have sideCard : Fintype.card TreeSide = 2 := by decide
  have treePhaseCard : Fintype.card TreeParserMachine.Phase = 5 := by decide
  have resultCard : Fintype.card TreeParserMachine.Result = 2 := by decide
  have phaseCard : Fintype.card Phase = 12 := by decide
  simp only [Label, TreeParserMachine.Label, TreeParserMachine.External, Fintype.card_sum,
    Fintype.card_prod, Fintype.card_unit, sideCard, treePhaseCard, resultCard, phaseCard]
  omega

theorem registers_card [Fintype R] : Fintype.card (Registers R) = 34 * Fintype.card R := by
  have tagCard : Fintype.card Tag = 16 := by decide
  simp only [Registers, TreeParserMachine.Registers, TreeParserMachine.Temporaries,
    Fintype.card_prod, Fintype.card_option, Fintype.card_unit, tagCard]

variable [Fintype K] [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]

/-- One fixed finite program, chosen before raw words and protected data. Results remain live. -/
def machine (initial : R) : Turing.FinTM2 where
  K := StackId K
  k₀ := rawStack
  k₁ := fuelStack
  Γ := Alphabet Γ
  Λ := Label Λ
  main := treeLabel .source .init
  σ := Registers R
  initialState := ((none, none), initial)
  Γk₀Fin := TreeParserMachine.alphabetFintype rawStack
  m := program caller

theorem machine_step_eq (initial : R) (c : Cfg Γ Λ R) :
    (machine caller initial).step c = step caller c := rfl

theorem initList_eq (initial : R) (raw : Word) :
    Turing.initList (machine caller initial) raw = entry ((none, none), initial) raw (fun _ => []) := by
  apply cfg_ext <;> first | rfl | exact fun _ => rfl | intro d; cases d <;> rfl


end FinitePackage

end Resources.RotationCertificate.InputParserMachine
