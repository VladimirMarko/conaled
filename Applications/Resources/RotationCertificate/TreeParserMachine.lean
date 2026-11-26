import Applications.Resources.RotationCertificate.TreeParser
import Applications.Resources.BinaryCounter.FixedWidthMachine
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# An open finite-stack preorder tree parser

The actual finite blocks keep the accepted tags on a reverse stack and pending
child positions on a Unit stack. Success transfers the literal code to a selected
output; failure restores the entire original raw word and clears both scratch
stacks. Source trees, frames, counts and ranks below are proof-side objects.
Live caller labels are reached before any caller body is executed.
Correspondence: `docs/research/fdsa-rotation-certificate-preparation.md`.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.RotationCertificate.TreeParserMachine

inductive LocalStack (D : Type)
  | raw | reverse | pending | output (destination : D)
  deriving DecidableEq, Fintype

inductive Phase
  | init | scan | emit | undo | dropPending
  deriving DecidableEq

instance : Fintype Phase where
  elems := {.init, .scan, .emit, .undo, .dropPending}
  complete phase := by cases phase <;> decide

inductive Result
  | success | failure
  deriving DecidableEq

instance : Fintype Result where
  elems := {.success, .failure}
  complete result := by cases result <;> decide

abbrev StackId (D K : Type) := LocalStack D ⊕ K
abbrev External (D Λ : Type) := (D × Result) ⊕ Λ
abbrev Label (D Λ : Type) := (D × Phase) ⊕ External D Λ
abbrev Temporaries := Option Tag × Option Unit
abbrev Registers (R : Type) := Temporaries × R

variable {D K Λ R : Type} {Γ : K → Type}

abbrev Alphabet (D : Type) (Γ : K → Type) : StackId D K → Type
  | .inl .raw | .inl .reverse | .inl (.output _) => Tag
  | .inl .pending => Unit
  | .inr k => Γ k

instance alphabetFintype [∀ k, Fintype (Γ k)] (k : StackId D K) :
    Fintype (Alphabet D Γ k) := by
  cases k with
  | inl slot => cases slot <;> exact inferInstance
  | inr k => exact inferInstance

abbrev Statement (D : Type) (Γ : K → Type) (Λ R : Type) :=
  Turing.TM2.Stmt (Alphabet D Γ) (Label D Λ) (Registers R)
abbrev Cfg (D : Type) (Γ : K → Type) (Λ R : Type) :=
  Turing.TM2.Cfg (Alphabet D Γ) (Label D Λ) (Registers R)

def phaseLabel (d : D) (phase : Phase) : Label D Λ := .inl (d, phase)
def resultLabel (d : D) (result : Result) : Label D Λ := .inr (.inl (d, result))
def callerLabel (label : Λ) : Label D Λ := .inr (.inr label)

def reset (regs : Registers R) : Registers R := ((none, none), regs.2)

@[simp] theorem reset_reset (regs : Registers R) : reset (reset regs) = reset regs := rfl
def storeTag (regs : Registers R) (tag : Option Tag) : Registers R :=
  ((tag, regs.1.2), regs.2)
def storePending (regs : Registers R) (token : Option Unit) : Registers R :=
  ((regs.1.1, token), regs.2)

def jump (label : Label D Λ) : Statement D Γ Λ R :=
  .load reset (.goto (fun _ => label))

/-- Every test sees finite registers overwritten by an actual stack observation. -/
def block (d : D) : Phase → Statement D Γ Λ R
  | .init =>
      .push (.inl .pending) (fun _ => ()) (jump (phaseLabel d .scan))
  | .scan =>
      .peek (.inl .raw) storeTag (.branch (fun regs => decide (regs.1.1 = some nodeTag))
        (.pop (.inl .raw) storeTag
          (.push (.inl .reverse) (fun _ => nodeTag)
            (.push (.inl .pending) (fun _ => ()) (jump (phaseLabel d .scan)))))
        (.branch (fun regs => decide (regs.1.1 = some emptyTag))
          (.pop (.inl .raw) storeTag
            (.push (.inl .reverse) (fun _ => emptyTag)
              (.pop (.inl .pending) storePending
                (.peek (.inl .pending) storePending
                  (.branch (fun regs => regs.1.2.isSome)
                    (jump (phaseLabel d .scan)) (jump (phaseLabel d .emit)))))))
          (jump (phaseLabel d .undo))))
  | .emit =>
      .pop (.inl .reverse) storeTag (.branch (fun regs => regs.1.1.isSome)
        (.push (.inl (.output d)) (fun regs => regs.1.1.getD emptyTag)
          (jump (phaseLabel d .emit)))
        (jump (resultLabel d .success)))
  | .undo =>
      .pop (.inl .reverse) storeTag (.branch (fun regs => regs.1.1.isSome)
        (.push (.inl .raw) (fun regs => regs.1.1.getD emptyTag)
          (jump (phaseLabel d .undo)))
        (jump (phaseLabel d .dropPending)))
  | .dropPending =>
      .pop (.inl .pending) storePending (.branch (fun regs => regs.1.2.isSome)
        (jump (phaseLabel d .dropPending)) (jump (resultLabel d .failure)))

def program (caller : External D Λ → Statement D Γ Λ R) :
    Label D Λ → Statement D Γ Λ R
  | .inl (d, phase) => block d phase
  | .inr external => caller external

theorem program_eq_of_agrees (ambient : Label D Λ → Statement D Γ Λ R)
    (owned : ∀ d phase, ambient (phaseLabel d phase) = block d phase) :
    ambient = program (fun external => ambient (.inr external)) := by
  funext label
  cases label with
  | inl pair => exact owned pair.1 pair.2
  | inr external => rfl

def cfg (label : Option (Label D Λ)) (regs : Registers R) (raw rev : Word)
    (pending : List Unit) (outputs : D → Word) (ctx : ∀ k, List (Γ k)) : Cfg D Γ Λ R where
  l := label
  var := regs
  stk
    | .inl .raw => raw
    | .inl .reverse => rev
    | .inl .pending => pending
    | .inl (.output d) => outputs d
    | .inr k => ctx k

theorem cfg_ext {left right : Cfg D Γ Λ R}
    (label : left.l = right.l) (regs : left.var = right.var)
    (raw : left.stk (.inl .raw) = right.stk (.inl .raw))
    (rev : left.stk (.inl .reverse) = right.stk (.inl .reverse))
    (pending : left.stk (.inl .pending) = right.stk (.inl .pending))
    (outputs : ∀ d, left.stk (.inl (.output d)) = right.stk (.inl (.output d)))
    (ctx : ∀ k, left.stk (.inr k) = right.stk (.inr k)) : left = right := by
  have stackEq : left.stk = right.stk := by
    funext k
    cases k with
    | inl slot => cases slot with
      | raw => exact raw
      | reverse => exact rev
      | pending => exact pending
      | output d => exact outputs d
    | inr k => exact ctx k
  cases left
  cases right
  cases label
  cases regs
  cases stackEq
  rfl

theorem cfg_eta (c : Cfg D Γ Λ R) :
    cfg c.l c.var (c.stk (.inl .raw)) (c.stk (.inl .reverse))
      (c.stk (.inl .pending)) (fun d => c.stk (.inl (.output d)))
      (fun k => c.stk (.inr k)) = c := by
  apply cfg_ext <;> first | rfl | exact fun _ => rfl

variable [DecidableEq D] [DecidableEq K]

def step (caller : External D Λ → Statement D Γ Λ R) : Cfg D Γ Λ R → Option (Cfg D Γ Λ R) :=
  Turing.TM2.step (program caller)

def next (caller : External D Λ → Statement D Γ Λ R) (c : Option (Cfg D Γ Λ R)) :
    Option (Cfg D Γ Λ R) := c.bind (step caller)

@[simp] theorem next_none (caller : External D Λ → Statement D Γ Λ R) : next caller none = none := rfl
@[simp] theorem next_some (caller : External D Λ → Statement D Γ Λ R) (c : Cfg D Γ Λ R) :
    next caller (some c) = step caller c := rfl

variable (caller : External D Λ → Statement D Γ Λ R)

theorem init_step (d : D) (raw rev : Word) (pending : List Unit) (regs : Registers R)
    (outputs : D → Word) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel d .init)) regs raw rev pending outputs ctx) =
      some (cfg (some (phaseLabel d .scan)) (reset regs) raw rev (() :: pending) outputs ctx) := by
  apply congrArg some
  apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem scan_step_node (d : D) (raw rev : Word) (pending : List Unit) (regs : Registers R)
    (outputs : D → Word) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel d .scan)) regs (nodeTag :: raw) rev pending outputs ctx) =
      some (cfg (some (phaseLabel d .scan)) (reset regs) raw (nodeTag :: rev)
        (() :: pending) outputs ctx) := by
  apply congrArg some
  apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem scan_step_empty (d : D) (raw rev : Word) (pending : List Unit) (regs : Registers R)
    (outputs : D → Word) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel d .scan)) regs (emptyTag :: raw) rev pending outputs ctx) =
      some (cfg (some (phaseLabel d (if pending.tail = [] then .emit else .scan)))
        (reset regs) raw (emptyTag :: rev) pending.tail outputs ctx) := by
  cases pending with
  | nil => apply congrArg some; apply cfg_ext <;> first | rfl | exact fun _ => rfl
  | cons token pending => cases pending with
    | nil => apply congrArg some; apply cfg_ext <;> first | rfl | exact fun _ => rfl
    | cons token pending =>
        apply congrArg some
        apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem scan_step_nil (d : D) (rev : Word) (pending : List Unit) (regs : Registers R)
    (outputs : D → Word) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel d .scan)) regs [] rev pending outputs ctx) =
      some (cfg (some (phaseLabel d .undo)) (reset regs) [] rev pending outputs ctx) := by
  apply congrArg some
  apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem scan_step_foreign (d : D) (tag : Tag) (raw rev : Word) (pending : List Unit)
    (regs : Registers R) (outputs : D → Word) (ctx : ∀ k, List (Γ k))
    (notNode : tag ≠ nodeTag) (notEmpty : tag ≠ emptyTag) :
    step caller (cfg (some (phaseLabel d .scan)) regs (tag :: raw) rev pending outputs ctx) =
      some (cfg (some (phaseLabel d .undo)) (reset regs) (tag :: raw) rev pending outputs ctx) := by
  simp only [step, Turing.TM2.step, program, phaseLabel, block, Turing.TM2.stepAux,
    cfg, storeTag, List.head?_cons, jump, reset]
  simp only [Bool.cond_decide, Option.some.injEq, notNode, notEmpty, ite_false]

theorem emit_step_cons (d : D) (tag : Tag) (raw rev : Word) (pending : List Unit)
    (regs : Registers R) (outputs : D → Word) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel d .emit)) regs raw (tag :: rev) pending outputs ctx) =
      some (cfg (some (phaseLabel d .emit)) (reset regs) raw rev pending
        (Function.update outputs d (tag :: outputs d)) ctx) := by
  apply congrArg some
  apply cfg_ext <;> try rfl
  · intro other
    by_cases same : other = d
    · subst other; simp [Turing.TM2.stepAux, program, block,
        cfg, phaseLabel, storeTag, jump, reset, Function.update]
    · simp [Turing.TM2.stepAux, program, block,
        cfg, phaseLabel, storeTag, jump, reset, Function.update, same]
  · exact fun _ => rfl

theorem emit_step_nil (d : D) (raw : Word) (pending : List Unit) (regs : Registers R)
    (outputs : D → Word) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel d .emit)) regs raw [] pending outputs ctx) =
      some (cfg (some (resultLabel d .success)) (reset regs) raw [] pending outputs ctx) := by
  apply congrArg some
  apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem undo_step_cons (d : D) (tag : Tag) (raw rev : Word) (pending : List Unit)
    (regs : Registers R) (outputs : D → Word) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel d .undo)) regs raw (tag :: rev) pending outputs ctx) =
      some (cfg (some (phaseLabel d .undo)) (reset regs) (tag :: raw) rev pending outputs ctx) := by
  apply congrArg some
  apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem undo_step_nil (d : D) (raw : Word) (pending : List Unit) (regs : Registers R)
    (outputs : D → Word) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel d .undo)) regs raw [] pending outputs ctx) =
      some (cfg (some (phaseLabel d .dropPending)) (reset regs) raw [] pending outputs ctx) := by
  apply congrArg some
  apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem dropPending_step_cons (d : D) (raw rev : Word) (pending : List Unit)
    (regs : Registers R) (outputs : D → Word) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel d .dropPending)) regs raw rev (() :: pending) outputs ctx) =
      some (cfg (some (phaseLabel d .dropPending)) (reset regs) raw rev pending outputs ctx) := by
  apply congrArg some
  apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem dropPending_step_nil (d : D) (raw rev : Word) (regs : Registers R)
    (outputs : D → Word) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel d .dropPending)) regs raw rev [] outputs ctx) =
      some (cfg (some (resultLabel d .failure)) (reset regs) raw rev [] outputs ctx) := by
  apply congrArg some
  apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem iterate_step (n : Nat) (c e : Cfg D Γ Λ R) (transition : step caller c = some e) :
    (next caller)^[n + 1] (some c) = (next caller)^[n] (some e) := by
  rw [Function.iterate_succ_apply, next_some, transition]

/-- Reversal includes its actual final empty probe and the live success handoff. -/
theorem emit_iterate (d : D) (raw rev : Word) (pending : List Unit) (regs : Registers R)
    (outputs : D → Word) (ctx : ∀ k, List (Γ k)) :
    (next caller)^[rev.length + 1]
        (some (cfg (some (phaseLabel d .emit)) regs raw rev pending outputs ctx)) =
      some (cfg (some (resultLabel d .success)) (reset regs) raw [] pending
        (Function.update outputs d (rev.reverse ++ outputs d)) ctx) := by
  induction rev generalizing outputs regs with
  | nil =>
      simpa only [List.length_nil, Nat.zero_add, Function.iterate_one, next_some,
        List.reverse_nil, List.nil_append, Function.update_eq_self] using
        emit_step_nil caller d raw pending regs outputs ctx
  | cons tag rev ih =>
      rw [show (tag :: rev).length + 1 = (rev.length + 1) + 1 by rfl,
        iterate_step caller _ _ _ (emit_step_cons caller d tag raw rev pending regs outputs ctx), ih]
      simp only [reset, List.reverse_cons, List.append_assoc, List.singleton_append,
        Function.update_self, Function.update_idem]

/-- The actual reverse stack is restored above the arbitrary unread raw tail. -/
theorem undo_iterate (d : D) (raw rev : Word) (pending : List Unit) (regs : Registers R)
    (outputs : D → Word) (ctx : ∀ k, List (Γ k)) :
    (next caller)^[rev.length + 1]
        (some (cfg (some (phaseLabel d .undo)) regs raw rev pending outputs ctx)) =
      some (cfg (some (phaseLabel d .dropPending)) (reset regs)
        (rev.reverse ++ raw) [] pending outputs ctx) := by
  induction rev generalizing raw regs with
  | nil => exact undo_step_nil caller d raw pending regs outputs ctx
  | cons tag rev ih =>
      rw [show (tag :: rev).length + 1 = (rev.length + 1) + 1 by rfl,
        iterate_step caller _ _ _ (undo_step_cons caller d tag raw rev pending regs outputs ctx), ih]
      simp only [reset, List.reverse_cons, List.append_assoc, List.singleton_append]

theorem dropPending_iterate (d : D) (raw rev : Word) (pending : List Unit)
    (regs : Registers R) (outputs : D → Word) (ctx : ∀ k, List (Γ k)) :
    (next caller)^[pending.length + 1]
        (some (cfg (some (phaseLabel d .dropPending)) regs raw rev pending outputs ctx)) =
      some (cfg (some (resultLabel d .failure)) (reset regs) raw rev [] outputs ctx) := by
  induction pending generalizing regs with
  | nil => exact dropPending_step_nil caller d raw rev regs outputs ctx
  | cons token pending ih =>
      cases token
      rw [show (() :: pending).length + 1 = (pending.length + 1) + 1 by rfl,
        iterate_step caller _ _ _ (dropPending_step_cons caller d raw rev pending regs outputs ctx), ih]
      rfl

theorem undo_drop_iterate (d : D) (raw rev : Word) (pending : List Unit)
    (regs : Registers R) (outputs : D → Word) (ctx : ∀ k, List (Γ k)) :
    (next caller)^[rev.length + pending.length + 2]
        (some (cfg (some (phaseLabel d .undo)) regs raw rev pending outputs ctx)) =
      some (cfg (some (resultLabel d .failure)) (reset regs)
        (rev.reverse ++ raw) [] [] outputs ctx) := by
  rw [show rev.length + pending.length + 2 =
    (pending.length + 1) + (rev.length + 1) by omega,
    Function.iterate_add_apply, undo_iterate, dropPending_iterate]
  rfl

/-- Proof-side count of the actual scan/return path; absent from every callback. -/
def scanSteps : Word → Nat → Nat → Nat
  | [], p, k => k + p + 3
  | tag :: raw, p, k =>
      if tag = nodeTag then 1 + scanSteps raw (p + 1) (k + 1)
      else if tag = emptyTag then
        if p ≤ 1 then k + 3 else 1 + scanSteps raw (p - 1) (k + 1)
      else k + p + 3

@[simp] theorem scanSteps_nil (p k : Nat) : scanSteps [] p k = k + p + 3 := rfl

theorem scanSteps_node (raw : Word) (p k : Nat) :
    scanSteps (nodeTag :: raw) p k = 1 + scanSteps raw (p + 1) (k + 1) := by
  rw [scanSteps, ite_eq_left rfl]

theorem scanSteps_empty (raw : Word) (p k : Nat) :
    scanSteps (emptyTag :: raw) p k =
      if p ≤ 1 then k + 3 else 1 + scanSteps raw (p - 1) (k + 1) := rfl

theorem scanSteps_foreign (tag : Tag) (raw : Word) (p k : Nat)
    (notNode : tag ≠ nodeTag) (notEmpty : tag ≠ emptyTag) :
    scanSteps (tag :: raw) p k = k + p + 3 := by
  simp only [scanSteps, ite_eq_right notNode, ite_eq_right notEmpty]

theorem scanSteps_pos (raw : Word) (p k : Nat) : 0 < scanSteps raw p k := by
  induction raw generalizing p k with
  | nil => simp only [scanSteps_nil]; omega
  | cons tag raw ih =>
      simp only [scanSteps]
      split
      · have positive := ih (p + 1) (k + 1); omega
      · split
        · split
          · omega
          · have positive := ih (p - 1) (k + 1); omega
        · omega

theorem scanSteps_le (raw : Word) (p k : Nat) :
    scanSteps raw p k ≤ 3 * raw.length + k + p + 3 := by
  induction raw generalizing p k with
  | nil => simp only [scanSteps_nil, List.length_nil]; omega
  | cons tag raw ih =>
      simp only [scanSteps, List.length_cons]
      split
      · have bounded := ih (p + 1) (k + 1); omega
      · split
        · split
          · omega
          · have bounded := ih (p - 1) (k + 1); omega
        · omega

def runSteps (raw : Word) : Nat := 1 + scanSteps raw 1 0

theorem runSteps_pos (raw : Word) : 0 < runSteps raw := by unfold runSteps; omega

theorem runSteps_le (raw : Word) : runSteps raw ≤ 3 * raw.length + 5 := by
  have bounded := scanSteps_le raw 1 0
  unfold runSteps
  omega

/-- A complete tree consumes precisely one slot, retaining every outer slot. -/
theorem scanSteps_code (t : BinaryTree Unit) (rest : Word) (p k : Nat) :
    scanSteps (treeCode t ++ rest) (p + 1) k =
      if p = 0 then 2 * (treeCode t).length + k + 1
      else (treeCode t).length + scanSteps rest p (k + (treeCode t).length) := by
  induction t generalizing rest p k with
  | nil =>
      cases p with
      | zero => simp [treeCode, scanSteps_empty]; omega
      | succ p => simp [treeCode, scanSteps_empty, Nat.add_comm]
  | node a l r ihl ihr =>
      simp only [treeCode, List.cons_append, List.append_assoc, scanSteps_node]
      rw [show p + 1 + 1 = (p + 1) + 1 by rfl, ihl]
      simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false]
      rw [ihr]
      simp only [List.length_cons, List.length_append]
      split <;> rename_i condition
      · omega
      · rw [show k + 1 + (treeCode l).length + (treeCode r).length =
          k + ((treeCode l).length + (treeCode r).length + 1) by omega]
        omega

theorem runSteps_code (t : BinaryTree Unit) (rest : Word) :
    runSteps (treeCode t ++ rest) = 2 * (treeCode t).length + 2 := by
  unfold runSteps
  rw [show 1 = 0 + 1 by rfl, scanSteps_code]
  simp only [ite_true]
  omega

theorem runSteps_code_nodes (t : BinaryTree Unit) (rest : Word) :
    runSteps (treeCode t ++ rest) = 4 * t.numNodes + 4 := by
  rw [runSteps_code, treeCode_length]
  omega

def phaseSteps : Phase → Word → Word → List Unit → Nat
  | .init, raw, rev, pending => 1 + scanSteps raw (pending.length + 1) rev.length
  | .scan, raw, rev, pending => scanSteps raw pending.length rev.length
  | .emit, _, rev, _ => rev.length + 1
  | .undo, _, rev, pending => rev.length + pending.length + 2
  | .dropPending, _, _, pending => pending.length + 1

def Owned : Option (Label D Λ) → Prop
  | some (.inl _) => True
  | _ => False

def remainingSteps (c : Cfg D Γ Λ R) : Nat :=
  match c.l with
  | some (.inl (_, phase)) =>
      phaseSteps phase (c.stk (.inl .raw)) (c.stk (.inl .reverse)) (c.stk (.inl .pending))
  | _ => 0

omit [DecidableEq D] [DecidableEq K] in
theorem remainingSteps_pos_iff (c : Cfg D Γ Λ R) :
    0 < remainingSteps c ↔ Owned c.l := by
  cases labelEq : c.l with
  | none => simp [remainingSteps, Owned, labelEq]
  | some label => cases label with
    | inr external => simp [remainingSteps, Owned, labelEq]
    | inl pair =>
        rcases pair with ⟨d, phase⟩
        cases phase with
        | init => simp [remainingSteps, labelEq, phaseSteps, Owned]
        | scan =>
            simp only [remainingSteps, labelEq, phaseSteps, Owned, iff_true]
            exact scanSteps_pos _ _ _
        | emit => simp [remainingSteps, labelEq, phaseSteps, Owned]
        | undo => simp [remainingSteps, labelEq, phaseSteps, Owned]
        | dropPending => simp [remainingSteps, labelEq, phaseSteps, Owned]

omit [DecidableEq D] [DecidableEq K] in
theorem owned_cases (c : Cfg D Γ Λ R) (owned : Owned c.l) :
    ∃ d phase regs raw rev pending outputs ctx,
      c = cfg (some (phaseLabel d phase)) regs raw rev pending outputs ctx := by
  cases labelEq : c.l with
  | none => simp [Owned, labelEq] at owned
  | some label => cases label with
    | inr external => simp [Owned, labelEq] at owned
    | inl pair =>
        refine ⟨pair.1, pair.2, c.var, c.stk (.inl .raw), c.stk (.inl .reverse),
          c.stk (.inl .pending), (fun d => c.stk (.inl (.output d))),
          (fun k => c.stk (.inr k)), ?_⟩
        simpa only [labelEq, phaseLabel] using (cfg_eta c).symm

/-- Source frames are ghost witnesses; only their pending-slot count is represented. -/
def leftSlots : List TreeFrame → Nat
  | [] => 0
  | .needLeft :: outer => 1 + leftSlots outer
  | .needRight _ :: outer => leftSlots outer

theorem resumeTreeRun_slots (frames : List TreeFrame) (t : BinaryTree Unit) :
    match (resumeTreeRun frames t).1 with
    | .done _ => leftSlots frames = 0
    | .next next => leftSlots frames = 1 + leftSlots next := by
  induction frames generalizing t with
  | nil => rfl
  | cons frame outer ih =>
      cases frame with
      | needLeft => rfl
      | needRight l => exact ih (.node () l t)

theorem parseTreeLoop_empty_value (raw : Word) (frames : List TreeFrame) :
    (parseTreeLoop (emptyTag :: raw) frames).1 =
      match (resumeTreeRun frames .nil).1 with
      | .done t => some (t, raw)
      | .next next => (parseTreeLoop raw next).1 := by
  change (bind (resumeTreeRun frames .nil) (fun result => match result with
      | .done t => (some (t, raw), 1)
      | .next next => parseTreeLoop raw next)).1 = _
  cases resumed : (resumeTreeRun frames .nil).1 <;> simp only [bind, resumed]

/-- A proof-facing source continuation value, never evaluated by the finite blocks. -/
def resumeTreeValue (frames : List TreeFrame) (t : BinaryTree Unit) (rest : Word) :
    Option (BinaryTree Unit × Word) :=
  match (resumeTreeRun frames t).1 with
  | .done u => some (u, rest)
  | .next nextFrames => (parseTreeLoop rest nextFrames).1

theorem parseTreeLoop_code_value (t : BinaryTree Unit) (rest : Word) (frames : List TreeFrame) :
    (parseTreeLoop (treeCode t ++ rest) frames).1 = resumeTreeValue frames t rest := by
  induction t generalizing frames rest with
  | nil => exact parseTreeLoop_empty_value rest frames
  | node a l r ihl ihr =>
      cases a
      simp only [treeCode, List.cons_append, List.append_assoc, parseTreeLoop_node]
      rw [ihl]
      change (parseTreeLoop (treeCode r ++ rest) (.needRight l :: frames)).1 = _
      rw [ihr]
      rfl

/-- This endpoint description is a specification, never called by a statement. -/
def resultCfg (d : D) (regs : Registers R) (original : Word) (outputs : D → Word)
    (ctx : ∀ k, List (Γ k)) : Option (BinaryTree Unit × Word) → Cfg D Γ Λ R
  | none => cfg (some (resultLabel d .failure)) (reset regs) original [] [] outputs ctx
  | some (t, rest) => cfg (some (resultLabel d .success)) (reset regs) rest [] []
      (Function.update outputs d (treeCode t ++ outputs d)) ctx

omit [DecidableEq K] in
@[simp] theorem resultCfg_reset (d : D) (regs : Registers R) (original : Word)
    (outputs : D → Word) (ctx : ∀ k, List (Γ k)) (result : Option (BinaryTree Unit × Word)) :
    resultCfg (Λ := Λ) d (reset regs) original outputs ctx result =
      resultCfg d regs original outputs ctx result := by
  cases result with
  | none => rfl
  | some pair => cases pair; rfl

theorem scan_nil_iterate (d : D) (rev : Word) (pending : List Unit) (regs : Registers R)
    (outputs : D → Word) (ctx : ∀ k, List (Γ k)) :
    (next caller)^[rev.length + pending.length + 3]
        (some (cfg (some (phaseLabel d .scan)) regs [] rev pending outputs ctx)) =
      some (cfg (some (resultLabel d .failure)) (reset regs) rev.reverse [] [] outputs ctx) := by
  rw [show rev.length + pending.length + 3 = (rev.length + pending.length + 2) + 1 by omega,
    iterate_step caller _ _ _ (scan_step_nil caller d rev pending regs outputs ctx),
    undo_drop_iterate]
  simp only [reset, List.append_nil]

theorem scan_foreign_iterate (d : D) (tag : Tag) (raw rev : Word) (pending : List Unit)
    (regs : Registers R) (outputs : D → Word) (ctx : ∀ k, List (Γ k))
    (notNode : tag ≠ nodeTag) (notEmpty : tag ≠ emptyTag) :
    (next caller)^[rev.length + pending.length + 3]
        (some (cfg (some (phaseLabel d .scan)) regs (tag :: raw) rev pending outputs ctx)) =
      some (cfg (some (resultLabel d .failure)) (reset regs)
        (rev.reverse ++ tag :: raw) [] [] outputs ctx) := by
  rw [show rev.length + pending.length + 3 = (rev.length + pending.length + 2) + 1 by omega,
    iterate_step caller _ _ _ (scan_step_foreign caller d tag raw rev pending regs outputs ctx
      notNode notEmpty), undo_drop_iterate]
  rfl

/-- Every source continuation is represented by its actual prefix and a Unit slot stack. -/
theorem scan_source (d : D) (raw : Word) (frames : List TreeFrame) (regs : Registers R)
    (outputs : D → Word) (ctx : ∀ k, List (Γ k)) :
    (next caller)^[scanSteps raw (1 + leftSlots frames) (stackPrefix frames).length]
        (some (cfg (some (phaseLabel d .scan)) regs raw (stackPrefix frames).reverse
          (List.replicate (1 + leftSlots frames) ()) outputs ctx)) =
      some (resultCfg d regs (stackPrefix frames ++ raw) outputs ctx
        (parseTreeLoop raw frames).1) := by
  induction raw generalizing frames regs with
  | nil =>
      simpa only [scanSteps_nil, parseTreeLoop_nil, resultCfg, List.length_reverse,
        List.length_replicate, List.reverse_reverse, List.append_nil] using
        scan_nil_iterate caller d (stackPrefix frames).reverse
          (List.replicate (1 + leftSlots frames) ()) regs outputs ctx
  | cons tag raw ih =>
      by_cases node : tag = nodeTag
      · subst tag
        rw [scanSteps_node,
          show 1 + scanSteps raw (1 + leftSlots frames + 1) ((stackPrefix frames).length + 1) =
            scanSteps raw (1 + leftSlots frames + 1) ((stackPrefix frames).length + 1) + 1 by omega,
          iterate_step caller _ _ _ (scan_step_node caller d raw (stackPrefix frames).reverse
            (List.replicate (1 + leftSlots frames) ()) regs outputs ctx)]
        have recurse := ih (.needLeft :: frames) (reset regs)
        simpa only [stackPrefix, leftSlots, List.length_append, List.length_singleton,
          List.reverse_append, List.reverse_singleton, List.singleton_append,
          show 1 + (1 + leftSlots frames) = (1 + leftSlots frames) + 1 by omega,
          List.replicate_succ, parseTreeLoop_node, List.append_assoc,
          resultCfg_reset] using recurse
      · by_cases empty : tag = emptyTag
        · subst tag
          have slots := resumeTreeRun_slots frames .nil
          have pref := resumeTreeRun_prefix frames .nil
          cases resumed : (resumeTreeRun frames .nil).1 with
          | done t =>
              simp only [resumed] at slots
              simp only [resumed, treeCode] at pref
              rw [scanSteps_empty, slots]
              simp only [Nat.add_zero, Nat.le_refl, ite_true, List.replicate_one]
              rw [show (stackPrefix frames).length + 3 =
                ((emptyTag :: (stackPrefix frames).reverse).length + 1) + 1 by
                  simp only [List.length_cons, List.length_reverse],
                iterate_step caller _ _ _ (scan_step_empty caller d raw (stackPrefix frames).reverse
                  [()] regs outputs ctx)]
              simp only [List.tail_cons, ite_true]
              rw [emit_iterate]
              simp only [parseTreeLoop_empty_value, resumed, resultCfg, reset,
                List.reverse_cons, List.reverse_reverse, pref]
          | next nextFrames =>
              simp only [resumed] at slots
              simp only [resumed, treeCode] at pref
              have afterCount : 1 + leftSlots frames - 1 = 1 + leftSlots nextFrames := by omega
              have notLast : ¬ 1 + leftSlots frames ≤ 1 := by omega
              have prefixLength : (stackPrefix nextFrames).length =
                  (stackPrefix frames).length + 1 := by
                rw [← pref, List.length_append, List.length_singleton]
              rw [scanSteps_empty, ite_eq_right notLast, afterCount,
                show 1 + scanSteps raw (1 + leftSlots nextFrames) ((stackPrefix frames).length + 1) =
                  scanSteps raw (1 + leftSlots nextFrames) ((stackPrefix frames).length + 1) + 1 by omega,
                iterate_step caller _ _ _ (scan_step_empty caller d raw (stackPrefix frames).reverse
                  (List.replicate (1 + leftSlots frames) ()) regs outputs ctx)]
              simp only [List.tail_replicate, afterCount, List.replicate_eq_nil_iff,
                Nat.add_eq_zero_iff, Nat.one_ne_zero, false_and, ite_false]
              have recurse := ih nextFrames (reset regs)
              rw [prefixLength, ← pref] at recurse
              simpa only [List.reverse_append, List.reverse_singleton, List.singleton_append,
                List.append_assoc, parseTreeLoop_empty_value, resumed, resultCfg_reset] using recurse
        · rw [scanSteps_foreign tag raw (1 + leftSlots frames) (stackPrefix frames).length node empty,
            parseTreeLoop_foreign tag raw frames node empty]
          simpa only [resultCfg, List.length_reverse, List.length_replicate,
            List.reverse_reverse] using
            scan_foreign_iterate caller d tag raw (stackPrefix frames).reverse
              (List.replicate (1 + leftSlots frames) ()) regs outputs ctx node empty

/-- Every raw word reaches its exact source-connected live result, including restoration on failure. -/
theorem run_source (d : D) (raw : Word) (regs : Registers R) (outputs : D → Word)
    (ctx : ∀ k, List (Γ k)) :
    (next caller)^[runSteps raw]
        (some (cfg (some (phaseLabel d .init)) regs raw [] [] outputs ctx)) =
      some (resultCfg d regs raw outputs ctx (parseTreeRun raw).1) := by
  rw [runSteps, show 1 + scanSteps raw 1 0 = scanSteps raw 1 0 + 1 by omega,
    iterate_step caller _ _ _ (init_step caller d raw [] [] regs outputs ctx)]
  simpa only [stackPrefix, leftSlots, Nat.add_zero, List.length_nil, List.reverse_nil,
    List.replicate_one, List.nil_append, resultCfg_reset, parseTreeRun] using
    scan_source caller d raw [] (reset regs) outputs ctx

theorem run_of_some (d : D) (raw : Word) (t : BinaryTree Unit) (rest : Word)
    (regs : Registers R) (outputs : D → Word) (ctx : ∀ k, List (Γ k))
    (returned : (parseTreeRun raw).1 = some (t, rest)) :
    (next caller)^[runSteps raw]
        (some (cfg (some (phaseLabel d .init)) regs raw [] [] outputs ctx)) =
      some (cfg (some (resultLabel d .success)) (reset regs) rest [] []
        (Function.update outputs d (treeCode t ++ outputs d)) ctx) := by
  rw [run_source, returned]
  rfl

theorem run_of_none (d : D) (raw : Word) (regs : Registers R) (outputs : D → Word)
    (ctx : ∀ k, List (Γ k)) (returned : (parseTreeRun raw).1 = none) :
    (next caller)^[runSteps raw]
        (some (cfg (some (phaseLabel d .init)) regs raw [] [] outputs ctx)) =
      some (cfg (some (resultLabel d .failure)) (reset regs) raw [] [] outputs ctx) := by
  rw [run_source, returned]
  rfl

theorem run_code (d : D) (t : BinaryTree Unit) (rest : Word) (regs : Registers R)
    (outputs : D → Word) (ctx : ∀ k, List (Γ k)) :
    (next caller)^[2 * (treeCode t).length + 2]
        (some (cfg (some (phaseLabel d .init)) regs (treeCode t ++ rest) [] [] outputs ctx)) =
      some (cfg (some (resultLabel d .success)) (reset regs) rest [] []
        (Function.update outputs d (treeCode t ++ outputs d)) ctx) := by
  have run := run_of_some caller d (treeCode t ++ rest) t rest regs outputs ctx
    (congrArg Prod.fst (parseTreeRun_code t rest))
  simpa only [runSteps_code] using run

def runInTime (d : D) (raw : Word) (regs : Registers R) (outputs : D → Word)
    (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller)
      (cfg (some (phaseLabel d .init)) regs raw [] [] outputs ctx)
      (some (resultCfg d regs raw outputs ctx (parseTreeRun raw).1)) (runSteps raw) where
  steps := runSteps raw
  evals_in_steps := run_source caller d raw regs outputs ctx
  steps_le_m := Nat.le_refl _

def runInLinearTime (d : D) (raw : Word) (regs : Registers R) (outputs : D → Word)
    (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller)
      (cfg (some (phaseLabel d .init)) regs raw [] [] outputs ctx)
      (some (resultCfg d regs raw outputs ctx (parseTreeRun raw).1)) (3 * raw.length + 5) where
  steps := runSteps raw
  evals_in_steps := run_source caller d raw regs outputs ctx
  steps_le_m := runSteps_le raw

/-- The selected destination is retained through the live result label. -/
def destination (c : Cfg D Γ Λ R) : Option D :=
  match c.l with
  | some (.inl (d, _)) | some (.inr (.inl (d, _))) => some d
  | _ => none

/-- All owned states, including corrupt scratch states, make one exact rank step. -/
theorem phase_step_data (d : D) (phase : Phase) (raw rev : Word) (pending : List Unit)
    (regs : Registers R) (outputs : D → Word) (ctx : ∀ k, List (Γ k)) :
    ∃ reached,
      step caller (cfg (some (phaseLabel d phase)) regs raw rev pending outputs ctx) = some reached ∧
      phaseSteps phase raw rev pending = remainingSteps reached + 1 ∧
      reached.var = reset regs ∧ destination reached = some d ∧
      (∀ other, other ≠ d → reached.stk (.inl (.output other)) = outputs other) ∧
      (∀ k, reached.stk (.inr k) = ctx k) := by
  cases phase with
  | init =>
      refine ⟨_, init_step caller d raw rev pending regs outputs ctx, ?_, rfl, rfl,
        fun _ _ => rfl, fun _ => rfl⟩
      simp only [phaseSteps, remainingSteps, cfg, phaseLabel, List.length_cons]
      omega
  | scan =>
      cases raw with
      | nil =>
          refine ⟨_, scan_step_nil caller d rev pending regs outputs ctx, ?_, rfl, rfl,
            fun _ _ => rfl, fun _ => rfl⟩
          simp only [phaseSteps, remainingSteps, cfg, phaseLabel, scanSteps_nil]
      | cons tag raw =>
          by_cases node : tag = nodeTag
          · subst tag
            refine ⟨_, scan_step_node caller d raw rev pending regs outputs ctx, ?_, rfl, rfl,
              fun _ _ => rfl, fun _ => rfl⟩
            simp only [phaseSteps, remainingSteps, cfg, phaseLabel, scanSteps_node, List.length_cons]
            omega
          · by_cases empty : tag = emptyTag
            · subst tag
              cases pending with
              | nil =>
                  refine ⟨_, scan_step_empty caller d raw rev [] regs outputs ctx, ?_, rfl, rfl,
                    fun _ _ => rfl, fun _ => rfl⟩
                  simp [phaseSteps, remainingSteps, cfg, phaseLabel, scanSteps_empty]
              | cons token pending =>
                  cases token
                  cases pending with
                  | nil =>
                      refine ⟨_, scan_step_empty caller d raw rev [()] regs outputs ctx, ?_, rfl, rfl,
                        fun _ _ => rfl, fun _ => rfl⟩
                      simp [phaseSteps, remainingSteps, cfg, phaseLabel, scanSteps_empty]
                  | cons token pending =>
                      cases token
                      refine ⟨_, scan_step_empty caller d raw rev (() :: () :: pending) regs outputs ctx,
                        ?_, rfl, rfl, fun _ _ => rfl, fun _ => rfl⟩
                      simp only [phaseSteps, remainingSteps, cfg, phaseLabel, scanSteps_empty,
                        List.tail_cons, List.cons_ne_nil, ite_false, List.length_cons]
                      rw [ite_eq_right (show ¬ pending.length + 1 + 1 ≤ 1 by omega),
                        show pending.length + 1 + 1 - 1 = pending.length + 1 by omega]
                      omega
            · refine ⟨_, scan_step_foreign caller d tag raw rev pending regs outputs ctx node empty,
                ?_, rfl, rfl, fun _ _ => rfl, fun _ => rfl⟩
              simp only [phaseSteps, remainingSteps, cfg, phaseLabel,
                scanSteps_foreign tag raw pending.length rev.length node empty]
  | emit =>
      cases rev with
      | nil =>
          refine ⟨_, emit_step_nil caller d raw pending regs outputs ctx, ?_, rfl, rfl,
            fun _ _ => rfl, fun _ => rfl⟩
          rfl
      | cons tag rev =>
          refine ⟨_, emit_step_cons caller d tag raw rev pending regs outputs ctx, ?_, rfl, rfl,
            ?_, fun _ => rfl⟩
          · rfl
          · intro other different
            exact Function.update_of_ne different _ _
  | undo =>
      cases rev with
      | nil =>
          refine ⟨_, undo_step_nil caller d raw pending regs outputs ctx, ?_, rfl, rfl,
            fun _ _ => rfl, fun _ => rfl⟩
          simp only [phaseSteps, remainingSteps, cfg, phaseLabel, List.length_nil]
          omega
      | cons tag rev =>
          refine ⟨_, undo_step_cons caller d tag raw rev pending regs outputs ctx, ?_, rfl, rfl,
            fun _ _ => rfl, fun _ => rfl⟩
          simp only [phaseSteps, remainingSteps, cfg, phaseLabel, List.length_cons]
          omega
  | dropPending =>
      cases pending with
      | nil =>
          refine ⟨_, dropPending_step_nil caller d raw rev regs outputs ctx, ?_, rfl, rfl,
            fun _ _ => rfl, fun _ => rfl⟩
          rfl
      | cons token pending =>
          cases token
          refine ⟨_, dropPending_step_cons caller d raw rev pending regs outputs ctx, ?_, rfl, rfl,
            fun _ _ => rfl, fun _ => rfl⟩
          rfl

def LocalStep (before after : Cfg D Γ Λ R) : Prop :=
  Owned before.l ∧ step caller before = some after

theorem local_step_data {before after : Cfg D Γ Λ R}
    (transition : LocalStep caller before after) :
    remainingSteps before = remainingSteps after + 1 ∧
      after.var = reset before.var ∧ destination after = destination before ∧
      (∀ other, destination before ≠ some other →
        after.stk (.inl (.output other)) = before.stk (.inl (.output other))) ∧
      (∀ k, after.stk (.inr k) = before.stk (.inr k)) := by
  obtain ⟨d, phase, regs, raw, rev, pending, outputs, ctx, rfl⟩ := owned_cases before transition.1
  obtain ⟨reached, executed, rank, registers, dest, otherOutputs, frame⟩ :=
    phase_step_data caller d phase raw rev pending regs outputs ctx
  have equal : reached = after := Option.some.inj (executed.symm.trans transition.2)
  subst after
  refine ⟨rank, registers, dest, ?_, frame⟩
  intro other different
  apply otherOutputs other
  intro equal
  subst other
  exact different rfl

theorem local_progress (before : Cfg D Γ Λ R) (positive : 0 < remainingSteps before) :
    ∃ after, step caller before = some after ∧ remainingSteps before = remainingSteps after + 1 := by
  obtain ⟨d, phase, regs, raw, rev, pending, outputs, ctx, rfl⟩ :=
    owned_cases before ((remainingSteps_pos_iff before).mp positive)
  obtain ⟨after, executed, rank, _⟩ := phase_step_data caller d phase raw rev pending regs outputs ctx
  exact ⟨after, executed, rank⟩

theorem step_caller_independent (other : External D Λ → Statement D Γ Λ R)
    (c : Cfg D Γ Λ R) (owned : Owned c.l) : step caller c = step other c := by
  obtain ⟨d, phase, regs, raw, rev, pending, outputs, ctx, rfl⟩ := owned_cases c owned
  rfl

theorem prefix_local_register (n : Nat) (start reached : Cfg D Γ Λ R)
    (bound : n ≤ remainingSteps start)
    (executed : (next caller)^[n] (some start) = some reached)
    (positive : 0 < n) : reached.var.1 = (none, none) := by
  induction n generalizing start reached with
  | zero => omega
  | succ n ih =>
      have rankPositive : 0 < remainingSteps start := by omega
      obtain ⟨middle, first, decreased⟩ := local_progress caller start rankPositive
      have owned := (remainingSteps_pos_iff start).mp rankPositive
      have canonical := (local_step_data caller ⟨owned, first⟩).2.1
      rw [Function.iterate_succ_apply, next_some, first] at executed
      by_cases empty : n = 0
      · subst n
        have equal : middle = reached := Option.some.inj executed
        rw [← equal, canonical]
        rfl
      · exact ih middle reached (by omega) executed (by omega)

theorem phase_prefix (d : D) (phase : Phase) (raw rev : Word) (pending : List Unit)
    (regs : Registers R) (outputs : D → Word) (ctx : ∀ k, List (Γ k)) (n : Nat)
    (bound : n ≤ phaseSteps phase raw rev pending) :
    ∃ reached,
      (next caller)^[n] (some (cfg (some (phaseLabel d phase)) regs raw rev pending outputs ctx)) =
        some reached ∧
      remainingSteps reached = phaseSteps phase raw rev pending - n ∧
      Relation.ReflTransGen (LocalStep caller)
        (cfg (some (phaseLabel d phase)) regs raw rev pending outputs ctx) reached ∧
      (n < phaseSteps phase raw rev pending ↔ Owned reached.l) ∧
      (0 < n → reached.var.1 = (none, none)) := by
  obtain ⟨reached, executed, rank, path⟩ := Resources.BinaryCounter.FixedWidthMachine.ranked_prefix
    (step caller) remainingSteps (local_progress caller) n
    (cfg (some (phaseLabel d phase)) regs raw rev pending outputs ctx) bound
  change remainingSteps reached = phaseSteps phase raw rev pending - n at rank
  refine ⟨reached, executed, rank, ?_, ?_, ?_⟩
  · exact Relation.ReflTransGen.mono
      (fun before _ h => ⟨(remainingSteps_pos_iff before).mp h.1, h.2⟩) _ _ path
  · rw [← remainingSteps_pos_iff, rank]
    omega
  · exact prefix_local_register caller n
      (cfg (some (phaseLabel d phase)) regs raw rev pending outputs ctx) reached bound executed

theorem run_prefix (d : D) (raw : Word) (regs : Registers R) (outputs : D → Word)
    (ctx : ∀ k, List (Γ k)) (n : Nat) (bound : n ≤ runSteps raw) :
    ∃ reached,
      (next caller)^[n] (some (cfg (some (phaseLabel d .init)) regs raw [] [] outputs ctx)) =
        some reached ∧
      remainingSteps reached = runSteps raw - n ∧
      Relation.ReflTransGen (LocalStep caller)
        (cfg (some (phaseLabel d .init)) regs raw [] [] outputs ctx) reached ∧
      (n < runSteps raw ↔ Owned reached.l) ∧ (0 < n → reached.var.1 = (none, none)) := by
  exact phase_prefix caller d .init raw [] [] regs outputs ctx n bound

theorem phase_prefix_caller_independent (other : External D Λ → Statement D Γ Λ R)
    (d : D) (phase : Phase) (raw rev : Word) (pending : List Unit)
    (regs : Registers R) (outputs : D → Word) (ctx : ∀ k, List (Γ k)) (n : Nat)
    (bound : n ≤ phaseSteps phase raw rev pending) :
    (next caller)^[n] (some (cfg (some (phaseLabel d phase)) regs raw rev pending outputs ctx)) =
      (next other)^[n] (some (cfg (some (phaseLabel d phase)) regs raw rev pending outputs ctx)) := by
  exact Resources.BinaryCounter.FixedWidthMachine.ranked_prefix_eq
    (step caller) (step other) remainingSteps (local_progress caller)
    (fun c positive => step_caller_independent caller other c ((remainingSteps_pos_iff c).mp positive))
    n _ bound

theorem local_reaches_preserves {start reached : Cfg D Γ Λ R}
    (path : Relation.ReflTransGen (LocalStep caller) start reached) :
    reached.var.2 = start.var.2 ∧ destination reached = destination start ∧
      (∀ other, destination start ≠ some other →
        reached.stk (.inl (.output other)) = start.stk (.inl (.output other))) ∧
      (∀ k, reached.stk (.inr k) = start.stk (.inr k)) := by
  induction path with
  | refl => exact ⟨rfl, rfl, fun _ _ => rfl, fun _ => rfl⟩
  | @tail before after _ transition ih =>
      obtain ⟨_, registers, dest, outputs, frame⟩ := local_step_data caller transition
      refine ⟨?_, dest.trans ih.2.1, ?_, fun k => (frame k).trans (ih.2.2.2 k)⟩
      · simpa only [registers, reset] using ih.1
      · intro other different
        exact (outputs other (by simpa only [ih.2.1] using different)).trans (ih.2.2.1 other different)

theorem prefix_preserves (d : D) (phase : Phase) (raw rev : Word) (pending : List Unit)
    (regs : Registers R) (outputs : D → Word) (ctx : ∀ k, List (Γ k))
    (n : Nat) (reached : Cfg D Γ Λ R) (bound : n ≤ phaseSteps phase raw rev pending)
    (executed : (next caller)^[n]
      (some (cfg (some (phaseLabel d phase)) regs raw rev pending outputs ctx)) = some reached) :
    reached.var.2 = regs.2 ∧ destination reached = some d ∧
      (∀ other, other ≠ d → reached.stk (.inl (.output other)) = outputs other) ∧
      (∀ k, reached.stk (.inr k) = ctx k) := by
  obtain ⟨actual, run, _, path, _, _⟩ :=
    phase_prefix caller d phase raw rev pending regs outputs ctx n bound
  have equal : actual = reached := Option.some.inj (run.symm.trans executed)
  subst reached
  obtain ⟨registers, dest, otherOutputs, frame⟩ := local_reaches_preserves caller path
  refine ⟨registers, dest, ?_, frame⟩
  intro other different
  apply otherOutputs other
  change some d ≠ some other
  intro equal
  exact different (Option.some.inj equal).symm

/-- Every partial transfer preserves the exact physical word orientation. -/
theorem emit_prefix (d : D) (raw accepted rest : Word) (pending : List Unit)
    (regs : Registers R) (outputs : D → Word) (ctx : ∀ k, List (Γ k)) :
    (next caller)^[accepted.length]
        (some (cfg (some (phaseLabel d .emit)) regs raw (accepted ++ rest) pending outputs ctx)) =
      some (cfg (some (phaseLabel d .emit)) (if accepted = [] then regs else reset regs)
        raw rest pending (Function.update outputs d (accepted.reverse ++ outputs d)) ctx) := by
  induction accepted generalizing regs outputs with
  | nil => simp only [List.length_nil, Function.iterate_zero_apply, List.nil_append,
      ite_true, List.reverse_nil, Function.update_eq_self]
  | cons tag accepted ih =>
      rw [List.length_cons, List.cons_append,
        iterate_step caller _ _ _ (emit_step_cons caller d tag raw (accepted ++ rest)
          pending regs outputs ctx), ih]
      simp only [List.cons_ne_nil, ite_false, reset_reset, ite_self, List.reverse_cons,
        List.append_assoc, List.singleton_append, Function.update_self, Function.update_idem]

theorem undo_prefix (d : D) (raw accepted rest : Word) (pending : List Unit)
    (regs : Registers R) (outputs : D → Word) (ctx : ∀ k, List (Γ k)) :
    (next caller)^[accepted.length]
        (some (cfg (some (phaseLabel d .undo)) regs raw (accepted ++ rest) pending outputs ctx)) =
      some (cfg (some (phaseLabel d .undo)) (if accepted = [] then regs else reset regs)
        (accepted.reverse ++ raw) rest pending outputs ctx) := by
  induction accepted generalizing raw regs with
  | nil => rfl
  | cons tag accepted ih =>
      rw [List.length_cons, List.cons_append,
        iterate_step caller _ _ _ (undo_step_cons caller d tag raw (accepted ++ rest)
          pending regs outputs ctx), ih]
      simp only [List.cons_ne_nil, ite_false, reset_reset, ite_self, List.reverse_cons,
        List.append_assoc, List.singleton_append]

theorem dropPending_prefix (d : D) (raw rev : Word) (accepted rest : List Unit)
    (regs : Registers R) (outputs : D → Word) (ctx : ∀ k, List (Γ k)) :
    (next caller)^[accepted.length]
        (some (cfg (some (phaseLabel d .dropPending)) regs raw rev (accepted ++ rest) outputs ctx)) =
      some (cfg (some (phaseLabel d .dropPending)) (if accepted = [] then regs else reset regs)
        raw rev rest outputs ctx) := by
  induction accepted generalizing regs with
  | nil => rfl
  | cons token accepted ih =>
      cases token
      rw [List.length_cons, List.cons_append,
        iterate_step caller _ _ _ (dropPending_step_cons caller d raw rev (accepted ++ rest)
          regs outputs ctx), ih]
      simp only [List.cons_ne_nil, ite_false, reset_reset, ite_self]

/-- Independent proof evidence for a still-incomplete preorder prefix. -/
inductive OpenPrefix : Word → Nat → Prop where
  | nil : OpenPrefix [] 1
  | node {accepted : Word} {p : Nat} :
      OpenPrefix accepted p → OpenPrefix (accepted ++ [nodeTag]) (p + 1)
  | empty {accepted : Word} {p : Nat} :
      OpenPrefix accepted (p + 2) → OpenPrefix (accepted ++ [emptyTag]) (p + 1)

theorem openPrefix_bounds {accepted : Word} {p : Nat} (opened : OpenPrefix accepted p) :
    0 < p ∧ p ≤ accepted.length + 1 := by
  induction opened with
  | nil => simp
  | node opened ih => simp only [List.length_append, List.length_singleton]; omega
  | empty opened ih => simp only [List.length_append, List.length_singleton]; omega

/-- Neither this relation nor the source frames occur in a runtime callback. -/
theorem openPrefix_frames {accepted : Word} {p : Nat} (opened : OpenPrefix accepted p) :
    ∃ frames : List TreeFrame,
      stackPrefix frames = accepted ∧ p = 1 + leftSlots frames ∧
        ∀ rest, (parseTreeRun (accepted ++ rest)).1 = (parseTreeLoop rest frames).1 := by
  induction opened with
  | nil => exact ⟨[], rfl, rfl, fun _ => rfl⟩
  | @node accepted p opened ih =>
      obtain ⟨frames, prefixEq, slots, source⟩ := ih
      refine ⟨.needLeft :: frames, ?_, ?_, ?_⟩
      · simp only [stackPrefix, prefixEq]
      · simp only [leftSlots]; omega
      · intro rest
        rw [List.append_assoc, List.singleton_append, source, parseTreeLoop_node]
  | @empty accepted p opened ih =>
      obtain ⟨frames, prefixEq, slots, source⟩ := ih
      have resumedSlots := resumeTreeRun_slots frames .nil
      have resumedPrefix := resumeTreeRun_prefix frames .nil
      cases resumed : (resumeTreeRun frames .nil).1 with
      | done t =>
          simp only [resumed] at resumedSlots
          omega
      | next nextFrames =>
          simp only [resumed] at resumedSlots
          simp only [resumed, treeCode, prefixEq] at resumedPrefix
          refine ⟨nextFrames, resumedPrefix.symm, ?_, ?_⟩
          · omega
          · intro rest
            rw [List.append_assoc, List.singleton_append, source,
              parseTreeLoop_empty_value, resumed]

theorem scanSteps_openPrefix {accepted : Word} {p : Nat} (opened : OpenPrefix accepted p)
    (raw : Word) (k : Nat) :
    scanSteps (accepted ++ raw) 1 k = accepted.length + scanSteps raw p (k + accepted.length) := by
  induction opened generalizing raw k with
  | nil => simp only [List.nil_append, List.length_nil, Nat.add_zero, Nat.zero_add]
  | @node accepted p opened ih =>
      rw [List.append_assoc, List.singleton_append, ih, scanSteps_node]
      simp only [List.length_append, List.length_singleton, Nat.add_assoc]
  | @empty accepted p opened ih =>
      rw [List.append_assoc, List.singleton_append, ih, scanSteps_empty,
        ite_eq_right (show ¬ p + 2 ≤ 1 by omega), show p + 2 - 1 = p + 1 by omega]
      simp only [List.length_append, List.length_singleton, Nat.add_assoc]

/-- A rejection probe sees EOF or a foreign tag and consumes neither. -/
def Blocked : Word → Prop
  | [] => True
  | tag :: _ => tag ≠ nodeTag ∧ tag ≠ emptyTag

theorem runSteps_openPrefix {accepted rest : Word} {p : Nat}
    (opened : OpenPrefix accepted p) (blocked : Blocked rest) :
    runSteps (accepted ++ rest) = 2 * accepted.length + p + 4 := by
  rw [runSteps, scanSteps_openPrefix opened]
  cases rest with
  | nil => rw [scanSteps_nil]; omega
  | cons tag rest =>
      rw [scanSteps_foreign tag rest p (0 + accepted.length) blocked.1 blocked.2]
      omega

theorem parseTreeRun_none_of_openPrefix {accepted rest : Word} {p : Nat}
    (opened : OpenPrefix accepted p) (blocked : Blocked rest) :
    (parseTreeRun (accepted ++ rest)).1 = none := by
  obtain ⟨frames, _, _, source⟩ := openPrefix_frames opened
  rw [source]
  cases rest with
  | nil => rfl
  | cons tag rest => rw [parseTreeLoop_foreign tag rest frames blocked.1 blocked.2]

/-- Every failed source continuation extends a proper prefix to its actual first blocked head. -/
theorem parseTreeLoop_none_openPrefix (raw : Word) (frames : List TreeFrame) (accepted : Word)
    (opened : OpenPrefix accepted (1 + leftSlots frames))
    (returned : (parseTreeLoop raw frames).1 = none) :
    ∃ consumed rest p,
      accepted ++ raw = consumed ++ rest ∧ OpenPrefix consumed p ∧ Blocked rest := by
  induction raw generalizing frames accepted with
  | nil => exact ⟨accepted, [], 1 + leftSlots frames, rfl, opened, True.intro⟩
  | cons tag raw ih =>
      by_cases node : tag = nodeTag
      · subst tag
        rw [parseTreeLoop_node] at returned
        have extended : OpenPrefix (accepted ++ [nodeTag])
            (1 + leftSlots (.needLeft :: frames)) := by
          simpa only [leftSlots, Nat.add_assoc, Nat.add_comm] using OpenPrefix.node opened
        obtain ⟨consumed, rest, p, word, proper, blocked⟩ :=
          ih (.needLeft :: frames) (accepted ++ [nodeTag]) extended returned
        refine ⟨consumed, rest, p, ?_, proper, blocked⟩
        simpa only [List.append_assoc, List.singleton_append] using word
      · by_cases empty : tag = emptyTag
        · subst tag
          rw [parseTreeLoop_empty_value] at returned
          have slots := resumeTreeRun_slots frames .nil
          cases resumed : (resumeTreeRun frames .nil).1 with
          | done t => simp only [resumed, reduceCtorEq] at returned
          | next nextFrames =>
              simp only [resumed] at returned slots
              have before : 1 + leftSlots frames = leftSlots nextFrames + 2 := by omega
              rw [before] at opened
              have extended : OpenPrefix (accepted ++ [emptyTag])
                  (1 + leftSlots nextFrames) := by
                simpa only [Nat.add_comm] using OpenPrefix.empty opened
              obtain ⟨consumed, rest, p, word, proper, blocked⟩ :=
                ih nextFrames (accepted ++ [emptyTag]) extended returned
              refine ⟨consumed, rest, p, ?_, proper, blocked⟩
              simpa only [List.append_assoc, List.singleton_append] using word
        · exact ⟨accepted, tag :: raw, 1 + leftSlots frames, rfl, opened, node, empty⟩

theorem parseTreeRun_none_iff_openPrefix (raw : Word) :
    (parseTreeRun raw).1 = none ↔
      ∃ accepted rest p, raw = accepted ++ rest ∧ OpenPrefix accepted p ∧ Blocked rest := by
  constructor
  · intro returned
    simpa only [List.nil_append] using
      parseTreeLoop_none_openPrefix raw [] [] OpenPrefix.nil returned
  · rintro ⟨accepted, rest, p, rfl, opened, blocked⟩
    exact parseTreeRun_none_of_openPrefix opened blocked

/-- This exact count includes the rejection probe, rollback, both empty probes and slot cleanup. -/
theorem run_openPrefix_failure (d : D) (accepted rest : Word) (p : Nat)
    (opened : OpenPrefix accepted p) (blocked : Blocked rest) (regs : Registers R)
    (outputs : D → Word) (ctx : ∀ k, List (Γ k)) :
    (next caller)^[2 * accepted.length + p + 4]
        (some (cfg (some (phaseLabel d .init)) regs (accepted ++ rest) [] [] outputs ctx)) =
      some (cfg (some (resultLabel d .failure)) (reset regs) (accepted ++ rest) [] [] outputs ctx) := by
  have executed := run_of_none caller d (accepted ++ rest) regs outputs ctx
    (parseTreeRun_none_of_openPrefix opened blocked)
  simpa only [runSteps_openPrefix opened blocked] using executed


variable [Fintype D] [Fintype K]

def outputCells (outputs : D → Word) : Nat := ∑ d, (outputs d).length
def contextCells (ctx : ∀ k, List (Γ k)) : Nat := ∑ k, (ctx k).length

theorem outputCells_update_cons (outputs : D → Word) (d : D) (tag : Tag) :
    outputCells (Function.update outputs d (tag :: outputs d)) = outputCells outputs + 1 := by
  have lengths : (fun other => (Function.update outputs d (tag :: outputs d) other).length) =
      Function.update (fun other => (outputs other).length) d ((outputs d).length + 1) := by
    funext other
    by_cases same : other = d
    · subst other; simp
    · simp only [Function.update_of_ne same]
  have old := Finset.sum_update_of_mem (Finset.mem_univ d)
    (fun other => (outputs other).length) (outputs d).length
  have updated := Finset.sum_update_of_mem (Finset.mem_univ d)
    (fun other => (outputs other).length) ((outputs d).length + 1)
  rw [Function.update_eq_self] at old
  unfold outputCells
  rw [lengths, updated, old]
  omega

/-- All actual stack cells, including arbitrary old outputs and protected context. -/
def stackCells (c : Cfg D Γ Λ R) : Nat :=
  (c.stk (.inl .raw)).length + (c.stk (.inl .reverse)).length +
    (c.stk (.inl .pending)).length +
    outputCells (fun d => c.stk (.inl (.output d))) + contextCells (fun k => c.stk (.inr k))

def credit : Option (Label D Λ) → Nat → Nat
  | some (.inl (_, .init)), rawLength => rawLength + 1
  | some (.inl (_, .scan)), rawLength => rawLength
  | _, _ => 0

def potential (c : Cfg D Γ Λ R) : Nat :=
  stackCells c + credit c.l (c.stk (.inl .raw)).length

/-- Only owned transitions have this bound; arbitrary caller execution is excluded. -/
theorem step_potential_le {before after : Cfg D Γ Λ R}
    (transition : LocalStep caller before after) : potential after ≤ potential before := by
  obtain ⟨d, phase, regs, raw, rev, pending, outputs, ctx, rfl⟩ := owned_cases before transition.1
  have executed := transition.2
  cases phase with
  | init =>
      rw [init_step] at executed
      cases Option.some.inj executed
      simp only [potential, stackCells, credit, cfg, phaseLabel, List.length_cons]
      omega
  | scan =>
      cases raw with
      | nil =>
          rw [scan_step_nil] at executed
          cases Option.some.inj executed
          simp only [potential, stackCells, credit, cfg, phaseLabel, List.length_nil]
          omega
      | cons tag raw =>
          by_cases node : tag = nodeTag
          · subst tag
            rw [scan_step_node] at executed
            cases Option.some.inj executed
            simp only [potential, stackCells, credit, cfg, phaseLabel, List.length_cons]
            omega
          · by_cases empty : tag = emptyTag
            · subst tag
              rw [scan_step_empty] at executed
              cases Option.some.inj executed
              cases pending with
              | nil =>
                  simp [potential, stackCells, credit, cfg, phaseLabel]
                  omega
              | cons token pending =>
                  cases pending with
                  | nil =>
                      simp [potential, stackCells, credit, cfg, phaseLabel]
                      omega
                  | cons token pending =>
                      simp only [potential, stackCells, cfg, phaseLabel, List.tail_cons,
                        List.cons_ne_nil, ite_false, credit, List.length_cons]
                      omega
            · rw [scan_step_foreign caller d tag raw rev pending regs outputs ctx node empty] at executed
              cases Option.some.inj executed
              simp only [potential, stackCells, credit, cfg, phaseLabel, List.length_cons]
              omega
  | emit =>
      cases rev with
      | nil =>
          rw [emit_step_nil] at executed
          cases Option.some.inj executed
          rfl
      | cons tag rev =>
          rw [emit_step_cons] at executed
          cases Option.some.inj executed
          simp only [potential, stackCells, credit, cfg, phaseLabel, List.length_cons,
            outputCells_update_cons]
          dsimp only [outputCells]
          omega
  | undo =>
      cases rev with
      | nil =>
          rw [undo_step_nil] at executed
          cases Option.some.inj executed
          rfl
      | cons tag rev =>
          rw [undo_step_cons] at executed
          cases Option.some.inj executed
          simp only [potential, stackCells, credit, cfg, phaseLabel, List.length_cons]
          omega
  | dropPending =>
      cases pending with
      | nil =>
          rw [dropPending_step_nil] at executed
          cases Option.some.inj executed
          rfl
      | cons token pending =>
          cases token
          rw [dropPending_step_cons] at executed
          cases Option.some.inj executed
          simp only [potential, stackCells, credit, cfg, phaseLabel, List.length_cons]
          omega

theorem local_reaches_potential_le {start reached : Cfg D Γ Λ R}
    (path : Relation.ReflTransGen (LocalStep caller) start reached) :
    potential reached ≤ potential start := by
  induction path with
  | refl => exact Nat.le_refl _
  | @tail before after _ transition ih => exact Nat.le_trans (step_potential_le caller transition) ih

theorem prefix_stackCells_le (d : D) (raw : Word) (regs : Registers R)
    (outputs : D → Word) (ctx : ∀ k, List (Γ k)) (n : Nat) (reached : Cfg D Γ Λ R)
    (bound : n ≤ runSteps raw)
    (executed : (next caller)^[n]
      (some (cfg (some (phaseLabel d .init)) regs raw [] [] outputs ctx)) = some reached) :
    stackCells reached ≤ 2 * raw.length + outputCells outputs + contextCells ctx + 1 := by
  obtain ⟨actual, run, _, path, _, _⟩ := run_prefix caller d raw regs outputs ctx n bound
  have equal : actual = reached := Option.some.inj (run.symm.trans executed)
  subst reached
  have bounded := local_reaches_potential_le caller path
  simp only [potential, stackCells, credit, cfg, phaseLabel, List.length_nil] at bounded
  change stackCells actual + credit actual.l (actual.stk (.inl .raw)).length ≤ _ at bounded
  dsimp only [outputCells, contextCells] at bounded ⊢
  omega

theorem scanSteps_nodes (count : Nat) (raw : Word) (p k : Nat) :
    scanSteps (List.replicate count nodeTag ++ raw) p k =
      count + scanSteps raw (p + count) (k + count) := by
  induction count generalizing p k with
  | zero => simp
  | succ count ih =>
      simp only [List.replicate_succ, List.cons_append, scanSteps_node, ih]
      simp only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem runSteps_nodes (count : Nat) :
    runSteps (List.replicate count nodeTag) = 3 * count + 5 := by
  have countEq := scanSteps_nodes count [] 1 0
  simp only [List.append_nil, scanSteps_nil] at countEq
  rw [runSteps, countEq]
  omega

theorem runSteps_nodes_foreign (count : Nat) (tag : Tag) (tail : Word)
    (notNode : tag ≠ nodeTag) (notEmpty : tag ≠ emptyTag) :
    runSteps (List.replicate count nodeTag ++ tag :: tail) = 3 * count + 5 := by
  rw [runSteps, scanSteps_nodes, scanSteps_foreign tag tail _ _ notNode notEmpty]
  omega

private theorem replicate_append_cons {α : Type} (count : Nat) (value : α) (tail : List α) :
    List.replicate count value ++ value :: tail = List.replicate (count + 1) value ++ tail := by
  rw [List.replicate_add]
  simp only [List.replicate_one, List.append_assoc, List.singleton_append]

omit [Fintype D] [Fintype K] in
theorem scan_nodes_iterate (d : D) (count : Nat) (raw rev : Word) (pending : List Unit)
    (regs : Registers R) (outputs : D → Word) (ctx : ∀ k, List (Γ k)) :
    (next caller)^[count]
        (some (cfg (some (phaseLabel d .scan)) (reset regs)
          (List.replicate count nodeTag ++ raw) rev pending outputs ctx)) =
      some (cfg (some (phaseLabel d .scan)) (reset regs) raw
        (List.replicate count nodeTag ++ rev) (List.replicate count () ++ pending) outputs ctx) := by
  induction count generalizing rev pending with
  | zero => rfl
  | succ count ih =>
      rw [List.replicate_succ, List.cons_append,
        iterate_step caller _ _ _ (scan_step_node caller d
          (List.replicate count nodeTag ++ raw) rev pending (reset regs) outputs ctx), reset_reset, ih]
      simp only [reset, replicate_append_cons, List.replicate_succ, List.cons_append]

omit [Fintype D] [Fintype K] in
theorem nodes_prefix (d : D) (count : Nat) (regs : Registers R)
    (outputs : D → Word) (ctx : ∀ k, List (Γ k)) :
    (next caller)^[count + 1]
        (some (cfg (some (phaseLabel d .init)) regs
          (List.replicate count nodeTag) [] [] outputs ctx)) =
      some (cfg (some (phaseLabel d .scan)) (reset regs) []
        (List.replicate count nodeTag) (List.replicate (count + 1) ()) outputs ctx) := by
  rw [iterate_step caller _ _ _
    (init_step caller d (List.replicate count nodeTag) [] [] regs outputs ctx)]
  have executed := scan_nodes_iterate caller d count [] [] [()] regs outputs ctx
  have pendingEq : List.replicate count () ++ [()] = List.replicate (count + 1) () := by
    rw [List.replicate_add, List.replicate_one]
  simpa only [List.append_nil, pendingEq] using executed

/-- The maximum is attained by an exhibited actual prefix, for every input length. -/
theorem nodes_prefix_sharp (d : D) (count : Nat) (regs : Registers R)
    (outputs : D → Word) (ctx : ∀ k, List (Γ k)) :
    ∃ reached,
      (next caller)^[count + 1]
          (some (cfg (some (phaseLabel d .init)) regs
            (List.replicate count nodeTag) [] [] outputs ctx)) = some reached ∧
      count + 1 < runSteps (List.replicate count nodeTag) ∧
      stackCells reached = 2 * count + outputCells outputs + contextCells ctx + 1 := by
  refine ⟨_, nodes_prefix caller d count regs outputs ctx, ?_, ?_⟩
  · rw [runSteps_nodes]
    omega
  · simp only [stackCells, cfg, List.length_nil, List.length_replicate]
    dsimp only [outputCells, contextCells]
    omega

/-- Success is the actual first live result, never arbitrary later reachability. -/
def FirstSuccess (d : D) (raw : Word) (t : BinaryTree Unit) (rest : Word)
    (regs : Registers R) (outputs : D → Word) (ctx : ∀ k, List (Γ k)) : Prop :=
  (next caller)^[runSteps raw]
      (some (cfg (some (phaseLabel d .init)) regs raw [] [] outputs ctx)) =
    some (cfg (some (resultLabel d .success)) (reset regs) rest [] []
      (Function.update outputs d (treeCode t ++ outputs d)) ctx)

omit [Fintype D] [Fintype K] in
theorem firstSuccess_iff (d : D) (raw : Word) (t : BinaryTree Unit) (rest : Word)
    (regs : Registers R) (outputs : D → Word) (ctx : ∀ k, List (Γ k)) :
    FirstSuccess caller d raw t rest regs outputs ctx ↔
      (parseTreeRun raw).1 = some (t, rest) := by
  constructor
  · intro observed
    unfold FirstSuccess at observed
    rw [run_source] at observed
    generalize sourceEq : (parseTreeRun raw).1 = source at observed
    cases source with
    | none =>
        have labelEq := congrArg (fun c : Cfg D Γ Λ R => c.l) (Option.some.inj observed)
        cases labelEq
    | some pair =>
        rcases pair with ⟨actual, suffix⟩
        have equal := Option.some.inj observed
        have rawEq := congrArg (fun c : Cfg D Γ Λ R => c.stk (.inl .raw)) equal
        have outputEq := congrArg (fun c : Cfg D Γ Λ R => c.stk (.inl (.output d))) equal
        change suffix = rest at rawEq
        simp only [resultCfg, cfg, Function.update_self] at outputEq
        have treeEq := (treeCode_prefix_injective actual t (outputs d) (outputs d) outputEq).1
        simp only [treeEq, rawEq]
  · exact run_of_some caller d raw t rest regs outputs ctx

omit [Fintype D] [Fintype K] in
theorem firstSuccess_code_iff (d : D) (raw : Word) (t : BinaryTree Unit) (rest : Word)
    (regs : Registers R) (outputs : D → Word) (ctx : ∀ k, List (Γ k)) :
    FirstSuccess caller d raw t rest regs outputs ctx ↔ raw = treeCode t ++ rest := by
  rw [firstSuccess_iff, parseTreeRun_iff]

variable [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]

/-- One fixed finite program, chosen before its arbitrary input words. Its results remain live. -/
def machine (d : D) (initial : R) : Turing.FinTM2 where
  K := StackId D K
  k₀ := .inl .raw
  k₁ := .inl (.output d)
  Γ := Alphabet D Γ
  Λ := Label D Λ
  main := phaseLabel d .init
  σ := Registers R
  initialState := ((none, none), initial)
  Γk₀Fin := alphabetFintype (.inl .raw)
  m := program caller

theorem machine_step_eq (d : D) (initial : R) (c : Cfg D Γ Λ R) :
    (machine caller d initial).step c = step caller c := rfl

theorem initList_eq (d : D) (initial : R) (raw : Word) :
    Turing.initList (machine caller d initial) raw =
      cfg (some (phaseLabel d .init)) ((none, none), initial) raw [] []
        (fun _ => []) (fun _ => []) := by
  apply cfg_ext <;> first | rfl | exact fun _ => rfl

end Resources.RotationCertificate.TreeParserMachine
