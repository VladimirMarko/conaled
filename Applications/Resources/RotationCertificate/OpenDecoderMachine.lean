import Applications.Resources.RotationCertificate.BitDecoderMachine
import Applications.Resources.BinaryCounter.FixedWidthMachine

/-!
# Open four-bit decoding on physical Tag stacks

The actual scan statement pops at most four Bool cells, decodes the finite
nibble and pushes its Tag onto a reverse stack. Emit transfers those actual
tags to a direct Tag output; clear discards the actual reverse accumulator.
The final empty probes reset only the borrowed finite registers and jump to
live success or failure labels. Every caller stack and caller register is
protected until that first handoff. No runtime callback traverses a list or
evaluates the proof-side source decoder, rank, length or execution bound.

The source correspondence includes every malformed partial final block and
arbitrary old reverse/output stacks. This component does not yet implement
the complete certificate verifier or its remaining machine-model/NP bridge.
Correspondence: `docs/research/fdsa-rotation-certificate-preparation.md`.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.RotationCertificate.OpenDecoderMachine
open Resources.BinaryCounter (Bits)

abbrev LocalStack := BitDecoderMachine.StackId
abbrev Phase := BitDecoderMachine.Label
abbrev Temporaries := BitDecoderMachine.Registers

inductive Result
  | success | failure
  deriving DecidableEq

instance : Fintype Result where
  elems := {.success, .failure}
  complete result := by cases result <;> decide

abbrev StackId (K : Type) := LocalStack ⊕ K
abbrev External (Λ : Type) := Result ⊕ Λ
abbrev Label (Λ : Type) := Phase ⊕ External Λ
abbrev Registers (R : Type) := Temporaries × R

variable {K Λ R : Type} {Γ : K → Type}

abbrev alphabet (Γ : K → Type) : StackId K → Type
  | .inl .input => Bool
  | .inl .reverse => Tag
  | .inl .output => Tag
  | .inr k => Γ k

instance alphabetFintype [∀ k, Fintype (Γ k)] (k : StackId K) :
    Fintype (alphabet Γ k) := by
  cases k with
  | inl slot => cases slot <;> exact inferInstance
  | inr k => exact inferInstance

abbrev Statement (Γ : K → Type) (Λ R : Type) :=
  Turing.TM2.Stmt (alphabet Γ) (Label Λ) (Registers R)
abbrev Cfg (Γ : K → Type) (Λ R : Type) :=
  Turing.TM2.Cfg (alphabet Γ) (Label Λ) (Registers R)

def phaseLabel (phase : Phase) : Label Λ := .inl phase
def resultLabel (result : Result) : Label Λ := .inr (.inl result)
def callerLabel (label : Λ) : Label Λ := .inr (.inr label)

/-- The actual five-field finite register representation, not an invented cardinality model. -/
def temporariesEquiv : Temporaries ≃
    Option Bool × Option Bool × Option Bool × Option Bool × Option Tag where
  toFun regs := (regs.b0, regs.b1, regs.b2, regs.b3, regs.tag)
  invFun regs := ⟨regs.1, regs.2.1, regs.2.2.1, regs.2.2.2.1, regs.2.2.2.2⟩
  left_inv regs := by cases regs; rfl
  right_inv regs := by rcases regs with ⟨b0, b1, b2, b3, tag⟩; rfl

theorem card_temporaries : Fintype.card Temporaries = 1377 := by
  rw [Fintype.card_congr temporariesEquiv]
  simp

theorem card_stackId [Fintype K] : Fintype.card (StackId K) = 3 + Fintype.card K := by
  rw [Fintype.card_sum]
  rfl

theorem card_label [Fintype Λ] : Fintype.card (Label Λ) = 5 + Fintype.card Λ := by
  have phases : Fintype.card Phase = 3 := rfl
  have results : Fintype.card Result = 2 := rfl
  simp only [Fintype.card_sum, phases, results]
  omega

theorem card_registers [Fintype R] : Fintype.card (Registers R) = 1377 * Fintype.card R := by
  rw [Fintype.card_prod, card_temporaries]

def reset (regs : Registers R) : Registers R := (BitDecoderMachine.zeroRegisters, regs.2)
def store0 (regs : Registers R) (bit : Option Bool) : Registers R :=
  (BitDecoderMachine.store0 regs.1 bit, regs.2)
def store1 (regs : Registers R) (bit : Option Bool) : Registers R :=
  (BitDecoderMachine.store1 regs.1 bit, regs.2)
def store2 (regs : Registers R) (bit : Option Bool) : Registers R :=
  (BitDecoderMachine.store2 regs.1 bit, regs.2)
def store3 (regs : Registers R) (bit : Option Bool) : Registers R :=
  (BitDecoderMachine.store3 regs.1 bit, regs.2)
def storeTag (regs : Registers R) (tag : Option Tag) : Registers R :=
  (BitDecoderMachine.storeTag regs.1 tag, regs.2)

@[simp] theorem reset_reset (regs : Registers R) : reset (reset regs) = reset regs := rfl

def jump (label : Label Λ) : Statement Γ Λ R :=
  .load reset (.goto (fun _ => label))

/-- All observations are finite and overwritten by an actual pop before their use. -/
def block : Phase → Statement Γ Λ R
  | .scan =>
      .pop (.inl .input) store0 (.branch (fun regs => regs.1.b0.isSome)
        (.pop (.inl .input) store1 (.branch (fun regs => regs.1.b1.isSome)
          (.pop (.inl .input) store2 (.branch (fun regs => regs.1.b2.isSome)
            (.pop (.inl .input) store3 (.branch (fun regs => regs.1.b3.isSome)
              (.push (.inl .reverse) (fun regs => BitDecoderMachine.nibble regs.1)
                (jump (phaseLabel .scan)))
              (jump (phaseLabel .clear))))
            (jump (phaseLabel .clear))))
          (jump (phaseLabel .clear))))
        (jump (phaseLabel .emit)))
  | .emit =>
      .pop (.inl .reverse) storeTag (.branch (fun regs => regs.1.tag.isSome)
        (.push (.inl .output) (fun regs => regs.1.tag.getD 0) (jump (phaseLabel .emit)))
        (jump (resultLabel .success)))
  | .clear =>
      .pop (.inl .reverse) storeTag (.branch (fun regs => regs.1.tag.isSome)
        (jump (phaseLabel .clear)) (jump (resultLabel .failure)))

def program (caller : External Λ → Statement Γ Λ R) : Label Λ → Statement Γ Λ R
  | .inl phase => block phase
  | .inr external => caller external

theorem program_eq_of_agrees (ambient : Label Λ → Statement Γ Λ R)
    (owned : ∀ phase, ambient (phaseLabel phase) = block phase) :
    ambient = program (fun external => ambient (.inr external)) := by
  funext label
  cases label with
  | inl phase => exact owned phase
  | inr external => rfl

def cfg (label : Option (Label Λ)) (regs : Registers R) (raw : Bits) (rev out : Word)
    (ctx : ∀ k, List (Γ k)) : Cfg Γ Λ R where
  l := label
  var := regs
  stk
    | .inl .input => raw
    | .inl .reverse => rev
    | .inl .output => out
    | .inr k => ctx k

theorem cfg_ext {left right : Cfg Γ Λ R}
    (label : left.l = right.l) (regs : left.var = right.var)
    (raw : left.stk (.inl .input) = right.stk (.inl .input))
    (rev : left.stk (.inl .reverse) = right.stk (.inl .reverse))
    (out : left.stk (.inl .output) = right.stk (.inl .output))
    (ctx : ∀ k, left.stk (.inr k) = right.stk (.inr k)) : left = right := by
  have stackEq : left.stk = right.stk := by
    funext k
    cases k with
    | inl slot => cases slot with
      | input => exact raw
      | reverse => exact rev
      | output => exact out
    | inr k => exact ctx k
  cases left
  cases right
  cases label
  cases regs
  cases stackEq
  rfl

theorem cfg_eta (c : Cfg Γ Λ R) :
    cfg c.l c.var (c.stk (.inl .input)) (c.stk (.inl .reverse))
      (c.stk (.inl .output)) (fun k => c.stk (.inr k)) = c := by
  apply cfg_ext <;> first | rfl | exact fun _ => rfl

variable [DecidableEq K]

abbrev step (caller : External Λ → Statement Γ Λ R) : Cfg Γ Λ R → Option (Cfg Γ Λ R) :=
  Turing.TM2.step (program caller)

def next (caller : External Λ → Statement Γ Λ R) :
    Option (Cfg Γ Λ R) → Option (Cfg Γ Λ R) := fun c => c.bind (step caller)

variable (caller : External Λ → Statement Γ Λ R)

@[simp] theorem next_none : next caller none = none := rfl
@[simp] theorem next_some (c : Cfg Γ Λ R) : next caller (some c) = step caller c := rfl

theorem iterate_step (n : Nat) (c d : Cfg Γ Λ R) (transition : step caller c = some d) :
    (next caller)^[n + 1] (some c) = (next caller)^[n] (some d) := by
  rw [Function.iterate_succ_apply, next_some, transition]

theorem scan_step_block (b0 b1 b2 b3 : Bool) (raw : Bits) (rev out : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel .scan)) regs (b0 :: b1 :: b2 :: b3 :: raw) rev out ctx) =
      some (cfg (some (phaseLabel .scan)) (reset regs) raw
        ((decodeTagRun b0 b1 b2 b3).1 :: rev) out ctx) := by
  apply congrArg some; apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem scan_step_nil (rev out : Word) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel .scan)) regs [] rev out ctx) =
      some (cfg (some (phaseLabel .emit)) (reset regs) [] rev out ctx) := by
  apply congrArg some; apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem scan_step_one (b0 : Bool) (rev out : Word) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel .scan)) regs [b0] rev out ctx) =
      some (cfg (some (phaseLabel .clear)) (reset regs) [] rev out ctx) := by
  apply congrArg some; apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem scan_step_two (b0 b1 : Bool) (rev out : Word) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel .scan)) regs [b0, b1] rev out ctx) =
      some (cfg (some (phaseLabel .clear)) (reset regs) [] rev out ctx) := by
  apply congrArg some; apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem scan_step_three (b0 b1 b2 : Bool) (rev out : Word) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel .scan)) regs [b0, b1, b2] rev out ctx) =
      some (cfg (some (phaseLabel .clear)) (reset regs) [] rev out ctx) := by
  apply congrArg some; apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem scan_step_tag (tag : Tag) (raw : Bits) (rev out : Word) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel .scan)) regs (tagBits tag ++ raw) rev out ctx) =
      some (cfg (some (phaseLabel .scan)) (reset regs) raw (tag :: rev) out ctx) := by
  fin_cases tag <;> apply congrArg some <;> apply cfg_ext <;>
    first | rfl | exact fun _ => rfl

theorem emit_step_cons (tag : Tag) (rev : Word) (raw : Bits) (out : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel .emit)) regs raw (tag :: rev) out ctx) =
      some (cfg (some (phaseLabel .emit)) (reset regs) raw rev (tag :: out) ctx) := by
  apply congrArg some; apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem emit_step_nil (raw : Bits) (out : Word) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel .emit)) regs raw [] out ctx) =
      some (cfg (some (resultLabel .success)) (reset regs) raw [] out ctx) := by
  apply congrArg some; apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem clear_step_cons (tag : Tag) (rev : Word) (raw : Bits) (out : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel .clear)) regs raw (tag :: rev) out ctx) =
      some (cfg (some (phaseLabel .clear)) (reset regs) raw rev out ctx) := by
  apply congrArg some; apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem clear_step_nil (raw : Bits) (out : Word) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel .clear)) regs raw [] out ctx) =
      some (cfg (some (resultLabel .failure)) (reset regs) raw [] out ctx) := by
  apply congrArg some; apply cfg_ext <;> first | rfl | exact fun _ => rfl

/-- The final empty probe is included; the caller's body has not executed. -/
theorem emit_iterate (rev : Word) (raw : Bits) (out : Word) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    (next caller)^[rev.length + 1] (some (cfg (some (phaseLabel .emit)) regs raw rev out ctx)) =
      some (cfg (some (resultLabel .success)) (reset regs) raw [] (rev.reverse ++ out) ctx) := by
  induction rev generalizing out regs with
  | nil => simpa only [List.length_nil, Nat.zero_add, Function.iterate_one, next_some,
      List.reverse_nil, List.nil_append] using emit_step_nil caller raw out regs ctx
  | cons tag rev ih =>
      rw [show (tag :: rev).length + 1 = (rev.length + 1) + 1 by rfl,
        iterate_step caller _ _ _ (emit_step_cons caller tag rev raw out regs ctx), ih]
      simp only [reset_reset, List.reverse_cons, List.append_assoc, List.singleton_append]

/-- Dirty output and arbitrary input are retained while reverse cells are really discarded. -/
theorem clear_iterate (rev : Word) (raw : Bits) (out : Word) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    (next caller)^[rev.length + 1] (some (cfg (some (phaseLabel .clear)) regs raw rev out ctx)) =
      some (cfg (some (resultLabel .failure)) (reset regs) raw [] out ctx) := by
  induction rev generalizing regs with
  | nil => simpa only [List.length_nil, Nat.zero_add, Function.iterate_one, next_some]
      using clear_step_nil caller raw out regs ctx
  | cons tag rev ih =>
      rw [show (tag :: rev).length + 1 = (rev.length + 1) + 1 by rfl,
        iterate_step caller _ _ _ (clear_step_cons caller tag rev raw out regs ctx), ih, reset_reset]

/-- Proof-side count of actual transitions, absent from every runtime callback. -/
def runSteps (raw : Bits) : Nat := 2 * (raw.length / 4) + 2

omit [DecidableEq K] in
theorem runSteps_pos (raw : Bits) : 0 < runSteps raw := by unfold runSteps; omega

omit [DecidableEq K] in
theorem runSteps_le (raw : Bits) : runSteps raw ≤ raw.length + 2 := by
  unfold runSteps
  omega

/-- A proof-facing endpoint; the actual program never computes this source result. -/
def resultCfg (result : Option Word) (rev out : Word) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) : Cfg Γ Λ R :=
  match result with
  | none => cfg (some (resultLabel .failure)) (reset regs) [] [] out ctx
  | some word =>
      cfg (some (resultLabel .success)) (reset regs) [] [] (rev.reverse ++ word ++ out) ctx

/-- Both outcomes of an arbitrary raw suffix with arbitrary old reverse/output cells. -/
theorem scan_iterate (raw : Bits) (rev out : Word) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    (next caller)^[runSteps raw + rev.length]
        (some (cfg (some (phaseLabel .scan)) regs raw rev out ctx)) =
      some (resultCfg (unpackWordRun raw).1 rev out regs ctx) := by
  induction raw using unpackWordRun.induct generalizing rev regs with
  | case1 =>
      rw [show runSteps [] + rev.length = (rev.length + 1) + 1 by simp [runSteps]; omega,
        iterate_step caller _ _ _ (scan_step_nil caller rev out regs ctx), emit_iterate]
      simp [resultCfg, unpackWordRun]
  | case2 b0 =>
      rw [show runSteps [b0] + rev.length = (rev.length + 1) + 1 by simp [runSteps]; omega,
        iterate_step caller _ _ _ (scan_step_one caller b0 rev out regs ctx), clear_iterate]
      rfl
  | case3 b0 b1 =>
      rw [show runSteps [b0, b1] + rev.length = (rev.length + 1) + 1 by simp [runSteps]; omega,
        iterate_step caller _ _ _ (scan_step_two caller b0 b1 rev out regs ctx), clear_iterate]
      rfl
  | case4 b0 b1 b2 =>
      rw [show runSteps [b0, b1, b2] + rev.length = (rev.length + 1) + 1 by simp [runSteps]; omega,
        iterate_step caller _ _ _ (scan_step_three caller b0 b1 b2 rev out regs ctx), clear_iterate]
      rfl
  | case5 b0 b1 b2 b3 raw ih =>
      have count : runSteps (b0 :: b1 :: b2 :: b3 :: raw) + rev.length =
          (runSteps raw + ((decodeTagRun b0 b1 b2 b3).1 :: rev).length) + 1 := by
        simp only [runSteps, List.length_cons]
        omega
      rw [count, iterate_step caller _ _ _ (scan_step_block caller b0 b1 b2 b3 raw rev out regs ctx),
        ih, unpackWordRun_cons4]
      cases returned : unpackWordRun raw with
      | mk result cost => cases result with
        | none => rfl
        | some suffix => simp [resultCfg, List.reverse_cons, List.append_assoc]

theorem run_source (raw : Bits) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (next caller)^[runSteps raw] (some (cfg (some (phaseLabel .scan)) regs raw [] [] ctx)) =
      some (resultCfg (unpackWordRun raw).1 [] [] regs ctx) := by
  simpa only [List.length_nil, Nat.add_zero] using scan_iterate caller raw [] [] regs ctx

theorem scan_of_some (raw : Bits) (word rev out : Word) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (decoded : (unpackWordRun raw).1 = some word) :
    (next caller)^[runSteps raw + rev.length]
        (some (cfg (some (phaseLabel .scan)) regs raw rev out ctx)) =
      some (cfg (some (resultLabel .success)) (reset regs) [] []
        (rev.reverse ++ word ++ out) ctx) := by
  simpa only [decoded, resultCfg] using scan_iterate caller raw rev out regs ctx

theorem scan_of_none (raw : Bits) (rev out : Word) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (decoded : (unpackWordRun raw).1 = none) :
    (next caller)^[runSteps raw + rev.length]
        (some (cfg (some (phaseLabel .scan)) regs raw rev out ctx)) =
      some (cfg (some (resultLabel .failure)) (reset regs) [] [] out ctx) := by
  simpa only [decoded, resultCfg] using scan_iterate caller raw rev out regs ctx

theorem run_of_some (raw : Bits) (word : Word) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (decoded : (unpackWordRun raw).1 = some word) :
    (next caller)^[runSteps raw] (some (cfg (some (phaseLabel .scan)) regs raw [] [] ctx)) =
      some (cfg (some (resultLabel .success)) (reset regs) [] [] word ctx) := by
  simpa using scan_of_some caller raw word [] [] regs ctx decoded

theorem run_of_none (raw : Bits) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (decoded : (unpackWordRun raw).1 = none) :
    (next caller)^[runSteps raw] (some (cfg (some (phaseLabel .scan)) regs raw [] [] ctx)) =
      some (cfg (some (resultLabel .failure)) (reset regs) [] [] [] ctx) := by
  simpa using scan_of_none caller raw [] [] regs ctx decoded

omit [DecidableEq K] in
theorem runSteps_code (word : Word) : runSteps (wordBits word) = 2 * word.length + 2 := by
  rw [runSteps, wordBits_length]
  omega

theorem scan_code (word rev out : Word) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (next caller)^[2 * word.length + 2 + rev.length]
        (some (cfg (some (phaseLabel .scan)) regs (wordBits word) rev out ctx)) =
      some (cfg (some (resultLabel .success)) (reset regs) [] []
        (rev.reverse ++ word ++ out) ctx) := by
  simpa only [runSteps_code] using scan_of_some caller (wordBits word) word rev out regs ctx
    (congrArg Prod.fst (unpackWordRun_code word))

theorem run_code (word : Word) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (next caller)^[2 * word.length + 2]
        (some (cfg (some (phaseLabel .scan)) regs (wordBits word) [] [] ctx)) =
      some (cfg (some (resultLabel .success)) (reset regs) [] [] word ctx) := by
  simpa using scan_code caller word [] [] regs ctx

theorem scan_partial (word rev out : Word) (short : Bits) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (positive : 0 < short.length) (incomplete : short.length < 4) :
    (next caller)^[2 * word.length + 2 + rev.length]
        (some (cfg (some (phaseLabel .scan)) regs (wordBits word ++ short) rev out ctx)) =
      some (cfg (some (resultLabel .failure)) (reset regs) [] [] out ctx) := by
  have count : runSteps (wordBits word ++ short) = 2 * word.length + 2 := by
    rw [runSteps, List.length_append, wordBits_length]
    omega
  simpa only [count] using scan_of_none caller (wordBits word ++ short) rev out regs ctx
    (congrArg Prod.fst (unpackWordRun_partial word short positive incomplete))

theorem run_partial (word : Word) (short : Bits) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (positive : 0 < short.length) (incomplete : short.length < 4) :
    (next caller)^[2 * word.length + 2]
        (some (cfg (some (phaseLabel .scan)) regs (wordBits word ++ short) [] [] ctx)) =
      some (cfg (some (resultLabel .failure)) (reset regs) [] [] [] ctx) := by
  simpa using scan_partial caller word [] [] short regs ctx positive incomplete

/-- Zero transfers retain stale registers; every positive transfer resets the borrowed fields. -/
def prefixRegisters (n : Nat) (regs : Registers R) : Registers R :=
  if n = 0 then regs else reset regs

omit [DecidableEq K] in
@[simp] theorem prefixRegisters_zero (regs : Registers R) : prefixRegisters 0 regs = regs := rfl
omit [DecidableEq K] in
@[simp] theorem prefixRegisters_succ (n : Nat) (regs : Registers R) :
    prefixRegisters (n + 1) regs = reset regs := rfl
omit [DecidableEq K] in
@[simp] theorem prefixRegisters_reset (n : Nat) (regs : Registers R) :
    prefixRegisters n (reset regs) = reset regs := by
  cases n <;> rfl

/-- A literal split-prefix reversal before the final empty probe. -/
theorem emit_prefix (headWord tail : Word) (raw : Bits) (out : Word) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    (next caller)^[headWord.length]
        (some (cfg (some (phaseLabel .emit)) regs raw (headWord ++ tail) out ctx)) =
      some (cfg (some (phaseLabel .emit)) (prefixRegisters headWord.length regs)
        raw tail (headWord.reverse ++ out) ctx) := by
  induction headWord generalizing out regs with
  | nil => rfl
  | cons tag headWord ih =>
      rw [List.length_cons, List.cons_append,
        iterate_step caller _ _ _ (emit_step_cons caller tag (headWord ++ tail) raw out regs ctx), ih]
      simp only [prefixRegisters_reset, prefixRegisters_succ,
        List.reverse_cons, List.append_assoc, List.singleton_append]

/-- A literal deletion prefix retains input and every old output cell. -/
theorem clear_prefix (headWord tail : Word) (raw : Bits) (out : Word) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    (next caller)^[headWord.length]
        (some (cfg (some (phaseLabel .clear)) regs raw (headWord ++ tail) out ctx)) =
      some (cfg (some (phaseLabel .clear)) (prefixRegisters headWord.length regs) raw tail out ctx) := by
  induction headWord generalizing regs with
  | nil => rfl
  | cons tag headWord ih =>
      rw [List.length_cons, List.cons_append,
        iterate_step caller _ _ _ (clear_step_cons caller tag (headWord ++ tail) raw out regs ctx), ih]
      simp only [prefixRegisters_reset, prefixRegisters_succ]

/-- Every complete encoded prefix is really consumed, one finite block per Tag. -/
theorem scan_prefix (headWord : Word) (raw : Bits) (rev out : Word) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    (next caller)^[headWord.length]
        (some (cfg (some (phaseLabel .scan)) regs (wordBits headWord ++ raw) rev out ctx)) =
      some (cfg (some (phaseLabel .scan)) (prefixRegisters headWord.length regs)
        raw (headWord.reverse ++ rev) out ctx) := by
  induction headWord generalizing rev regs with
  | nil => rfl
  | cons tag headWord ih =>
      rw [List.length_cons, wordBits_cons, List.append_assoc,
        iterate_step caller _ _ _ (scan_step_tag caller tag (wordBits headWord ++ raw) rev out regs ctx), ih]
      simp only [prefixRegisters_reset, prefixRegisters_succ,
        List.reverse_cons, List.append_assoc, List.singleton_append]

/-- Success is observed at the fixed first-return clock, before arbitrary caller code. -/
def FirstSuccess (raw : Bits) (word : Word) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) : Prop :=
  (next caller)^[runSteps raw] (some (cfg (some (phaseLabel .scan)) regs raw [] [] ctx)) =
    some (cfg (some (resultLabel .success)) (reset regs) [] [] word ctx)

theorem firstSuccess_iff (raw : Bits) (word : Word) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    FirstSuccess caller raw word regs ctx ↔ (unpackWordRun raw).1 = some word := by
  constructor
  · intro observed
    unfold FirstSuccess at observed
    rw [run_source] at observed
    generalize decoded : (unpackWordRun raw).1 = result at observed
    cases result with
    | none =>
        have labels := congrArg (fun c : Cfg Γ Λ R => c.l) (Option.some.inj observed)
        cases labels
    | some actual =>
        have output := congrArg (fun c : Cfg Γ Λ R => c.stk (.inl .output))
          (Option.some.inj observed)
        have equal : actual = word := by simpa [resultCfg, cfg] using output
        simp only [equal]
  · exact run_of_some caller raw word regs ctx

theorem firstSuccess_code_iff (raw : Bits) (word : Word) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    FirstSuccess caller raw word regs ctx ↔ raw = wordBits word := by
  rw [firstSuccess_iff, unpackWordRun_iff]

def FirstFailure (raw : Bits) (regs : Registers R) (ctx : ∀ k, List (Γ k)) : Prop :=
  (next caller)^[runSteps raw] (some (cfg (some (phaseLabel .scan)) regs raw [] [] ctx)) =
    some (cfg (some (resultLabel .failure)) (reset regs) [] [] [] ctx)

theorem firstFailure_iff (raw : Bits) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    FirstFailure caller raw regs ctx ↔ (unpackWordRun raw).1 = none := by
  constructor
  · intro observed
    unfold FirstFailure at observed
    rw [run_source] at observed
    generalize decoded : (unpackWordRun raw).1 = result at observed
    cases result with
    | none => rfl
    | some actual =>
        have labels := congrArg (fun c : Cfg Γ Λ R => c.l) (Option.some.inj observed)
        cases labels
  · exact run_of_none caller raw regs ctx

theorem firstFailure_length_iff (raw : Bits) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    FirstFailure caller raw regs ctx ↔ raw.length % 4 ≠ 0 := by
  rw [firstFailure_iff, unpackWordRun_none_iff]

/-- Type-valued timed data for this actual open program and its exact dirty endpoint. -/
def scanInTime (raw : Bits) (rev out : Word) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller)
      (cfg (some (phaseLabel .scan)) regs raw rev out ctx)
      (some (resultCfg (unpackWordRun raw).1 rev out regs ctx)) (runSteps raw + rev.length) where
  steps := runSteps raw + rev.length
  evals_in_steps := scan_iterate caller raw rev out regs ctx
  steps_le_m := Nat.le_refl _

def runInTimeExact (raw : Bits) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller)
      (cfg (some (phaseLabel .scan)) regs raw [] [] ctx)
      (some (resultCfg (unpackWordRun raw).1 [] [] regs ctx)) (runSteps raw) where
  steps := runSteps raw
  evals_in_steps := run_source caller raw regs ctx
  steps_le_m := Nat.le_refl _

def runInLinearTime (raw : Bits) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller)
      (cfg (some (phaseLabel .scan)) regs raw [] [] ctx)
      (some (resultCfg (unpackWordRun raw).1 [] [] regs ctx)) (raw.length + 2) where
  steps := runSteps raw
  evals_in_steps := run_source caller raw regs ctx
  steps_le_m := runSteps_le raw

def emitInTime (rev : Word) (raw : Bits) (out : Word) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller)
      (cfg (some (phaseLabel .emit)) regs raw rev out ctx)
      (some (cfg (some (resultLabel .success)) (reset regs) raw [] (rev.reverse ++ out) ctx))
      (rev.length + 1) where
  steps := rev.length + 1
  evals_in_steps := emit_iterate caller rev raw out regs ctx
  steps_le_m := Nat.le_refl _

def clearInTime (rev : Word) (raw : Bits) (out : Word) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller)
      (cfg (some (phaseLabel .clear)) regs raw rev out ctx)
      (some (cfg (some (resultLabel .failure)) (reset regs) raw [] out ctx)) (rev.length + 1) where
  steps := rev.length + 1
  evals_in_steps := clear_iterate caller rev raw out regs ctx
  steps_le_m := Nat.le_refl _

/-- The local phases are disjoint from both results and every external caller label. -/
def Owned : Option (Label Λ) → Prop
  | some (.inl _) => True
  | _ => False

def phaseSteps : Phase → Bits → Word → Nat
  | .scan, raw, rev => runSteps raw + rev.length
  | .emit, _, rev => rev.length + 1
  | .clear, _, rev => rev.length + 1

/-- Exact proof-only rank on every owned configuration, including dirty and stale states. -/
def remainingSteps (c : Cfg Γ Λ R) : Nat :=
  match c.l with
  | some (.inl phase) => phaseSteps phase (c.stk (.inl .input)) (c.stk (.inl .reverse))
  | _ => 0

omit [DecidableEq K] in
theorem remainingSteps_pos_iff (c : Cfg Γ Λ R) : 0 < remainingSteps c ↔ Owned c.l := by
  cases labelEq : c.l with
  | none => simp [remainingSteps, Owned, labelEq]
  | some label => cases label with
    | inr external => simp [remainingSteps, Owned, labelEq]
    | inl phase =>
        cases phase <;> simp [remainingSteps, Owned, labelEq, phaseSteps, runSteps]

omit [DecidableEq K] in
theorem owned_cases (c : Cfg Γ Λ R) (owned : Owned c.l) :
    ∃ phase regs raw rev out ctx,
      c = cfg (some (phaseLabel phase)) regs raw rev out ctx := by
  cases labelEq : c.l with
  | none => simp [Owned, labelEq] at owned
  | some label => cases label with
    | inr external => simp [Owned, labelEq] at owned
    | inl phase =>
        refine ⟨phase, c.var, c.stk (.inl .input), c.stk (.inl .reverse),
          c.stk (.inl .output), (fun k => c.stk (.inr k)), ?_⟩
        simpa only [labelEq, phaseLabel] using (cfg_eta c).symm

/-- One owned step has genuine progress, exact rank decrease, reset and physical nonincrease. -/
theorem phase_step_data (phase : Phase) (raw : Bits) (rev out : Word) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    ∃ reached,
      step caller (cfg (some (phaseLabel phase)) regs raw rev out ctx) = some reached ∧
      phaseSteps phase raw rev = remainingSteps reached + 1 ∧
      reached.var = reset regs ∧
      (reached.stk (.inl .input)).length + (reached.stk (.inl .reverse)).length +
          (reached.stk (.inl .output)).length ≤ raw.length + rev.length + out.length ∧
      ∀ k, reached.stk (.inr k) = ctx k := by
  cases phase with
  | scan =>
      cases raw with
      | nil =>
          refine ⟨_, scan_step_nil caller rev out regs ctx, ?_, rfl, ?_, fun _ => rfl⟩
          · simp only [phaseSteps, runSteps, remainingSteps, cfg, phaseLabel, List.length_nil]
            omega
          · rfl
      | cons b0 raw => cases raw with
        | nil =>
            refine ⟨_, scan_step_one caller b0 rev out regs ctx, ?_, rfl, ?_, fun _ => rfl⟩
            · simp only [phaseSteps, runSteps, remainingSteps, cfg, phaseLabel,
                List.length_nil, List.length_cons]
              omega
            · simp only [cfg, List.length_nil, List.length_cons]; omega
        | cons b1 raw => cases raw with
          | nil =>
              refine ⟨_, scan_step_two caller b0 b1 rev out regs ctx, ?_, rfl, ?_, fun _ => rfl⟩
              · simp only [phaseSteps, runSteps, remainingSteps, cfg, phaseLabel,
                  List.length_nil, List.length_cons]
                omega
              · simp only [cfg, List.length_nil, List.length_cons]; omega
          | cons b2 raw => cases raw with
            | nil =>
                refine ⟨_, scan_step_three caller b0 b1 b2 rev out regs ctx, ?_, rfl, ?_, fun _ => rfl⟩
                · simp only [phaseSteps, runSteps, remainingSteps, cfg, phaseLabel,
                    List.length_nil, List.length_cons]
                  omega
                · simp only [cfg, List.length_nil, List.length_cons]; omega
            | cons b3 raw =>
                refine ⟨_, scan_step_block caller b0 b1 b2 b3 raw rev out regs ctx,
                  ?_, rfl, ?_, fun _ => rfl⟩
                · simp only [phaseSteps, runSteps, remainingSteps, cfg, phaseLabel, List.length_cons]
                  omega
                · simp only [cfg, List.length_cons]; omega
  | emit =>
      cases rev with
      | nil =>
          refine ⟨_, emit_step_nil caller raw out regs ctx, ?_, rfl, ?_, fun _ => rfl⟩
          · rfl
          · rfl
      | cons tag rev =>
          refine ⟨_, emit_step_cons caller tag rev raw out regs ctx, ?_, rfl, ?_, fun _ => rfl⟩
          · rfl
          · simp only [cfg, List.length_cons]; omega
  | clear =>
      cases rev with
      | nil =>
          refine ⟨_, clear_step_nil caller raw out regs ctx, ?_, rfl, ?_, fun _ => rfl⟩
          · rfl
          · rfl
      | cons tag rev =>
          refine ⟨_, clear_step_cons caller tag rev raw out regs ctx, ?_, rfl, ?_, fun _ => rfl⟩
          · rfl
          · simp only [cfg, List.length_cons]; omega

def LocalStep (before after : Cfg Γ Λ R) : Prop :=
  Owned before.l ∧ step caller before = some after

theorem local_step_data {before after : Cfg Γ Λ R} (transition : LocalStep caller before after) :
    remainingSteps before = remainingSteps after + 1 ∧
    after.var.1 = BitDecoderMachine.zeroRegisters ∧ after.var.2 = before.var.2 ∧
    (after.stk (.inl .input)).length + (after.stk (.inl .reverse)).length +
        (after.stk (.inl .output)).length ≤
      (before.stk (.inl .input)).length + (before.stk (.inl .reverse)).length +
        (before.stk (.inl .output)).length ∧
    ∀ k, after.stk (.inr k) = before.stk (.inr k) := by
  obtain ⟨phase, regs, raw, rev, out, ctx, rfl⟩ := owned_cases before transition.1
  obtain ⟨reached, executed, rank, registers, cells, frame⟩ :=
    phase_step_data caller phase raw rev out regs ctx
  have equal : reached = after := Option.some.inj (executed.symm.trans transition.2)
  subst after
  exact ⟨rank, by rw [registers]; rfl, by rw [registers]; rfl, cells, frame⟩

theorem local_step_remaining {before after : Cfg Γ Λ R}
    (transition : LocalStep caller before after) :
    remainingSteps before = remainingSteps after + 1 := (local_step_data caller transition).1

theorem local_progress (before : Cfg Γ Λ R) (positive : 0 < remainingSteps before) :
    ∃ after, step caller before = some after ∧ remainingSteps before = remainingSteps after + 1 := by
  obtain ⟨phase, regs, raw, rev, out, ctx, rfl⟩ :=
    owned_cases before ((remainingSteps_pos_iff before).mp positive)
  obtain ⟨after, executed, rank, _⟩ := phase_step_data caller phase raw rev out regs ctx
  exact ⟨after, executed, rank⟩

theorem step_caller_independent (other : External Λ → Statement Γ Λ R)
    (c : Cfg Γ Λ R) (owned : Owned c.l) : step caller c = step other c := by
  obtain ⟨phase, regs, raw, rev, out, ctx, rfl⟩ := owned_cases c owned
  rfl

theorem prefix_local_register (n : Nat) (start reached : Cfg Γ Λ R)
    (bound : n ≤ remainingSteps start)
    (executed : (next caller)^[n] (some start) = some reached)
    (positive : 0 < n) : reached.var.1 = BitDecoderMachine.zeroRegisters := by
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
        simpa only [equal] using canonical
      · exact ih middle reached (by omega) executed (by omega)

/-- Every inclusive prefix of the exact rank exists; every strict prefix is still owned. -/
theorem owned_prefix (start : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start) :
    ∃ reached,
      (next caller)^[n] (some start) = some reached ∧
      remainingSteps reached = remainingSteps start - n ∧
      Relation.ReflTransGen (LocalStep caller) start reached ∧
      (n < remainingSteps start ↔ Owned reached.l) ∧
      (0 < n → reached.var.1 = BitDecoderMachine.zeroRegisters) := by
  obtain ⟨reached, executed, rank, path⟩ := BinaryCounter.FixedWidthMachine.ranked_prefix
    (step caller) remainingSteps (local_progress caller) n start bound
  refine ⟨reached, executed, rank, ?_, ?_, ?_⟩
  · exact Relation.ReflTransGen.mono
      (fun before _ h => ⟨(remainingSteps_pos_iff before).mp h.1, h.2⟩) _ _ path
  · rw [← remainingSteps_pos_iff, rank]
    omega
  · exact prefix_local_register caller n start reached bound executed

theorem phase_prefix (phase : Phase) (raw : Bits) (rev out : Word) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (n : Nat) (bound : n ≤ phaseSteps phase raw rev) :
    ∃ reached,
      (next caller)^[n] (some (cfg (some (phaseLabel phase)) regs raw rev out ctx)) = some reached ∧
      remainingSteps reached = phaseSteps phase raw rev - n ∧
      Relation.ReflTransGen (LocalStep caller)
        (cfg (some (phaseLabel phase)) regs raw rev out ctx) reached ∧
      (n < phaseSteps phase raw rev ↔ Owned reached.l) ∧
      (0 < n → reached.var.1 = BitDecoderMachine.zeroRegisters) :=
  owned_prefix caller _ n bound

theorem prefix_caller_independent (other : External Λ → Statement Γ Λ R)
    (start : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start) :
    (next caller)^[n] (some start) = (next other)^[n] (some start) := by
  exact BinaryCounter.FixedWidthMachine.ranked_prefix_eq (step caller) (step other) remainingSteps
    (local_progress caller)
    (fun c positive => step_caller_independent caller other c ((remainingSteps_pos_iff c).mp positive))
    n start bound

theorem phase_prefix_caller_independent (other : External Λ → Statement Γ Λ R)
    (phase : Phase) (raw : Bits) (rev out : Word) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (n : Nat) (bound : n ≤ phaseSteps phase raw rev) :
    (next caller)^[n] (some (cfg (some (phaseLabel phase)) regs raw rev out ctx)) =
      (next other)^[n] (some (cfg (some (phaseLabel phase)) regs raw rev out ctx)) :=
  prefix_caller_independent caller other _ n bound

theorem first_return (phase : Phase) (raw : Bits) (rev out : Word) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    ∃ reached,
      (next caller)^[phaseSteps phase raw rev]
          (some (cfg (some (phaseLabel phase)) regs raw rev out ctx)) = some reached ∧
      ¬ Owned reached.l ∧
      ∀ n, n < phaseSteps phase raw rev →
        ∃ before, (next caller)^[n]
          (some (cfg (some (phaseLabel phase)) regs raw rev out ctx)) = some before ∧ Owned before.l := by
  obtain ⟨reached, run, _, _, owned, _⟩ :=
    phase_prefix caller phase raw rev out regs ctx (phaseSteps phase raw rev) (Nat.le_refl _)
  refine ⟨reached, run, ?_, ?_⟩
  · intro impossible
    exact (Nat.lt_irrefl _) (owned.mpr impossible)
  · intro n strict
    obtain ⟨before, run, _, _, owned, _⟩ :=
      phase_prefix caller phase raw rev out regs ctx n (Nat.le_of_lt strict)
    exact ⟨before, run, owned.mp strict⟩

/-- Installing these actual owned bodies in a larger caller program preserves the full run. -/
theorem ambient_scan_iterate (ambient : Label Λ → Statement Γ Λ R)
    (agrees : ∀ phase, ambient (phaseLabel phase) = block phase)
    (raw : Bits) (rev out : Word) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (fun c : Option (Cfg Γ Λ R) => c.bind (Turing.TM2.step ambient))^[runSteps raw + rev.length]
        (some (cfg (some (phaseLabel .scan)) regs raw rev out ctx)) =
      some (resultCfg (unpackWordRun raw).1 rev out regs ctx) := by
  rw [program_eq_of_agrees ambient agrees]
  exact scan_iterate _ raw rev out regs ctx

/-- Every protected stack and the caller register survive all owned transitions. -/
theorem local_reaches_frame {start reached : Cfg Γ Λ R}
    (path : Relation.ReflTransGen (LocalStep caller) start reached) :
    reached.var.2 = start.var.2 ∧ ∀ k, reached.stk (.inr k) = start.stk (.inr k) := by
  induction path with
  | refl => exact ⟨rfl, fun _ => rfl⟩
  | @tail before after _ transition ih =>
      obtain ⟨_, _, registers, _, frame⟩ := local_step_data caller transition
      exact ⟨registers.trans ih.1, fun k => (frame k).trans (ih.2 k)⟩

theorem prefix_frame (start reached : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start)
    (executed : (next caller)^[n] (some start) = some reached) :
    reached.var.2 = start.var.2 ∧ ∀ k, reached.stk (.inr k) = start.stk (.inr k) := by
  obtain ⟨actual, run, _, path, _, _⟩ := owned_prefix caller start n bound
  have equal : actual = reached := Option.some.inj (run.symm.trans executed)
  subst actual
  exact local_reaches_frame caller path

/-- Actual occupied cells on the three owned stacks; no finite register is an unbounded store. -/
def ownedCells (c : Cfg Γ Λ R) : Nat :=
  (c.stk (.inl .input)).length + (c.stk (.inl .reverse)).length + (c.stk (.inl .output)).length

variable [Fintype K]

def contextCells (ctx : ∀ k, List (Γ k)) : Nat := ∑ k, (ctx k).length

/-- All physical stack cells, including the arbitrary protected family. -/
def stackCells (c : Cfg Γ Λ R) : Nat := ownedCells c + contextCells (fun k => c.stk (.inr k))

theorem local_step_preserves {before after : Cfg Γ Λ R}
    (transition : LocalStep caller before after) :
    after.var.2 = before.var.2 ∧
      (∀ k, after.stk (.inr k) = before.stk (.inr k)) ∧ stackCells after ≤ stackCells before := by
  obtain ⟨_, _, registers, cells, frame⟩ := local_step_data caller transition
  refine ⟨registers, frame, ?_⟩
  simp only [stackCells, ownedCells, contextCells, frame]
  exact Nat.add_le_add_right cells _

/-- This relation excludes caller bodies; their later allocations are outside the bound. -/
theorem local_reaches_preserves {start reached : Cfg Γ Λ R}
    (path : Relation.ReflTransGen (LocalStep caller) start reached) :
    reached.var.2 = start.var.2 ∧
      (∀ k, reached.stk (.inr k) = start.stk (.inr k)) ∧ stackCells reached ≤ stackCells start := by
  induction path with
  | refl => exact ⟨rfl, fun _ => rfl, Nat.le_refl _⟩
  | @tail before after _ transition ih =>
      obtain ⟨registers, frame, cells⟩ := local_step_preserves caller transition
      exact ⟨registers.trans ih.1, fun k => (frame k).trans (ih.2.1 k), cells.trans ih.2.2⟩

theorem prefix_preserves (start reached : Cfg Γ Λ R) (n : Nat) (bound : n ≤ remainingSteps start)
    (executed : (next caller)^[n] (some start) = some reached) :
    reached.var.2 = start.var.2 ∧
      (∀ k, reached.stk (.inr k) = start.stk (.inr k)) ∧ stackCells reached ≤ stackCells start := by
  obtain ⟨actual, run, _, path, _, _⟩ := owned_prefix caller start n bound
  have equal : actual = reached := Option.some.inj (run.symm.trans executed)
  subst actual
  exact local_reaches_preserves caller path

theorem phase_prefix_stackCells_le (phase : Phase) (raw : Bits) (rev out : Word)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) (n : Nat) (reached : Cfg Γ Λ R)
    (bound : n ≤ phaseSteps phase raw rev)
    (executed : (next caller)^[n]
      (some (cfg (some (phaseLabel phase)) regs raw rev out ctx)) = some reached) :
    stackCells reached ≤ raw.length + rev.length + out.length + contextCells ctx :=
  (prefix_preserves caller (cfg (some (phaseLabel phase)) regs raw rev out ctx)
    reached n bound executed).2.2

/-- The inclusive clean-entry bound is N+U; this direct-output decoder creates no marker. -/
theorem run_prefix_stackCells_le (raw : Bits) (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (n : Nat) (reached : Cfg Γ Λ R) (bound : n ≤ runSteps raw)
    (executed : (next caller)^[n]
      (some (cfg (some (phaseLabel .scan)) regs raw [] [] ctx)) = some reached) :
    stackCells reached ≤ raw.length + contextCells ctx := by
  simpa only [List.length_nil, Nat.add_zero] using
    phase_prefix_stackCells_le caller .scan raw [] [] regs ctx n reached bound executed

omit [DecidableEq K] in
theorem stackCells_cfg (label : Option (Label Λ)) (regs : Registers R)
    (raw : Bits) (rev out : Word) (ctx : ∀ k, List (Γ k)) :
    stackCells (cfg label regs raw rev out ctx) =
      raw.length + rev.length + out.length + contextCells ctx := rfl

variable [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]

/-- One fixed finite program before its input is chosen, with genuinely live result labels. -/
def machine (initial : R) : Turing.FinTM2 where
  K := StackId K
  k₀ := .inl .input
  k₁ := .inl .output
  Γ := alphabet Γ
  Λ := Label Λ
  main := phaseLabel .scan
  σ := Registers R
  initialState := (BitDecoderMachine.zeroRegisters, initial)
  Γk₀Fin := alphabetFintype (.inl .input)
  m := program caller

theorem machine_step_eq (initial : R) (c : Cfg Γ Λ R) :
    (machine caller initial).step c = step caller c := rfl

theorem initList_eq (initial : R) (raw : Bits) :
    Turing.initList (machine caller initial) raw =
      cfg (some (phaseLabel .scan)) (BitDecoderMachine.zeroRegisters, initial)
        raw [] [] (fun _ => []) := by
  apply cfg_ext <;> first | rfl | exact fun _ => rfl

/-- The finite package uses the same actual open run, without a fake halt or output marker. -/
theorem machine_run_source (initial : R) (raw : Bits) :
    (fun c => c.bind (machine caller initial).step)^[runSteps raw]
        (some (Turing.initList (machine caller initial) raw)) =
      some (resultCfg (unpackWordRun raw).1 [] []
        (BitDecoderMachine.zeroRegisters, initial) (fun _ => [])) := by
  change (next caller)^[runSteps raw]
      (some (Turing.initList (machine caller initial) raw)) = _
  rw [initList_eq]
  exact run_source caller raw (BitDecoderMachine.zeroRegisters, initial) (fun _ => [])

def machineInTime (initial : R) (raw : Bits) :
    StateTransition.EvalsToInTime (machine caller initial).step
      (Turing.initList (machine caller initial) raw)
      (some (resultCfg (unpackWordRun raw).1 [] []
        (BitDecoderMachine.zeroRegisters, initial) (fun _ => []))) (raw.length + 2) where
  steps := runSteps raw
  evals_in_steps := machine_run_source caller initial raw
  steps_le_m := runSteps_le raw

end Resources.RotationCertificate.OpenDecoderMachine
