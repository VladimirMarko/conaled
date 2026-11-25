import Applications.Resources.RotationCertificate.BitPairFraming
import Applications.Resources.BinaryCounter.FixedWidthMachine

/-!
# Open binary pair framing on physical output stacks

The five finite blocks consume a guarded input prefix and copy its certificate
tail. They return the two actual Bool lists on separate stacks at live caller
labels. No statement allocates a result marker or calls a source parser.
Correspondence: `docs/research/fdsa-rotation-certificate-preparation.md`.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.RotationCertificate.OpenFramingMachine
open Resources.BinaryCounter (Bits)

inductive LocalStack
  | raw | firstReverse | certificateReverse | inputBits | certificateBits
  deriving DecidableEq

instance : Fintype LocalStack where
  elems := {.raw, .firstReverse, .certificateReverse, .inputBits, .certificateBits}
  complete slot := by cases slot <;> decide

abbrev Phase := BitPairFraming.Label

inductive Result
  | success | failure
  deriving DecidableEq

instance : Fintype Result where
  elems := {.success, .failure}
  complete result := by cases result <;> decide

abbrev StackId (K : Type) := LocalStack ⊕ K
abbrev External (Λ : Type) := Result ⊕ Λ
abbrev Label (Λ : Type) := Phase ⊕ External Λ
abbrev Registers (R : Type) := Option Bool × R

variable {K Λ R : Type} {Γ : K → Type}

abbrev alphabet (Γ : K → Type) : StackId K → Type
  | .inl _ => Bool
  | .inr k => Γ k

instance alphabetFintype [∀ k, Fintype (Γ k)] (k : StackId K) :
    Fintype (alphabet Γ k) := by
  cases k <;> exact inferInstance

abbrev Statement (Γ : K → Type) (Λ R : Type) :=
  Turing.TM2.Stmt (alphabet Γ) (Label Λ) (Registers R)
abbrev Cfg (Γ : K → Type) (Λ R : Type) :=
  Turing.TM2.Cfg (alphabet Γ) (Label Λ) (Registers R)

def phaseLabel (phase : Phase) : Label Λ := .inl phase
def resultLabel (result : Result) : Label Λ := .inr (.inl result)
def callerLabel (label : Λ) : Label Λ := .inr (.inr label)

def reset (regs : Registers R) : Registers R := (none, regs.2)
def store (regs : Registers R) (bit : Option Bool) : Registers R := (bit, regs.2)

@[simp] theorem reset_reset (regs : Registers R) : reset (reset regs) = reset regs := rfl

def jump (label : Label Λ) : Statement Γ Λ R :=
  .load reset (.goto (fun _ => label))

/-- Each callback reads only the finite temporary overwritten by its actual pop. -/
def block : Phase → Statement Γ Λ R
  | .scanPrefix =>
      .pop (.inl .raw) store (.branch (fun regs => regs.1.isSome)
        (.branch (fun regs => regs.1.getD false)
          (jump (phaseLabel .copyCert))
          (.pop (.inl .raw) store (.branch (fun regs => regs.1.isSome)
            (.push (.inl .firstReverse) (fun regs => regs.1.getD false)
              (jump (phaseLabel .scanPrefix)))
            (jump (phaseLabel .clearFirst)))))
        (jump (phaseLabel .clearFirst)))
  | .copyCert =>
      .pop (.inl .raw) store (.branch (fun regs => regs.1.isSome)
        (.push (.inl .certificateReverse) (fun regs => regs.1.getD false)
          (jump (phaseLabel .copyCert)))
        (jump (phaseLabel .emitCert)))
  | .emitCert =>
      .pop (.inl .certificateReverse) store (.branch (fun regs => regs.1.isSome)
        (.push (.inl .certificateBits) (fun regs => regs.1.getD false)
          (jump (phaseLabel .emitCert)))
        (jump (phaseLabel .emitFirst)))
  | .emitFirst =>
      .pop (.inl .firstReverse) store (.branch (fun regs => regs.1.isSome)
        (.push (.inl .inputBits) (fun regs => regs.1.getD false)
          (jump (phaseLabel .emitFirst)))
        (jump (resultLabel .success)))
  | .clearFirst =>
      .pop (.inl .firstReverse) store (.branch (fun regs => regs.1.isSome)
        (jump (phaseLabel .clearFirst)) (jump (resultLabel .failure)))

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

def cfg (label : Option (Label Λ)) (regs : Registers R)
    (raw firstRev certRev input cert : Bits) (ctx : ∀ k, List (Γ k)) : Cfg Γ Λ R where
  l := label
  var := regs
  stk
    | .inl .raw => raw
    | .inl .firstReverse => firstRev
    | .inl .certificateReverse => certRev
    | .inl .inputBits => input
    | .inl .certificateBits => cert
    | .inr k => ctx k

theorem cfg_ext {left right : Cfg Γ Λ R}
    (label : left.l = right.l) (regs : left.var = right.var)
    (raw : left.stk (.inl .raw) = right.stk (.inl .raw))
    (firstRev : left.stk (.inl .firstReverse) = right.stk (.inl .firstReverse))
    (certRev : left.stk (.inl .certificateReverse) = right.stk (.inl .certificateReverse))
    (input : left.stk (.inl .inputBits) = right.stk (.inl .inputBits))
    (cert : left.stk (.inl .certificateBits) = right.stk (.inl .certificateBits))
    (ctx : ∀ k, left.stk (.inr k) = right.stk (.inr k)) : left = right := by
  have stackEq : left.stk = right.stk := by
    funext k
    cases k with
    | inl slot => cases slot with
      | raw => exact raw
      | firstReverse => exact firstRev
      | certificateReverse => exact certRev
      | inputBits => exact input
      | certificateBits => exact cert
    | inr k => exact ctx k
  cases left
  cases right
  cases label
  cases regs
  cases stackEq
  rfl

theorem cfg_eta (c : Cfg Γ Λ R) :
    cfg c.l c.var (c.stk (.inl .raw)) (c.stk (.inl .firstReverse))
      (c.stk (.inl .certificateReverse)) (c.stk (.inl .inputBits))
      (c.stk (.inl .certificateBits)) (fun k => c.stk (.inr k)) = c := by
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

theorem scanPrefix_step_nil (firstRev certRev input cert : Bits) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel .scanPrefix)) regs [] firstRev certRev input cert ctx) =
      some (cfg (some (phaseLabel .clearFirst)) (reset regs) [] firstRev certRev input cert ctx) := by
  apply congrArg some; apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem scanPrefix_step_false_nil (firstRev certRev input cert : Bits) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel .scanPrefix)) regs [false] firstRev certRev input cert ctx) =
      some (cfg (some (phaseLabel .clearFirst)) (reset regs) [] firstRev certRev input cert ctx) := by
  apply congrArg some; apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem scanPrefix_step_false_cons (bit : Bool) (raw firstRev certRev input cert : Bits)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel .scanPrefix)) regs (false :: bit :: raw)
        firstRev certRev input cert ctx) =
      some (cfg (some (phaseLabel .scanPrefix)) (reset regs) raw
        (bit :: firstRev) certRev input cert ctx) := by
  apply congrArg some; apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem scanPrefix_step_true (raw firstRev certRev input cert : Bits) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel .scanPrefix)) regs (true :: raw) firstRev certRev input cert ctx) =
      some (cfg (some (phaseLabel .copyCert)) (reset regs) raw firstRev certRev input cert ctx) := by
  apply congrArg some; apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem copyCert_step_cons (bit : Bool) (raw firstRev certRev input cert : Bits)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel .copyCert)) regs (bit :: raw) firstRev certRev input cert ctx) =
      some (cfg (some (phaseLabel .copyCert)) (reset regs) raw firstRev (bit :: certRev) input cert ctx) := by
  apply congrArg some; apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem copyCert_step_nil (firstRev certRev input cert : Bits) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel .copyCert)) regs [] firstRev certRev input cert ctx) =
      some (cfg (some (phaseLabel .emitCert)) (reset regs) [] firstRev certRev input cert ctx) := by
  apply congrArg some; apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem emitCert_step_cons (bit : Bool) (raw firstRev certRev input cert : Bits)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel .emitCert)) regs raw firstRev (bit :: certRev) input cert ctx) =
      some (cfg (some (phaseLabel .emitCert)) (reset regs) raw firstRev certRev input (bit :: cert) ctx) := by
  apply congrArg some; apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem emitCert_step_nil (raw firstRev input cert : Bits) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel .emitCert)) regs raw firstRev [] input cert ctx) =
      some (cfg (some (phaseLabel .emitFirst)) (reset regs) raw firstRev [] input cert ctx) := by
  apply congrArg some; apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem emitFirst_step_cons (bit : Bool) (raw firstRev certRev input cert : Bits)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel .emitFirst)) regs raw (bit :: firstRev) certRev input cert ctx) =
      some (cfg (some (phaseLabel .emitFirst)) (reset regs) raw firstRev certRev (bit :: input) cert ctx) := by
  apply congrArg some; apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem emitFirst_step_nil (raw certRev input cert : Bits) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel .emitFirst)) regs raw [] certRev input cert ctx) =
      some (cfg (some (resultLabel .success)) (reset regs) raw [] certRev input cert ctx) := by
  apply congrArg some; apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem clearFirst_step_cons (bit : Bool) (raw firstRev certRev input cert : Bits)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel .clearFirst)) regs raw (bit :: firstRev) certRev input cert ctx) =
      some (cfg (some (phaseLabel .clearFirst)) (reset regs) raw firstRev certRev input cert ctx) := by
  apply congrArg some; apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem clearFirst_step_nil (raw certRev input cert : Bits) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel .clearFirst)) regs raw [] certRev input cert ctx) =
      some (cfg (some (resultLabel .failure)) (reset regs) raw [] certRev input cert ctx) := by
  apply congrArg some; apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem emitFirst_iterate (raw firstRev certRev input cert : Bits) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    (next caller)^[firstRev.length + 1]
        (some (cfg (some (phaseLabel .emitFirst)) regs raw firstRev certRev input cert ctx)) =
      some (cfg (some (resultLabel .success)) (reset regs) raw [] certRev
        (firstRev.reverse ++ input) cert ctx) := by
  induction firstRev generalizing input regs with
  | nil => simp only [List.length_nil, Nat.zero_add, Function.iterate_one, next_some,
      emitFirst_step_nil, List.reverse_nil, List.nil_append]
  | cons bit firstRev ih =>
      rw [show (bit :: firstRev).length + 1 = (firstRev.length + 1) + 1 by rfl,
        iterate_step caller _ _ _ (emitFirst_step_cons caller bit raw firstRev certRev input cert regs ctx), ih]
      simp [List.reverse_cons, List.append_assoc]

theorem clearFirst_iterate (raw firstRev certRev input cert : Bits) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    (next caller)^[firstRev.length + 1]
        (some (cfg (some (phaseLabel .clearFirst)) regs raw firstRev certRev input cert ctx)) =
      some (cfg (some (resultLabel .failure)) (reset regs) raw [] certRev input cert ctx) := by
  induction firstRev generalizing regs with
  | nil => simp only [List.length_nil, Nat.zero_add, Function.iterate_one, next_some,
      clearFirst_step_nil]
  | cons bit firstRev ih =>
      rw [show (bit :: firstRev).length + 1 = (firstRev.length + 1) + 1 by rfl,
        iterate_step caller _ _ _ (clearFirst_step_cons caller bit raw firstRev certRev input cert regs ctx), ih]
      simp only [reset_reset]

theorem emitCert_iterate (raw firstRev certRev input cert : Bits) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    (next caller)^[certRev.length + firstRev.length + 2]
        (some (cfg (some (phaseLabel .emitCert)) regs raw firstRev certRev input cert ctx)) =
      some (cfg (some (resultLabel .success)) (reset regs) raw [] []
        (firstRev.reverse ++ input) (certRev.reverse ++ cert) ctx) := by
  induction certRev generalizing cert regs with
  | nil =>
      rw [show ([] : Bits).length + firstRev.length + 2 = (firstRev.length + 1) + 1 by simp,
        iterate_step caller _ _ _ (emitCert_step_nil caller raw firstRev input cert regs ctx),
        emitFirst_iterate]
      simp
  | cons bit certRev ih =>
      rw [show (bit :: certRev).length + firstRev.length + 2 =
          (certRev.length + firstRev.length + 2) + 1 by simp only [List.length_cons]; omega,
        iterate_step caller _ _ _ (emitCert_step_cons caller bit raw firstRev certRev input cert regs ctx), ih]
      simp [List.reverse_cons, List.append_assoc]

theorem copyCert_iterate (raw firstRev certRev input cert : Bits) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    (next caller)^[2 * raw.length + certRev.length + firstRev.length + 3]
        (some (cfg (some (phaseLabel .copyCert)) regs raw firstRev certRev input cert ctx)) =
      some (cfg (some (resultLabel .success)) (reset regs) [] [] []
        (firstRev.reverse ++ input) (certRev.reverse ++ raw ++ cert) ctx) := by
  induction raw generalizing certRev regs with
  | nil =>
      rw [show 2 * ([] : Bits).length + certRev.length + firstRev.length + 3 =
          (certRev.length + firstRev.length + 2) + 1 by simp,
        iterate_step caller _ _ _ (copyCert_step_nil caller firstRev certRev input cert regs ctx),
        emitCert_iterate]
      simp
  | cons bit raw ih =>
      rw [show 2 * (bit :: raw).length + certRev.length + firstRev.length + 3 =
          (2 * raw.length + (bit :: certRev).length + firstRev.length + 3) + 1 by
            simp only [List.length_cons]; omega,
        iterate_step caller _ _ _ (copyCert_step_cons caller bit raw firstRev certRev input cert regs ctx), ih]
      simp [List.reverse_cons, List.append_assoc]


/-- Proof-side exact rank at a scan entry, including dirty reverse accumulators. -/
def scanSteps (raw firstRev certRev : Bits) : Nat :=
  BitPairFraming.runSteps raw + firstRev.length +
    match BitPairFraming.unframe raw with
    | none => 0
    | some _ => certRev.length

def scanResult (regs : Registers R) (firstRev certRev input cert : Bits)
    (ctx : ∀ k, List (Γ k)) : Option (Bits × Bits) → Cfg Γ Λ R
  | none => cfg (some (resultLabel .failure)) (reset regs) [] [] certRev input cert ctx
  | some pair => cfg (some (resultLabel .success)) (reset regs) [] [] []
      (firstRev.reverse ++ pair.1 ++ input) (certRev.reverse ++ pair.2 ++ cert) ctx

theorem runSteps_pos (raw : Bits) : 0 < BitPairFraming.runSteps raw := by
  induction raw using BitPairFraming.unframe.induct with
  | case1 => decide
  | case2 cert => simp [BitPairFraming.runSteps]
  | case3 => decide
  | case4 bit raw ih => simp only [BitPairFraming.runSteps]; omega

theorem scanSteps_pos (raw firstRev certRev : Bits) : 0 < scanSteps raw firstRev certRev := by
  have positive := runSteps_pos raw
  unfold scanSteps
  omega

theorem scanSteps_false_cons (bit : Bool) (raw firstRev certRev : Bits) :
    scanSteps (false :: bit :: raw) firstRev certRev =
      scanSteps raw (bit :: firstRev) certRev + 1 := by
  unfold scanSteps
  rw [BitPairFraming.runSteps, BitPairFraming.unframe_false_cons]
  cases BitPairFraming.unframe raw <;> simp <;> omega

/-- This is a real execution from arbitrary dirty accumulators and old outputs. -/
theorem scanPrefix_iterate (raw firstRev certRev input cert : Bits) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    (next caller)^[scanSteps raw firstRev certRev]
        (some (cfg (some (phaseLabel .scanPrefix)) regs raw firstRev certRev input cert ctx)) =
      some (scanResult regs firstRev certRev input cert ctx (BitPairFraming.unframe raw)) := by
  induction raw using BitPairFraming.unframe.induct generalizing firstRev regs with
  | case1 =>
      rw [show scanSteps [] firstRev certRev = (firstRev.length + 1) + 1 by
          simp [scanSteps, BitPairFraming.runSteps]; omega,
        iterate_step caller _ _ _ (scanPrefix_step_nil caller firstRev certRev input cert regs ctx),
        clearFirst_iterate]
      rfl
  | case2 raw =>
      rw [show scanSteps (true :: raw) firstRev certRev =
          (2 * raw.length + certRev.length + firstRev.length + 3) + 1 by
            simp [scanSteps, BitPairFraming.runSteps]; omega,
        iterate_step caller _ _ _ (scanPrefix_step_true caller raw firstRev certRev input cert regs ctx),
        copyCert_iterate]
      simp [scanResult, List.append_assoc]
  | case3 =>
      rw [show scanSteps [false] firstRev certRev = (firstRev.length + 1) + 1 by
          simp [scanSteps, BitPairFraming.runSteps]; omega,
        iterate_step caller _ _ _
          (scanPrefix_step_false_nil caller firstRev certRev input cert regs ctx), clearFirst_iterate]
      rfl
  | case4 bit raw ih =>
      rw [scanSteps_false_cons, iterate_step caller _ _ _
        (scanPrefix_step_false_cons caller bit raw firstRev certRev input cert regs ctx), ih,
        BitPairFraming.unframe_false_cons]
      cases BitPairFraming.unframe raw <;>
        simp [scanResult, List.reverse_cons, List.append_assoc]

theorem scanPrefix_frame (first second firstRev certRev input cert : Bits)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (next caller)^[2 * first.length + 2 * second.length + firstRev.length + certRev.length + 4]
        (some (cfg (some (phaseLabel .scanPrefix)) regs (BitPairFraming.frame first second)
          firstRev certRev input cert ctx)) =
      some (cfg (some (resultLabel .success)) (reset regs) [] [] []
        (firstRev.reverse ++ first ++ input) (certRev.reverse ++ second ++ cert) ctx) := by
  have run := scanPrefix_iterate caller (BitPairFraming.frame first second)
    firstRev certRev input cert regs ctx
  have count : scanSteps (BitPairFraming.frame first second) firstRev certRev =
      2 * first.length + 2 * second.length + firstRev.length + certRev.length + 4 := by
    simp [scanSteps, BitPairFraming.runSteps_frame, BitPairFraming.unframe_frame]; omega
  simpa only [count, BitPairFraming.unframe_frame, scanResult] using run

theorem scanPrefix_missing_delimiter (pref firstRev certRev input cert : Bits)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (next caller)^[2 * pref.length + firstRev.length + 2]
        (some (cfg (some (phaseLabel .scanPrefix)) regs (BitPairFraming.escapeBits pref)
          firstRev certRev input cert ctx)) =
      some (cfg (some (resultLabel .failure)) (reset regs) [] [] certRev input cert ctx) := by
  have run := scanPrefix_iterate caller (BitPairFraming.escapeBits pref)
    firstRev certRev input cert regs ctx
  have count : scanSteps (BitPairFraming.escapeBits pref) firstRev certRev =
      2 * pref.length + firstRev.length + 2 := by
    simp [scanSteps, BitPairFraming.runSteps_missing_delimiter,
      BitPairFraming.unframe_missing_delimiter]
    omega
  simpa only [count, BitPairFraming.unframe_missing_delimiter, scanResult] using run

theorem scanPrefix_incomplete_guard (pref firstRev certRev input cert : Bits)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (next caller)^[2 * pref.length + firstRev.length + 2]
        (some (cfg (some (phaseLabel .scanPrefix)) regs (BitPairFraming.escapeBits pref ++ [false])
          firstRev certRev input cert ctx)) =
      some (cfg (some (resultLabel .failure)) (reset regs) [] [] certRev input cert ctx) := by
  have run := scanPrefix_iterate caller (BitPairFraming.escapeBits pref ++ [false])
    firstRev certRev input cert regs ctx
  have count : scanSteps (BitPairFraming.escapeBits pref ++ [false]) firstRev certRev =
      2 * pref.length + firstRev.length + 2 := by
    simp [scanSteps, BitPairFraming.runSteps_incomplete_guard,
      BitPairFraming.unframe_incomplete_guard]
    omega
  simpa only [count, BitPairFraming.unframe_incomplete_guard, scanResult] using run

theorem run_source (raw : Bits) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (next caller)^[BitPairFraming.runSteps raw]
        (some (cfg (some (phaseLabel .scanPrefix)) regs raw [] [] [] [] ctx)) =
      some (scanResult regs [] [] [] [] ctx (BitPairFraming.unframe raw)) := by
  have count : scanSteps raw [] [] = BitPairFraming.runSteps raw := by
    unfold scanSteps
    cases BitPairFraming.unframe raw <;> simp
  simpa only [count] using scanPrefix_iterate caller raw [] [] [] [] regs ctx

theorem run_of_some (raw first second : Bits) (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (parsed : BitPairFraming.unframe raw = some (first, second)) :
    (next caller)^[BitPairFraming.runSteps raw]
        (some (cfg (some (phaseLabel .scanPrefix)) regs raw [] [] [] [] ctx)) =
      some (cfg (some (resultLabel .success)) (reset regs) [] [] [] first second ctx) := by
  simpa [parsed, scanResult] using run_source caller raw regs ctx

theorem run_of_none (raw : Bits) (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (parsed : BitPairFraming.unframe raw = none) :
    (next caller)^[BitPairFraming.runSteps raw]
        (some (cfg (some (phaseLabel .scanPrefix)) regs raw [] [] [] [] ctx)) =
      some (cfg (some (resultLabel .failure)) (reset regs) [] [] [] [] [] ctx) := by
  simpa only [parsed, scanResult] using run_source caller raw regs ctx

theorem run_frame (first second : Bits) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (next caller)^[2 * first.length + 2 * second.length + 4]
        (some (cfg (some (phaseLabel .scanPrefix)) regs (BitPairFraming.frame first second)
          [] [] [] [] ctx)) =
      some (cfg (some (resultLabel .success)) (reset regs) [] [] [] first second ctx) := by
  simpa using scanPrefix_frame caller first second [] [] [] [] regs ctx

def runInTime (raw : Bits) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller)
      (cfg (some (phaseLabel .scanPrefix)) regs raw [] [] [] [] ctx)
      (some (scanResult regs [] [] [] [] ctx (BitPairFraming.unframe raw)))
      (BitPairFraming.runSteps raw) where
  steps := BitPairFraming.runSteps raw
  evals_in_steps := run_source caller raw regs ctx
  steps_le_m := Nat.le_refl _

def runInLinearTime (raw : Bits) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller)
      (cfg (some (phaseLabel .scanPrefix)) regs raw [] [] [] [] ctx)
      (some (scanResult regs [] [] [] [] ctx (BitPairFraming.unframe raw)))
      (2 * raw.length + 2) where
  steps := BitPairFraming.runSteps raw
  evals_in_steps := run_source caller raw regs ctx
  steps_le_m := BitPairFraming.runSteps_le raw


def phaseSteps : Phase → Bits → Bits → Bits → Nat
  | .scanPrefix, raw, firstRev, certRev => scanSteps raw firstRev certRev
  | .copyCert, raw, firstRev, certRev => 2 * raw.length + certRev.length + firstRev.length + 3
  | .emitCert, _, firstRev, certRev => certRev.length + firstRev.length + 2
  | .emitFirst, _, firstRev, _ => firstRev.length + 1
  | .clearFirst, _, firstRev, _ => firstRev.length + 1

def Owned : Option (Label Λ) → Prop
  | some (.inl _) => True
  | _ => False

def remainingSteps (c : Cfg Γ Λ R) : Nat :=
  match c.l with
  | some (.inl phase) => phaseSteps phase (c.stk (.inl .raw))
      (c.stk (.inl .firstReverse)) (c.stk (.inl .certificateReverse))
  | _ => 0

def ownedCells (c : Cfg Γ Λ R) : Nat :=
  (c.stk (.inl .raw)).length + (c.stk (.inl .firstReverse)).length +
    (c.stk (.inl .certificateReverse)).length + (c.stk (.inl .inputBits)).length +
    (c.stk (.inl .certificateBits)).length

omit [DecidableEq K] in
theorem remainingSteps_pos_iff (c : Cfg Γ Λ R) :
    0 < remainingSteps c ↔ Owned c.l := by
  cases labelEq : c.l with
  | none => simp [remainingSteps, Owned, labelEq]
  | some label => cases label with
    | inr external => simp [remainingSteps, Owned, labelEq]
    | inl phase =>
        cases phase with
        | scanPrefix =>
            simp only [remainingSteps, labelEq, phaseSteps, Owned, iff_true]
            exact scanSteps_pos _ _ _
        | copyCert => simp [remainingSteps, labelEq, phaseSteps, Owned]
        | emitCert => simp [remainingSteps, labelEq, phaseSteps, Owned]
        | emitFirst => simp [remainingSteps, labelEq, phaseSteps, Owned]
        | clearFirst => simp [remainingSteps, labelEq, phaseSteps, Owned]

omit [DecidableEq K] in
theorem owned_cases (c : Cfg Γ Λ R) (owned : Owned c.l) :
    ∃ phase regs raw firstRev certRev input cert ctx,
      c = cfg (some (phaseLabel phase)) regs raw firstRev certRev input cert ctx := by
  cases labelEq : c.l with
  | none => simp [Owned, labelEq] at owned
  | some label => cases label with
    | inr external => simp [Owned, labelEq] at owned
    | inl phase =>
        refine ⟨phase, c.var, c.stk (.inl .raw), c.stk (.inl .firstReverse),
          c.stk (.inl .certificateReverse), c.stk (.inl .inputBits),
          c.stk (.inl .certificateBits), (fun k => c.stk (.inr k)), ?_⟩
        simpa only [labelEq, phaseLabel] using (cfg_eta c).symm

/-- Every owned primitive step resets its local field, preserves the complete
protected context, decreases the exact rank by one, and allocates no cell. -/
theorem phase_step_data (phase : Phase) (raw firstRev certRev input cert : Bits)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ∃ reached,
      step caller (cfg (some (phaseLabel phase)) regs raw firstRev certRev input cert ctx) =
        some reached ∧
      phaseSteps phase raw firstRev certRev = remainingSteps reached + 1 ∧
      reached.var = reset regs ∧
      (∀ k, reached.stk (.inr k) = ctx k) ∧
      ownedCells reached ≤ raw.length + firstRev.length + certRev.length + input.length + cert.length := by
  cases phase with
  | scanPrefix =>
      cases raw with
      | nil =>
          refine ⟨_, scanPrefix_step_nil caller firstRev certRev input cert regs ctx,
            ?_, rfl, fun _ => rfl, ?_⟩
          · simp [phaseSteps, remainingSteps, cfg, phaseLabel, scanSteps, BitPairFraming.runSteps]; omega
          · simp [ownedCells, cfg]
      | cons flag raw =>
          cases flag with
          | false =>
              cases raw with
              | nil =>
                  refine ⟨_, scanPrefix_step_false_nil caller firstRev certRev input cert regs ctx,
                    ?_, rfl, fun _ => rfl, ?_⟩
                  · simp [phaseSteps, remainingSteps, cfg, phaseLabel, scanSteps, BitPairFraming.runSteps]; omega
                  · simp [ownedCells, cfg]
              | cons bit raw =>
                  refine ⟨_, scanPrefix_step_false_cons caller bit raw firstRev certRev input cert regs ctx,
                    ?_, rfl, fun _ => rfl, ?_⟩
                  · exact scanSteps_false_cons bit raw firstRev certRev
                  · simp [ownedCells, cfg]; omega
          | true =>
              refine ⟨_, scanPrefix_step_true caller raw firstRev certRev input cert regs ctx,
                ?_, rfl, fun _ => rfl, ?_⟩
              · simp [phaseSteps, remainingSteps, cfg, phaseLabel, scanSteps, BitPairFraming.runSteps]; omega
              · simp [ownedCells, cfg]
  | copyCert =>
      cases raw with
      | nil =>
          refine ⟨_, copyCert_step_nil caller firstRev certRev input cert regs ctx,
            ?_, rfl, fun _ => rfl, ?_⟩
          · simp [phaseSteps, remainingSteps, cfg, phaseLabel]
          · simp [ownedCells, cfg]
      | cons bit raw =>
          refine ⟨_, copyCert_step_cons caller bit raw firstRev certRev input cert regs ctx,
            ?_, rfl, fun _ => rfl, ?_⟩
          · simp [phaseSteps, remainingSteps, cfg, phaseLabel]; omega
          · simp [ownedCells, cfg]; omega
  | emitCert =>
      cases certRev with
      | nil =>
          refine ⟨_, emitCert_step_nil caller raw firstRev input cert regs ctx,
            ?_, rfl, fun _ => rfl, ?_⟩
          · simp [phaseSteps, remainingSteps, cfg, phaseLabel]
          · simp [ownedCells, cfg]
      | cons bit certRev =>
          refine ⟨_, emitCert_step_cons caller bit raw firstRev certRev input cert regs ctx,
            ?_, rfl, fun _ => rfl, ?_⟩
          · simp [phaseSteps, remainingSteps, cfg, phaseLabel]; omega
          · simp [ownedCells, cfg]; omega
  | emitFirst =>
      cases firstRev with
      | nil =>
          refine ⟨_, emitFirst_step_nil caller raw certRev input cert regs ctx,
            rfl, rfl, fun _ => rfl, ?_⟩
          simp [ownedCells, cfg]
      | cons bit firstRev =>
          refine ⟨_, emitFirst_step_cons caller bit raw firstRev certRev input cert regs ctx,
            rfl, rfl, fun _ => rfl, ?_⟩
          simp [ownedCells, cfg]; omega
  | clearFirst =>
      cases firstRev with
      | nil =>
          refine ⟨_, clearFirst_step_nil caller raw certRev input cert regs ctx,
            rfl, rfl, fun _ => rfl, ?_⟩
          simp [ownedCells, cfg]
      | cons bit firstRev =>
          refine ⟨_, clearFirst_step_cons caller bit raw firstRev certRev input cert regs ctx,
            rfl, rfl, fun _ => rfl, ?_⟩
          simp [ownedCells, cfg]

def LocalStep (before after : Cfg Γ Λ R) : Prop :=
  Owned before.l ∧ step caller before = some after

theorem local_step_data {before after : Cfg Γ Λ R}
    (transition : LocalStep caller before after) :
    remainingSteps before = remainingSteps after + 1 ∧ after.var = reset before.var ∧
      (∀ k, after.stk (.inr k) = before.stk (.inr k)) ∧ ownedCells after ≤ ownedCells before := by
  obtain ⟨phase, regs, raw, firstRev, certRev, input, cert, ctx, rfl⟩ :=
    owned_cases before transition.1
  obtain ⟨reached, executed, rank, registers, frame, cells⟩ :=
    phase_step_data caller phase raw firstRev certRev input cert regs ctx
  have equal : reached = after := Option.some.inj (executed.symm.trans transition.2)
  subst after
  exact ⟨rank, registers, frame, cells⟩

theorem local_progress (before : Cfg Γ Λ R) (positive : 0 < remainingSteps before) :
    ∃ after, step caller before = some after ∧ remainingSteps before = remainingSteps after + 1 := by
  obtain ⟨phase, regs, raw, firstRev, certRev, input, cert, ctx, rfl⟩ :=
    owned_cases before ((remainingSteps_pos_iff before).mp positive)
  obtain ⟨after, executed, rank, _⟩ :=
    phase_step_data caller phase raw firstRev certRev input cert regs ctx
  exact ⟨after, executed, rank⟩

theorem step_caller_independent (other : External Λ → Statement Γ Λ R)
    (c : Cfg Γ Λ R) (owned : Owned c.l) : step caller c = step other c := by
  obtain ⟨phase, regs, raw, firstRev, certRev, input, cert, ctx, rfl⟩ := owned_cases c owned
  rfl

theorem prefix_local_register (n : Nat) (start reached : Cfg Γ Λ R)
    (bound : n ≤ remainingSteps start)
    (executed : (next caller)^[n] (some start) = some reached)
    (positive : 0 < n) : reached.var.1 = none := by
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

theorem phase_prefix (phase : Phase) (raw firstRev certRev input cert : Bits)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) (n : Nat)
    (bound : n ≤ phaseSteps phase raw firstRev certRev) :
    ∃ reached,
      (next caller)^[n]
          (some (cfg (some (phaseLabel phase)) regs raw firstRev certRev input cert ctx)) =
        some reached ∧
      remainingSteps reached = phaseSteps phase raw firstRev certRev - n ∧
      Relation.ReflTransGen (LocalStep caller)
        (cfg (some (phaseLabel phase)) regs raw firstRev certRev input cert ctx) reached ∧
      (n < phaseSteps phase raw firstRev certRev ↔ Owned reached.l) ∧
      (0 < n → reached.var.1 = none) := by
  obtain ⟨reached, executed, rank, path⟩ := Resources.BinaryCounter.FixedWidthMachine.ranked_prefix
    (step caller) remainingSteps (local_progress caller) n
    (cfg (some (phaseLabel phase)) regs raw firstRev certRev input cert ctx) bound
  change remainingSteps reached = phaseSteps phase raw firstRev certRev - n at rank
  refine ⟨reached, executed, rank, ?_, ?_, ?_⟩
  · exact Relation.ReflTransGen.mono
      (fun before _ h => ⟨(remainingSteps_pos_iff before).mp h.1, h.2⟩) _ _ path
  · rw [← remainingSteps_pos_iff, rank]
    omega
  · exact prefix_local_register caller n
      (cfg (some (phaseLabel phase)) regs raw firstRev certRev input cert ctx) reached bound executed

theorem run_prefix (raw : Bits) (regs : Registers R) (ctx : ∀ k, List (Γ k)) (n : Nat)
    (bound : n ≤ BitPairFraming.runSteps raw) :
    ∃ reached,
      (next caller)^[n] (some (cfg (some (phaseLabel .scanPrefix)) regs raw [] [] [] [] ctx)) =
        some reached ∧
      remainingSteps reached = BitPairFraming.runSteps raw - n ∧
      Relation.ReflTransGen (LocalStep caller)
        (cfg (some (phaseLabel .scanPrefix)) regs raw [] [] [] [] ctx) reached ∧
      (n < BitPairFraming.runSteps raw ↔ Owned reached.l) ∧
      (0 < n → reached.var.1 = none) := by
  have count : phaseSteps .scanPrefix raw [] [] = BitPairFraming.runSteps raw := by
    change scanSteps raw [] [] = BitPairFraming.runSteps raw
    unfold scanSteps
    split <;> simp
  simpa only [count] using
    phase_prefix caller .scanPrefix raw [] [] [] [] regs ctx n (count.symm ▸ bound)

theorem phase_prefix_caller_independent (other : External Λ → Statement Γ Λ R)
    (phase : Phase) (raw firstRev certRev input cert : Bits) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (n : Nat) (bound : n ≤ phaseSteps phase raw firstRev certRev) :
    (next caller)^[n]
        (some (cfg (some (phaseLabel phase)) regs raw firstRev certRev input cert ctx)) =
      (next other)^[n]
        (some (cfg (some (phaseLabel phase)) regs raw firstRev certRev input cert ctx)) := by
  exact Resources.BinaryCounter.FixedWidthMachine.ranked_prefix_eq
    (step caller) (step other) remainingSteps (local_progress caller)
    (fun c positive => step_caller_independent caller other c ((remainingSteps_pos_iff c).mp positive))
    n _ bound

theorem local_reaches_preserves {start reached : Cfg Γ Λ R}
    (path : Relation.ReflTransGen (LocalStep caller) start reached) :
    reached.var.2 = start.var.2 ∧ (∀ k, reached.stk (.inr k) = start.stk (.inr k)) ∧
      ownedCells reached ≤ ownedCells start := by
  induction path with
  | refl => exact ⟨rfl, fun _ => rfl, Nat.le_refl _⟩
  | @tail before after _ transition ih =>
      obtain ⟨_, registers, frame, cells⟩ := local_step_data caller transition
      refine ⟨?_, fun k => (frame k).trans (ih.2.1 k), cells.trans ih.2.2⟩
      simpa only [registers, reset] using ih.1

theorem prefix_preserves (phase : Phase) (raw firstRev certRev input cert : Bits)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) (n : Nat) (reached : Cfg Γ Λ R)
    (bound : n ≤ phaseSteps phase raw firstRev certRev)
    (executed : (next caller)^[n]
      (some (cfg (some (phaseLabel phase)) regs raw firstRev certRev input cert ctx)) = some reached) :
    reached.var.2 = regs.2 ∧ (∀ k, reached.stk (.inr k) = ctx k) ∧
      ownedCells reached ≤ raw.length + firstRev.length + certRev.length + input.length + cert.length := by
  obtain ⟨actual, run, _, path, _, _⟩ :=
    phase_prefix caller phase raw firstRev certRev input cert regs ctx n bound
  have equal : actual = reached := Option.some.inj (run.symm.trans executed)
  subst reached
  exact local_reaches_preserves caller path


theorem scanPrefix_prefix (accepted raw firstRev certRev input cert : Bits)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (next caller)^[accepted.length]
        (some (cfg (some (phaseLabel .scanPrefix)) regs
          (BitPairFraming.escapeBits accepted ++ raw) firstRev certRev input cert ctx)) =
      some (cfg (some (phaseLabel .scanPrefix)) (if accepted = [] then regs else reset regs)
        raw (accepted.reverse ++ firstRev) certRev input cert ctx) := by
  induction accepted generalizing firstRev regs with
  | nil => rfl
  | cons bit accepted ih =>
      rw [List.length_cons, BitPairFraming.escapeBits_cons, List.cons_append, List.cons_append,
        iterate_step caller _ _ _ (scanPrefix_step_false_cons caller bit
          (BitPairFraming.escapeBits accepted ++ raw) firstRev certRev input cert regs ctx), ih]
      simp [List.reverse_cons, List.append_assoc]

theorem copyCert_prefix (accepted raw firstRev certRev input cert : Bits)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (next caller)^[accepted.length]
        (some (cfg (some (phaseLabel .copyCert)) regs (accepted ++ raw)
          firstRev certRev input cert ctx)) =
      some (cfg (some (phaseLabel .copyCert)) (if accepted = [] then regs else reset regs)
        raw firstRev (accepted.reverse ++ certRev) input cert ctx) := by
  induction accepted generalizing certRev regs with
  | nil => rfl
  | cons bit accepted ih =>
      rw [List.length_cons, List.cons_append, iterate_step caller _ _ _
        (copyCert_step_cons caller bit (accepted ++ raw) firstRev certRev input cert regs ctx), ih]
      simp [List.reverse_cons, List.append_assoc]

theorem emitCert_prefix (raw firstRev accepted certRev input cert : Bits)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (next caller)^[accepted.length]
        (some (cfg (some (phaseLabel .emitCert)) regs raw firstRev
          (accepted ++ certRev) input cert ctx)) =
      some (cfg (some (phaseLabel .emitCert)) (if accepted = [] then regs else reset regs)
        raw firstRev certRev input (accepted.reverse ++ cert) ctx) := by
  induction accepted generalizing cert regs with
  | nil => rfl
  | cons bit accepted ih =>
      rw [List.length_cons, List.cons_append, iterate_step caller _ _ _
        (emitCert_step_cons caller bit raw firstRev (accepted ++ certRev) input cert regs ctx), ih]
      simp [List.reverse_cons, List.append_assoc]

theorem emitFirst_prefix (raw accepted firstRev certRev input cert : Bits)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (next caller)^[accepted.length]
        (some (cfg (some (phaseLabel .emitFirst)) regs raw (accepted ++ firstRev)
          certRev input cert ctx)) =
      some (cfg (some (phaseLabel .emitFirst)) (if accepted = [] then regs else reset regs)
        raw firstRev certRev (accepted.reverse ++ input) cert ctx) := by
  induction accepted generalizing input regs with
  | nil => rfl
  | cons bit accepted ih =>
      rw [List.length_cons, List.cons_append, iterate_step caller _ _ _
        (emitFirst_step_cons caller bit raw (accepted ++ firstRev) certRev input cert regs ctx), ih]
      simp [List.reverse_cons, List.append_assoc]

theorem clearFirst_prefix (raw accepted firstRev certRev input cert : Bits)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (next caller)^[accepted.length]
        (some (cfg (some (phaseLabel .clearFirst)) regs raw (accepted ++ firstRev)
          certRev input cert ctx)) =
      some (cfg (some (phaseLabel .clearFirst)) (if accepted = [] then regs else reset regs)
        raw firstRev certRev input cert ctx) := by
  induction accepted generalizing regs with
  | nil => rfl
  | cons bit accepted ih =>
      rw [List.length_cons, List.cons_append, iterate_step caller _ _ _
        (clearFirst_step_cons caller bit raw (accepted ++ firstRev) certRev input cert regs ctx), ih]
      simp

/-- The exact first return is used; an arbitrary later caller can change outputs. -/
def FirstSuccess (raw first second : Bits) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) : Prop :=
  (next caller)^[BitPairFraming.runSteps raw]
      (some (cfg (some (phaseLabel .scanPrefix)) regs raw [] [] [] [] ctx)) =
    some (cfg (some (resultLabel .success)) (reset regs) [] [] [] first second ctx)

theorem firstSuccess_iff (raw first second : Bits) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    FirstSuccess caller raw first second regs ctx ↔
      BitPairFraming.unframe raw = some (first, second) := by
  constructor
  · intro observed
    unfold FirstSuccess at observed
    rw [run_source] at observed
    generalize parsed : BitPairFraming.unframe raw = source at observed
    cases source with
    | none =>
        have labelEq := congrArg (fun c : Cfg Γ Λ R => c.l) (Option.some.inj observed)
        cases labelEq
    | some pair =>
        rcases pair with ⟨actualFirst, actualSecond⟩
        have equal := Option.some.inj observed
        have firstEq := congrArg (fun c : Cfg Γ Λ R => c.stk (.inl .inputBits)) equal
        have secondEq := congrArg (fun c : Cfg Γ Λ R => c.stk (.inl .certificateBits)) equal
        simp only [scanResult, cfg, List.reverse_nil, List.nil_append, List.append_nil] at firstEq secondEq
        simp only [firstEq, secondEq]
  · exact run_of_some caller raw first second regs ctx

theorem firstSuccess_frame_iff (raw first second : Bits) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    FirstSuccess caller raw first second regs ctx ↔ raw = BitPairFraming.frame first second := by
  rw [firstSuccess_iff, BitPairFraming.unframe_iff]

def FirstFailure (raw : Bits) (regs : Registers R) (ctx : ∀ k, List (Γ k)) : Prop :=
  (next caller)^[BitPairFraming.runSteps raw]
      (some (cfg (some (phaseLabel .scanPrefix)) regs raw [] [] [] [] ctx)) =
    some (cfg (some (resultLabel .failure)) (reset regs) [] [] [] [] [] ctx)

theorem firstFailure_iff (raw : Bits) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    FirstFailure caller raw regs ctx ↔ BitPairFraming.unframe raw = none := by
  constructor
  · intro observed
    unfold FirstFailure at observed
    rw [run_source] at observed
    generalize parsed : BitPairFraming.unframe raw = source at observed
    cases source with
    | none => rfl
    | some pair =>
        have labelEq := congrArg (fun c : Cfg Γ Λ R => c.l) (Option.some.inj observed)
        cases labelEq
  · exact run_of_none caller raw regs ctx

theorem run_first_return (raw : Bits) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ¬ Owned (scanResult (Λ := Λ) regs [] [] [] [] ctx (BitPairFraming.unframe raw)).l ∧
      ∀ n, n < BitPairFraming.runSteps raw → ∃ reached,
        (next caller)^[n]
          (some (cfg (some (phaseLabel .scanPrefix)) regs raw [] [] [] [] ctx)) = some reached ∧
        Owned reached.l := by
  constructor
  · cases BitPairFraming.unframe raw <;> simp [scanResult, cfg, resultLabel, Owned]
  · intro n bound
    obtain ⟨reached, executed, _, _, owned, _⟩ := run_prefix caller raw regs ctx n (Nat.le_of_lt bound)
    exact ⟨reached, executed, owned.mp bound⟩

theorem ambient_run_source (ambient : Label Λ → Statement Γ Λ R)
    (installed : ∀ phase, ambient (phaseLabel phase) = block phase)
    (raw : Bits) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (fun c : Option (Cfg Γ Λ R) => c.bind (Turing.TM2.step ambient))^[BitPairFraming.runSteps raw]
        (some (cfg (some (phaseLabel .scanPrefix)) regs raw [] [] [] [] ctx)) =
      some (scanResult regs [] [] [] [] ctx (BitPairFraming.unframe raw)) := by
  rw [program_eq_of_agrees ambient installed]
  exact run_source _ raw regs ctx

def scanInTime (raw firstRev certRev input cert : Bits) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller)
      (cfg (some (phaseLabel .scanPrefix)) regs raw firstRev certRev input cert ctx)
      (some (scanResult regs firstRev certRev input cert ctx (BitPairFraming.unframe raw)))
      (scanSteps raw firstRev certRev) where
  steps := scanSteps raw firstRev certRev
  evals_in_steps := scanPrefix_iterate caller raw firstRev certRev input cert regs ctx
  steps_le_m := Nat.le_refl _

variable [Fintype K]

def contextCells (ctx : ∀ k, List (Γ k)) : Nat := ∑ k, (ctx k).length

/-- The unweighted physical sum over all five owned and all protected stacks. -/
def stackCells (c : Cfg Γ Λ R) : Nat :=
  ownedCells c + contextCells (fun k => c.stk (.inr k))

theorem localStack_sum (f : LocalStack → Nat) :
    ∑ k, f k = f .raw + f .firstReverse + f .certificateReverse + f .inputBits + f .certificateBits := by
  change (∑ k ∈ ({.raw, .firstReverse, .certificateReverse, .inputBits, .certificateBits} : Finset LocalStack),
    f k) = _
  simp; omega

omit [DecidableEq K] in
theorem stackCells_eq_sum (c : Cfg Γ Λ R) :
    stackCells c = ∑ k : StackId K, (c.stk k).length := by
  rw [Fintype.sum_sum_type, localStack_sum]
  rfl

theorem phase_prefix_stackCells_le (phase : Phase) (raw firstRev certRev input cert : Bits)
    (regs : Registers R) (ctx : ∀ k, List (Γ k)) (n : Nat) (reached : Cfg Γ Λ R)
    (bound : n ≤ phaseSteps phase raw firstRev certRev)
    (executed : (next caller)^[n]
      (some (cfg (some (phaseLabel phase)) regs raw firstRev certRev input cert ctx)) = some reached) :
    stackCells reached ≤ raw.length + firstRev.length + certRev.length + input.length + cert.length +
      contextCells ctx := by
  obtain ⟨_, frame, cells⟩ :=
    prefix_preserves caller phase raw firstRev certRev input cert regs ctx n reached bound executed
  have contextEq : (fun k => reached.stk (.inr k)) = ctx := funext frame
  simpa only [stackCells, contextEq] using Nat.add_le_add_right cells (contextCells ctx)

theorem prefix_stackCells_le (raw : Bits) (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (n : Nat) (reached : Cfg Γ Λ R) (bound : n ≤ BitPairFraming.runSteps raw)
    (executed : (next caller)^[n]
      (some (cfg (some (phaseLabel .scanPrefix)) regs raw [] [] [] [] ctx)) = some reached) :
    stackCells reached ≤ raw.length + contextCells ctx := by
  obtain ⟨actual, run, _, path, _, _⟩ := run_prefix caller raw regs ctx n bound
  have equal : actual = reached := Option.some.inj (run.symm.trans executed)
  subst reached
  obtain ⟨_, frame, cells⟩ := local_reaches_preserves caller path
  have contextEq : (fun k => actual.stk (.inr k)) = ctx := funext frame
  simpa [stackCells, contextEq, ownedCells, cfg] using
    Nat.add_le_add_right cells (contextCells ctx)

omit [DecidableEq K] in
theorem initial_stackCells (raw : Bits) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    stackCells (cfg (Λ := Λ) (some (phaseLabel .scanPrefix)) regs raw [] [] [] [] ctx) =
      raw.length + contextCells ctx := by
  simp [stackCells, ownedCells, cfg]

omit [DecidableEq K] in
theorem stackId_card : Fintype.card (StackId K) = 5 + Fintype.card K := by
  rw [Fintype.card_sum]
  rfl

variable [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]

theorem label_card : Fintype.card (Label Λ) = 7 + Fintype.card Λ := by
  rw [Fintype.card_sum, Fintype.card_sum]
  have phases : Fintype.card Phase = 5 := by decide
  have results : Fintype.card Result = 2 := by decide
  rw [phases, results]
  omega

theorem registers_card : Fintype.card (Registers R) = 3 * Fintype.card R := by
  simp [Registers]

/-- A fixed finite physical program, chosen before any input; its exits remain live. -/
def machine (initial : R) : Turing.FinTM2 where
  K := StackId K
  k₀ := .inl .raw
  k₁ := .inl .inputBits
  Γ := alphabet Γ
  Λ := Label Λ
  main := phaseLabel .scanPrefix
  σ := Registers R
  initialState := (none, initial)
  Γk₀Fin := alphabetFintype (.inl .raw)
  m := program caller

theorem machine_step_eq (initial : R) (c : Cfg Γ Λ R) :
    (machine caller initial).step c = step caller c := rfl

theorem initList_eq (initial : R) (raw : Bits) :
    Turing.initList (machine caller initial) raw =
      cfg (some (phaseLabel .scanPrefix)) (none, initial) raw [] [] [] [] (fun _ => []) := by
  apply cfg_ext <;> first | rfl | exact fun _ => rfl

end Resources.RotationCertificate.OpenFramingMachine
