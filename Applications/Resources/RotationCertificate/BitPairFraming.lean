import Applications.Resources.RotationCertificate.BinaryVerifier
import Mathlib.Computability.TuringMachine.Computable

/-!
# Strict binary pair framing and its finite machine

Each first-list bit is guarded by false; the first true flag separates it from
the entire unchanged certificate suffix. The source parser recognizes exactly
these frames. A fixed four-stack, five-label TM2 machine implements that parser
on every raw list, including actual reversal, markers, reset, and failure cleanup.
Its exact transitions and reachable stack cells have separate numerical proofs.

The Boolean client passes the pair actually returned by the source parser to
the existing binary verifier. The framing machine does not execute that verifier;
quantitative machine composition and the formal NP correspondence remain open.
Correspondence: `docs/research/fdsa-rotation-certificate-preparation.md`.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.RotationCertificate.BitPairFraming
open Resources.BinaryCounter (Bits value)
open Trees Trees.Rotations

def escapeBits (input : Bits) : Bits := input.flatMap (fun bit => [false, bit])

def frame (input cert : Bits) : Bits := escapeBits input ++ true :: cert

@[simp] theorem escapeBits_nil : escapeBits [] = [] := rfl

@[simp] theorem escapeBits_cons (bit : Bool) (input : Bits) :
    escapeBits (bit :: input) = false :: bit :: escapeBits input := rfl

@[simp] theorem frame_nil (cert : Bits) : frame [] cert = true :: cert := rfl

@[simp] theorem frame_cons (bit : Bool) (input cert : Bits) :
    frame (bit :: input) cert = false :: bit :: frame input cert := rfl

theorem escapeBits_length (input : Bits) :
    (escapeBits input).length = 2 * input.length := by
  induction input with
  | nil => rfl
  | cons bit input ih =>
      simp only [escapeBits_cons, List.length_cons, ih]
      omega

theorem escapeBits_append (left right : Bits) :
    escapeBits (left ++ right) = escapeBits left ++ escapeBits right := by
  induction left with
  | nil => rfl
  | cons bit left ih => simp only [List.cons_append, escapeBits_cons, ih]

theorem frame_length (input cert : Bits) :
    (frame input cert).length = 2 * input.length + cert.length + 1 := by
  simp only [frame, List.length_append, escapeBits_length, List.length_cons]
  omega

theorem frame_append (input cert tail : Bits) :
    frame input cert ++ tail = frame input (cert ++ tail) := by
  simp only [frame, List.append_assoc, List.cons_append]

def unframe : Bits → Option (Bits × Bits)
  | [] => none
  | true :: cert => some ([], cert)
  | [false] => none
  | false :: bit :: raw =>
      (unframe raw).map (fun pair => (bit :: pair.1, pair.2))

@[simp] theorem unframe_nil : unframe [] = none := rfl

@[simp] theorem unframe_true (cert : Bits) :
    unframe (true :: cert) = some ([], cert) := rfl

@[simp] theorem unframe_false_nil : unframe [false] = none := rfl

theorem unframe_false_cons (bit : Bool) (raw : Bits) :
    unframe (false :: bit :: raw) =
      (unframe raw).map (fun pair => (bit :: pair.1, pair.2)) := rfl

theorem unframe_escape_append (pref raw : Bits) :
    unframe (escapeBits pref ++ raw) =
      (unframe raw).map (fun pair => (pref ++ pair.1, pair.2)) := by
  induction pref with
  | nil =>
      cases parsed : unframe raw <;> simp [parsed]
  | cons bit pref ih =>
      rw [escapeBits_cons, List.cons_append, List.cons_append, unframe_false_cons, ih]
      cases unframe raw <;> simp

theorem unframe_frame (input cert : Bits) :
    unframe (frame input cert) = some (input, cert) := by
  rw [frame, unframe_escape_append, unframe_true]
  simp

private theorem frame_of_unframe (raw input cert : Bits)
    (parsed : unframe raw = some (input, cert)) : raw = frame input cert := by
  induction raw using unframe.induct generalizing input cert with
  | case1 => cases parsed
  | case2 raw =>
      have pairEq : ([], raw) = (input, cert) := Option.some.inj parsed
      rcases Prod.mk.inj pairEq with ⟨rfl, rfl⟩
      rfl
  | case3 => cases parsed
  | case4 bit raw ih =>
      cases tailResult : unframe raw with
      | none => simp [unframe_false_cons, tailResult] at parsed
      | some pair =>
          rcases pair with ⟨pref, suffix⟩
          have pairEq : (bit :: pref, suffix) = (input, cert) := by
            simpa only [unframe_false_cons, tailResult, Option.map_some,
              Option.some.injEq] using parsed
          rcases Prod.mk.inj pairEq with ⟨rfl, rfl⟩
          simpa only [frame_cons] using
            congrArg (fun bits => false :: bit :: bits) (ih pref suffix tailResult)

theorem unframe_iff (raw input cert : Bits) :
    unframe raw = some (input, cert) ↔ raw = frame input cert := by
  constructor
  · exact frame_of_unframe raw input cert
  · rintro rfl
    exact unframe_frame input cert

theorem unframe_missing_delimiter (input : Bits) : unframe (escapeBits input) = none := by
  simpa using unframe_escape_append input []

theorem unframe_incomplete_guard (input : Bits) :
    unframe (escapeBits input ++ [false]) = none := by
  simpa using unframe_escape_append input [false]

theorem unframe_none_iff (raw : Bits) :
    unframe raw = none ↔
      ∃ input : Bits, raw = escapeBits input ∨ raw = escapeBits input ++ [false] := by
  constructor
  · intro failed
    induction raw using unframe.induct with
    | case1 => exact ⟨[], Or.inl rfl⟩
    | case2 cert => cases failed
    | case3 => exact ⟨[], Or.inr rfl⟩
    | case4 bit raw ih =>
        have tailFailed : unframe raw = none := by
          cases parsed : unframe raw with
          | none => rfl
          | some pair => simp [unframe_false_cons, parsed] at failed
        obtain ⟨pref, encoded | encoded⟩ := ih tailFailed
        · exact ⟨bit :: pref, Or.inl (by rw [escapeBits_cons, encoded])⟩
        · exact ⟨bit :: pref, Or.inr (by
            rw [escapeBits_cons, List.cons_append, List.cons_append, encoded])⟩
  · rintro ⟨input, rfl | rfl⟩
    · exact unframe_missing_delimiter input
    · exact unframe_incomplete_guard input

theorem frame_injective :
    Function.Injective (fun pair : Bits × Bits => frame pair.1 pair.2) := by
  intro left right equal
  have decoded := congrArg unframe equal
  rw [unframe_frame, unframe_frame] at decoded
  exact Option.some.inj decoded

/-- Two markers distinguish ordinary failure, successful emptiness, and both coordinates. -/
def resultCode : Option (Bits × Bits) → List (Option Bool)
  | none => []
  | some (input, cert) => none :: (input.map some ++ none :: cert.map some)

theorem resultCode_injective : Function.Injective resultCode := by
  intro left right equal
  cases left with
  | none => cases right with
    | none => rfl
    | some pair => cases equal
  | some left => cases right with
    | none => cases equal
    | some right =>
        rcases left with ⟨leftInput, leftCert⟩
        rcases right with ⟨rightInput, rightCert⟩
        have tailEq := (List.cons.inj equal).2
        have parts : leftInput.map some = rightInput.map some ∧
            (none : Option Bool) = none ∧ leftCert.map some = rightCert.map some :=
          (List.append_cons_inj_of_notMem (by simp) (by simp)).1 tailEq
        have injective : Function.Injective (List.map (some : Bool → Option Bool)) :=
          List.map_injective_iff.mpr (Option.some_injective Bool)
        cases injective parts.1
        cases injective parts.2.2
        rfl

theorem resultCode_length (input cert : Bits) :
    (resultCode (some (input, cert))).length = input.length + cert.length + 2 := by
  simp only [resultCode, List.length_cons, List.length_append, List.length_map]
  omega

inductive StackId
  | input | firstReverse | certReverse | output
  deriving DecidableEq

instance : Fintype StackId where
  elems := {.input, .firstReverse, .certReverse, .output}
  complete stack := by cases stack <;> decide

inductive Label
  | scanPrefix | copyCert | emitCert | emitFirst | clearFirst
  deriving DecidableEq

instance : Fintype Label where
  elems := {.scanPrefix, .copyCert, .emitCert, .emitFirst, .clearFirst}
  complete label := by cases label <;> decide

abbrev Registers := Option Bool
def zeroRegisters : Registers := none

abbrev alphabet : StackId → Type
  | .input | .firstReverse | .certReverse => Bool
  | .output => Option Bool

instance alphabetFintype (stack : StackId) : Fintype (alphabet stack) := by
  cases stack with
  | input => exact inferInstanceAs (Fintype Bool)
  | firstReverse => exact inferInstanceAs (Fintype Bool)
  | certReverse => exact inferInstanceAs (Fintype Bool)
  | output => exact inferInstanceAs (Fintype (Option Bool))

abbrev Statement := Turing.TM2.Stmt alphabet Label Registers

def store (_ : Registers) (bit : Option Bool) : Registers := bit

def jump (label : Label) : Statement :=
  .load (fun _ => zeroRegisters) (.goto (fun _ => label))

def finish : Statement := .load (fun _ => zeroRegisters) .halt

/-- Every callback reads only one finite register; unbounded traversals use actual gotos. -/
def program : Label → Statement
  | .scanPrefix =>
      .pop .input store (.branch Option.isSome
        (.branch (fun bit => bit.getD false)
          (jump .copyCert)
          (.pop .input store (.branch Option.isSome
            (.push .firstReverse (fun bit => bit.getD false) (jump .scanPrefix))
            (jump .clearFirst))))
        (jump .clearFirst))
  | .copyCert =>
      .pop .input store (.branch Option.isSome
        (.push .certReverse (fun bit => bit.getD false) (jump .copyCert))
        (jump .emitCert))
  | .emitCert =>
      .pop .certReverse store (.branch Option.isSome
        (.push .output (fun bit => some (bit.getD false)) (jump .emitCert))
        (.push .output (fun _ => none) (jump .emitFirst)))
  | .emitFirst =>
      .pop .firstReverse store (.branch Option.isSome
        (.push .output (fun bit => some (bit.getD false)) (jump .emitFirst))
        (.push .output (fun _ => none) finish))
  | .clearFirst =>
      .pop .firstReverse store (.branch Option.isSome (jump .clearFirst) finish)

abbrev machine : Turing.FinTM2 where
  K := StackId
  k₀ := .input
  k₁ := .output
  Γ := alphabet
  Λ := Label
  main := .scanPrefix
  σ := Registers
  initialState := zeroRegisters
  m := program

def cfg (label : Option Label) (regs : Registers) (raw firstRev certRev : Bits)
    (out : List (Option Bool)) : machine.Cfg where
  l := label
  var := regs
  stk
    | .input => raw
    | .firstReverse => firstRev
    | .certReverse => certRev
    | .output => out

private theorem cfg_ext {left right : machine.Cfg}
    (label : left.l = right.l) (regs : left.var = right.var)
    (raw : left.stk .input = right.stk .input)
    (firstRev : left.stk .firstReverse = right.stk .firstReverse)
    (certRev : left.stk .certReverse = right.stk .certReverse)
    (out : left.stk .output = right.stk .output) : left = right := by
  have stackEq : left.stk = right.stk := by
    funext stack
    cases stack with
    | input => exact raw
    | firstReverse => exact firstRev
    | certReverse => exact certRev
    | output => exact out
  cases left
  cases right
  cases label
  cases regs
  cases stackEq
  rfl

theorem cfg_eta (c : machine.Cfg) :
    cfg c.l c.var (c.stk .input) (c.stk .firstReverse) (c.stk .certReverse)
      (c.stk .output) = c := by
  apply cfg_ext <;> rfl

theorem initList_eq (raw : Bits) :
    Turing.initList machine raw = cfg (some .scanPrefix) zeroRegisters raw [] [] [] := by
  apply cfg_ext <;> rfl

theorem haltList_eq (out : List (Option Bool)) :
    Turing.haltList machine out = cfg none zeroRegisters [] [] [] out := by
  apply cfg_ext <;> rfl

theorem scanPrefix_step_nil (firstRev certRev : Bits) (out : List (Option Bool))
    (regs : Registers) :
    machine.step (cfg (some .scanPrefix) regs [] firstRev certRev out) =
      some (cfg (some .clearFirst) zeroRegisters [] firstRev certRev out) := by
  apply congrArg some
  apply cfg_ext <;> rfl

theorem scanPrefix_step_false_nil (firstRev certRev : Bits) (out : List (Option Bool))
    (regs : Registers) :
    machine.step (cfg (some .scanPrefix) regs [false] firstRev certRev out) =
      some (cfg (some .clearFirst) zeroRegisters [] firstRev certRev out) := by
  apply congrArg some
  apply cfg_ext <;> rfl

theorem scanPrefix_step_false_cons (bit : Bool) (raw firstRev certRev : Bits)
    (out : List (Option Bool)) (regs : Registers) :
    machine.step (cfg (some .scanPrefix) regs (false :: bit :: raw) firstRev certRev out) =
      some (cfg (some .scanPrefix) zeroRegisters raw (bit :: firstRev) certRev out) := by
  apply congrArg some
  apply cfg_ext <;> rfl

theorem scanPrefix_step_true (cert firstRev certRev : Bits) (out : List (Option Bool))
    (regs : Registers) :
    machine.step (cfg (some .scanPrefix) regs (true :: cert) firstRev certRev out) =
      some (cfg (some .copyCert) zeroRegisters cert firstRev certRev out) := by
  apply congrArg some
  apply cfg_ext <;> rfl

theorem copyCert_step_cons (bit : Bool) (raw firstRev certRev : Bits)
    (out : List (Option Bool)) (regs : Registers) :
    machine.step (cfg (some .copyCert) regs (bit :: raw) firstRev certRev out) =
      some (cfg (some .copyCert) zeroRegisters raw firstRev (bit :: certRev) out) := by
  apply congrArg some
  apply cfg_ext <;> rfl

theorem copyCert_step_nil (firstRev certRev : Bits) (out : List (Option Bool))
    (regs : Registers) :
    machine.step (cfg (some .copyCert) regs [] firstRev certRev out) =
      some (cfg (some .emitCert) zeroRegisters [] firstRev certRev out) := by
  apply congrArg some
  apply cfg_ext <;> rfl

theorem emitCert_step_cons (bit : Bool) (raw firstRev certRev : Bits)
    (out : List (Option Bool)) (regs : Registers) :
    machine.step (cfg (some .emitCert) regs raw firstRev (bit :: certRev) out) =
      some (cfg (some .emitCert) zeroRegisters raw firstRev certRev (some bit :: out)) := by
  apply congrArg some
  apply cfg_ext <;> rfl

theorem emitCert_step_nil (raw firstRev : Bits) (out : List (Option Bool))
    (regs : Registers) :
    machine.step (cfg (some .emitCert) regs raw firstRev [] out) =
      some (cfg (some .emitFirst) zeroRegisters raw firstRev [] (none :: out)) := by
  apply congrArg some
  apply cfg_ext <;> rfl

theorem emitFirst_step_cons (bit : Bool) (raw firstRev certRev : Bits)
    (out : List (Option Bool)) (regs : Registers) :
    machine.step (cfg (some .emitFirst) regs raw (bit :: firstRev) certRev out) =
      some (cfg (some .emitFirst) zeroRegisters raw firstRev certRev (some bit :: out)) := by
  apply congrArg some
  apply cfg_ext <;> rfl

theorem emitFirst_step_nil (raw certRev : Bits) (out : List (Option Bool))
    (regs : Registers) :
    machine.step (cfg (some .emitFirst) regs raw [] certRev out) =
      some (cfg none zeroRegisters raw [] certRev (none :: out)) := by
  apply congrArg some
  apply cfg_ext <;> rfl

theorem clearFirst_step_cons (bit : Bool) (raw firstRev certRev : Bits)
    (out : List (Option Bool)) (regs : Registers) :
    machine.step (cfg (some .clearFirst) regs raw (bit :: firstRev) certRev out) =
      some (cfg (some .clearFirst) zeroRegisters raw firstRev certRev out) := by
  apply congrArg some
  apply cfg_ext <;> rfl

theorem clearFirst_step_nil (raw certRev : Bits) (out : List (Option Bool))
    (regs : Registers) :
    machine.step (cfg (some .clearFirst) regs raw [] certRev out) =
      some (cfg none zeroRegisters raw [] certRev out) := by
  apply congrArg some
  apply cfg_ext <;> rfl

theorem halt_step (regs : Registers) (raw firstRev certRev : Bits)
    (out : List (Option Bool)) : machine.step (cfg none regs raw firstRev certRev out) = none := rfl

def next (c : Option machine.Cfg) : Option machine.Cfg := c.bind machine.step

@[simp] theorem next_none : next none = none := rfl
@[simp] theorem next_some (c : machine.Cfg) : next (some c) = machine.step c := rfl

private theorem iterate_step (n : Nat) (c d : machine.Cfg)
    (step : machine.step c = some d) :
    next^[n + 1] (some c) = next^[n] (some d) := by
  rw [Function.iterate_succ_apply, next_some, step]

theorem emitFirst_iterate (firstRev : Bits) (out : List (Option Bool))
    (regs : Registers) :
    next^[firstRev.length + 1]
        (some (cfg (some .emitFirst) regs [] firstRev [] out)) =
      some (Turing.haltList machine (none :: (firstRev.reverse.map some ++ out))) := by
  induction firstRev generalizing out regs with
  | nil =>
      simp only [List.length_nil, Nat.zero_add, Function.iterate_one, next_some,
        emitFirst_step_nil, List.reverse_nil, List.map_nil, List.nil_append, haltList_eq]
  | cons bit firstRev ih =>
      rw [show (bit :: firstRev).length + 1 = (firstRev.length + 1) + 1 by rfl,
        iterate_step _ _ _ (emitFirst_step_cons bit [] firstRev [] out regs), ih]
      simp [List.reverse_cons, List.map_append, List.append_assoc]

theorem clearFirst_iterate (firstRev : Bits) (out : List (Option Bool))
    (regs : Registers) :
    next^[firstRev.length + 1]
        (some (cfg (some .clearFirst) regs [] firstRev [] out)) =
      some (Turing.haltList machine out) := by
  induction firstRev generalizing regs with
  | nil =>
      simp only [List.length_nil, Nat.zero_add, Function.iterate_one, next_some,
        clearFirst_step_nil, haltList_eq]
  | cons bit firstRev ih =>
      rw [show (bit :: firstRev).length + 1 = (firstRev.length + 1) + 1 by rfl,
        iterate_step _ _ _ (clearFirst_step_cons bit [] firstRev [] out regs), ih]

theorem emitCert_iterate (firstRev certRev : Bits) (out : List (Option Bool))
    (regs : Registers) :
    next^[certRev.length + firstRev.length + 2]
        (some (cfg (some .emitCert) regs [] firstRev certRev out)) =
      some (Turing.haltList machine
        (none :: (firstRev.reverse.map some ++ none :: (certRev.reverse.map some ++ out)))) := by
  induction certRev generalizing out regs with
  | nil =>
      rw [show ([] : Bits).length + firstRev.length + 2 = (firstRev.length + 1) + 1 by simp,
        iterate_step _ _ _ (emitCert_step_nil [] firstRev out regs), emitFirst_iterate]
      simp
  | cons bit certRev ih =>
      rw [show (bit :: certRev).length + firstRev.length + 2 =
          (certRev.length + firstRev.length + 2) + 1 by simp only [List.length_cons]; omega,
        iterate_step _ _ _ (emitCert_step_cons bit [] firstRev certRev out regs), ih]
      simp [List.reverse_cons, List.map_append, List.append_assoc]

theorem copyCert_iterate (raw firstRev certRev : Bits) (out : List (Option Bool))
    (regs : Registers) :
    next^[2 * raw.length + certRev.length + firstRev.length + 3]
        (some (cfg (some .copyCert) regs raw firstRev certRev out)) =
      some (Turing.haltList machine
        (none :: (firstRev.reverse.map some ++
          none :: ((certRev.reverse ++ raw).map some ++ out)))) := by
  induction raw generalizing certRev regs with
  | nil =>
      rw [show 2 * ([] : Bits).length + certRev.length + firstRev.length + 3 =
          (certRev.length + firstRev.length + 2) + 1 by simp,
        iterate_step _ _ _ (copyCert_step_nil firstRev certRev out regs), emitCert_iterate]
      simp
  | cons bit raw ih =>
      rw [show 2 * (bit :: raw).length + certRev.length + firstRev.length + 3 =
          (2 * raw.length + (bit :: certRev).length + firstRev.length + 3) + 1 by
            simp only [List.length_cons]; omega,
        iterate_step _ _ _ (copyCert_step_cons bit raw firstRev certRev out regs), ih]
      simp [List.reverse_cons, List.append_assoc]

/-- A proof-side count; no program callback computes it. -/
def runSteps : Bits → Nat
  | [] => 2
  | true :: cert => 2 * cert.length + 4
  | [false] => 2
  | false :: _ :: raw => runSteps raw + 2

/-- Failure clears the entire first accumulator and preserves the actual old output suffix. -/
theorem scanPrefix_iterate (raw firstRev : Bits) (out : List (Option Bool))
    (regs : Registers) :
    next^[runSteps raw + firstRev.length]
        (some (cfg (some .scanPrefix) regs raw firstRev [] out)) =
      some (Turing.haltList machine
        (resultCode ((unframe raw).map
          (fun pair => (firstRev.reverse ++ pair.1, pair.2))) ++ out)) := by
  induction raw using unframe.induct generalizing firstRev regs with
  | case1 =>
      rw [show runSteps [] + firstRev.length = (firstRev.length + 1) + 1 by
          simp only [runSteps]; omega,
        iterate_step _ _ _ (scanPrefix_step_nil firstRev [] out regs), clearFirst_iterate]
      rfl
  | case2 cert =>
      rw [show runSteps (true :: cert) + firstRev.length =
          (2 * cert.length + ([] : Bits).length + firstRev.length + 3) + 1 by
            simp only [runSteps, List.length_nil]; omega,
        iterate_step _ _ _ (scanPrefix_step_true cert firstRev [] out regs), copyCert_iterate]
      simp [unframe, resultCode, List.append_assoc]
  | case3 =>
      rw [show runSteps [false] + firstRev.length = (firstRev.length + 1) + 1 by
          simp only [runSteps]; omega,
        iterate_step _ _ _ (scanPrefix_step_false_nil firstRev [] out regs), clearFirst_iterate]
      rfl
  | case4 bit raw ih =>
      rw [show runSteps (false :: bit :: raw) + firstRev.length =
          (runSteps raw + (bit :: firstRev).length) + 1 by
            simp only [runSteps, List.length_cons]; omega,
        iterate_step _ _ _ (scanPrefix_step_false_cons bit raw firstRev [] out regs), ih,
        unframe_false_cons]
      cases unframe raw <;>
        simp [List.reverse_cons, List.append_assoc, resultCode]

theorem runSteps_escape_append (pref raw : Bits) :
    runSteps (escapeBits pref ++ raw) = 2 * pref.length + runSteps raw := by
  induction pref with
  | nil => simp
  | cons bit pref ih =>
      simp only [escapeBits_cons, List.cons_append, runSteps, ih, List.length_cons]
      omega

theorem runSteps_frame (input cert : Bits) :
    runSteps (frame input cert) = 2 * input.length + 2 * cert.length + 4 := by
  rw [frame, runSteps_escape_append, runSteps]
  omega

theorem runSteps_missing_delimiter (input : Bits) :
    runSteps (escapeBits input) = 2 * input.length + 2 := by
  simpa only [List.append_nil, runSteps] using runSteps_escape_append input []

theorem runSteps_incomplete_guard (input : Bits) :
    runSteps (escapeBits input ++ [false]) = 2 * input.length + 2 := by
  simpa only [runSteps] using runSteps_escape_append input [false]

theorem runSteps_le (raw : Bits) : runSteps raw ≤ 2 * raw.length + 2 := by
  induction raw using unframe.induct with
  | case1 => simp [runSteps]
  | case2 cert => simp only [runSteps, List.length_cons]; omega
  | case3 => simp [runSteps]
  | case4 bit raw ih => simp only [runSteps, List.length_cons]; omega

/-- Exact terminal configuration for every raw list, including both malformed endings. -/
theorem machine_run (raw : Bits) :
    next^[runSteps raw] (some (Turing.initList machine raw)) =
      some (Turing.haltList machine (resultCode (unframe raw))) := by
  simpa [initList_eq] using scanPrefix_iterate raw [] [] zeroRegisters

def outputsInTimeExact (raw : Bits) :
    Turing.TM2OutputsInTime machine raw
      (some (resultCode (unframe raw))) (runSteps raw) where
  steps := runSteps raw
  evals_in_steps := machine_run raw
  steps_le_m := Nat.le_refl _

def outputsInTime (raw : Bits) :
    Turing.TM2OutputsInTime machine raw
      (some (resultCode (unframe raw))) (2 * raw.length + 2) where
  steps := runSteps raw
  evals_in_steps := machine_run raw
  steps_le_m := runSteps_le raw

noncomputable def computableInPolyTime :
    Turing.TM2ComputableInPolyTime (id : Bits → List Bool) resultCode unframe where
  tm := machine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl (Option Bool)
  time := 2 * Polynomial.X + 2
  outputsFun raw := by simpa [List.map_id] using outputsInTime raw

theorem machine_run_frame (input cert : Bits) :
    next^[2 * input.length + 2 * cert.length + 4]
        (some (Turing.initList machine (frame input cert))) =
      some (Turing.haltList machine (resultCode (some (input, cert)))) := by
  have run := machine_run (frame input cert)
  rw [runSteps_frame, unframe_frame] at run
  exact run

theorem machine_run_missing_delimiter (input : Bits) :
    next^[2 * input.length + 2] (some (Turing.initList machine (escapeBits input))) =
      some (Turing.haltList machine []) := by
  have run := machine_run (escapeBits input)
  rw [runSteps_missing_delimiter, unframe_missing_delimiter] at run
  exact run

theorem machine_run_incomplete_guard (input : Bits) :
    next^[2 * input.length + 2]
        (some (Turing.initList machine (escapeBits input ++ [false]))) =
      some (Turing.haltList machine []) := by
  have run := machine_run (escapeBits input ++ [false])
  rw [runSteps_incomplete_guard, unframe_incomplete_guard] at run
  exact run

/-- Every physical list cell on every actual machine stack is counted. -/
def stackCells (c : machine.Cfg) : Nat :=
  (c.stk .input).length + (c.stk .firstReverse).length +
    (c.stk .certReverse).length + (c.stk .output).length

/-- The consumed delimiter pays for the second future output marker. -/
def credit : Option Label → Nat
  | some .scanPrefix | some .emitFirst => 1
  | some .copyCert | some .emitCert => 2
  | some .clearFirst | none => 0

def potential (c : machine.Cfg) : Nat := stackCells c + credit c.l

theorem step_potential_le (c d : machine.Cfg)
    (stepped : machine.step c = some d) : potential d ≤ potential c := by
  obtain ⟨label, regs, raw, firstRev, certRev, out, rfl⟩ :
      ∃ (label : Option Label) (regs : Registers) (raw firstRev certRev : Bits)
        (out : List (Option Bool)), c = cfg label regs raw firstRev certRev out :=
    ⟨c.l, c.var, c.stk .input, c.stk .firstReverse, c.stk .certReverse,
      c.stk .output, (cfg_eta c).symm⟩
  cases label with
  | none =>
      rw [halt_step] at stepped
      cases stepped
  | some label =>
      cases label with
      | scanPrefix =>
          cases raw with
          | nil =>
              rw [scanPrefix_step_nil] at stepped
              cases Option.some.inj stepped
              simp only [potential, stackCells, credit, cfg, List.length_nil]; omega
          | cons flag raw =>
              cases flag with
              | false =>
                  cases raw with
                  | nil =>
                      rw [scanPrefix_step_false_nil] at stepped
                      cases Option.some.inj stepped
                      simp only [potential, stackCells, credit, cfg,
                        List.length_nil, List.length_cons]; omega
                  | cons bit raw =>
                      rw [scanPrefix_step_false_cons] at stepped
                      cases Option.some.inj stepped
                      simp only [potential, stackCells, credit, cfg, List.length_cons]; omega
              | true =>
                  rw [scanPrefix_step_true] at stepped
                  cases Option.some.inj stepped
                  simp only [potential, stackCells, credit, cfg, List.length_cons]; omega
      | copyCert =>
          cases raw with
          | nil =>
              rw [copyCert_step_nil] at stepped
              cases Option.some.inj stepped
              simp only [potential, stackCells, credit, cfg, List.length_nil]; omega
          | cons bit raw =>
              rw [copyCert_step_cons] at stepped
              cases Option.some.inj stepped
              simp only [potential, stackCells, credit, cfg, List.length_cons]; omega
      | emitCert =>
          cases certRev with
          | nil =>
              rw [emitCert_step_nil] at stepped
              cases Option.some.inj stepped
              simp only [potential, stackCells, credit, cfg,
                List.length_nil, List.length_cons]; omega
          | cons bit certRev =>
              rw [emitCert_step_cons] at stepped
              cases Option.some.inj stepped
              simp only [potential, stackCells, credit, cfg, List.length_cons]; omega
      | emitFirst =>
          cases firstRev with
          | nil =>
              rw [emitFirst_step_nil] at stepped
              cases Option.some.inj stepped
              simp only [potential, stackCells, credit, cfg,
                List.length_nil, List.length_cons]; omega
          | cons bit firstRev =>
              rw [emitFirst_step_cons] at stepped
              cases Option.some.inj stepped
              simp only [potential, stackCells, credit, cfg, List.length_cons]; omega
      | clearFirst =>
          cases firstRev with
          | nil =>
              rw [clearFirst_step_nil] at stepped
              cases Option.some.inj stepped
              simp only [potential, stackCells, credit, cfg, List.length_nil]; omega
          | cons bit firstRev =>
              rw [clearFirst_step_cons] at stepped
              cases Option.some.inj stepped
              simp only [potential, stackCells, credit, cfg, List.length_cons]; omega

theorem reaches_potential_le (start reached : machine.Cfg)
    (run : Turing.TM2.Reaches program start reached) :
    potential reached ≤ potential start := by
  change Relation.ReflTransGen
    (fun before after : machine.Cfg => machine.step before = some after) start reached at run
  induction run with
  | refl => exact Nat.le_refl _
  | @tail before after _ step ih =>
      exact Nat.le_trans (step_potential_le before after step) ih

theorem reachable_stackCells_le (raw : Bits) (reached : machine.Cfg)
    (run : Turing.TM2.Reaches program (Turing.initList machine raw) reached) :
    stackCells reached ≤ raw.length + 1 := by
  have initial : potential (Turing.initList machine raw) = raw.length + 1 := by
    simp [initList_eq, potential, stackCells, credit, cfg]
  have bounded := reaches_potential_le (Turing.initList machine raw) reached run
  rw [initial] at bounded
  unfold potential at bounded
  omega

/-- A source composition on the actual parsed pair, without introducing a new work tariff. -/
def verifyFramed (raw : Bits) : Bool :=
  match unframe raw with
  | none => false
  | some (input, cert) => (verifyBitsRun input cert).1

theorem verifyFramed_frame (input cert : Bits) :
    verifyFramed (frame input cert) = (verifyBitsRun input cert).1 := by
  rw [verifyFramed, unframe_frame]

theorem verifyFramed_accept_iff (raw : Bits) :
    verifyFramed raw = true ↔
      ∃ input cert : Bits, raw = frame input cert ∧ (verifyBitsRun input cert).1 = true := by
  constructor
  · intro accepted
    cases parsed : unframe raw with
    | none => simp [verifyFramed, parsed] at accepted
    | some pair =>
        rcases pair with ⟨input, cert⟩
        refine ⟨input, cert, (unframe_iff raw input cert).1 parsed, ?_⟩
        simpa only [verifyFramed, parsed] using accepted
  · rintro ⟨input, cert, rfl, accepted⟩
    rw [verifyFramed_frame]
    exact accepted

theorem verifyFramed_accept_iff_trace (raw : Bits) :
    verifyFramed raw = true ↔
      ∃ (source target : BinaryTree Unit) (bs : Bits) (moves : List RotationMove),
        raw = frame (wordBits (inputCode source target bs)) (wordBits (certCode moves)) ∧
        applyMoves? moves source = some target ∧ moves.length ≤ value bs := by
  constructor
  · intro accepted
    obtain ⟨input, cert, encoded, checked⟩ := (verifyFramed_accept_iff raw).1 accepted
    obtain ⟨source, target, bs, moves, inputEq, certEq, run, bound⟩ :=
      (verifyBitsRun_accept_iff_trace input cert).1 checked
    refine ⟨source, target, bs, moves, ?_, run, bound⟩
    simpa only [inputEq, certEq] using encoded
  · rintro ⟨source, target, bs, moves, encoded, run, bound⟩
    apply (verifyFramed_accept_iff raw).2
    refine ⟨wordBits (inputCode source target bs), wordBits (certCode moves), encoded, ?_⟩
    exact (verifyBitsRun_accept_iff_trace _ _).2
      ⟨source, target, bs, moves, rfl, rfl, run, bound⟩

theorem verifyFramed_sound (raw : Bits) (accepted : verifyFramed raw = true) :
    ∃ input cert : Bits, raw = frame input cert ∧ BinaryYes input := by
  obtain ⟨input, cert, encoded, checked⟩ := (verifyFramed_accept_iff raw).1 accepted
  exact ⟨input, cert, encoded, verifyBitsRun_sound input cert checked⟩

theorem binaryYes_iff_exists_framed_certificate (input : Bits) :
    BinaryYes input ↔ ∃ cert : Bits, verifyFramed (frame input cert) = true := by
  simpa only [verifyFramed_frame] using binaryYes_iff_exists_certificate input

theorem frame_length_le_square (input cert : Bits) (small : cert.length ≤ input.length ^ 2) :
    (frame input cert).length ≤ (input.length + 1) ^ 2 := by
  rw [frame_length]
  nlinarith

theorem verifyFramed_complete_small (input : Bits) (yes : BinaryYes input) :
    ∃ cert : Bits, cert.length ≤ input.length ^ 2 ∧
      (frame input cert).length ≤ (input.length + 1) ^ 2 ∧
      verifyFramed (frame input cert) = true := by
  obtain ⟨cert, small, accepted⟩ := verifyBitsRun_complete_small input yes
  refine ⟨cert, small, frame_length_le_square input cert small, ?_⟩
  rw [verifyFramed_frame]
  exact accepted

theorem runSteps_frame_le_square (input cert : Bits) (small : cert.length ≤ input.length ^ 2) :
    runSteps (frame input cert) ≤ 2 * (input.length + 1) ^ 2 + 2 :=
  Nat.le_trans (runSteps_le (frame input cert))
    (Nat.add_le_add_right (Nat.mul_le_mul_left 2 (frame_length_le_square input cert small)) 2)

/-- This timed record executes the framing machine, not the downstream verifier. -/
def outputsInTimeOfSmallCertificate (input cert : Bits) (small : cert.length ≤ input.length ^ 2) :
    Turing.TM2OutputsInTime machine (frame input cert)
      (some (resultCode (some (input, cert)))) (2 * (input.length + 1) ^ 2 + 2) where
  steps := runSteps (frame input cert)
  evals_in_steps := by
    change next^[runSteps (frame input cert)]
        (some (Turing.initList machine (frame input cert))) =
      some (Turing.haltList machine (resultCode (some (input, cert))))
    rw [machine_run, unframe_frame]
  steps_le_m := runSteps_frame_le_square input cert small

theorem reachable_framed_stackCells_le (input cert : Bits)
    (small : cert.length ≤ input.length ^ 2) (reached : machine.Cfg)
    (run : Turing.TM2.Reaches program (Turing.initList machine (frame input cert)) reached) :
    stackCells reached ≤ (input.length + 1) ^ 2 + 1 :=
  Nat.le_trans (reachable_stackCells_le (frame input cert) reached run)
    (Nat.add_le_add_right (frame_length_le_square input cert small) 1)

/-- Actual packed emitters feed the actual source parser and binary verifier. -/
theorem verifyFramed_emit_trace (source target : BinaryTree Unit) (bs : Bits)
    (moves : List RotationMove) (run : applyMoves? moves source = some target)
    (bound : moves.length ≤ value bs) :
    verifyFramed (frame (emitPackedInputRun source target bs).1
      (emitPackedCertificateRun moves).1) = true := by
  rw [verifyFramed_frame]
  exact verifyBitsRun_emit_trace source target bs moves run bound

end Resources.RotationCertificate.BitPairFraming
