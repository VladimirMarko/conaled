import Applications.Resources.RotationCertificate.BitCodec
import Mathlib.Computability.TuringMachine.Computable

/-!
# A finite TM2 machine for complete four-bit decoding

The input, reverse, and output stacks have finite alphabets Bool, Fin 16, and
Option (Fin 16). Four optional-bit registers and one optional-tag register are
finite control. A fixed scan statement consumes up to four actual input cells;
successful blocks push a tag onto the reverse stack. Emit reverses those tags
into output. Failure clears every accumulated tag. Every jump and halt resets
the registers, and both final configurations have empty nonoutput stacks.

The exact transition theorem concerns the pinned TM2.step, including reversal
and cleanup. It does not relabel the source decoder's measured observation as
machine time. This decoder component does not yet implement the complete
certificate verifier or establish the remaining formal NP correspondence.
Correspondence: `docs/research/fdsa-rotation-certificate-preparation.md`.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.RotationCertificate.BitDecoderMachine
open Resources.BinaryCounter (Bits)

inductive StackId
  | input | reverse | output
  deriving DecidableEq

instance : Fintype StackId where
  elems := {.input, .reverse, .output}
  complete k := by cases k <;> decide

inductive Label
  | scan | emit | clear
  deriving DecidableEq

instance : Fintype Label where
  elems := {.scan, .emit, .clear}
  complete label := by cases label <;> decide

abbrev Alphabet : StackId → Type
  | .input => Bool
  | .reverse => Tag
  | .output => Option Tag

instance alphabetFintype (k : StackId) : Fintype (Alphabet k) := by
  cases k with
  | input => exact inferInstanceAs (Fintype Bool)
  | reverse => exact inferInstanceAs (Fintype Tag)
  | output => exact inferInstanceAs (Fintype (Option Tag))

structure Registers where
  b0 : Option Bool
  b1 : Option Bool
  b2 : Option Bool
  b3 : Option Bool
  tag : Option Tag
  deriving DecidableEq, Fintype

def zeroRegisters : Registers := ⟨none, none, none, none, none⟩

/-- Ordinary decoder failure and successful empty decoding have different codes. -/
def resultCode : Option Word → List (Option Tag)
  | none => []
  | some word => none :: word.map some

theorem resultCode_injective : Function.Injective resultCode := by
  intro left right equal
  cases left with
  | none => cases right with
    | none => rfl
    | some word => cases equal
  | some left => cases right with
    | none => cases equal
    | some right =>
        have mapped := (List.cons.inj equal).2
        exact congrArg some
          ((List.map_injective_iff.mpr (Option.some_injective Tag)) mapped)

abbrev Statement := Turing.TM2.Stmt Alphabet Label Registers

def store0 (r : Registers) (b : Option Bool) : Registers := { r with b0 := b }
def store1 (r : Registers) (b : Option Bool) : Registers := { r with b1 := b }
def store2 (r : Registers) (b : Option Bool) : Registers := { r with b2 := b }
def store3 (r : Registers) (b : Option Bool) : Registers := { r with b3 := b }
def storeTag (r : Registers) (tag : Option Tag) : Registers := { r with tag := tag }

/-- This callback sees only four finite registers, never a word or input list. -/
def nibble (r : Registers) : Tag :=
  (decodeTagRun (r.b0.getD false) (r.b1.getD false)
    (r.b2.getD false) (r.b3.getD false)).1

def jump (label : Label) : Statement :=
  .load (fun _ => zeroRegisters) (.goto (fun _ => label))

def finish : Statement := .load (fun _ => zeroRegisters) .halt

/-- All unbounded repetition is an actual goto between these fixed finite blocks. -/
def program : Label → Statement
  | .scan =>
      .pop .input store0 (.branch (fun r => r.b0.isSome)
        (.pop .input store1 (.branch (fun r => r.b1.isSome)
          (.pop .input store2 (.branch (fun r => r.b2.isSome)
            (.pop .input store3 (.branch (fun r => r.b3.isSome)
              (.push .reverse nibble (jump .scan))
              (jump .clear)))
            (jump .clear)))
          (jump .clear)))
        (jump .emit))
  | .emit =>
      .pop .reverse storeTag (.branch (fun r => r.tag.isSome)
        (.push .output (fun r => some (r.tag.getD 0)) (jump .emit))
        (.push .output (fun _ => none) finish))
  | .clear =>
      .pop .reverse storeTag (.branch (fun r => r.tag.isSome)
        (jump .clear) finish)

abbrev machine : Turing.FinTM2 where
  K := StackId
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := Label
  main := .scan
  σ := Registers
  initialState := zeroRegisters
  m := program

/-- Explicit configurations expose every stack rather than only the output projection. -/
def cfg (label : Option Label) (regs : Registers) (input : Bits) (rev : Word)
    (output : List (Option Tag)) : machine.Cfg where
  l := label
  var := regs
  stk
    | .input => input
    | .reverse => rev
    | .output => output

private theorem cfg_ext {left right : machine.Cfg}
    (label : left.l = right.l) (regs : left.var = right.var)
    (input : left.stk .input = right.stk .input)
    (rev : left.stk .reverse = right.stk .reverse)
    (output : left.stk .output = right.stk .output) : left = right := by
  have stackEq : left.stk = right.stk := by
    funext k
    cases k with
    | input => exact input
    | reverse => exact rev
    | output => exact output
  cases left
  cases right
  cases label
  cases regs
  cases stackEq
  rfl

theorem cfg_eta (c : machine.Cfg) :
    cfg c.l c.var (c.stk .input) (c.stk .reverse) (c.stk .output) = c := by
  apply cfg_ext <;> rfl

theorem initList_eq (raw : Bits) :
    Turing.initList machine raw = cfg (some .scan) zeroRegisters raw [] [] := by
  apply cfg_ext <;> rfl

theorem haltList_eq (out : List (Option Tag)) :
    Turing.haltList machine out = cfg none zeroRegisters [] [] out := by
  apply cfg_ext <;> rfl

/-- A complete block is consumed in one actual bounded TM2 statement. -/
theorem scan_step_block (b0 b1 b2 b3 : Bool) (raw : Bits) (rev : Word)
    (out : List (Option Tag)) (regs : Registers) :
    machine.step (cfg (some .scan) regs (b0 :: b1 :: b2 :: b3 :: raw) rev out) =
      some (cfg (some .scan) zeroRegisters raw
        ((decodeTagRun b0 b1 b2 b3).1 :: rev) out) := by
  apply congrArg some
  apply cfg_ext <;> rfl

theorem scan_step_nil (rev : Word) (out : List (Option Tag)) (regs : Registers) :
    machine.step (cfg (some .scan) regs [] rev out) =
      some (cfg (some .emit) zeroRegisters [] rev out) := by
  apply congrArg some
  apply cfg_ext <;> rfl

theorem scan_step_one (b0 : Bool) (rev : Word) (out : List (Option Tag))
    (regs : Registers) :
    machine.step (cfg (some .scan) regs [b0] rev out) =
      some (cfg (some .clear) zeroRegisters [] rev out) := by
  apply congrArg some
  apply cfg_ext <;> rfl

theorem scan_step_two (b0 b1 : Bool) (rev : Word) (out : List (Option Tag))
    (regs : Registers) :
    machine.step (cfg (some .scan) regs [b0, b1] rev out) =
      some (cfg (some .clear) zeroRegisters [] rev out) := by
  apply congrArg some
  apply cfg_ext <;> rfl

theorem scan_step_three (b0 b1 b2 : Bool) (rev : Word) (out : List (Option Tag))
    (regs : Registers) :
    machine.step (cfg (some .scan) regs [b0, b1, b2] rev out) =
      some (cfg (some .clear) zeroRegisters [] rev out) := by
  apply congrArg some
  apply cfg_ext <;> rfl

theorem emit_step_cons (tag : Tag) (rev : Word) (raw : Bits)
    (out : List (Option Tag)) (regs : Registers) :
    machine.step (cfg (some .emit) regs raw (tag :: rev) out) =
      some (cfg (some .emit) zeroRegisters raw rev (some tag :: out)) := by
  apply congrArg some
  apply cfg_ext <;> rfl

theorem emit_step_nil (raw : Bits) (out : List (Option Tag)) (regs : Registers) :
    machine.step (cfg (some .emit) regs raw [] out) =
      some (cfg none zeroRegisters raw [] (none :: out)) := by
  apply congrArg some
  apply cfg_ext <;> rfl

theorem clear_step_cons (tag : Tag) (rev : Word) (raw : Bits)
    (out : List (Option Tag)) (regs : Registers) :
    machine.step (cfg (some .clear) regs raw (tag :: rev) out) =
      some (cfg (some .clear) zeroRegisters raw rev out) := by
  apply congrArg some
  apply cfg_ext <;> rfl

theorem clear_step_nil (raw : Bits) (out : List (Option Tag)) (regs : Registers) :
    machine.step (cfg (some .clear) regs raw [] out) =
      some (cfg none zeroRegisters raw [] out) := by
  apply congrArg some
  apply cfg_ext <;> rfl

theorem halt_step (regs : Registers) (raw : Bits) (rev : Word)
    (out : List (Option Tag)) : machine.step (cfg none regs raw rev out) = none := rfl

/-- The ordinary optional lift of the actual machine transition. -/
def next (c : Option machine.Cfg) : Option machine.Cfg := c.bind machine.step

@[simp] theorem next_none : next none = none := rfl
@[simp] theorem next_some (c : machine.Cfg) : next (some c) = machine.step c := rfl

private theorem iterate_step (n : Nat) (c d : machine.Cfg)
    (step : machine.step c = some d) :
    next^[n + 1] (some c) = next^[n] (some d) := by
  rw [Function.iterate_succ_apply, next_some, step]

/-- Actual reversal, including the final marker/reset/halt and arbitrary old output. -/
theorem emit_iterate (rev : Word) (out : List (Option Tag)) (regs : Registers) :
    next^[rev.length + 1] (some (cfg (some .emit) regs [] rev out)) =
      some (Turing.haltList machine (none :: (rev.reverse.map some ++ out))) := by
  induction rev generalizing out regs with
  | nil =>
      simp only [List.length_nil, Nat.zero_add, Function.iterate_one, next_some,
        emit_step_nil, List.reverse_nil, List.map_nil, List.nil_append, haltList_eq]
  | cons tag rev ih =>
      rw [show (tag :: rev).length + 1 = (rev.length + 1) + 1 by rfl,
        iterate_step _ _ _ (emit_step_cons tag rev [] out regs), ih]
      simp [List.reverse_cons, List.map_append, List.append_assoc]

/-- Actual cleanup preserves an arbitrary output suffix while emptying the work stack. -/
theorem clear_iterate (rev : Word) (out : List (Option Tag)) (regs : Registers) :
    next^[rev.length + 1] (some (cfg (some .clear) regs [] rev out)) =
      some (Turing.haltList machine out) := by
  induction rev generalizing regs with
  | nil =>
      simp only [List.length_nil, Nat.zero_add, Function.iterate_one, next_some,
        clear_step_nil, haltList_eq]
  | cons tag rev ih =>
      rw [show (tag :: rev).length + 1 = (rev.length + 1) + 1 by rfl,
        iterate_step _ _ _ (clear_step_cons tag rev [] out regs), ih]

private theorem scan_count_of_short (raw : Bits) (rev : Word)
    (short : raw.length < 4) :
    2 * (raw.length / 4) + rev.length + 2 = rev.length + 2 := by
  omega

/-- Arbitrary suffixes and reverse accumulators, including failed continuation cleanup. -/
theorem scan_iterate (raw : Bits) (rev : Word) (regs : Registers) :
    next^[2 * (raw.length / 4) + rev.length + 2]
        (some (cfg (some .scan) regs raw rev [])) =
      some (Turing.haltList machine
        (resultCode ((unpackWordRun raw).1.map (fun suffix => rev.reverse ++ suffix)))) := by
  induction raw using unpackWordRun.induct generalizing rev regs with
  | case1 =>
      rw [scan_count_of_short [] rev (by decide)]
      rw [show rev.length + 2 = (rev.length + 1) + 1 by rfl,
        iterate_step _ _ _ (scan_step_nil rev [] regs), emit_iterate]
      simp [unpackWordRun, resultCode]
  | case2 b0 =>
      rw [scan_count_of_short [b0] rev (by change 1 < 4; decide)]
      change next^[rev.length + 2] (some (cfg (some .scan) regs [b0] rev [])) =
        some (Turing.haltList machine [])
      rw [show rev.length + 2 = (rev.length + 1) + 1 by rfl,
        iterate_step _ _ _ (scan_step_one b0 rev [] regs), clear_iterate]
  | case3 b0 b1 =>
      rw [scan_count_of_short [b0, b1] rev (by change 2 < 4; decide)]
      change next^[rev.length + 2] (some (cfg (some .scan) regs [b0, b1] rev [])) =
        some (Turing.haltList machine [])
      rw [show rev.length + 2 = (rev.length + 1) + 1 by rfl,
        iterate_step _ _ _ (scan_step_two b0 b1 rev [] regs), clear_iterate]
  | case4 b0 b1 b2 =>
      rw [scan_count_of_short [b0, b1, b2] rev (by change 3 < 4; decide)]
      change next^[rev.length + 2] (some (cfg (some .scan) regs [b0, b1, b2] rev [])) =
        some (Turing.haltList machine [])
      rw [show rev.length + 2 = (rev.length + 1) + 1 by rfl,
        iterate_step _ _ _ (scan_step_three b0 b1 b2 rev [] regs), clear_iterate]
  | case5 b0 b1 b2 b3 raw ih =>
      have count : 2 * (List.length (b0 :: b1 :: b2 :: b3 :: raw) / 4) +
          rev.length + 2 =
          (2 * (raw.length / 4) + ((decodeTagRun b0 b1 b2 b3).1 :: rev).length + 2) + 1 := by
        simp only [List.length_cons]
        omega
      rw [count, iterate_step _ _ _ (scan_step_block b0 b1 b2 b3 raw rev [] regs), ih,
        unpackWordRun_cons4]
      cases returned : unpackWordRun raw with
      | mk result cost => cases result with
        | none => rfl
        | some suffix => simp [List.reverse_cons, List.append_assoc, resultCode]

/-- A mathematical count of actual transitions; the program never computes it. -/
def runSteps (raw : Bits) : Nat := 2 * (raw.length / 4) + 2

/-- Every raw input reaches the exact reset halt configuration in the stated steps. -/
theorem machine_run (raw : Bits) :
    next^[runSteps raw] (some (Turing.initList machine raw)) =
      some (Turing.haltList machine (resultCode (unpackWordRun raw).1)) := by
  simpa [runSteps, initList_eq] using scan_iterate raw [] zeroRegisters

theorem runSteps_le (raw : Bits) : runSteps raw ≤ raw.length + 2 := by
  unfold runSteps
  omega

/-- Construct timed data from actual iterate equality, with the exact witness count. -/
def outputsInTimeExact (raw : Bits) :
    Turing.TM2OutputsInTime machine raw
      (some (resultCode (unpackWordRun raw).1)) (runSteps raw) where
  steps := runSteps raw
  evals_in_steps := machine_run raw
  steps_le_m := Nat.le_refl _

/-- A linear bound on the actual machine execution, valid on malformed input as well. -/
def outputsInTime (raw : Bits) :
    Turing.TM2OutputsInTime machine raw
      (some (resultCode (unpackWordRun raw).1)) (raw.length + 2) where
  steps := runSteps raw
  evals_in_steps := machine_run raw
  steps_le_m := runSteps_le raw

/-- The fixed finite machine supplies the execution field of the polynomial record. -/
noncomputable def computableInPolyTime :
    Turing.TM2ComputableInPolyTime (id : Bits → List Bool) resultCode
      (fun raw => (unpackWordRun raw).1) where
  tm := machine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl (Option Tag)
  time := Polynomial.X + 2
  outputsFun raw := by simpa [List.map_id] using outputsInTime raw

theorem machine_run_code (word : Word) :
    next^[2 * word.length + 2] (some (Turing.initList machine (wordBits word))) =
      some (Turing.haltList machine (resultCode (some word))) := by
  have count : runSteps (wordBits word) = 2 * word.length + 2 := by
    rw [runSteps, wordBits_length]
    omega
  have run := machine_run (wordBits word)
  rw [count, unpackWordRun_code] at run
  exact run

theorem machine_run_partial (word : Word) (short : Bits)
    (positive : 0 < short.length) (incomplete : short.length < 4) :
    next^[2 * word.length + 2]
        (some (Turing.initList machine (wordBits word ++ short))) =
      some (Turing.haltList machine []) := by
  have count : runSteps (wordBits word ++ short) = 2 * word.length + 2 := by
    rw [runSteps, List.length_append, wordBits_length]
    omega
  have run := machine_run (wordBits word ++ short)
  rw [count, unpackWordRun_partial word short positive incomplete] at run
  exact run

/-- Number of actual cells on the three machine stacks. -/
def stackCells (c : machine.Cfg) : Nat :=
  (c.stk .input).length + (c.stk .reverse).length + (c.stk .output).length

/-- One cell reserved for the eventual successful-output marker. -/
def credit : Option Label → Nat
  | some .scan => 1
  | some .emit => 1
  | some .clear => 0
  | none => 0

def potential (c : machine.Cfg) : Nat := stackCells c + credit c.l

/-- Every actual successful transition is nonincreasing, from any configuration. -/
theorem step_potential_le (c d : machine.Cfg)
    (stepped : machine.step c = some d) : potential d ≤ potential c := by
  obtain ⟨label, regs, raw, rev, out, rfl⟩ :
      ∃ (label : Option Label) (regs : Registers) (raw : Bits) (rev : Word)
        (out : List (Option Tag)), c = cfg label regs raw rev out :=
    ⟨c.l, c.var, c.stk .input, c.stk .reverse, c.stk .output, (cfg_eta c).symm⟩
  cases label with
  | none =>
      rw [halt_step] at stepped
      cases stepped
  | some label =>
      cases label with
      | scan =>
          cases raw with
          | nil =>
              rw [scan_step_nil] at stepped
              cases Option.some.inj stepped
              simp only [potential, stackCells, credit, cfg, List.length_nil]; omega
          | cons b0 raw =>
              cases raw with
              | nil =>
                  rw [scan_step_one] at stepped
                  cases Option.some.inj stepped
                  simp only [potential, stackCells, credit, cfg,
                    List.length_nil, List.length_cons]; omega
              | cons b1 raw =>
                  cases raw with
                  | nil =>
                      rw [scan_step_two] at stepped
                      cases Option.some.inj stepped
                      simp only [potential, stackCells, credit, cfg,
                        List.length_nil, List.length_cons]; omega
                  | cons b2 raw =>
                      cases raw with
                      | nil =>
                          rw [scan_step_three] at stepped
                          cases Option.some.inj stepped
                          simp only [potential, stackCells, credit, cfg,
                            List.length_nil, List.length_cons]; omega
                      | cons b3 raw =>
                          rw [scan_step_block] at stepped
                          cases Option.some.inj stepped
                          simp only [potential, stackCells, credit, cfg,
                            List.length_cons]; omega
      | emit =>
          cases rev with
          | nil =>
              rw [emit_step_nil] at stepped
              cases Option.some.inj stepped
              simp only [potential, stackCells, credit, cfg,
                List.length_nil, List.length_cons]; omega
          | cons tag rev =>
              rw [emit_step_cons] at stepped
              cases Option.some.inj stepped
              simp only [potential, stackCells, credit, cfg, List.length_cons]; omega
      | clear =>
          cases rev with
          | nil =>
              rw [clear_step_nil] at stepped
              cases Option.some.inj stepped
              simp only [potential, stackCells, credit, cfg, List.length_nil]; omega
          | cons tag rev =>
              rw [clear_step_cons] at stepped
              cases Option.some.inj stepped
              simp only [potential, stackCells, credit, cfg, List.length_cons]; omega

/-- Monotonicity along the actual TM2 reflexive-transitive step relation. -/
theorem reaches_potential_le (start reached : machine.Cfg)
    (run : Turing.TM2.Reaches program start reached) :
    potential reached ≤ potential start := by
  change Relation.ReflTransGen
    (fun before after : machine.Cfg => machine.step before = some after)
    start reached at run
  induction run with
  | refl => exact Nat.le_refl _
  | @tail before after _ step ih =>
      exact Nat.le_trans (step_potential_le before after step) ih

/-- Every reached block-boundary configuration uses at most one extra stack cell. -/
theorem reachable_stackCells_le (raw : Bits) (reached : machine.Cfg)
    (run : Turing.TM2.Reaches program (Turing.initList machine raw) reached) :
    stackCells reached ≤ raw.length + 1 := by
  have initial : potential (Turing.initList machine raw) = raw.length + 1 := by
    simp [initList_eq, potential, stackCells, credit, cfg]
  have bounded := reaches_potential_le (Turing.initList machine raw) reached run
  rw [initial] at bounded
  unfold potential at bounded
  omega

end Resources.RotationCertificate.BitDecoderMachine
