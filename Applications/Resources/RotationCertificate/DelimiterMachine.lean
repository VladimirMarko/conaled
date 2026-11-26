import Applications.Resources.RotationCertificate.FrontEndStreamTapeMachine

set_option autoImplicit false
set_option warningAsError true

/-!
# Paid literal delimiter preprocessing

The fixed source machine consumes literal optional Boolean letters,
separates the input and certificate, and retains supplied registers.
-/

/- Complete preserved component: delimiter_machine. -/
section

namespace Resources.RotationCertificate.DelimiterMachine

open Resources.BinaryCounter (Bits)

abbrev Raw := List (Option Bool)
abbrev Scratch := Option (Option Bool)

inductive CallerStore
  | input | work
  deriving DecidableEq

instance : Fintype CallerStore where
  elems := {.input, .work}
  complete k := by cases k <;> decide

inductive CallerPhase
  | prefix | certificate | reverse | drainInput | drainWork
  deriving DecidableEq

instance : Fintype CallerPhase where
  elems := {.prefix, .certificate, .reverse, .drainInput, .drainWork}
  complete q := by cases q <;> decide

abbrev CallerAlphabet : CallerStore → Type
  | .input => Option Bool
  | .work => Bool

instance callerAlphabetFintype (k : CallerStore) : Fintype (CallerAlphabet k) := by
  cases k with
  | input => exact inferInstanceAs (Fintype (Option Bool))
  | work => exact inferInstanceAs (Fintype Bool)

abbrev Registers (R : Type) := FrontEndStreamMachine.Registers (Scratch × R)
abbrev Statement (R : Type) :=
  FrontEndStreamMachine.Statement CallerAlphabet CallerPhase (Scratch × R)
abbrev Cfg (R : Type) :=
  FrontEndStreamMachine.Cfg CallerAlphabet CallerPhase (Scratch × R)

def inputIndex : FrontEndStreamMachine.StackId CallerStore := .inr (.inr .input)
def workIndex : FrontEndStreamMachine.StackId CallerStore := .inr (.inr .work)
def framedIndex : FrontEndStreamMachine.StackId CallerStore := .inl .framedRaw
def fuelIndex : FrontEndStreamMachine.StackId CallerStore := .inl .fuel

def oldMain : FrontEndStreamMachine.Label CallerPhase :=
  FrontEndStreamMachine.phaseLabel FrontEndStreamMachine.entryPhase

variable {R : Type}

def scratch (regs : Registers R) : Scratch := (FrontEndStreamMachine.user regs).1
def baseUser (regs : Registers R) : R := (FrontEndStreamMachine.user regs).2

/-- Only the finite caller scratch changes. Every old temporary and the base
user value are retained by this actual register update. -/
def setScratch (seen : Scratch) (regs : Registers R) : Registers R :=
  (regs.1, regs.2.1, (regs.2.2.1, (seen, baseUser regs)))

def observeInput (regs : Registers R) (head : Option (Option Bool)) : Registers R :=
  setScratch head regs

def observeWork (regs : Registers R) (head : Option Bool) : Registers R :=
  setScratch (head.map some) regs

def present (regs : Registers R) : Bool := (scratch regs).isSome
def isBit (regs : Registers R) : Bool := ((scratch regs).getD none).isSome
def bit (regs : Registers R) : Bool := ((scratch regs).getD none).getD false

/-- The base user value was never changed. This actual load restores scratch
and every old temporary before entering the old genuine initializer. -/
def reset (regs : Registers R) : Registers R :=
  FrontEndStreamMachine.initialRegisters (none, baseUser regs)

def jump (q : CallerPhase) : Statement R :=
  .goto (fun _ => FrontEndStreamMachine.callerLabel q)

def handoff : Statement R := .load reset (.goto (fun _ => oldMain))

/-- All five caller bodies are fixed independently of the input. -/
def caller : CallerPhase → Statement R
  | .prefix =>
      .pop inputIndex observeInput
        (.branch present
          (.branch isBit
            (.push workIndex (fun _ => false)
              (.push workIndex bit (jump .prefix)))
            (.push workIndex (fun _ => true) (jump .certificate)))
          (jump .drainWork))
  | .certificate =>
      .pop inputIndex observeInput
        (.branch present
          (.branch isBit
            (.push workIndex bit (jump .certificate))
            (jump .drainInput))
          (jump .reverse))
  | .reverse =>
      .pop workIndex observeWork
        (.branch present (.push framedIndex bit (jump .reverse)) handoff)
  | .drainInput =>
      .pop inputIndex observeInput
        (.branch present (jump .drainInput) (jump .drainWork))
  | .drainWork =>
      .pop workIndex observeWork
        (.branch present (jump .drainWork) handoff)

def program : FrontEndStreamMachine.Label CallerPhase → Statement R :=
  FrontEndStreamMachine.program caller

def step : Cfg R → Option (Cfg R) := FrontEndStreamMachine.step caller
def next (c : Option (Cfg R)) : Option (Cfg R) := c.bind step

/-- Typed native optional-step reduction, avoiding package-Cfg rewriting. -/
theorem next_some (c : Cfg R) : next (some c) = step c := rfl

theorem program_caller (q : CallerPhase) :
    program (R := R) (FrontEndStreamMachine.callerLabel q) = caller q := rfl

/-- Counts stack operations in the actual native source syntax. Loads and
branches remain fixed finite register operations; no list traversal is inside
one of these functions. -/
theorem caller_actionBound_le (q : CallerPhase) :
    Resources.TuringSimulation.StackToTape.actionBound (caller (R := R) q) ≤ 3 := by
  cases q with
  | «prefix» => change (3 : ℕ) ≤ 3; decide
  | certificate => change (2 : ℕ) ≤ 3; decide
  | reverse => change (2 : ℕ) ≤ 3; decide
  | drainInput => change (1 : ℕ) ≤ 3; decide
  | drainWork => change (1 : ℕ) ≤ 3; decide

def callerContext (raw : Raw) (work : Bits) : ∀ k, List (CallerAlphabet k)
  | .input => raw
  | .work => work

/-- A complete configuration, including all sixteen original stores. Exactly
framedRaw may be nonempty among those stores; no caller context is omitted. -/
def state (q : CallerPhase) (initial : R) (seen : Scratch)
    (raw : Raw) (work framed : Bits) : Cfg R :=
  FrontEndStreamMachine.cfg (some (FrontEndStreamMachine.callerLabel q))
    (FrontEndStreamMachine.initialRegisters (seen, initial))
    { framedRaw := framed } (callerContext raw work)

section FinitePackage

variable [Fintype R]

/-- The comparison controller has the identical full program and registers.
Its actual entry remains the existing framedRaw parser main. -/
def oldMachine (initial : R) : Turing.FinTM2 :=
  FrontEndStreamMachine.machine caller (none, initial)

/-- The real main/input fields designate the paid prelude and literal caller
input. Output fuel, initial registers and every old program body are retained. -/
def machine (initial : R) : Turing.FinTM2 where
  K := FrontEndStreamMachine.StackId CallerStore
  k₀ := inputIndex
  k₁ := fuelIndex
  Γ := FrontEndStreamMachine.Alphabet CallerAlphabet
  Λ := FrontEndStreamMachine.Label CallerPhase
  main := FrontEndStreamMachine.callerLabel .prefix
  σ := Registers R
  initialState := FrontEndStreamMachine.initialRegisters (none, initial)
  Γk₀Fin := inferInstanceAs (Fintype (Option Bool))
  m := program

@[instance_reducible]
def machineAlphabetFintype (initial : R) (k : (machine initial).K) :
    Fintype ((machine initial).Γ k) :=
  FrontEndStreamMachine.machineAlphabetFintype caller (none, initial) k

theorem machine_inputAlphabet (initial : R) :
    (machine initial).Γ (machine initial).k₀ = Option Bool := rfl

theorem machine_output_alphabet (initial : R) :
    (machine initial).Γ (machine initial).k₁ = Bool := rfl

theorem machine_program_eq_old (initial : R) :
    (machine initial).m = (oldMachine initial).m := rfl

theorem machine_initialState_eq_old (initial : R) :
    (machine initial).initialState = (oldMachine initial).initialState := rfl

theorem machine_step_eq (initial : R) : (machine initial).step = step := rfl
theorem oldMachine_step_eq (initial : R) : (oldMachine initial).step = step := rfl

/-- Changing main and the input index does not change the literal halt. -/
theorem haltList_eq_old (initial : R) (out : Bits) :
    Turing.haltList (machine initial) out = Turing.haltList (oldMachine initial) out := rfl

theorem machine_initList_eq (initial : R) (raw : Raw) :
    Turing.initList (machine initial) raw = state .prefix initial none raw [] [] := by
  apply FrontEndStreamMachine.cfg_ext
  · rfl
  · rfl
  · funext k
    cases k with
    | inl k => cases k <;> rfl
    | inr k => cases k with
      | inl k => cases k <;> rfl
      | inr k => cases k <;> rfl

/-- Once all external stores have actually been drained, the full old
initializer is exactly the intended handoff, with the original user value. -/
theorem oldMachine_initList_eq (initial : R) (framed : Bits) :
    Turing.initList (oldMachine initial) framed =
      FrontEndStreamMachine.cfg (some oldMain)
        (FrontEndStreamMachine.initialRegisters (none, initial))
        { framedRaw := framed } (callerContext [] []) := by
  change Turing.initList (FrontEndStreamMachine.machine caller (none, initial)) framed = _
  rw [FrontEndStreamMachine.machine_initList_eq]
  apply FrontEndStreamMachine.cfg_ext
  · rfl
  · rfl
  · funext k
    cases k with
    | inl k => cases k <;> rfl
    | inr k => cases k with
      | inl k => cases k <;> rfl
      | inr k => cases k <;> rfl

end FinitePackage

/-! ## Local actual transitions

These proof drafts expose all twelve actual branches, including prefix push
order and cleanup/reset at reverse completion. Their full store equalities
are written extensionally, including both caller stores. All twelve branches
still need ordinary Lean validation; no compiler was run here.
-/

theorem step_prefix_bit (initial : R) (seen : Scratch) (b : Bool)
    (raw : Raw) (work framed : Bits) :
    step (state .prefix initial seen (some b :: raw) work framed) =
      some (state .prefix initial (some (some b)) raw (b :: false :: work) framed) := by
  apply congrArg some
  apply FrontEndStreamMachine.cfg_ext
  · rfl
  · rfl
  · funext k
    cases k with
    | inl k => cases k <;> rfl
    | inr k => cases k with
      | inl k => cases k <;> rfl
      | inr k => cases k <;> rfl

theorem step_prefix_delimiter (initial : R) (seen : Scratch)
    (raw : Raw) (work framed : Bits) :
    step (state .prefix initial seen (none :: raw) work framed) =
      some (state .certificate initial (some none) raw (true :: work) framed) := by
  apply congrArg some
  apply FrontEndStreamMachine.cfg_ext
  · rfl
  · rfl
  · funext k
    cases k with
    | inl k => cases k <;> rfl
    | inr k => cases k with
      | inl k => cases k <;> rfl
      | inr k => cases k <;> rfl

theorem step_prefix_empty (initial : R) (seen : Scratch) (work framed : Bits) :
    step (state .prefix initial seen [] work framed) =
      some (state .drainWork initial none [] work framed) := by
  apply congrArg some
  apply FrontEndStreamMachine.cfg_ext
  · rfl
  · rfl
  · funext k
    cases k with
    | inl k => cases k <;> rfl
    | inr k => cases k with
      | inl k => cases k <;> rfl
      | inr k => cases k <;> rfl

theorem step_certificate_bit (initial : R) (seen : Scratch) (b : Bool)
    (raw : Raw) (work framed : Bits) :
    step (state .certificate initial seen (some b :: raw) work framed) =
      some (state .certificate initial (some (some b)) raw (b :: work) framed) := by
  apply congrArg some
  apply FrontEndStreamMachine.cfg_ext
  · rfl
  · rfl
  · funext k
    cases k with
    | inl k => cases k <;> rfl
    | inr k => cases k with
      | inl k => cases k <;> rfl
      | inr k => cases k <;> rfl

theorem step_certificate_delimiter (initial : R) (seen : Scratch)
    (raw : Raw) (work framed : Bits) :
    step (state .certificate initial seen (none :: raw) work framed) =
      some (state .drainInput initial (some none) raw work framed) := by
  apply congrArg some
  apply FrontEndStreamMachine.cfg_ext
  · rfl
  · rfl
  · funext k
    cases k with
    | inl k => cases k <;> rfl
    | inr k => cases k with
      | inl k => cases k <;> rfl
      | inr k => cases k <;> rfl

theorem step_certificate_empty (initial : R) (seen : Scratch) (work framed : Bits) :
    step (state .certificate initial seen [] work framed) =
      some (state .reverse initial none [] work framed) := by
  apply congrArg some
  apply FrontEndStreamMachine.cfg_ext
  · rfl
  · rfl
  · funext k
    cases k with
    | inl k => cases k <;> rfl
    | inr k => cases k with
      | inl k => cases k <;> rfl
      | inr k => cases k <;> rfl

theorem step_reverse_bit (initial : R) (seen : Scratch) (b : Bool)
    (work framed : Bits) :
    step (state .reverse initial seen [] (b :: work) framed) =
      some (state .reverse initial (some (some b)) [] work (b :: framed)) := by
  apply congrArg some
  apply FrontEndStreamMachine.cfg_ext
  · rfl
  · rfl
  · funext k
    cases k with
    | inl k => cases k <;> rfl
    | inr k => cases k with
      | inl k => cases k <;> rfl
      | inr k => cases k <;> rfl

theorem step_drainInput_cons (initial : R) (seen : Scratch) (a : Option Bool)
    (raw : Raw) (work framed : Bits) :
    step (state .drainInput initial seen (a :: raw) work framed) =
      some (state .drainInput initial (some a) raw work framed) := by
  apply congrArg some
  apply FrontEndStreamMachine.cfg_ext
  · rfl
  · rfl
  · funext k
    cases k with
    | inl k => cases k <;> rfl
    | inr k => cases k with
      | inl k => cases k <;> rfl
      | inr k => cases k <;> rfl

theorem step_drainInput_empty (initial : R) (seen : Scratch) (work framed : Bits) :
    step (state .drainInput initial seen [] work framed) =
      some (state .drainWork initial none [] work framed) := by
  apply congrArg some
  apply FrontEndStreamMachine.cfg_ext
  · rfl
  · rfl
  · funext k
    cases k with
    | inl k => cases k <;> rfl
    | inr k => cases k with
      | inl k => cases k <;> rfl
      | inr k => cases k <;> rfl

theorem step_drainWork_bit (initial : R) (seen : Scratch) (b : Bool) (work : Bits) :
    step (state .drainWork initial seen [] (b :: work) []) =
      some (state .drainWork initial (some (some b)) [] work []) := by
  apply congrArg some
  apply FrontEndStreamMachine.cfg_ext
  · rfl
  · rfl
  · funext k
    cases k with
    | inl k => cases k <;> rfl
    | inr k => cases k with
      | inl k => cases k <;> rfl
      | inr k => cases k <;> rfl

theorem step_reverse_empty [Fintype R] (initial : R) (seen : Scratch) (framed : Bits) :
    step (state .reverse initial seen [] [] framed) =
      some (Turing.initList (oldMachine initial) framed) := by
  rw [oldMachine_initList_eq]
  apply congrArg some
  apply FrontEndStreamMachine.cfg_ext
  · rfl
  · rfl
  · funext k
    cases k with
    | inl k => cases k <;> rfl
    | inr k => cases k with
      | inl k => cases k <;> rfl
      | inr k => cases k <;> rfl

theorem step_drainWork_empty [Fintype R] (initial : R) (seen : Scratch) :
    step (state .drainWork initial seen [] [] []) =
      some (Turing.initList (oldMachine initial) []) := by
  exact step_reverse_empty initial seen []

/-! ## Proof-side protocol functions

None of these whole-word functions is called by a machine statement or its
initializer. They specify the language, exact time and execution invariants.
-/

def literalPair (input cert : Bits) : Raw :=
  input.map some ++ [none] ++ cert.map some

def suffixBits : Raw → Option Bits
  | [] => some []
  | none :: _ => none
  | some b :: rest => (suffixBits rest).map (b :: ·)

def splitLiteral : Raw → Option (Bits × Bits)
  | [] => none
  | none :: rest => (suffixBits rest).map (fun cert => ([], cert))
  | some b :: rest => (splitLiteral rest).map (fun pair => (b :: pair.1, pair.2))

def handoffWord (raw : Raw) : Bits :=
  match splitLiteral raw with
  | none => []
  | some (input, cert) => BitPairFraming.frame input cert

def verifyDelimited (raw : Raw) : Bool :=
  match splitLiteral raw with
  | none => false
  | some (input, cert) => (verifyBitsRun input cert).1

/-- Number of work cells after the first delimiter, stopping at the second. -/
def suffixWorkLength : Raw → Nat
  | [] => 0
  | none :: _ => 0
  | some _ :: rest => suffixWorkLength rest + 1

/-- Final work length before reversal or clearing. All remaining raw letters
after a repeated delimiter are still consumed, but add no work cells. -/
def workLength : Raw → Nat
  | [] => 0
  | none :: rest => suffixWorkLength rest + 1
  | some _ :: rest => workLength rest + 2

def preludeSteps (raw : Raw) : Nat := raw.length + workLength raw + 2

theorem suffixWorkLength_le (raw : Raw) : suffixWorkLength raw ≤ raw.length := by
  induction raw with
  | nil => exact Nat.le_refl 0
  | cons a rest ih => cases a <;> simp only [suffixWorkLength, List.length_cons] <;> omega

theorem workLength_le (raw : Raw) : workLength raw ≤ 2 * raw.length := by
  induction raw with
  | nil => exact Nat.le_refl 0
  | cons a rest ih =>
      cases a with
      | none =>
          have h := suffixWorkLength_le rest
          simp only [workLength, List.length_cons]
          omega
      | some b =>
          simp only [workLength, List.length_cons]
          omega

theorem preludeSteps_le (raw : Raw) : preludeSteps raw ≤ 3 * raw.length + 2 := by
  have h := workLength_le raw
  unfold preludeSteps
  omega

theorem literalPair_length (input cert : Bits) :
    (literalPair input cert).length = input.length + cert.length + 1 := by
  simp only [literalPair, List.length_append, List.length_map, List.length_cons, List.length_nil]
  omega

theorem suffixBits_map (cert : Bits) : suffixBits (cert.map some) = some cert := by
  induction cert with
  | nil => rfl
  | cons b cert ih => simp only [List.map_cons, suffixBits, ih, Option.map_some]

theorem splitLiteral_pair (input cert : Bits) :
    splitLiteral (literalPair input cert) = some (input, cert) := by
  induction input with
  | nil => simp only [literalPair, List.map_nil, List.nil_append, List.cons_append,
      splitLiteral, suffixBits_map, Option.map_some]
  | cons b input ih =>
      change (splitLiteral (literalPair input cert)).map
        (fun pair => (b :: pair.1, pair.2)) = some (b :: input, cert)
      rw [ih]
      rfl

theorem handoffWord_pair (input cert : Bits) :
    handoffWord (literalPair input cert) = BitPairFraming.frame input cert := by
  rw [handoffWord, splitLiteral_pair]

theorem verifyDelimited_pair (input cert : Bits) :
    verifyDelimited (literalPair input cert) = (verifyBitsRun input cert).1 := by
  rw [verifyDelimited, splitLiteral_pair]

theorem verifyFramed_handoffWord (raw : Raw) :
    BitPairFraming.verifyFramed (handoffWord raw) = verifyDelimited raw := by
  cases h : splitLiteral raw with
  | none => simp only [handoffWord, verifyDelimited, h,
      BitPairFraming.verifyFramed, BitPairFraming.unframe_nil]
  | some pair =>
      rcases pair with ⟨input, cert⟩
      simp only [handoffWord, verifyDelimited, h, BitPairFraming.verifyFramed_frame]

theorem binaryYes_iff_exists_delimited_certificate (input : Bits) :
    BinaryYes input ↔ ∃ cert : Bits, verifyDelimited (literalPair input cert) = true := by
  simpa only [verifyDelimited_pair] using binaryYes_iff_exists_certificate input

theorem binaryYes_iff_exists_small_delimited_certificate (input : Bits) :
    BinaryYes input ↔ ∃ cert : Bits,
      cert.length ≤ input.length ^ 2 ∧
      (literalPair input cert).length ≤ input.length ^ 2 + input.length + 1 ∧
      verifyDelimited (literalPair input cert) = true := by
  constructor
  · intro yes
    obtain ⟨cert, small, accepted⟩ := verifyBitsRun_complete_small input yes
    refine ⟨cert, small, ?_, ?_⟩
    · rw [literalPair_length]
      omega
    · rw [verifyDelimited_pair]
      exact accepted
  · rintro ⟨cert, _, _, accepted⟩
    apply verifyBitsRun_sound input cert
    rwa [verifyDelimited_pair] at accepted

/-! ## Complete proof-side boundary invariant

All raw words have one of the missing/valid/repeated forms used below. The
constructors specify the full configuration, including exact scratch and all
stores. `PreludeInvariant` is a proof relation, not a reachability
theorem. Its execution/completeness obligations are explicitly unproved here.
-/

def lastInputPop (seed : Scratch) (consumed : Raw) : Scratch :=
  match consumed.reverse with
  | [] => seed
  | a :: _ => some a

def lastBitPop (seed : Scratch) (consumed : Bits) : Scratch :=
  lastInputPop seed (consumed.map some)

inductive PreludeInvariant [Fintype R] (initial : R) (raw : Raw) : Nat → Cfg R → Prop
  | prefix (before : Bits) (rest : Raw)
      (whole : raw = before.map some ++ rest) :
      PreludeInvariant initial raw before.length
        (state .prefix initial (lastBitPop none before) rest
          (BitPairFraming.escapeBits before).reverse [])
  | certificate (input before : Bits) (rest : Raw)
      (whole : raw = literalPair input before ++ rest) :
      PreludeInvariant initial raw (input.length + 1 + before.length)
        (state .certificate initial (lastBitPop (some none) before) rest
          (BitPairFraming.frame input before).reverse [])
  | reverse (input cert : Bits) (j : Nat)
      (whole : raw = literalPair input cert)
      (within : j ≤ (BitPairFraming.frame input cert).length) :
      PreludeInvariant initial raw (raw.length + 1 + j)
        (state .reverse initial
          (lastBitPop none ((BitPairFraming.frame input cert).reverse.take j)) []
          ((BitPairFraming.frame input cert).reverse.drop j)
          ((BitPairFraming.frame input cert).reverse.take j).reverse)
  | drain_input (input cert : Bits) (tail : Raw) (j : Nat)
      (whole : raw = literalPair input cert ++ none :: tail)
      (within : j ≤ tail.length) :
      PreludeInvariant initial raw (input.length + cert.length + 2 + j)
        (state .drainInput initial (lastInputPop (some none) (tail.take j))
          (tail.drop j) (BitPairFraming.frame input cert).reverse [])
  | drain_missing (input : Bits) (j : Nat)
      (whole : raw = input.map some)
      (within : j ≤ (BitPairFraming.escapeBits input).length) :
      PreludeInvariant initial raw (raw.length + 1 + j)
        (state .drainWork initial
          (lastBitPop none ((BitPairFraming.escapeBits input).reverse.take j)) []
          ((BitPairFraming.escapeBits input).reverse.drop j) [])
  | drain_repeated (input cert : Bits) (tail : Raw) (j : Nat)
      (whole : raw = literalPair input cert ++ none :: tail)
      (within : j ≤ (BitPairFraming.frame input cert).length) :
      PreludeInvariant initial raw (raw.length + 1 + j)
        (state .drainWork initial
          (lastBitPop none ((BitPairFraming.frame input cert).reverse.take j)) []
          ((BitPairFraming.frame input cert).reverse.drop j) [])
  | handoff_valid (input cert : Bits) (whole : raw = literalPair input cert) :
      PreludeInvariant initial raw (raw.length + (BitPairFraming.frame input cert).length + 2)
        (Turing.initList (oldMachine initial) (BitPairFraming.frame input cert))
  | handoff_missing (input : Bits) (whole : raw = input.map some) :
      PreludeInvariant initial raw (raw.length + 2 * input.length + 2)
        (Turing.initList (oldMachine initial) [])
  | handoff_repeated (input cert : Bits) (tail : Raw)
      (whole : raw = literalPair input cert ++ none :: tail) :
      PreludeInvariant initial raw (raw.length + (BitPairFraming.frame input cert).length + 2)
        (Turing.initList (oldMachine initial) [])

/-- Exact execution from the package's literal initializer. The execution
module proves this contract as `Execution.handoff_obligation`. -/
def HandoffObligation [Fintype R] : Prop :=
  ∀ (initial : R) (raw : Raw),
    next^[preludeSteps raw] (some (Turing.initList (machine initial) raw)) =
      some (Turing.initList (oldMachine initial) (handoffWord raw))

/-- Every actual source boundary, including the final handoff, has the
complete invariant and total occupancy bound. The execution module proves
this contract as `Execution.prefix_obligation`. -/
def PrefixObligation [Fintype R] : Prop :=
  ∀ (initial : R) (raw : Raw) (n : Nat), n ≤ preludeSteps raw →
    ∃ reached,
      next^[n] (some (Turing.initList (machine initial) raw)) = some reached ∧
      PreludeInvariant initial raw n reached ∧
      FrontEndStreamMachine.stackCells reached ≤ 2 * raw.length

def totalSourceSteps (raw : Raw) : Nat :=
  preludeSteps raw + FrontEndStreamMachine.runSteps (handoffWord raw)

/-- Source-time bound proved by `Execution.totalSourceSteps_le`. -/
def sourceTimeBound (N : Nat) : Nat := 4 * N * N + 23 * N + 38

/-- The actual fixed full program determines A before the input. -/
def actionMaximum [Fintype R] : Nat :=
  Resources.TuringSimulation.StackToTape.finiteActionBound (program (R := R))

/-- Primitive execution bound proved by `Native.encoded_native_run` from the
paid source run and prefix occupancy. `Native.ordinary_run` adds ordinary I/O. -/
def encodedPrimitiveTimeBound (A N : Nat) : Nat :=
  3 * sourceTimeBound N * (1 + A * (2 * (2 * N + 1 + A) + 2))

end Resources.RotationCertificate.DelimiterMachine

end
