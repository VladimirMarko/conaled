import Applications.Resources.RotationCertificate.TreeParser
import Applications.Resources.RotationCertificate.Execution
import Applications.Resources.BinaryCounter.FixedWidthMachine
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Open finite comparison of two represented tree words

One actual finite block pops both physical stacks, compares the two observed
optional tags and resets its finite temporaries. Equal heads cause one real
loop transition; unequal heads or an EOF observation reach a live result.
Words, tree equality, exact counts, ranks and prefixes below are proof-side.
Correspondence: `docs/research/fdsa-rotation-certificate-preparation.md`.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.RotationCertificate.TreeEqualityMachine

inductive LocalStack
  | source | target
  deriving DecidableEq

instance : Fintype LocalStack where
  elems := {.source, .target}
  complete slot := by cases slot <;> decide

inductive Phase
  | compare
  deriving DecidableEq

instance : Fintype Phase where
  elems := {.compare}
  complete phase := by cases phase; decide

inductive Result
  | equal | different
  deriving DecidableEq

instance : Fintype Result where
  elems := {.equal, .different}
  complete result := by cases result <;> decide

abbrev StackId (K : Type) := LocalStack ⊕ K
abbrev External (Λ : Type) := Result ⊕ Λ
abbrev Label (Λ : Type) := Phase ⊕ External Λ
abbrev Temporaries := Option Tag × Option Unit
abbrev Registers (R : Type) := Temporaries × R

variable {K Λ R : Type} {Γ : K → Type}

abbrev alphabet (Γ : K → Type) : StackId K → Type
  | .inl _ => Tag
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

theorem card_temporaries : Fintype.card Temporaries = 34 := by simp [Temporaries, Tag]

theorem card_stackId [Fintype K] : Fintype.card (StackId K) = 2 + Fintype.card K := by
  rw [Fintype.card_sum]
  rfl

theorem card_label [Fintype Λ] : Fintype.card (Label Λ) = 3 + Fintype.card Λ := by
  have phases : Fintype.card Phase = 1 := rfl
  have results : Fintype.card Result = 2 := rfl
  simp only [Fintype.card_sum, phases, results]
  omega

theorem card_registers [Fintype R] : Fintype.card (Registers R) = 34 * Fintype.card R := by
  rw [Fintype.card_prod, card_temporaries]

def reset (regs : Registers R) : Registers R := ((none, none), regs.2)

@[simp] theorem reset_reset (regs : Registers R) : reset (reset regs) = reset regs := rfl

def storeTag (regs : Registers R) (tag : Option Tag) : Registers R :=
  ((tag, regs.1.2), regs.2)

def storeMatch (regs : Registers R) (tag : Option Tag) : Registers R :=
  ((regs.1.1, if tag = regs.1.1 then some () else none), regs.2)

def jump (label : Label Λ) : Statement Γ Λ R :=
  .load reset (.goto (fun _ => label))

/-- Both pops and both tests are in this one finite statement. -/
def block : Phase → Statement Γ Λ R
  | .compare =>
      .pop (.inl .source) storeTag
        (.pop (.inl .target) storeMatch
          (.branch (fun regs => regs.1.2.isSome)
            (.branch (fun regs => regs.1.1.isNone)
              (jump (resultLabel .equal)) (jump (phaseLabel .compare)))
            (jump (resultLabel .different))))

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

def cfg (label : Option (Label Λ)) (regs : Registers R) (source target : Word)
    (ctx : ∀ k, List (Γ k)) : Cfg Γ Λ R where
  l := label
  var := regs
  stk
    | .inl .source => source
    | .inl .target => target
    | .inr k => ctx k

theorem cfg_ext {left right : Cfg Γ Λ R}
    (label : left.l = right.l) (regs : left.var = right.var)
    (source : left.stk (.inl .source) = right.stk (.inl .source))
    (target : left.stk (.inl .target) = right.stk (.inl .target))
    (ctx : ∀ k, left.stk (.inr k) = right.stk (.inr k)) : left = right := by
  have stackEq : left.stk = right.stk := by
    funext k
    cases k with
    | inl slot => cases slot with
      | source => exact source
      | target => exact target
    | inr k => exact ctx k
  cases left
  cases right
  cases label
  cases regs
  cases stackEq
  rfl

theorem cfg_eta (c : Cfg Γ Λ R) :
    cfg c.l c.var (c.stk (.inl .source)) (c.stk (.inl .target))
      (fun k => c.stk (.inr k)) = c := by
  apply cfg_ext <;> first | rfl | exact fun _ => rfl

/-- Exact proof-side count; no count or list recursion occurs in `block`. -/
def runSteps : Word → Word → Nat
  | [], _ => 1
  | _ :: _, [] => 1
  | a :: xs, b :: ys => if a = b then runSteps xs ys + 1 else 1

theorem runSteps_pos (xs ys : Word) : 0 < runSteps xs ys := by
  cases xs with
  | nil => exact Nat.zero_lt_one
  | cons a xs => cases ys with
    | nil => exact Nat.zero_lt_one
    | cons b ys => simp only [runSteps]; split <;> omega

theorem runSteps_le (xs ys : Word) :
    runSteps xs ys ≤ min xs.length ys.length + 1 := by
  induction xs generalizing ys with
  | nil => simp [runSteps]
  | cons a xs ih => cases ys with
    | nil => simp [runSteps]
    | cons b ys =>
        have previous := ih ys
        simp only [runSteps, List.length_cons]
        split <;> omega

@[simp] theorem runSteps_self (xs : Word) : runSteps xs xs = xs.length + 1 := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [runSteps, ih]

theorem runSteps_common_prefix (common xs ys : Word) :
    runSteps (common ++ xs) (common ++ ys) = common.length + runSteps xs ys := by
  induction common with
  | nil => simp
  | cons a common ih => simp [runSteps, ih, Nat.add_assoc, Nat.add_comm]

theorem runSteps_head_mismatch (xs ys : Word) (different : xs.head? ≠ ys.head?) :
    runSteps xs ys = 1 := by
  cases xs with
  | nil => rfl
  | cons a xs => cases ys with
    | nil => rfl
    | cons b ys =>
        have ne : a ≠ b := by intro same; apply different; simp [same]
        simp [runSteps, ne]

def wordResult (xs ys : Word) : Result := if xs = ys then .equal else .different

@[simp] theorem wordResult_equal_iff (xs ys : Word) : wordResult xs ys = .equal ↔ xs = ys := by
  by_cases same : xs = ys <;> simp [wordResult, same]

@[simp] theorem wordResult_different_iff (xs ys : Word) :
    wordResult xs ys = .different ↔ xs ≠ ys := by
  by_cases same : xs = ys <;> simp [wordResult, same]

@[simp] theorem wordResult_cons (a : Tag) (xs ys : Word) :
    wordResult (a :: xs) (a :: ys) = wordResult xs ys := by simp [wordResult]

def prefixRegisters (n : Nat) (regs : Registers R) : Registers R :=
  if n = 0 then regs else reset regs

@[simp] theorem prefixRegisters_zero (regs : Registers R) : prefixRegisters 0 regs = regs := rfl
@[simp] theorem prefixRegisters_succ (n : Nat) (regs : Registers R) :
    prefixRegisters (n + 1) regs = reset regs := by simp [prefixRegisters]
@[simp] theorem prefixRegisters_reset (n : Nat) (regs : Registers R) :
    prefixRegisters n (reset regs) = reset regs := by simp [prefixRegisters]

def resultCfg (xs ys : Word) (regs : Registers R) (ctx : ∀ k, List (Γ k)) : Cfg Γ Λ R :=
  cfg (some (resultLabel (wordResult xs ys))) (reset regs)
    (xs.drop (runSteps xs ys)) (ys.drop (runSteps xs ys)) ctx

def prefixCfg (xs ys : Word) (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (n : Nat) : Cfg Γ Λ R :=
  cfg (some (if n < runSteps xs ys then phaseLabel .compare else resultLabel (wordResult xs ys)))
    (prefixRegisters n regs) (xs.drop n) (ys.drop n) ctx

@[simp] theorem prefixCfg_zero (xs ys : Word) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    prefixCfg (Λ := Λ) xs ys regs ctx 0 = cfg (some (phaseLabel .compare)) regs xs ys ctx := by
  simp [prefixCfg, runSteps_pos]

theorem prefixCfg_end (xs ys : Word) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    prefixCfg (Λ := Λ) xs ys regs ctx (runSteps xs ys) = resultCfg xs ys regs ctx := by
  simp [prefixCfg, resultCfg, prefixRegisters, Nat.ne_of_gt (runSteps_pos xs ys)]

theorem prefixCfg_cons_succ (a : Tag) (xs ys : Word) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (n : Nat) :
    prefixCfg (Λ := Λ) (a :: xs) (a :: ys) regs ctx (n + 1) =
      prefixCfg xs ys (reset regs) ctx n := by
  simp [prefixCfg, runSteps]

variable [DecidableEq K]

def step (caller : External Λ → Statement Γ Λ R) : Cfg Γ Λ R → Option (Cfg Γ Λ R) :=
  Turing.TM2.step (program caller)

def next (caller : External Λ → Statement Γ Λ R) (c : Option (Cfg Γ Λ R)) :
    Option (Cfg Γ Λ R) := c.bind (step caller)

variable (caller : External Λ → Statement Γ Λ R)

@[simp] theorem next_none : next caller none = none := rfl
@[simp] theorem next_some (c : Cfg Γ Λ R) : next caller (some c) = step caller c := rfl

theorem iterate_step (n : Nat) (c d : Cfg Γ Λ R) (transition : step caller c = some d) :
    (next caller)^[n + 1] (some c) = (next caller)^[n] (some d) := by
  rw [Function.iterate_succ_apply, next_some, transition]

theorem compare_step_nil_nil (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel .compare)) regs [] [] ctx) =
      some (cfg (some (resultLabel .equal)) (reset regs) [] [] ctx) := by
  apply congrArg some
  apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem compare_step_nil_cons (b : Tag) (ys : Word) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel .compare)) regs [] (b :: ys) ctx) =
      some (cfg (some (resultLabel .different)) (reset regs) [] ys ctx) := by
  apply congrArg some
  apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem compare_step_cons_nil (a : Tag) (xs : Word) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel .compare)) regs (a :: xs) [] ctx) =
      some (cfg (some (resultLabel .different)) (reset regs) xs [] ctx) := by
  apply congrArg some
  apply cfg_ext <;> first | rfl | exact fun _ => rfl

theorem compare_step_same (a : Tag) (xs ys : Word) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    step caller (cfg (some (phaseLabel .compare)) regs (a :: xs) (a :: ys) ctx) =
      some (cfg (some (phaseLabel .compare)) (reset regs) xs ys ctx) := by
  simp [step, Turing.TM2.step, program, phaseLabel, block, Turing.TM2.stepAux,
    cfg, storeTag, storeMatch, jump, reset]
  funext k
  cases k with
  | inl slot => cases slot <;> simp
  | inr k => simp

theorem compare_step_different (a b : Tag) (xs ys : Word) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (different : a ≠ b) :
    step caller (cfg (some (phaseLabel .compare)) regs (a :: xs) (b :: ys) ctx) =
      some (cfg (some (resultLabel .different)) (reset regs) xs ys ctx) := by
  simp [step, Turing.TM2.step, program, phaseLabel, block, Turing.TM2.stepAux,
    cfg, storeTag, storeMatch, jump, reset, Ne.symm different]
  funext k
  cases k with
  | inl slot => cases slot <;> simp
  | inr k => simp

/-- All inclusive prefixes are literal physical configurations. -/
theorem prefix_exact (xs ys : Word) (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (n : Nat) (bound : n ≤ runSteps xs ys) :
    (next caller)^[n] (some (cfg (some (phaseLabel .compare)) regs xs ys ctx)) =
      some (prefixCfg xs ys regs ctx n) := by
  induction xs generalizing ys regs n with
  | nil =>
      have small : n ≤ 1 := bound
      have casesN : n = 0 ∨ n = 1 := by omega
      rcases casesN with rfl | rfl
      · simp
      · cases ys with
        | nil => simpa [prefixCfg, runSteps, wordResult] using compare_step_nil_nil caller regs ctx
        | cons b ys =>
            simpa [prefixCfg, runSteps, wordResult] using compare_step_nil_cons caller b ys regs ctx
  | cons a xs ih =>
      cases ys with
      | nil =>
          have small : n ≤ 1 := bound
          have casesN : n = 0 ∨ n = 1 := by omega
          rcases casesN with rfl | rfl
          · simp
          · simpa [prefixCfg, runSteps, wordResult] using compare_step_cons_nil caller a xs regs ctx
      | cons b ys =>
          by_cases same : a = b
          · subst b
            cases n with
            | zero => simp
            | succ n =>
                have shorter : n ≤ runSteps xs ys := by
                  simpa [runSteps] using bound
                rw [iterate_step caller n _ _ (compare_step_same caller a xs ys regs ctx)]
                rw [ih ys (reset regs) n shorter, prefixCfg_cons_succ]
          · have small : n ≤ 1 := by simpa [runSteps, same] using bound
            have casesN : n = 0 ∨ n = 1 := by omega
            rcases casesN with rfl | rfl
            · simp
            · simpa [prefixCfg, runSteps, wordResult, same] using
                compare_step_different caller a b xs ys regs ctx same

/-- Unconditional endpoint for arbitrary raw words, stale temporaries and callers. -/
theorem run (xs ys : Word) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (next caller)^[runSteps xs ys]
        (some (cfg (some (phaseLabel .compare)) regs xs ys ctx)) =
      some (resultCfg xs ys regs ctx) := by
  rw [← prefixCfg_end]
  exact prefix_exact caller xs ys regs ctx _ (Nat.le_refl _)

theorem run_equal (xs : Word) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (next caller)^[xs.length + 1]
      (some (cfg (some (phaseLabel .compare)) regs xs xs ctx)) =
    some (cfg (some (resultLabel .equal)) (reset regs) [] [] ctx) := by
  have empty : xs.drop (xs.length + 1) = [] := List.drop_eq_nil_of_le (Nat.le_succ _)
  simpa [resultCfg, wordResult, empty] using run caller xs xs regs ctx

theorem run_different (xs ys : Word) (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (different : xs ≠ ys) :
    (next caller)^[runSteps xs ys]
      (some (cfg (some (phaseLabel .compare)) regs xs ys ctx)) =
    some (cfg (some (resultLabel .different)) (reset regs)
      (xs.drop (runSteps xs ys)) (ys.drop (runSteps xs ys)) ctx) := by
  simpa [resultCfg, wordResult, different] using run caller xs ys regs ctx

theorem common_prefix (common xs ys : Word) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    (next caller)^[common.length]
        (some (cfg (some (phaseLabel .compare)) regs (common ++ xs) (common ++ ys) ctx)) =
      some (cfg (some (phaseLabel .compare)) (prefixRegisters common.length regs) xs ys ctx) := by
  have strict : common.length < runSteps (common ++ xs) (common ++ ys) := by
    rw [runSteps_common_prefix]
    have positive := runSteps_pos xs ys
    omega
  simpa [prefixCfg, strict] using
    prefix_exact caller (common ++ xs) (common ++ ys) regs ctx common.length (Nat.le_of_lt strict)

theorem common_prefix_mismatch (common xs ys : Word) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (different : xs.head? ≠ ys.head?) :
    (next caller)^[common.length + 1]
        (some (cfg (some (phaseLabel .compare)) regs (common ++ xs) (common ++ ys) ctx)) =
      some (cfg (some (resultLabel .different)) (reset regs) xs.tail ys.tail ctx) := by
  have ne : xs ≠ ys := by intro same; apply different; rw [same]
  have count : runSteps (common ++ xs) (common ++ ys) = common.length + 1 := by
    rw [runSteps_common_prefix, runSteps_head_mismatch xs ys different]
  have executed := run caller (common ++ xs) (common ++ ys) regs ctx
  rw [count] at executed
  simpa [resultCfg, count, wordResult, ne, List.drop_add_one_eq_tail_drop] using executed

def runInTimeExact (xs ys : Word) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller)
      (cfg (some (phaseLabel .compare)) regs xs ys ctx)
      (some (resultCfg xs ys regs ctx)) (runSteps xs ys) where
  steps := runSteps xs ys
  evals_in_steps := run caller xs ys regs ctx
  steps_le_m := Nat.le_refl _

def runInLinearTime (xs ys : Word) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller)
      (cfg (some (phaseLabel .compare)) regs xs ys ctx)
      (some (resultCfg xs ys regs ctx)) (min xs.length ys.length + 1) where
  steps := runSteps xs ys
  evals_in_steps := run caller xs ys regs ctx
  steps_le_m := runSteps_le xs ys

/-- Results and all extra caller labels are disjoint from the single owned phase. -/
def Owned : Option (Label Λ) → Prop
  | some (.inl _) => True
  | _ => False

abbrev OwnedLabel (Λ : Type) := {label : Label Λ // Owned (some label)}

omit [DecidableEq K] in
/-- The owned label set is finite constructively, even for an infinite caller label type. -/
def ownedLabelEquiv : OwnedLabel Λ ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨phaseLabel .compare, trivial⟩
  left_inv label := by
    rcases label with ⟨label, owned⟩
    cases label with
    | inl phase => cases phase; rfl
    | inr external => exact False.elim owned
  right_inv value := by cases value; rfl

omit [DecidableEq K] in
instance ownedLabelFintype : Fintype (OwnedLabel Λ) :=
  Fintype.ofEquiv Unit ownedLabelEquiv.symm

omit [DecidableEq K] in
theorem card_ownedLabel : Fintype.card (OwnedLabel Λ) = 1 := by
  rw [Fintype.card_congr ownedLabelEquiv]
  rfl

def remainingSteps (c : Cfg Γ Λ R) : Nat :=
  match c.l with
  | some (.inl _) => runSteps (c.stk (.inl .source)) (c.stk (.inl .target))
  | _ => 0

omit [DecidableEq K] in
theorem remainingSteps_pos_iff (c : Cfg Γ Λ R) : 0 < remainingSteps c ↔ Owned c.l := by
  cases labelEq : c.l with
  | none => simp [remainingSteps, Owned, labelEq]
  | some label => cases label with
    | inr external => simp [remainingSteps, Owned, labelEq]
    | inl phase => simp [remainingSteps, Owned, labelEq, runSteps_pos]

omit [DecidableEq K] in
theorem owned_cases (c : Cfg Γ Λ R) (owned : Owned c.l) :
    ∃ regs xs ys ctx, c = cfg (some (phaseLabel .compare)) regs xs ys ctx := by
  cases labelEq : c.l with
  | none => simp [Owned, labelEq] at owned
  | some label => cases label with
    | inr external => simp [Owned, labelEq] at owned
    | inl phase =>
        cases phase
        refine ⟨c.var, c.stk (.inl .source), c.stk (.inl .target),
          (fun k => c.stk (.inr k)), ?_⟩
        simpa only [labelEq, phaseLabel] using (cfg_eta c).symm

theorem compare_step_data (xs ys : Word) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    ∃ reached,
      step caller (cfg (some (phaseLabel .compare)) regs xs ys ctx) = some reached ∧
      runSteps xs ys = remainingSteps reached + 1 ∧
      reached.var = reset regs ∧
      reached.stk (.inl .source) = xs.tail ∧ reached.stk (.inl .target) = ys.tail ∧
      ∀ k, reached.stk (.inr k) = ctx k := by
  cases xs with
  | nil => cases ys with
    | nil =>
        exact ⟨_, compare_step_nil_nil caller regs ctx, rfl, rfl, rfl, rfl, fun _ => rfl⟩
    | cons b ys =>
        exact ⟨_, compare_step_nil_cons caller b ys regs ctx, rfl, rfl, rfl, rfl, fun _ => rfl⟩
  | cons a xs => cases ys with
    | nil =>
        exact ⟨_, compare_step_cons_nil caller a xs regs ctx, rfl, rfl, rfl, rfl, fun _ => rfl⟩
    | cons b ys =>
        by_cases same : a = b
        · subst b
          refine ⟨_, compare_step_same caller a xs ys regs ctx, ?_, rfl, rfl, rfl, fun _ => rfl⟩
          simp [runSteps, remainingSteps, cfg, phaseLabel]
        · refine ⟨_, compare_step_different caller a b xs ys regs ctx same,
            ?_, rfl, rfl, rfl, fun _ => rfl⟩
          simp [runSteps, same, remainingSteps, cfg, resultLabel]

def LocalStep (before after : Cfg Γ Λ R) : Prop :=
  Owned before.l ∧ step caller before = some after

theorem local_step_data {before after : Cfg Γ Λ R} (transition : LocalStep caller before after) :
    remainingSteps before = remainingSteps after + 1 ∧
    after.var = reset before.var ∧
    after.stk (.inl .source) = (before.stk (.inl .source)).tail ∧
    after.stk (.inl .target) = (before.stk (.inl .target)).tail ∧
    ∀ k, after.stk (.inr k) = before.stk (.inr k) := by
  obtain ⟨regs, xs, ys, ctx, rfl⟩ := owned_cases before transition.1
  obtain ⟨reached, executed, rank, registers, source, target, frame⟩ :=
    compare_step_data caller xs ys regs ctx
  have equal : reached = after := Option.some.inj (executed.symm.trans transition.2)
  subst after
  exact ⟨rank, registers, source, target, frame⟩

theorem local_step_remaining {before after : Cfg Γ Λ R}
    (transition : LocalStep caller before after) :
    remainingSteps before = remainingSteps after + 1 := (local_step_data caller transition).1

theorem local_progress (before : Cfg Γ Λ R) (positive : 0 < remainingSteps before) :
    ∃ after, step caller before = some after ∧ remainingSteps before = remainingSteps after + 1 := by
  obtain ⟨regs, xs, ys, ctx, rfl⟩ := owned_cases before ((remainingSteps_pos_iff before).mp positive)
  obtain ⟨after, executed, rank, _⟩ := compare_step_data caller xs ys regs ctx
  exact ⟨after, executed, rank⟩

theorem step_caller_independent (other : External Λ → Statement Γ Λ R)
    (c : Cfg Γ Λ R) (owned : Owned c.l) : step caller c = step other c := by
  obtain ⟨regs, xs, ys, ctx, rfl⟩ := owned_cases c owned
  rfl

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

theorem first_return (xs ys : Word) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (next caller)^[runSteps xs ys]
        (some (cfg (some (phaseLabel .compare)) regs xs ys ctx)) = some (resultCfg xs ys regs ctx) ∧
      ¬ Owned (resultCfg (Λ := Λ) xs ys regs ctx).l ∧
      ∀ n, n < runSteps xs ys → Owned (prefixCfg (Λ := Λ) xs ys regs ctx n).l := by
  refine ⟨run caller xs ys regs ctx, ?_, ?_⟩
  · simp [resultCfg, cfg, resultLabel, Owned]
  · intro n strict
    simp [prefixCfg, cfg, strict, phaseLabel, Owned]

theorem first_return_exact (xs ys : Word) (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (n : Nat) (reached : Cfg Γ Λ R) (bound : n ≤ runSteps xs ys)
    (executed : (next caller)^[n]
      (some (cfg (some (phaseLabel .compare)) regs xs ys ctx)) = some reached)
    (external : ¬ Owned reached.l) : n = runSteps xs ys := by
  have actual := prefix_exact caller xs ys regs ctx n bound
  have same : reached = prefixCfg xs ys regs ctx n := Option.some.inj (executed.symm.trans actual)
  subst reached
  by_contra ne
  have strict : n < runSteps xs ys := by omega
  exact external ((first_return caller xs ys regs ctx).2.2 n strict)

/-- A first external return is unique, even when the caller later loops or fabricates a result. -/
theorem first_return_unique (xs ys : Word) (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (n : Nat) (reached : Cfg Γ Λ R)
    (executed : (next caller)^[n]
      (some (cfg (some (phaseLabel .compare)) regs xs ys ctx)) = some reached)
    (external : ¬ Owned reached.l)
    (earlier : ∀ k, k < n → ∃ before,
      (next caller)^[k] (some (cfg (some (phaseLabel .compare)) regs xs ys ctx)) = some before ∧
        Owned before.l) :
    n = runSteps xs ys ∧ reached = resultCfg xs ys regs ctx := by
  have bound : n ≤ runSteps xs ys := by
    by_contra bad
    have strict : runSteps xs ys < n := by omega
    obtain ⟨before, arrived, owned⟩ := earlier (runSteps xs ys) strict
    have same : before = resultCfg xs ys regs ctx :=
      Option.some.inj (arrived.symm.trans (run caller xs ys regs ctx))
    rw [same] at owned
    exact (first_return caller xs ys regs ctx).2.1 owned
  have exactCount := first_return_exact caller xs ys regs ctx n reached bound executed external
  refine ⟨exactCount, ?_⟩
  rw [exactCount] at executed
  exact Option.some.inj (executed.symm.trans (run caller xs ys regs ctx))

theorem ambient_run (ambient : Label Λ → Statement Γ Λ R)
    (agrees : ∀ phase, ambient (phaseLabel phase) = block phase)
    (xs ys : Word) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (fun c : Option (Cfg Γ Λ R) => c.bind (Turing.TM2.step ambient))^[runSteps xs ys]
      (some (cfg (some (phaseLabel .compare)) regs xs ys ctx)) = some (resultCfg xs ys regs ctx) := by
  rw [program_eq_of_agrees ambient agrees]
  exact run _ xs ys regs ctx

theorem local_reaches_frame {start reached : Cfg Γ Λ R}
    (path : Relation.ReflTransGen (LocalStep caller) start reached) :
    reached.var.2 = start.var.2 ∧ ∀ k, reached.stk (.inr k) = start.stk (.inr k) := by
  induction path with
  | refl => exact ⟨rfl, fun _ => rfl⟩
  | @tail before after _ transition ih =>
      obtain ⟨_, registers, _, _, frame⟩ := local_step_data caller transition
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

theorem prefix_reset (xs ys : Word) (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (n : Nat) (reached : Cfg Γ Λ R) (positive : 0 < n) (bound : n ≤ runSteps xs ys)
    (executed : (next caller)^[n]
      (some (cfg (some (phaseLabel .compare)) regs xs ys ctx)) = some reached) :
    reached.var = reset regs := by
  have same : reached = prefixCfg xs ys regs ctx n :=
    Option.some.inj (executed.symm.trans (prefix_exact caller xs ys regs ctx n bound))
  rw [same]
  simp [prefixCfg, cfg, prefixRegisters, Nat.ne_of_gt positive]

def ownedCells (c : Cfg Γ Λ R) : Nat :=
  (c.stk (.inl .source)).length + (c.stk (.inl .target)).length

theorem local_step_ownedCells_le {before after : Cfg Γ Λ R}
    (transition : LocalStep caller before after) : ownedCells after ≤ ownedCells before := by
  obtain ⟨_, _, source, target, _⟩ := local_step_data caller transition
  simp only [ownedCells, source, target, List.length_tail]
  omega

variable [Fintype K]

def contextCells (ctx : ∀ k, List (Γ k)) : Nat := ∑ k, (ctx k).length

def stackCells (c : Cfg Γ Λ R) : Nat := ownedCells c + contextCells (fun k => c.stk (.inr k))

theorem localStack_sum (f : LocalStack → Nat) :
    ∑ k, f k = f .source + f .target := by
  change (∑ k ∈ ({.source, .target} : Finset LocalStack), f k) = _
  simp

omit [DecidableEq K] in
theorem stackCells_eq_sum (c : Cfg Γ Λ R) :
    stackCells c = ∑ k : StackId K, (c.stk k).length := by
  rw [Fintype.sum_sum_type, localStack_sum]
  rfl

omit [DecidableEq K] in
theorem stackCells_cfg (label : Option (Label Λ)) (regs : Registers R)
    (xs ys : Word) (ctx : ∀ k, List (Γ k)) :
    stackCells (cfg label regs xs ys ctx) = xs.length + ys.length + contextCells ctx := rfl

theorem local_step_preserves {before after : Cfg Γ Λ R}
    (transition : LocalStep caller before after) :
    after.var.2 = before.var.2 ∧ (∀ k, after.stk (.inr k) = before.stk (.inr k)) ∧
      stackCells after ≤ stackCells before := by
  obtain ⟨_, registers, _, _, frame⟩ := local_step_data caller transition
  refine ⟨?_, frame, ?_⟩
  · rw [registers]; rfl
  · simp only [stackCells, contextCells, frame]
    exact Nat.add_le_add_right (local_step_ownedCells_le caller transition) _

theorem local_reaches_preserves {start reached : Cfg Γ Λ R}
    (path : Relation.ReflTransGen (LocalStep caller) start reached) :
    reached.var.2 = start.var.2 ∧ (∀ k, reached.stk (.inr k) = start.stk (.inr k)) ∧
      stackCells reached ≤ stackCells start := by
  induction path with
  | refl => exact ⟨rfl, fun _ => rfl, Nat.le_refl _⟩
  | @tail before after _ transition ih =>
      obtain ⟨registers, frame, cells⟩ := local_step_preserves caller transition
      exact ⟨registers.trans ih.1, fun k => (frame k).trans (ih.2.1 k), cells.trans ih.2.2⟩

/-- Exact physical space at every inclusive common, with natural subtraction. -/
theorem prefix_stackCells (xs ys : Word) (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (n : Nat) (reached : Cfg Γ Λ R) (bound : n ≤ runSteps xs ys)
    (executed : (next caller)^[n]
      (some (cfg (some (phaseLabel .compare)) regs xs ys ctx)) = some reached) :
    stackCells reached = (xs.length - n) + (ys.length - n) + contextCells ctx := by
  have same : reached = prefixCfg xs ys regs ctx n :=
    Option.some.inj (executed.symm.trans (prefix_exact caller xs ys regs ctx n bound))
  rw [same]
  simp [prefixCfg, stackCells_cfg]

theorem prefix_stackCells_le (xs ys : Word) (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (n : Nat) (reached : Cfg Γ Λ R) (bound : n ≤ runSteps xs ys)
    (executed : (next caller)^[n]
      (some (cfg (some (phaseLabel .compare)) regs xs ys ctx)) = some reached) :
    stackCells reached ≤ xs.length + ys.length + contextCells ctx := by
  rw [prefix_stackCells caller xs ys regs ctx n reached bound executed]
  omega

theorem self_prefix_stackCells (xs : Word) (regs : Registers R) (ctx : ∀ k, List (Γ k))
    (n : Nat) (reached : Cfg Γ Λ R) (bound : n ≤ xs.length + 1)
    (executed : (next caller)^[n]
      (some (cfg (some (phaseLabel .compare)) regs xs xs ctx)) = some reached) :
    stackCells reached = 2 * (xs.length - n) + contextCells ctx := by
  have exactCells := prefix_stackCells caller xs xs regs ctx n reached
    (by simpa only [runSteps_self] using bound) executed
  omega

omit [DecidableEq K] in
theorem initial_space_sharp (xs ys : Word) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    stackCells (cfg (some (phaseLabel (Λ := Λ) .compare)) regs xs ys ctx) =
      xs.length + ys.length + contextCells ctx := rfl

omit [DecidableEq K] [Fintype K] in
theorem treeCode_injective : Function.Injective treeCode := by
  intro s t encoded
  exact (parseTreeRun_prefix_injective s t [] [] (by simpa using encoded)).1

omit [DecidableEq K] [Fintype K] in
theorem wordResult_code_equal_iff (s t : BinaryTree Unit) :
    wordResult (treeCode s) (treeCode t) = .equal ↔ s = t := by
  rw [wordResult_equal_iff]
  exact treeCode_injective.eq_iff

omit [DecidableEq K] [Fintype K] in
theorem wordResult_code_different_iff (s t : BinaryTree Unit) :
    wordResult (treeCode s) (treeCode t) = .different ↔ s ≠ t := by
  rw [wordResult_different_iff]
  exact not_congr treeCode_injective.eq_iff

omit [DecidableEq K] [Fintype K] in
theorem result_code_source (s t : BinaryTree Unit) :
    decide (wordResult (treeCode s) (treeCode t) = .equal) = (eqTreeRun s t).1 := by
  simp only [wordResult_code_equal_iff, eqTreeRun_value]

omit [DecidableEq K] [Fintype K] in
theorem runSteps_code_le (s t : BinaryTree Unit) :
    runSteps (treeCode s) (treeCode t) ≤ 2 * min s.numNodes t.numNodes + 2 := by
  have bound := runSteps_le (treeCode s) (treeCode t)
  simp only [treeCode_length] at bound
  omega

omit [DecidableEq K] [Fintype K] in
theorem runSteps_code_source_le (s t : BinaryTree Unit) :
    runSteps (treeCode s) (treeCode t) ≤ 2 * s.numNodes + 2 := by
  have bound := runSteps_code_le s t
  omega

omit [DecidableEq K] [Fintype K] in
theorem runSteps_code_target_le (s t : BinaryTree Unit) :
    runSteps (treeCode s) (treeCode t) ≤ 2 * t.numNodes + 2 := by
  have bound := runSteps_code_le s t
  omega

omit [DecidableEq K] [Fintype K] in
theorem runSteps_code_self (t : BinaryTree Unit) :
    runSteps (treeCode t) (treeCode t) = 2 * t.numNodes + 2 := by simp

omit [DecidableEq K] [Fintype K] in
/-- Source event work and actual finite-machine time remain different measures. -/
theorem self_source_and_machine_counts (t : BinaryTree Unit) :
    (eqTreeRun t t).2 = 3 * t.numNodes + 2 ∧
      runSteps (treeCode t) (treeCode t) = 2 * t.numNodes + 2 :=
  ⟨eqTreeRun_self_cost t, runSteps_code_self t⟩

omit [Fintype K] in
def FirstResult (result : Result) (xs ys : Word) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) : Prop :=
  (next caller)^[runSteps xs ys]
      (some (cfg (some (phaseLabel .compare)) regs xs ys ctx)) =
    some (cfg (some (resultLabel result)) (reset regs)
      (xs.drop (runSteps xs ys)) (ys.drop (runSteps xs ys)) ctx)

omit [Fintype K] in
theorem firstResult_iff (result : Result) (xs ys : Word) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    FirstResult caller result xs ys regs ctx ↔ wordResult xs ys = result := by
  rw [FirstResult, run]
  constructor
  · intro same
    have labels := congrArg (fun c : Cfg Γ Λ R => c.l) (Option.some.inj same)
    simpa [resultCfg, cfg, resultLabel] using labels
  · intro same
    simp only [resultCfg, same]

omit [Fintype K] in
theorem firstEqual_code_iff (s t : BinaryTree Unit) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    FirstResult caller .equal (treeCode s) (treeCode t) regs ctx ↔ s = t := by
  rw [firstResult_iff, wordResult_code_equal_iff]

omit [Fintype K] in
theorem firstDifferent_code_iff (s t : BinaryTree Unit) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    FirstResult caller .different (treeCode s) (treeCode t) regs ctx ↔ s ≠ t := by
  rw [firstResult_iff, wordResult_code_different_iff]

omit [Fintype K] in
theorem run_code_equal (t : BinaryTree Unit) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    (next caller)^[2 * t.numNodes + 2]
      (some (cfg (some (phaseLabel .compare)) regs (treeCode t) (treeCode t) ctx)) =
    some (cfg (some (resultLabel .equal)) (reset regs) [] [] ctx) := by
  simpa only [treeCode_length, Nat.add_assoc] using run_equal caller (treeCode t) regs ctx

omit [Fintype K] in
theorem run_code_different (s t : BinaryTree Unit) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) (different : s ≠ t) :
    (next caller)^[runSteps (treeCode s) (treeCode t)]
      (some (cfg (some (phaseLabel .compare)) regs (treeCode s) (treeCode t) ctx)) =
    some (cfg (some (resultLabel .different)) (reset regs)
      ((treeCode s).drop (runSteps (treeCode s) (treeCode t)))
      ((treeCode t).drop (runSteps (treeCode s) (treeCode t))) ctx) :=
  run_different caller _ _ regs ctx (fun same => different (treeCode_injective same))

omit [Fintype K] in
def treeInTime (s t : BinaryTree Unit) (regs : Registers R) (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (step caller)
      (cfg (some (phaseLabel .compare)) regs (treeCode s) (treeCode t) ctx)
      (some (resultCfg (treeCode s) (treeCode t) regs ctx))
      (2 * min s.numNodes t.numNodes + 2) where
  steps := runSteps (treeCode s) (treeCode t)
  evals_in_steps := run caller (treeCode s) (treeCode t) regs ctx
  steps_le_m := runSteps_code_le s t

variable [Fintype Λ] [Fintype R] [∀ k, Fintype (Γ k)]

/-- The real one-input package uses source as both input and distinguished output.
Its live result is a label; no total output-function claim is made here. -/
def machine (initial : R) : Turing.FinTM2 where
  K := StackId K
  k₀ := .inl .source
  k₁ := .inl .source
  Γ := alphabet Γ
  Λ := Label Λ
  main := phaseLabel .compare
  σ := Registers R
  initialState := ((none, none), initial)
  Γk₀Fin := alphabetFintype (.inl .source)
  m := program caller

theorem machine_step_eq (initial : R) (c : Cfg Γ Λ R) :
    (machine caller initial).step c = step caller c := rfl

/-- `initList` initializes one word only; the target really is empty. -/
theorem initList_eq (initial : R) (raw : Word) :
    Turing.initList (machine caller initial) raw =
      cfg (some (phaseLabel .compare)) ((none, none), initial) raw [] (fun _ => []) := by
  apply cfg_ext <;> first | rfl | exact fun _ => rfl

/-- The same fixed package executes a configuration installed by an earlier real handoff. -/
theorem machine_cfg_run (initial : R) (xs ys : Word) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    (fun c => c.bind (machine caller initial).step)^[runSteps xs ys]
      (some (cfg (some (phaseLabel .compare)) regs xs ys ctx)) = some (resultCfg xs ys regs ctx) :=
  run caller xs ys regs ctx

def machineCfgInTime (initial : R) (xs ys : Word) (regs : Registers R)
    (ctx : ∀ k, List (Γ k)) :
    StateTransition.EvalsToInTime (machine caller initial).step
      (cfg (some (phaseLabel .compare)) regs xs ys ctx)
      (some (resultCfg xs ys regs ctx)) (runSteps xs ys) where
  steps := runSteps xs ys
  evals_in_steps := machine_cfg_run caller initial xs ys regs ctx
  steps_le_m := Nat.le_refl _

theorem machine_init_run (initial : R) (raw : Word) :
    (fun c => c.bind (machine caller initial).step)^[1]
      (some (Turing.initList (machine caller initial) raw)) =
    some (cfg (some (resultLabel (if raw = [] then .equal else .different)))
      ((none, none), initial) raw.tail [] (fun _ => [])) := by
  change next caller (some (Turing.initList (machine caller initial) raw)) = _
  rw [initList_eq, next_some]
  cases raw with
  | nil => exact compare_step_nil_nil caller ((none, none), initial) (fun _ => [])
  | cons a xs => exact compare_step_cons_nil caller a xs ((none, none), initial) (fun _ => [])

def machineInitInTime (initial : R) (raw : Word) :
    StateTransition.EvalsToInTime (machine caller initial).step
      (Turing.initList (machine caller initial) raw)
      (some (cfg (some (resultLabel (if raw = [] then .equal else .different)))
        ((none, none), initial) raw.tail [] (fun _ => []))) 1 where
  steps := 1
  evals_in_steps := machine_init_run caller initial raw
  steps_le_m := Nat.le_refl _

end Resources.RotationCertificate.TreeEqualityMachine
