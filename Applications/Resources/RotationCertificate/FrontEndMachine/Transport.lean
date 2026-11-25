import Applications.Resources.BinaryCounter.FixedWidthMachine
import Mathlib.Logic.Equiv.List
import Applications.Resources.RotationCertificate.InputParserMachine
import Applications.Resources.RotationCertificate.OpenFramingMachine
import Applications.Resources.RotationCertificate.OpenDecoderMachine

/-!
# Finite open front end for framed binary rotation-certificate data

The installed finite program frames the raw bit list, decodes its input field,
parses the complete decoded input, and then decodes the certificate field.
It returns at a live rejection or decoded-certificate dispatch label. Complete
physical configuration maps connect the actual components without a runtime
conversion, omitted transfer, or skipped empty probe.

The source, exact-time and inclusive-prefix contracts describe this syntactic
front end. Fuel inspection, move parsing, rotations, equality, final Boolean
cleanup and the quantitative computational-model/NP bridge remain separate
obligations in the full rotation-certificate programme.
Correspondence: `docs/research/fdsa-rotation-certificate-preparation.md`.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.RotationCertificate.FrontEndMachine.Transport

variable {K K' Λ Λ' R R' : Type} {Γ : K → Type} {Γ' : K' → Type}
variable (names : K ≃ K') (symbols : ∀ k, Γ k ≃ Γ' (names k))
  (registers : R ≃ R') (labels : Λ → Λ')

def stackEquiv : (∀ k, List (Γ k)) ≃ (∀ j, List (Γ' j)) :=
  names.piCongr (fun k => Equiv.listEquivOfEquiv (symbols k))

@[simp] theorem stackEquiv_apply (data : ∀ k, List (Γ k)) (k : K) :
    stackEquiv names symbols data (names k) = (data k).map (symbols k) := by
  exact Equiv.piCongr_apply_apply (W := fun k => List (Γ k)) (Z := fun j => List (Γ' j))
    names (fun k => Equiv.listEquivOfEquiv (symbols k)) data k

def cfg (c : Turing.TM2.Cfg Γ Λ R) : Turing.TM2.Cfg Γ' Λ' R' where
  l := c.l.map labels
  var := registers c.var
  stk := stackEquiv names symbols c.stk

theorem cfg_injective (injective : Function.Injective labels) :
    Function.Injective (cfg names symbols registers labels) := by
  intro before after equal
  have labelEq := congrArg Turing.TM2.Cfg.l equal
  have registerEq := congrArg Turing.TM2.Cfg.var equal
  have stackEq := congrArg Turing.TM2.Cfg.stk equal
  have labelEq' := Option.map_injective injective labelEq
  have registerEq' := registers.injective registerEq
  have stackEq' := (stackEquiv names symbols).injective stackEq
  cases before
  cases after
  cases labelEq'
  cases registerEq'
  cases stackEq'
  rfl

/-- Only finite syntax and finite callbacks are translated. -/
def statement : Turing.TM2.Stmt Γ Λ R → Turing.TM2.Stmt Γ' Λ' R'
  | .push k value tail =>
      .push (names k) (fun regs => symbols k (value (registers.symm regs)))
        (statement tail)
  | .peek k store tail =>
      .peek (names k)
        (fun regs value => registers (store (registers.symm regs) (value.map (symbols k).symm)))
        (statement tail)
  | .pop k store tail =>
      .pop (names k)
        (fun regs value => registers (store (registers.symm regs) (value.map (symbols k).symm)))
        (statement tail)
  | .load update tail =>
      .load (fun regs => registers (update (registers.symm regs))) (statement tail)
  | .branch test yes no =>
      .branch (fun regs => test (registers.symm regs)) (statement yes) (statement no)
  | .goto label => .goto (fun regs => labels (label (registers.symm regs)))
  | .halt => .halt

theorem observed_head (k : K) (data : List (Γ k)) :
    ((data.map (symbols k)).head?).map (symbols k).symm = data.head? := by
  cases data <;> simp

theorem mapped_tail (k : K) (data : List (Γ k)) :
    (data.map (symbols k)).tail = data.tail.map (symbols k) := by
  cases data <;> rfl

variable [DecidableEq K] [DecidableEq K']

theorem stackEquiv_update (data : ∀ k, List (Γ k)) (k : K) (value : List (Γ k)) :
    stackEquiv names symbols (Function.update data k value) =
      Function.update (stackEquiv names symbols data) (names k) (value.map (symbols k)) := by
  funext j
  obtain ⟨other, rfl⟩ := names.surjective j
  by_cases equal : other = k
  · subst other
    simp only [stackEquiv_apply, Function.update_self]
  · have different : names other ≠ names k := fun h => equal (names.injective h)
    simp only [stackEquiv_apply, Function.update_of_ne equal, Function.update_of_ne different]

/-- The proof follows each actual primitive in the pinned TM2 evaluator. -/
theorem stepAux (body : Turing.TM2.Stmt Γ Λ R) (regs : R) (data : ∀ k, List (Γ k)) :
    Turing.TM2.stepAux (statement names symbols registers labels body)
        (registers regs) (stackEquiv names symbols data) =
      cfg names symbols registers labels (Turing.TM2.stepAux body regs data) := by
  induction body generalizing regs data with
  | push k value tail ih =>
      simp only [statement, Turing.TM2.stepAux, Equiv.symm_apply_apply, stackEquiv_apply]
      rw [← List.map_cons, ← stackEquiv_update, ih]
  | peek k store tail ih =>
      simp only [statement, Turing.TM2.stepAux, Equiv.symm_apply_apply,
        stackEquiv_apply, observed_head]
      exact ih _ _
  | pop k store tail ih =>
      simp only [statement, Turing.TM2.stepAux, Equiv.symm_apply_apply,
        stackEquiv_apply, observed_head, mapped_tail]
      rw [← stackEquiv_update, ih]
  | load update tail ih =>
      simp only [statement, Turing.TM2.stepAux, Equiv.symm_apply_apply]
      exact ih _ _
  | branch test yes no yesIH noIH =>
      simp only [statement, Turing.TM2.stepAux, Equiv.symm_apply_apply]
      cases test regs <;> first | exact yesIH _ _ | exact noIH _ _
  | goto label => simp [statement, Turing.TM2.stepAux, cfg]
  | halt => rfl

theorem step (source : Λ → Turing.TM2.Stmt Γ Λ R)
    (ambient : Λ' → Turing.TM2.Stmt Γ' Λ' R')
    (installed : ∀ label, ambient (labels label) = statement names symbols registers labels (source label))
    (c : Turing.TM2.Cfg Γ Λ R) :
    Turing.TM2.step ambient (cfg names symbols registers labels c) =
      (Turing.TM2.step source c).map (cfg names symbols registers labels) := by
  rcases c with ⟨label, regs, data⟩
  cases label with
  | none => rfl
  | some label =>
      simp only [cfg, Option.map_some, Turing.TM2.step, installed]
      exact congrArg some (stepAux names symbols registers labels (source label) regs data)

def next (program : Λ → Turing.TM2.Stmt Γ Λ R) :
    Option (Turing.TM2.Cfg Γ Λ R) → Option (Turing.TM2.Cfg Γ Λ R) :=
  fun c => c.bind (Turing.TM2.step program)

theorem next_map (source : Λ → Turing.TM2.Stmt Γ Λ R)
    (ambient : Λ' → Turing.TM2.Stmt Γ' Λ' R')
    (installed : ∀ label, ambient (labels label) = statement names symbols registers labels (source label))
    (c : Option (Turing.TM2.Cfg Γ Λ R)) :
    next ambient (c.map (cfg names symbols registers labels)) =
      (next source c).map (cfg names symbols registers labels) := by
  cases c with
  | none => rfl
  | some c => exact step names symbols registers labels source ambient installed c

theorem iterate (source : Λ → Turing.TM2.Stmt Γ Λ R)
    (ambient : Λ' → Turing.TM2.Stmt Γ' Λ' R')
    (installed : ∀ label, ambient (labels label) = statement names symbols registers labels (source label))
    (n : Nat) (c : Option (Turing.TM2.Cfg Γ Λ R)) :
    (next ambient)^[n] (c.map (cfg names symbols registers labels)) =
      ((next source)^[n] c).map (cfg names symbols registers labels) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
        next_map names symbols registers labels source ambient installed, ih]

def timed (source : Λ → Turing.TM2.Stmt Γ Λ R)
    (ambient : Λ' → Turing.TM2.Stmt Γ' Λ' R')
    (installed : ∀ label, ambient (labels label) = statement names symbols registers labels (source label))
    (start : Turing.TM2.Cfg Γ Λ R) (final : Option (Turing.TM2.Cfg Γ Λ R)) (bound : Nat)
    (run : StateTransition.EvalsToInTime (Turing.TM2.step source) start final bound) :
    StateTransition.EvalsToInTime (Turing.TM2.step ambient)
      (cfg names symbols registers labels start) (final.map (cfg names symbols registers labels)) bound where
  steps := run.steps
  evals_in_steps := by
    change (next ambient)^[run.steps] ((some start).map (cfg names symbols registers labels)) = _
    rw [iterate names symbols registers labels source ambient installed run.steps (some start)]
    have executed : (next source)^[run.steps] (some start) = final := run.evals_in_steps
    rw [executed]
  steps_le_m := run.steps_le_m

/-- Agreement only at owned labels supports only the actual owned prefix. -/
theorem step_owned (source : Λ → Turing.TM2.Stmt Γ Λ R)
    (ambient : Λ' → Turing.TM2.Stmt Γ' Λ' R') (owned : Option Λ → Prop)
    (installed : ∀ label, owned (some label) →
      ambient (labels label) = statement names symbols registers labels (source label))
    (c : Turing.TM2.Cfg Γ Λ R) (ownership : owned c.l) :
    Turing.TM2.step ambient (cfg names symbols registers labels c) =
      (Turing.TM2.step source c).map (cfg names symbols registers labels) := by
  rcases c with ⟨label, regs, data⟩
  cases label with
  | none => rfl
  | some label =>
      simp only [cfg, Option.map_some, Turing.TM2.step, installed label ownership]
      exact congrArg some (stepAux names symbols registers labels (source label) regs data)

theorem iterate_owned (source : Λ → Turing.TM2.Stmt Γ Λ R)
    (ambient : Λ' → Turing.TM2.Stmt Γ' Λ' R') (owned : Option Λ → Prop)
    (installed : ∀ label, owned (some label) →
      ambient (labels label) = statement names symbols registers labels (source label))
    (n : Nat) (start : Turing.TM2.Cfg Γ Λ R)
    (prefixRun : ∀ j, j < n → ∃ reached, (next source)^[j] (some start) = some reached ∧ owned reached.l) :
    (next ambient)^[n] (some (cfg names symbols registers labels start)) =
      ((next source)^[n] (some start)).map (cfg names symbols registers labels) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have prior := ih (fun j bound => prefixRun j (by omega))
      obtain ⟨before, executed, ownership⟩ := prefixRun n (Nat.lt_succ_self n)
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', prior, executed]
      exact step_owned names symbols registers labels source ambient owned installed before ownership

variable [Fintype K] [Fintype K']

omit [DecidableEq K] [DecidableEq K'] in
theorem stackCells (data : ∀ k, List (Γ k)) :
    ∑ j, (stackEquiv names symbols data j).length = ∑ k, (data k).length := by
  symm
  apply Fintype.sum_equiv names
  intro k
  simp only [stackEquiv_apply, List.length_map]

end Resources.RotationCertificate.FrontEndMachine.Transport

