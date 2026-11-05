import SquareKit.GuardedTheory
import SquareKit.Internal.PathTransport.Comprehension
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Fin

/-! A guarded presentation of dependent comprehension. The raw syntax is
independent of semantic annotations. Totalization is a host interpretation
device: guards exclude ill-sorted operands from admitted typing derivations. -/

namespace SquareKit.Internal.DependentJudgments
open GuardedTheory
open PathTransport.Typed
universe u

inductive Operation where
  | empty | extend | id | comp | subTy | subTm | weaken | generic | pair
  deriving DecidableEq

abbrev Operation.arity : Operation → Nat
  | .empty => 0
  | .id => 1
  | .pair => 3
  | _ => 2

inductive Predicate where
  | context | family | term | substitution
  deriving DecidableEq

abbrev Predicate.arity : Predicate → Nat
  | .context => 1
  | .family => 2
  | _ => 3

def signature : Signature where
  Operation := Operation
  arity := Operation.arity
  Predicate := Predicate
  arguments := Predicate.arity

inductive Value (M : StructuralModel.{u}) where
  | context : M.Context → Value M
  | family : (Γ : M.Context) → M.Family Γ → Value M
  | term : (Γ : M.Context) → (A : M.Family Γ) → M.Section Γ A → Value M
  | substitution : (Δ Γ : M.Context) → M.Substitution Δ Γ → Value M
  | invalid : Value M

namespace Value
variable {M : StructuralModel.{u}}

noncomputable def familyAt (Γ : M.Context) : Value M → Option (M.Family Γ) := by
  classical
  exact fun v => match v with
    | .family Δ A => if h : Δ = Γ then some (h ▸ A) else none
    | _ => none

noncomputable def termAt (Γ : M.Context) (A : M.Family Γ) :
    Value M → Option (M.Section Γ A) := by
  classical
  exact fun v => match v with
    | .term Δ B t =>
      if h : Δ = Γ then
        let b : (A : M.Family Γ) × M.Section Γ A := h ▸ ⟨B, t⟩
        if k : b.1 = A then some (k ▸ b.2) else none
      else none
    | _ => none

noncomputable def termIn (Γ : M.Context) :
    Value M → Option ((A : M.Family Γ) × M.Section Γ A) := by
  classical
  exact fun v => match v with
    | .term Δ B t => if h : Δ = Γ then some (h ▸ ⟨B, t⟩) else none
    | _ => none

noncomputable def substitutionAt (Δ Γ : M.Context) : Value M → Option (M.Substitution Δ Γ) := by
  classical
  exact fun v => match v with
    | .substitution Δ' Γ' σ =>
      if h : Δ' = Δ then if k : Γ' = Γ then some (h ▸ k ▸ σ) else none else none
    | _ => none

@[simp] theorem familyAt_family (Γ : M.Context) (A : M.Family Γ) :
    familyAt Γ (.family Γ A) = some A := by simp [familyAt]

@[simp] theorem termAt_term (Γ : M.Context) (A : M.Family Γ) (t : M.Section Γ A) :
    termAt Γ A (.term Γ A t) = some t := by simp [termAt]

@[simp] theorem termIn_term (Γ : M.Context) (A : M.Family Γ) (t : M.Section Γ A) :
    termIn Γ (.term Γ A t) = some ⟨A, t⟩ := by simp [termIn]

@[simp] theorem substitutionAt_substitution (Δ Γ : M.Context) (σ : M.Substitution Δ Γ) :
    substitutionAt Δ Γ (.substitution Δ Γ σ) = some σ := by simp [substitutionAt]

end Value

noncomputable def operation (M : StructuralModel.{u}) (op : Operation)
    (args : Fin op.arity → Value M) : Value M :=
  match op with
  | .empty => .context M.empty
  | .extend => match args 0 with
    | .context Γ => match (args 1).familyAt Γ with
      | some A => .context (M.extend Γ A)
      | none => .invalid
    | _ => .invalid
  | .id => match args 0 with
    | .context Γ => .substitution Γ Γ (M.idSub Γ)
    | _ => .invalid
  | .comp => match args 0, args 1 with
    | .substitution Δ Γ σ, .substitution Θ _ _ =>
      match (args 1).substitutionAt Θ Δ with
      | some τ => .substitution Θ Γ (M.compSub σ τ)
      | none => .invalid
    | _, _ => .invalid
  | .subTy => match args 1 with
    | .substitution Δ Γ σ => match (args 0).familyAt Γ with
      | some A => .family Δ (M.subTy A σ)
      | none => .invalid
    | _ => .invalid
  | .subTm => match args 1 with
    | .substitution Δ Γ σ => match (args 0).termIn Γ with
      | some ⟨A, t⟩ => .term Δ (M.subTy A σ) (M.subTm t σ)
      | none => .invalid
    | _ => .invalid
  | .weaken => match args 0 with
    | .context Γ => match (args 1).familyAt Γ with
      | some A => .substitution (M.extend Γ A) Γ (M.weaken Γ A)
      | none => .invalid
    | _ => .invalid
  | .generic => match args 0 with
    | .context Γ => match (args 1).familyAt Γ with
      | some A => .term (M.extend Γ A) (M.subTy A (M.weaken Γ A)) (M.genericVariable Γ A)
      | none => .invalid
    | _ => .invalid
  | .pair => match args 0, args 1 with
    | .family Γ A, .substitution Δ _ _ => match (args 1).substitutionAt Δ Γ with
      | some σ => match (args 2).termAt Δ (M.subTy A σ) with
        | some t => .substitution Δ (M.extend Γ A) (M.pairSub A σ t)
        | none => .invalid
      | none => .invalid
    | _, _ => .invalid

def predicate (M : StructuralModel.{u}) (p : Predicate) (args : Fin p.arity → Value M) : Prop :=
  match p with
  | .context => ∃ Γ, args 0 = .context Γ
  | .family => ∃ Γ A, args 0 = .context Γ ∧ args 1 = .family Γ A
  | .term => ∃ Γ A t, args 0 = .context Γ ∧ args 1 = .family Γ A ∧ args 2 = .term Γ A t
  | .substitution => ∃ Δ Γ σ,
      args 0 = .context Δ ∧ args 1 = .context Γ ∧ args 2 = .substitution Δ Γ σ

noncomputable def algebra (M : StructuralModel.{u}) : Algebra signature where
  Carrier := Value M
  operation := operation M
  predicate := predicate M

abbrev Expression (V : Type) := Term signature V
abbrev Judgment (V : Type) := Atom signature V

def apply0 (op : Operation) (h : op.arity = 0) : Expression V :=
  .app op (fun i => nomatch Fin.cast h i)

def apply1 (op : Operation) (h : op.arity = 1) (a : Expression V) : Expression V :=
  .app op (fun i => ![a] (Fin.cast h i))

def apply2 (op : Operation) (h : op.arity = 2) (a b : Expression V) : Expression V :=
  .app op (fun i => ![a, b] (Fin.cast h i))

def apply3 (op : Operation) (h : op.arity = 3) (a b c : Expression V) : Expression V :=
  .app op (fun i => ![a, b, c] (Fin.cast h i))

def family (Γ A : Expression V) : Judgment V := .pred .family ![Γ, A]
def term (Γ A t : Expression V) : Judgment V := .pred .term ![Γ, A, t]
def substitution (Δ Γ σ : Expression V) : Judgment V := .pred .substitution ![Δ, Γ, σ]
def subTy (A σ : Expression V) : Expression V := apply2 .subTy rfl A σ
def subTm (t σ : Expression V) : Expression V := apply2 .subTm rfl t σ
def generic (Γ A : Expression V) : Expression V := apply2 .generic rfl Γ A
def pair (A σ t : Expression V) : Expression V := apply3 .pair rfl A σ t

abbrev variablePairRule : Rule signature where
  parameterCount := 5
  hypotheses := 3
  premise := ![family (.var 0) (.var 2), substitution (.var 1) (.var 0) (.var 3),
    term (.var 1) (subTy (.var 2) (.var 3)) (.var 4)]
  conclusion := .eq (subTm (generic (.var 0) (.var 2)) (pair (.var 2) (.var 3) (.var 4))) (.var 4)

theorem Value.term_eq {M : StructuralModel} {Γ : M.Context} {A B : M.Family Γ}
    {s : M.Section Γ A} {t : M.Section Γ B} (hA : A = B) (ht : HEq s t) :
    Value.term Γ A s = Value.term Γ B t := by
  cases hA; cases eq_of_heq ht; rfl

/-- Soundness of the guarded rule, for every actual structural model. -/
theorem variablePair_valid (M : StructuralModel.{u}) :
    Satisfies (algebra M) variablePairRule := by
  intro ρ h
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  change predicate M .family ![ρ 0, ρ 2] at h0
  change predicate M .substitution ![ρ 1, ρ 0, ρ 3] at h1
  change predicate M .term ![ρ 1, operation M .subTy ![ρ 2, ρ 3], ρ 4] at h2
  simp only [predicate] at h0 h1 h2
  rcases h0 with ⟨Γ, A, hΓ, hA⟩
  change ρ 0 = .context Γ at hΓ
  change ρ 2 = .family Γ A at hA
  rcases h1 with ⟨Δ, Γ', σ, hΔ, hΓ', hσ⟩
  change ρ 1 = .context Δ at hΔ
  change ρ 0 = .context Γ' at hΓ'
  change ρ 3 = .substitution Δ Γ' σ at hσ
  have eΓ : Γ' = Γ := Value.context.inj (hΓ'.symm.trans hΓ)
  subst Γ'
  have evalSub : operation M .subTy ![ρ 2, ρ 3] = .family Δ (M.subTy A σ) := by
    simp [hA, hσ, operation]
  change ∃ Δ' B t, ρ 1 = .context Δ' ∧
    operation M .subTy ![ρ 2, ρ 3] = .family Δ' B ∧ ρ 4 = .term Δ' B t at h2
  rw [evalSub] at h2
  rcases h2 with ⟨Δ', B, t, hΔ', hB, ht⟩
  have eΔ : Δ' = Δ := Value.context.inj (hΔ'.symm.trans hΔ)
  subst Δ'
  have eB : M.subTy A σ = B := eq_of_heq (Value.family.inj hB).2
  subst B
  change operation M .subTm
    ![operation M .generic ![ρ 0, ρ 2], operation M .pair ![ρ 2, ρ 3, ρ 4]] = ρ 4
  simp only [hΓ, hA, hσ, ht]
  simp only [operation, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    Value.familyAt_family, Value.substitutionAt_substitution, Value.termAt_term, Value.termIn_term]
  apply Value.term_eq
  · rw [M.subTy_comp, M.weaken_pair]
  · exact M.variable_pair A σ t

inductive ComprehensionAxiom where
  | variablePair

abbrev comprehensionTheory : Theory signature where
  Axiom := ComprehensionAxiom
  rule _ := variablePairRule

noncomputable def comprehensionModel (M : StructuralModel.{u}) :
    GuardedTheory.Model comprehensionTheory where
  toAlgebra := algebra M
  rules _ := variablePair_valid M

/-- A source derivation with no semantic context, type, or term indices. -/
def variablePairDerivation : Derivation comprehensionTheory
    (List.ofFn variablePairRule.premise) variablePairRule.conclusion := by
  have d := Derivation.rule (T := comprehensionTheory)
    ComprehensionAxiom.variablePair Term.var
    (fun i => Derivation.hypothesis (List.mem_ofFn.mpr ⟨i, rfl⟩))
  simpa only [Atom.subst_id, comprehensionTheory] using d

/-- The derivation is reusable at a new interpretation by supplying its model
and its five schematic arguments. No old all-model annotation is reconstructed. -/
theorem interpret_variablePair (M : StructuralModel.{u}) (Γ Δ : M.Context)
    (A : M.Family Γ) (σ : M.Substitution Δ Γ) (t : M.Section Δ (M.subTy A σ)) :
    variablePairRule.conclusion.eval (algebra M)
      ![.context Γ, .context Δ, .family Γ A, .substitution Δ Γ σ,
        .term Δ (M.subTy A σ) t] := by
  apply variablePairDerivation.sound (comprehensionModel M)
  intro p hp
  rcases List.mem_ofFn.mp hp with ⟨i, rfl⟩
  change Fin 3 at i
  fin_cases i
  · exact ⟨Γ, A, rfl, rfl⟩
  · exact ⟨Δ, Γ, σ, rfl, rfl, rfl⟩
  · refine ⟨Δ, M.subTy A σ, t, rfl, ?_, rfl⟩
    simp [variablePairRule, Term.eval, subTy, apply2, comprehensionModel, algebra, operation]

end SquareKit.Internal.DependentJudgments
