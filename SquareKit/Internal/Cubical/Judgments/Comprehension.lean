import SquareKit.Internal.Cubical.Judgments.Semantics

/-! A constructed interpretation of the existing annotation-free comprehension
signature. Typing guards recover dependent operands from the tagged carrier. -/
namespace SquareKit.Cubical.Source
set_option backward.isDefEq.respectTransparency false
open GuardedTheory Internal.DependentJudgments
universe u

inductive Value : Type (u+1) where
  | context : Semantics.Context.{u} → Value
  | family : (Γ : Semantics.Context.{u}) → Semantics.Family Γ → Value
  | term : (Γ : Semantics.Context.{u}) → (A : Semantics.Family Γ) → Semantics.Section Γ A → Value
  | substitution : (Δ Γ : Semantics.Context.{u}) → Semantics.Substitution Δ Γ → Value
  | invalid : Value

namespace Value
noncomputable def familyAt (Γ : Semantics.Context.{u}) : Value.{u} → Option (Semantics.Family Γ) := by
  classical
  exact fun v => match v with
    | .family Δ A => if h : Δ = Γ then some (h ▸ A) else none
    | _ => none

noncomputable def termAt (Γ : Semantics.Context.{u}) (A : Semantics.Family Γ) :
    Value.{u} → Option (Semantics.Section Γ A) := by
  classical
  exact fun v => match v with
    | .term Δ B t =>
      if h : Δ = Γ then
        let b : (A : Semantics.Family Γ) × Semantics.Section Γ A := h ▸ ⟨B, t⟩
        if k : b.1 = A then some (k ▸ b.2) else none
      else none
    | _ => none

noncomputable def termIn (Γ : Semantics.Context.{u}) :
    Value.{u} → Option ((A : Semantics.Family Γ) × Semantics.Section Γ A) := by
  classical
  exact fun v => match v with
    | .term Δ B t => if h : Δ = Γ then some (h ▸ ⟨B, t⟩) else none
    | _ => none

noncomputable def substitutionAt (Δ Γ : Semantics.Context.{u}) : Value.{u} → Option (Semantics.Substitution Δ Γ) := by
  classical
  exact fun v => match v with
    | .substitution Δ' Γ' σ =>
      if h : Δ' = Δ then if k : Γ' = Γ then some (h ▸ k ▸ σ) else none else none
    | _ => none

@[simp] theorem familyAt_family (Γ : Semantics.Context.{u}) (A : Semantics.Family Γ) :
    familyAt Γ (.family Γ A) = some A := by simp [familyAt]

@[simp] theorem termAt_term (Γ : Semantics.Context.{u}) (A : Semantics.Family Γ) (t : Semantics.Section Γ A) :
    termAt Γ A (.term Γ A t) = some t := by simp [termAt]

@[simp] theorem termIn_term (Γ : Semantics.Context.{u}) (A : Semantics.Family Γ) (t : Semantics.Section Γ A) :
    termIn Γ (.term Γ A t) = some ⟨A, t⟩ := by simp [termIn]

@[simp] theorem substitutionAt_substitution (Δ Γ : Semantics.Context.{u}) (σ : Semantics.Substitution Δ Γ) :
    substitutionAt Δ Γ (.substitution Δ Γ σ) = some σ := by simp [substitutionAt]

end Value

noncomputable def operation (op : Operation)
    (args : Fin op.arity → Value.{u}) : Value.{u} :=
  match op with
  | .empty => .context Semantics.empty
  | .extend => match args 0 with
    | .context Γ => match (args 1).familyAt Γ with
      | some A => .context (Semantics.extend Γ A)
      | none => .invalid
    | _ => .invalid
  | .id => match args 0 with
    | .context Γ => .substitution Γ Γ (Semantics.idSub Γ)
    | _ => .invalid
  | .comp => match args 0, args 1 with
    | .substitution Δ Γ σ, .substitution Θ _ _ =>
      match (args 1).substitutionAt Θ Δ with
      | some τ => .substitution Θ Γ (Semantics.compSub σ τ)
      | none => .invalid
    | _, _ => .invalid
  | .subTy => match args 1 with
    | .substitution Δ Γ σ => match (args 0).familyAt Γ with
      | some A => .family Δ (Semantics.subTy A σ)
      | none => .invalid
    | _ => .invalid
  | .subTm => match args 1 with
    | .substitution Δ Γ σ => match (args 0).termIn Γ with
      | some ⟨A, t⟩ => .term Δ (Semantics.subTy A σ) (Semantics.subTm t σ)
      | none => .invalid
    | _ => .invalid
  | .weaken => match args 0 with
    | .context Γ => match (args 1).familyAt Γ with
      | some A => .substitution (Semantics.extend Γ A) Γ (Semantics.weaken Γ A)
      | none => .invalid
    | _ => .invalid
  | .generic => match args 0 with
    | .context Γ => match (args 1).familyAt Γ with
      | some A => .term (Semantics.extend Γ A) (Semantics.subTy A (Semantics.weaken Γ A)) (Semantics.genericVariable Γ A)
      | none => .invalid
    | _ => .invalid
  | .pair => match args 0, args 1 with
    | .family Γ A, .substitution Δ _ _ => match (args 1).substitutionAt Δ Γ with
      | some σ => match (args 2).termAt Δ (Semantics.subTy A σ) with
        | some t => .substitution Δ (Semantics.extend Γ A) (Semantics.pairSub A σ t)
        | none => .invalid
      | none => .invalid
    | _, _ => .invalid

def predicate (p : Predicate) (args : Fin p.arity → Value.{u}) : Prop :=
  match p with
  | .context => ∃ Γ, args 0 = .context Γ
  | .family => ∃ Γ A, args 0 = .context Γ ∧ args 1 = .family Γ A
  | .term => ∃ Γ A t, args 0 = .context Γ ∧ args 1 = .family Γ A ∧ args 2 = .term Γ A t
  | .substitution => ∃ Δ Γ σ,
      args 0 = .context Δ ∧ args 1 = .context Γ ∧ args 2 = .substitution Δ Γ σ

noncomputable def algebra : Algebra signature where
  Carrier := Value.{u}
  operation := operation
  predicate := predicate

theorem Value.term_eq {Γ : Semantics.Context.{u}} {A B : Semantics.Family Γ}
    {s : Semantics.Section Γ A} {t : Semantics.Section Γ B} (hA : A = B) (ht : HEq s t) :
    Value.term Γ A s = Value.term Γ B t := by
  cases hA; cases eq_of_heq ht; rfl

def pairingEnvironment (Γ Δ : Semantics.Context.{u})
    (A : Semantics.Family Γ) (σ : Semantics.Substitution Δ Γ) (t : Semantics.Section Δ (Semantics.subTy A σ)) :
    Fin 5 → Value.{u} :=
  ![.context Γ, .context Δ, .family Γ A, .substitution Δ Γ σ, .term Δ (Semantics.subTy A σ) t]

/-- Inverting the source guards recovers actual dependent input data. -/
theorem pairing_inputs :
    ∀ ρ : Fin 5 → Value.{u},
    (∀ i, (variablePairRule.premise i).eval algebra.{u} ρ) →
    ∃ (Γ Δ : Semantics.Context.{u}) (A : Semantics.Family Γ) (σ : Semantics.Substitution Δ Γ)
      (t : Semantics.Section Δ (Semantics.subTy A σ)), ρ = pairingEnvironment  Γ Δ A σ t := by
  intro ρ h
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  change predicate  .family ![ρ 0, ρ 2] at h0
  change predicate  .substitution ![ρ 1, ρ 0, ρ 3] at h1
  change predicate  .term ![ρ 1, operation  .subTy ![ρ 2, ρ 3], ρ 4] at h2
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
  have evalSub : operation  .subTy ![ρ 2, ρ 3] = .family Δ (Semantics.subTy A σ) := by
    simp [hA, hσ, operation]
  change ∃ Δ' B t, ρ 1 = .context Δ' ∧
    operation  .subTy ![ρ 2, ρ 3] = .family Δ' B ∧ ρ 4 = .term Δ' B t at h2
  rw [evalSub] at h2
  rcases h2 with ⟨Δ', B, t, hΔ', hB, ht⟩
  have eΔ : Δ' = Δ := Value.context.inj (hΔ'.symm.trans hΔ)
  subst Δ'
  have eB : Semantics.subTy A σ = B := eq_of_heq (Value.family.inj hB).2
  subst B
  refine ⟨Γ, Δ, A, σ, t, ?_⟩
  funext i
  fin_cases i <;> simpa only [pairingEnvironment, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    Matrix.cons_val_succ] using (by first | exact hΓ | exact hΔ | exact hA | exact hσ | exact ht)

/-- Soundness of the guarded rule, for every actual structural model. -/
theorem variablePair_valid :
    Satisfies algebra.{u} variablePairRule := by
  intro ρ h
  rcases pairing_inputs  ρ h with ⟨Γ, Δ, A, σ, t, rfl⟩
  change operation  .subTm
    ![operation  .generic ![.context Γ, .family Γ A],
      operation  .pair ![.family Γ A, .substitution Δ Γ σ, .term Δ (Semantics.subTy A σ) t]] =
    .term Δ (Semantics.subTy A σ) t
  simp only [operation, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, Value.familyAt_family, Value.substitutionAt_substitution,
    Value.termAt_term, Value.termIn_term]
  apply Value.term_eq
  · rw [Semantics.subTy_comp, Semantics.weaken_pair]
  · exact Semantics.variable_pair A σ t

theorem pairing_valid : Satisfies algebra.{u} pairingRule := by
  intro ρ h
  rcases pairing_inputs  ρ h with ⟨Γ, Δ, A, σ, t, rfl⟩
  refine ⟨Δ, Semantics.extend Γ A, Semantics.pairSub A σ t, rfl, ?_, ?_⟩
  · simp [pairingRule, substitution, extend, apply2, pairingEnvironment,
      Term.eval, algebra, operation]
  · simp [pairingRule, substitution, pair, apply3, pairingEnvironment,
      Term.eval, algebra, operation]

theorem weakenPair_valid : Satisfies algebra.{u} weakenPairRule := by
  intro ρ h
  rcases pairing_inputs  ρ h with ⟨Γ, Δ, A, σ, t, rfl⟩
  change operation  .comp
    ![operation  .weaken ![.context Γ, .family Γ A],
      operation  .pair ![.family Γ A, .substitution Δ Γ σ, .term Δ (Semantics.subTy A σ) t]] =
    .substitution Δ Γ σ
  simp only [operation, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, Value.familyAt_family, Value.substitutionAt_substitution,
    Value.termAt_term]
  exact congrArg (Value.substitution Δ Γ) (Semantics.weaken_pair A σ t)

theorem familySchema_valid (out : Judgment (Fin 2))
    (h : ∀ (Γ : Semantics.Context.{u}) (A : Semantics.Family Γ),
      out.eval algebra.{u} ![.context Γ, .family Γ A]) :
    Satisfies algebra.{u} (familySchema out) := by
  intro ρ hp
  have h0 := hp 0
  change predicate  .family ![ρ 0, ρ 1] at h0
  rcases h0 with ⟨Γ, A, hΓ, hA⟩
  have e : ρ = ![.context Γ, .family Γ A] := by
    funext i
    fin_cases i
    · exact hΓ
    · exact hA
  simpa only [e] using h Γ A

theorem extension_valid : Satisfies algebra.{u} extensionRule := by
  apply familySchema_valid
  intro Γ A
  refine ⟨Semantics.extend Γ A, ?_⟩
  simp [extend, apply2, Term.eval, algebra, operation]

theorem weakening_valid : Satisfies algebra.{u} weakeningRule := by
  apply familySchema_valid
  intro Γ A
  refine ⟨Semantics.extend Γ A, Γ, Semantics.weaken Γ A, ?_, rfl, ?_⟩
  · simp [extend, apply2, Term.eval, algebra, operation]
  · simp [weaken, apply2, Term.eval, algebra, operation]

theorem generic_valid : Satisfies algebra.{u} genericRule := by
  apply familySchema_valid
  intro Γ A
  refine ⟨Semantics.extend Γ A, Semantics.subTy A (Semantics.weaken Γ A), Semantics.genericVariable Γ A, ?_, ?_, ?_⟩
  · simp [extend, apply2, Term.eval, algebra, operation]
  · simp [subTy, weaken, apply2, Term.eval, algebra, operation]
  · simp [generic, apply2, Term.eval, algebra, operation]

theorem empty_valid : Satisfies algebra.{u} emptyRule := by
  intro ρ _
  exact ⟨Semantics.empty, rfl⟩

theorem identity_valid : Satisfies algebra.{u} identityRule := by
  intro ρ h
  rcases h 0 with ⟨Γ, hΓ⟩
  refine ⟨Γ, Γ, Semantics.idSub Γ, hΓ, hΓ, ?_⟩
  change ρ 0 = .context Γ at hΓ
  change operation  .id ![ρ 0] = .substitution Γ Γ (Semantics.idSub Γ)
  simp [operation, hΓ]

noncomputable def comprehensionModel :
    GuardedTheory.Model.{0,u+1} comprehensionTheory where
  toAlgebra := algebra.{u}
  rules
    | .variablePair => variablePair_valid
    | .pairing => pairing_valid
    | .weakenPair => weakenPair_valid
    | .extension => extension_valid
    | .weakening => weakening_valid
    | .generic => generic_valid
    | .empty => empty_valid
    | .identity => identity_valid


theorem Value.term_input (Γ : Semantics.Context.{u}) (A : Semantics.Family Γ) (v : Value.{u})
    (h : predicate .term ![.context Γ,.family Γ A,v]) :
    ∃ t : Semantics.Section Γ A, v = .term Γ A t := by
  rcases h with ⟨Δ,B,t,hΓ,hA,ht⟩
  have eΓ := Value.context.inj hΓ
  subst Δ
  have eA := eq_of_heq (Value.family.inj hA).2
  subst B
  exact ⟨t,ht⟩

theorem Value.termAt_convert {Γ : Semantics.Context.{u}} {A B : Semantics.Family Γ}
    (h : A = B) (t : Semantics.Section Γ A) :
    termAt Γ B (.term Γ A t) = some (Presheaf.Term.convert h t) := by
  cases h
  exact termAt_term Γ A t

end SquareKit.Cubical.Source
