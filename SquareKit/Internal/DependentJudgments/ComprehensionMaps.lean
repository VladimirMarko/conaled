import SquareKit.Internal.DependentJudgments.Comprehension
import SquareKit.Internal.PathTransport.InterpretationMaps

/-! Defined comprehension operations commute with structural model maps.
The invalid value is an interpreter artifact; its behavior is not reflected. -/
namespace SquareKit.Internal.DependentJudgments
open GuardedTheory PathTransport.Typed
set_option backward.isDefEq.respectTransparency false
universe u v w

namespace Value
variable {M : StructuralModel.{u}} {N : StructuralModel.{v}}

def map (F : StructuralMap M N) : Value M → Value N
  | .context Γ => .context (F.context Γ)
  | .family Γ A => .family (F.context Γ) (F.family A)
  | .term Γ A t => .term (F.context Γ) (F.family A) (F.mapTm t)
  | .substitution Δ Γ σ => .substitution (F.context Δ) (F.context Γ) (F.substitution σ)
  | .telescope Γ n T => .telescope (F.context Γ) n (F.telescope T)
  | .invalid => .invalid

theorem map_defined (F : StructuralMap M N) (x : Value M) (h : x ≠ .invalid) :
    map F x ≠ .invalid := by cases x <;> simp_all [map]

theorem familyAt_some {Γ : M.Context} {A : M.Family Γ} {x : Value M}
    (h : familyAt Γ x = some A) : x = .family Γ A := by
  cases x <;> simp only [familyAt] at h
  all_goals try contradiction
  split at h
  · rename_i e
    cases e
    simp only [Option.some.injEq] at h
    cases h
    rfl
  · contradiction

theorem termAt_some {Γ : M.Context} {A : M.Family Γ} {t : M.Section Γ A} {x : Value M}
    (h : termAt Γ A x = some t) : x = .term Γ A t := by
  cases x <;> simp only [termAt] at h
  all_goals try contradiction
  split at h
  · rename_i e
    cases e
    split at h
    · rename_i e
      cases e
      simp only [Option.some.injEq] at h
      cases h
      rfl
    · contradiction
  · contradiction

theorem termIn_some {Γ : M.Context} {A : M.Family Γ} {t : M.Section Γ A} {x : Value M}
    (h : termIn Γ x = some ⟨A, t⟩) : x = .term Γ A t := by
  cases x <;> simp only [termIn] at h
  all_goals try contradiction
  split at h
  · rename_i e
    cases e
    simp only [Option.some.injEq, Sigma.mk.inj_iff] at h
    rcases h with ⟨hA, ht⟩
    cases hA
    cases eq_of_heq ht
    rfl
  · contradiction

theorem substitutionAt_some {Δ Γ : M.Context} {σ : M.Substitution Δ Γ} {x : Value M}
    (h : substitutionAt Δ Γ x = some σ) : x = .substitution Δ Γ σ := by
  cases x <;> simp only [substitutionAt] at h
  all_goals try contradiction
  split at h
  · rename_i e
    cases e
    split at h
    · rename_i e
      cases e
      simp only [Option.some.injEq] at h
      cases h
      rfl
    · contradiction
  · contradiction


theorem family_heq_eq {Γ Δ : M.Context} {A : M.Family Γ} {B : M.Family Δ}
    (hΓ : Γ = Δ) (hA : HEq A B) : Value.family Γ A = .family Δ B := by
  cases hΓ; cases eq_of_heq hA; rfl

theorem term_heq_eq {Γ Δ : M.Context} {A : M.Family Γ} {B : M.Family Δ}
    {s : M.Section Γ A} {t : M.Section Δ B}
    (hΓ : Γ = Δ) (hA : HEq A B) (ht : HEq s t) : Value.term Γ A s = .term Δ B t := by
  cases hΓ; cases eq_of_heq hA; cases eq_of_heq ht; rfl

theorem substitution_heq_eq {Γ Γ' Δ Δ' : M.Context}
    {σ : M.Substitution Δ Γ} {τ : M.Substitution Δ' Γ'}
    (hΓ : Γ = Γ') (hΔ : Δ = Δ') (hσ : HEq σ τ) :
    Value.substitution Δ Γ σ = .substitution Δ' Γ' τ := by
  cases hΓ; cases hΔ; cases eq_of_heq hσ; rfl


@[simp] theorem map_identity (x : Value M) : map (StructuralMap.identityMap M) x = x := by
  cases x with
  | telescope Γ n T => exact congrArg (Value.telescope Γ n) (StructuralMap.telescope_identity T)
  | _ => rfl

theorem map_compose {P : StructuralModel.{w}} (G : StructuralMap N P) (F : StructuralMap M N)
    (x : Value M) : map (StructuralMap.compose G F) x = map G (map F x) := by
  cases x with
  | telescope Γ n T =>
    exact congrArg (Value.telescope (G.context (F.context Γ)) n)
      (StructuralMap.telescope_compose G F T).symm
  | _ => rfl

end Value

/-- The exact semantic operands on which a structural operation is defined. -/
inductive Inputs (M : StructuralModel.{u}) :
    (op : Operation) → (Fin op.arity → Value M) → Prop where
  | empty : Inputs M .empty Fin.elim0
  | extend (Γ) (A : M.Family Γ) : Inputs M .extend ![.context Γ, .family Γ A]
  | id (Γ) : Inputs M .id ![.context Γ]
  | comp {Γ Δ Θ} (σ : M.Substitution Δ Γ) (τ : M.Substitution Θ Δ) :
      Inputs M .comp ![.substitution Δ Γ σ, .substitution Θ Δ τ]
  | subTy {Γ Δ} (A : M.Family Γ) (σ : M.Substitution Δ Γ) :
      Inputs M .subTy ![.family Γ A, .substitution Δ Γ σ]
  | subTm {Γ Δ A} (t : M.Section Γ A) (σ : M.Substitution Δ Γ) :
      Inputs M .subTm ![.term Γ A t, .substitution Δ Γ σ]
  | weaken (Γ) (A : M.Family Γ) : Inputs M .weaken ![.context Γ, .family Γ A]
  | generic (Γ) (A : M.Family Γ) : Inputs M .generic ![.context Γ, .family Γ A]
  | pair {Γ Δ} (A : M.Family Γ) (σ : M.Substitution Δ Γ)
      (t : M.Section Δ (M.subTy A σ)) :
      Inputs M .pair ![.family Γ A, .substitution Δ Γ σ, .term Δ (M.subTy A σ) t]

theorem inputs_of_defined (M : StructuralModel.{u}) (op : Operation)
    (args : Fin op.arity → Value M) (h : operation M op args ≠ .invalid) : Inputs M op args := by
  cases op with
  | empty =>
    have e : args = Fin.elim0 := by funext i; exact Fin.elim0 i
    rw [e]; exact Inputs.empty
  | id =>
    cases h0 : args 0 <;> simp only [operation, h0] at h
    all_goals try contradiction
    rename_i Γ
    have e : args = ![.context Γ] := by funext i; fin_cases i; exact h0
    rw [e]; exact Inputs.id Γ
  | extend =>
    cases h0 : args 0 <;> simp only [operation, h0] at h
    all_goals try contradiction
    rename_i Γ
    cases ha : Value.familyAt Γ (args 1) with
    | none => simp [ha] at h
    | some A =>
      have h1 := Value.familyAt_some ha
      have e : args = ![.context Γ, .family Γ A] := by
        funext i; fin_cases i <;> assumption
      rw [e]; exact Inputs.extend Γ A
  | weaken =>
    cases h0 : args 0 <;> simp only [operation, h0] at h
    all_goals try contradiction
    rename_i Γ
    cases ha : Value.familyAt Γ (args 1) with
    | none => simp [ha] at h
    | some A =>
      have h1 := Value.familyAt_some ha
      have e : args = ![.context Γ, .family Γ A] := by
        funext i; fin_cases i <;> assumption
      rw [e]; exact Inputs.weaken Γ A
  | generic =>
    cases h0 : args 0 <;> simp only [operation, h0] at h
    all_goals try contradiction
    rename_i Γ
    cases ha : Value.familyAt Γ (args 1) with
    | none => simp [ha] at h
    | some A =>
      have h1 := Value.familyAt_some ha
      have e : args = ![.context Γ, .family Γ A] := by
        funext i; fin_cases i <;> assumption
      rw [e]; exact Inputs.generic Γ A
  | subTy =>
    cases h1 : args 1 <;> simp only [operation, h1] at h
    all_goals try contradiction
    rename_i Δ Γ σ
    cases ha : Value.familyAt Γ (args 0) with
    | none => simp [ha] at h
    | some A =>
      have h0 := Value.familyAt_some ha
      have e : args = ![.family Γ A, .substitution Δ Γ σ] := by
        funext i; fin_cases i <;> assumption
      rw [e]; exact Inputs.subTy A σ
  | subTm =>
    cases h1 : args 1 <;> simp only [operation, h1] at h
    all_goals try contradiction
    rename_i Δ Γ σ
    cases ht : Value.termIn Γ (args 0) with
    | none => simp [ht] at h
    | some t =>
      rcases t with ⟨A, t⟩
      have h0 := Value.termIn_some ht
      have e : args = ![.term Γ A t, .substitution Δ Γ σ] := by
        funext i; fin_cases i <;> assumption
      rw [e]; exact Inputs.subTm t σ
  | comp =>
    cases h0 : args 0 <;> simp only [operation, h0] at h
    all_goals try contradiction
    rename_i Δ Γ σ
    cases h1 : args 1 <;> simp only [h1] at h
    all_goals try contradiction
    rename_i Θ Ξ τ
    cases ht : Value.substitutionAt Θ Δ (args 1) with
    | none => simp [h1] at ht; simp [ht] at h
    | some τ' =>
      have h1' := Value.substitutionAt_some ht
      have e : args = ![.substitution Δ Γ σ, .substitution Θ Δ τ'] := by
        funext i; fin_cases i <;> assumption
      rw [e]; exact Inputs.comp σ τ'
  | pair =>
    cases h0 : args 0 <;> simp only [operation, h0] at h
    all_goals try contradiction
    rename_i Γ A
    cases h1 : args 1 <;> simp only [h1] at h
    all_goals try contradiction
    rename_i Δ Ξ σ
    cases hs : Value.substitutionAt Δ Γ (args 1) with
    | none => simp [h1] at hs; simp [hs] at h
    | some σ' =>
      have h1' := Value.substitutionAt_some hs
      have hs' : Value.substitutionAt Δ Γ (.substitution Δ Ξ σ) = some σ' := by simpa [h1] using hs
      rw [hs'] at h
      cases ht : Value.termAt Δ (M.subTy A σ') (args 2) with
      | none => simp [ht] at h
      | some t =>
        have h2 := Value.termAt_some ht
        have e : args = ![.family Γ A, .substitution Δ Γ σ', .term Δ (M.subTy A σ') t] := by
          funext i; fin_cases i <;> assumption
        rw [e]; exact Inputs.pair A σ' t


theorem Inputs.operands_defined {M : StructuralModel.{u}} {op args} (h : Inputs M op args) :
    ∀ i, args i ≠ .invalid := by
  cases h <;> intro i <;> fin_cases i <;> simp

noncomputable def partialAlgebra (M : StructuralModel.{u}) : PartialAlgebra signature where
  toAlgebra := algebra M
  invalid := .invalid
  strict op args h := (inputs_of_defined M op args h).operands_defined

theorem Inputs.operation_map {M : StructuralModel.{u}} {N : StructuralModel.{v}}
    (F : StructuralMap M N) {op args} (h : Inputs M op args) :
    Value.map F (operation M op args) = operation N op (Value.map F ∘ args) := by
  cases h with
  | empty => exact congrArg Value.context F.empty
  | extend Γ A =>
    simpa [operation, Value.map, Function.comp_def] using congrArg Value.context (F.extend A)
  | id Γ =>
    simpa [operation, Value.map, Function.comp_def] using
      congrArg (Value.substitution (F.context Γ) (F.context Γ)) (F.id Γ)
  | comp σ τ =>
    simpa [operation, Value.map, Function.comp_def] using
      congrArg (Value.substitution _ _) (F.comp σ τ)
  | subTy A σ =>
    simpa [operation, Value.map, Function.comp_def] using
      Value.family_heq_eq rfl (heq_of_eq (F.subTy A σ))
  | subTm t σ =>
    simpa [operation, Value.map, Function.comp_def] using
      Value.term_heq_eq rfl (heq_of_eq (F.subTy _ σ)) (F.subTm t σ)
  | weaken Γ A =>
    simpa [operation, Value.map, Function.comp_def] using
      Value.substitution_heq_eq rfl (F.extend A) (F.weaken A)
  | generic Γ A =>
    simpa [operation, Value.map, Function.comp_def] using
      Value.term_heq_eq (F.extend A) (F.variable_type A) (F.mapVariable A)
  | @pair Γ Δ A σ t =>
    let t' := cast (congrArg (N.Section _) (F.subTy A σ)) (F.mapTm t)
    have ht : Value.term (F.context Δ) (F.family (M.subTy A σ)) (F.mapTm t) =
        Value.term (F.context Δ) (N.subTy (F.family A) (F.substitution σ)) t' :=
      Value.term_heq_eq rfl (heq_of_eq (F.subTy A σ)) (cast_heq _ _).symm
    simp only [operation, Function.comp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
      Value.substitutionAt_substitution, Value.termAt_term, Value.map]
    rw [ht, Value.termAt_term]
    exact Value.substitution_heq_eq (F.extend A) rfl (F.pair A σ t)

theorem predicate_map {M : StructuralModel.{u}} {N : StructuralModel.{v}}
    (F : StructuralMap M N) (p : Predicate) (args : Fin p.arity → Value M)
    (h : predicate M p args) : predicate N p (Value.map F ∘ args) := by
  cases p with
  | context =>
    rcases h with ⟨Γ, h⟩
    exact ⟨F.context Γ, by simp [ h, Value.map]⟩
  | family =>
    rcases h with ⟨Γ, A, hΓ, hA⟩
    exact ⟨F.context Γ, F.family A, by simp [ hΓ, Value.map],
      by simp [ hA, Value.map]⟩
  | term =>
    rcases h with ⟨Γ, A, t, hΓ, hA, ht⟩
    exact ⟨F.context Γ, F.family A, F.mapTm t,
      by simp [ hΓ, Value.map], by simp [ hA, Value.map],
      by simp [ ht, Value.map]⟩
  | substitution =>
    rcases h with ⟨Δ, Γ, σ, hΔ, hΓ, hσ⟩
    exact ⟨F.context Δ, F.context Γ, F.substitution σ,
      by simp [ hΔ, Value.map], by simp [ hΓ, Value.map],
      by simp [ hσ, Value.map]⟩

noncomputable def partialHom {M : StructuralModel.{u}} {N : StructuralModel.{v}}
    (F : StructuralMap M N) : PartialHom (partialAlgebra M) (partialAlgebra N) where
  map := Value.map F
  operation op args h := (inputs_of_defined M op args h).operation_map F
  defined := Value.map_defined F
  predicate := predicate_map F

/-- A generated expression commutes whenever its source interpretation is defined.
No injectivity or reflection of semantic equality is required of the model map. -/
theorem interpret_map {M : StructuralModel.{u}} {N : StructuralModel.{v}}
    (F : StructuralMap M N) {V : Type} (t : Expression V) (ρ : V → Value M)
    (h : t.eval (algebra M) ρ ≠ .invalid) :
    Value.map F (t.eval (algebra M) ρ) = t.eval (algebra N) (Value.map F ∘ ρ) :=
  (partialHom F).eval t ρ h


/-- The generated variable-pair expression is defined by its checked derivation,
and therefore commutes at every structural map admitting the given inputs. -/
theorem variablePair_expression_map {M : StructuralModel.{u}} {N : StructuralModel.{v}}
    (F : StructuralMap M N) (Γ Δ : M.Context) (A : M.Family Γ)
    (σ : M.Substitution Δ Γ) (t : M.Section Δ (M.subTy A σ)) :
    let e : Expression (Fin 5) := subTm (generic (.var 0) (.var 2))
      (pair (.var 2) (.var 3) (.var 4))
    Value.map F (e.eval (algebra M) (pairingEnvironment M Γ Δ A σ t)) =
      e.eval (algebra N) (Value.map F ∘ pairingEnvironment M Γ Δ A σ t) := by
  apply interpret_map
  have hv := interpret_variablePair M Γ Δ A σ t
  change (subTm (generic (.var 0) (.var 2)) (pair (.var 2) (.var 3) (.var 4))).eval
    (algebra M) (pairingEnvironment M Γ Δ A σ t) = .term Δ (M.subTy A σ) t at hv
  rw [hv]
  intro h
  cases h

end SquareKit.Internal.DependentJudgments
