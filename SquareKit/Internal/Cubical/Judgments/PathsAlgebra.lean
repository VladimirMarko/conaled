import SquareKit.Internal.Cubical.Judgments.PathsSyntax
import SquareKit.Internal.Cubical.Judgments.IntervalsTheory

namespace SquareKit.Cubical.Source.Paths
set_option backward.isDefEq.respectTransparency false
open GuardedTheory Presheaf CategoryTheory
universe u

noncomputable def extraOperation (op : Operation)
    (args : Fin (extraSignature.arity op) → Value.{u}) : Value.{u} := by
  classical
  exact match args ⟨0, by cases op <;> decide⟩ with
  | .context Γ => match (args ⟨1, by cases op <;> decide⟩).familyAt (total (Presheaf.interval Γ)) with
    | some B => match (args ⟨2, by cases op <;> decide⟩).termAt Γ (reindex B (Presheaf.endpointSub Γ false)) with
      | some a₀ => match (args ⟨3, by cases op <;> decide⟩).termAt Γ (reindex B (Presheaf.endpointSub Γ true)) with
        | some a₁ => match op with
          | .path => .family Γ (normalizedPath B a₀ a₁)
          | .lam => match (args 4).termAt (total (Presheaf.interval Γ)) B with
            | some b => if h₀ : b.reindex (Presheaf.endpointSub Γ false) = a₀ then
                if h₁ : b.reindex (Presheaf.endpointSub Γ true) = a₁ then
                  .term Γ (normalizedPath B a₀ a₁) (normalizedPathLam b h₀ h₁)
                else .invalid
              else .invalid
            | none => .invalid
          | .app => match (args 4).termAt Γ (normalizedPath B a₀ a₁) with
            | some p => .term (total (Presheaf.interval Γ)) B (normalizedPathApp p)
            | none => .invalid
        | none => .invalid
      | none => .invalid
    | none => .invalid
  | _ => .invalid

variable (Γ : Context.{u}) (B : Family (total (Presheaf.interval Γ)))
  (a₀ : Presheaf.Term (reindex B (Presheaf.endpointSub Γ false)))
  (a₁ : Presheaf.Term (reindex B (Presheaf.endpointSub Γ true)))

@[simp] theorem extra_path :
    extraOperation .path ![.context Γ,.family (total (Presheaf.interval Γ)) B,
      .term Γ (reindex B (Presheaf.endpointSub Γ false)) a₀,
      .term Γ (reindex B (Presheaf.endpointSub Γ true)) a₁] = .family Γ (normalizedPath B a₀ a₁) := by
  simp [extraOperation,Value.familyAt_family,Value.termAt_term]

@[simp] theorem extra_lam (b : Presheaf.Term B)
    (h₀ : b.reindex (Presheaf.endpointSub Γ false) = a₀)
    (h₁ : b.reindex (Presheaf.endpointSub Γ true) = a₁) :
    extraOperation .lam ![.context Γ,.family (total (Presheaf.interval Γ)) B,
      .term Γ (reindex B (Presheaf.endpointSub Γ false)) a₀,
      .term Γ (reindex B (Presheaf.endpointSub Γ true)) a₁,.term (total (Presheaf.interval Γ)) B b] =
      .term Γ (normalizedPath B a₀ a₁) (normalizedPathLam b h₀ h₁) := by
  simp [extraOperation,Value.familyAt_family,Value.termAt_term,h₀,h₁]

@[simp] theorem extra_app (p : Presheaf.Term (normalizedPath B a₀ a₁)) :
    extraOperation .app ![.context Γ,.family (total (Presheaf.interval Γ)) B,
      .term Γ (reindex B (Presheaf.endpointSub Γ false)) a₀,
      .term Γ (reindex B (Presheaf.endpointSub Γ true)) a₁,.term Γ (normalizedPath B a₀ a₁) p] =
      .term (total (Presheaf.interval Γ)) B (normalizedPathApp p) := by
  simp [extraOperation,Value.familyAt_family,Value.termAt_term]

noncomputable def algebra : Algebra signature where
  Carrier := Value.{u}
  operation
    | .inl op => Intervals.algebra.operation op
    | .inr op => extraOperation op
  predicate
    | .inl p => Intervals.algebra.predicate p
    | .inr p => nomatch p

theorem endpoint_eval {V : Type} (γ : Expression V) (ρ : V → Value.{u})
    (Γ : Context.{u}) (hΓ : γ.eval algebra ρ = .context Γ) (b : Bool) :
    (endpoint γ b).eval algebra ρ = .term Γ (Presheaf.interval Γ) (Presheaf.endpoint Γ b) := by
  have he : (Fin.elim0 : Fin 0 → Value.{u}) =
      (fun i => .term Γ (Presheaf.interval Γ) (Fin.elim0 i)) := funext (fun i => Fin.elim0 i)
  cases b
  · change Intervals.extraOperation (.dimension (n := 0) .zero) (Matrix.vecCons (γ.eval algebra ρ) Fin.elim0) = _
    rw [hΓ,he,Intervals.extra_dimension,intervalDimension_zero]
  · change Intervals.extraOperation (.dimension (n := 0) .one) (Matrix.vecCons (γ.eval algebra ρ) Fin.elim0) = _
    rw [hΓ,he,Intervals.extra_dimension,intervalDimension_one]

theorem endpointSub_eval {V : Type} (γ : Expression V) (ρ : V → Value.{u})
    (Γ : Context.{u}) (hΓ : γ.eval algebra ρ = .context Γ) (b : Bool) :
    (endpointSub γ b).eval algebra ρ =
      .substitution Γ (total (Presheaf.interval Γ)) (Presheaf.endpointSub Γ b) := by
  have he := endpoint_eval γ ρ Γ hΓ b
  change Source.operation .pair ![Intervals.extraOperation .interval ![γ.eval algebra ρ],
    Source.operation .id ![γ.eval algebra ρ],(endpoint γ b).eval algebra ρ] = _
  rw [hΓ,he,Intervals.extra_interval]
  simp only [Source.operation,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.head_cons,Matrix.tail_cons,Value.substitutionAt_substitution]
  have ht : Value.termAt Γ (Semantics.subTy (Presheaf.interval Γ) (Semantics.idSub Γ))
      (.term Γ (Presheaf.interval Γ) (Presheaf.endpoint Γ b)) = some (Presheaf.endpoint Γ b) :=
    Value.termAt_term _ _ _
  rw [ht]
  rfl

theorem lift_eval {V : Type} (δ a τ : Expression V) (ρ : V → Value.{u})
    (Γ Δ : Context.{u}) (A : Family Γ) (σ : Δ ⟶ Γ)
    (hΔ : δ.eval algebra ρ = .context Δ) (hA : a.eval algebra ρ = .family Γ A)
    (hσ : τ.eval algebra ρ = .substitution Δ Γ σ) :
    (lift δ a τ).eval algebra ρ = .substitution (total (reindex A σ)) (total A) (liftSub A σ) := by
  change Source.operation .pair ![a.eval algebra ρ,
    Source.operation .comp ![τ.eval algebra ρ,
      Source.operation .weaken ![δ.eval algebra ρ,Source.operation .subTy ![a.eval algebra ρ,τ.eval algebra ρ]]],
    Source.operation .generic ![δ.eval algebra ρ,Source.operation .subTy ![a.eval algebra ρ,τ.eval algebra ρ]]] = _
  rw [hΔ,hA,hσ]
  simp only [Source.operation,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.head_cons,Matrix.tail_cons,Value.familyAt_family,Value.substitutionAt_substitution]
  have ht : Value.termAt (total (reindex A σ))
      (Semantics.subTy A (Semantics.compSub σ (Semantics.weaken Δ (Semantics.subTy A σ))))
      (.term (total (reindex A σ)) (reindex (reindex A σ) (projection (reindex A σ)))
        (Presheaf.generic (reindex A σ))) = some (Presheaf.generic (reindex A σ)) := Value.termAt_term _ _ _
  rw [ht]
  rfl


end SquareKit.Cubical.Source.Paths
