import SquareKit.Internal.Cubical.Judgments.FillingAlgebra

/-! Evaluation equations expose the actual provider and restricted operands. -/
namespace SquareKit.Cubical.Source.Fillings
set_option backward.isDefEq.respectTransparency false
open GuardedTheory Presheaf CategoryTheory
universe u

@[simp] theorem extra_faceTop (Γ : Context.{u}) :
    extraOperation .faceTop ![.context Γ] = .cofibration Γ (Cofibration.top Γ) := rfl
@[simp] theorem extra_faceBot (Γ : Context.{u}) :
    extraOperation .faceBot ![.context Γ] = .cofibration Γ (Cofibration.bot Γ) := rfl
@[simp] theorem extra_faceJoin (Γ : Context.{u}) (φ ψ : Cofibration Γ) :
    extraOperation .faceJoin ![.context Γ,.cofibration Γ φ,.cofibration Γ ψ] = .cofibration Γ (φ.join ψ) := by
  simp [extraOperation,Value.cofibrationAt_cofibration]
@[simp] theorem extra_faceEndpoint (Γ : Context.{u}) (r : Presheaf.Term (Presheaf.interval Γ)) (b : Bool) :
    extraOperation (.faceEndpoint b) ![.context Γ,.term Γ (Presheaf.interval Γ) r] =
      .cofibration Γ (Cofibration.endpoint r b) := by simp [extraOperation,Value.termAt_term]
@[simp] theorem extra_restriction (Γ : Context.{u}) (φ : Cofibration Γ) :
    extraOperation .restriction ![.context Γ,.cofibration Γ φ] = .context (restrictContext φ) := by
  simp [extraOperation,Value.cofibrationAt_cofibration]
@[simp] theorem extra_inclusion (Γ : Context.{u}) (φ : Cofibration Γ) :
    extraOperation .inclusion ![.context Γ,.cofibration Γ φ] =
      .substitution (restrictContext φ) Γ (restrictInclusion φ) := by
  simp [extraOperation,Value.cofibrationAt_cofibration]
@[simp] theorem extra_subFace (Γ Δ : Context.{u}) (φ : Cofibration Γ) (σ : Δ ⟶ Γ) :
    extraOperation .subFace ![.context Δ,.context Γ,.cofibration Γ φ,.substitution Δ Γ σ] =
      .cofibration Δ (φ.reindex σ) := by
  simp [extraOperation,Value.cofibrationAt_cofibration,Value.substitutionAt_substitution]
@[simp] theorem extra_restrictedSub (Γ Δ : Context.{u}) (φ : Cofibration Γ) (σ : Δ ⟶ Γ) :
    extraOperation .restrictedSub ![.context Δ,.context Γ,.cofibration Γ φ,.substitution Δ Γ σ] =
      .substitution (restrictContext (φ.reindex σ)) (restrictContext φ) (restrictSubstitution φ σ) := by
  simp [extraOperation,Value.cofibrationAt_cofibration,Value.substitutionAt_substitution]
@[simp] theorem extra_subProvider (Γ Δ : Context.{u}) (A : Family Γ) (F : Filling A) (σ : Δ ⟶ Γ) :
    extraOperation .subProvider ![.context Δ,.context Γ,.filling Γ A F,.substitution Δ Γ σ] =
      .filling Δ (reindex A σ) (F.reindex σ) := by
  simp [extraOperation,Value.fillingIn_filling,Value.substitutionAt_substitution]

@[simp] theorem extra_hcomp (Γ : Context.{u}) (A : Family Γ) (F : Filling A) (φ : Cofibration Γ)
    (b : OpenBox (reindex A (Presheaf.projection (Presheaf.interval Γ))) φ) :
    extraOperation .hcomp ![.context Γ,.family Γ A,.filling Γ A F,.cofibration Γ φ,
      .term (restrictContext (φ.reindex (Presheaf.projection (Presheaf.interval Γ))))
        (reindex (reindex A (Presheaf.projection (Presheaf.interval Γ)))
          (restrictInclusion (φ.reindex (Presheaf.projection (Presheaf.interval Γ))))) b.tube.toRestricted,
      .term Γ A b.base] = .term Γ A (F.hcomp φ b) := by
  classical
  simp [extraOperation,Value.familyAt_family,Value.fillingAt_filling,
    Value.cofibrationAt_cofibration,Value.termAt_term]
  split
  · rfl
  · next h => exact False.elim (h b.boundary)

@[simp] theorem extra_transp (Γ : Context.{u}) (B : Family (total (Presheaf.interval Γ)))
    (F : Filling B) (φ : Cofibration Γ) (h : RestrictedConstancy B φ)
    (a : Presheaf.Term (reindex B (Presheaf.endpointSub Γ false))) :
    extraOperation .transp ![.context Γ,.family (total (Presheaf.interval Γ)) B,
      .filling (total (Presheaf.interval Γ)) B F,.cofibration Γ φ,
      .term Γ (reindex B (Presheaf.endpointSub Γ false)) a] =
      .term Γ (reindex B (Presheaf.endpointSub Γ true)) (F.transp φ h a) := by
  simp [extraOperation,Value.familyAt_family,Value.fillingAt_filling,Value.cofibrationAt_cofibration,
    Value.termAt_term,h]

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

theorem intervalContext_eval {V : Type} (γ : Expression V) (ρ : V → Value.{u})
    (Γ : Context.{u}) (hΓ : γ.eval algebra ρ = .context Γ) :
    (intervalContext γ).eval algebra ρ = .context (total (Presheaf.interval Γ)) := by
  change Source.operation .extend ![γ.eval algebra ρ,Intervals.extraOperation .interval ![γ.eval algebra ρ]] = _
  rw [hΓ,Intervals.extra_interval]
  simp [Source.operation,Value.familyAt_family]

theorem projection_eval {V : Type} (γ : Expression V) (ρ : V → Value.{u})
    (Γ : Context.{u}) (hΓ : γ.eval algebra ρ = .context Γ) :
    (projection γ).eval algebra ρ =
      .substitution (total (Presheaf.interval Γ)) Γ (Presheaf.projection (Presheaf.interval Γ)) := by
  change Source.operation .weaken ![γ.eval algebra ρ,Intervals.extraOperation .interval ![γ.eval algebra ρ]] = _
  rw [hΓ,Intervals.extra_interval]
  simp [Source.operation,Value.familyAt_family]

end SquareKit.Cubical.Source.Fillings
