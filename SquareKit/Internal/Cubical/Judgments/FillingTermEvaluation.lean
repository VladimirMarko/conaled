import SquareKit.Internal.Cubical.Judgments.FillingRestrictedEvaluation

namespace SquareKit.Cubical.Source.Fillings
set_option backward.isDefEq.respectTransparency false
open GuardedTheory Presheaf CategoryTheory
universe u
variable {V : Type}

theorem subTy_eval (a τ : Expression V) (ρ : V → Value.{u})
    (Γ Δ : Context.{u}) (A : Family Γ) (σ : Δ ⟶ Γ)
    (hA : a.eval algebra ρ = .family Γ A)
    (hσ : τ.eval algebra ρ = .substitution Δ Γ σ) :
    (subTy a τ).eval algebra ρ = .family Δ (reindex A σ) := by
  change Source.operation .subTy ![a.eval algebra ρ,τ.eval algebra ρ] = _
  rw [hA,hσ]
  simp [Source.operation,Value.familyAt_family]

theorem subTm_eval (a τ : Expression V) (ρ : V → Value.{u})
    (Γ Δ : Context.{u}) (A : Family Γ) (t : Presheaf.Term A) (σ : Δ ⟶ Γ)
    (ht : a.eval algebra ρ = .term Γ A t)
    (hσ : τ.eval algebra ρ = .substitution Δ Γ σ) :
    (subTm a τ).eval algebra ρ = .term Δ (reindex A σ) (t.reindex σ) := by
  change Source.operation .subTm ![a.eval algebra ρ,τ.eval algebra ρ] = _
  rw [ht,hσ]
  simp [Source.operation,Value.termIn_term]

theorem inclusion_eval (γ p : Expression V) (ρ : V → Value.{u})
    (Γ : Context.{u}) (φ : Cofibration Γ)
    (hΓ : γ.eval algebra ρ = .context Γ) (hφ : p.eval algebra ρ = .cofibration Γ φ) :
    (inclusion γ p).eval algebra ρ = .substitution (restrictContext φ) Γ (restrictInclusion φ) := by
  change extraOperation .inclusion ![γ.eval algebra ρ,p.eval algebra ρ] = _
  rw [hΓ,hφ,extra_inclusion]

theorem tubeEndpoint_eval (γ p t : Expression V) (ρ : V → Value.{u})
    (Γ : Context.{u}) (B : Family (total (Presheaf.interval Γ))) (φ : Cofibration Γ)
    (s : Presheaf.Term (reindex B (restrictInclusion (φ.reindex (Presheaf.projection (Presheaf.interval Γ))))))
    (hΓ : γ.eval algebra ρ = .context Γ) (hφ : p.eval algebra ρ = .cofibration Γ φ)
    (hs : t.eval algebra ρ = .term (restrictContext (φ.reindex (Presheaf.projection (Presheaf.interval Γ)))) _ s)
    (b : Bool) :
    (tubeEndpoint γ p t b).eval algebra ρ =
      .term (restrictContext φ) (reindex (reindex B (Presheaf.endpointSub Γ b)) (restrictInclusion φ))
        (s.reindex (restrictSubstitution (φ.reindex (Presheaf.projection (Presheaf.interval Γ)))
          (Presheaf.endpointSub Γ b))) := by
  apply subTm_eval t _ ρ _ (restrictContext φ) _ s
    (restrictSubstitution (φ.reindex (Presheaf.projection (Presheaf.interval Γ))) (Presheaf.endpointSub Γ b)) hs
  change extraOperation .restrictedSub ![γ.eval algebra ρ,(intervalContext γ).eval algebra ρ,
    (intervalFace γ p).eval algebra ρ,(endpointSub γ b).eval algebra ρ] = _
  rw [intervalContext_eval γ ρ Γ hΓ,intervalFace_eval γ p ρ Γ φ hΓ hφ,
    endpointSub_eval γ ρ Γ hΓ b,hΓ,extra_restrictedSub]
  rfl

end SquareKit.Cubical.Source.Fillings
