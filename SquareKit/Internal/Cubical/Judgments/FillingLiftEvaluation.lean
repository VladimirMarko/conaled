import SquareKit.Internal.Cubical.Judgments.FillingTermEvaluation

namespace SquareKit.Cubical.Source.Fillings
set_option backward.isDefEq.respectTransparency false
open GuardedTheory Presheaf CategoryTheory
universe u

theorem lift_eval {V : Type} (δ γ τ : Expression V) (ρ : V → Value.{u})
    (Γ Δ : Context.{u}) (σ : Δ ⟶ Γ)
    (hΔ : δ.eval algebra ρ = .context Δ) (hΓ : γ.eval algebra ρ = .context Γ)
    (hσ : τ.eval algebra ρ = .substitution Δ Γ σ) :
    (lift δ γ τ).eval algebra ρ =
      .substitution (total (Presheaf.interval Δ)) (total (Presheaf.interval Γ)) (liftSub (Presheaf.interval Γ) σ) := by
  change Source.operation .pair ![Intervals.extraOperation .interval ![γ.eval algebra ρ],
    Source.operation .comp ![τ.eval algebra ρ,
      Source.operation .weaken ![δ.eval algebra ρ,Intervals.extraOperation .interval ![δ.eval algebra ρ]]],
    Source.operation .generic ![δ.eval algebra ρ,Intervals.extraOperation .interval ![δ.eval algebra ρ]]] = _
  rw [hΔ,hΓ,hσ,Intervals.extra_interval,Intervals.extra_interval]
  simp only [Source.operation,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.head_cons,Matrix.tail_cons,Value.familyAt_family,Value.substitutionAt_substitution]
  have ht : Value.termAt (total (Presheaf.interval Δ))
      (Semantics.subTy (Presheaf.interval Γ)
        (Semantics.compSub σ (Presheaf.projection (Presheaf.interval Δ))))
      (.term (total (Presheaf.interval Δ))
        (reindex (Presheaf.interval Δ) (Presheaf.projection (Presheaf.interval Δ)))
        (Presheaf.generic (Presheaf.interval Δ))) = some (Presheaf.generic (Presheaf.interval Δ)) :=
    Value.termAt_term _ _ _
  rw [ht]
  rfl

end SquareKit.Cubical.Source.Fillings
