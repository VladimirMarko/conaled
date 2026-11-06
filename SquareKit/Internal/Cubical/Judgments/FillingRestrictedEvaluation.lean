import SquareKit.Internal.Cubical.Judgments.FillingEvaluation

namespace SquareKit.Cubical.Source.Fillings
set_option backward.isDefEq.respectTransparency false
open GuardedTheory Presheaf CategoryTheory
universe u
variable {V : Type}

theorem intervalFace_eval (γ p : Expression V) (ρ : V → Value.{u})
    (Γ : Context.{u}) (φ : Cofibration Γ)
    (hΓ : γ.eval algebra ρ = .context Γ) (hφ : p.eval algebra ρ = .cofibration Γ φ) :
    (intervalFace γ p).eval algebra ρ =
      .cofibration (total (Presheaf.interval Γ)) (φ.reindex (Presheaf.projection (Presheaf.interval Γ))) := by
  change extraOperation .subFace ![(intervalContext γ).eval algebra ρ,γ.eval algebra ρ,p.eval algebra ρ,
    (projection γ).eval algebra ρ] = _
  rw [intervalContext_eval γ ρ Γ hΓ,projection_eval γ ρ Γ hΓ,hΓ,hφ,extra_subFace]

theorem restrictedType_eval (γ a p : Expression V) (ρ : V → Value.{u})
    (Γ : Context.{u}) (A : Family Γ) (φ : Cofibration Γ)
    (hΓ : γ.eval algebra ρ = .context Γ) (hA : a.eval algebra ρ = .family Γ A)
    (hφ : p.eval algebra ρ = .cofibration Γ φ) :
    (subTy a (inclusion γ p)).eval algebra ρ = .family (restrictContext φ) (reindex A (restrictInclusion φ)) := by
  change Source.operation .subTy ![a.eval algebra ρ,extraOperation .inclusion ![γ.eval algebra ρ,p.eval algebra ρ]] = _
  rw [hΓ,hA,hφ,extra_inclusion]
  simp [Source.operation,Value.familyAt_family]

theorem restrictedTerm_input (γ a p t : Expression V) (ρ : V → Value.{u})
    (Γ : Context.{u}) (A : Family Γ) (φ : Cofibration Γ)
    (hΓ : γ.eval algebra ρ = .context Γ) (hA : a.eval algebra ρ = .family Γ A)
    (hφ : p.eval algebra ρ = .cofibration Γ φ)
    (h : (restrictedTerm γ a p t).eval algebra ρ) :
    ∃ s : Presheaf.Term (reindex A (restrictInclusion φ)),
      t.eval algebra ρ = .term (restrictContext φ) (reindex A (restrictInclusion φ)) s := by
  change Source.predicate .term ![extraOperation .restriction ![γ.eval algebra ρ,p.eval algebra ρ],
    (subTy a (inclusion γ p)).eval algebra ρ,t.eval algebra ρ] at h
  rw [restrictedType_eval γ a p ρ Γ A φ hΓ hA hφ,hΓ,hφ,extra_restriction] at h
  exact Value.term_input _ _ _ h

end SquareKit.Cubical.Source.Fillings
