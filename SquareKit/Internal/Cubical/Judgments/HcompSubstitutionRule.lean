import SquareKit.Internal.Cubical.Judgments.FillingSubstitutionInputs
import SquareKit.Internal.Cubical.Judgments.FillingLiftEvaluation

namespace SquareKit.Cubical.Source.Fillings
set_option backward.isDefEq.respectTransparency false
open GuardedTheory Presheaf CategoryTheory
universe u

theorem hcompSub_valid : Satisfies algebra.{u} hcompSubRule := by
  apply hcompSubSchema_valid
  intro Γ Δ A F φ b σ hF
  let ρ : Fin 8 → Value := ![.context Γ,.context Δ,.family Γ A,.filling Γ A F,.cofibration Γ φ,
    .term (restrictContext (φ.reindex (Presheaf.projection (Presheaf.interval Γ))))
      (reindex (reindex A (Presheaf.projection (Presheaf.interval Γ)))
        (restrictInclusion (φ.reindex (Presheaf.projection (Presheaf.interval Γ))))) b.tube.toRestricted,
    .term Γ A b.base,.substitution Δ Γ σ]
  have hl := lift_eval (.var 1) (.var 0) (.var 7) ρ Γ Δ σ rfl rfl rfl
  have hIΓ := intervalContext_eval (.var (0 : Fin 8)) ρ Γ rfl
  have hIΔ := intervalContext_eval (.var (1 : Fin 8)) ρ Δ rfl
  have hφ := intervalFace_eval (.var (0 : Fin 8)) (.var 4) ρ Γ φ rfl rfl
  have hsub : (restrictedSub (intervalContext (.var (1 : Fin 8))) (intervalContext (.var 0))
      (intervalFace (.var 0) (.var 4)) (lift (.var 1) (.var 0) (.var 7))).eval algebra ρ =
      .substitution (restrictContext ((φ.reindex (Presheaf.projection (Presheaf.interval Γ))).reindex
        (liftSub (Presheaf.interval Γ) σ)))
        (restrictContext (φ.reindex (Presheaf.projection (Presheaf.interval Γ))))
        (restrictSubstitution (φ.reindex (Presheaf.projection (Presheaf.interval Γ)))
          (liftSub (Presheaf.interval Γ) σ)) := by
    change extraOperation .restrictedSub ![(intervalContext (.var 1)).eval algebra ρ,
      (intervalContext (.var 0)).eval algebra ρ,(intervalFace (.var 0) (.var 4)).eval algebra ρ,
      (lift (.var 1) (.var 0) (.var 7)).eval algebra ρ] = _
    rw [hIΔ,hIΓ,hφ,hl,extra_restrictedSub]
  change Source.operation .subTm ![extraOperation .hcomp ![.context Γ,.family Γ A,.filling Γ A F,
    .cofibration Γ φ,.term _ _ b.tube.toRestricted,.term Γ A b.base],.substitution Δ Γ σ] =
    extraOperation .hcomp ![.context Δ,
      Source.operation .subTy ![.family Γ A,.substitution Δ Γ σ],
      extraOperation .subProvider ![.context Δ,.context Γ,.filling Γ A F,.substitution Δ Γ σ],
      extraOperation .subFace ![.context Δ,.context Γ,.cofibration Γ φ,.substitution Δ Γ σ],
      Source.operation .subTm ![.term _ _ b.tube.toRestricted,
        (restrictedSub (intervalContext (.var 1)) (intervalContext (.var 0))
          (intervalFace (.var 0) (.var 4)) (lift (.var 1) (.var 0) (.var 7))).eval algebra ρ],
      Source.operation .subTm ![.term Γ A b.base,.substitution Δ Γ σ]]
  rw [hsub,extra_hcomp Γ A F φ b,extra_subProvider,extra_subFace]
  simp only [Source.operation,Matrix.cons_val_zero,Matrix.cons_val_one,Value.termIn_term,
    Value.familyAt_family]
  exact (congrArg (Value.term Δ (reindex A σ)) (Filling.hcomp_reindex hF φ b σ).symm).trans
    (extra_hcomp Δ (reindex A σ) (F.reindex σ) (φ.reindex σ) (b.reindex σ)).symm

end SquareKit.Cubical.Source.Fillings
