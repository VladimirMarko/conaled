import SquareKit.Internal.Cubical.Judgments.FillingSubstitutionInputs
import SquareKit.Internal.Cubical.Judgments.FillingLiftEvaluation

namespace SquareKit.Cubical.Source.Fillings
set_option backward.isDefEq.respectTransparency false
open GuardedTheory Presheaf CategoryTheory
universe u

theorem transpSub_valid : Satisfies algebra.{u} transpSubRule := by
  apply transpSubSchema_valid
  intro Γ Δ B F φ a σ hF hc
  let ρ : Fin 7 → Value := ![.context Γ,.context Δ,.family (total (Presheaf.interval Γ)) B,
    .filling (total (Presheaf.interval Γ)) B F,.cofibration Γ φ,
    .term Γ (reindex B (Presheaf.endpointSub Γ false)) a,.substitution Δ Γ σ]
  have hl := lift_eval (.var 1) (.var 0) (.var 6) ρ Γ Δ σ rfl rfl rfl
  have hIΓ := intervalContext_eval (.var (0 : Fin 7)) ρ Γ rfl
  have hIΔ := intervalContext_eval (.var (1 : Fin 7)) ρ Δ rfl
  change Source.operation .subTm ![extraOperation .transp ![.context Γ,
    .family (total (Presheaf.interval Γ)) B,.filling (total (Presheaf.interval Γ)) B F,
    .cofibration Γ φ,.term Γ (reindex B (Presheaf.endpointSub Γ false)) a],.substitution Δ Γ σ] =
    extraOperation .transp ![.context Δ,
      Source.operation .subTy ![.family (total (Presheaf.interval Γ)) B,(lift (.var 1) (.var 0) (.var 6)).eval algebra ρ],
      extraOperation .subProvider ![(intervalContext (.var 1)).eval algebra ρ,(intervalContext (.var 0)).eval algebra ρ,
        .filling (total (Presheaf.interval Γ)) B F,(lift (.var 1) (.var 0) (.var 6)).eval algebra ρ],
      extraOperation .subFace ![.context Δ,.context Γ,.cofibration Γ φ,.substitution Δ Γ σ],
      Source.operation .subTm ![.term Γ (reindex B (Presheaf.endpointSub Γ false)) a,.substitution Δ Γ σ]]
  rw [hl,hIΓ,hIΔ,extra_transp Γ B F φ hc a,extra_subProvider,extra_subFace]
  simp only [Source.operation,Matrix.cons_val_zero,Matrix.cons_val_one,Value.termIn_term,
    Value.familyAt_family]
  exact (congrArg (Value.term Δ (reindex (reindex B (Presheaf.endpointSub Γ true)) σ))
    (Filling.transp_reindex hF φ hc a σ).symm).trans
      (extra_transp Δ (reindex B (liftSub (Presheaf.interval Γ) σ))
        (F.reindex (liftSub (Presheaf.interval Γ) σ)) (φ.reindex σ) (hc.reindex σ) (a.reindex σ)).symm

end SquareKit.Cubical.Source.Fillings
