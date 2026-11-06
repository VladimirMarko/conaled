import SquareKit.Internal.Cubical.Judgments.PathsSubstitutionInputs

namespace SquareKit.Cubical.Source.Paths
set_option backward.isDefEq.respectTransparency false
open GuardedTheory Presheaf
universe u

theorem pathSub_valid : Satisfies algebra.{u} pathSubRule := by
  apply substitutionSchema_valid
  intro Γ Δ B a₀ a₁ σ
  let ρ : Fin 6 → Value := ![.context Γ,.context Δ,.family (total (Presheaf.interval Γ)) B,
    .term Γ (reindex B (Presheaf.endpointSub Γ false)) a₀,
    .term Γ (reindex B (Presheaf.endpointSub Γ true)) a₁,.substitution Δ Γ σ]
  have hl := lift_eval (.var 1) (interval (.var 0)) (.var 5) ρ Γ Δ (Presheaf.interval Γ) σ rfl rfl rfl
  change Source.operation .subTy ![extraOperation .path ![.context Γ,.family (total (Presheaf.interval Γ)) B,
      .term Γ (reindex B (Presheaf.endpointSub Γ false)) a₀,
      .term Γ (reindex B (Presheaf.endpointSub Γ true)) a₁],.substitution Δ Γ σ] =
    extraOperation .path ![.context Δ,Source.operation .subTy ![.family (total (Presheaf.interval Γ)) B,
      (lift (.var 1) (interval (.var 0)) (.var 5)).eval algebra ρ],
      Source.operation .subTm ![.term Γ (reindex B (Presheaf.endpointSub Γ false)) a₀,.substitution Δ Γ σ],
      Source.operation .subTm ![.term Γ (reindex B (Presheaf.endpointSub Γ true)) a₁,.substitution Δ Γ σ]]
  rw [hl,extra_path]
  simp only [Source.operation,Matrix.cons_val_zero,Matrix.cons_val_one,Value.familyAt_family,Value.termIn_term]
  exact (congrArg (Value.family Δ) (normalizedPath_reindex B a₀ a₁ σ)).trans
    (extra_path Δ (reindex B (liftSub (Presheaf.interval Γ) σ)) (a₀.reindex σ) (a₁.reindex σ)).symm

private theorem convert_heq {Γ : Context.{u}} {A B : Family Γ} (h : A = B)
    (t : Presheaf.Term A) : HEq (t.convert h) t := by cases h; rfl

theorem lamSub_valid : Satisfies algebra.{u} lamSubRule := by
  apply bodySubstitutionSchema_valid
  intro Γ Δ B a₀ a₁ b σ h₀ h₁
  let ρ : Fin 7 → Value := ![.context Γ,.context Δ,.family (total (Presheaf.interval Γ)) B,
    .term Γ (reindex B (Presheaf.endpointSub Γ false)) a₀,
    .term Γ (reindex B (Presheaf.endpointSub Γ true)) a₁,.term (total (Presheaf.interval Γ)) B b,.substitution Δ Γ σ]
  have hl := lift_eval (.var 1) (interval (.var 0)) (.var 6) ρ Γ Δ (Presheaf.interval Γ) σ rfl rfl rfl
  change Source.operation .subTm ![extraOperation .lam ![.context Γ,.family (total (Presheaf.interval Γ)) B,
      .term Γ (reindex B (Presheaf.endpointSub Γ false)) a₀,
      .term Γ (reindex B (Presheaf.endpointSub Γ true)) a₁,.term (total (Presheaf.interval Γ)) B b],.substitution Δ Γ σ] =
    extraOperation .lam ![.context Δ,Source.operation .subTy ![.family (total (Presheaf.interval Γ)) B,
      (lift (.var 1) (interval (.var 0)) (.var 6)).eval algebra ρ],
      Source.operation .subTm ![.term Γ (reindex B (Presheaf.endpointSub Γ false)) a₀,.substitution Δ Γ σ],
      Source.operation .subTm ![.term Γ (reindex B (Presheaf.endpointSub Γ true)) a₁,.substitution Δ Γ σ],
      Source.operation .subTm ![.term (total (Presheaf.interval Γ)) B b,
        (lift (.var 1) (interval (.var 0)) (.var 6)).eval algebra ρ]]
  rw [hl,extra_lam Γ B a₀ a₁ b h₀ h₁]
  simp only [Source.operation,Matrix.cons_val_zero,Matrix.cons_val_one,Value.familyAt_family,Value.termIn_term]
  have he := (convert_heq (normalizedPath_reindex B a₀ a₁ σ) ((normalizedPathLam b h₀ h₁).reindex σ)).symm.trans
    (heq_of_eq (normalizedPathLam_reindex b h₀ h₁ σ))
  exact (Value.term_eq (normalizedPath_reindex B a₀ a₁ σ) he).trans
    (extra_lam Δ (reindex B (liftSub (Presheaf.interval Γ) σ)) (a₀.reindex σ) (a₁.reindex σ)
      (b.reindex (liftSub (Presheaf.interval Γ) σ))
      (congrArg (fun t => t.reindex σ) h₀) (congrArg (fun t => t.reindex σ) h₁)).symm

theorem appSub_valid : Satisfies algebra.{u} appSubRule := by
  apply functionSubstitutionSchema_valid
  intro Γ Δ B a₀ a₁ p σ
  let ρ : Fin 7 → Value := ![.context Γ,.context Δ,.family (total (Presheaf.interval Γ)) B,
    .term Γ (reindex B (Presheaf.endpointSub Γ false)) a₀,
    .term Γ (reindex B (Presheaf.endpointSub Γ true)) a₁,.term Γ (normalizedPath B a₀ a₁) p,.substitution Δ Γ σ]
  have hl := lift_eval (.var 1) (interval (.var 0)) (.var 6) ρ Γ Δ (Presheaf.interval Γ) σ rfl rfl rfl
  change Source.operation .subTm ![extraOperation .app ![.context Γ,.family (total (Presheaf.interval Γ)) B,
      .term Γ (reindex B (Presheaf.endpointSub Γ false)) a₀,
      .term Γ (reindex B (Presheaf.endpointSub Γ true)) a₁,.term Γ (normalizedPath B a₀ a₁) p],
      (lift (.var 1) (interval (.var 0)) (.var 6)).eval algebra ρ] =
    extraOperation .app ![.context Δ,Source.operation .subTy ![.family (total (Presheaf.interval Γ)) B,
      (lift (.var 1) (interval (.var 0)) (.var 6)).eval algebra ρ],
      Source.operation .subTm ![.term Γ (reindex B (Presheaf.endpointSub Γ false)) a₀,.substitution Δ Γ σ],
      Source.operation .subTm ![.term Γ (reindex B (Presheaf.endpointSub Γ true)) a₁,.substitution Δ Γ σ],
      Source.operation .subTm ![.term Γ (normalizedPath B a₀ a₁) p,.substitution Δ Γ σ]]
  rw [hl,extra_app]
  simp only [Source.operation,Matrix.cons_val_zero,Matrix.cons_val_one,Value.familyAt_family,Value.termIn_term]
  have ht : Value.term Δ (reindex (normalizedPath B a₀ a₁) σ) (p.reindex σ) =
      .term Δ (normalizedPath (reindex B (liftSub (Presheaf.interval Γ) σ)) (a₀.reindex σ) (a₁.reindex σ))
        ((p.reindex σ).convert (normalizedPath_reindex B a₀ a₁ σ)) :=
    Value.term_eq (normalizedPath_reindex B a₀ a₁ σ) (convert_heq _ _).symm
  rw [ht]
  exact (congrArg (Value.term (total (Presheaf.interval Δ)) (reindex B (liftSub (Presheaf.interval Γ) σ)))
    (normalizedPathApp_reindex p σ).symm).trans
      (extra_app Δ (reindex B (liftSub (Presheaf.interval Γ) σ)) (a₀.reindex σ) (a₁.reindex σ)
        ((p.reindex σ).convert (normalizedPath_reindex B a₀ a₁ σ))).symm

end SquareKit.Cubical.Source.Paths
