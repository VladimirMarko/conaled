import SquareKit.Internal.Cubical.Judgments.PathsInputs

namespace SquareKit.Cubical.Source.Paths
set_option backward.isDefEq.respectTransparency false
open GuardedTheory Presheaf
universe u

theorem formation_valid : Satisfies algebra.{u} formationRule := by
  apply formationSchema_valid
  intro Γ B a₀ a₁
  exact ⟨Γ,normalizedPath B a₀ a₁,rfl,extra_path Γ B a₀ a₁⟩

theorem lam_valid : Satisfies algebra.{u} lamRule := by
  apply bodySchema_valid
  intro Γ B a₀ a₁ b h₀ h₁
  exact ⟨Γ,normalizedPath B a₀ a₁,normalizedPathLam b h₀ h₁,rfl,
    extra_path Γ B a₀ a₁,extra_lam Γ B a₀ a₁ b h₀ h₁⟩

theorem app_valid : Satisfies algebra.{u} appRule := by
  apply functionSchema_valid
  intro Γ B a₀ a₁ p
  refine ⟨total (Presheaf.interval Γ),B,normalizedPathApp p,?_,rfl,extra_app Γ B a₀ a₁ p⟩
  change Source.operation .extend ![.context Γ,Intervals.extraOperation .interval ![.context Γ]] = _
  rw [Intervals.extra_interval]
  simp [Source.operation]

theorem beta_valid : Satisfies algebra.{u} betaRule := by
  apply bodySchema_valid
  intro Γ B a₀ a₁ b h₀ h₁
  change extraOperation .app ![.context Γ,.family (total (Presheaf.interval Γ)) B,
    .term Γ (reindex B (Presheaf.endpointSub Γ false)) a₀,
    .term Γ (reindex B (Presheaf.endpointSub Γ true)) a₁,
    extraOperation .lam ![.context Γ,.family (total (Presheaf.interval Γ)) B,
      .term Γ (reindex B (Presheaf.endpointSub Γ false)) a₀,
      .term Γ (reindex B (Presheaf.endpointSub Γ true)) a₁,.term (total (Presheaf.interval Γ)) B b]] = _
  rw [extra_lam Γ B a₀ a₁ b h₀ h₁,extra_app,normalizedPathApp_lam]
  rfl

theorem eta_valid : Satisfies algebra.{u} etaRule := by
  apply functionSchema_valid
  intro Γ B a₀ a₁ p
  change extraOperation .lam ![.context Γ,.family (total (Presheaf.interval Γ)) B,
    .term Γ (reindex B (Presheaf.endpointSub Γ false)) a₀,
    .term Γ (reindex B (Presheaf.endpointSub Γ true)) a₁,
    extraOperation .app ![.context Γ,.family (total (Presheaf.interval Γ)) B,
      .term Γ (reindex B (Presheaf.endpointSub Γ false)) a₀,
      .term Γ (reindex B (Presheaf.endpointSub Γ true)) a₁,.term Γ (normalizedPath B a₀ a₁) p]] = _
  rw [extra_app,extra_lam Γ B a₀ a₁ (normalizedPathApp p)
    (normalizedPathApp_zero p) (normalizedPathApp_one p),normalizedPathLam_app]
  rfl

theorem endpoint_valid (b : Bool) : Satisfies algebra.{u} (endpointRule b) := by
  apply functionSchema_valid
  intro Γ B a₀ a₁ p
  have he := endpointSub_eval (.var (0 : Fin 5))
    ![.context Γ,.family (total (Presheaf.interval Γ)) B,
      .term Γ (reindex B (Presheaf.endpointSub Γ false)) a₀,
      .term Γ (reindex B (Presheaf.endpointSub Γ true)) a₁,.term Γ (normalizedPath B a₀ a₁) p] Γ rfl b
  change Source.operation .subTm ![extraOperation .app ![.context Γ,.family (total (Presheaf.interval Γ)) B,
      .term Γ (reindex B (Presheaf.endpointSub Γ false)) a₀,
      .term Γ (reindex B (Presheaf.endpointSub Γ true)) a₁,.term Γ (normalizedPath B a₀ a₁) p],
    (endpointSub (.var (0 : Fin 5)) b).eval algebra _] = _
  rw [he,extra_app]
  simp only [Source.operation,Matrix.cons_val_zero,Matrix.cons_val_one,Value.termIn_term]
  cases b
  · exact congrArg (Value.term Γ (reindex B (Presheaf.endpointSub Γ false))) (normalizedPathApp_zero p)
  · exact congrArg (Value.term Γ (reindex B (Presheaf.endpointSub Γ true))) (normalizedPathApp_one p)

end SquareKit.Cubical.Source.Paths
