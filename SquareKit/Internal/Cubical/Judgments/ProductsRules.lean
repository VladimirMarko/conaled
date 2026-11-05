import SquareKit.Internal.Cubical.Judgments.ProductsInputs

/-! Validity of independently specified dependent product judgments in the
constructed normalized presheaf interpretation. -/
namespace SquareKit.Cubical.Source.Products
set_option backward.isDefEq.respectTransparency false
open GuardedTheory Presheaf
universe u

local macro "eval_simp" : tactic => `(tactic|
  simp [GuardedTheory.Term.eval, algebra, Source.operation])

theorem formation_valid : Satisfies algebra.{u} formationRule := by
  apply formationSchema_valid
  intro Γ A B
  refine ⟨Γ,normalizedPi A B,rfl,?_⟩
  exact extra_pi Γ A B

theorem lam_valid : Satisfies algebra.{u} lamRule := by
  apply bodySchema_valid
  intro Γ A B b
  exact ⟨Γ,normalizedPi A B,normalizedLam b,rfl,extra_pi Γ A B,extra_lam Γ A B b⟩

theorem app_valid : Satisfies algebra.{u} appRule := by
  apply functionSchema_valid
  intro Γ A B p
  refine ⟨total A,B,normalizedApp p,?_,rfl,extra_app Γ A B p⟩
  eval_simp

theorem beta_valid : Satisfies algebra.{u} betaRule := by
  apply bodySchema_valid
  intro Γ A B b
  change extraOperation .app ![.family Γ A,.family (total A) B,
    extraOperation .lam ![.family Γ A,.family (total A) B,.term (total A) B b]] = _
  rw [extra_lam, extra_app, normalizedApp_lam]
  rfl

theorem eta_valid : Satisfies algebra.{u} etaRule := by
  apply functionSchema_valid
  intro Γ A B p
  change extraOperation .lam ![.family Γ A,.family (total A) B,
    extraOperation .app ![.family Γ A,.family (total A) B,.term Γ (normalizedPi A B) p]] = _
  rw [extra_app, extra_lam, normalizedLam_app]
  rfl

theorem piSub_valid : Satisfies algebra.{u} piSubRule := by
  apply substitutionSchema_valid
  intro Γ Δ A B σ
  have hl : (lift (.var 1) (.var 2) (.var 4) : Expression (Fin 5)).eval algebra
      ![.context Γ,.context Δ,.family Γ A,.family (total A) B,.substitution Δ Γ σ] =
      .substitution (total (reindex A σ)) (total A) (liftSub A σ) := lift_eval Γ Δ A σ
  change Source.operation .subTy ![extraOperation .pi ![.family Γ A,.family (total A) B],
      .substitution Δ Γ σ] =
    extraOperation .pi ![Source.operation .subTy ![.family Γ A,.substitution Δ Γ σ],
      Source.operation .subTy ![.family (total A) B,
        (lift (.var 1) (.var 2) (.var 4) : Expression (Fin 5)).eval algebra
          ![.context Γ,.context Δ,.family Γ A,.family (total A) B,.substitution Δ Γ σ]]]
  rw [hl, extra_pi]
  simp only [Source.operation, Matrix.cons_val_zero, Matrix.cons_val_one, Value.familyAt_family]
  exact (congrArg (Value.family Δ) (normalizedPi_reindex A B σ)).trans (extra_pi _ _ _).symm

private theorem convert_heq {Γ : Context.{u}} {A B : Family Γ} (h : A = B)
    (t : Presheaf.Term A) : HEq (t.convert h) t := by cases h; rfl

theorem lamSub_valid : Satisfies algebra.{u} lamSubRule := by
  apply lamSubSchema_valid
  intro Γ Δ A B σ b
  let ρ : Fin 6 → Value := ![.context Γ,.context Δ,.family Γ A,.family (total A) B,
    .term (total A) B b,.substitution Δ Γ σ]
  have hl : (lift (.var 1) (.var 2) (.var 5) : Expression (Fin 6)).eval algebra ρ =
      .substitution (total (reindex A σ)) (total A) (liftSub A σ) := lift_eval Γ Δ A σ
  change Source.operation .subTm ![extraOperation .lam ![.family Γ A,.family (total A) B,
      .term (total A) B b],.substitution Δ Γ σ] =
    extraOperation .lam ![Source.operation .subTy ![.family Γ A,.substitution Δ Γ σ],
      Source.operation .subTy ![.family (total A) B,(lift (.var 1) (.var 2) (.var 5)).eval algebra ρ],
      Source.operation .subTm ![.term (total A) B b,(lift (.var 1) (.var 2) (.var 5)).eval algebra ρ]]
  rw [hl,extra_lam]
  simp only [Source.operation,Matrix.cons_val_zero,Matrix.cons_val_one,Value.familyAt_family,Value.termIn_term]
  have he := (convert_heq (normalizedPi_reindex A B σ) ((normalizedLam b).reindex σ)).symm.trans
    (heq_of_eq (normalizedLam_reindex b σ))
  exact (Value.term_eq (normalizedPi_reindex A B σ) he).trans (extra_lam _ _ _ _).symm

theorem appSub_valid : Satisfies algebra.{u} appSubRule := by
  apply appSubSchema_valid
  intro Γ Δ A B σ p
  let ρ : Fin 6 → Value := ![.context Γ,.context Δ,.family Γ A,.family (total A) B,
    .term Γ (normalizedPi A B) p,.substitution Δ Γ σ]
  have hl : (lift (.var 1) (.var 2) (.var 5) : Expression (Fin 6)).eval algebra ρ =
      .substitution (total (reindex A σ)) (total A) (liftSub A σ) := lift_eval Γ Δ A σ
  change Source.operation .subTm ![extraOperation .app ![.family Γ A,.family (total A) B,
      .term Γ (normalizedPi A B) p],(lift (.var 1) (.var 2) (.var 5)).eval algebra ρ] =
    extraOperation .app ![Source.operation .subTy ![.family Γ A,.substitution Δ Γ σ],
      Source.operation .subTy ![.family (total A) B,(lift (.var 1) (.var 2) (.var 5)).eval algebra ρ],
      Source.operation .subTm ![.term Γ (normalizedPi A B) p,.substitution Δ Γ σ]]
  rw [hl,extra_app]
  simp only [Source.operation,Matrix.cons_val_zero,Matrix.cons_val_one,Value.familyAt_family,Value.termIn_term]
  have ht : Value.term Δ (reindex (normalizedPi A B) σ) (p.reindex σ) =
      .term Δ (normalizedPi (reindex A σ) (reindex B (liftSub A σ)))
        ((p.reindex σ).convert (normalizedPi_reindex A B σ)) :=
    Value.term_eq (normalizedPi_reindex A B σ) (convert_heq _ _).symm
  change Value.term (total (reindex A σ)) (reindex B (liftSub A σ))
      ((normalizedApp p).reindex (liftSub A σ)) =
    extraOperation .app ![.family Δ (reindex A σ),
      .family (total (reindex A σ)) (reindex B (liftSub A σ)),
      .term Δ (reindex (normalizedPi A B) σ) (p.reindex σ)]
  rw [ht,extra_app]
  exact congrArg (Value.term _ _) (normalizedApp_reindex p σ).symm

end SquareKit.Cubical.Source.Products
