import SquareKit.Internal.Cubical.Judgments.SumsRules

namespace SquareKit.Cubical.Source.Sums
set_option backward.isDefEq.respectTransparency false
open GuardedTheory Presheaf CategoryTheory
universe u

abbrev substitutionEnvironment (Γ Δ : Context.{u}) (A : Family Γ) (B : Family (total A)) (σ : Δ ⟶ Γ) :
    Fin 5 → Value.{u} := ![.context Γ,.context Δ,.family Γ A,.family (total A) B,.substitution Δ Γ σ]

theorem liftA_eval (Γ Δ : Context.{u}) (A : Family Γ) (B : Family (total A)) (σ : Δ ⟶ Γ) :
    (lift (.var 1) (.var 2) (.var 4)).eval algebra (substitutionEnvironment Γ Δ A B σ) =
      .substitution (total (reindex A σ)) (total A) (liftSub A σ) :=
  lift_eval _ _ _ _ Γ Δ A σ rfl rfl rfl

theorem liftSigma_eval (Γ Δ : Context.{u}) (A : Family Γ) (B : Family (total A)) (σ : Δ ⟶ Γ) :
    (lift (.var 1) (sigma (.var 2) (.var 3)) (.var 4)).eval algebra (substitutionEnvironment Γ Δ A B σ) =
      .substitution (total (reindex (Presheaf.sigma A B) σ)) (total (Presheaf.sigma A B))
        (liftSub (Presheaf.sigma A B) σ) :=
  lift_eval _ _ _ _ Γ Δ (Presheaf.sigma A B) σ rfl (extra_sigma Γ A B) rfl

theorem liftB_eval (Γ Δ : Context.{u}) (A : Family Γ) (B : Family (total A)) (σ : Δ ⟶ Γ) :
    (lift (extend (.var 1) (subTy (.var 2) (.var 4))) (.var 3) (lift (.var 1) (.var 2) (.var 4))).eval
      algebra (substitutionEnvironment Γ Δ A B σ) =
      .substitution (total (reindex B (liftSub A σ))) (total B) (liftSub B (liftSub A σ)) := by
  apply lift_eval _ _ _ _ (total A) (total (reindex A σ)) B (liftSub A σ)
  · change Source.operation .extend ![.context Δ,Source.operation .subTy ![.family Γ A,.substitution Δ Γ σ]] = _
    simp [Source.operation]
  · rfl
  · exact liftA_eval Γ Δ A B σ

theorem packSub_valid : Satisfies algebra.{u} packSubRule := by
  apply substitutionSchema_valid
  intro Γ Δ A B σ
  let ρ := substitutionEnvironment Γ Δ A B σ
  change Source.operation .comp ![(lift (.var 1) (sigma (.var 2) (.var 3)) (.var 4)).eval algebra ρ,
    extraOperation .pack ![Source.operation .subTy ![.family Γ A,.substitution Δ Γ σ],
      Source.operation .subTy ![.family (total A) B,(lift (.var 1) (.var 2) (.var 4)).eval algebra ρ]]] =
    Source.operation .comp ![extraOperation .pack ![.family Γ A,.family (total A) B],
      (lift (extend (.var 1) (subTy (.var 2) (.var 4))) (.var 3) (lift (.var 1) (.var 2) (.var 4))).eval algebra ρ]
  rw [liftSigma_eval,liftA_eval,liftB_eval,extra_pack]
  simp only [Source.operation,Matrix.cons_val_zero,Matrix.cons_val_one,Value.familyAt_family,
    Value.substitutionAt_substitution]
  rw [extra_pack]
  have ht : Value.substitutionAt (total (reindex B (liftSub A σ))) (total (reindex (Presheaf.sigma A B) σ))
      (.substitution (total (reindex B (liftSub A σ)))
        (total (Presheaf.sigma (reindex A σ) (reindex B (liftSub A σ))))
        (sigmaPack (reindex A σ) (reindex B (liftSub A σ)))) =
      some (sigmaPack (reindex A σ) (reindex B (liftSub A σ))) := Value.substitutionAt_substitution _ _ _
  dsimp only at *
  rw [ht]
  rfl

theorem unpackSub_valid : Satisfies algebra.{u} unpackSubRule := by
  apply substitutionSchema_valid
  intro Γ Δ A B σ
  let ρ := substitutionEnvironment Γ Δ A B σ
  change Source.operation .comp ![
      (lift (extend (.var 1) (subTy (.var 2) (.var 4))) (.var 3) (lift (.var 1) (.var 2) (.var 4))).eval algebra ρ,
      extraOperation .unpack ![Source.operation .subTy ![.family Γ A,.substitution Δ Γ σ],
        Source.operation .subTy ![.family (total A) B,(lift (.var 1) (.var 2) (.var 4)).eval algebra ρ]]] =
    Source.operation .comp ![extraOperation .unpack ![.family Γ A,.family (total A) B],
      (lift (.var 1) (sigma (.var 2) (.var 3)) (.var 4)).eval algebra ρ]
  rw [liftB_eval,liftA_eval,liftSigma_eval,extra_unpack]
  simp only [Source.operation,Matrix.cons_val_zero,Matrix.cons_val_one,Value.familyAt_family,
    Value.substitutionAt_substitution]
  rw [extra_unpack]
  simp only [Value.substitutionAt_substitution]
  rfl

end SquareKit.Cubical.Source.Sums
