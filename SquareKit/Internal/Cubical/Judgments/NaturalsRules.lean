import SquareKit.Internal.Cubical.Judgments.NaturalsInputs

namespace SquareKit.Cubical.Source.Naturals
set_option backward.isDefEq.respectTransparency false
open GuardedTheory Presheaf CategoryTheory
universe u

theorem formation_valid : Satisfies algebra.{u} formationRule := by
  apply contextSchema_valid
  intro Γ
  exact ⟨Γ,natFamily Γ,rfl,rfl⟩

theorem zero_valid : Satisfies algebra.{u} zeroRule := by
  apply contextSchema_valid
  intro Γ
  exact ⟨Γ,natFamily Γ,natZero Γ,rfl,rfl,rfl⟩

theorem successor_valid : Satisfies algebra.{u} successorRule := by
  apply successorSchema_valid
  intro Γ n
  exact ⟨Γ,natFamily Γ,natSucc n,rfl,rfl,extra_succ Γ n⟩

theorem elimination_valid : Satisfies algebra.{u} eliminationRule := by
  apply eliminationSchema_valid
  intro Γ B z s
  refine ⟨total (natFamily Γ),B,natElim z (NatStep.ofTerm s),?_,rfl,extra_elim Γ B z s⟩
  change Source.operation .extend ![.context Γ,extraOperation .nat ![.context Γ]] = _
  rw [extra_nat]
  simp [Source.operation]

theorem zeroBeta_valid : Satisfies algebra.{u} zeroBetaRule := by
  apply eliminationSchema_valid
  intro Γ B z s
  have hz := zeroSub_eval (.var (0 : Fin 4))
    ![.context Γ,.family (total (natFamily Γ)) B,
      .term Γ (reindex B (Presheaf.pair (𝟙 Γ) (natZero Γ))) z,
      .term (total B) (reindex B (projection B ≫ natSuccessorSub Γ)) s] Γ rfl
  change Source.operation .subTm ![extraOperation .elim ![.context Γ,.family (total (natFamily Γ)) B,
      .term Γ (reindex B (Presheaf.pair (𝟙 Γ) (natZero Γ))) z,
      .term (total B) (reindex B (projection B ≫ natSuccessorSub Γ)) s],
    (zeroSub (.var (0 : Fin 4))).eval algebra _] = _
  rw [hz,extra_elim]
  simp only [Source.operation,Matrix.cons_val_zero,Matrix.cons_val_one,Value.termIn_term]
  rfl

theorem successorBeta_valid : Satisfies algebra.{u} successorBetaRule := by
  apply eliminationSchema_valid
  intro Γ B z s
  have hs := successorSub_eval (.var (0 : Fin 4))
    ![.context Γ,.family (total (natFamily Γ)) B,
      .term Γ (reindex B (Presheaf.pair (𝟙 Γ) (natZero Γ))) z,
      .term (total B) (reindex B (projection B ≫ natSuccessorSub Γ)) s] Γ rfl
  let e := extraOperation .elim ![.context Γ,.family (total (natFamily Γ)) B,
    .term Γ (reindex B (Presheaf.pair (𝟙 Γ) (natZero Γ))) z,
    .term (total B) (reindex B (projection B ≫ natSuccessorSub Γ)) s]
  change Source.operation .subTm ![e,(successorSub (.var (0 : Fin 4))).eval algebra _] =
    Source.operation .subTm ![.term (total B) (reindex B (projection B ≫ natSuccessorSub Γ)) s,
      Source.operation .pair ![.family (total (natFamily Γ)) B,
        Source.operation .id ![Source.operation .extend ![.context Γ,extraOperation .nat ![.context Γ]]],e]]
  rw [hs]
  dsimp only [e]
  rw [extra_elim,extra_nat]
  simp only [Source.operation,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.head_cons,Matrix.tail_cons,Value.familyAt_family,Value.substitutionAt_substitution,
    Value.termIn_term]
  have ht : Value.termAt (total (natFamily Γ))
      (Semantics.subTy B (Semantics.idSub (total (natFamily Γ))))
      (.term (total (natFamily Γ)) B (natElim z (NatStep.ofTerm s))) =
      some (natElim z (NatStep.ofTerm s)) := Value.termAt_term _ _ _
  rw [ht]
  simp only [Value.termIn_term]
  rfl

theorem natSub_valid : Satisfies algebra.{u} natSubRule := by
  apply substitutionSchema_valid
  intro Γ Δ σ
  change Source.operation .subTy ![extraOperation .nat ![.context Γ],.substitution Δ Γ σ] = extraOperation .nat ![.context Δ]
  rw [extra_nat,extra_nat]
  simp [Source.operation]

theorem zeroSub_valid : Satisfies algebra.{u} zeroSubRule := by
  apply substitutionSchema_valid
  intro Γ Δ σ
  change Source.operation .subTm ![extraOperation .zero ![.context Γ],.substitution Δ Γ σ] = extraOperation .zero ![.context Δ]
  rw [extra_zero,extra_zero]
  simp [Source.operation]

theorem successorSub_valid : Satisfies algebra.{u} successorSubRule := by
  apply successorSubstitutionSchema_valid
  intro Γ Δ σ n
  change Source.operation .subTm ![extraOperation .succ ![.context Γ,.term Γ (natFamily Γ) n],.substitution Δ Γ σ] =
    extraOperation .succ ![.context Δ,Source.operation .subTm ![.term Γ (natFamily Γ) n,.substitution Δ Γ σ]]
  rw [extra_succ]
  simp only [Source.operation,Matrix.cons_val_zero,Matrix.cons_val_one,Value.termIn_term]
  exact (extra_succ Δ (n.reindex σ)).symm

theorem eliminationSub_valid : Satisfies algebra.{u} eliminationSubRule := by
  apply eliminationSubstitutionSchema_valid
  intro Γ Δ B z s σ
  let ρ : Fin 6 → Value := ![.context Γ,.family (total (natFamily Γ)) B,
    .term Γ (reindex B (Presheaf.pair (𝟙 Γ) (natZero Γ))) z,
    .term (total B) (reindex B (projection B ≫ natSuccessorSub Γ)) s,
    .context Δ,.substitution Δ Γ σ]
  have hn := lift_eval (.var 4) (nat (.var 0)) (.var 5) ρ Γ Δ (natFamily Γ) σ rfl rfl rfl
  have hc : (extend (.var 4) (nat (.var 4))).eval algebra ρ = .context (total (natFamily Δ)) := by
    change Source.operation .extend ![.context Δ,extraOperation .nat ![.context Δ]] = _
    rw [extra_nat]
    simp [Source.operation]
  have hb := lift_eval (extend (.var 4) (nat (.var 4))) (.var 1)
    (lift (.var 4) (nat (.var 0)) (.var 5)) ρ (total (natFamily Γ)) (total (natFamily Δ))
    B (liftSub (natFamily Γ) σ) hc rfl hn
  change Source.operation .subTm ![extraOperation .elim ![ρ 0,ρ 1,ρ 2,ρ 3],
      (lift (.var 4) (nat (.var 0)) (.var 5)).eval algebra ρ] =
    extraOperation .elim ![ρ 4,Source.operation .subTy ![ρ 1,(lift (.var 4) (nat (.var 0)) (.var 5)).eval algebra ρ],
      Source.operation .subTm ![ρ 2,ρ 5],
      Source.operation .subTm ![ρ 3,(lift (extend (.var 4) (nat (.var 4))) (.var 1)
        (lift (.var 4) (nat (.var 0)) (.var 5))).eval algebra ρ]]
  rw [hn,hb]
  change Source.operation .subTm ![extraOperation .elim ![.context Γ,.family (total (natFamily Γ)) B,
      .term Γ (reindex B (Presheaf.pair (𝟙 Γ) (natZero Γ))) z,
      .term (total B) (reindex B (projection B ≫ natSuccessorSub Γ)) s],
      .substitution (total (natFamily Δ)) (total (natFamily Γ)) (liftSub (natFamily Γ) σ)] =
    extraOperation .elim ![.context Δ,Source.operation .subTy ![.family (total (natFamily Γ)) B,
      .substitution (total (natFamily Δ)) (total (natFamily Γ)) (liftSub (natFamily Γ) σ)],
      Source.operation .subTm ![.term Γ (reindex B (Presheaf.pair (𝟙 Γ) (natZero Γ))) z,.substitution Δ Γ σ],
      Source.operation .subTm ![.term (total B) (reindex B (projection B ≫ natSuccessorSub Γ)) s,
        .substitution (total (reindex B (liftSub (natFamily Γ) σ))) (total B) (liftSub B (liftSub (natFamily Γ) σ))]]
  rw [extra_elim]
  simp only [Source.operation,Matrix.cons_val_zero,Matrix.cons_val_one,Value.familyAt_family,Value.termIn_term]
  exact (congrArg (Value.term (total (natFamily Δ)) (reindex B (liftSub (natFamily Γ) σ)))
    (natElim_term_reindex z s σ)).trans
      (extra_elim Δ (reindex B (liftSub (natFamily Γ) σ)) (z.reindex σ)
        (s.reindex (liftSub B (liftSub (natFamily Γ) σ)))).symm

end SquareKit.Cubical.Source.Naturals
