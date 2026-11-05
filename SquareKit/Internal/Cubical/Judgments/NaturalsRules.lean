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

end SquareKit.Cubical.Source.Naturals
