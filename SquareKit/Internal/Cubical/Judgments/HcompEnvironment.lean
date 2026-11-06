import SquareKit.Internal.Cubical.Judgments.FillingTheory

namespace SquareKit.Cubical.Source.Fillings
set_option backward.isDefEq.respectTransparency false
open GuardedTheory Presheaf CategoryTheory
universe u

abbrev hcompEnvironment (Γ : Context.{u}) (A : Family Γ) (F : Filling A) (φ : Cofibration Γ)
    (b : OpenBox (reindex A (Presheaf.projection (Presheaf.interval Γ))) φ) : Fin 6 → Value.{u} :=
  ![.context Γ,.family Γ A,.filling Γ A F,.cofibration Γ φ,
    .term (restrictContext (φ.reindex (Presheaf.projection (Presheaf.interval Γ))))
      (reindex (reindex A (Presheaf.projection (Presheaf.interval Γ)))
        (restrictInclusion (φ.reindex (Presheaf.projection (Presheaf.interval Γ))))) b.tube.toRestricted,
    .term Γ A b.base]

theorem hcompEnvironment_valid (Γ : Context.{u}) (A : Family Γ) (F : Filling A) (φ : Cofibration Γ)
    (b : OpenBox (reindex A (Presheaf.projection (Presheaf.interval Γ))) φ)
    (hF : F.Lawful) (i : Fin 5) :
    (hcompRule.premise i).eval algebra (hcompEnvironment Γ A F φ b) := by
  let ρ := hcompEnvironment Γ A F φ b
  have hI := intervalContext_eval (.var (0 : Fin 6)) ρ Γ rfl
  have hp := projection_eval (.var (0 : Fin 6)) ρ Γ rfl
  have hB := subTy_eval (.var (1 : Fin 6)) (projection (.var 0)) ρ _ _ A _ rfl hp
  have hface := intervalFace_eval (.var (0 : Fin 6)) (.var 3) ρ Γ φ rfl rfl
  fin_cases i
  · exact ⟨Γ,A,F,rfl,rfl,rfl,hF⟩
  · exact ⟨Γ,φ,rfl,rfl⟩
  · refine ⟨restrictContext (φ.reindex (Presheaf.projection (Presheaf.interval Γ))),
      reindex (reindex A (Presheaf.projection (Presheaf.interval Γ)))
        (restrictInclusion (φ.reindex (Presheaf.projection (Presheaf.interval Γ)))),b.tube.toRestricted,?_,?_,rfl⟩
    · change extraOperation .restriction ![(intervalContext (.var 0)).eval algebra ρ,
        (intervalFace (.var 0) (.var 3)).eval algebra ρ] = _
      rw [hI,hface,extra_restriction]
    · exact restrictedType_eval (intervalContext (.var 0)) (subTy (.var 1) (projection (.var 0)))
        (intervalFace (.var 0) (.var 3)) ρ _ _ _ hI hB hface
  · exact ⟨Γ,A,b.base,rfl,rfl,rfl⟩
  · have hzero := tubeEndpoint_eval (.var (0 : Fin 6)) (.var 3) (.var 4) ρ Γ _ φ
      b.tube.toRestricted rfl rfl rfl false
    have hinc := inclusion_eval (.var (0 : Fin 6)) (.var 3) ρ Γ φ rfl rfl
    have hbase := subTm_eval (.var (5 : Fin 6)) (inclusion (.var 0) (.var 3)) ρ Γ _ A b.base _ rfl hinc
    have heq : b.tube.toRestricted.reindex
        (restrictSubstitution (φ.reindex (Presheaf.projection (Presheaf.interval Γ))) (Presheaf.endpointSub Γ false)) =
        b.base.reindex (restrictInclusion φ) := by
      apply Presheaf.Term.ext
      intro x
      exact b.boundary ((restrictInclusion φ).mapElements.obj x) x.val.property
    exact hzero.trans ((congrArg (Value.term (restrictContext φ) (reindex A (restrictInclusion φ))) heq).trans hbase.symm)

end SquareKit.Cubical.Source.Fillings
