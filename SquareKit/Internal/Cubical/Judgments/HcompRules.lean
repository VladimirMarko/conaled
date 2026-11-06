import SquareKit.Internal.Cubical.Judgments.HcompInputs
import SquareKit.Internal.Cubical.RestrictedOperationBoundaries

namespace SquareKit.Cubical.Source.Fillings
set_option backward.isDefEq.respectTransparency false
open GuardedTheory Presheaf CategoryTheory
universe u

theorem hcompSchema_valid (out : Judgment (Fin 6))
    (valid : ∀ (Γ : Context.{u}) (A : Family Γ) (F : Filling A) (φ : Cofibration Γ)
      (b : OpenBox (reindex A (Presheaf.projection (Presheaf.interval Γ))) φ), F.Lawful →
      out.eval algebra ![.context Γ,.family Γ A,.filling Γ A F,.cofibration Γ φ,
        .term (restrictContext (φ.reindex (Presheaf.projection (Presheaf.interval Γ))))
          (reindex (reindex A (Presheaf.projection (Presheaf.interval Γ)))
            (restrictInclusion (φ.reindex (Presheaf.projection (Presheaf.interval Γ))))) b.tube.toRestricted,
        .term Γ A b.base]) :
    Satisfies algebra.{u} (hcompSchema out) := by
  intro ρ h
  obtain ⟨Γ,A,F,φ,b,hF,rfl⟩ := hcompSchema_inputs out ρ h
  exact valid Γ A F φ b hF

theorem hcomp_valid : Satisfies algebra.{u} hcompRule := by
  apply hcompSchema_valid
  intro Γ A F φ b _
  exact ⟨Γ,A,F.hcomp φ b,rfl,rfl,extra_hcomp Γ A F φ b⟩

theorem hcompBoundary_valid : Satisfies algebra.{u} hcompBoundaryRule := by
  apply hcompSchema_valid
  intro Γ A F φ b hF
  have ht := tubeEndpoint_eval (.var (0 : Fin 6)) (.var 3) (.var 4)
    ![.context Γ,.family Γ A,.filling Γ A F,.cofibration Γ φ,
      .term (restrictContext (φ.reindex (Presheaf.projection (Presheaf.interval Γ))))
        (reindex (reindex A (Presheaf.projection (Presheaf.interval Γ)))
          (restrictInclusion (φ.reindex (Presheaf.projection (Presheaf.interval Γ))))) b.tube.toRestricted,
      .term Γ A b.base] Γ _ φ b.tube.toRestricted rfl rfl rfl true
  change Source.operation .subTm ![extraOperation .hcomp ![.context Γ,.family Γ A,.filling Γ A F,
    .cofibration Γ φ,.term _ _ b.tube.toRestricted,.term Γ A b.base],
    extraOperation .inclusion ![.context Γ,.cofibration Γ φ]] = _
  rw [ht,extra_hcomp Γ A F φ b,extra_inclusion]
  simp only [Source.operation,Matrix.cons_val_zero,Matrix.cons_val_one,Value.termIn_term]
  exact congrArg (Value.term (restrictContext φ) (reindex A (restrictInclusion φ)))
    (Filling.hcomp_restricted hF φ b)

end SquareKit.Cubical.Source.Fillings
