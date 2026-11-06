import SquareKit.Internal.Cubical.Judgments.TransportInputs
import SquareKit.Internal.Cubical.RestrictedOperationBoundaries

namespace SquareKit.Cubical.Source.Fillings
set_option backward.isDefEq.respectTransparency false
open GuardedTheory Presheaf CategoryTheory
universe u

theorem transpSchema_valid (out : Judgment (Fin 5))
    (valid : ∀ (Γ : Context.{u}) (B : Family (total (Presheaf.interval Γ))) (F : Filling B)
      (φ : Cofibration Γ) (a : Presheaf.Term (reindex B (Presheaf.endpointSub Γ false))),
      F.Lawful → RestrictedConstancy B φ →
      out.eval algebra ![.context Γ,.family (total (Presheaf.interval Γ)) B,
        .filling (total (Presheaf.interval Γ)) B F,.cofibration Γ φ,
        .term Γ (reindex B (Presheaf.endpointSub Γ false)) a]) :
    Satisfies algebra.{u} (transpSchema out) := by
  intro ρ h
  obtain ⟨Γ,B,F,φ,a,hF,hc,rfl⟩ := transpSchema_inputs out ρ h
  exact valid Γ B F φ a hF hc

theorem transp_valid : Satisfies algebra.{u} transpRule := by
  apply transpSchema_valid
  intro Γ B F φ a _ hc
  refine ⟨Γ,reindex B (Presheaf.endpointSub Γ true),F.transp φ hc a,rfl,?_,?_⟩
  · exact subTy_eval (.var (1 : Fin 5)) (endpointSub (.var 0) true) _ _ _ B _ rfl
      (endpointSub_eval (.var 0) _ Γ rfl true)
  · exact extra_transp Γ B F φ hc a

theorem transpBoundary_valid : Satisfies algebra.{u} transpBoundaryRule := by
  apply transpSchema_valid
  intro Γ B F φ a hF hc
  change Source.operation .subTm ![extraOperation .transp ![.context Γ,
    .family (total (Presheaf.interval Γ)) B,.filling (total (Presheaf.interval Γ)) B F,
    .cofibration Γ φ,.term Γ (reindex B (Presheaf.endpointSub Γ false)) a],
    extraOperation .inclusion ![.context Γ,.cofibration Γ φ]] =
    Source.operation .subTm ![.term Γ (reindex B (Presheaf.endpointSub Γ false)) a,
      extraOperation .inclusion ![.context Γ,.cofibration Γ φ]]
  rw [extra_transp Γ B F φ hc a,extra_inclusion]
  simp only [Source.operation,Matrix.cons_val_zero,Matrix.cons_val_one,Value.termIn_term]
  exact Value.term_eq hc.restricted_endpoints (Filling.transp_restricted hF φ hc a)

end SquareKit.Cubical.Source.Fillings
