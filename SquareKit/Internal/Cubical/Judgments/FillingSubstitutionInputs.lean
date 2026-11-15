import SquareKit.Internal.Cubical.Judgments.HcompInputs
import SquareKit.Internal.Cubical.Judgments.TransportInputs
import SquareKit.Internal.Cubical.Judgments.FillingSubstitutionSyntax

namespace SquareKit.Cubical.Source.Fillings
set_option backward.isDefEq.respectTransparency false
open GuardedTheory Presheaf CategoryTheory
universe u

theorem transpSubSchema_valid (out : Judgment (Fin 7))
    (valid : ∀ (Γ Δ : Context.{u}) (B : Family (total (Presheaf.interval Γ))) (F : Filling B)
      (φ : Cofibration Γ) (a : Presheaf.Term (reindex B (Presheaf.endpointSub Γ false))) (σ : Δ ⟶ Γ),
      F.Lawful → RestrictedConstancy B φ →
      out.eval algebra ![.context Γ,.context Δ,.family (total (Presheaf.interval Γ)) B,
        .filling (total (Presheaf.interval Γ)) B F,.cofibration Γ φ,
        .term Γ (reindex B (Presheaf.endpointSub Γ false)) a,.substitution Δ Γ σ]) :
    Satisfies algebra.{u} (transpSubSchema out) := by
  intro ρ h
  have hp : ∀ i, (transpRule.premise i).eval algebra (fun j => ρ (![0,2,3,4,5] j)) := by
    intro i
    have hi := h ⟨i.val,Nat.lt_trans i.isLt (by decide : 4 < 5)⟩
    simpa only [transpSubSchema,dite_eq_left i.isLt,Atom.eval_subst,GuardedTheory.Term.eval,FinitaryTerm.fold] using hi
  obtain ⟨Γ,B,F,φ,a,hF,hc,e⟩ := transpSchema_inputs _ _ hp
  have hΓ : ρ 0 = .context Γ := congrFun e 0
  have hB : ρ 2 = .family (total (Presheaf.interval Γ)) B := congrFun e 1
  have hProvider : ρ 3 = .filling (total (Presheaf.interval Γ)) B F := congrFun e 2
  have hφ : ρ 4 = .cofibration Γ φ := congrFun e 3
  have ha : ρ 5 = .term Γ (reindex B (Presheaf.endpointSub Γ false)) a := congrFun e 4
  have hσ := h 4
  change Source.predicate .substitution ![ρ 1,ρ 0,ρ 6] at hσ
  obtain ⟨Δ,Γ',σ,hΔ,hΓ',hσ⟩ := hσ
  have he := Value.context.inj (hΓ'.symm.trans hΓ)
  subst Γ'
  have he : ρ = ![.context Γ,.context Δ,.family (total (Presheaf.interval Γ)) B,
      .filling (total (Presheaf.interval Γ)) B F,.cofibration Γ φ,
      .term Γ (reindex B (Presheaf.endpointSub Γ false)) a,.substitution Δ Γ σ] := by
    funext i
    fin_cases i <;> first | exact hΓ | exact hΔ | exact hB | exact hProvider | exact hφ | exact ha | exact hσ
  subst ρ
  exact valid Γ Δ B F φ a σ hF hc

theorem hcompSubSchema_valid (out : Judgment (Fin 8))
    (valid : ∀ (Γ Δ : Context.{u}) (A : Family Γ) (F : Filling A) (φ : Cofibration Γ)
      (b : OpenBox (reindex A (Presheaf.projection (Presheaf.interval Γ))) φ) (σ : Δ ⟶ Γ), F.Lawful →
      out.eval algebra ![.context Γ,.context Δ,.family Γ A,.filling Γ A F,.cofibration Γ φ,
        .term (restrictContext (φ.reindex (Presheaf.projection (Presheaf.interval Γ))))
          (reindex (reindex A (Presheaf.projection (Presheaf.interval Γ)))
            (restrictInclusion (φ.reindex (Presheaf.projection (Presheaf.interval Γ))))) b.tube.toRestricted,
        .term Γ A b.base,.substitution Δ Γ σ]) :
    Satisfies algebra.{u} (hcompSubSchema out) := by
  intro ρ h
  have hp : ∀ i, (hcompRule.premise i).eval algebra (fun j => ρ (![0,2,3,4,5,6] j)) := by
    intro i
    have hi := h ⟨i.val,Nat.lt_trans i.isLt (by decide : 5 < 6)⟩
    simpa only [hcompSubSchema,dite_eq_left i.isLt,Atom.eval_subst,GuardedTheory.Term.eval,FinitaryTerm.fold] using hi
  obtain ⟨Γ,A,F,φ,b,hF,e⟩ := hcompSchema_inputs _ _ hp
  have hΓ : ρ 0 = .context Γ := congrFun e 0
  have hA : ρ 2 = .family Γ A := congrFun e 1
  have hProvider : ρ 3 = .filling Γ A F := congrFun e 2
  have hφ : ρ 4 = .cofibration Γ φ := congrFun e 3
  have hu := congrFun e 4
  have ha := congrFun e 5
  have hσ := h 5
  change Source.predicate .substitution ![ρ 1,ρ 0,ρ 7] at hσ
  obtain ⟨Δ,Γ',σ,hΔ,hΓ',hσ⟩ := hσ
  have he := Value.context.inj (hΓ'.symm.trans hΓ)
  subst Γ'
  have he : ρ = ![.context Γ,.context Δ,.family Γ A,.filling Γ A F,.cofibration Γ φ,
      .term (restrictContext (φ.reindex (Presheaf.projection (Presheaf.interval Γ))))
        (reindex (reindex A (Presheaf.projection (Presheaf.interval Γ)))
          (restrictInclusion (φ.reindex (Presheaf.projection (Presheaf.interval Γ))))) b.tube.toRestricted,
      .term Γ A b.base,.substitution Δ Γ σ] := by
    funext i
    fin_cases i <;> first | exact hΓ | exact hΔ | exact hA | exact hProvider | exact hφ | exact hu | exact ha | exact hσ
  subst ρ
  exact valid Γ Δ A F φ b σ hF

end SquareKit.Cubical.Source.Fillings
