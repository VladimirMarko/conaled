import SquareKit.Internal.Cubical.RestrictedTransport

/-! Primitive computation equations hold as terms of the actual restricted
family, including transport whose endpoint families differ outside the face. -/
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u

theorem RestrictedConstancy.restricted_endpoints {Γ : Context.{u}}
    {A : Family (total (interval Γ))} {φ : Cofibration Γ} (h : RestrictedConstancy A φ) :
    Presheaf.reindex (Presheaf.reindex A (endpointSub Γ true)) (restrictInclusion φ) =
      Presheaf.reindex (Presheaf.reindex A (endpointSub Γ false)) (restrictInclusion φ) :=
  congrArg (fun B => Presheaf.reindex B
    (restrictSubstitution (φ.reindex (projection (interval Γ))) (endpointSub Γ true))) h

theorem Filling.transp_restricted {Γ : Context.{u}} {A : Family (total (interval Γ))}
    {F : Filling A} (hF : F.Lawful) (φ : Cofibration Γ) (h : RestrictedConstancy A φ)
    (a : Term (Presheaf.reindex A (endpointSub Γ false))) :
    HEq ((F.transp φ h a).reindex (restrictInclusion φ)) (a.reindex (restrictInclusion φ)) := by
  apply Term.hext h.restricted_endpoints
  intro x
  exact Filling.transp_on_face hF φ h a ((restrictInclusion φ).mapElements.obj x) x.val.property

theorem Filling.hcomp_restricted {Γ : Context.{u}} {A : Family Γ} {F : Filling A}
    (hF : F.Lawful) (φ : Cofibration Γ)
    (b : OpenBox (Presheaf.reindex A (projection (interval Γ))) φ) :
    (F.hcomp φ b).reindex (restrictInclusion φ) =
      b.tube.toRestricted.reindex
        (restrictSubstitution (φ.reindex (projection (interval Γ))) (endpointSub Γ true)) := by
  apply Term.ext
  intro x
  exact Filling.hcomp_boundary hF φ b ((restrictInclusion φ).mapElements.obj x) x.val.property

end SquareKit.Cubical.Presheaf
