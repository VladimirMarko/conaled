import SquareKit.SmoothQuotientGeneratedIdentityMatching
import SquareKit.SmoothQuotientGeneratedTermMatching
import SquareKit.Internal.PathTransport.SectionIdentityRestriction
import SquareKit.Internal.PathTransport.ConjugatedSquare
import SquareKit.Internal.PathTransport.CechMatchingComprehensionFiberArrowEquiv
import SquareKit.Internal.PathTransport.GrothendieckVertical

/-! The identity matching equation is the actual square between descended terms. -/
noncomputable section
namespace SquareKit.SmoothQuotientGeneratedMatching
open CategoryTheory SheafActionQuotient SmoothOpenSite Internal.PathTransport
open GroupoidModel Comparison
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {H : Type} [Group H] {M X : Sheaf topology Type}
variable (a : Action (locallyConstantGroup H) M)
variable {Γ γ B b x ξ y η} (hΓ : Typed.CtxDeriv.{2} Γ γ)
variable (hB : Typed.TyDeriv.{2} Γ γ B b)
variable (hx : Typed.TmDeriv.{2} Γ γ B b x ξ) (hy : Typed.TmDeriv.{2} Γ γ B b y η)

theorem identityValue_square (A : SplitSheaf.Ty X) (d : Datum a hΓ A)
    (p : (identitySetData a hΓ hB hx hy A).localFamily.obj d.localObject) :
    (identitySetData a hΓ hB hx hy A).doubleFamily.map d.overlap.hom
        ((identitySetData a hΓ hB hx hy A).first.app d.localObject p) =
      (identitySetData a hΓ hB hx hy A).second.app d.localObject p ↔
    (relativeFamilyData a hΓ hB A).firstMap.map
        ((Grothendieck.ι ((relativeFamilyData a hΓ hB A).localFamily ⋙ Grpd.forgetToCat)
          d.localObject).map p) ≫ ((termDiagram a hΓ hB hy A).overlap d).hom =
      ((termDiagram a hΓ hB hx A).overlap d).hom ≫
        (relativeFamilyData a hΓ hB A).secondMap.map
          ((Grothendieck.ι ((relativeFamilyData a hΓ hB A).localFamily ⋙ Grpd.forgetToCat)
            d.localObject).map p) := by
  let S₀ := SmoothQuotientComparison.signature (a := a) (SplitSheaf.Cech.first A)
  let S₁ := SmoothQuotientComparison.signature (a := a) (SplitSheaf.Cech.second A)
  have hp := generatedIdentity_included S₀ hΓ hB hx hy d.localObject p
  have hr := generatedIdentity_included S₁ hΓ hB hx hy d.localObject p
  exact (identity_transport_iff_square _ _ _ d.overlap.hom _ _).trans
    (eq_comm.trans (conjugated_square_iff
      (eqToIso (Functor.congr_obj (generatedSectionLift_commutes S₀ hΓ hB hx) d.localObject))
      (eqToIso (Functor.congr_obj (generatedSectionLift_commutes S₀ hΓ hB hy) d.localObject))
      (eqToIso (Functor.congr_obj (generatedSectionLift_commutes S₁ hΓ hB hx) d.localObject))
      (eqToIso (Functor.congr_obj (generatedSectionLift_commutes S₁ hΓ hB hy) d.localObject))
      _ _ _ _ _ _ hp hr))


def identityDatumArrowEquiv (A : SplitSheaf.Ty X) (d : Datum a hΓ A) :
    (identitySetData a hΓ hB hx hy A).MatchingSet d ≃
      {p : (termDiagram a hΓ hB hx A).functor.obj d ⟶
          (termDiagram a hΓ hB hy A).functor.obj d //
        ((relativeFamilyData a hΓ hB A).projection (relativeFamilyCoherence a hΓ hB A)).functor.map p ≫
          eqToHom (Functor.congr_obj (termMatching_projection a hΓ hB hy A) d) =
            eqToHom (Functor.congr_obj (termMatching_projection a hΓ hB hx A) d)} where
  toFun p := ⟨⟨(Grothendieck.ι
    ((relativeFamilyData a hΓ hB A).localFamily ⋙ Grpd.forgetToCat) d.localObject).map p.val,
      (identityValue_square a hΓ hB hx hy A d p.val).mp p.property⟩, by
        apply CechMatching.Datum.Hom.ext
        simp only [CechMatching.Datum.comp_localArrow, CechMatching.Datum.eqToHom_localArrow]
        change (𝟙 d.localObject) ≫ eqToHom _ = eqToHom _
        simp only [Category.id_comp]⟩
  invFun p := by
    have hv : p.val.localArrow.base = 𝟙 d.localObject := by
      have hh := congrArg CechMatching.Datum.Hom.localArrow p.property
      simp only [CechMatching.Datum.comp_localArrow, CechMatching.Datum.eqToHom_localArrow] at hh
      change p.val.localArrow.base ≫ (𝟙 d.localObject) = 𝟙 d.localObject at hh
      exact (Category.comp_id p.val.localArrow.base).symm.trans hh
    refine ⟨GrothendieckVertical.arrow
      ((relativeFamilyData a hΓ hB A).localFamily ⋙ Grpd.forgetToCat) p.val.localArrow hv, ?_⟩
    apply (identityValue_square a hΓ hB hx hy A d _).mpr
    erw [GrothendieckVertical.inclusion_arrow]
    exact p.val.commutes
  left_inv p := by
    apply Subtype.ext
    apply (Grothendieck.ι
      ((relativeFamilyData a hΓ hB A).localFamily ⋙ Grpd.forgetToCat) d.localObject).map_injective
    exact GrothendieckVertical.inclusion_arrow
      ((relativeFamilyData a hΓ hB A).localFamily ⋙ Grpd.forgetToCat)
      ((Grothendieck.ι ((relativeFamilyData a hΓ hB A).localFamily ⋙ Grpd.forgetToCat)
        d.localObject).map p.val) rfl
  right_inv p := by
    apply Subtype.ext
    apply CechMatching.Datum.Hom.ext
    exact GrothendieckVertical.inclusion_arrow
      ((relativeFamilyData a hΓ hB A).localFamily ⋙ Grpd.forgetToCat)
      (c := d.localObject) p.val.localArrow (by
        have hh := congrArg CechMatching.Datum.Hom.localArrow p.property
        simp only [CechMatching.Datum.comp_localArrow, CechMatching.Datum.eqToHom_localArrow] at hh
        change p.val.localArrow.base ≫ (𝟙 d.localObject) = 𝟙 d.localObject at hh
        exact (Category.comp_id p.val.localArrow.base).symm.trans hh)

@[simp] theorem identityDatumArrowEquiv_local (A : SplitSheaf.Ty X) (d : Datum a hΓ A)
    (p : (identitySetData a hΓ hB hx hy A).MatchingSet d) :
    ((identityDatumArrowEquiv a hΓ hB hx hy A d p).val).localArrow =
      (Grothendieck.ι ((relativeFamilyData a hΓ hB A).localFamily ⋙ Grpd.forgetToCat)
        d.localObject).map p.val := rfl

def identityFiberArrowEquiv (A : SplitSheaf.Ty X) (d : Datum a hΓ A) :
    (identitySetData a hΓ hB hx hy A).MatchingSet d ≃
      (termFiber a hΓ hB hx A d ⟶ termFiber a hΓ hB hy A d) :=
  (identityDatumArrowEquiv a hΓ hB hx hy A d).trans
    (CechMatching.Comprehension.ofDatumArrowEquiv _ _)

end SquareKit.SmoothQuotientGeneratedMatching
