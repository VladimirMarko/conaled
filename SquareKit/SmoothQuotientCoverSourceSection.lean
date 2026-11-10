import SquareKit.SmoothQuotientCoverGeneratedSections
import SquareKit.SmoothQuotientGeneratedBaseChangeSource
import SquareKit.Internal.PathTransport.GeneratedSectionSubstitution

/-! The unchanged source sections restrict to the actual original-cover matching
functor, including the transport-composition proof and dependent J. -/
noncomputable section
namespace SquareKit.SmoothQuotientCoverMatching
open CategoryTheory SheafActionQuotient SmoothOpenSite Internal.PathTransport GroupoidModel
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {H : Type} [Group H] {M X Y : Sheaf topology Type}
variable (a : Action (locallyConstantGroup H) M) (f : Y ⟶ X)
variable {Γ γ B b x ξ} (hΓ : Typed.CtxDeriv.{2} Γ γ)
variable (hB : Typed.TyDeriv.{2} Γ γ B b) (hx : Typed.TmDeriv.{2} Γ γ B b x ξ)

/-- The whole interpreted section, on objects and arrows, restricts canonically. -/
theorem sourceSection_restriction :
    (ξ (SmoothQuotientSource.model a X)).down.lift ⋙ restrictionFunctor a (.ext hΓ hB) f =
      restrictionFunctor a hΓ f ⋙
        substitution a (.ext hΓ hB) hΓ (Typed.SubDeriv.section hΓ hB hx) f := by
  have hh := restriction_substitution a f (.ext hΓ hB) hΓ
    (Typed.SubDeriv.section hΓ hB hx)
  have hs : ((Typed.sectionCode b ξ) (SmoothQuotientSource.model a X)).down =
      (ξ (SmoothQuotientSource.model a X)).down.lift :=
    Typed.sectionCode_universeLift (Object a X) (SmoothQuotientDeformations.family a X) b ξ
  rw [hs] at hh
  exact hh.symm

/-- Independent relative matching receives the very same interpreted source section. -/
theorem sourceSection_totalRestriction :
    (ξ (SmoothQuotientSource.model a X)).down.lift ⋙ totalRestriction a f hΓ hB =
      restrictionFunctor a hΓ f ⋙
        substitution a (.ext hΓ hB) hΓ (Typed.SubDeriv.section hΓ hB hx) f ⋙
        (generatedToRelative a hΓ hB f).functor := by
  dsimp only [totalRestriction]
  rw [← Functor.assoc, sourceSection_restriction a f hΓ hB hx]
  rfl

/-- This is the exact proof consumed by the classical tangent-composition theorem. -/
abbrev universalTransfer_restriction := sourceSection_totalRestriction a f
  Typed.Authoring.UniversalTransfer.context Typed.Authoring.UniversalTransfer.type
  Typed.Authoring.UniversalTransfer.proof

end SquareKit.SmoothQuotientCoverMatching
