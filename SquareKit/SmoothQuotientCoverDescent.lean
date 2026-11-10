import SquareKit.SmoothQuotientCoverMatchingNaturality

/-! Effectivity transfers from the split display to its original cover through
the proved comparison of the actual restriction functors. -/
noncomputable section
namespace SquareKit.SmoothQuotientCoverMatching
open CategoryTheory SmoothOpenSite
open SheafActionQuotient (Action)
open Internal.PathTransport GroupoidModel Comparison
open SmoothQuotientGeneratedMatching
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {H : Type} [Group H] {M X Y : Sheaf topology Type}
variable (a : Action (locallyConstantGroup H) M)
variable {Γ γ} (hΓ : Typed.CtxDeriv.{2} Γ γ) (f : Y ⟶ X)

/-- This transfer lemma requires split effectivity explicitly; it does not
replace the generated effectivity proof. -/
theorem restriction_equivalence_of_split
    [(SmoothQuotientGeneratedMatching.restrictionFunctor a hΓ
      (SplitSheaf.ofDisplay f)).IsEquivalence] :
    (restrictionFunctor a hΓ f).IsEquivalence := by
  let : (restrictionFunctor a hΓ f ⋙ (matchingEquivalence a hΓ f).functor).IsEquivalence := by
    rw [restriction_toSplit]
    infer_instance
  exact Functor.isEquivalence_of_comp_right _ (matchingEquivalence a hΓ f).functor

/-- The chosen inverse recovers arbitrary supplied original-cover matching data. -/
def descentEquivalenceOfSplit
    [(SmoothQuotientGeneratedMatching.restrictionFunctor a hΓ
      (SplitSheaf.ofDisplay f)).IsEquivalence] :
    context a hΓ X ≌ Datum a hΓ f := by
  letI := restriction_equivalence_of_split a hΓ f
  exact (restrictionFunctor a hΓ f).asEquivalence

@[simp] theorem descentEquivalenceOfSplit_functor
    [(SmoothQuotientGeneratedMatching.restrictionFunctor a hΓ
      (SplitSheaf.ofDisplay f)).IsEquivalence] :
    (descentEquivalenceOfSplit a hΓ f).functor = restrictionFunctor a hΓ f := rfl

/-- Recovery is natural in each supplied matching arrow, including ineffective loops. -/
theorem recovery_natural
    [(SmoothQuotientGeneratedMatching.restrictionFunctor a hΓ
      (SplitSheaf.ofDisplay f)).IsEquivalence]
    {d e : Datum a hΓ f} (p : d ⟶ e) :
    (restrictionFunctor a hΓ f).map ((descentEquivalenceOfSplit a hΓ f).inverse.map p) ≫
      ((descentEquivalenceOfSplit a hΓ f).counitIso.app e).hom =
    ((descentEquivalenceOfSplit a hΓ f).counitIso.app d).hom ≫ p :=
  (descentEquivalenceOfSplit a hΓ f).counitIso.hom.naturality p

variable {X' Y' : Sheaf topology Type} (k : Y' ⟶ X')
variable (u : X' ⟶ X) (v : Y' ⟶ Y) (square : v ≫ f = k ≫ u)

/-- Chosen gluing is compatible with arbitrary cover squares by a selected
natural isomorphism; parameter restriction need not be invertible. -/
def descentSquareOfSplit
    [(SmoothQuotientGeneratedMatching.restrictionFunctor a hΓ
      (SplitSheaf.ofDisplay f)).IsEquivalence]
    [(SmoothQuotientGeneratedMatching.restrictionFunctor a hΓ
      (SplitSheaf.ofDisplay k)).IsEquivalence] :
    (descentEquivalenceOfSplit a hΓ f).inverse ⋙ restriction a hΓ u ≅
      squareFunctor a hΓ u v square ⋙ (descentEquivalenceOfSplit a hΓ k).inverse := by
  let E := descentEquivalenceOfSplit a hΓ f
  let K := descentEquivalenceOfSplit a hΓ k
  let i : E.functor ⋙ squareFunctor a hΓ u v square ≅ restriction a hΓ u ⋙ K.functor :=
    eqToIso (restriction_square a hΓ u v square)
  exact ((Functor.associator E.inverse (restriction a hΓ u) K.functor) ≪≫
    Iso.inverseCompIso (G := E) i.symm).isoCompInverse (H := K)

end SquareKit.SmoothQuotientCoverMatching
