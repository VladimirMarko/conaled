import SquareKit.SmoothQuotientCoverDescent
import Examples.ArbitraryCoverSections

/-! Actual two-sheet matching data and original-cover presentation recovery. -/
noncomputable section
namespace Examples.OriginalCoverMatching
open CategoryTheory SquareKit SmoothOpenSite
open SheafActionQuotient (Action Object)
open Internal.PathTransport
open SmoothQuotientGeneratedMatching
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {H : Type} [Group H] {M X Y : Sheaf topology Type}
variable (a : Action (locallyConstantGroup H) M)
variable {Γ γ} (hΓ : Typed.CtxDeriv.{2} Γ γ)

/-- Every supported generated context has matching presentation recovery on
the actual two-sheet cover, without any global-extension premise on d. -/
example (d : SmoothQuotientCoverMatching.Datum a hΓ (ArbitraryCoverSections.twoSheet X)) :
    d ≅ (SmoothQuotientCoverMatching.matchingEquivalence a hΓ
      (ArbitraryCoverSections.twoSheet X)).inverse.obj
      ((SmoothQuotientCoverMatching.matchingEquivalence a hΓ
        (ArbitraryCoverSections.twoSheet X)).functor.obj d) :=
  (SmoothQuotientCoverMatching.matchingEquivalence a hΓ
    (ArbitraryCoverSections.twoSheet X)).unitIso.app d

/-- The presentation change preserves distinct selected matching arrows. -/
example {d e : SmoothQuotientCoverMatching.Datum a hΓ (ArbitraryCoverSections.twoSheet X)}
    (p q : d ⟶ e) (hne : p ≠ q) :
    (SmoothQuotientCoverMatching.matchingEquivalence a hΓ
      (ArbitraryCoverSections.twoSheet X)).functor.map p ≠
    (SmoothQuotientCoverMatching.matchingEquivalence a hΓ
      (ArbitraryCoverSections.twoSheet X)).functor.map q := by
  intro h
  exact hne ((SmoothQuotientCoverMatching.matchingEquivalence a hΓ
    (ArbitraryCoverSections.twoSheet X)).functor.map_injective h)

/-- The original restriction functor, not a replacement functor defined through
the split presentation, commutes with the checked matching equivalence. -/
example :
    SmoothQuotientCoverMatching.restrictionFunctor a hΓ (ArbitraryCoverSections.twoSheet X) ⋙
      (SmoothQuotientCoverMatching.matchingEquivalence a hΓ
        (ArbitraryCoverSections.twoSheet X)).functor =
      SmoothQuotientGeneratedMatching.restrictionFunctor a hΓ
        (SplitSheaf.ofDisplay (ArbitraryCoverSections.twoSheet X)) :=
  SmoothQuotientCoverMatching.restriction_toSplit a hΓ _

/-- An arbitrary parameter map uses the actual pullback cover and its square. -/
example (u : Y ⟶ X) :
    SmoothQuotientCoverMatching.Datum a hΓ (ArbitraryCoverSections.twoSheet X) ⥤
      SmoothQuotientCoverMatching.Datum a hΓ (Limits.pullback.snd
        (ArbitraryCoverSections.twoSheet X) u) :=
  SmoothQuotientCoverMatching.squareFunctor a hΓ u
    (Limits.pullback.fst (ArbitraryCoverSections.twoSheet X) u) Limits.pullback.condition

/-- The pullback square preserves complete canonical matching restrictions. -/
example (u : Y ⟶ X) :
    SmoothQuotientCoverMatching.restrictionFunctor a hΓ (ArbitraryCoverSections.twoSheet X) ⋙
      SmoothQuotientCoverMatching.squareFunctor a hΓ u
        (Limits.pullback.fst (ArbitraryCoverSections.twoSheet X) u) Limits.pullback.condition =
    restriction a hΓ u ⋙ SmoothQuotientCoverMatching.restrictionFunctor a hΓ
      (Limits.pullback.snd (ArbitraryCoverSections.twoSheet X) u) :=
  SmoothQuotientCoverMatching.restriction_square a hΓ u _ Limits.pullback.condition

abbrev baseContext : Typed.CtxDeriv.{2} [.base]
    (Typed.extendCode Typed.emptyCode (Typed.baseCode Typed.emptyCode)) :=
  .ext .empty (.base .empty)

def baseObject (P : Object a X) : context a baseContext X :=
  ⟨Discrete.mk PUnit.unit, AsSmall.up.obj P⟩

/-- The nontrivial doubled-origin torsor supplies a concrete generated object
and actual two-sheet matching datum, without choosing its trivialization. -/
example (K : Type) [Group K] (c : K) :
    SmoothQuotientCoverMatching.Datum (ActionQuotientEvidence.ineffective K) baseContext
      (ArbitraryCoverSections.twoSheet SmoothClutching.base) :=
  (SmoothQuotientCoverMatching.restrictionFunctor (ActionQuotientEvidence.ineffective K)
    baseContext (ArbitraryCoverSections.twoSheet SmoothClutching.base)).obj
    (baseObject _ (ActionQuotientEvidence.nontrivialObject K c))

end Examples.OriginalCoverMatching
