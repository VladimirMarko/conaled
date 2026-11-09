import SquareKit.SmoothQuotientDescentExtension
import SquareKit.Internal.PathTransport.SectionDescent

/-! Fixed-cover section transport on the full quotient cocycle groupoid. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SquareKit.SmoothQuotientDeformations
open CategoryTheory SheafActionQuotient SmoothOpenSite
open Internal.PathTransport.GroupoidModel
variable {H : Type} [Group H] {M X : Sheaf topology Type}
variable {a : Action (locallyConstantGroup H) M} {A : SplitSheaf.Ty X}
variable [Presheaf.IsLocallySurjective topology (SplitSheaf.p A).hom]

/-- The existing gluing comparison regarded as a map of groupoid families. -/
def CocycleDatum.sectionComparison :
    setFamily (Descent.descentFunctor a A ⋙ family a X) ⟶
      setFamily (fiberFamily (a := a) (A := A)) :=
  Functor.whiskerRight (fiberComparison (a := a) (A := A)).hom discrete

theorem CocycleDatum.sectionEquivalences : ∀ d : Descent.Datum (a := a) A,
    Functor.IsEquivalence ((CocycleDatum.sectionComparison (a := a) (A := A)).app d) :=
  fun d => (Discrete.equivalence (CocycleDatum.fiberEquivalence d)).isEquivalence_functor

/-- Reconstruct a section of descended deformations from a section on *all*
local cocycles and compatible arrows. No global deformation section is supplied.
This is a fixed-cover comparison, not parameter-compatible local-section gluing. -/
def CocycleDatum.descendSection
    (s : Section (setFamily (fiberFamily (a := a) (A := A)))) :
    Section (setFamily (Descent.descentFunctor a A ⋙ family a X)) :=
  SectionDescent.descendFibers (hβ := sectionEquivalences) CategoryTheory.Equivalence.refl s sectionComparison

/-- The reconstructed section recovers the supplied local section on objects
and arrows through the actual deformation gluing comparison. -/
def CocycleDatum.descendSectionRecovery
    (s : Section (setFamily (fiberFamily (a := a) (A := A)))) :
    (descendSection s).lift ⋙
        (SectionDescent.totalEquivalence (hβ := sectionEquivalences)
          (B := setFamily (fiberFamily (a := a) (A := A)))
          CategoryTheory.Equivalence.refl (sectionComparison (a := a) (A := A))).functor ≅
      s.lift :=
  SectionDescent.recoverFibers (hβ := sectionEquivalences) CategoryTheory.Equivalence.refl s sectionComparison

/-- Recovery preserves the selected cocycle context rather than changing it
by an arbitrary automorphism. -/
theorem CocycleDatum.descendSectionRecovery_base
    (s : Section (setFamily (fiberFamily (a := a) (A := A))))
    (d : Descent.Datum (a := a) A) :
    ((descendSectionRecovery s).hom.app d).base = 𝟙 d :=
  SectionDescent.recoverFibers_base (hβ := sectionEquivalences) CategoryTheory.Equivalence.refl s sectionComparison d

end SquareKit.SmoothQuotientDeformations
