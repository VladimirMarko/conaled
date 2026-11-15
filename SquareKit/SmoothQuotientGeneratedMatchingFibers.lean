import SquareKit.SmoothQuotientGeneratedMatchingSubstitution
import SquareKit.Internal.PathTransport.GroupoidFiberDecomposition

/-! Relative matching fibers over independent generated context data. The
selected base identification is retained as an isomorphism, not erased. -/
noncomputable section
namespace SquareKit.SmoothQuotientGeneratedMatching
open CategoryTheory SheafActionQuotient SmoothOpenSite
open Internal.PathTransport
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {H : Type} [Group H] {M X : Sheaf topology Type}
variable (a : Action (locallyConstantGroup H) M)
variable {Γ γ B b} (hΓ : Typed.CtxDeriv.{2} Γ γ) (hB : Typed.TyDeriv.{2} Γ γ B b)
variable (A : SplitSheaf.Ty X)

/-- Relative matching consists of independent matching data for the local
extended context, together with a selected identification of its base datum.
The identification has its own actual local arrow and overlap square. -/
def matchingFamily : Datum a hΓ A ⥤ Grpd.{1,1} :=
  GroupoidFiberDecomposition.family (projection a hΓ hB A)

/-- Comprehension decomposes naturally into context matching and relative
matching. This theorem is independent of effectivity of the parameter cover. -/
def comprehensionEquivalence :
    Grothendieck (matchingFamily a hΓ hB A ⋙ Grpd.forgetToCat) ≌
      Datum a (.ext hΓ hB) A :=
  GroupoidFiberDecomposition.equivalence (projection a hΓ hB A)

/-- The decomposition's base comparison is the supplied identification of
matching data, naturally on all arrows. -/
def comprehensionProjection :
    (comprehensionEquivalence a hΓ hB A).functor ⋙ projection a hΓ hB A ≅
      Grothendieck.forget (matchingFamily a hΓ hB A ⋙ Grpd.forgetToCat) :=
  GroupoidFiberDecomposition.projectionComparison (projection a hΓ hB A)

/-- Reindexing the matching family retains the extended local datum, changing
its selected base identification by the given matching arrow. -/
theorem matchingFamily_map_object {d e : Datum a hΓ A} (f : d ⟶ e)
    (x : (matchingFamily a hΓ hB A).obj d) :
    (((matchingFamily a hΓ hB A).map f).obj x).left = x.left := rfl

end SquareKit.SmoothQuotientGeneratedMatching
