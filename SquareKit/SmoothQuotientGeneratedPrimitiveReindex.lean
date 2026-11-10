import SquareKit.SmoothQuotientGeneratedPrimitiveMatching
import SquareKit.SmoothQuotientGeneratedBaseTerm
import SquareKit.Internal.PathTransport.CechMatchingSetReindex

/-! Primitive matching is the primitive coefficient matching pulled back by its actual base term. -/
noncomputable section
namespace SquareKit.SmoothQuotientGeneratedMatching
open CategoryTheory SheafActionQuotient SmoothOpenSite Internal.PathTransport
open GroupoidModel Comparison
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {H : Type} [Group H] {M X : Sheaf topology Type}
variable (a : Action (locallyConstantGroup H) M)
variable {Γ γ x ξ} (hΓ : Typed.CtxDeriv.{2} Γ γ)
variable (hx : Typed.TmDeriv.{2} Γ γ .base (Typed.baseCode γ) x ξ)

/-- The actual primitive matching equation, independently of any generated term. -/
def primitiveCoefficientValues (A : SplitSheaf.Ty X) :
    CechMatching.Datum (baseDiagram a A).toDiagram ⥤ Type 1 :=
  CechMatching.SetFamily.family
    (Instance.liftedFamily (Object a (SplitSheaf.Ext A)) (SmoothQuotientDeformations.family a _))
    (Instance.liftedFamily (Object a (SplitSheaf.Cech.double A)) (SmoothQuotientDeformations.family a _))
    (SmoothQuotientComparison.signature (a := a) (SplitSheaf.Cech.first A)).fiberMap
    (SmoothQuotientComparison.signature (a := a) (SplitSheaf.Cech.second A)).fiberMap

/-- Contextual primitive matching is precisely reindexing by the supplied base term. -/
def primitiveValueMatchingEquiv (A : SplitSheaf.Ty X) (d : Datum a hΓ A) :
    (primitiveSetData a hΓ hx A).MatchingSet d ≃
      (primitiveCoefficientValues a A).obj ((baseTermDiagram a hΓ hx A).mapDatum d) :=
  CechMatching.SetFamily.pullEquiv (baseTermDiagram a hΓ hx A) _ _ _ _ d

theorem primitiveValueMatchingEquiv_value (A : SplitSheaf.Ty X) (d : Datum a hΓ A)
    (z : (primitiveSetData a hΓ hx A).MatchingSet d) :
    HEq (primitiveValueMatchingEquiv a hΓ hx A d z).val z.val := HEq.rfl

/-- The whole primitive fiber groupoid is the coefficient matching set at the
actual term datum, including all vertical arrows. -/
def primitiveCoefficientMatchingEquivalence (A : SplitSheaf.Ty X) (d : Datum a hΓ A) :
    (relativeMatchingFamily a hΓ (.fiber hx) A).obj d ≌
      Discrete ((primitiveCoefficientValues a A).obj ((baseTermDiagram a hΓ hx A).mapDatum d)) :=
  (primitiveMatchingEquivalence a hΓ hx A d).trans
    (Discrete.equivalence (primitiveValueMatchingEquiv a hΓ hx A d))

theorem primitiveCoefficientMatchingEquivalence_value (A : SplitSheaf.Ty X)
    (d : Datum a hΓ A) (z : (relativeMatchingFamily a hΓ (.fiber hx) A).obj d) :
    HEq (((primitiveCoefficientMatchingEquivalence a hΓ hx A d).functor.obj z).as.val)
      z.localFiber.as :=
  (primitiveValueMatchingEquiv_value a hΓ hx A d
    ((primitiveMatchingEquivalence a hΓ hx A d).functor.obj z).as).trans
    (primitiveMatchingEquivalence_value a hΓ hx A d z)

end SquareKit.SmoothQuotientGeneratedMatching
