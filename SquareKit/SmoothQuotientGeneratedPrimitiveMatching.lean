import SquareKit.SmoothQuotientGeneratedRelativeMatching
import SquareKit.Internal.PathTransport.GeneratedPrimitiveFiber
import SquareKit.Internal.PathTransport.CechMatchingComprehensionDiscrete
import SquareKit.Internal.PathTransport.CechMatchingComprehensionConstant

/-! Independently matched primitive fibers use actual set-valued restriction. -/
noncomputable section
namespace SquareKit.SmoothQuotientGeneratedMatching
open CategoryTheory SheafActionQuotient SmoothOpenSite Internal.PathTransport
open GroupoidModel Comparison
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {H : Type} [Group H] {M X Y : Sheaf topology Type}
variable (a : Action (locallyConstantGroup H) M)
variable {Γ γ x ξ} (hΓ : Typed.CtxDeriv.{2} Γ γ)
variable (hx : Typed.TmDeriv.{2} Γ γ .base (Typed.baseCode γ) x ξ)

def primitiveValues (_hx : Typed.TmDeriv.{2} Γ γ .base (Typed.baseCode γ) x ξ) (Y : Sheaf topology Type) : context a hΓ Y ⥤ Type 1 :=
  baseFunctor (ξ (SmoothQuotientSource.model a Y)).down ⋙
    Instance.liftedFamily (Object a Y) (SmoothQuotientDeformations.family a Y)

def primitiveValueRestriction (f : Y ⟶ X) :
    primitiveValues a hΓ hx X ⟶ restriction a hΓ f ⋙ primitiveValues a hΓ hx Y :=
  generatedFiberSetMap (SmoothQuotientComparison.signature (a := a) f) hΓ hx

def primitiveSetData (A : SplitSheaf.Ty X) :
    CechMatching.Comprehension.SetData (strictDiagram a hΓ A) where
  localFamily := primitiveValues a hΓ hx (SplitSheaf.Ext A)
  doubleFamily := primitiveValues a hΓ hx (SplitSheaf.Cech.double A)
  tripleFamily := primitiveValues a hΓ hx (SplitSheaf.Cech.triple A)
  first := primitiveValueRestriction a hΓ hx (SplitSheaf.Cech.first A)
  second := primitiveValueRestriction a hΓ hx (SplitSheaf.Cech.second A)
  diagonal := primitiveValueRestriction a hΓ hx (SplitSheaf.Cech.diagonal A)
  firstSecond := primitiveValueRestriction a hΓ hx (SplitSheaf.Cech.firstSecond A)
  firstThird := primitiveValueRestriction a hΓ hx (SplitSheaf.Cech.firstThird A)
  secondThird := primitiveValueRestriction a hΓ hx (SplitSheaf.Cech.secondThird A)

theorem familyRestriction_fiber (f : Y ⟶ X) :
    familyRestriction a hΓ (.fiber hx) f =
      Functor.whiskerRight (primitiveValueRestriction a hΓ hx f) discrete :=
  generatedFamilyMap_fiber_set (SmoothQuotientComparison.signature (a := a) f) hΓ hx

theorem relativeFamilyData_fiber (A : SplitSheaf.Ty X) :
    relativeFamilyData a hΓ (.fiber hx) A = (primitiveSetData a hΓ hx A).toFamilyData := by
  unfold relativeFamilyData familyRestriction
  simp only [generatedFamilyMap_fiber_set]
  rfl

theorem primitiveSetCoherence (A : SplitSheaf.Ty X) :
    (primitiveSetData a hΓ hx A).toFamilyData.Coherence := by
  rw [← relativeFamilyData_fiber a hΓ hx A]
  exact relativeFamilyCoherence a hΓ (.fiber hx) A

/-- Primitive relative matching is exactly the discrete set of local values
satisfying the actual overlap equation over the supplied base datum. -/
def primitiveMatchingEquivalence (A : SplitSheaf.Ty X) (d : Datum a hΓ A) :
    (relativeMatchingFamily a hΓ (.fiber hx) A).obj d ≌
      Discrete ((primitiveSetData a hΓ hx A).MatchingSet d) :=
  (CechMatching.Comprehension.Constant.equivalenceOfGrpdIso
    ((CechMatching.Comprehension.Constant.familyIsoOfEq (relativeFamilyData_fiber a hΓ hx A)
      (relativeFamilyCoherence a hΓ (.fiber hx) A) (primitiveSetCoherence a hΓ hx A)).app d)).trans
    ((primitiveSetData a hΓ hx A).discreteEquivalence (primitiveSetCoherence a hΓ hx A) d)

theorem primitiveMatchingEquivalence_value (A : SplitSheaf.Ty X) (d : Datum a hΓ A)
    (z : (relativeMatchingFamily a hΓ (.fiber hx) A).obj d) :
    HEq (((primitiveMatchingEquivalence a hΓ hx A d).functor.obj z).as.val)
      z.localFiber.as := by
  have hh := CechMatching.Comprehension.Constant.familyIsoOfEq_localFiber
    (relativeFamilyData_fiber a hΓ hx A)
    (relativeFamilyCoherence a hΓ (.fiber hx) A) (primitiveSetCoherence a hΓ hx A) d z
  exact heq_of_eq (congrArg Discrete.as (eq_of_heq hh))

end SquareKit.SmoothQuotientGeneratedMatching
