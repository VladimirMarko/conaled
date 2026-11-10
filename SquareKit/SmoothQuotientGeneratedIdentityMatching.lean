import SquareKit.SmoothQuotientGeneratedRelativeMatching
import SquareKit.Internal.PathTransport.GeneratedIdentitySetMap
import SquareKit.Internal.PathTransport.CechMatchingComprehensionDiscrete
import SquareKit.Internal.PathTransport.CechMatchingComprehensionConstant

/-! Independently matched identity fibers use actual set-valued restriction. -/
noncomputable section
namespace SquareKit.SmoothQuotientGeneratedMatching
open CategoryTheory SheafActionQuotient SmoothOpenSite Internal.PathTransport
open GroupoidModel Comparison
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {H : Type} [Group H] {M X Y : Sheaf topology Type}
variable (a : Action (locallyConstantGroup H) M)
variable {Γ γ B b x ξ y η} (hΓ : Typed.CtxDeriv.{2} Γ γ)
variable (hB : Typed.TyDeriv.{2} Γ γ B b)
variable (hx : Typed.TmDeriv.{2} Γ γ B b x ξ) (hy : Typed.TmDeriv.{2} Γ γ B b y η)

def identityValues (_hB : Typed.TyDeriv.{2} Γ γ B b)
    (_hx : Typed.TmDeriv.{2} Γ γ B b x ξ) (_hy : Typed.TmDeriv.{2} Γ γ B b y η)
    (Y : Sheaf topology Type) : context a hΓ Y ⥤ Type 1 :=
  directIdentity (b (SmoothQuotientSource.model a Y))
    (ξ (SmoothQuotientSource.model a Y)).down (η (SmoothQuotientSource.model a Y)).down

def identityValueRestriction (f : Y ⟶ X) :
    identityValues a hΓ hB hx hy X ⟶ restriction a hΓ f ⋙ identityValues a hΓ hB hx hy Y :=
  generatedIdentitySetMap (SmoothQuotientComparison.signature (a := a) f) hΓ hB hx hy

def identitySetData (A : SplitSheaf.Ty X) :
    CechMatching.Comprehension.SetData (strictDiagram a hΓ A) where
  localFamily := identityValues a hΓ hB hx hy (SplitSheaf.Ext A)
  doubleFamily := identityValues a hΓ hB hx hy (SplitSheaf.Cech.double A)
  tripleFamily := identityValues a hΓ hB hx hy (SplitSheaf.Cech.triple A)
  first := identityValueRestriction a hΓ hB hx hy (SplitSheaf.Cech.first A)
  second := identityValueRestriction a hΓ hB hx hy (SplitSheaf.Cech.second A)
  diagonal := identityValueRestriction a hΓ hB hx hy (SplitSheaf.Cech.diagonal A)
  firstSecond := identityValueRestriction a hΓ hB hx hy (SplitSheaf.Cech.firstSecond A)
  firstThird := identityValueRestriction a hΓ hB hx hy (SplitSheaf.Cech.firstThird A)
  secondThird := identityValueRestriction a hΓ hB hx hy (SplitSheaf.Cech.secondThird A)

theorem familyRestriction_identity (f : Y ⟶ X) :
    familyRestriction a hΓ (.identity hB hx hy) f =
      Functor.whiskerRight (identityValueRestriction a hΓ hB hx hy f) discrete :=
  generatedFamilyMap_identity_set (SmoothQuotientComparison.signature (a := a) f) hΓ hB hx hy

theorem relativeFamilyData_identity (A : SplitSheaf.Ty X) :
    relativeFamilyData a hΓ (.identity hB hx hy) A = (identitySetData a hΓ hB hx hy A).toFamilyData := by
  unfold relativeFamilyData familyRestriction
  simp only [generatedFamilyMap_identity_set]
  rfl

theorem identitySetCoherence (A : SplitSheaf.Ty X) :
    (identitySetData a hΓ hB hx hy A).toFamilyData.Coherence := by
  rw [← relativeFamilyData_identity a hΓ hB hx hy A]
  exact relativeFamilyCoherence a hΓ (.identity hB hx hy) A

/-- Identity relative matching is exactly the discrete set of local values
satisfying the actual overlap equation over the supplied base datum. -/
def identityMatchingEquivalence (A : SplitSheaf.Ty X) (d : Datum a hΓ A) :
    (relativeMatchingFamily a hΓ (.identity hB hx hy) A).obj d ≌
      Discrete ((identitySetData a hΓ hB hx hy A).MatchingSet d) :=
  (CechMatching.Comprehension.Constant.equivalenceOfGrpdIso
    ((CechMatching.Comprehension.Constant.familyIsoOfEq (relativeFamilyData_identity a hΓ hB hx hy A)
      (relativeFamilyCoherence a hΓ (.identity hB hx hy) A) (identitySetCoherence a hΓ hB hx hy A)).app d)).trans
    ((identitySetData a hΓ hB hx hy A).discreteEquivalence (identitySetCoherence a hΓ hB hx hy A) d)

theorem identityMatchingEquivalence_value (A : SplitSheaf.Ty X) (d : Datum a hΓ A)
    (z : (relativeMatchingFamily a hΓ (.identity hB hx hy) A).obj d) :
    HEq (((identityMatchingEquivalence a hΓ hB hx hy A d).functor.obj z).as.val)
      z.localFiber.as := by
  have hh := CechMatching.Comprehension.Constant.familyIsoOfEq_localFiber
    (relativeFamilyData_identity a hΓ hB hx hy A)
    (relativeFamilyCoherence a hΓ (.identity hB hx hy) A) (identitySetCoherence a hΓ hB hx hy A) d z
  exact heq_of_eq (congrArg Discrete.as (eq_of_heq hh))

end SquareKit.SmoothQuotientGeneratedMatching
