import SquareKit.SmoothQuotientCechBaseEvaluation
import SquareKit.SmoothQuotientCechBaseTermSquare
import SquareKit.SmoothQuotientGeneratedBaseTerm
import SquareKit.Internal.PathTransport.Authoring

/-! Coefficient extraction from the relative base total is the newest base
variable's matching map, including its action on arrows. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.CechMatching.Comprehension.Constant
open CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {D E : StrictDiagram.{u,u}} {B : FamilyData D}
variable (q : B = data D E) (ha : B.Coherence) (hb : (data D E).Coherence)

theorem projectionOfEq_localMap : HEq (projectionOfEq q ha hb).localMap
    (fiberFunctor D.localCategory E.localCategory) := by
  subst B
  rfl

theorem projectionOfEq_doubleMap : HEq (projectionOfEq q ha hb).doubleMap
    (fiberFunctor D.doubleCategory E.doubleCategory) := by
  subst B
  rfl

theorem projectionOfEq_tripleMap : HEq (projectionOfEq q ha hb).tripleMap
    (fiberFunctor D.tripleCategory E.tripleCategory) := by
  subst B
  rfl
end SquareKit.Internal.PathTransport.CechMatching.Comprehension.Constant

namespace SquareKit.SmoothQuotientCechLocal
open CategoryTheory SheafActionQuotient SmoothOpenSite Internal.PathTransport
open GroupoidModel SmoothQuotientGeneratedMatching
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {H : Type} [Group H] {M X : Sheaf topology Type}
variable (a : Action (locallyConstantGroup H) M) (A : SplitSheaf.Ty X)
variable {Γ γ} (hΓ : Typed.CtxDeriv.{2} Γ γ)

theorem baseVariable_functor (Y : Sheaf topology Type) :
    baseFunctor ((Typed.Authoring.BasePoint.variable hΓ).code
      (SmoothQuotientSource.model a Y)).down =
    CechMatching.Comprehension.Constant.fiberFunctor
      (context a hΓ Y) (Grpd.of (AsSmall.{0} (Object a Y))) := by
  have hh := Typed.castCode_eval
    (Typed.baseSub_code (Typed.weakenCode γ (Typed.baseCode γ)))
    (Typed.varCode γ (Typed.baseCode γ)) (SmoothQuotientSource.model a Y)
  have he := eq_of_heq hh
  dsimp only [Typed.Authoring.BasePoint.variable]
  rw [he]
  rfl

/-- The relative total coefficient projection is the newest variable's complete
matching map, rather than just an equality of local objects. -/
theorem baseCoefficientProjection_variable :
    (generatedToRelative a hΓ (.base hΓ) A).comp
      (baseCoefficientProjection a A hΓ) =
    baseTermDiagram a (.ext hΓ (.base hΓ))
      (Typed.Authoring.BasePoint.variable hΓ).deriv A := by
  apply CechMatching.StrictMap.ext
  · change (baseCoefficientProjection a A hΓ).localMap = _
    rw [show (baseCoefficientProjection a A hΓ).localMap =
      CechMatching.Comprehension.Constant.fiberFunctor
        (context a hΓ (SplitSheaf.Ext A))
        (Grpd.of (AsSmall.{0} (Object a (SplitSheaf.Ext A)))) from
      eq_of_heq (CechMatching.Comprehension.Constant.projectionOfEq_localMap
        (relativeFamilyData_base a hΓ A) _ _)]
    exact (baseVariable_functor a hΓ (SplitSheaf.Ext A)).symm
  · change (baseCoefficientProjection a A hΓ).doubleMap = _
    rw [show (baseCoefficientProjection a A hΓ).doubleMap =
      CechMatching.Comprehension.Constant.fiberFunctor
        (context a hΓ (SplitSheaf.Cech.double A))
        (Grpd.of (AsSmall.{0} (Object a (SplitSheaf.Cech.double A)))) from
      eq_of_heq (CechMatching.Comprehension.Constant.projectionOfEq_doubleMap
        (relativeFamilyData_base a hΓ A) _ _)]
    exact (baseVariable_functor a hΓ (SplitSheaf.Cech.double A)).symm
  · change (baseCoefficientProjection a A hΓ).tripleMap = _
    rw [show (baseCoefficientProjection a A hΓ).tripleMap =
      CechMatching.Comprehension.Constant.fiberFunctor
        (context a hΓ (SplitSheaf.Cech.triple A))
        (Grpd.of (AsSmall.{0} (Object a (SplitSheaf.Cech.triple A)))) from
      eq_of_heq (CechMatching.Comprehension.Constant.projectionOfEq_tripleMap
        (relativeFamilyData_base a hΓ A) _ _)]
    exact (baseVariable_functor a hΓ (SplitSheaf.Cech.triple A)).symm

theorem baseCoefficientProjection_variable_functor :
    (generatedToRelative a hΓ (.base hΓ) A).functor ⋙
      (baseCoefficientProjection a A hΓ).functor =
    (baseTermDiagram a (.ext hΓ (.base hΓ))
      (Typed.Authoring.BasePoint.variable hΓ).deriv A).functor := by
  rw [← CechMatching.StrictMap.functor_comp, baseCoefficientProjection_variable]

theorem baseVariable_sourceFunctor :
    baseFunctor ((Typed.Authoring.BasePoint.variable hΓ).code (model a A)).down =
    CechMatching.Comprehension.Constant.fiberFunctor
      (show Grpd.{1,1} from γ (model a A))
      (Grpd.of (AsSmall.{0} (SheafActionQuotient.Cech.Datum (a := a) A))) := by
  have he := eq_of_heq (Typed.castCode_eval
    (Typed.baseSub_code (Typed.weakenCode γ (Typed.baseCode γ)))
    (Typed.varCode γ (Typed.baseCode γ)) (model a A))
  dsimp only [Typed.Authoring.BasePoint.variable]
  rw [he]
  rfl

theorem baseVariable_fiber (c : (show Grpd.{1,1} from γ (model a A))) :
    Grothendieck.ι (Typed.baseCode γ (model a A) ⋙ Grpd.forgetToCat) c ⋙
      baseFunctor ((Typed.Authoring.BasePoint.variable hΓ).code (model a A)).down =
    𝟭 (AsSmall.{0} (SheafActionQuotient.Cech.Datum (a := a) A)) := by
  rw [baseVariable_sourceFunctor]
  rfl

/-- A whole-functor base-term identity determines the actual fixed-base
coefficient evaluation, with the existing fixed-base comparison retained. -/
theorem fiberCoefficientEvaluationOfTerm
    (F : AsSmall.{0} (SheafActionQuotient.Cech.Datum (a := a) A) ⥤
      CechMatching.Datum (baseDiagram a A).toDiagram)
    (hF : matchingEvaluation a A (.ext hΓ (.base hΓ)) ⋙
      (baseTermDiagram a (.ext hΓ (.base hΓ))
        (Typed.Authoring.BasePoint.variable hΓ).deriv A).functor =
      baseFunctor ((Typed.Authoring.BasePoint.variable hΓ).code (model a A)).down ⋙ F)
    (c : (show Grpd.{1,1} from γ (model a A))) :
    fiberTotalEvaluation a A hΓ (.base hΓ) c ⋙
      (baseCoefficientProjection a A hΓ).functor = F := by
    dsimp only [fiberTotalEvaluation, totalMatchingEvaluation]
    rw [Functor.assoc, Functor.assoc]
    rw [baseCoefficientProjection_variable_functor, hF, ← Functor.assoc,
      baseVariable_fiber]
    rfl

def baseEvaluationComparisonOfTerm
    (F : AsSmall.{0} (SheafActionQuotient.Cech.Datum (a := a) A) ⥤
      CechMatching.Datum (baseDiagram a A).toDiagram)
    (hF : matchingEvaluation a A (.ext hΓ (.base hΓ)) ⋙
      (baseTermDiagram a (.ext hΓ (.base hΓ))
        (Typed.Authoring.BasePoint.variable hΓ).deriv A).functor =
      baseFunctor ((Typed.Authoring.BasePoint.variable hΓ).code (model a A)).down ⋙ F)
    (c : (show Grpd.{1,1} from γ (model a A))) :
    familyEvaluation a A hΓ (.base hΓ) c ⋙
      ((baseFamilyIso a hΓ A).hom.app ((matchingEvaluation a A hΓ).obj c)) ≅ F :=
  baseEvaluationComparison a A hΓ c ≪≫
    eqToIso (fiberCoefficientEvaluationOfTerm a A hΓ F hF c)

/-- Equivalence of the independently supplied coefficient functor transfers
through the checked whole-functor identity to the actual base evaluation. -/
theorem familyEvaluation_base_isEquivalence_of_term
    (F : AsSmall.{0} (SheafActionQuotient.Cech.Datum (a := a) A) ⥤
      CechMatching.Datum (baseDiagram a A).toDiagram) [F.IsEquivalence]
    (hF : matchingEvaluation a A (.ext hΓ (.base hΓ)) ⋙
      (baseTermDiagram a (.ext hΓ (.base hΓ))
        (Typed.Authoring.BasePoint.variable hΓ).deriv A).functor =
      baseFunctor ((Typed.Authoring.BasePoint.variable hΓ).code (model a A)).down ⋙ F)
    (c : (show Grpd.{1,1} from γ (model a A))) :
    (familyEvaluation a A hΓ (.base hΓ) c).IsEquivalence := by
  let e := (baseFamilyIso a hΓ A).app ((matchingEvaluation a A hΓ).obj c)
  let : e.hom.IsEquivalence :=
    (CechMatching.Comprehension.Constant.equivalenceOfGrpdIso e).isEquivalence_functor
  let : (familyEvaluation a A hΓ (.base hΓ) c ⋙ e.hom).IsEquivalence :=
    Functor.isEquivalence_of_iso (baseEvaluationComparisonOfTerm a A hΓ F hF c).symm
  exact Functor.isEquivalence_of_comp_right _ e.hom

/-- The actual base-family evaluation is an equivalence at every source context.
The coefficient equivalence and base-term comparison discharge the intermediate
criterion without an effectiveness assumption on this evaluation. -/
theorem familyEvaluation_base_isEquivalence
    (c : (show Grpd.{1,1} from γ (model a A))) :
    (familyEvaluation a A hΓ (.base hΓ) c).IsEquivalence := by
  let : (primitiveCoefficientFunctor a A).IsEquivalence :=
    (primitiveCoefficientEquivalence a A).isEquivalence_functor
  exact familyEvaluation_base_isEquivalence_of_term a A hΓ
    (primitiveCoefficientFunctor a A)
    (matchingEvaluation_baseTerm a A (.ext hΓ (.base hΓ))
      (Typed.Authoring.BasePoint.variable hΓ).deriv) c

end SquareKit.SmoothQuotientCechLocal
