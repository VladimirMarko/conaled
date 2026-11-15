import SquareKit.Internal.PathTransport.CechMatchingIdentityCriterion
import SquareKit.SmoothQuotientGeneratedIdentityPaths
import SquareKit.SmoothQuotientCechTermEvaluation
import SquareKit.SmoothQuotientCechFamilyEvaluationRecovery

/-! Actual identity evaluation retains the hom map of the underlying family. -/
noncomputable section
namespace SquareKit.SmoothQuotientCechLocal
open CategoryTheory SheafActionQuotient SmoothOpenSite Internal.PathTransport
open GroupoidModel Comparison SmoothQuotientGeneratedMatching
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {H : Type} [Group H] {M X : Sheaf topology Type}
variable (a : Action (locallyConstantGroup H) M) (A : SplitSheaf.Ty X)
variable {Γ γ B b x ξ y η} (hΓ : Typed.CtxDeriv.{2} Γ γ)
variable (hB : Typed.TyDeriv.{2} Γ γ B b)
variable (hx : Typed.TmDeriv.{2} Γ γ B b x ξ) (hy : Typed.TmDeriv.{2} Γ γ B b y η)
variable (c : (show Grpd.{1,1} from γ (model a A)))

def identityEvaluationValues :=
  familyEvaluation a A hΓ (.identity hB hx hy) c ⋙
    (identityMatchingEquivalence a hΓ hB hx hy A ((matchingEvaluation a A hΓ).obj c)).functor

theorem identityEvaluationValues_local (p : (ξ (model a A)).down.obj c ⟶ (η (model a A)).down.obj c) :
    (((identityEvaluationValues a A hΓ hB hx hy c).obj (Discrete.mk p)).as).val =
      (generatedIdentitySetMap (signature a A) hΓ hB hx hy).app c p := by
  have h₀ := identityMatchingEquivalence_value a hΓ hB hx hy A
    ((matchingEvaluation a A hΓ).obj c)
    ((familyEvaluation a A hΓ (.identity hB hx hy) c).obj (Discrete.mk p))
  have h₁ := familyEvaluation_localComponent a A hΓ (.identity hB hx hy) c (Discrete.mk p)
  have h₂ := congrArg Discrete.as (eq_of_heq h₁)
  change _ = (((generatedFamilyMap (signature a A) hΓ (.identity hB hx hy)).app c).obj
    (Discrete.mk p)).as at h₂
  rw [generatedFamilyMap_identity_set] at h₂
  exact (eq_of_heq h₀).trans h₂

theorem fiberTotalEvaluation_localArrow {s t : (b (model a A)).obj c} (p : s ⟶ t) :
    ((fiberTotalEvaluation a A hΓ hB c).map p).localArrow =
      (localMap a A (.ext hΓ hB)).map
        ((Grothendieck.ι (b (model a A) ⋙ Grpd.forgetToCat) c).map p) := rfl

theorem identityEvaluationValues_included
    (p : (ξ (model a A)).down.obj c ⟶ (η (model a A)).down.obj c) :
    ((identityDatumArrowEquiv a hΓ hB hx hy A ((matchingEvaluation a A hΓ).obj c)
      (((identityEvaluationValues a A hΓ hB hx hy c).obj (Discrete.mk p)).as)).val).localArrow =
      (Grothendieck.ι ((relativeFamilyData a hΓ hB A).localFamily ⋙ Grpd.forgetToCat)
        ((matchingEvaluation a A hΓ).obj c).localObject).map
          ((generatedIdentitySetMap (signature a A) hΓ hB hx hy).app c p) := by
  exact (identityDatumArrowEquiv_local a hΓ hB hx hy A _ _).trans
    (congrArg (fun q => (Grothendieck.ι
      ((relativeFamilyData a hΓ hB A).localFamily ⋙ Grpd.forgetToCat)
        ((matchingEvaluation a A hΓ).obj c).localObject).map q)
      (identityEvaluationValues_local a A hΓ hB hx hy c p))

theorem identityEvaluation_conjugateLocal
    (ex : (localMap a A (.ext hΓ hB)).obj ((ξ (model a A)).down.lift.obj c) =
      (ξ (SmoothQuotientSource.model a (SplitSheaf.Ext A))).down.lift.obj ((localMap a A hΓ).obj c))
    (ey : (localMap a A (.ext hΓ hB)).obj ((η (model a A)).down.lift.obj c) =
      (η (SmoothQuotientSource.model a (SplitSheaf.Ext A))).down.lift.obj ((localMap a A hΓ).obj c))
    (p : (ξ (model a A)).down.obj c ⟶ (η (model a A)).down.obj c) :
    (Grothendieck.ι ((relativeFamilyData a hΓ hB A).localFamily ⋙ Grpd.forgetToCat)
      ((localMap a A hΓ).obj c)).map
        ((generatedIdentitySetMap (signature a A) hΓ hB hx hy).app c p) =
      eqToHom ex.symm ≫ (localMap a A (.ext hΓ hB)).map
        ((Grothendieck.ι (b (model a A) ⋙ Grpd.forgetToCat) c).map p) ≫ eqToHom ey :=
  generatedIdentity_conjugate (signature a A) hΓ hB hx hy
    (localMap a A (.ext hΓ hB)) (localMap_extend a A hΓ hB) c ex ey p

theorem identityValuesEffectivityAt
    (ex : (fiberTotalEvaluation a A hΓ hB c).obj ((ξ (model a A)).down.obj c) =
      (termDiagram a hΓ hB hx A).functor.obj ((matchingEvaluation a A hΓ).obj c))
    (ey : (fiberTotalEvaluation a A hΓ hB c).obj ((η (model a A)).down.obj c) =
      (termDiagram a hΓ hB hy A).functor.obj ((matchingEvaluation a A hΓ).obj c))
    [ (familyEvaluation a A hΓ hB c).Full] [ (familyEvaluation a A hΓ hB c).Faithful] :
    (identityEvaluationValues a A hΓ hB hx hy c).IsEquivalence :=
  letI : (CechMatching.Comprehension.fixedBaseFunctor
    (relativeFamilyData a hΓ hB A) (relativeFamilyCoherence a hΓ hB A)
    (fiberTotalEvaluation a A hΓ hB c) ((matchingEvaluation a A hΓ).obj c)
    (fiberTotalEvaluation_projection a A hΓ hB c)).Full :=
      inferInstanceAs (familyEvaluation a A hΓ hB c).Full
  letI : (CechMatching.Comprehension.fixedBaseFunctor
    (relativeFamilyData a hΓ hB A) (relativeFamilyCoherence a hΓ hB A)
    (fiberTotalEvaluation a A hΓ hB c) ((matchingEvaluation a A hΓ).obj c)
    (fiberTotalEvaluation_projection a A hΓ hB c)).Faithful :=
      inferInstanceAs (familyEvaluation a A hΓ hB c).Faithful
  CechMatching.Comprehension.identityValues_isEquivalence
    (relativeFamilyData a hΓ hB A) (relativeFamilyCoherence a hΓ hB A)
    (fiberTotalEvaluation a A hΓ hB c) ((matchingEvaluation a A hΓ).obj c)
    (fiberTotalEvaluation_projection a A hΓ hB c)
    ((ξ (model a A)).down.obj c) ((η (model a A)).down.obj c)
    ((termDiagram a hΓ hB hx A).functor.obj ((matchingEvaluation a A hΓ).obj c))
    ((termDiagram a hΓ hB hy A).functor.obj ((matchingEvaluation a A hΓ).obj c))
    (Functor.congr_obj (termMatching_projection a hΓ hB hx A) _)
    (Functor.congr_obj (termMatching_projection a hΓ hB hy A) _)
    ex
    ey
    (identityDatumArrowEquiv a hΓ hB hx hy A ((matchingEvaluation a A hΓ).obj c))
    (identityEvaluationValues a A hΓ hB hx hy c)
    (fun p => (Grothendieck.ι ((relativeFamilyData a hΓ hB A).localFamily ⋙ Grpd.forgetToCat)
      ((matchingEvaluation a A hΓ).obj c).localObject).map
        ((generatedIdentitySetMap (signature a A) hΓ hB hx hy).app c p))
    (fun p => (localMap a A (.ext hΓ hB)).map
      ((Grothendieck.ι (b (model a A) ⋙ Grpd.forgetToCat) c).map p))
    (identityEvaluationValues_included a A hΓ hB hx hy c)
    (fun p => identityEvaluation_conjugateLocal a A hΓ hB hx hy c
      (congrArg CechMatching.Datum.localObject
        ex)
      (congrArg CechMatching.Datum.localObject
        ey) p)
    (fiberTotalEvaluation_localArrow a A hΓ hB c)

/-- Identity evaluation is effective as soon as the underlying actual family
comparison is fully faithful. Surjectivity of underlying objects is unnecessary. -/
theorem identityEvaluation_isEquivalenceAt
    (ex : (fiberTotalEvaluation a A hΓ hB c).obj ((ξ (model a A)).down.obj c) =
      (termDiagram a hΓ hB hx A).functor.obj ((matchingEvaluation a A hΓ).obj c))
    (ey : (fiberTotalEvaluation a A hΓ hB c).obj ((η (model a A)).down.obj c) =
      (termDiagram a hΓ hB hy A).functor.obj ((matchingEvaluation a A hΓ).obj c))
    [ (familyEvaluation a A hΓ hB c).Full] [ (familyEvaluation a A hΓ hB c).Faithful] :
    (familyEvaluation a A hΓ (.identity hB hx hy) c).IsEquivalence := by
  let G := identityMatchingEquivalence a hΓ hB hx hy A ((matchingEvaluation a A hΓ).obj c)
  let : G.functor.IsEquivalence := G.isEquivalence_functor
  let : (familyEvaluation a A hΓ (.identity hB hx hy) c ⋙ G.functor).IsEquivalence :=
    identityValuesEffectivityAt a A hΓ hB hx hy c
      ex ey
  exact Functor.isEquivalence_of_comp_right _ G.functor

theorem identityEvaluation_isEquivalence
    [ (familyEvaluation a A hΓ hB c).Full] [ (familyEvaluation a A hΓ hB c).Faithful] :
    (familyEvaluation a A hΓ (.identity hB hx hy) c).IsEquivalence :=
  identityEvaluation_isEquivalenceAt a A hΓ hB hx hy c
    (sectionFiberEndpoint a A hΓ hB hx c)
    (sectionFiberEndpoint a A hΓ hB hy c)

end SquareKit.SmoothQuotientCechLocal
