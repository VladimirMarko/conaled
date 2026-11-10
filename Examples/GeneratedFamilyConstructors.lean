import SquareKit.SmoothQuotientCechFamilyEffectivity
import SquareKit.SmoothQuotientCechPrimitiveEffectivity
import SquareKit.SmoothQuotientCechGlobalEquivalence
import SquareKit.SmoothQuotientCechGlobalRestriction
import SquareKit.SmoothQuotientCechGlobalMatching
import SquareKit.SmoothQuotientCechBaseEffectivity
import SquareKit.SmoothQuotientCechGeneratedEffectivity
import SquareKit.SmoothQuotientCechGeneratedEmpty
import SquareKit.SmoothQuotientCechSubstitutionEvaluation
import SquareKit.SmoothQuotientCechIdentityEvaluation
import SquareKit.SmoothQuotientCechTermEvaluation
import SquareKit.SmoothQuotientGeneratedIdentityMatching
import SquareKit.SmoothQuotientGeneratedIdentityPaths
import SquareKit.SmoothQuotientCechBaseTermEvaluation
import SquareKit.Internal.PathTransport.GeneratedPrimitiveFiber
import SquareKit.SmoothQuotientComparison

/-! Constructor equations specialize to actual smooth quotient restrictions. -/
noncomputable section
namespace Examples.GeneratedFamilyConstructors
open CategoryTheory CategoryTheory.Functor SquareKit SheafActionQuotient SmoothOpenSite
open Internal.PathTransport GroupoidModel Comparison
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {H : Type} [Group H] {M X Y : Sheaf topology Type}
variable (a : Action (locallyConstantGroup H) M) (f : Y ⟶ X)
local notation "S" => SmoothQuotientComparison.signature (a := a) f
local notation "L" => SmoothQuotientSource.model a X
local notation "R" => SmoothQuotientSource.model a Y

/-- Restriction transports a primitive fiber along its supplied, possibly
context-dependent base term, retaining the complete natural transformation. -/
example (hΓ : Typed.CtxDeriv.{2} Γ γ)
    (hx : Typed.TmDeriv.{2} Γ γ .base (Typed.baseCode γ) x ξ) :
    generatedFamilyMap S hΓ (.fiber hx) =
      whiskerLeft (baseFunctor (ξ L).down) (whiskerRight (S).fiberMap discrete) ≫
        eqToHom (congrArg (· ⋙ setFamily (S).rightFiber)
          (generatedBaseTerm_commutes S hΓ hx)) :=
  generatedFamilyMap_fiber S hΓ hx

/-- The same equation applies to any generated substitution, including root
and path-tail maps; neither invertibility nor faithfulness is required. -/
example (hΓ : Typed.CtxDeriv.{2} Γ γ) (hΔ : Typed.CtxDeriv.{2} Δ δ)
    (hB : Typed.TyDeriv.{2} Γ γ B b) (hs : Typed.SubDeriv.{2} Δ δ Γ γ σ s) :
    generatedFamilyMap S hΔ (.sub hB hs) =
      whiskerLeft (s L).down (generatedFamilyMap S hΓ hB) ≫
        eqToHom (congrArg (· ⋙ (show (show Grpd.{1,1} from γ R) ⥤ Grpd.{1,1} from b R))
          (generatedSubstitution_commutes S hΓ hΔ hs)) :=
  generatedFamilyMap_sub S hΓ hΔ hB hs

/-- Independent primitive matching recovers an arbitrary supplied local value. -/
example (hΓ : Typed.CtxDeriv.{2} Γ γ)
    (hx : Typed.TmDeriv.{2} Γ γ .base (Typed.baseCode γ) x ξ)
    (A : SplitSheaf.Ty X) (d : SmoothQuotientGeneratedMatching.Datum a hΓ A)
    (z : (SmoothQuotientGeneratedMatching.relativeMatchingFamily a hΓ (.fiber hx) A).obj d) :
    HEq (((SmoothQuotientGeneratedMatching.primitiveCoefficientMatchingEquivalence a hΓ hx A d).functor.obj z).as.val)
      z.localFiber.as :=
  SmoothQuotientGeneratedMatching.primitiveCoefficientMatchingEquivalence_value a hΓ hx A d z

/-- Forgetting universe wrappers retains the supplied matching deformation. -/
example (A : SplitSheaf.Ty X)
    (d : CechMatching.Datum (SmoothQuotientGeneratedMatching.baseDiagram a A).toDiagram)
    (z : (SmoothQuotientGeneratedMatching.primitiveCoefficientValues a A).obj d) :
    (SmoothQuotientGeneratedMatching.coefficientValueEquiv a A d z).down.val = z.val.down :=
  SmoothQuotientGeneratedMatching.coefficientValueEquiv_value a A d z

/-- Actual evaluation keeps an arbitrary source matching deformation. -/
example (A : SplitSheaf.Ty X) (hΓ : Typed.CtxDeriv.{2} Γ γ)
    (hx : Typed.TmDeriv.{2} Γ γ .base (Typed.baseCode γ) x ξ)
    (c : (show Grpd.{1,1} from γ (SmoothQuotientCechLocal.model a A)))
    (z : ((Typed.fiberCode ξ) (SmoothQuotientCechLocal.model a A)).obj c) :
    HEq ((SmoothQuotientCechLocal.familyEvaluation a A hΓ (.fiber hx) c).obj z).localFiber.as
      (ULift.up.{1} z.as.down.val) :=
  SmoothQuotientCechLocal.primitiveEvaluation_value_heq a A hΓ hx c z

/-- Effectivity imposes no extra equation on the generated base term. -/
example (A : SplitSheaf.Ty X) (hΓ : Typed.CtxDeriv.{2} Γ γ)
    (hx : Typed.TmDeriv.{2} Γ γ .base (Typed.baseCode γ) x ξ)
    (c : (show Grpd.{1,1} from γ (SmoothQuotientCechLocal.model a A))) :
    (SmoothQuotientCechLocal.familyEvaluation a A hΓ (.fiber hx) c).IsEquivalence :=
  SmoothQuotientCechLocal.primitiveEvaluation_isEquivalence a A hΓ hx c

/-- A base binder retains the full quotient groupoid under global recovery. -/
example (A : SplitSheaf.Ty X)
    [Presheaf.IsLocallySurjective topology (SplitSheaf.p A).hom]
    (hΓ : Typed.CtxDeriv.{2} Γ γ) :
    (generatedContextMap (SmoothQuotientCechGlobal.signature a A) (.ext hΓ (.base hΓ))).IsEquivalence :=
  (SmoothQuotientCechGlobal.contextEquivalence a A (.ext hΓ (.base hΓ))).isEquivalence_functor

/-- The recovery comparison retains the selected arrow for an arbitrary datum. -/
example (A : SplitSheaf.Ty X)
    [Presheaf.IsLocallySurjective topology (SplitSheaf.p A).hom]
    (d : SheafActionQuotient.Cech.Datum (a := a) A) :
    (SmoothQuotientCechGlobal.localComparison a A).hom.app d = d.toDescent.comparison := rfl

/-- Canonical direct restriction is effective for a full quotient base binder. -/
example (A : SplitSheaf.Ty X)
    [Presheaf.IsLocallySurjective topology (SplitSheaf.p A).hom] :
    (SmoothQuotientGeneratedMatching.restrictionFunctor a
      (.ext .empty (.base .empty)) A).IsEquivalence := by
  have : (SmoothQuotientCechLocal.matchingEvaluation a A
      (.ext .empty (.base .empty))).IsEquivalence :=
    SmoothQuotientCechLocal.matchingEvaluation_ext_isEquivalence a A .empty (.base .empty)
      (SmoothQuotientCechLocal.familyEvaluation_base_isEquivalence a A .empty)
  exact SmoothQuotientCechGlobal.restrictionFunctor_isEquivalence a A _

/-- The full matching comparison retains its selected local recovery arrow. -/
example (A : SplitSheaf.Ty X)
    [Presheaf.IsLocallySurjective topology (SplitSheaf.p A).hom]
    (hΓ : Typed.CtxDeriv.{2} Γ γ)
    (c : (show Grpd.{1,1} from γ (SmoothQuotientCechLocal.model a A))) :
    ((SmoothQuotientCechGlobal.matchingComparison a A hΓ).hom.app c).localArrow =
      (SmoothQuotientCechGlobal.restrictionComparison a A hΓ).hom.app c := rfl
/-- Matching an identity type keeps the supplied local identity arrow. -/
example (hΓ : Typed.CtxDeriv.{2} Γ γ) (hB : Typed.TyDeriv.{2} Γ γ B b)
    (hx : Typed.TmDeriv.{2} Γ γ B b x ξ) (hy : Typed.TmDeriv.{2} Γ γ B b y η)
    (A : SplitSheaf.Ty X) (d : SmoothQuotientGeneratedMatching.Datum a hΓ A)
    (z : (SmoothQuotientGeneratedMatching.relativeMatchingFamily a hΓ
      (.identity hB hx hy) A).obj d) :
    HEq (((SmoothQuotientGeneratedMatching.identityMatchingEquivalence a hΓ hB hx hy A d).functor.obj z).as.val)
      z.localFiber.as :=
  SmoothQuotientGeneratedMatching.identityMatchingEquivalence_value a hΓ hB hx hy A d z

/-- The endpoint recovery is available for any generated section and source context. -/
example (hΓ : Typed.CtxDeriv.{2} Γ γ) (hB : Typed.TyDeriv.{2} Γ γ B b)
    (hx : Typed.TmDeriv.{2} Γ γ B b x ξ) (A : SplitSheaf.Ty X)
    (c : (show Grpd.{1,1} from γ (SmoothQuotientCechLocal.model a A))) :=
  (SmoothQuotientCechLocal.familyEvaluation_termComparison a A hΓ hB hx).endpoint c

/-- An independently supplied compatible identity arrow becomes precisely its
included local arrow in matching; it need not be reflexivity. -/
example (hΓ : Typed.CtxDeriv.{2} Γ γ) (hB : Typed.TyDeriv.{2} Γ γ B b)
    (hx : Typed.TmDeriv.{2} Γ γ B b x ξ) (hy : Typed.TmDeriv.{2} Γ γ B b y η)
    (A : SplitSheaf.Ty X) (d : SmoothQuotientGeneratedMatching.Datum a hΓ A)
    (p : (SmoothQuotientGeneratedMatching.identitySetData a hΓ hB hx hy A).MatchingSet d) :=
  SmoothQuotientGeneratedMatching.identityDatumArrowEquiv_local a hΓ hB hx hy A d p

/-- Actual identity evaluation needs only full faithfulness of the underlying
family evaluation, including all its nonidentity arrows. -/
example (hΓ : Typed.CtxDeriv.{2} Γ γ) (hB : Typed.TyDeriv.{2} Γ γ B b)
    (hx : Typed.TmDeriv.{2} Γ γ B b x ξ) (hy : Typed.TmDeriv.{2} Γ γ B b y η)
    (A : SplitSheaf.Ty X) (c : (show Grpd.{1,1} from γ (SmoothQuotientCechLocal.model a A)))
    [ (SmoothQuotientCechLocal.familyEvaluation a A hΓ hB c).Full]
    [ (SmoothQuotientCechLocal.familyEvaluation a A hΓ hB c).Faithful] :
    (SmoothQuotientCechLocal.familyEvaluation a A hΓ (.identity hB hx hy) c).IsEquivalence :=
  SmoothQuotientCechLocal.identityEvaluation_isEquivalence a A hΓ hB hx hy c

/-- Arbitrary substitutions preserve the actual fiber evaluation equivalence. -/
example (hΓ : Typed.CtxDeriv.{2} Γ γ) (hΔ : Typed.CtxDeriv.{2} Δ δ)
    (hB : Typed.TyDeriv.{2} Γ γ B b) (hs : Typed.SubDeriv.{2} Δ δ Γ γ σ s)
    (A : SplitSheaf.Ty X) (c : (show Grpd.{1,1} from δ (SmoothQuotientCechLocal.model a A)))
    [(SmoothQuotientCechLocal.familyEvaluation a A hΓ hB
      ((s (SmoothQuotientCechLocal.model a A)).down.obj c)).IsEquivalence] :
    (SmoothQuotientCechLocal.familyEvaluation a A hΔ (.sub hB hs) c).IsEquivalence :=
  SmoothQuotientCechLocal.substitutionEvaluation_isEquivalence a A hΓ hΔ hB hs c

/-- Weakening applies to an arbitrary extended context, without an equivalence
hypothesis on the projection substitution. -/
example (hΓ : Typed.CtxDeriv.{2} Γ γ) (hB : Typed.TyDeriv.{2} Γ γ B b)
    (hC : Typed.TyDeriv.{2} Γ γ C t) (A : SplitSheaf.Ty X)
    (c : (show Grpd.{1,1} from (Typed.extendCode γ t) (SmoothQuotientCechLocal.model a A)))
    [(SmoothQuotientCechLocal.familyEvaluation a A hΓ hB
      ((Typed.weakenCode γ t (SmoothQuotientCechLocal.model a A)).down.obj c)).IsEquivalence] :
    (SmoothQuotientCechLocal.familyEvaluation a A (.ext hΓ hC)
      (.sub hB (.weaken hΓ hC)) c).IsEquivalence :=
  SmoothQuotientCechLocal.substitutionEvaluation_isEquivalence a A hΓ (.ext hΓ hC)
    hB (.weaken hΓ hC) c

/-- A substituted identity family is effective without any recursive
fullness, faithfulness, or equivalence hypotheses. -/
example (hΓ : Typed.CtxDeriv.{2} Γ γ) (hΔ : Typed.CtxDeriv.{2} Δ δ)
    (hB : Typed.TyDeriv.{2} Γ γ B b) (hx : Typed.TmDeriv.{2} Γ γ B b x ξ)
    (hy : Typed.TmDeriv.{2} Γ γ B b y η) (hs : Typed.SubDeriv.{2} Δ δ Γ γ σ s)
    (A : SplitSheaf.Ty X) (c : (show Grpd.{1,1} from δ (SmoothQuotientCechLocal.model a A))) :
    (SmoothQuotientCechLocal.familyEvaluation a A hΔ (.sub (.identity hB hx hy) hs) c).IsEquivalence :=
  SmoothQuotientCechLocal.familyEvaluation_isEquivalence a A _ hΔ c

/-- Any generated binder extends an effective context. All recursive family
premises of the total matching criterion are discharged by the induction. -/
example (hΓ : Typed.CtxDeriv.{2} Γ γ) (hB : Typed.TyDeriv.{2} Γ γ B b)
    (A : SplitSheaf.Ty X)
    [(SmoothQuotientCechLocal.matchingEvaluation a A hΓ).IsEquivalence] :
    (SmoothQuotientCechLocal.matchingEvaluation a A (.ext hΓ hB)).IsEquivalence :=
  SmoothQuotientCechLocal.matchingEvaluation_ext_isEquivalence a A hΓ hB
    (SmoothQuotientCechLocal.familyEvaluation_isEquivalence a A hB hΓ)

end Examples.GeneratedFamilyConstructors
