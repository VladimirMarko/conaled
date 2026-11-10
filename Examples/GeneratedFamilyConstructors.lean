import SquareKit.SmoothQuotientCechPrimitiveEffectivity
import SquareKit.SmoothQuotientCechGlobalEquivalence
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

end Examples.GeneratedFamilyConstructors
