import SquareKit.SmoothQuotientCechBaseEffectivity
import SquareKit.SmoothQuotientCechPrimitiveEffectivity
import SquareKit.SmoothQuotientCechIdentityEvaluation
import SquareKit.SmoothQuotientCechSubstitutionEvaluation
import SquareKit.SmoothQuotientCechDerivationInvariance
import SquareKit.Internal.PathTransport.TypedContexts
import SquareKit.Internal.PathTransport.TypedFamilyInduction

/-! Effective matching for every generated dependent family. -/
noncomputable section
namespace SquareKit.SmoothQuotientCechLocal
open CategoryTheory SheafActionQuotient SmoothOpenSite Internal.PathTransport
open GroupoidModel
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {H : Type} [Group H] {M X : Sheaf topology Type}
variable (a : Action (locallyConstantGroup H) M) (A : SplitSheaf.Ty X)

theorem familyEvaluation_isEquivalence (hB : Typed.TyDeriv.{2} Γ γ B b)
    (hΓ : Typed.CtxDeriv.{2} Γ γ) (c : (show Grpd.{1,1} from γ (model a A))) :
    (familyEvaluation a A hΓ hB c).IsEquivalence := by
  apply Typed.TyDeriv.familyInduction
    (fun {Γ γ B b} hB => ∀ (hΓ : Typed.CtxDeriv.{2} Γ γ)
      (c : (show Grpd.{1,1} from γ (model a A))),
      (familyEvaluation a A hΓ hB c).IsEquivalence) (hB := hB) _ _ _ _ hΓ c
  · intro Γ γ hΓ' hΓ c
    exact (familyEvaluation_derivation_iff a A hΓ (.base hΓ) (.base hΓ') c).mp
      (familyEvaluation_base_isEquivalence a A hΓ c)
  · intro Γ γ x ξ hx hΓ c
    exact primitiveEvaluation_isEquivalence a A hΓ hx c
  · intro Γ γ B b x ξ y η hB hx hy ih hΓ c
    let := ih hΓ c
    exact identityEvaluation_isEquivalence a A hΓ hB hx hy c
  · intro Γ γ B b Δ δ σ s hB hs ih hΔ c
    let := ih hB.context ((s (model a A)).down.obj c)
    exact substitutionEvaluation_isEquivalence a A hB.context hΔ hB hs c

end SquareKit.SmoothQuotientCechLocal
