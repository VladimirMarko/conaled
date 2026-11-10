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

end Examples.GeneratedFamilyConstructors
