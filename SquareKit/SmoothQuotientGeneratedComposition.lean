import SquareKit.SmoothQuotientGeneratedIdentity
import SquareKit.Internal.PathTransport.GeneratedComparisonCompositionMaps

/-! Parameter composition for every generated context and family of the
unchanged smooth quotient interpretation. -/
noncomputable section
namespace SquareKit.SmoothQuotientComparison
open CategoryTheory SheafActionQuotient SmoothOpenSite
open Internal.PathTransport GroupoidModel Comparison
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {H : Type} [Group H] {M X Y Z : Sheaf topology Type}
variable (a : Action (locallyConstantGroup H) M)

theorem generatedContextMap_comp (f : Y ⟶ X) (g : Z ⟶ Y) (hΓ : Typed.CtxDeriv.{2} Γ γ) :
    generatedContextMap (signature (a := a) f) hΓ ⋙ generatedContextMap (signature (a := a) g) hΓ =
      generatedContextMap (signature (a := a) (g ≫ f)) hΓ :=
  Context.relabel_composition
    (GeneratedComposition.generatedCtx (signature (a := a) f) (signature (a := a) g) rfl HEq.rfl hΓ)
    _ _ _ _ _ _

/-- The family law is HEq because the target functor is indexed by the context
restriction; generatedContextMap_comp supplies its strict identification. -/
theorem generatedFamilyMap_comp (f : Y ⟶ X) (g : Z ⟶ Y) (hΓ : Typed.CtxDeriv.{2} Γ γ)
    (hA : Typed.TyDeriv.{2} Γ γ A b) :
    HEq (generatedFamilyMap (signature (a := a) f) hΓ hA ≫
      CategoryTheory.Functor.whiskerLeft (generatedContextMap (signature (a := a) f) hΓ)
        (generatedFamilyMap (signature (a := a) g) hΓ hA))
      (generatedFamilyMap (signature (a := a) (g ≫ f)) hΓ hA) :=
  Family.relabel_composition
    (GeneratedComposition.generatedTy (signature (a := a) f) (signature (a := a) g) rfl HEq.rfl hA)
    _ _ _ _ _ _ _ _ _ _ _ _

end SquareKit.SmoothQuotientComparison
