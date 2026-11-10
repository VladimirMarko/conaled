import SquareKit.Internal.PathTransport.GeneratedComparisonEquivalence

/-! Equivalences use the same normalized generated forward maps as restriction. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.GroupoidModel.Comparison
open CategoryTheory
set_option backward.isDefEq.respectTransparency false
universe u

private theorem relabel_equivalence (Γ : Context.{u}) [Γ.map.IsEquivalence]
    {C D : Grpd.{u,u}} (hC : Γ.left = C) (hD : Γ.right = D) :
    (Γ.relabel hC hD).IsEquivalence := by subst C; subst D; assumption

private theorem relabel_fiber_equivalences {Γ : Context.{u}} (A : Family Γ)
    (h : A.FiberEquivalences) {C D : Grpd.{u,u}} (hC : Γ.left = C) (hD : Γ.right = D)
    {B : C ⥤ Grpd.{u,u}} {E : D ⥤ Grpd.{u,u}}
    (hB : HEq A.left B) (hE : HEq A.right E) :
    ∀ c, ((A.relabelMap hC hD hB hE).app c).IsEquivalence := by
  subst C; subst D
  cases eq_of_heq hB; cases eq_of_heq hE
  exact h

variable (S : Signature.{u}) [S.base.map.IsEquivalence]
    (hF : ∀ c, Function.Bijective (S.fiberMap.app c))

include hF

theorem generatedContextMap_equivalence (hΓ : Typed.CtxDeriv.{u+1} Γ γ) :
    (generatedContextMap S hΓ).IsEquivalence := by
  let : (γ (fullModel S)).map.IsEquivalence := GeneratedEquivalence.generatedCtx S hF hΓ
  exact relabel_equivalence _ _ _

theorem generatedFamilyMap_equivalences (hΓ : Typed.CtxDeriv.{u+1} Γ γ)
    (hA : Typed.TyDeriv.{u+1} Γ γ A a) :
    ∀ c, ((generatedFamilyMap S hΓ hA).app c).IsEquivalence :=
  relabel_fiber_equivalences _ (GeneratedEquivalence.generatedTy S hF hA) _ _ _ _

def generatedContextEquivalence (hΓ : Typed.CtxDeriv.{u+1} Γ γ) :
    (show Grpd.{u,u} from γ (Instance.fullModel S.base.left S.leftFiber)) ≌
      (show Grpd.{u,u} from γ (Instance.fullModel S.base.right S.rightFiber)) := by
  let := generatedContextMap_equivalence S hF hΓ
  exact (generatedContextMap S hΓ).asEquivalence

@[simp] theorem generatedContextEquivalence_functor (hΓ : Typed.CtxDeriv.{u+1} Γ γ) :
    (generatedContextEquivalence S hF hΓ).functor = generatedContextMap S hΓ := rfl

end SquareKit.Internal.PathTransport.GroupoidModel.Comparison
