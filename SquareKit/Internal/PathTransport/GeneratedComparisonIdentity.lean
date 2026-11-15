import SquareKit.Internal.PathTransport.ComparisonDiagonalMap
import SquareKit.Internal.PathTransport.GeneratedComparisonRestriction

/-! Identity comparison for every generated context and family, extracted on
exactly the same semantic codes and including the complete arrow action. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.GroupoidModel.Comparison
open CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u

private theorem relabel_diagonal {C : Grpd.{u,u}} (Γ : Context.{u})
    (h : Context.diagonal C = Γ) (hL : Γ.left = C) (hR : Γ.right = C) :
    Γ.relabel hL hR = 𝟭 C := by cases h; rfl

private theorem relabelMap_diagonal {C : Grpd.{u,u}} {B : C ⥤ Grpd.{u,u}}
    {Γ : Context.{u}} (hΓ : Context.diagonal C = Γ) (A : Family Γ)
    (hA : HEq (Family.diagonal B) A) (hL : Γ.left = C) (hR : Γ.right = C)
    (hBL : HEq A.left B) (hBR : HEq A.right B) :
    HEq (A.relabelMap hL hR hBL hBR) (𝟙 B) := by
  cases hΓ; cases eq_of_heq hA; rfl

variable (C : Grpd.{u,u}) (B : C ⥤ Type u)
local notation "M" => Instance.fullModel C B
local notation "S" => Signature.diagonal C B

/-- The entire generated comparison context is diagonal, not only its objects. -/
theorem generated_diagonal_context (h : Typed.CtxDeriv.{u+1} Γ γ) :
    Context.diagonal (show Grpd.{u,u} from γ M) = γ (fullModel S) :=
  (diagonalSignatureMap C B).generatedCtx h

theorem generated_diagonal_family (h : Typed.TyDeriv.{u+1} Γ γ A a) :
    HEq (Family.diagonal (show (show Grpd.{u,u} from γ M) ⥤ Grpd.{u,u} from a M))
      (a (fullModel S)) := (diagonalSignatureMap C B).generatedTy h |>.2

theorem generatedContextMap_identity (h : Typed.CtxDeriv.{u+1} Γ γ) :
    generatedContextMap S h = 𝟭 (show Grpd.{u,u} from γ M) :=
  relabel_diagonal _ (generated_diagonal_context C B h) _ _

/-- Family identity uses HEq because its target functor is indexed by the
extracted context map; the preceding theorem identifies that map with identity. -/
theorem generatedFamilyMap_identity (hΓ : Typed.CtxDeriv.{u+1} Γ γ)
    (hA : Typed.TyDeriv.{u+1} Γ γ A a) :
    HEq (generatedFamilyMap S hΓ hA)
      (𝟙 (show (show Grpd.{u,u} from γ M) ⥤ Grpd.{u,u} from a M)) :=
  relabelMap_diagonal (generated_diagonal_context C B hΓ) _
    (generated_diagonal_family C B hA) _ _ _ _

end SquareKit.Internal.PathTransport.GroupoidModel.Comparison
