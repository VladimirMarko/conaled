import SquareKit.Internal.PathTransport.AlignedSignatureComparison
import SquareKit.Internal.PathTransport.GeneratedBaseTermComparison

/-! Base-term squares retain selected comparisons through universe alignment. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.GroupoidModel.Comparison
open CategoryTheory CategoryTheory.Functor
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w
variable {C D : Type u} [Groupoid.{v} C] [Groupoid.{v} D]
variable {F G : C ⥤ D} (η : F ≅ G) (P : C ⥤ Type w) (Q : D ⥤ Type w)
variable (α : P ⟶ F ⋙ Q) (β : P ⟶ G ⋙ Q)
local notation "S" => alignedUniverseSignature F P Q α
local notation "T" => alignedUniverseSignature G P Q β
local notation "L" => Instance.universeModel C P
local notation "R" => Instance.universeModel D Q

theorem alignedContextComparison_baseTerm (h : α ≫ whiskerRight η.hom Q = β)
    (hΓ : Typed.CtxDeriv.{max u v w + 1} Γ γ)
    (hx : Typed.TmDeriv.{max u v w + 1} Γ γ .base (Typed.baseCode γ) x ξ) :
    isoWhiskerLeft (baseFunctor (ξ L).down) (alignedBaseIso η P Q α β) ≪≫
        eqToIso (generatedBaseTerm_commutes T hΓ hx) =
      eqToIso (generatedBaseTerm_commutes S hΓ hx) ≪≫
        isoWhiskerRight (alignedContextComparison η P Q α β h hΓ)
          (baseFunctor (ξ R).down) :=
  SignatureCylinder.contextComparison_baseTerm _ _ (alignedBaseIso η P Q α β) _ _ _
    (alignedFiber_square η P Q α β h) hΓ hx

end SquareKit.Internal.PathTransport.GroupoidModel.Comparison
