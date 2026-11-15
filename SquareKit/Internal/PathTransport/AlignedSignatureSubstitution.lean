import SquareKit.Internal.PathTransport.AlignedSignatureComparison
import SquareKit.Internal.PathTransport.GeneratedCylinderCoherence

/-! Selected aligned comparisons commute with every generated substitution. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.GroupoidModel.Comparison
open CategoryTheory CategoryTheory.Functor
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w
variable {C D : Type u} [Groupoid.{v} C] [Groupoid.{v} D]
variable {F G : C ⥤ D} (η : F ≅ G) (P : C ⥤ Type w) (Q : D ⥤ Type w)
variable (α : P ⟶ F ⋙ Q) (β : P ⟶ G ⋙ Q)

theorem alignedContextComparison_substitution (h : α ≫ whiskerRight η.hom Q = β)
    (hΓ : Typed.CtxDeriv.{max u v w + 1} Γ γ)
    (hΔ : Typed.CtxDeriv.{max u v w + 1} Δ δ)
    (hs : Typed.SubDeriv.{max u v w + 1} Δ δ Γ γ σ s) :
    isoWhiskerLeft (s (Instance.universeModel C P)).down
        (alignedContextComparison η P Q α β h hΓ) ≪≫
      eqToIso (generatedSubstitution_commutes (alignedUniverseSignature G P Q β) hΓ hΔ hs) =
    eqToIso (generatedSubstitution_commutes (alignedUniverseSignature F P Q α) hΓ hΔ hs) ≪≫
      isoWhiskerRight (alignedContextComparison η P Q α β h hΔ)
        (s (Instance.universeModel D Q)).down :=
  SignatureCylinder.contextComparison_substitution
    (alignedUniverseSignature F P Q α).base.map
    (alignedUniverseSignature F P Q α).leftFiber
    (alignedBaseIso η P Q α β)
    (alignedUniverseSignature F P Q α).rightFiber
    (alignedUniverseSignature F P Q α).fiberMap
    (alignedUniverseSignature G P Q β).fiberMap
    (alignedFiber_square η P Q α β h) hΓ hΔ hs

end SquareKit.Internal.PathTransport.GroupoidModel.Comparison
