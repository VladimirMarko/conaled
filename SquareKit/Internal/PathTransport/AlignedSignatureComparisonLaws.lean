import SquareKit.Internal.PathTransport.AlignedSignatureComparison
import SquareKit.Internal.PathTransport.GeneratedCylinderComposition
import SquareKit.Internal.PathTransport.GeneratedCylinderPostcompose

/-! Identity and composition laws at the direct universe-aligned endpoints. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.GroupoidModel.Comparison
open CategoryTheory CategoryTheory.Functor
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w
variable {C D : Type u} [Groupoid.{v} C] [Groupoid.{v} D]
variable {F G K : C ⥤ D} (P : C ⥤ Type w) (Q : D ⥤ Type w)

theorem alignedContextComparison_refl (α : P ⟶ F ⋙ Q)
    (h : α ≫ whiskerRight (Iso.refl F).hom Q = α)
    (hΓ : Typed.CtxDeriv.{max u v w + 1} Γ γ) :
    alignedContextComparison (Iso.refl F) P Q α α h hΓ = Iso.refl _ := by
  unfold alignedContextComparison
  simp only [alignedBaseIso, isoWhiskerRight_refl, isoWhiskerLeft_refl]
  apply SignatureCylinder.contextComparison_refl

theorem alignedContextComparison_trans (η : F ≅ G) (θ : G ≅ K)
    (α : P ⟶ F ⋙ Q) (β : P ⟶ G ⋙ Q) (δ : P ⟶ K ⋙ Q)
    (hη : α ≫ whiskerRight η.hom Q = β)
    (hθ : β ≫ whiskerRight θ.hom Q = δ)
    (hηθ : α ≫ whiskerRight (η ≪≫ θ).hom Q = δ)
    (hΓ : Typed.CtxDeriv.{max u v w + 1} Γ γ) :
    alignedContextComparison (η ≪≫ θ) P Q α δ hηθ hΓ =
      alignedContextComparison η P Q α β hη hΓ ≪≫
        alignedContextComparison θ P Q β δ hθ hΓ := by
  unfold alignedContextComparison
  simp only [alignedBaseIso, isoWhiskerRight_trans, isoWhiskerLeft_trans]
  apply SignatureCylinder.contextComparison_trans

/-- Equality of primitive fiber maps induces equality of the generated maps,
without reducing the full generated interpretation. -/
theorem alignedGenerated_fiber_eq {α β : P ⟶ F ⋙ Q} (h : α = β)
    (hΓ : Typed.CtxDeriv.{max u v w + 1} Γ γ) :
    generatedContextMap (alignedUniverseSignature F P Q α) hΓ =
      generatedContextMap (alignedUniverseSignature F P Q β) hΓ := by
  cases h
  rfl

theorem alignedContextComparison_congr (η θ : F ≅ G)
    {α α' : P ⟶ F ⋙ Q} {β β' : P ⟶ G ⋙ Q}
    (hη : η = θ) (hα : α = α') (hβ : β = β')
    (h : α ≫ whiskerRight η.hom Q = β)
    (h' : α' ≫ whiskerRight θ.hom Q = β')
    (hΓ : Typed.CtxDeriv.{max u v w + 1} Γ γ) :
    alignedContextComparison η P Q α β h hΓ =
      eqToIso (alignedGenerated_fiber_eq P Q hα hΓ) ≪≫
        alignedContextComparison θ P Q α' β' h' hΓ ≪≫
        (eqToIso (alignedGenerated_fiber_eq P Q hβ hΓ)).symm := by
  cases hη
  cases hα
  cases hβ
  simp

theorem alignedContextComparison_trans_transport (η : F ≅ G) (θ : G ≅ K)
    (α : P ⟶ F ⋙ Q) (β β' : P ⟶ G ⋙ Q) (δ : P ⟶ K ⋙ Q)
    (he : β = β')
    (hη : α ≫ whiskerRight η.hom Q = β)
    (hθ : β' ≫ whiskerRight θ.hom Q = δ)
    (hηθ : α ≫ whiskerRight (η ≪≫ θ).hom Q = δ)
    (hΓ : Typed.CtxDeriv.{max u v w + 1} Γ γ) :
    alignedContextComparison η P Q α β hη hΓ ≪≫
      eqToIso (alignedGenerated_fiber_eq P Q he hΓ) ≪≫
      alignedContextComparison θ P Q β' δ hθ hΓ =
    alignedContextComparison (η ≪≫ θ) P Q α δ hηθ hΓ := by
  cases he
  simp only [eqToIso_refl, Iso.refl_trans]
  exact (alignedContextComparison_trans P Q η θ α β δ hη hθ hηθ hΓ).symm

variable {E : Type u} [Groupoid.{v} E] (L : D ⥤ E) (R : E ⥤ Type w)

theorem alignedGenerated_comp (α : P ⟶ F ⋙ Q) (κ : Q ⟶ L ⋙ R)
    (hΓ : Typed.CtxDeriv.{max u v w + 1} Γ γ) :
    generatedContextMap (alignedUniverseSignature F P Q α) hΓ ⋙
      generatedContextMap (alignedUniverseSignature L Q R κ) hΓ =
    generatedContextMap (alignedUniverseSignature (F ⋙ L) P R
      (α ≫ whiskerLeft F κ)) hΓ :=
  Context.relabel_composition
    (GeneratedComposition.generatedCtx (alignedUniverseSignature F P Q α)
      (alignedUniverseSignature L Q R κ) rfl HEq.rfl hΓ) _ _ _ _ _ _

theorem alignedContextComparison_postcompose (η : F ≅ G)
    (α : P ⟶ F ⋙ Q) (β : P ⟶ G ⋙ Q) (κ : Q ⟶ L ⋙ R)
    (h : α ≫ whiskerRight η.hom Q = β)
    (hk : (α ≫ whiskerLeft F κ) ≫ whiskerRight (isoWhiskerRight η L).hom R =
      β ≫ whiskerLeft G κ)
    (hΓ : Typed.CtxDeriv.{max u v w + 1} Γ γ) :
    alignedContextComparison (isoWhiskerRight η L) P R
      (α ≫ whiskerLeft F κ) (β ≫ whiskerLeft G κ) hk hΓ =
      (eqToIso (alignedGenerated_comp P Q L R α κ hΓ)).symm ≪≫
        isoWhiskerRight (alignedContextComparison η P Q α β h hΓ)
          (generatedContextMap (alignedUniverseSignature L Q R κ) hΓ) ≪≫
        eqToIso (alignedGenerated_comp P Q L R β κ hΓ) := by
  exact SignatureCylinder.contextComparison_postcompose
    (alignedUniverseSignature F P Q α).base.map
    (alignedUniverseSignature L Q R κ).base.map
    (alignedUniverseSignature F P Q α).leftFiber
    (alignedUniverseSignature F P Q α).rightFiber
    (alignedUniverseSignature L Q R κ).rightFiber
    (alignedUniverseSignature F P Q α).fiberMap
    (alignedUniverseSignature L Q R κ).fiberMap
    (alignedBaseIso η P Q α β)
    (alignedUniverseSignature G P Q β).fiberMap
    (alignedFiber_square η P Q α β h)
    (alignedFiber_square (isoWhiskerRight η L) P R
      (α ≫ whiskerLeft F κ) (β ≫ whiskerLeft G κ) hk) hΓ

end SquareKit.Internal.PathTransport.GroupoidModel.Comparison
