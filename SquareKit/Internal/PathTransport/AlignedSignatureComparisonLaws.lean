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

/-- Three compatible primitive squares generate the same selected cocycle. -/
theorem alignedContextComparison_cocycle (η : F ≅ G) (θ : G ≅ K) (ζ : F ≅ K)
    (α α' : P ⟶ F ⋙ Q) (β β' : P ⟶ G ⋙ Q) (δ δ' : P ⟶ K ⋙ Q)
    (hηθ : η ≪≫ θ = ζ) (ha : α = α') (hb : β = β') (hd : δ = δ')
    (hη : α ≫ whiskerRight η.hom Q = β)
    (hθ : β' ≫ whiskerRight θ.hom Q = δ)
    (hζ : α' ≫ whiskerRight ζ.hom Q = δ')
    (hΓ : Typed.CtxDeriv.{max u v w + 1} Γ γ) :
    alignedContextComparison η P Q α β hη hΓ ≪≫
      eqToIso (alignedGenerated_fiber_eq P Q hb hΓ) ≪≫
      alignedContextComparison θ P Q β' δ hθ hΓ =
    eqToIso (alignedGenerated_fiber_eq P Q ha hΓ) ≪≫
      alignedContextComparison ζ P Q α' δ' hζ hΓ ≪≫
      (eqToIso (alignedGenerated_fiber_eq P Q hd hΓ)).symm := by
  subst α'; subst β'; subst δ'; subst ζ
  simp only [eqToIso_refl, Iso.refl_symm, Iso.refl_trans, Iso.trans_refl]
  exact (alignedContextComparison_trans P Q η θ α β δ hη hθ hζ hΓ).symm

/-- Equality of signatures at explicitly identified primitive base functors. -/
theorem alignedGenerated_eq {F' : C ⥤ D} {α : P ⟶ F ⋙ Q} {α' : P ⟶ F' ⋙ Q}
    (hF : F = F') (hα : HEq α α') (hΓ : Typed.CtxDeriv.{max u v w + 1} Γ γ) :
    generatedContextMap (alignedUniverseSignature F P Q α) hΓ =
      generatedContextMap (alignedUniverseSignature F' P Q α') hΓ := by
  subst F'
  cases eq_of_heq hα
  rfl

/-- The selected cocycle with separately presented primitive vertices. -/
theorem alignedContextComparison_cocycle_presentations
    {F₁ F₂ G₁ G₂ H₁ H₂ : C ⥤ D}
    (η : F₁ ≅ F₂) (θ : G₁ ≅ G₂) (ζ : H₁ ≅ H₂)
    (α : P ⟶ F₁ ⋙ Q) (β : P ⟶ F₂ ⋙ Q)
    (β' : P ⟶ G₁ ⋙ Q) (δ : P ⟶ G₂ ⋙ Q)
    (α' : P ⟶ H₁ ⋙ Q) (δ' : P ⟶ H₂ ⋙ Q)
    (hm : F₂ = G₁) (hf : F₁ = H₁) (hl : G₂ = H₂)
    (ha : HEq α α') (hb : HEq β β') (hd : HEq δ δ')
    (hηθ : η ≪≫ eqToIso hm ≪≫ θ = eqToIso hf ≪≫ ζ ≪≫ (eqToIso hl).symm)
    (hη : α ≫ whiskerRight η.hom Q = β)
    (hθ : β' ≫ whiskerRight θ.hom Q = δ)
    (hζ : α' ≫ whiskerRight ζ.hom Q = δ')
    (hΓ : Typed.CtxDeriv.{max u v w + 1} Γ γ) :
    alignedContextComparison η P Q α β hη hΓ ≪≫
      eqToIso (alignedGenerated_eq P Q hm hb hΓ) ≪≫
      alignedContextComparison θ P Q β' δ hθ hΓ =
    eqToIso (alignedGenerated_eq P Q hf ha hΓ) ≪≫
      alignedContextComparison ζ P Q α' δ' hζ hΓ ≪≫
      (eqToIso (alignedGenerated_eq P Q hl hd hΓ)).symm := by
  subst G₁; subst H₁; subst H₂
  cases eq_of_heq ha; cases eq_of_heq hb; cases eq_of_heq hd
  simp only [eqToIso_refl, Iso.refl_symm, Iso.refl_trans, Iso.trans_refl] at hηθ ⊢
  subst ζ
  exact (alignedContextComparison_trans P Q η θ α β δ hη hθ hζ hΓ).symm

/-- A primitive triangle packages its three presentations before generation. -/
structure AlignedTriangle where
  F₁ : C ⥤ D
  F₂ : C ⥤ D
  G₁ : C ⥤ D
  G₂ : C ⥤ D
  H₁ : C ⥤ D
  H₂ : C ⥤ D
  η : F₁ ≅ F₂
  θ : G₁ ≅ G₂
  ζ : H₁ ≅ H₂
  α : P ⟶ F₁ ⋙ Q
  β : P ⟶ F₂ ⋙ Q
  β' : P ⟶ G₁ ⋙ Q
  δ : P ⟶ G₂ ⋙ Q
  α' : P ⟶ H₁ ⋙ Q
  δ' : P ⟶ H₂ ⋙ Q
  hm : F₂ = G₁
  hf : F₁ = H₁
  hl : G₂ = H₂
  ha : HEq α α'
  hb : HEq β β'
  hd : HEq δ δ'
  cocycle : η ≪≫ eqToIso hm ≪≫ θ = eqToIso hf ≪≫ ζ ≪≫ (eqToIso hl).symm
  squareη : α ≫ whiskerRight η.hom Q = β
  squareθ : β' ≫ whiskerRight θ.hom Q = δ
  squareζ : α' ≫ whiskerRight ζ.hom Q = δ'

namespace AlignedTriangle
variable {P Q} (T : AlignedTriangle P Q)

theorem generatedCocycle (hΓ : Typed.CtxDeriv.{max u v w + 1} Γ γ) :
    alignedContextComparison T.η P Q T.α T.β T.squareη hΓ ≪≫
      eqToIso (alignedGenerated_eq P Q T.hm T.hb hΓ) ≪≫
      alignedContextComparison T.θ P Q T.β' T.δ T.squareθ hΓ =
    eqToIso (alignedGenerated_eq P Q T.hf T.ha hΓ) ≪≫
      alignedContextComparison T.ζ P Q T.α' T.δ' T.squareζ hΓ ≪≫
      (eqToIso (alignedGenerated_eq P Q T.hl T.hd hΓ)).symm :=
  alignedContextComparison_cocycle_presentations P Q T.η T.θ T.ζ
    T.α T.β T.β' T.δ T.α' T.δ' T.hm T.hf T.hl T.ha T.hb T.hd
    T.cocycle T.squareη T.squareθ T.squareζ hΓ

end AlignedTriangle

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
