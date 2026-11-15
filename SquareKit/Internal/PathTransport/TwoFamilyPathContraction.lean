import SquareKit.Internal.PathTransport.TwoFamilyPathContext
/-! Components of contraction in the actual general higher path context. -/
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u v w uΓ vΓ wΓ
variable {Γ : Type uΓ} [Bicategory.{wΓ,vΓ} Γ] [Bicategory.Strict Γ]
variable (F : Family.{uΓ,vΓ,wΓ,u,v,w} Γ)
variable [∀ γ, IsGroupoid (F.obj γ)] [∀ γ, IsLocallyGroupoid (F.obj γ)]
/-- The endpoint arrow from the reflexive source to an arbitrary path. -/
noncomputable def contractionEndpoint (x : PathContext F) :
    (pathReflexivityObj F ((pathFirst F).obj x)).base ⟶ x.base :=
  ⟨𝟙 x.base.base, ((identity F ((pathFirst F).obj x)).fiber,
    (identity F ((pathFirst F).obj x)).fiber ≫ x.fiber.as)⟩

/-- The canonical endpoint arrow sends the identity path to the supplied path. -/
theorem contractionBoundary (x : PathContext F) :
    (openIdMap F (contractionEndpoint F x)).obj (𝟙 x.base.fiber.1) = x.fiber.as := by
  let c : (F.map (𝟙 x.base.base)).obj x.base.fiber.1 ⟶ x.base.fiber.1 :=
    (identity F (⟨x.base.base, x.base.fiber.1⟩ : Total F)).fiber
  let : IsIso c := IsGroupoid.all_isIso _
  change inv c ≫ (F.map (𝟙 x.base.base)).map (𝟙 x.base.fiber.1) ≫
    (c ≫ x.fiber.as) = x.fiber.as
  rw [(F.map (𝟙 x.base.base)).map_id]
  simp

/-- A component in the actual total path context, with its required fiber boundary. -/
noncomputable def contractionComponent (x : PathContext F) :
    pathReflexivityObj F ((pathFirst F).obj x) ⟶ x :=
  ⟨contractionEndpoint F x, eqToHom (congrArg LocallyDiscrete.mk (contractionBoundary F x))⟩
/-- At reflexivity the endpoint contraction is exactly the identity. -/
theorem contractionEndpoint_refl (x : Total F) :
    contractionEndpoint F (pathReflexivityObj F x) = 𝟙 (pathReflexivityObj F x).base := by
  apply Pseudofunctor.CoGrothendieck.ext
  · rfl
  · apply heq_of_eq
    apply Prod.ext
    · change (identity F x).fiber = (identity (endpointFamily F) ⟨x.base, (x.fiber,x.fiber)⟩).fiber.1
      simp only [identity, TwoGroupoidHom.arrow]
      rw [CategoryTheory.eqToHom_fst]
    · change (identity F x).fiber ≫ 𝟙 x.fiber = (identity (endpointFamily F) ⟨x.base, (x.fiber,x.fiber)⟩).fiber.2
      rw [Category.comp_id]
      simp only [identity, TwoGroupoidHom.arrow]
      rw [CategoryTheory.eqToHom_snd]

private theorem canonicalArrow_eq {C D : Type*} [Category C] [Bicategory D] [Strict D]
    (E : C ⥤ D) (b : D) {p q : C} (e : p = q) (h : E.obj p = b) (k : E.obj q = b) :
    TwoGroupoidHom.arrow E b p (eqToHom h) = TwoGroupoidHom.arrow E b q (eqToHom k) := by
  cases e
  rfl

/-- The actual total contraction component is normalized at reflexivity. -/
theorem contractionComponent_refl (x : Total F) :
    contractionComponent F (pathReflexivityObj F x) = 𝟙 (pathReflexivityObj F x) := by
  exact canonicalArrow_eq (evaluation (openIdHigher F) (pathReflexivityObj F x).fiber)
    (pathReflexivityObj F x).fiber (contractionEndpoint_refl F x) _ _
end SquareKit.Internal.PathTransport.TwoFamily
