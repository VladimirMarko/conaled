import SquareKit.Internal.PathTransport.TwoFamilyPathContractionNaturality
import SquareKit.Internal.PathTransport.TwoPathContractionComparison
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
universe u v w uΓ vΓ wΓ
variable {Γ : Type uΓ} [Bicategory.{wΓ,vΓ} Γ] [Bicategory.Strict Γ]
variable (F : Family.{uΓ,vΓ,wΓ,u,v,w} Γ)
variable [∀ γ, IsGroupoid (F.obj γ)] [∀ γ, IsLocallyGroupoid (F.obj γ)]
private theorem casts_heq {C : Type*} [Category C] {a b a' b' : C}
    (h : a = b) (k : a' = b') (e : a = a') : HEq (eqToHom h) (eqToHom k) := by
  cases e; cases h; cases k; rfl
/-- The normalized endpoint comparison acts by the inverse of the genuine supplied path cell. -/
theorem contractionEndpointSquare_action {x y : PathContext F} (p : x ⟶ y) :
    HEq ((openIdCell F (contractionEndpointSquare F p)).app (𝟙 x.base.fiber.1))
      (inv (show (openIdMap F p.base).obj x.fiber.as ⟶ y.fiber.as from p.fiber.as)) := by
  let u : (F.map p.base.base).obj x.base.fiber.1 ⟶ y.base.fiber.1 := p.base.fiber.1
  let : IsIso u := IsGroupoid.all_isIso _
  let σ := TwoIdentityTransport.pathSquare u ((F.map p.base.base).map x.fiber.as)
    p.base.fiber.2 y.fiber.as p.fiber.as
  let e : (u, (F.map p.base.base).map x.fiber.as ≫ p.base.fiber.2) =
      ((endpointFamily F).map₂ (𝟙 p.base.base)).app (x.base.fiber.1,x.base.fiber.1) ≫
        (u, (F.map p.base.base).map x.fiber.as ≫ p.base.fiber.2) := by
    rw [(endpointFamily F).map₂_id]
    exact (Category.id_comp (contractionRightEndpoint F p).fiber).symm
  have hc : openIdCell F (contractionEndpointSquare F p) =
      TwoIdentityTransport.homComparison (StrictTwoTransformation.Trans.id (F.map p.base.base))
        (eqToHom (Category.id_comp u).symm)
        (σ ≫ eqToHom (Category.id_comp _).symm) := by
    apply eq_of_heq
    dsimp only [openIdCell]
    apply TwoIdentityTransport.homComparison_heq rfl rfl _ _
      (heq_of_eq (F.map₂_id p.base.base)) _ _ _ _ _ _ _ _
      (HEq.refl _) (HEq.refl _) (HEq.refl _) (HEq.refl _)
    · change HEq ((𝟙 u) ≫ (eqToHom e).1) (eqToHom (Category.id_comp u).symm)
      rw [CategoryTheory.eqToHom_fst, Category.id_comp]
      exact casts_heq _ _ rfl
    · change HEq (σ ≫ (eqToHom e).2) (σ ≫ eqToHom (Category.id_comp _).symm)
      rw [CategoryTheory.eqToHom_snd]
      exact HEq.trans (comp_eqToHom_heq _ _) (comp_eqToHom_heq _ _).symm
  rw [hc]
  apply HEq.trans (TwoIdentityTransport.homComparison_identity_path (F.map p.base.base) u σ)
  exact TwoIdentityTransport.pathSquare_cancel u _ _ _ p.fiber.as
/-- The normalized left endpoint sends reflexivity to the target path. -/
theorem contractionLeftBoundary {x y : PathContext F} (p : x ⟶ y) :
    (openIdMap F (contractionLeftEndpoint F p)).obj (𝟙 x.base.fiber.1) = y.fiber.as := by
  let u : (F.map p.base.base).obj x.base.fiber.1 ⟶ y.base.fiber.1 := p.base.fiber.1
  let : IsIso u := IsGroupoid.all_isIso _
  change inv u ≫ (F.map p.base.base).map (𝟙 x.base.fiber.1) ≫ (u ≫ y.fiber.as) = y.fiber.as
  rw [(F.map p.base.base).map_id]
  simp

/-- The normalized right endpoint sends reflexivity to the transported source path. -/
theorem contractionRightBoundary {x y : PathContext F} (p : x ⟶ y) :
    (openIdMap F (contractionRightEndpoint F p)).obj (𝟙 x.base.fiber.1) =
      (openIdMap F p.base).obj x.fiber.as := by
  let u : (F.map p.base.base).obj x.base.fiber.1 ⟶ y.base.fiber.1 := p.base.fiber.1
  let : IsIso u := IsGroupoid.all_isIso _
  change inv u ≫ (F.map p.base.base).map (𝟙 x.base.fiber.1) ≫
      ((F.map p.base.base).map x.fiber.as ≫ p.base.fiber.2) =
    inv u ≫ (F.map p.base.base).map x.fiber.as ≫ p.base.fiber.2
  rw [(F.map p.base.base).map_id]
  simp

/-- The normalized left composite lifted into the actual total path context. -/
noncomputable def contractionLeftArrow {x y : PathContext F} (p : x ⟶ y) :
    pathReflexivityObj F ((pathFirst F).obj x) ⟶ y :=
  ⟨contractionLeftEndpoint F p, Discrete.mk (eqToHom (contractionLeftBoundary F p))⟩
/-- The normalized right composite retains the original path-family cell. -/
noncomputable def contractionRightArrow {x y : PathContext F} (p : x ⟶ y) :
    pathReflexivityObj F ((pathFirst F).obj x) ⟶ y :=
  ⟨contractionRightEndpoint F p,
    Discrete.mk (eqToHom (contractionRightBoundary F p) ≫ p.fiber.as)⟩
/-- The normalized endpoint comparison lifts to a genuine cell in the actual total path context. -/
noncomputable def contractionLiftCell {x y : PathContext F} (p : x ⟶ y) :
    contractionLeftArrow F p ⟶ contractionRightArrow F p :=
  TwoGroupoidHom.cell (E := evaluation (openIdHigher F)
      (pathReflexivityObj F ((pathFirst F).obj x)).fiber)
    (f := (contractionLeftArrow F p).fiber) (g := (contractionRightArrow F p).fiber)
    (contractionEndpointSquare F p) (eqToHom (by
      apply Discrete.ext
      change eqToHom (contractionLeftBoundary F p) =
        (openIdCell F (contractionEndpointSquare F p)).app (𝟙 x.base.fiber.1) ≫
          (eqToHom (contractionRightBoundary F p) ≫ p.fiber.as)
      have h := (conj_eqToHom_iff_heq' _ _ (contractionLeftBoundary F p)
        (contractionRightBoundary F p).symm).2 (contractionEndpointSquare_action F p)
      rw [h]
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      rw [IsIso.inv_hom_id, Category.comp_id]))
end SquareKit.Internal.PathTransport.TwoFamily
