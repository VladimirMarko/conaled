import SquareKit.Internal.PathTransport.TwoFamilyPathContractionNaturality
import SquareKit.Internal.PathTransport.TwoFamilySigmaAction
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
/-- The contraction endpoint is the vertical inclusion of the identity and the supplied path. -/
theorem contractionEndpoint_inclusion (x : PathContext F) :
    contractionEndpoint F x =
      (fiberInclusion (endpointFamily F) x.base.base).map
        (show (x.base.fiber.1,x.base.fiber.1) ⟶ x.base.fiber from
          (𝟙 x.base.fiber.1, x.fiber.as)) := by
  apply Pseudofunctor.CoGrothendieck.ext
  · rfl
  · apply heq_of_eq
    apply Prod.ext
    · change (identity F ((pathFirst F).obj x)).fiber =
        (show ((endpointFamily F).map (𝟙 x.base.base)).obj
            (x.base.fiber.1,x.base.fiber.1) ⟶ (x.base.fiber.1,x.base.fiber.1) from eqToHom _).1 ≫ 𝟙 x.base.fiber.1
      rw [Category.comp_id, CategoryTheory.eqToHom_fst]
      rfl
    · change (identity F ((pathFirst F).obj x)).fiber ≫ x.fiber.as =
        (show ((endpointFamily F).map (𝟙 x.base.base)).obj
            (x.base.fiber.1,x.base.fiber.1) ⟶ (x.base.fiber.1,x.base.fiber.1) from eqToHom _).2 ≫ x.fiber.as
      rw [CategoryTheory.eqToHom_snd]
      rfl

/-- The first projection followed by reflexivity duplicates the original first endpoint arrow. -/
theorem reflexivityEndpoint_normal {x y : PathContext F} (p : x ⟶ y) :
    ((pathReflexivity F).map ((pathFirst F).map p)).base =
      (⟨p.base.base, (p.base.fiber.1,p.base.fiber.1)⟩ :
        Hom (endpointFamily F) (pathReflexivityObj F ((pathFirst F).obj x)).base
          (pathReflexivityObj F ((pathFirst F).obj y)).base) := by
  apply Pseudofunctor.CoGrothendieck.ext
  · rfl
  · apply heq_of_eq
    apply Prod.ext
    · exact (diagonal_fiber_fst F ((pathFirst F).map p)).trans (pathFirst_map_fiber F p)
    · exact (diagonal_fiber_snd F ((pathFirst F).map p)).trans (pathFirst_map_fiber F p)
/-- Cartesian factorization identifies the actual left endpoint composite. -/
theorem contractionLeftEndpoint_composite {x y : PathContext F} (p : x ⟶ y) :
    ((pathReflexivity F).map ((pathFirst F).map p)).base ≫ contractionEndpoint F y =
      contractionLeftEndpoint F p := by
  rw [reflexivityEndpoint_normal, contractionEndpoint_inclusion]
  let d : (pathReflexivityObj F ((pathFirst F).obj x)).base ⟶
      (pathReflexivityObj F ((pathFirst F).obj y)).base :=
    ⟨p.base.base,(p.base.fiber.1,p.base.fiber.1)⟩
  change d ≫ _ = _
  rw [← cartesianLift_factorization (endpointFamily F) d, Category.assoc]
  have hm := (fiberInclusionFunctor (endpointFamily F) y.base.base).map_comp d.fiber
    (show (y.base.fiber.1,y.base.fiber.1) ⟶ y.base.fiber from (𝟙 y.base.fiber.1,y.fiber.as))
  erw [← hm]
  have h : d.fiber ≫ (show (y.base.fiber.1,y.base.fiber.1) ⟶ y.base.fiber from
      (𝟙 y.base.fiber.1,y.fiber.as)) = (contractionLeftEndpoint F p).fiber := by
    apply Prod.ext
    · exact Category.comp_id _
    · rfl
  rw [h]
  exact cartesianLift_factorization (endpointFamily F) (contractionLeftEndpoint F p)
/-- Cartesian naturality identifies the actual right endpoint composite. -/
theorem contractionRightEndpoint_composite {x y : PathContext F} (p : x ⟶ y) :
    contractionEndpoint F x ≫ p.base = contractionRightEndpoint F p := by
  rw [contractionEndpoint_inclusion, ← cartesianLift_factorization (endpointFamily F) p.base,
    ← Category.assoc]
  erw [cartesianLift_naturality]
  rw [Category.assoc]
  have hm := (fiberInclusionFunctor (endpointFamily F) y.base.base).map_comp
    (((endpointFamily F).map p.base.base).map
      (show (x.base.fiber.1,x.base.fiber.1) ⟶ x.base.fiber from
        (𝟙 x.base.fiber.1,x.fiber.as))) p.base.fiber
  erw [← hm]
  have h : ((endpointFamily F).map p.base.base).map
      (show (x.base.fiber.1,x.base.fiber.1) ⟶ x.base.fiber from
        (𝟙 x.base.fiber.1,x.fiber.as)) ≫ p.base.fiber =
        (contractionRightEndpoint F p).fiber := by
    apply Prod.ext
    · change (F.map p.base.base).map (𝟙 x.base.fiber.1) ≫ p.base.fiber.1 = _
      rw [(F.map p.base.base).map_id, Category.id_comp]
      rfl
    · rfl
  rw [h]
  exact cartesianLift_factorization (endpointFamily F) (contractionRightEndpoint F p)
end SquareKit.Internal.PathTransport.TwoFamily
