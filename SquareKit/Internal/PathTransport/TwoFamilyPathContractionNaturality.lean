import SquareKit.Internal.PathTransport.TwoFamilyPathRetraction
import SquareKit.Internal.PathTransport.TwoFamilyPathContraction
import SquareKit.Internal.PathTransport.TwoPathContractionSquare
/-! Genuine endpoint comparison for path contraction; total naturality remains to be assembled. -/
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
/-- Normalized endpoint composite through reflexivity and the target contraction. -/
noncomputable def contractionLeftEndpoint {x y : PathContext F} (p : x ⟶ y) :
    (pathReflexivityObj F ((pathFirst F).obj x)).base ⟶ y.base :=
  ⟨p.base.base, (p.base.fiber.1, p.base.fiber.1 ≫ y.fiber.as)⟩
/-- Normalized endpoint composite through the source contraction and the supplied arrow. -/
noncomputable def contractionRightEndpoint {x y : PathContext F} (p : x ⟶ y) :
    (pathReflexivityObj F ((pathFirst F).obj x)).base ⟶ y.base :=
  ⟨p.base.base, (p.base.fiber.1, (F.map p.base.base).map x.fiber.as ≫ p.base.fiber.2)⟩
/-- The endpoint comparison retains the supplied path-family cell through its inverse mate. -/
noncomputable def contractionEndpointSquare {x y : PathContext F} (p : x ⟶ y) :
    contractionLeftEndpoint F p ⟶ contractionRightEndpoint F p := by
  let u : (F.map p.base.base).obj x.base.fiber.1 ⟶ y.base.fiber.1 := p.base.fiber.1
  letI : IsIso u := IsGroupoid.all_isIso _
  let σ := TwoIdentityTransport.pathSquare u ((F.map p.base.base).map x.fiber.as)
    p.base.fiber.2 y.fiber.as p.fiber.as
  let c : (contractionLeftEndpoint F p).fiber ⟶ (contractionRightEndpoint F p).fiber :=
    (𝟙 u, σ)
  refine TwoGroupoidHom.cell (E := evaluation (endpointFamily F) (x.base.fiber.1,x.base.fiber.1))
    (f := (contractionLeftEndpoint F p).fiber) (g := (contractionRightEndpoint F p).fiber)
    (𝟙 p.base.base) (c ≫ eqToHom ?_)
  change (u, (F.map p.base.base).map x.fiber.as ≫ p.base.fiber.2) =
    ((endpointFamily F).map₂ (𝟙 p.base.base)).app (x.base.fiber.1,x.base.fiber.1) ≫ _
  rw [(endpointFamily F).map₂_id]
  exact (Category.id_comp (contractionRightEndpoint F p).fiber).symm
end SquareKit.Internal.PathTransport.TwoFamily
