import SquareKit.Internal.PathTransport.TwoFamilyPathRetraction
import SquareKit.Internal.PathTransport.TwoIdentityComparisonFaithful
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
universe u v w uΓ vΓ wΓ
variable {Γ : Type uΓ} [Bicategory.{wΓ,vΓ} Γ] [Bicategory.Strict Γ]
variable (F : Family.{uΓ,vΓ,wΓ,u,v,w} Γ)
variable [∀ γ, IsGroupoid (F.obj γ)] [∀ γ, IsLocallyGroupoid (F.obj γ)]
/-- Base cell, first endpoint cell and path action jointly determine an endpoint cell. -/
theorem openIdCell_joint_injective {x y : Total (endpointFamily F)} {p q : x ⟶ y} (α β : p ⟶ q)
    (r : x.fiber.1 ⟶ x.fiber.2) (hb : α.base = β.base)
    (hf : HEq α.fiber.1 β.fiber.1)
    (hc : (openIdCell F α).app r = (openIdCell F β).app r) : α = β := by
  rcases α with ⟨a,ρ,σ⟩
  rcases β with ⟨b,ρ',σ'⟩
  dsimp only at hb
  cases hb
  have hρ : ρ = ρ' := eq_of_heq hf
  cases hρ
  have hσ : σ = σ' := by
    exact TwoIdentityTransport.homComparison_second_injective (F.map₂ a) ρ σ σ' r hc
  cases hσ
  rfl
private theorem dep_congr {A : Sort*} {B : A → Sort*} (f : (a : A) → B a)
    {a b : A} (h : a = b) : HEq (f a) (f b) := by cases h; rfl
/-- The first endpoint projection is faithful on every actual path-context hom-category. -/
theorem pathFirst_cell_injective {x y : PathContext F} {p q : x ⟶ y}
    (α β : p ⟶ q) (h : (pathFirst F).map₂ α = (pathFirst F).map₂ β) : α = β := by
  have hb : α.base.base = β.base.base := congrArg (fun c => c.base) h
  have hf : HEq α.base.fiber.1 β.base.fiber.1 := by
    apply HEq.trans (pathFirst_cell_fiber_heq F α).symm
    apply HEq.trans _ (pathFirst_cell_fiber_heq F β)
    exact dep_congr (fun c => c.fiber) h
  have hc : (openIdCell F α.base).app x.fiber.as = (openIdCell F β.base).app x.fiber.as := by
    have ha := Discrete.eq_of_hom α.fiber
    have hb := Discrete.eq_of_hom β.fiber
    change p.fiber.as = (openIdCell F α.base).app x.fiber.as ≫ q.fiber.as at ha
    change p.fiber.as = (openIdCell F β.base).app x.fiber.as ≫ q.fiber.as at hb
    have hh := ha.symm.trans hb
    let τ : (openIdMap F q.base).obj x.fiber.as ⟶ y.fiber.as := q.fiber.as
    let : IsIso τ := IsGroupoid.all_isIso _
    exact (cancel_mono τ).1 hh
  refine Pseudofunctor.CoGrothendieck.Hom.ext _ _
    (openIdCell_joint_injective F α.base β.base x.fiber.as hb hf hc) ?_
  exact @Subsingleton.elim _ (Discrete.instSubsingletonDiscreteHom _ _) _ _
end SquareKit.Internal.PathTransport.TwoFamily
