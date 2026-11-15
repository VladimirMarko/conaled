import SquareKit.Internal.PathTransport.TwoFamilyReindexLift
import SquareKit.Internal.PathTransport.TwoFunctorInverseData
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u v w uD vD wD uE vE wE
variable {Γ : Type u} [Bicategory.{w,v} Γ] [Strict Γ]
variable {Δ : Type uD} [Bicategory.{wD,vD} Δ] [Strict Δ]
variable (E : Family.{u,v,w,uE,vE,wE} Γ) (σ : StrictPseudofunctor Δ Γ)
theorem reindexHigher_map_injective
    (hσ : ∀{x y : Δ}, Function.Injective (σ.map (X := x) (Y := y)))
    {x y : Total (reindex σ E)} : Function.Injective ((reindexHigher E σ).map (X := x) (Y := y)) := by
  intro p q h
  apply Pseudofunctor.CoGrothendieck.ext (hσ (congrArg (fun k => k.base) h))
  exact congr_arg_heq (fun k => k.fiber) h

theorem reindexHigher_cell_injective
    (hσ : ∀{x y : Δ} {p q : x ⟶ y}, Function.Injective (σ.map₂ (f := p) (g := q)))
    {x y : Total (reindex σ E)} {p q : x ⟶ y} :
    Function.Injective ((reindexHigher E σ).map₂ (f := p) (g := q)) := by
  intro α β h
  apply Pseudofunctor.CoGrothendieck.Hom.ext _ _ (hσ (congrArg (fun k => k.base) h))
  have hf := congr_arg_heq (fun k : (reindexHigher E σ).map p ⟶ (reindexHigher E σ).map q => k.fiber) h
  apply eq_of_heq
  apply HEq.trans hf
  exact (comp_eqToHom_heq _ _).symm
end SquareKit.Internal.PathTransport.TwoFamily
