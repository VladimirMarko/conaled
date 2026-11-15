import SquareKit.Internal.PathTransport.TwoFamilyReindexFaithful
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u v w uD vD wD uE vE wE
variable {Γ : Type u} [Bicategory.{w,v} Γ] [Strict Γ]
variable {Δ : Type uD} [Bicategory.{wD,vD} Δ] [Strict Δ]
variable (E : Family.{u,v,w,uE,vE,wE} Γ) (σ : StrictPseudofunctor Δ Γ)
theorem reindexHigher_obj_injective (hσ : Function.Injective σ.obj) : Function.Injective (reindexHigher E σ).obj := by
  rintro ⟨a, fa⟩ ⟨b, fb⟩ h
  have hb := hσ (congrArg (fun z => z.base) h)
  cases hb
  have hf := congr_arg_heq (fun z => z.fiber) h
  have hf' : fa = fb := eq_of_heq hf
  cases hf'
  rfl
variable {F : Family.{uD,vD,wD,uE,vE,wE} Δ} (e : F = reindex σ E)
theorem familySubstitution_obj_injective (hσ : Function.Injective σ.obj) :
    Function.Injective (familySubstitution E σ e).obj := by
  cases e
  rw [familySubstitution_reindex]
  exact reindexHigher_obj_injective E σ hσ
theorem familySubstitution_map_injective
    (hσ : ∀{x y : Δ}, Function.Injective (σ.map (X := x) (Y := y)))
    {x y : Total F} : Function.Injective ((familySubstitution E σ e).map (X := x) (Y := y)) := by
  cases e
  rw [familySubstitution_reindex]
  exact reindexHigher_map_injective E σ (@hσ)
theorem familySubstitution_cell_injective
    (hσ : ∀{x y : Δ} {p q : x ⟶ y}, Function.Injective (σ.map₂ (f := p) (g := q)))
    {x y : Total F} {p q : x ⟶ y} : Function.Injective ((familySubstitution E σ e).map₂ (f := p) (g := q)) := by
  cases e
  rw [familySubstitution_reindex]
  exact reindexHigher_cell_injective E σ (@hσ)
end SquareKit.Internal.PathTransport.TwoFamily
