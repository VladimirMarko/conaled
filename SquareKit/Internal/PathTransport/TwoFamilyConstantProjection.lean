import SquareKit.Internal.PathTransport.TwoFamilyModelData

/-! Projection from a constant-family extension retains its selected fiber. -/
namespace SquareKit.Internal.PathTransport.HigherInterpretation
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable (Γ : Type u) [Bicategory.{u,u} Γ] [Strict Γ] (C : StrictTwoCategory.{u,u,u})

def constantFiberProjection : TwoFamily.Total (constantFamily Γ C) ⥤ C where
  obj x := x.fiber
  map p := p.fiber
  map_id x := rfl
  map_comp p q := by
    change (𝟙 _ ≫ p.fiber ≫ q.fiber) = p.fiber ≫ q.fiber
    simp

variable (K : Type u) [Category.{u} K]
def discreteCategory : StrictTwoCategory.{u,u,u} := ⟨LocallyDiscrete K⟩

def constantDiscreteProjection :
    StrictPseudofunctor (TwoFamily.Total (constantFamily Γ (discreteCategory K))) (LocallyDiscrete K) :=
  StrictPseudofunctor.mk'' {
    obj := fun x => x.fiber
    map := fun p => p.fiber
    map₂ := fun α => eqToHom (by
      have e := LocallyDiscrete.eq_of_hom α.fiber
      change _ = 𝟙 _ ≫ _ at e
      simpa using e)
    map₂_id := fun _ => Subsingleton.elim _ _
    map₂_comp := fun _ _ => Subsingleton.elim _ _
    map_id := fun x => (constantFiberProjection Γ (discreteCategory K)).map_id x
    map_comp := fun p q => (constantFiberProjection Γ (discreteCategory K)).map_comp p q
    map₂_whisker_left := fun _ _ _ _ => Subsingleton.elim _ _
    map₂_whisker_right := fun _ _ => Subsingleton.elim _ _
  }

end SquareKit.Internal.PathTransport.HigherInterpretation
