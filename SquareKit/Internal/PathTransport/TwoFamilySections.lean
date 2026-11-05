import SquareKit.Internal.PathTransport.TwoFamilyHigherReindex
/-! Higher sections retain their complete action on base and fiber cells. -/
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u v w u' v' w'
variable {Γ : Type u} [Bicategory.{w,v} Γ] [Bicategory.Strict Γ]
/-- A section is a strict higher lift over identity, including genuine 2-cell action. -/
structure Section (F : Family.{u,v,w,u',v',w'} Γ) where
  lift : StrictPseudofunctor Γ (Total F)
  over : lift.comp (projectionHigher F) = StrictPseudofunctor.id Γ

/-- Context extension supplies the generic dependent variable in every dimension. -/
def variableLift (F : Family.{u,v,w,u',v',w'} Γ) :
    StrictPseudofunctor (Total F) (Total (reindex (projectionHigher F) F)) :=
  StrictPseudofunctor.mk'' {
    obj := fun x => ⟨x,x.fiber⟩
    map := fun p => ⟨p,p.fiber⟩
    map₂ := fun α => ⟨α,α.fiber⟩
  }

/-- The generic variable is a section of the family pulled back along projection. -/
def variableSection (F : Family.{u,v,w,u',v',w'} Γ) :
    Section (reindex (projectionHigher F) F) where
  lift := variableLift F
  over := StrictTwoTransformation.functor_ext rfl
end SquareKit.Internal.PathTransport.TwoFamily
