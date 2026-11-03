import SquareKit.Internal.PathTransport.PathContext
import SquareKit.Internal.PathTransport.SectionNormalization

/-!
# Section-valued contextual elimination

Normalized path contraction and its dependent telescope lifts produce
sections in the original split family, with strict reflexive computation.
-/
noncomputable section
namespace SquareKit.Internal.PathTransport.GroupoidModel
open CategoryTheory ContextualElimination
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {D C : Cat.{u,u}} (e : NormalizedEquivalence D C) (A : C ⥤ Grpd.{u,u})

def eliminateSection (d : Section (e.equiv.functor ⋙ A)) : Section A :=
  Section.ofOver
    (e.eliminate (pair A e.equiv.functor d) rfl)
    (extend_over _ _ _ _ _)

@[simp] theorem eliminateSection_beta (d : Section (e.equiv.functor ⋙ A)) :
    (eliminateSection e A d).reindex e.equiv.functor = d := by
  apply pair_injective e.equiv.functor
  change e.equiv.functor ⋙ (eliminateSection e A d).lift = pair A e.equiv.functor d
  rw [eliminateSection, Section.ofOver_lift]
  exact e.eliminate_beta _ _

end SquareKit.Internal.PathTransport.GroupoidModel
