import Examples.GroupoidComparison
import SquareKit.Internal.PathTransport.ComparisonHorizontalReindex

/-! Horizontal composition retains the chosen arrows of the noninvertible
comparison fixture and composes its actual compatible section. -/
noncomputable section
namespace Examples.HorizontalComparison
open CategoryTheory SquareKit.Internal.PathTransport.GroupoidModel
open Comparison GroupoidComparison FamilyMapElimination
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

def middle : Context.{0} := ⟨context.right, context.right, 𝟭 _⟩
def remaining : Family middle := ⟨family.right, family.right, 𝟙 _⟩
def remainingSection : Comparison.Section remaining where
  left := chosenSection.right
  right := chosenSection.right
  commutes := SquareKit.Internal.PathTransport.GroupoidModel.Section.familyImage_id _

def compositeSection := chosenSection.horizontal remainingSection rfl HEq.rfl HEq.rfl

example : compositeSection.left = chosenSection.left := rfl
example : compositeSection.right = chosenSection.right := rfl

example : (family.horizontal remaining rfl HEq.rfl).extend =
    family.extend.horizontal remaining.extend (family.horizontal_middle remaining rfl HEq.rfl) :=
  family.horizontal_extend remaining rfl HEq.rfl

example (b : Bool) (g : p ⟶ p) :
    ((family.horizontal remaining rfl HEq.rfl).extend.map.map (loop b g)).fiber = g := by
  simp [Family.horizontal, Family.extend, remaining, middle, family, context, loop,
    familyMap, selected, collapse, Grothendieck.map, before, after, constant,
    Grpd.forgetToCat]
  rfl

example :
    (family.horizontal remaining rfl HEq.rfl).reindex
      ((Substitution.id context).horizontal (Substitution.id middle) rfl rfl HEq.rfl) =
    (family.reindex (Substitution.id context)).horizontal
      (remaining.reindex (Substitution.id middle)) rfl
      (family.horizontal_reindex_middle remaining (Substitution.id context)
        (Substitution.id middle) rfl rfl HEq.rfl HEq.rfl) :=
  family.horizontal_reindex remaining (Substitution.id context)
    (Substitution.id middle) rfl rfl HEq.rfl HEq.rfl

end Examples.HorizontalComparison
