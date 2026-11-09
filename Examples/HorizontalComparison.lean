import Examples.GroupoidComparison
import SquareKit.Internal.PathTransport.ComparisonDiagonal
import SquareKit.Internal.PathTransport.ComparisonHorizontalIdentity

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

def remainingSignature : Signature.{0} where
  base := ⟨signature.base.right, signature.base.right, 𝟭 _⟩
  leftFiber := signature.rightFiber
  rightFiber := signature.rightFiber
  fiberMap := 𝟙 _

def remainingPoint : Comparison.Section (remainingSignature.baseFamily middle) where
  left := basePoint.right
  right := basePoint.right
  commutes := SquareKit.Internal.PathTransport.GroupoidModel.Section.familyImage_id _

def compositePoint := signature.horizontal_point remainingSignature rfl HEq.rfl rfl
  basePoint remainingPoint HEq.rfl

def compositeFiber := (signature.horizontal remainingSignature rfl HEq.rfl).fiber compositePoint

example : compositeFiber = (signature.fiber basePoint).horizontal
    (remainingSignature.fiber remainingPoint) rfl
    (signature.horizontal_fiber_middle remainingSignature rfl HEq.rfl rfl
      basePoint remainingPoint HEq.rfl) :=
  signature.horizontal_fiber remainingSignature rfl HEq.rfl rfl basePoint remainingPoint HEq.rfl

/-- Composition still sends the two distinct primitive inputs to one output. -/
example : (compositeFiber.map.app (Discrete.mk PUnit.unit)).obj (Discrete.mk false) =
    (compositeFiber.map.app (Discrete.mk PUnit.unit)).obj (Discrete.mk true) := rfl

example : (Family.diagonal family.left).extend =
    Context.diagonal (@Grpd.of (Extend family.left) Groupoid.ofIsGroupoid) :=
  Family.diagonal_extend family.left

example : (Family.diagonal family.left).identity
    (Section.diagonal chosenSection.left) (Section.diagonal chosenSection.left) =
      Family.diagonal (identityFamily family.left chosenSection.left chosenSection.left) :=
  Family.diagonal_identity family.left chosenSection.left chosenSection.left

example : (Signature.diagonal signature.base.left signature.leftFiber).fiber
    (Section.diagonal basePoint.left) =
      Family.diagonal (primitiveFiber signature.leftFiber basePoint.left) :=
  Signature.diagonal_fiber signature.leftFiber basePoint.left

private theorem comparison_map_heq {Γ : Comparison.Context} {A B : Comparison.Family Γ}
    (h : A = B) : HEq A.map B.map := by cases h; rfl

/-- Composing the noninvertible comparison with its identity continuation
still maps each selected C4 arrow to that very arrow. -/
theorem identity_selected (g : p ⟶ p) :
    (((family.horizontal remaining rfl HEq.rfl).identity compositeSection compositeSection).map.app
      (Discrete.mk PUnit.unit)).obj (Discrete.mk (selected false g)) = Discrete.mk g := by
  have law := Family.horizontal_identity family remaining chosenSection chosenSection
    remainingSection remainingSection rfl HEq.rfl HEq.rfl HEq.rfl
  have maps := eq_of_heq (comparison_map_heq law)
  exact (congrArg (fun t => (t.app (Discrete.mk PUnit.unit)).obj
    (Discrete.mk (selected false g))) maps).trans rfl

/-- The comparison does not identify distinct selected identity objects. -/
example : Function.Injective (fun g : p ⟶ p =>
    (((family.horizontal remaining rfl HEq.rfl).identity compositeSection compositeSection).map.app
      (Discrete.mk PUnit.unit)).obj (Discrete.mk (selected false g))) := by
  intro g h e
  exact congrArg Discrete.as ((identity_selected g).symm.trans (e.trans (identity_selected h)))

end Examples.HorizontalComparison
