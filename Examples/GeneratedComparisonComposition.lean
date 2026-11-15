import Examples.GeneratedComparisonRestriction
import Examples.HorizontalComparison
import SquareKit.SmoothQuotientGeneratedComposition

/-! Generated composition at the dependent J caller, its reindexed branch and
its whole tail substitution, with the noninvertible selected-arrow signature. -/
noncomputable section
namespace Examples.GeneratedComparisonComposition
open CategoryTheory SquareKit SquareKit.Internal.PathTransport
open GroupoidModel Comparison Typed SignatureInterpretationMaps.DependentTail
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

theorem j_composition (S T : Comparison.Signature.{0})
    (h : S.base.right = T.base.left) (hB : HEq S.rightFiber T.leftFiber) :
    (interpretTm (Comparison.fullModel S) generic).Composes
      (interpretTm (Comparison.fullModel T) generic)
      (interpretTm (Comparison.fullModel (S.horizontal T h hB)) generic) := by
  rw [interpretTm_agrees, interpretTm_agrees, interpretTm_agrees]
  exact GeneratedComposition.generatedTm S T h hB generic

theorem branch_composition (S T : Comparison.Signature.{0})
    (h : S.base.right = T.base.left) (hB : HEq S.rightFiber T.leftFiber) :
    (interpretTm (Comparison.fullModel S) reindexedBranch).Composes
      (interpretTm (Comparison.fullModel T) reindexedBranch)
      (interpretTm (Comparison.fullModel (S.horizontal T h hB)) reindexedBranch) := by
  rw [interpretTm_agrees, interpretTm_agrees, interpretTm_agrees]
  exact GeneratedComposition.generatedTm S T h hB reindexedBranch

theorem tail_map_composition (S T : Comparison.Signature.{0})
    (h : S.base.right = T.base.left) (hB : HEq S.rightFiber T.leftFiber) :
    (interpretSub (Comparison.fullModel S) tailMap).Composes
      (interpretSub (Comparison.fullModel T) tailMap)
      (interpretSub (Comparison.fullModel (S.horizontal T h hB)) tailMap) := by
  rw [interpretSub_agrees, interpretSub_agrees, interpretSub_agrees]
  exact GeneratedComposition.generatedSub S T h hB tailMap

example := j_composition GroupoidComparison.signature HorizontalComparison.remainingSignature rfl HEq.rfl
example := branch_composition GroupoidComparison.signature HorizontalComparison.remainingSignature rfl HEq.rfl
example := tail_map_composition GroupoidComparison.signature HorizontalComparison.remainingSignature rfl HEq.rfl
example := GeneratedComposition.generatedTel GroupoidComparison.signature
  HorizontalComparison.remainingSignature rfl HEq.rfl tail

open SmoothOpenSite SheafActionQuotient
variable {H : Type} [Group H] {M X Y Z : Sheaf topology Type}
variable (a : Action (locallyConstantGroup H) M) (f : Y ⟶ X) (g : Z ⟶ Y)

example : generatedContextMap (SmoothQuotientComparison.signature (a := a) f) withFiber ⋙
    generatedContextMap (SmoothQuotientComparison.signature (a := a) g) withFiber =
    generatedContextMap (SmoothQuotientComparison.signature (a := a) (g ≫ f)) withFiber :=
  SmoothQuotientComparison.generatedContextMap_comp a f g withFiber

example : HEq
    (generatedFamilyMap (SmoothQuotientComparison.signature (a := a) f) withFiber command.motive.typing ≫
      CategoryTheory.Functor.whiskerLeft
        (generatedContextMap (SmoothQuotientComparison.signature (a := a) f) withFiber)
        (generatedFamilyMap (SmoothQuotientComparison.signature (a := a) g) withFiber command.motive.typing))
    (generatedFamilyMap (SmoothQuotientComparison.signature (a := a) (g ≫ f)) withFiber command.motive.typing) :=
  SmoothQuotientComparison.generatedFamilyMap_comp a f g withFiber command.motive.typing

end Examples.GeneratedComparisonComposition
