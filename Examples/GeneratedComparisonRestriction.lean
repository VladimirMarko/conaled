import Examples.SignatureInterpretationMaps
import Examples.GroupoidComparison
import SquareKit.SmoothQuotientComparisonCoherence
import SquareKit.Internal.PathTransport.GeneratedComparisonLaws

/-! Whole-section restriction for the fresh dependent J caller and the
noninvertible C4 comparison signature. -/
noncomputable section
namespace Examples.GeneratedComparisonRestriction
open CategoryTheory SquareKit SquareKit.Internal.PathTransport
open GroupoidModel Comparison Typed SignatureInterpretationMaps.DependentTail
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- The J result over the two-binder tail respects the extracted comparison. -/
theorem j_restriction (S : Comparison.Signature.{0}) :
    (interpretTm (Instance.fullModel S.base.left S.leftFiber) generic).down.familyImage
      (generatedFamilyMap S withFiber command.motive.typing) =
    (interpretTm (Instance.fullModel S.base.right S.rightFiber) generic).down.reindex
      (generatedContextMap S withFiber) := by
  rw [interpretTm_agrees, interpretTm_agrees]
  exact generatedTerm_commutes S withFiber command.motive.typing generic

/-- The open weakening substitution gives a square on objects and arrows. -/
theorem weakening_restriction (S : Comparison.Signature.{0}) :
    (interpretSub (Instance.fullModel S.base.left S.leftFiber) weakening).down ⋙
      generatedContextMap S context =
    generatedContextMap S (CtxDeriv.ext context (TyDeriv.fiber point.deriv)) ⋙
      (interpretSub (Instance.fullModel S.base.right S.rightFiber) weakening).down := by
  rw [interpretSub_agrees, interpretSub_agrees]
  exact generatedSubstitution_commutes S context
    (CtxDeriv.ext context (TyDeriv.fiber point.deriv)) weakening

example := j_restriction GroupoidComparison.signature
example := weakening_restriction GroupoidComparison.signature

/-- Comprehension composition applies to the noninvertible fixture's actual map. -/
example : totalMap GroupoidComparison.context.map GroupoidComparison.family.map ⋙
    totalMap (A := GroupoidComparison.family.right) (B := GroupoidComparison.family.right)
      (𝟭 GroupoidComparison.context.right) (𝟙 GroupoidComparison.family.right) =
    totalMap (GroupoidComparison.context.map ⋙ 𝟭 GroupoidComparison.context.right)
      (GroupoidComparison.family.map ≫
        CategoryTheory.Functor.whiskerLeft GroupoidComparison.context.map
          (𝟙 GroupoidComparison.family.right)) :=
  totalMap_comp _ _ _ _

example (S : Comparison.Signature.{0}) :
    generatedContextMap S (.ext context (TyDeriv.fiber point.deriv)) =
      totalMap (generatedContextMap S context)
        (generatedFamilyMap S context (TyDeriv.fiber point.deriv)) :=
  generatedContextMap_extend S context (TyDeriv.fiber point.deriv)

open SmoothOpenSite SheafActionQuotient
variable {H : Type} [Group H] {M X Y Z : Sheaf topology Type}
variable (a : Action (locallyConstantGroup H) M)

example : SmoothQuotientComparison.signature (a := a) (𝟙 X) =
    SmoothQuotientComparison.identitySignature a X := SmoothQuotientComparison.signature_id

example (f : Y ⟶ X) (g : Z ⟶ Y) :
    SmoothQuotientComparison.signature (a := a) (g ≫ f) =
      SmoothQuotientComparison.compositeSignature (a := a) f g :=
  SmoothQuotientComparison.signature_comp f g

end Examples.GeneratedComparisonRestriction
