import SquareKit.Internal.ClassifierDisplayComparison
import Examples.SplitSheafFamilies
import Examples.CoherentFamilyClassification

/-! A proper-cover sheaf consumer of coherent classification and comprehension.
Empty global fibers, distinct overlap restrictions, and a noninvertible code map
prevent the comparison from testing only constant or groupoidal families. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace Examples.ClassifierPresentationComparison
open CategoryTheory Opposite SquareKit
open SquareKit.CoherentFamilyClassification
open Examples.SheafImage Examples.SheafImage.Diamond Examples.SheafBaseChange
open Examples.SheafFamilies Examples.SheafFunctions Examples.SplitSheafFamilies

abbrev varyingCode := (code D.obj.Elements (Type)).obj varying.family

example : ClassifierDisplayComparison.extension D.obj varyingCode =
    (SplitSheaf.extension varying).obj := rfl

example (b : Bool) : IsEmpty (((decode _ _).obj varyingCode).obj
    (D.obj.elementsMk (op X) b)) := varying_empty b

example (b : Bool) :
    Nonempty (((decode _ _).obj varyingCode).obj (D.obj.elementsMk (op U) b)) ∧
    Nonempty (((decode _ _).obj varyingCode).obj (D.obj.elementsMk (op V) b)) :=
  varying_local b

example (b : Bool) (a : Fiber varying U b) :
    varyingEquiv W b (((decode _ _).obj varyingCode).map
      (ElementFamilies.along D.obj (show W ⟶ U from Arrow.wu).op b) a) = false := rfl

example (b : Bool) (a : Fiber varying V b) :
    varyingEquiv W b (((decode _ _).obj varyingCode).map
      (ElementFamilies.along D.obj (show W ⟶ V from Arrow.wv).op b) a) = true := rfl

example : ¬ Nonempty (SplitPresheaf.Tm ((decode _ _).obj varyingCode)) := varying_no_term

abbrev reversedCode := (code D.obj.Elements (Type)).obj reversed.family

/-- The classifier's derived comprehension recovers an actual inhabited pairing. -/
example : (ClassifierDisplayComparison.comprehension reversedCode).symm
    ⟨truePoint.hom, restrictedTerm⟩ = pairing.hom := rfl

/-- Two substitutions agree on both the dependent term and its extension map. -/
example : (ClassifierDisplayComparison.comprehension reversedCode).symm
    ⟨(negation ≫ base ≫ truePoint).hom, repeatedTerm⟩ =
      (negation ≫ base ≫ pairing).hom := rfl

/-- Substitution is a pullback, even for this family with empty fibers. -/
example : IsPullback (SplitPresheaf.lift reversed.family truePoint.hom)
    (SplitPresheaf.p (SplitPresheaf.tySub reversed.family truePoint.hom))
    (ClassifierDisplayComparison.projection D.obj reversedCode) truePoint.hom :=
  ClassifierDisplayComparison.extension_pullback reversedCode truePoint.hom

/-- The equivalence retains a concrete noninvertible map of non-strict codes. -/
theorem collapse_display_not_iso :
    ¬ IsIso ((ClassifierDisplayComparison.equivalence
      Examples.CategoryValuedEvaluation.context).functor.map
        Examples.CoherentFamilyClassification.collapse) := by
  intro h
  let := h
  exact Examples.CoherentFamilyClassification.collapse_not_iso
    (isIso_of_reflects_iso Examples.CoherentFamilyClassification.collapse
      (ClassifierDisplayComparison.equivalence Examples.CategoryValuedEvaluation.context).functor)

end Examples.ClassifierPresentationComparison
