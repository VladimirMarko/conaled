import SquareKit.SheafSectionsConstant
import Examples.SheafFamilies
import Examples.SheafSums

/-! Experimental internal sections on the diamond site. These ordinary
consumers coexist with the regular, function-space, and dependent sum clients. -/
noncomputable section
namespace Examples.SheafSections
open CategoryTheory Opposite SquareKit.SheafRelation
open Examples.SheafImage Examples.SheafImage.Diamond Examples.SheafBaseChange
open Examples.SheafFamilies Examples.SheafFunctions

/-- Use the constructed terminal sheaf, reached from the finite site's terminal. -/
def unitPoint : SheafImage.terminal ⟶ SquareKit.SheafSections.unit := Limits.terminal.from _

def negationTerm : SquareKit.Family.Term (snd D D) := ⟨lift negation (𝟙 D), rfl⟩
def negationSection := SquareKit.SheafSections.name (snd D D) negationTerm

/-- Constant-family currying agrees with the already used exponential name. -/
theorem negation_comparison :
    unitPoint ≫ negationSection ≫ (SquareKit.SheafSections.constantIso D D).hom = negationName := by
  have hc := SquareKit.SheafSections.constantIso_curry
    ((SquareKit.SheafSections.termEquiv (snd D D)).symm negationTerm)
  have hn := SquareKit.SheafFunction.curry_parameter
    (fst D SquareKit.SheafSections.unit ≫ negation) unitPoint
  change unitPoint ≫ SquareKit.SheafSections.curry (snd D D) _ ≫ _ = _
  rw [hc]
  exact hn.symm

theorem negation_false :
    (SquareKit.SheafSections.evaluation (snd D D)).hom.app (op X)
      (false, negationSection.hom.app (op X) (unitPoint.hom.app (op X) ())) = (true,false) :=
  SquareKit.SheafSections.evaluation_name_apply _ negationTerm _ _ _

theorem negation_true :
    (SquareKit.SheafSections.evaluation (snd D D)).hom.app (op X)
      (true, negationSection.hom.app (op X) (unitPoint.hom.app (op X) ())) = (false,true) :=
  SquareKit.SheafSections.evaluation_name_apply _ negationTerm _ _ _

/-- The exponential evaluation recovered through the comparison has the same value. -/
theorem negation_compared_value (b : Bool) :
    (SquareKit.SheafFunction.evaluation D D).hom.app (op X)
      (b, (unitPoint ≫ negationSection ≫ (SquareKit.SheafSections.constantIso D D).hom).hom.app
        (op X) ()) = !b := by
  rw [negation_comparison]
  exact evaluate_name negation (op X) b

theorem negation_eta :
    SquareKit.SheafSections.curry (snd D D)
      (SquareKit.SheafSections.uncurry (snd D D) negationSection) = negationSection :=
  SquareKit.SheafSections.eta _ _

/-- Nonidentity transport changes the parameter, preserving the classified section. -/
def negationParam : SquareKit.SheafSections.Param (snd D D) D :=
  ⟨lift (snd D D) (fst D D), rfl⟩

theorem negation_transport :
    SquareKit.SheafSections.curry (snd D D)
      (SquareKit.SheafSections.parameter (snd D D) negationParam negation) =
        negation ≫ SquareKit.SheafSections.curry (snd D D) negationParam :=
  SquareKit.SheafSections.curry_parameter _ _ _

theorem negation_transport_value (a b : Bool) :
    (SquareKit.SheafSections.evaluation (snd D D)).hom.app (op X)
      (a, (SquareKit.SheafSections.curry (snd D D)
        (SquareKit.SheafSections.parameter (snd D D) negationParam negation)).hom.app (op X) b) =
      (!b,a) :=
  SquareKit.SheafSections.evaluation_curry_apply _ _ _ _ _

theorem no_false_global :
    ¬ Nonempty (SquareKit.SheafSections.unit ⟶ SquareKit.SheafSections.sections falsePoint) := by
  rintro ⟨s⟩
  exact no_total_term ⟨SquareKit.SheafSections.globalEquiv falsePoint s⟩

/-- Name the existing term of the genuinely varying family after restriction. -/
def trueSection := SquareKit.SheafSections.name
  (SquareKit.Family.reindex reversedDisplay truePoint) trueTerm

theorem trueSection_evaluation (U : Diamondᵒᵖ) :
    (SquareKit.SheafSections.evaluation (SquareKit.Family.reindex reversedDisplay truePoint)).hom.app U
      ((), trueSection.hom.app U (unitPoint.hom.app U ())) = trueTerm.val.hom.app U () :=
  SquareKit.SheafSections.evaluation_name_apply _ trueTerm _ _ _

theorem trueSection_value (U : Diamondᵒᵖ) :
    reversedDisplay.hom.app U ((SquareKit.Family.comparison reversedDisplay truePoint).hom.app U
      ((SquareKit.SheafSections.evaluation (SquareKit.Family.reindex reversedDisplay truePoint)).hom.app U
        ((), trueSection.hom.app U (unitPoint.hom.app U ())))) = true := by
  rw [trueSection_evaluation]
  have h := congrArg (fun k : SheafImage.terminal ⟶ D => k.hom.app U ())
    ((congrArg (fun k => k ≫ reversedDisplay) trueTerm_value).trans trueLift_display)
  exact h

/-- Local existential truth does not supply a global internal section. -/
theorem local_truth_without_global :
    SquareKit.SheafImage.localImage ⊤ toTerminal = ⊤ ∧
    ¬ Nonempty (SquareKit.SheafSections.unit ⟶ SquareKit.SheafSections.sections toTerminal) := by
  refine ⟨locally_inhabited_without_term.1, ?_⟩
  rintro ⟨s⟩
  exact locally_inhabited_without_term.2 ⟨SquareKit.SheafSections.globalEquiv toTerminal s⟩
end Examples.SheafSections
