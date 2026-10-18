import SquareKit.SheafProductBaseChangeConstant
import SquareKit.DependentBaseChangeIdentity
import Examples.TerminalProducts
import Examples.ProjectionProducts

/-! Experimental nonidentity dependent-product base change on the diamond site.
Bool parameters transport actual family maps through the canonical mate. -/
noncomputable section
namespace Examples.DependentBaseChange
open CategoryTheory Limits Opposite
open SquareKit.SheafRelation SquareKit.SheafProductBaseChange
open Examples.SheafImage Examples.SheafImage.Diamond Examples.SheafBaseChange
open Examples.SheafFamilies

abbrev parameters : Over D := Over.mk (𝟙 D)

/-- The old global negation section, pulled back along Bool → 1. -/
def negationBase : parameters ⟶ constantSource D D D :=
  Over.homMk (pullback.lift
    (base ≫ SheafSections.unitPoint ≫ TerminalProducts.negationProduct) (𝟙 D)
    (CartesianMonoidalCategory.isTerminalTensorUnit.hom_ext _ _)) (by simp)

/-- Transport uses the canonical mate, then the explicit constant-input comparison. -/
def negationProduct : parameters ⟶
    (SquareKit.SheafProjectionProduct.pi D D).obj (Over.mk (snd D (product D D))) :=
  negationBase ≫ constantTransport D D D

/-- Explicitly connect the finite transported term to the canonical mate path. -/
abbrev negation_mate := congrArg (fun k => negationBase ≫ k)
  (constantTransport_eq_mate D D D)

theorem negation_old_comparison :
    negationBase.left ≫ oldConstantValue D D D = base ≫ SheafFunctions.negationName := by
  simp only [negationBase, oldConstantValue, Over.homMk_left, Category.assoc,
    pullback.lift_fst_assoc]
  exact congrArg (fun k => base ≫ k) TerminalProducts.negation_exponential

/-- The mate recovers the same pre-existing exponential operation. -/
theorem negation_comparison :
    negationProduct ≫ (SquareKit.SheafProjectionProduct.constantIso D D D).hom =
      (SquareKit.SheafProjectionProduct.constantMaps parameters
        (SquareKit.SheafFunction.exponential D D)).symm
          (base ≫ SheafFunctions.negationName) := by
  unfold negationProduct
  rw [Category.assoc]
  rw [constant_comparison]
  apply (SquareKit.SheafProjectionProduct.constantMaps parameters
    (SquareKit.SheafFunction.exponential D D)).injective
  exact negation_old_comparison

/-- Evaluate the actual projection-product counit on the transported term. -/
def evaluation : product D D ⟶ D :=
  SquareKit.SheafFunction.parameterMap D negationProduct.left ≫
    (SquareKit.SheafProjectionProduct.parameterIso D D
      ((SquareKit.SheafProjectionProduct.pi D D).obj (Over.mk (snd D (product D D))))).inv ≫
        ((SquareKit.SheafProjectionProduct.adjunction D D).counit.app
          (Over.mk (snd D (product D D)))).left ≫ fst D (product D D)

theorem evaluation_negation (a b : Bool) :
    evaluation.hom.app (op X) (a,b) = !a := by
  have h := SquareKit.SheafProjectionProduct.evaluation_comparison (A := D) (Γ := D) (B := D)
  have hn := congrArg (fun k => k.left ≫ fst (SquareKit.SheafFunction.exponential D D) D)
    negation_comparison
  change negationProduct.left ≫
    (SquareKit.SheafProjectionProduct.constantIso D D D).hom.left ≫
      fst (SquareKit.SheafFunction.exponential D D) D = base ≫ SheafFunctions.negationName at hn
  have he : evaluation = SquareKit.SheafFunction.parameterMap D
      (base ≫ SheafFunctions.negationName) ≫ SquareKit.SheafFunction.evaluation D D := by
    unfold evaluation
    rw [← h]
    have hp : SquareKit.SheafFunction.parameterMap D negationProduct.left ≫
        SquareKit.SheafFunction.parameterMap D
          ((SquareKit.SheafProjectionProduct.constantIso D D D).hom.left ≫
            fst (SquareKit.SheafFunction.exponential D D) D) =
      SquareKit.SheafFunction.parameterMap D (base ≫ SheafFunctions.negationName) := by
      rw [← hn]
      rfl
    rw [← Category.assoc, hp]
  rw [he]
  exact SheafFunctions.evaluate_name SheafFunctions.negation (op X) a

example (b : Bool) : evaluation.hom.app (op X) (false,b) = true := evaluation_negation false b
example (b : Bool) : evaluation.hom.app (op X) (true,b) = false := evaluation_negation true b

/-- The genuinely dependent false-point family is pulled back along the argument projection. -/
abbrev falseInput := (Over.pullback (fst D D)).obj (Over.mk falsePoint)

/-- A term of its new dependent product would give an old forbidden global section. -/
theorem dependent_product_no_term :
    ¬ Nonempty (parameters ⟶ (SquareKit.SheafProjectionProduct.pi D D).obj falseInput) := by
  rintro ⟨t⟩
  apply TerminalProducts.false_product_no_global
  refine ⟨(SheafImage.terminalIsTerminal.from SquareKit.SheafSections.unit) ≫ truePoint ≫
    t.left ≫ ((iso D D).inv.app (Over.mk falsePoint)).left ≫
      pullback.fst ((SquareKit.SheafTerminalProduct.pi D).obj (Over.mk falsePoint)).hom
        (SquareKit.SheafTerminalProduct.terminalMap D)⟩

end Examples.DependentBaseChange
