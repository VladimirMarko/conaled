import SquareKit.SheafProjectionConstant
import Examples.TerminalProducts

/-! Experimental projection products over the nonterminal Bool sheaf. A
constant-family operation and a varying empty fiber both use the new adjunction. -/
noncomputable section
namespace Examples.ProjectionProducts
open CategoryTheory Limits Opposite SquareKit.SheafRelation
open Examples.SheafImage Examples.SheafImage.Diamond Examples.SheafBaseChange
open Examples.SheafFunctions Examples.SheafFamilies

abbrev P := product D D
abbrev projection := snd D D
abbrev constantFamily := Over.mk (snd D P)
abbrev parameters : Over D := Over.mk (𝟙 D)
abbrev result := (SquareKit.SheafProjectionProduct.pi D D).obj constantFamily

/-- A body over the actual pullback of the parameter family. -/
def negationBody : (Over.pullback projection).obj parameters ⟶ constantFamily :=
  Over.homMk (lift
    ((SquareKit.SheafProjectionProduct.parameterIso D D parameters).hom ≫ fst D D ≫ negation)
    (SquareKit.Family.reindex (𝟙 D) projection)) rfl

/-- Curry with the constructed projection adjunction, over the Bool base. -/
def negationProduct : parameters ⟶ result :=
  (SquareKit.SheafProjectionProduct.adjunction D D).homEquiv parameters constantFamily negationBody

theorem negation_comparison :
    negationProduct.left ≫ (SquareKit.SheafProjectionProduct.constantIso D D D).hom.left ≫
      fst (SquareKit.SheafFunction.exponential D D) D =
        SquareKit.SheafFunction.curry (fst D D ≫ negation) := by
  have h := SquareKit.SheafProjectionProduct.curry_comparison parameters negationBody
  have hv := congrArg (fun k => k.left ≫ fst (SquareKit.SheafFunction.exponential D D) D) h
  change _ = SquareKit.SheafFunction.curry
    ((SquareKit.SheafProjectionProduct.parameterIso D D parameters).inv ≫
      ((SquareKit.SheafProjectionProduct.parameterIso D D parameters).hom ≫ fst D D ≫ negation)) at hv
  simpa only [negationProduct, Iso.inv_hom_id_assoc, Over.comp_left, Category.assoc] using hv

/-- Actual counit evaluation, after the explicit pullback comparison. -/
def evaluate : product D result.left ⟶ D :=
  (SquareKit.SheafProjectionProduct.parameterIso D D result).inv ≫
    ((SquareKit.SheafProjectionProduct.adjunction D D).counit.app constantFamily).left ≫ fst D P

theorem evaluate_negation (a b : Bool) :
    evaluate.hom.app (op X) (a, negationProduct.left.hom.app (op X) b) = !a := by
  have he := SquareKit.SheafProjectionProduct.evaluation_comparison (A := D) (Γ := D) (B := D)
  have hv := congrArg (fun k : product D result.left ⟶ D =>
    k.hom.app (op X) (a,negationProduct.left.hom.app (op X) b)) he
  have hn := congrArg (fun k : D ⟶ SquareKit.SheafFunction.exponential D D => k.hom.app (op X) b)
    negation_comparison
  change (SquareKit.SheafFunction.evaluation D D).hom.app (op X)
    (a, ((SquareKit.SheafProjectionProduct.constantIso D D D).hom.left ≫
      fst (SquareKit.SheafFunction.exponential D D) D).hom.app (op X)
        (negationProduct.left.hom.app (op X) b)) = _ at hv
  exact hv.symm.trans ((congrArg
    (fun z => (SquareKit.SheafFunction.evaluation D D).hom.app (op X) (a,z)) hn).trans
      (parameter_negation_value a b))

/-- This family selects argument false but permits every Bool base value. -/
def falseArgument : product SheafImage.terminal D ⟶ P :=
  lift (fst SheafImage.terminal D ≫ falsePoint) (snd SheafImage.terminal D)

theorem falseArgument_value (U : Diamondᵒᵖ) (b : Bool) :
    falseArgument.hom.app U ((),b) = (false,b) := rfl

theorem falseArgument_no_term : ¬ Nonempty (SquareKit.Family.Term falseArgument) := by
  rintro ⟨t⟩
  have h := congrArg (fun k : P ⟶ P => (k.hom.app (op X) (true,false)).1) t.property
  exact Bool.noConfusion h

/-- A product term would uncurry to a forbidden section of the input family. -/
theorem dependent_product_no_term :
    ¬ Nonempty (SquareKit.Family.Term
      (((SquareKit.SheafProjectionProduct.pi D D).obj (Over.mk falseArgument)).hom)) := by
  rintro ⟨t⟩
  let k : parameters ⟶ (SquareKit.SheafProjectionProduct.pi D D).obj (Over.mk falseArgument) :=
    Over.homMk t.val t.property
  let body := ((SquareKit.SheafProjectionProduct.adjunction D D).homEquiv parameters
    (Over.mk falseArgument)).symm k
  let diagonal : P ⟶ pullback (𝟙 D) projection :=
    pullback.lift projection (𝟙 P) (by simp)
  apply falseArgument_no_term
  refine ⟨⟨diagonal ≫ body.left, ?_⟩⟩
  have hw : body.left ≫ falseArgument = SquareKit.Family.reindex (𝟙 D) projection := Over.w body
  rw [Category.assoc, hw]
  exact pullback.lift_snd _ _ _

end Examples.ProjectionProducts
