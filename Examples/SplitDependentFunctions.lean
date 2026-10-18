import SquareKit.SplitPiPresentations
import Examples.FalsePointBaseChange
import Examples.DependentProducts

/-! Experimental split dependent functions on the diamond site. These cases
retain the ordinary finite calculation and the non-pointwise E example. -/
noncomputable section
namespace Examples.SplitDependentFunctions
open CategoryTheory Limits Opposite SquareKit
open Examples.SheafImage Examples.SheafImage.Diamond Examples.SheafBaseChange Examples.SheafFamilies
open SplitSheaf

abbrev argument : Ty D := ofDisplay falsePoint
abbrev result : Ty (Ext argument) := SplitSheafPi.resultPresentation falsePoint base
abbrev functions := SplitSheafPi.pi argument result
abbrev comparison := SplitSheafPi.ordinaryPresentation falsePoint base

/-- The original representing calculation computes the new split fibers. -/
def falseFiber (M : Diamond) : functions.family.obj (D.obj.elementsMk (op M) false) ≃ Bool :=
  (SplitSheafPi.familyEquiv functions FalsePointProduct.actual comparison _).trans
    (FalsePointProduct.falseFiberEquiv M)
def trueFiber (M : Diamond) : functions.family.obj (D.obj.elementsMk (op M) true) ≃ Unit :=
  (SplitSheafPi.familyEquiv functions FalsePointProduct.actual comparison _).trans
    (FalsePointProduct.trueFiberEquiv M)

theorem empty_index_unique (M : Diamond)
    (f g : functions.family.obj (D.obj.elementsMk (op M) true)) : f = g :=
  (trueFiber M).injective (Subsingleton.elim _ _)

def boolPoint (b : Bool) : SheafImage.terminal ⟶ D := ⟨{ app _ := ↾fun _ => b }⟩
abbrev resultDisplay := Family.reindex base (SplitSheaf.displayIso falsePoint).hom

def bodyMap (b : Bool) : Ext argument ⟶ pullback base (SplitSheaf.displayIso falsePoint).hom :=
  Family.pair base (SplitSheaf.displayIso falsePoint).hom
    ((SplitSheaf.displayIso falsePoint).hom ≫ boolPoint b) (𝟙 _) rfl

def body (b : Bool) : Tm result := (displayTerms resultDisplay).symm
  ⟨bodyMap b, Family.pair_reindex _ _ _ _ _⟩

theorem body_value (b : Bool) :
    pair result (𝟙 _) (body b) ≫ (SplitSheaf.displayIso resultDisplay).hom ≫
      pullback.fst base (SplitSheaf.displayIso falsePoint).hom =
      (SplitSheaf.displayIso falsePoint).hom ≫ boolPoint b := by
  have h := congrArg Subtype.val ((displayTerms resultDisplay).apply_symm_apply
    ⟨bodyMap b, Family.pair_reindex _ _ _ _ _⟩)
  change pair result (𝟙 _) (body b) ≫ (SplitSheaf.displayIso resultDisplay).hom = bodyMap b at h
  rw [← Category.assoc, h]
  exact Family.pair_comparison _ _ _ _ _

/-- Lambda evaluates to the chosen Boolean at every inhabited false fiber. -/
theorem lambda_false (M : Diamond) (b : Bool) (a : argument.family.obj (D.obj.elementsMk (op M) false)) :
    (pullback.fst base (SplitSheaf.displayIso falsePoint).hom).hom.app (op M)
      (SplitFunctionDiagram.evaluate argument.family result.family (D.obj.elementsMk (op M) false)
        ((SplitSheafPi.lam argument (body b)).val (D.obj.elementsMk (op M) false)) a).val = b := by
  have hb := congrArg (fun k => k.hom.app (op M) ⟨false,a⟩) (body_value b)
  have he := congrFun (SplitFunctionDiagram.evaluate_lam argument.family (body b)
    (D.obj.elementsMk (op M) false)) a
  rw [he]
  exact hb

/-- There is an actual argument after restricting to the false point. -/
def falseArgument : Tm (tySub argument falsePoint) :=
  readTerm argument (σ := falsePoint) (SplitSheaf.displayIso falsePoint).inv
    (by rw [← SplitSheaf.displayIso_projection, Iso.inv_hom_id_assoc])

/-- Dependent application after restriction uses the actual supplied argument. -/
theorem false_application (b : Bool) :
    SplitSheafPi.app (tySub argument falsePoint)
      (transport (SplitSheafPi.substitution argument result falsePoint)
        (tmSub (SplitSheafPi.lam argument (body b)) falsePoint)) falseArgument =
    tmSub (tmSub (body b) (lift argument falsePoint)) (pair (tySub argument falsePoint) (𝟙 _) falseArgument) := by
  rw [SplitSheafPi.lam_substitution, SplitSheafPi.app_beta]

abbrev reversedArgument := tySub argument SheafFunctions.negation
abbrev reversedResult := tySub result (lift argument SheafFunctions.negation)
abbrev reversedFunctions := SplitSheafPi.pi reversedArgument reversedResult

/-- Negation swaps the computed fibers through equality-level Π substitution. -/
def negationFiber (M : Diamond) (b : Bool) :
    reversedFunctions.family.obj (D.obj.elementsMk (op M) b) ≃
      functions.family.obj (D.obj.elementsMk (op M) (!b)) :=
  Equiv.cast (congrArg (fun T : Ty D => T.family.obj (D.obj.elementsMk (op M) b))
    (SplitSheafPi.substitution argument result SheafFunctions.negation).symm)

def reversedFalse (M : Diamond) : reversedFunctions.family.obj (D.obj.elementsMk (op M) false) ≃ Unit :=
  (negationFiber M false).trans (trueFiber M)
def reversedTrue (M : Diamond) : reversedFunctions.family.obj (D.obj.elementsMk (op M) true) ≃ Bool :=
  (negationFiber M true).trans (falseFiber M)

/-- The negation comparison is the canonical mate, not just some fiber iso. -/
abbrev negation_mate := SplitSheafPi.baseChange_eq argument result SheafFunctions.negation

/-- Two substitutions carry a genuine lambda term through the same transport. -/
theorem double_negation_transport (b : Bool) :
    transport (SplitSheafPi.substitution reversedArgument reversedResult SheafFunctions.negation)
      (tmSub (transport (SplitSheafPi.substitution argument result SheafFunctions.negation)
        (tmSub (SplitSheafPi.lam argument (body b)) SheafFunctions.negation)) SheafFunctions.negation) =
    transport (SplitSheafPi.substitution argument result (SheafFunctions.negation ≫ SheafFunctions.negation))
      (tmSub (SplitSheafPi.lam argument (body b)) (SheafFunctions.negation ≫ SheafFunctions.negation)) :=
  SplitSheafPi.substitution_comp argument result _ _ _

abbrev negation_mate_composition :=
  SplitSheafPi.baseChange_composition argument result SheafFunctions.negation SheafFunctions.negation

end Examples.SplitDependentFunctions
