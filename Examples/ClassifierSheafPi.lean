import SquareKit.Internal.ClassifierSheafPi
import Examples.SplitDependentFunctionEdges

/-! Proper-cover tests of classified Π operations, including inhabited
application, dependent empty outputs, varying inputs and two substitutions. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace Examples.ClassifierSheafPi
open CategoryTheory Limits Opposite SquareKit SplitSheaf
open Examples.SheafImage Examples.SheafImage.Diamond Examples.SheafBaseChange
open Examples.SheafFamilies Examples.SheafFunctions Examples.SplitDependentFunctions
open SquareKit.ClassifierSheafPi

def classifiedLambda (b : Bool) : Section functions (𝟙 D) :=
  lam argument result (𝟙 D) (sections result _ (body b))

theorem recover_lambda (b : Bool) :
    (sections functions (𝟙 D)).symm (classifiedLambda b) =
      SplitSheafPi.lam argument (body b) := by
  simp [classifiedLambda, lam, SplitSheafPi.lamAt]
  rfl

/-- The positive case observes an actual Boolean, so empty fibers cannot prove it. -/
theorem recovered_value (M : Diamond) (b : Bool)
    (a : argument.family.obj (D.obj.elementsMk (op M) false)) :
    (pullback.fst base (displayIso falsePoint).hom).hom.app (op M)
      (SplitFunctionDiagram.evaluate argument.family result.family (D.obj.elementsMk (op M) false)
        (((sections functions (𝟙 D)).symm (classifiedLambda b)).val
          (D.obj.elementsMk (op M) false)) a).val = b := by
  rw [recover_lambda]
  exact lambda_false M b a

theorem lambdas_distinct : classifiedLambda false ≠ classifiedLambda true := by
  intro h
  have h' := congrArg (fun t => (sections functions (𝟙 D)).symm t) h
  have ha : argument.family.obj (D.obj.elementsMk (op X) false) := ⟨(), rfl⟩
  have hv := congrArg (fun t =>
    (pullback.fst base (displayIso falsePoint).hom).hom.app (op X)
      (SplitFunctionDiagram.evaluate argument.family result.family
        (D.obj.elementsMk (op X) false) (t.val (D.obj.elementsMk (op X) false)) ha).val) h'
  rw [recovered_value, recovered_value] at hv
  exact Bool.noConfusion hv

example (b : Bool) : unlam argument result (𝟙 D) (classifiedLambda b) =
    sections result (lift argument (𝟙 D)) (body b) := beta _ _ _ _

/-- Application after a nonidentity restriction retains the dependent result display. -/
example (b : Bool) :
    app argument result falsePoint (sub (classifiedLambda b) falsePoint) falseArgument =
      sections result (pair argument falsePoint falseArgument)
        (tmSub (tmSub (body b) (lift argument falsePoint))
          (pair (tySub argument falsePoint) (𝟙 _) falseArgument)) := by
  change app argument result falsePoint
    (sections functions falsePoint (tmSub ((sections functions (𝟙 D)).symm
      (classifiedLambda b)) falsePoint)) falseArgument = _
  rw [recover_lambda]
  erw [app_sections, false_application]

/-- Application also respects two subsequent nonidentity substitutions. -/
example (b : Bool) :
    app argument result (negation ≫ base ≫ falsePoint)
      (sub
        (sub (sub (classifiedLambda b) falsePoint) base)
        negation) (tmSub (tmSub falseArgument base) negation) =
      sub
        (sub
          (app argument result falsePoint
            (sub (classifiedLambda b) falsePoint) falseArgument) base) negation :=
  app_sub_twice _ _ _ _ _ _ _

example : IsPullback (SplitPresheaf.lift functions.family negation.hom)
    (SplitPresheaf.p (SplitPresheaf.tySub functions.family negation.hom))
    (ClassifierDisplayComparison.projection D.obj (classify functions)) negation.hom :=
  display_pullback argument result negation

example :
    (CoherentFamilyClassification.reindex negation.hom.mapElements).obj
      (classify functions) =
        classify reversedFunctions :=
  pi_reindex argument result negation

theorem negation_not_identity : negation ≠ 𝟙 D := by
  intro h
  have hv := congrArg (fun f : D ⟶ D => f.hom.app (op X) false) h
  exact Bool.noConfusion hv

/-- Both successive substitutions are the nonidentity Boolean negation. -/
example (b : Bool) :
    lam argument result (negation ≫ negation ≫ 𝟙 D)
      (sub (sub (sections result (lift argument (𝟙 D)) (body b))
        (lift (tySub argument (𝟙 D)) negation))
          (lift (tySub argument (negation ≫ 𝟙 D)) negation)) =
      sub (sub (classifiedLambda b) negation) negation :=
  lam_sub_twice _ _ _ _ _ _

/-- The equation includes the actual maps into the classified total display. -/
example (b : Bool) :
    (sub (sub (classifiedLambda b) negation) negation).val =
      (negation ≫ negation).hom ≫ (classifiedLambda b).val := rfl

example (b : Bool) :
    (sub (sub (classifiedLambda b) negation) negation).val ≫
      ClassifierDisplayComparison.projection D.obj (classify functions) =
      (negation ≫ negation).hom := (sub (sub (classifiedLambda b) negation) negation).property

/-- A noninvertible endomorphism collapses all functions to the false lambda. -/
def collapseFamily : functions.family ⟶ functions.family where
  app x := ↾fun _ => (SplitSheafPi.lam argument (body false)).val x
  naturality {x y} f := by
    apply ConcreteCategory.hom_ext
    intro _
    exact ((SplitSheafPi.lam argument (body false)).natural f).symm

abbrev collapse := (CoherentFamilyClassification.code D.obj.Elements (Type)).map collapseFamily

theorem collapse_lambda (b : Bool) : map collapse (classifiedLambda b) = classifiedLambda false := by
  apply Subtype.ext
  rfl

theorem collapse_not_injective : ¬ Function.Injective
    (map (σ := 𝟙 D) collapse) := by
  intro h
  exact lambdas_distinct (h ((collapse_lambda false).trans (collapse_lambda true).symm))

theorem collapse_not_iso : ¬ IsIso collapse := by
  intro h
  let := h
  apply collapse_not_injective
  intro t s hs
  have hi := congrArg (map (inv collapse)) hs
  simp only [map_comp, IsIso.hom_inv_id] at hi
  exact (SquareKit.ClassifierSheafPi.map_id t).symm.trans
    (hi.trans (SquareKit.ClassifierSheafPi.map_id s))

example (b : Bool) : map collapse (sub (sub (classifiedLambda b) negation) negation) =
    sub (sub (classifiedLambda false) negation) negation := by
  rw [SquareKit.ClassifierSheafPi.map_sub, SquareKit.ClassifierSheafPi.map_sub, collapse_lambda]

open Examples.SplitDependentFunctionEdges

/-- The varying-input functions provide actual classified sections as well. -/
def varyingSection (b : Bool) : Section eFunctions (𝟙 SheafImage.terminal) :=
  ⟨(eName b).hom, by ext M x; change (_ : Unit) = _; exact Subsingleton.elim _ _⟩

example (b : Bool) : lam eArgument eResult (𝟙 _)
    (unlam eArgument eResult (𝟙 _) (varyingSection b)) = varyingSection b :=
  eta _ _ _ _

example : varyingSection false ≠ varyingSection true := by
  intro h
  exact e_names_distinct (congrArg (fun t => t.val.app (op X) ()) h)

/-- The result really depends on the Boolean argument; a total function would
have to supply an impossible output at true. Classification cannot hide that. -/
example : ¬ Nonempty (Section dependentFunctions (𝟙 SheafImage.terminal)) := by
  rintro ⟨t⟩
  exact dependent_no_term ⟨(sections _ _).symm t⟩

example : Nonempty (dependentResult.family.obj
    ((Ext boolArgument).obj.elementsMk (op X) ((displayIso base).inv.hom.app (op X) false))) :=
  dependent_false_inhabited

/-- Varying argument fibers retain their incompatible overlap restrictions. -/
example (a : (ClassifierDisplayComparison.extension SheafImage.terminal.obj
    (classify eArgument)).obj (op X)) : False := input_empty a

example (a : (Ext eArgument).obj.obj (op U)) :
    (displayIso eDisplay).hom.hom.app (op W)
      ((Ext eArgument).obj.map (show W ⟶ U from Arrow.wu).op a) = false := input_wu a

example (a : (Ext eArgument).obj.obj (op V)) :
    (displayIso eDisplay).hom.hom.app (op W)
      ((Ext eArgument).obj.map (show W ⟶ V from Arrow.wv).op a) = true := input_wv a

/-- Even at the empty top input fiber, classified functions remember restrictions. -/
example : ¬ Nonempty
    ((ClassifierDisplayComparison.extension SheafImage.terminal.obj (classify eFunctions)).obj (op X) ≃
      (E.obj.obj (op X) → D.obj.obj (op X))) := no_pointwise_equivalence

end Examples.ClassifierSheafPi
