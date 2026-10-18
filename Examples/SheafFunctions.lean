import SquareKit.SheafFunction
import Examples.SheafContexts

/-! Experimental function sheaves on the diamond site: negation and non-pointwise sections. -/
noncomputable section
namespace Examples.SheafFunctions
open CategoryTheory Opposite
open SquareKit.SheafRelation SquareKit.SheafFunction
open Examples.SheafImage Examples.SheafImage.Diamond Examples.SheafBaseChange

/-- Reuse the existing natural operation, now as an ordinary sheaf morphism. -/
def negation : D ⟶ D := ⟨SheafContexts.model.arrow SheafContexts.Op.neg⟩

abbrev boolFunctions := exponential D D
abbrev partialFunctions := exponential E D

/-- A global element obtained by transposition, with argument before Unit. -/
def name {A B : Sheaf topology Type} (f : A ⟶ B) : terminal ⟶ exponential A B :=
  curry (fst A terminal ≫ f)

theorem evaluate_name {A B : Sheaf topology Type} (f : A ⟶ B)
    (U : Diamondᵒᵖ) (a : A.obj.obj U) :
    (evaluation A B).hom.app U (a, (name f).hom.app U ()) = f.hom.app U a :=
  evaluation_curry_apply (fst A terminal ≫ f) U a ()

def negationName : terminal ⟶ boolFunctions := name negation

/-- Expected Boolean values, including the stage with no E section. -/
theorem negation_false :
    (evaluation D D).hom.app (op X) (false, negationName.hom.app (op X) ()) = true :=
  evaluate_name negation (op X) false

theorem negation_true :
    (evaluation D D).hom.app (op X) (true, negationName.hom.app (op X) ()) = false :=
  evaluate_name negation (op X) true

/-- Eta recovers the global operation after its evaluation is transposed. -/
theorem negation_eta :
    curry (parameterMap D negationName ≫ evaluation D D) = negationName := by
  rw [← uncurry_evaluation, eta]

/-- Any Bool parameter selects the same negation operation. -/
theorem negation_parameters :
    curry (fst D D ≫ negation) = base ≫ negationName := by
  have h := curry_parameter (fst D terminal ≫ negation) base
  have hp : parameterMap D base ≫ (fst D terminal ≫ negation) = fst D D ≫ negation := rfl
  rw [hp] at h
  exact h

theorem parameter_negation_value (a b : Bool) :
    (evaluation D D).hom.app (op X)
      (a, (curry (fst D D ≫ negation)).hom.app (op X) b) = !a := by
  rw [negation_parameters]
  exact evaluate_name negation (op X) a

/-- Two distinct operations despite E having no section at X. -/
def constant (b : Bool) : E ⟶ D := ⟨{ app _ := ↾fun _ => b }⟩

def constantName (b : Bool) : terminal ⟶ partialFunctions := name (constant b)

theorem constants_distinct_at_X :
    (constantName false).hom.app (op X) () ≠ (constantName true).hom.app (op X) () := by
  intro h
  have hr := congrArg (partialFunctions.obj.map (Quiver.Hom.op Arrow.wx)) h
  have hn (b : Bool) :
      partialFunctions.obj.map (Quiver.Hom.op Arrow.wx) ((constantName b).hom.app (op X) ()) =
        (constantName b).hom.app (op W) () :=
    (NatTrans.naturality_apply (constantName b).hom (Quiver.Hom.op Arrow.wx) ()).symm
  rw [hn false, hn true] at hr
  have he := congrArg (fun z => (evaluation E D).hom.app (op W) (false, z)) hr
  change (evaluation E D).hom.app (op W) (false, (name (constant false)).hom.app (op W) ()) =
    (evaluation E D).hom.app (op W) (false, (name (constant true)).hom.app (op W) ()) at he
  have impossible : false = true :=
    (evaluate_name (constant false) (op W) false).symm.trans
      (he.trans (evaluate_name (constant true) (op W) false))
  exact Bool.noConfusion impossible

/-- The external function type at X has exactly one function. -/
abbrev unique_pointwise : Unique (E.obj.obj (op X) → D.obj.obj (op X)) where
  default x := nomatch x
  uniq f := by funext x; exact nomatch x

/-- Thus no identification with pointwise functions can be an equivalence. -/
theorem no_pointwise_equivalence :
    ¬ Nonempty (partialFunctions.obj.obj (op X) ≃ (E.obj.obj (op X) → D.obj.obj (op X))) := by
  rintro ⟨e⟩
  apply constants_distinct_at_X
  apply e.injective
  exact (unique_pointwise.uniq _).trans (unique_pointwise.uniq _).symm
end Examples.SheafFunctions
