import Examples.DependentFunctionSource

/-! Experimental external consumers of the same dependent source derivation.
The E-based result family consists of actual natural E-to-Bool functions. The
source Pi still has the stated base-sort domain; this does not extend the source
with arbitrary family domains or identify sheaf Pi with pointwise Pi. -/
noncomputable section
namespace Examples.DependentFunctionSourceEdges
open CategoryTheory Limits Opposite SquareKit
open Internal.DependentFunctions Internal.DependentFunctions.SheafSem
open Internal.DependentStructural (Base)
open Internal.DependentStructural.SheafSem (evalBase)
open Examples.SheafImage Examples.SheafImage.Diamond Examples.SheafBaseChange Examples.SheafFamilies
open DependentFunctionSource

abbrev naturalFunctions := SplitSheaf.Ext SplitDependentFunctionEdges.eFunctions
abbrev naturalDisplay := SheafRelation.snd naturalFunctions D
abbrev naturalFamily := SplitSheaf.ofDisplay naturalDisplay

def naturalSection (b : Bool) : SplitSheaf.Tm naturalFamily :=
  (SplitSheaf.displayTerms naturalDisplay).symm
    ⟨SheafRelation.lift (base ≫ SplitDependentFunctionEdges.eName b) (𝟙 D), rfl⟩

private theorem display_value {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {A B : Sheaf J (Type w)} (d : A ⟶ B) (t : Family.Term d) :
    SplitSheaf.pair (SplitSheaf.ofDisplay d) (𝟙 B) ((SplitSheaf.displayTerms d).symm t) ≫
      (SplitSheaf.displayIso d).hom = t.val :=
  congrArg Subtype.val ((SplitSheaf.displayTerms d).apply_symm_apply t)

theorem naturalSection_value (b : Bool) :
    SplitSheaf.pair naturalFamily (𝟙 D) (naturalSection b) ≫ (SplitSheaf.displayIso naturalDisplay).hom =
      SheafRelation.lift (base ≫ SplitDependentFunctionEdges.eName b) (𝟙 D) :=
  display_value naturalDisplay ⟨SheafRelation.lift (base ≫ SplitDependentFunctionEdges.eName b) (𝟙 D), rfl⟩

def eModel : Model topology where
  B := D
  A := naturalFamily
  zero := DependentSource.unitIso.hom ≫ falsePoint
  neg := SheafFunctions.negation
  point := SplitSheaf.pair naturalFamily (DependentSource.unitIso.hom ≫ falsePoint)
    (SplitSheaf.tmSub (naturalSection false) (DependentSource.unitIso.hom ≫ falsePoint))
  point_type := rfl
abbrev eEnv (b : Bool) := parameterEnv eModel (naturalSection b)

theorem e_source (b : Bool) : HEq (evalDep eModel (eEnv b) left) (evalDep eModel (eEnv b) right) :=
  dep_sound eModel source_equation _

theorem e_ordinary (b : Bool) :
    HEq (ordinaryApplication eModel (eEnv b) (.lam body) (.neg (.var 0)))
      (evalDep eModel (eEnv b) right) :=
  derived_ordinary eModel (eEnv b) negSub negSub_typed body (.var 0)

theorem e_beta_value (U : Diamondᵒᵖ) (b : Bool) :
    (evalDep eModel (eEnv b) left).val (D.obj.elementsMk U false) =
      (naturalSection b).val (D.obj.elementsMk U false) := by
  have h : evalDep eModel (eEnv b) left = evalDep eModel (eEnv b) right := eq_of_heq (e_source b)
  rw [h]
  exact congrArg (fun t => t.val (D.obj.elementsMk U false))
    (parameter_application eModel (naturalSection b) (.neg (.neg (.var 0))))

def sourceName (b : Bool) : SheafImage.terminal ⟶ naturalFunctions :=
  falsePoint ≫ depValue eModel (eEnv b) left ≫ (SplitSheaf.displayIso naturalDisplay).hom ≫
    SheafRelation.fst naturalFunctions D

theorem sourceName_eq (b : Bool) : sourceName b = SplitDependentFunctionEdges.eName b := by
  unfold sourceName
  erw [left_value]
  change falsePoint ≫ (SheafFunctions.negation ≫ SheafFunctions.negation) ≫
    SplitSheaf.pair naturalFamily (𝟙 D) (naturalSection b) ≫
      (SplitSheaf.displayIso naturalDisplay).hom ≫ SheafRelation.fst naturalFunctions D = _
  rw [← Category.assoc falsePoint (SheafFunctions.negation ≫ SheafFunctions.negation)]
  have hn : falsePoint ≫ (SheafFunctions.negation ≫ SheafFunctions.negation) = falsePoint := rfl
  rw [hn, ← Category.assoc (SplitSheaf.pair naturalFamily (𝟙 D) (naturalSection b)), naturalSection_value]
  rfl

/-- The source proof's result is the old ordinary natural-function name through
the operation-preserving dependent-product comparison. -/
theorem source_natural_comparison (b : Bool) :
    sourceName b ≫ SplitDependentFunctionEdges.eComparison.hom ≫ DependentProducts.nonconstantIso.hom =
      SheafFunctions.constantName b := by
  rw [sourceName_eq]
  simp [SplitDependentFunctionEdges.eName, DependentProducts.nonconstantName]

theorem source_natural_evaluation (U : Diamondᵒᵖ) (b : Bool) (a : E.obj.obj U) :
    (SheafFunction.evaluation E D).hom.app U
      (a, (sourceName b ≫ SplitDependentFunctionEdges.eComparison.hom ≫
        DependentProducts.nonconstantIso.hom).hom.app U ()) = b := by
  rw [source_natural_comparison]
  exact SheafFunctions.evaluate_name (SheafFunctions.constant b) U a

theorem source_names_distinct :
    (sourceName false).hom.app (op X) () ≠ (sourceName true).hom.app (op X) () := by
  rw [sourceName_eq, sourceName_eq]
  exact SplitDependentFunctionEdges.e_names_distinct

/-- Both names came from the same source proof, but pointwise functions at X
have only one element because E(X) is empty. -/
theorem no_pointwise_equivalence :
    ¬ Nonempty (naturalFunctions.obj.obj (op X) ≃ (E.obj.obj (op X) → D.obj.obj (op X))) := by
  rintro ⟨e⟩
  apply source_names_distinct
  apply e.injective
  exact (SheafFunctions.unique_pointwise.uniq _).trans (SheafFunctions.unique_pointwise.uniq _).symm

/-- An ordinary client may use the existing counit directly beside the opt-in
source theorem. No syntax wrapper is required by the ordinary interface. -/
abbrev direct_ordinary := SheafDependentProduct.terminal_evaluation E DependentProducts.nonconstantInput
abbrev source_ordinary := e_ordinary false

end Examples.DependentFunctionSourceEdges
