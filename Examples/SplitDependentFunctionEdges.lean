import Examples.SplitDependentFunctions

/-! Experimental dependent outputs and incompatible input restrictions for split Π. -/
noncomputable section
namespace Examples.SplitDependentFunctionEdges
open CategoryTheory Limits Opposite SquareKit
open Examples.SheafImage Examples.SheafImage.Diamond Examples.SheafBaseChange Examples.SheafFamilies
open SplitSheaf

abbrev boolArgument := ofDisplay base
abbrev dependentResult := SplitSheafPi.resultPresentation base falsePoint
abbrev dependentFunctions := SplitSheafPi.pi boolArgument dependentResult
abbrev dependentDisplay := Family.reindex falsePoint (SplitSheaf.displayIso base).hom

/-- The result depends on the argument: its false fiber is inhabited. -/
theorem dependent_false_inhabited : Nonempty (dependentResult.family.obj
    ((Ext boolArgument).obj.elementsMk (op X) ((SplitSheaf.displayIso base).inv.hom.app (op X) false))) := by
  let a := (SplitSheaf.displayIso base).inv.hom.app (op X) false
  have ha : (SplitSheaf.displayIso base).hom.hom.app (op X) a = false :=
    congrArg (fun k => k.hom.app (op X) false) (SplitSheaf.displayIso base).inv_hom_id
  let z := (SheafFamily.sectionsEquiv falsePoint (SplitSheaf.displayIso base).hom (op X)).symm
    ⟨((),a), ha.symm⟩
  refine ⟨⟨z, ?_⟩⟩
  exact (SheafFamily.sectionsEquiv_snd falsePoint (SplitSheaf.displayIso base).hom (op X) z).symm.trans
    (congrArg (fun p => p.val.2)
      ((SheafFamily.sectionsEquiv falsePoint (SplitSheaf.displayIso base).hom (op X)).apply_symm_apply _))

/-- A dependent function cannot invent an output over the true argument. -/
theorem dependent_no_term : ¬ Nonempty (Tm dependentFunctions) := by
  rintro ⟨t⟩
  let s := displayTerms dependentDisplay (SplitSheafPi.unlam boolArgument t)
  have h : s.val ≫ pullback.fst falsePoint (SplitSheaf.displayIso base).hom ≫ falsePoint =
      (SplitSheaf.displayIso base).hom := by
    rw [pullback.condition, ← Category.assoc, s.property, Category.id_comp]
  have hv := congrArg (fun k => k.hom.app (op X) ((SplitSheaf.displayIso base).inv.hom.app (op X) true)) h
  have hi := congrArg (fun k => k.hom.app (op X) true) (SplitSheaf.displayIso base).inv_hom_id
  exact Bool.noConfusion (hv.trans hi)

abbrev eDisplay := SheafTerminalProduct.terminalMap E
abbrev eArgument := ofDisplay eDisplay
abbrev eResult := SplitSheafPi.resultPresentation eDisplay (SheafRelation.snd D E)
abbrev eFunctions := SplitSheafPi.pi eArgument eResult

def eComparison : Ext eFunctions ≅ DependentProducts.nonconstantResult.left :=
  (Over.forget _).mapIso (SplitSheafPi.ordinaryPresentation eDisplay (SheafRelation.snd D E))

def eName (b : Bool) : SheafImage.terminal ⟶ Ext eFunctions :=
  DependentProducts.nonconstantName b ≫ eComparison.inv

/-- Existing distinct natural functions remain distinct in the split model. -/
theorem e_names_distinct :
    (eName false).hom.app (op X) () ≠ (eName true).hom.app (op X) () := by
  intro h
  apply DependentProducts.nonconstant_names_distinct
  have hh := congrArg (fun z => eComparison.hom.hom.app (op X) z) h
  have he (b : Bool) : eName b ≫ eComparison.hom = DependentProducts.nonconstantName b := by
    simp [eName]
  exact (congrArg (fun k => k.hom.app (op X) ()) (he false)).symm.trans
    (hh.trans (congrArg (fun k => k.hom.app (op X) ()) (he true)))

theorem no_pointwise_equivalence :
    ¬ Nonempty ((Ext eFunctions).obj.obj (op X) ≃ (E.obj.obj (op X) → D.obj.obj (op X))) := by
  rintro ⟨e⟩
  apply e_names_distinct
  apply e.injective
  exact (SheafFunctions.unique_pointwise.uniq _).trans (SheafFunctions.unique_pointwise.uniq _).symm

/-- Reconstructed inputs retain E's empty and incompatible fibers. -/
theorem input_empty (a : (Ext eArgument).obj.obj (op X)) : False :=
  nomatch (SplitSheaf.displayIso eDisplay).hom.hom.app (op X) a

theorem input_wu (a : (Ext eArgument).obj.obj (op U)) :
    (SplitSheaf.displayIso eDisplay).hom.hom.app (op W)
      ((Ext eArgument).obj.map (show W ⟶ U from Arrow.wu).op a) = false := by
  rw [NatTrans.naturality_apply]
  rfl

theorem input_wv (a : (Ext eArgument).obj.obj (op V)) :
    (SplitSheaf.displayIso eDisplay).hom.hom.app (op W)
      ((Ext eArgument).obj.map (show W ⟶ V from Arrow.wv).op a) = true := by
  rw [NatTrans.naturality_apply]
  rfl

/-- The new nonconstant case also consumes the actual counit comparison. -/
abbrev e_evaluation := SplitSheafPi.displayIso_evaluation eArgument eResult

end Examples.SplitDependentFunctionEdges
