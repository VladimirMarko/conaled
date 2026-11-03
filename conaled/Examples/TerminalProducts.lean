import SquareKit.SheafTerminalProduct
import SquareKit.TypeTerminalProduct
import Examples.SheafSections
import Examples.TypeSums

/-! Experimental consumers of the actual terminal-map pullback adjunction,
with a sheaf example and a separate native dependent Type example. -/
noncomputable section
namespace Examples.TerminalProducts
open CategoryTheory Opposite SquareKit.SheafRelation
open Examples.SheafImage Examples.SheafImage.Diamond Examples.SheafBaseChange
open Examples.SheafFamilies

abbrev boolDisplay := snd D D
abbrev boolProduct := SquareKit.SheafTerminalProduct.object boolDisplay

def negationParam := (SquareKit.SheafSections.termEquiv boolDisplay).symm
  SheafSections.negationTerm

/-- Name negation by the new actual pullback adjunction. -/
def negationProduct : SquareKit.SheafSections.unit ⟶ boolProduct :=
  ((SquareKit.SheafTerminalProduct.adjunction D).homEquiv
    ((toOverUnit _).obj SquareKit.SheafSections.unit) (Over.mk boolDisplay)
    (SquareKit.SheafTerminalProduct.parameterMap boolDisplay negationParam)).left

theorem negation_section : negationProduct = SheafSections.negationSection :=
  SquareKit.SheafTerminalProduct.curry_comparison boolDisplay negationParam

def boolComparison : boolProduct ≅ SquareKit.SheafFunction.exponential D D :=
  SquareKit.SheafTerminalProduct.sectionsIso boolDisplay ≪≫ SquareKit.SheafSections.constantIso D D

theorem negation_exponential :
    SheafSections.unitPoint ≫ negationProduct ≫ boolComparison.hom = SheafFunctions.negationName := by
  rw [negation_section]
  exact SheafSections.negation_comparison

/-- The counit evaluates after both checked product/pullback comparisons. -/
def evaluation : product D boolProduct ⟶ product D D :=
  (SquareKit.SheafSections.parameterComparison D boolProduct).hom ≫
    ((SquareKit.TerminalProduct.pullbackComparison D).inv.app
      ((SquareKit.SheafTerminalProduct.pi D).obj (Over.mk boolDisplay))).left ≫
    ((SquareKit.SheafTerminalProduct.adjunction D).counit.app (Over.mk boolDisplay)).left

theorem evaluation_negation (b : Bool) :
    evaluation.hom.app (op X)
      (b, negationProduct.hom.app (op X) (SheafSections.unitPoint.hom.app (op X) ())) = (!b,b) := by
  have h := SquareKit.SheafTerminalProduct.counit_comparison boolDisplay
  change evaluation = SquareKit.SheafSections.evaluation boolDisplay at h
  rw [h, negation_section]
  exact SquareKit.SheafSections.evaluation_name_apply _ SheafSections.negationTerm _ _ _

theorem false_product_no_global :
    ¬ Nonempty (SquareKit.SheafSections.unit ⟶ SquareKit.SheafTerminalProduct.object falsePoint) := by
  rintro ⟨f⟩
  exact no_total_term ⟨SquareKit.SheafSections.globalEquiv falsePoint
    (f ≫ (SquareKit.SheafTerminalProduct.sectionsIso falsePoint).hom)⟩

namespace Native
open SquareKit.TypeTerminalProduct

def values (n : Nat) := Fin (n+1)
def body : DependentSquares.Tm (valueFamily values) := fun z => ⟨z.2, Nat.lt_succ_self _⟩
def last : object values := lambda values (fun n => body ⟨PUnit.unit,n⟩)

theorem last_native : piTyEquiv values last = DependentSquares.lam body PUnit.unit :=
  lambda_lam values body

theorem last_component (n : Nat) : (evaluate values last n).val = n := by
  rw [show last = lambda values (fun n => body ⟨PUnit.unit,n⟩) from rfl, beta]
  rfl

/-- This component is also the value of the actual pullback counit. -/
theorem last_counit (n : Nat) :
    ((SquareKit.TerminalProduct.adjunction Nat).counit.app (family values)).left
      (((SquareKit.TerminalProduct.pullbackComparison Nat).inv.app
        ((SquareKit.TerminalProduct.pi Nat).obj (family values))).left (last,n)) =
      (⟨n, ⟨n, Nat.lt_succ_self _⟩⟩ : Sigma values) := by
  rw [evaluate_counit]
  congr 1
  exact Fin.ext (last_component n)

theorem last_eta : lambda values (evaluate values last) = last := eta values last
end Native
end Examples.TerminalProducts
