import SquareKit.ObjectReindex
import SquareKit.FunctionInitial
import SquareKit.FunctionOptionalLaws
import SquareKit.SelectedFeedbackTransport

namespace Examples.ObjectReindex
open SquareKit
universe u
abbrev Tagged := Type u × Bool
def carrier (a : Tagged.{u}) : Type u := a.1
def productObject (a b : Tagged.{u}) : Tagged.{u} := (b.1 × a.1,false)
def productComparison (a b : Tagged.{u}) :
    Comparison FunctionCategory.ops (carrier (productObject a b))
      (FunctionCategory.products.prod (carrier a) (carrier b)) := ⟨Prod.swap,Prod.swap⟩
def products := SquareKit.ObjectReindex.products carrier FunctionCategory.products productObject productComparison

theorem productComparison_inverse (a b : Tagged.{u}) :
    ComparisonLaws (equality _) (productComparison a b) := ⟨rfl,rfl⟩
theorem product_laws : ProductLaws (SquareKit.ObjectReindex.equiv carrier (equality _)) products.{u} :=
  SquareKit.ObjectReindex.product_laws carrier (equalityCongr _) FunctionCategory.laws
    FunctionCategory.products productObject productComparison productComparison_inverse
    FunctionCategory.productCongr FunctionCategory.productLaws

def sumObject (a b : Tagged.{u}) : Tagged.{u} := (Sum b.1 a.1,false)
def sumComparison (a b : Tagged.{u}) :
    Comparison FunctionCategory.ops (carrier (sumObject a b))
      (FunctionCategory.coproducts.sum (carrier a) (carrier b)) := ⟨Sum.swap,Sum.swap⟩
def coproducts := SquareKit.ObjectReindex.coproducts carrier FunctionCategory.coproducts sumObject sumComparison

theorem sumComparison_inverse (a b : Tagged.{u}) :
    ComparisonLaws (equality _) (sumComparison a b) := by
  constructor <;> funext x <;> cases x <;> rfl
theorem coproduct_laws : CoproductLaws _ (SquareKit.ObjectReindex.equiv carrier (equality _)) coproducts.{u} :=
  SquareKit.ObjectReindex.coproduct_laws carrier (equalityCongr _) FunctionCategory.laws
    FunctionCategory.coproducts sumObject sumComparison sumComparison_inverse
    FunctionCategory.coproductCongr FunctionCategory.coproductLaws

theorem carrier_not_injective : ¬ Function.Injective carrier.{0} := by
  intro h
  have bad := congrArg Prod.snd (h (a₁ := (Nat,false)) (a₂ := (Nat,true)) rfl)
  cases bad

theorem swapped_pair : products.pair (a := (Nat,true)) (b := (Bool,false)) (c := (Nat,true))
    (fun _ => true) (fun n : Nat => n+1) (4 : Nat) = (5,true) := rfl
theorem swapped_injection : coproducts.inl (a := (Nat,true)) (b := (Bool,false)) (4 : Nat) = Sum.inr 4 := rfl

theorem projection_recovers (f : Nat → Bool) (g : Nat → Nat) :
    (SquareKit.ObjectReindex.ops FunctionCategory.ops carrier).comp
      (products.fst (a := (Bool,false)) (b := (Nat,true)))
      (products.pair (a := (Nat,true)) f g) = f := product_laws.fst_pair (a := (Nat,true)) (b := (Bool,false)) (c := (Nat,true)) f g

/-- A raw comparison need not be invertible, and its raw product need not obey product laws. -/
def badComparison (_ _ : Unit) : Comparison FunctionCategory.ops Bool (Bool × Bool) :=
  ⟨fun b => (b,b),Prod.fst⟩
def badProducts := SquareKit.ObjectReindex.products (fun _ : Unit => Bool)
  FunctionCategory.products (fun _ _ => ()) badComparison

theorem bad_product_law_rejected : ¬ ProductLaws
    (SquareKit.ObjectReindex.equiv (fun _ : Unit => Bool) (equality FunctionCategory.ops)) badProducts := by
  intro L
  have h := congrFun (L.snd_pair (a := ()) (b := ()) (c := ()) (fun _ => false) (fun _ => true)) false
  cases h

def taggedTerminal := SquareKit.ObjectReindex.terminal carrier FunctionCategory.terminal
  (PUnit,false) ⟨id,id⟩
theorem taggedTerminal_laws : TerminalLaws (SquareKit.ObjectReindex.equiv carrier (equality _)) taggedTerminal.{u} :=
  SquareKit.ObjectReindex.terminal_laws carrier (equalityCongr _) FunctionCategory.laws
    FunctionCategory.terminal (PUnit,false) ⟨id,id⟩ ⟨rfl,rfl⟩ FunctionCategory.terminalLaws

def taggedInitial := SquareKit.ObjectReindex.initial carrier FunctionCategory.initial
  (PEmpty,false) ⟨id,id⟩
theorem taggedInitial_laws : InitialLaws (SquareKit.ObjectReindex.equiv carrier (equality _)) taggedInitial.{u} :=
  SquareKit.ObjectReindex.initial_laws carrier (equalityCongr _) FunctionCategory.laws
    FunctionCategory.initial (PEmpty,false) ⟨id,id⟩ ⟨rfl,rfl⟩ FunctionCategory.initialLaws

def badSumComparison (_ _ : Unit) : Comparison FunctionCategory.ops Bool (Sum Bool Bool) :=
  ⟨Sum.inl,Sum.elim id id⟩
def badCoproducts := SquareKit.ObjectReindex.coproducts (fun _ : Unit => Bool)
  FunctionCategory.coproducts (fun _ _ => ()) badSumComparison
theorem bad_coproduct_law_rejected : ¬ CoproductLaws _
    (SquareKit.ObjectReindex.equiv (fun _ : Unit => Bool) (equality FunctionCategory.ops)) badCoproducts := by
  intro L
  have h := congrFun (L.right (a := ()) (b := ()) (c := ()) (fun _ => false) (fun _ => true)) false
  cases h

/-- Extraction of the shared raw core preserves the selected-feedback client's carrier. -/
theorem feedback_reindexed_eq :
    SelectedFeedback.reindexed FunctionCategory.ops carrier.{u} = SquareKit.ObjectReindex.ops FunctionCategory.ops carrier := rfl
end Examples.ObjectReindex
