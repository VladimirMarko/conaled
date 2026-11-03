import SquareKit.CommaExact
import SquareKit.CommaProducts

namespace SquareKit.Comma.Exact
universe u
open FunctionCategory
abbrev products : ProductOps categoryOps.{u} := Comma.productOps
  (equalityCongr FunctionCategory.ops) FunctionCategory.laws (RawMap.id_laws _) (RawMap.id_laws _)
  (ProductMap.id FunctionCategory.products) (ProductMap.id FunctionCategory.products)
  (fun _a _b => Comparison.id_laws FunctionCategory.laws _) (fun _a _b => Comparison.id_laws FunctionCategory.laws _)
  (ProductMap.id_laws FunctionCategory.laws _) (ProductMap.id_laws FunctionCategory.laws _)
  FunctionCategory.productCongr FunctionCategory.productLaws
abbrev terminal : TerminalOps categoryOps.{u} := Comma.terminalOps
  (equalityCongr FunctionCategory.ops) FunctionCategory.laws (RawMap.id_laws _) (RawMap.id_laws _)
  (TerminalMap.id FunctionCategory.terminal) (TerminalMap.id FunctionCategory.terminal)
  (Comparison.id_laws FunctionCategory.laws _) (TerminalMap.id_laws FunctionCategory.laws _) (TerminalMap.id_laws FunctionCategory.laws _)
  FunctionCategory.terminalLaws
@[simp] theorem ofRep_product (a b : Squares.Rep.{u}) :
    ofRep (Squares.product a b) = products.prod (ofRep a) (ofRep b) := rfl
@[simp] theorem ofRep_terminal : ofRep (Squares.terminal : Squares.Rep.{u}) = terminal.unit := rfl
@[simp] theorem ofSquare_first (a b : Squares.Rep.{u}) :
    ofSquare (Squares.first a b) = products.fst (a := ofRep a) (b := ofRep b) := rfl
@[simp] theorem ofSquare_second (a b : Squares.Rep.{u}) :
    ofSquare (Squares.second a b) = products.snd (a := ofRep a) (b := ofRep b) := rfl
@[simp] theorem ofSquare_pair {a b c : Squares.Rep.{u}} (f : Squares.Square a b) (g : Squares.Square a c) :
    ofSquare (Squares.pair f g) = products.pair (ofSquare f) (ofSquare g) := rfl
@[simp] theorem ofSquare_terminate (a : Squares.Rep.{u}) :
    ofSquare (Squares.terminate a) = terminal.terminal (a := ofRep a) := rfl

theorem products_laws : ProductLaws (Comma.equiv (equalityCongr FunctionCategory.ops) FunctionCategory.laws
    (RawMap.id_laws (equality FunctionCategory.ops)) (RawMap.id_laws (equality FunctionCategory.ops))) products.{u} :=
  Comma.productLaws _ _ _ _ _ _ _ _ _ _ _ _ FunctionCategory.productLaws FunctionCategory.productLaws

theorem terminal_laws : TerminalLaws (Comma.equiv (equalityCongr FunctionCategory.ops) FunctionCategory.laws
    (RawMap.id_laws (equality FunctionCategory.ops)) (RawMap.id_laws (equality FunctionCategory.ops))) terminal.{u} :=
  Comma.terminalLaws _ _ _ _ _ _ _ _ _ _ FunctionCategory.terminalLaws FunctionCategory.terminalLaws
/-- The existing square beta law follows from the shared comma law. -/
theorem first_pair {a b c : Squares.Rep.{u}} (f : Squares.Square a b) (g : Squares.Square a c) :
    Squares.compose (Squares.first b c) (Squares.pair f g) = f := by
  have h := (equiv_iff _ _).mp (products_laws.fst_pair (ofSquare f) (ofSquare g))
  exact congrArg toSquare h

theorem second_pair {a b c : Squares.Rep.{u}} (f : Squares.Square a b) (g : Squares.Square a c) :
    Squares.compose (Squares.second b c) (Squares.pair f g) = g := by
  have h := (equiv_iff _ _).mp (products_laws.snd_pair (ofSquare f) (ofSquare g))
  exact congrArg toSquare h

theorem pair_eta {a b c : Squares.Rep.{u}} (f : Squares.Square a (Squares.product b c)) :
    Squares.pair (Squares.compose (Squares.first b c) f) (Squares.compose (Squares.second b c) f) = f := by
  have h := (equiv_iff _ _).mp (products_laws.pair_eta (a := ofRep a) (b := ofRep b) (c := ofRep c) (ofSquare f))
  exact congrArg toSquare h

theorem terminal_unique {a : Squares.Rep.{u}} (f : Squares.Square a Squares.terminal) :
    f = Squares.terminate a := by
  have h := (equiv_iff _ _).mp (terminal_laws.unique (ofSquare f))
  exact congrArg toSquare h
end SquareKit.Comma.Exact
