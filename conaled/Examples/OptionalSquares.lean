import SquareKit.CommaOptionalExact
import SquareKit.OptionalMathlib
import Mathlib.CategoryTheory.Monoidal.Closed.Types

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace Examples.OptionalSquares
open SquareKit SquareKit.Comma.Exact

/-- Exact natural values with a captured environment. -/
def natRep : Squares.Rep := ⟨Nat, Nat, id⟩
def add : Squares.Square (Squares.product natRep natRep) natRep where
  impl p := Nat.add p.1 p.2
  spec p := Nat.add p.1 p.2
  commutes _ := rfl

def capturedAdd : Arrow (ofRep natRep) (closed.exp (ofRep natRep) (ofRep natRep)) :=
  closed.curry (x := ofRep natRep) (a := ofRep natRep) (b := ofRep natRep) (ofSquare add)

/-- Evaluation uses the stored implementation, with the specification retained. -/
example : (closed.evaluation (a := ofRep natRep) (b := ofRep natRep)).left
    (capturedAdd.left (3 : Nat), (4 : Nat)) = (7 : Nat) := rfl
example : (capturedAdd.left (3 : Nat)).val.2 (4 : Nat) = (7 : Nat) := rfl

/-- Beta compares both arrows for every environment and argument. -/
theorem captured_beta : closed.uncurry (x := ofRep natRep) (a := ofRep natRep) (b := ofRep natRep)
    capturedAdd = ofSquare add := closedLaws.beta _

/-- Eta still holds when a decoder forgets information. -/
example (f : Squares.Square Squares.forgetBool (Squares.exponential Squares.forgetBool Squares.exactBool)) :
    Squares.curry (Squares.uncurry f) = f := curry_uncurry f

def choose : Arrow (coproducts.sum (ofRep Squares.forgetBool) (ofRep Squares.forgetBool))
    (ofRep Squares.exactBool) :=
  coproducts.copair (ofSquare (Squares.constantBool false)) (ofSquare (Squares.constantBool true))
example : choose.left (.inl true) = false := rfl
example : choose.left (.inr false) = true := rfl
example : categoryOps.comp choose (coproducts.inl (a := ofRep Squares.forgetBool)
    (b := ofRep Squares.forgetBool)) = ofSquare (Squares.constantBool false) := coproductLaws.left _ _

example : (distribution.distribute (a := ofRep natRep) (b := ofRep natRep)
    (c := ofRep natRep)).left ((3 : Nat), Sum.inr (4 : Nat)) = Sum.inr ((3 : Nat), (4 : Nat)) := rfl
example : (distribution.distribute (a := ofRep natRep) (b := ofRep natRep)
    (c := ofRep natRep)).left ((3 : Nat), Sum.inl (4 : Nat)) = Sum.inl ((3 : Nat), (4 : Nat)) := rfl

/-- Distribution is checked against its independently defined canonical inverse. -/
example (a b c : Object) : categoryOps.comp
    (collect categoryOps products coproducts (a := a) (b := b) (c := c)) distribution.distribute =
    categoryOps.ident := distributionLaws.collect_distribute a b c
/-- The Mathlib adapter consumes its actual adjunction, including argument order. -/
example :
    ((OptionalMathlib.closed (Type)).uncurry
      ((OptionalMathlib.closed (Type)).curry (x := Nat) (a := Nat) (b := Nat)
        (TypeCat.ofHom (fun p : Nat × Nat => p.2 + 2 * p.1)))).hom (4, 3) = 11 := by
  have h := (OptionalMathlib.closedLaws (Type)).beta
    (x := Nat) (a := Nat) (b := Nat)
    (TypeCat.ofHom (fun p : Nat × Nat => p.2 + 2 * p.1))
  exact congrArg (fun f : TypeCat.Hom (Nat × Nat) Nat => f.hom (4, 3)) h
end Examples.OptionalSquares
