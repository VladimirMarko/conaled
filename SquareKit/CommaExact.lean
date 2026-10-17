import SquareKit.Comma
import SquareKit.FunctionCategory
import Squares

namespace SquareKit.Comma.Exact
universe u

abbrev interpretation : RawMap (FunctionCategory.ops : CategoryOps (Type u)) FunctionCategory.ops := RawMap.id FunctionCategory.ops
abbrev Object := Obj (interpretation.{u}) interpretation
abbrev Arrow (a b : Object.{u}) := Hom (equality FunctionCategory.ops) a b
abbrev categoryOps : CategoryOps Object.{u} := Comma.ops (equalityCongr FunctionCategory.ops)
  FunctionCategory.laws (RawMap.id_laws (equality FunctionCategory.ops)) (RawMap.id_laws (equality FunctionCategory.ops))

def ofRep (a : Squares.Rep.{u}) : Object := ⟨a.R, a.S, a.decode⟩
def toRep (a : Object.{u}) : Squares.Rep := ⟨a.left, a.right, a.connector⟩
@[simp] theorem toRep_ofRep (a : Squares.Rep.{u}) : toRep (ofRep a) = a := rfl
@[simp] theorem ofRep_toRep (a : Object.{u}) : ofRep (toRep a) = a := rfl

def ofSquare {a b : Squares.Rep.{u}} (f : Squares.Square a b) : Arrow (ofRep a) (ofRep b) where
  left := f.impl
  right := f.spec
  commutes := funext f.commutes

def toSquare {a b : Object.{u}} (f : Arrow a b) : Squares.Square (toRep a) (toRep b) where
  impl := f.left
  spec := f.right
  commutes x := congrFun f.commutes x

@[simp] theorem toSquare_ofSquare {a b : Squares.Rep.{u}} (f : Squares.Square a b) :
    toSquare (ofSquare f) = f := rfl
@[simp] theorem ofSquare_toSquare {a b : Object.{u}} (f : Arrow a b) :
    ofSquare (toSquare f) = f := rfl
@[simp] theorem ofSquare_left {a b : Squares.Rep.{u}} (f : Squares.Square a b) :
    (ofSquare f).left = f.impl := rfl
@[simp] theorem ofSquare_right {a b : Squares.Rep.{u}} (f : Squares.Square a b) :
    (ofSquare f).right = f.spec := rfl
@[simp] theorem toSquare_impl {a b : Object.{u}} (f : Arrow a b) :
    (toSquare f).impl = f.left := rfl
@[simp] theorem toSquare_spec {a b : Object.{u}} (f : Arrow a b) :
    (toSquare f).spec = f.right := rfl

@[simp] theorem ofSquare_identity (a : Squares.Rep.{u}) :
    ofSquare (Squares.identity a) = categoryOps.ident (a := ofRep a) := rfl
@[simp] theorem ofSquare_compose {a b c : Squares.Rep.{u}}
    (g : Squares.Square b c) (f : Squares.Square a b) :
    ofSquare (Squares.compose g f) = categoryOps.comp (ofSquare g) (ofSquare f) := rfl
@[simp] theorem toSquare_identity (a : Object.{u}) :
    toSquare (categoryOps.ident (a := a)) = Squares.identity (toRep a) := rfl
@[simp] theorem toSquare_compose {a b c : Object.{u}} (g : Arrow b c) (f : Arrow a b) :
    toSquare (categoryOps.comp g f) = Squares.compose (toSquare g) (toSquare f) := rfl

/-- Both horizontal arrows must agree, including for a noninjective decoder. -/
theorem equiv_iff {a b : Object.{u}} (f g : Arrow a b) :
    (Comma.equiv (equalityCongr FunctionCategory.ops) FunctionCategory.laws
      (RawMap.id_laws (equality FunctionCategory.ops)) (RawMap.id_laws (equality FunctionCategory.ops))).Rel f g ↔ f = g :=
  ⟨fun h => Hom.ext h.1 h.2, fun h => by subst g; exact ⟨rfl, rfl⟩⟩
end SquareKit.Comma.Exact
