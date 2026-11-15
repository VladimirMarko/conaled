import SquareKit.CartesianOperations
import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-! Raw tensor operations and selected structural comparisons. These records
assert no pentagon, triangle, hexagon, naturality or inverse equations. -/
namespace SquareKit
universe u v

structure TensorOps {O : Type u} (C : CategoryOps.{u,v} O) where
  obj : O → O → O
  map : {a b c d : O} → C.Hom a c → C.Hom b d → C.Hom (obj a b) (obj c d)

structure TensorComparisons {O : Type u} {C : CategoryOps.{u,v} O} (T : TensorOps C) where
  unit : O
  left : ∀ a, Comparison C (T.obj unit a) a
  right : ∀ a, Comparison C (T.obj a unit) a
  assoc : ∀ a b c, Comparison C (T.obj (T.obj a b) c) (T.obj a (T.obj b c))

structure TensorBraiding {O : Type u} {C : CategoryOps.{u,v} O} (T : TensorOps C) where
  swap : ∀ a b, Comparison C (T.obj a b) (T.obj b a)

namespace TensorOps
variable {O : Type u} {C : CategoryOps.{u,v} O} (T : TensorOps C)

def first {a b c : O} (f : C.Hom a c) : C.Hom (T.obj a b) (T.obj c b) := T.map f C.ident
def second {a b d : O} (g : C.Hom b d) : C.Hom (T.obj a b) (T.obj a d) := T.map C.ident g
def twice {a c : O} (f : C.Hom a c) : C.Hom (T.obj a a) (T.obj c c) := T.map f f

def ofProducts (P : ProductOps C) : TensorOps C := ⟨P.prod, Cartesian.tensor P⟩

theorem products_first (P : ProductOps C) {a b c : O} (f : C.Hom a c) :
    (ofProducts P).first (b := b) f = Cartesian.first P f := rfl

theorem products_second (P : ProductOps C) {a b d : O} (g : C.Hom b d) :
    (ofProducts P).second (a := a) g = Cartesian.second P g := rfl

theorem products_twice (P : ProductOps C) {a c : O} (f : C.Hom a c) :
    (ofProducts P).twice f = Cartesian.twice P f := rfl

open CategoryTheory MonoidalCategory

def ofMonoidal (O : Type u) [Category.{v} O] [MonoidalCategory O] : TensorOps (ofCategory O) where
  obj := tensorObj
  map := tensorHom

end TensorOps

namespace TensorComparisons
variable {O : Type u} {C : CategoryOps.{u,v} O} {T : TensorOps C}

def constLeft (U : TensorComparisons T) {a b : O} (f : C.Hom U.unit a) : C.Hom b (T.obj a b) :=
  C.comp (T.first f) (U.left b).inv

def constRight (U : TensorComparisons T) {a b : O} (f : C.Hom U.unit b) : C.Hom a (T.obj a b) :=
  C.comp (T.second f) (U.right a).inv

def constants (U : TensorComparisons T) {a b : O} (f : C.Hom U.unit a) (g : C.Hom U.unit b) :
    C.Hom U.unit (T.obj a b) := C.comp (T.map f g) (U.left U.unit).inv

def ofProducts (P : ProductOps C) (U : TerminalOps C) : TensorComparisons (TensorOps.ofProducts P) where
  unit := U.unit
  left _ := ⟨Cartesian.unitLeft P U, Cartesian.insertLeft P U⟩
  right _ := ⟨Cartesian.unitRight P U, Cartesian.insertRight P U⟩
  assoc _ _ _ := ⟨Cartesian.assocRight P, Cartesian.assocLeft P⟩

theorem products_constLeft (P : ProductOps C) (U : TerminalOps C)
    {a b : O} (f : C.Hom U.unit a) :
    (ofProducts P U).constLeft (b := b) f = Cartesian.constLeft P U f := rfl

theorem products_constRight (P : ProductOps C) (U : TerminalOps C)
    {a b : O} (f : C.Hom U.unit b) :
    (ofProducts P U).constRight (a := a) f = Cartesian.constRight P U f := rfl

theorem products_constants (P : ProductOps C) (U : TerminalOps C)
    {a b : O} (f : C.Hom U.unit a) (g : C.Hom U.unit b) :
    (ofProducts P U).constants f g = Cartesian.constants P U f g := rfl

open CategoryTheory MonoidalCategory

def ofMonoidal (O : Type u) [Category.{v} O] [MonoidalCategory O] :
    TensorComparisons (TensorOps.ofMonoidal O) where
  unit := tensorUnit O
  left a := ⟨(leftUnitor a).hom, (leftUnitor a).inv⟩
  right a := ⟨(rightUnitor a).hom, (rightUnitor a).inv⟩
  assoc a b c := ⟨(associator a b c).hom, (associator a b c).inv⟩

end TensorComparisons

namespace TensorBraiding
variable {O : Type u} {C : CategoryOps.{u,v} O}

def ofProducts (P : ProductOps C) : TensorBraiding (TensorOps.ofProducts P) where
  swap _ _ := ⟨Cartesian.swap P, Cartesian.swap P⟩

open CategoryTheory MonoidalCategory BraidedCategory

def ofBraided (O : Type u) [Category.{v} O] [MonoidalCategory O] [BraidedCategory O] :
    TensorBraiding (TensorOps.ofMonoidal O) where
  swap a b := ⟨(braiding a b).hom, (braiding a b).inv⟩

end TensorBraiding
end SquareKit
