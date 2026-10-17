import SquareKit.Category
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Fintype.Sum

/-! Finite matrices with explicit executable finite coordinates. Products are
coordinate sums; zero coordinates give the terminal object. No exponential is required. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SquareKit.MatrixCategory
universe u v

structure Coordinates where
  Carrier : Type u
  finite : Fintype Carrier
  decEq : DecidableEq Carrier

instance : CoeSort Coordinates.{u} (Type u) := ⟨Coordinates.Carrier⟩
attribute [instance] Coordinates.finite Coordinates.decEq

def Coordinates.empty : Coordinates.{u} := ⟨PEmpty, inferInstance, inferInstance⟩
def Coordinates.sum (a b : Coordinates.{u}) : Coordinates.{u} :=
  ⟨Sum a b, inferInstance, inferInstance⟩

/-- A wrapper permits different scalar categories on the same coordinate objects. -/
structure Object (R : Type v) where
  coordinates : Coordinates.{u}

instance (R : Type v) : CoeSort (Object.{u} R) (Type u) := ⟨fun a => a.coordinates⟩
instance (R : Type v) (a : Object.{u} R) : Fintype a := a.coordinates.finite
instance (R : Type v) (a : Object.{u} R) : DecidableEq a := a.coordinates.decEq

variable (R : Type v) [CommSemiring R]

instance category : CategoryTheory.Category (Object.{u} R) where
  Hom a b := Matrix b a R
  id _ := 1
  comp f g := g * f
  id_comp := Matrix.mul_one
  comp_id := Matrix.one_mul
  assoc f g h := (Matrix.mul_assoc h g f).symm

def ops : CategoryOps (Object.{u} R) := ofCategory _

def terminal : TerminalOps (ops R) where
  unit := ⟨Coordinates.empty⟩
  terminal := fun e => nomatch e

def products : ProductOps (ops R) where
  prod a b := ⟨Coordinates.sum a.coordinates b.coordinates⟩
  fst := fun i => Sum.elim (fun j => if i = j then 1 else 0) (fun _ => 0)
  snd := fun i => Sum.elim (fun _ => 0) (fun j => if i = j then 1 else 0)
  pair f g := Sum.elim f g

theorem terminalLaws : TerminalLaws (equality (ops R)) (terminal R) where
  unique f := by funext e; exact nomatch e

theorem productCongr : ProductCongr (equality (ops R)) (products R) where
  pair := by intros; subst_vars; rfl

theorem productLaws : ProductLaws (equality (ops R)) (products R) where
  fst_pair f g := by
    funext i j
    simp [ops, ofCategory, CategoryTheory.CategoryStruct.comp, products, Matrix.mul_apply, Fintype.sum_sum_type]
  snd_pair f g := by
    funext i j
    simp [ops, ofCategory, CategoryTheory.CategoryStruct.comp, products, Matrix.mul_apply, Fintype.sum_sum_type]
  pair_eta f := by
    funext i j
    cases i <;> simp [ops, ofCategory, CategoryTheory.CategoryStruct.comp, products, Matrix.mul_apply, Fintype.sum_sum_type]

/-- Arbitrary matrix composition recovers equality, not merely observational equivalence. -/
theorem association {a b c d : Object.{u} R}
    (h : (ops R).Hom c d) (g : (ops R).Hom b c) (f : (ops R).Hom a b) :
    (ops R).comp ((ops R).comp h g) f = (ops R).comp h ((ops R).comp g f) :=
  (ofCategoryLaws (Object R)).assoc h g f

/-- The matrix product universal property holds on concrete matrix entries. -/
theorem pair_recover {a b c : Object.{u} R} (f : (ops R).Hom a ((products R).prod b c)) :
    (products R).pair ((ops R).comp (products R).fst f)
      ((ops R).comp (products R).snd f) = f := (productLaws R).pair_eta f
end SquareKit.MatrixCategory
