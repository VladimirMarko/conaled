import SquareKit.Squared
import SquareKit.RawArrow
import SquareKit.SetoidMonoid
import SquareKit.RawQuiv
import SquareKit.FunctionLift
import SquareKit.CartesianInverses
import SquareKit.RawReasoning
import SquareKit.CartesianPreservation
import SquareKit.CodeCategory
import SquareKit.MatrixCategory

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace Examples.RawConstructions
open SquareKit CategoricalCompiler
universe u v w

/-- A raw-code component is retained alongside a finite-matrix component. -/
def mixed (Prim : Ty → Ty → Type) := CategoryProduct.ops (CodeCategory.ops Prim) (MatrixCategory.ops Nat)

theorem mixed_laws {Prim : Ty → Ty → Type} {B : Type}
    (meaning : {a b : Ty} → Prim a b → Val B a → Val B b) :
    CategoryLaws (mixed Prim) (CategoryProduct.equiv _ _ (CodeCategory.equiv meaning) (equality _)) :=
  CategoryProduct.laws (CodeCategory.laws meaning) (ofCategoryLaws _)

def one : MatrixCategory.Object Nat := ⟨⟨Fin 1,inferInstance,inferInstance⟩⟩

theorem mixed_comp {Prim : Ty → Ty → Type} :
    (mixed Prim).comp (a := (.base,one)) (b := (.base,one)) (c := (.base,one)) ((.ident : Code Prim .base .base), (fun _ _ : Fin 1 => 3))
      (.ident, (fun _ _ : Fin 1 => 2)) =
      ((.comp .ident .ident : Code Prim .base .base), (fun _ _ : Fin 1 => 6)) := by
  apply Prod.ext
  · rfl
  · funext a b
    simp [mixed, CategoryProduct.ops, MatrixCategory.ops, ofCategory,
      CategoryTheory.CategoryStruct.comp, Matrix.mul_apply, one]

theorem raw_ident_not_collapsed {Prim : Ty → Ty → Type} :
    (Code.comp Code.ident Code.ident : Code Prim .base .base) ≠ Code.ident := by
  intro h; cases h

/-- Four distinct entries make the middle-four comparison observable. -/
theorem shuffle_value :
    (Squared.productMap (P := FunctionCategory.products) (Nat,Nat) (Nat,Nat)).hom
      ((1,2),(3,4)) = ((1,3),(2,4)) := rfl

theorem shuffle_not_identity :
    (Squared.productMap (P := FunctionCategory.products) (Nat,Nat) (Nat,Nat)).hom ≠ id := by
  intro h
  have := congrFun h ((1,2),(3,4))
  change ((1,3),(2,4)) = ((1,2),(3,4)) at this
  cases this

theorem shuffle_recovers (x : (Nat × Nat) × (Nat × Nat)) :
    (Squared.productMap (P := FunctionCategory.products) (Nat,Nat) (Nat,Nat)).inv
      ((Squared.productMap (P := FunctionCategory.products) (Nat,Nat) (Nat,Nat)).hom x) = x :=
  congrFun (Squared.productMap_inverse (equalityCongr _) FunctionCategory.laws
    FunctionCategory.productCongr FunctionCategory.productLaws (Nat,Nat) (Nat,Nat)).inv_hom x

/-- Noncommutative lists distinguish the chosen composition order. -/
def words : SetoidMonoid.Ops (List Nat) := ⟨[],List.append⟩
theorem words_order : (SetoidMonoid.ops words).comp (a := ()) (b := ()) (c := ()) [1] [2] = [1,2] := rfl
theorem words_order_distinct : (SetoidMonoid.ops words).comp (a := ()) (b := ()) (c := ()) [1] [2] ≠
    (SetoidMonoid.ops words).comp (a := ()) (b := ()) (c := ()) [2] [1] := by change [1,2] ≠ ([2,1] : List Nat); decide

def wordSetoid : Setoid (List Nat) := ⟨Eq, ⟨Eq.refl,Eq.symm,Eq.trans⟩⟩
theorem words_laws : SetoidMonoid.Laws words wordSetoid :=
  ⟨fun h k => congrArg₂ List.append h k, List.nil_append, List.append_nil, List.append_assoc⟩
theorem words_category : CategoryLaws (SetoidMonoid.ops words) (SetoidMonoid.equiv words wordSetoid) :=
  SetoidMonoid.laws words_laws

def sampleSquare : RawArrow.Hom (equality FunctionCategory.ops)
    (⟨Nat,Nat,fun n : Nat => n+1⟩ : RawArrow.Obj FunctionCategory.ops)
    ⟨Nat,Nat,fun n : Nat => n+1⟩ :=
  ⟨fun n : Nat => n+2,fun n : Nat => n+2,by change (fun n : Nat => (n+2)+1) = (fun n : Nat => (n+1)+2); funext n; omega⟩
theorem square_transpose (n : Nat) : (RawArrow.transpose sampleSquare).left n = n+1 := rfl
theorem square_transpose_twice : RawArrow.transpose (RawArrow.transpose sampleSquare) = sampleSquare :=
  RawArrow.transpose_transpose sampleSquare

theorem composed_object (n : Nat) :
    (RawArrow.compose (⟨Nat,Nat,fun n : Nat => 2*n⟩ : RawArrow.Obj FunctionCategory.ops)
      ⟨Nat,Nat,fun n : Nat => n+1⟩ rfl).connector n = 2*(n+1) := rfl

theorem embedded_arrow (n : Nat) :
    ((RawArrow.identityMap (equalityCongr _) FunctionCategory.laws).map (fun n : Nat => n+7)).left n = n+7 := rfl

/-- Empty-arrow quivers are CAT objects, although their nonempty carrier cannot have identities. -/
def discreteWithoutLoops : RawQuiv.Obj := ⟨Bool,⟨fun _ _ => Empty⟩⟩
theorem no_category_operations : ¬ ∃ C : CategoryOps Bool, C.Hom = fun _ _ => Empty := by
  rintro ⟨C,h⟩
  have impossible : Empty := cast (congrFun (congrFun h false) false) (C.ident (a := false))
  exact impossible.elim

theorem lift_two_levels {A B : Type u} (f : A → B) (a : A) :
    FunctionLift.map.{max u v,w}.map (FunctionLift.map.{u,v}.map f)
      (ULift.up (ULift.up a)) = ULift.up (ULift.up (f a)) := rfl

theorem lifted_tensor {A B C D : Type u} (f : A → C) (g : B → D) :
    (equality FunctionCategory.ops).Rel
      (FunctionLift.map.{u,v}.map (Cartesian.tensor FunctionCategory.products f g))
      (FunctionCategory.ops.comp (FunctionLift.products C D).inv
        (FunctionCategory.ops.comp
          (Cartesian.tensor FunctionCategory.products (FunctionLift.map.map f) (FunctionLift.map.map g))
          (FunctionLift.products A B).hom)) :=
  CartesianPreservation.tensor_conjugate (equalityCongr _) FunctionCategory.laws
    FunctionCategory.productCongr FunctionCategory.productLaws FunctionLift.map_laws FunctionLift.products_laws f g

/-- Unsquaring can forget a component when the other input factor is empty. -/
theorem induced_not_componentwise :
    ((Squared.unsquare FunctionCategory.products).induced (equality _)).Rel
      (a := (Nat,Empty)) (b := (Nat,Empty)) (id,id) (Nat.succ,id) := by
  funext x
  exact nomatch x.2

theorem components_distinct :
    ¬ (CategoryProduct.equiv FunctionCategory.ops FunctionCategory.ops (equality _) (equality _)).Rel
      (a := (Nat,Empty)) (b := (Nat,Empty)) (id,id) (Nat.succ,id) := by
  intro h
  have bad := congrFun h.1 0
  cases bad

def lengthSetoid : Setoid (List Nat) :=
  ⟨fun a b => a.length = b.length, ⟨fun _ => rfl, Eq.symm, Eq.trans⟩⟩
theorem words_length_laws : SetoidMonoid.Laws words lengthSetoid := by
  constructor
  · intro a b c d h k
    change (a++c).length = (b++d).length
    change a.length = b.length at h
    change c.length = d.length at k
    simp only [List.length_append, h, k]
  · intro a; rfl
  · intro a; exact congrArg List.length (List.append_nil a)
  · intro a b c; exact congrArg List.length (List.append_assoc a b c)

theorem words_length_semantics : (SetoidMonoid.equiv words lengthSetoid).Rel
    (a := ()) (b := ()) [1] [2] := rfl

def pastedSquare := RawArrow.vertical (equalityCongr _) FunctionCategory.laws
  sampleSquare sampleSquare (rfl : sampleSquare.right = sampleSquare.left)
theorem pasted_connector (n : Nat) :
    (RawArrow.compose (⟨Nat,Nat,fun n : Nat => n+1⟩ : RawArrow.Obj FunctionCategory.ops)
      ⟨Nat,Nat,fun n : Nat => n+1⟩ rfl).connector n = n+2 := by
  change (n+1)+1 = n+2; omega
theorem pasted_outer_arrow (n : Nat) : pastedSquare.left n = n+2 := rfl
/-- CAT Cartesian functors preserve both nullary and binary products. -/
theorem quiv_cartesian_identity :
    RawQuiv.CartesianFunctorLaws
      (RawQuiv.ofRawMap (RawMap.id FunctionCategory.ops))
      (equality FunctionCategory.ops) (ProductMap.id FunctionCategory.products)
      (TerminalMap.id FunctionCategory.terminal) :=
  ⟨ProductMap.id_laws FunctionCategory.laws _,
    TerminalMap.id_laws FunctionCategory.laws _⟩

end Examples.RawConstructions
