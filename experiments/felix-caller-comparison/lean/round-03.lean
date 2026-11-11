import SquareKit.CommaProducts
import SquareKit.FunctionCategory
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace Trial
open SquareKit
abbrev V (n : Nat) := Fin n → Nat
abbrev Mat (n m : Nat) := Matrix (Fin m) (Fin n) Nat

def raw : CategoryOps Nat where
  Hom := Mat
  ident := 1
  comp g f := g * f

def coord : CategoryOps Nat where
  Hom n m := V n → V m
  ident := id
  comp g f := g ∘ f

def split {n m} (x : V (n+m)) : V n × V m :=
  (fun i => x (Fin.castAdd m i), fun i => x (Fin.natAdd n i))
def join {n m} (x : V n × V m) : V (n+m) := Fin.addCases x.1 x.2

theorem split_join {n m} (x : V n × V m) : split (join x) = x := by
  simp [split, join]
theorem join_split {n m} (x : V (n+m)) : join (split x) = x := by
  funext i
  refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [join, split]

def cp : ProductOps coord where
  prod := Nat.add
  fst x := (split x).1
  snd x := (split x).2
  pair f g x := join (f x, g x)
def ct : TerminalOps coord where
  unit := 0
  terminal _ := Fin.elim0

def types : RawMap coord FunctionCategory.ops where
  obj := V
  map f := f
abbrev ce := types.induced (equality FunctionCategory.ops)
theorem types_laws : MapLaws types ce (equality FunctionCategory.ops) :=
  types.inducedLaws _ rfl (fun _ _ => rfl)
theorem coord_laws : CategoryLaws coord ce :=
  RawMap.transportLaws types_laws (types.induced_reflects _) (equalityCongr _) FunctionCategory.laws
theorem coord_congr : CategoryCongr coord ce :=
  RawMap.transportCongr types_laws (types.induced_reflects _) (equalityCongr _)

def typeProducts : ProductMap types cp FunctionCategory.products := fun _ _ => ⟨split, join⟩
theorem typeProducts_inverse (n m) : ComparisonLaws (equality _) (typeProducts n m) :=
  ⟨funext split_join, funext join_split⟩
theorem typeProducts_laws : ProductMapLaws (equality _) typeProducts where
  fst := rfl
  snd := rfl
  pair _ _ := rfl
theorem coord_products : ProductLaws ce cp :=
  ProductMap.transportLaws types_laws (types.induced_reflects _) (equalityCongr _) FunctionCategory.laws
    typeProducts_inverse typeProducts_laws FunctionCategory.productCongr FunctionCategory.productLaws
theorem coord_productCongr : ProductCongr ce cp :=
  ProductMap.transportCongr types_laws (types.induced_reflects _) (equalityCongr _)
    typeProducts_laws FunctionCategory.productCongr

def typeTerminal : TerminalMap types ct FunctionCategory.terminal :=
  ⟨fun _ => PUnit.unit, fun _ => Fin.elim0⟩
theorem typeTerminal_inverse : ComparisonLaws (equality _) typeTerminal where
  hom_inv := rfl
  inv_hom := by funext x i; exact Fin.elim0 i
theorem typeTerminal_laws : TerminalMapLaws (equality _) typeTerminal := ⟨rfl⟩
theorem coord_terminal : TerminalLaws ce ct :=
  TerminalMap.transportLaws (types.induced_reflects _) (equalityCongr _) FunctionCategory.laws
    typeTerminal_inverse typeTerminal_laws FunctionCategory.terminalLaws

def interpret : RawMap raw coord where
  obj := id
  map A := Matrix.mulVec A
abbrev semantic := interpret.induced ce

theorem interpret_laws : MapLaws interpret semantic ce :=
  interpret.inducedLaws _ (by intro n; funext x; exact Matrix.one_mulVec x)
    (by intro a b c g f; funext x; exact (Matrix.mulVec_mulVec x g f).symm)

def mp : ProductOps raw where
  prod := Nat.add
  fst := fun i j => if j = Fin.castAdd _ i then 1 else 0
  snd := fun i j => if j = Fin.natAdd _ i then 1 else 0
  pair f g := Fin.addCases f g
def mt : TerminalOps raw where
  unit := 0
  terminal := fun i => Fin.elim0 i

def matrixProducts : ProductMap interpret mp cp := fun n m => ⟨id, id⟩
theorem matrixProducts_inverse (n m) : ComparisonLaws ce (matrixProducts n m) := ⟨rfl, rfl⟩
theorem matrixProducts_laws : ProductMapLaws ce matrixProducts where
  fst := by
    intro n m; funext x i
    simp [types, interpret, mp, Matrix.mulVec, dotProduct, coord, cp, split, matrixProducts]
  snd := by
    intro n m; funext x i
    simp [types, interpret, mp, Matrix.mulVec, dotProduct, coord, cp, split, matrixProducts]
  pair := by
    intro a b c f g; funext x i
    refine Fin.addCases ?_ ?_ i <;> intro j <;>
      simp [types, interpret, mp, Matrix.mulVec, dotProduct, coord, cp, join, matrixProducts]

def matrixTerminal : TerminalMap interpret mt ct := ⟨id, id⟩
theorem matrixTerminal_inverse : ComparisonLaws ce matrixTerminal := ⟨rfl, rfl⟩
theorem matrixTerminal_laws : TerminalMapLaws ce matrixTerminal where
  terminal := by intro n; funext x i; exact Fin.elim0 i

theorem matrix_laws : CategoryLaws raw semantic :=
  RawMap.transportLaws interpret_laws (interpret.induced_reflects _) coord_congr coord_laws
theorem matrix_congr : CategoryCongr raw semantic :=
  RawMap.transportCongr interpret_laws (interpret.induced_reflects _) coord_congr
theorem matrix_products : ProductLaws semantic mp :=
  ProductMap.transportLaws interpret_laws (interpret.induced_reflects _) coord_congr coord_laws
    matrixProducts_inverse matrixProducts_laws coord_productCongr coord_products
theorem matrix_productCongr : ProductCongr semantic mp :=
  ProductMap.transportCongr interpret_laws (interpret.induced_reflects _) coord_congr
    matrixProducts_laws coord_productCongr
theorem matrix_terminal : TerminalLaws semantic mt :=
  TerminalMap.transportLaws (interpret.induced_reflects _) coord_congr coord_laws
    matrixTerminal_inverse matrixTerminal_laws coord_terminal

-- Semantic equivalence is pointwise action equality, not entry equality.
theorem semantic_iff {n m} (A B : Mat n m) :
    semantic.Rel A B ↔ ∀ x i, Matrix.mulVec A x i = Matrix.mulVec B x i := by
  exact ⟨fun h x i => congrFun (congrFun h x) i, fun h => funext (fun x => funext (h x))⟩
-- Task 2: compose the established packages through the public operations.
def composite := interpret.comp types
theorem composite_laws : MapLaws composite semantic (equality FunctionCategory.ops) :=
  RawMap.comp_laws interpret_laws types_laws
def compositeProducts : ProductMap composite mp FunctionCategory.products :=
  ProductMap.comp matrixProducts typeProducts
theorem compositeProducts_inverse (n m) :
    ComparisonLaws (equality _) (compositeProducts n m) :=
  Comparison.comp_laws (equalityCongr _) FunctionCategory.laws
    (Comparison.map_laws types_laws (matrixProducts_inverse n m)) (typeProducts_inverse n m)
theorem compositeProducts_laws : ProductMapLaws (equality _) compositeProducts :=
  ProductMap.comp_laws types_laws (equalityCongr _) FunctionCategory.laws
    matrixProducts_laws typeProducts_laws
def compositeTerminal : TerminalMap composite mt FunctionCategory.terminal :=
  TerminalMap.comp matrixTerminal typeTerminal
theorem compositeTerminal_inverse : ComparisonLaws (equality _) compositeTerminal :=
  Comparison.comp_laws (equalityCongr _) FunctionCategory.laws
    (Comparison.map_laws types_laws matrixTerminal_inverse) typeTerminal_inverse
theorem compositeTerminal_laws : TerminalMapLaws (equality _) compositeTerminal :=
  TerminalMap.comp_laws types_laws (equalityCongr _) FunctionCategory.laws
    matrixTerminal_laws typeTerminal_laws

theorem composite_action {n m} (A : Mat n m) (x : V n) (i : Fin m) :
    composite.map A x i = ∑ j, A i j * x j := rfl

theorem composite_composition {n m k} (A : Mat n m) (B : Mat m k) (x : V n) :
    composite.map (B * A) x = composite.map B (composite.map A x) :=
  congrFun (composite_laws.comp B A) x

theorem composite_pair {a b c} (A : Mat a b) (B : Mat a c) (x : V a) :
    split (composite.map (mp.pair A B) x) = (composite.map A x, composite.map B x) := by
  have h := congrFun (compositeProducts_laws.pair A B) x
  change composite.map (mp.pair A B) x = join (composite.map A x, composite.map B x) at h
  rw [h, split_join]

theorem composite_first {n m} (x : V (n+m)) :
    composite.map (mp.fst (a := n) (b := m)) x = (split x).1 :=
  congrFun compositeProducts_laws.fst x
theorem composite_second {n m} (x : V (n+m)) :
    composite.map (mp.snd (a := n) (b := m)) x = (split x).2 :=
  congrFun compositeProducts_laws.snd x
end Trial
