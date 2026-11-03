import SquareKit.MatrixCategory
import SquareKit.CommaProducts
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Logic.Equiv.Sum

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SquareKit.MatrixDoubling
open MatrixCategory
universe u
abbrev M := MatrixCategory.ops.{u} Nat
abbrev P : ProductOps M.{u} := MatrixCategory.products Nat
/-- Tags distinguish the two source families without changing their matrices. -/
structure Source (tag : Bool) where
  coordinates : Coordinates.{u}
instance (tag) : CoeSort (Source.{u} tag) (Type u) := ⟨fun a => a.coordinates⟩
instance (tag) (a : Source.{u} tag) : Fintype a := a.coordinates.finite
instance (tag) (a : Source.{u} tag) : DecidableEq a := a.coordinates.decEq

abbrev sourceOps (tag) : CategoryOps (Source.{u} tag) where
  Hom a b := Matrix b a Nat
  ident := 1
  comp g f := g * f

abbrev sourceProducts (tag) : ProductOps (sourceOps.{u} tag) where
  prod a b := ⟨Coordinates.sum a.coordinates b.coordinates⟩
  fst := fun i => Sum.elim (fun j => if i = j then 1 else 0) (fun _ => 0)
  snd := fun i => Sum.elim (fun _ => 0) (fun j => if i = j then 1 else 0)
  pair f g := Sum.elim f g

abbrev identityMap : RawMap (sourceOps.{u} false) M :=
  ⟨fun a => ⟨a.coordinates⟩, fun f => f⟩
def duplicate {a b : Type u} (f : Matrix b a Nat) : Matrix (b ⊕ b) (a ⊕ a) Nat :=
  Matrix.fromBlocks f 0 0 f

abbrev doublingMap : RawMap (sourceOps.{u} true) M :=
  ⟨fun a => ⟨Coordinates.sum a.coordinates a.coordinates⟩, duplicate⟩

theorem duplicate_id (a : Coordinates.{u}) : duplicate (1 : Matrix a a Nat) = 1 :=
  Matrix.fromBlocks_one

theorem duplicate_comp {a b c : Coordinates.{u}} (g : Matrix c b Nat) (f : Matrix b a Nat) :
    duplicate (g * f) = duplicate g * duplicate f := by
  simp [duplicate, Matrix.fromBlocks_multiply]

theorem identityMap_laws : MapLaws identityMap (equality _) (equality _) where
  congr := by intros; subst_vars; rfl
  ident := rfl
  comp _ _ := rfl

theorem doublingMap_laws : MapLaws doublingMap (equality _) (equality _) where
  congr := by intros; subst_vars; rfl
  ident := duplicate_id _
  comp g f := duplicate_comp g f

/-- Rearranges copy-major coordinates into product-major coordinates. -/
def shuffle (a b : Type u) : ((a ⊕ b) ⊕ (a ⊕ b)) ≃ ((a ⊕ a) ⊕ (b ⊕ b)) :=
  { toFun := fun x => match x with
      | .inl (.inl x) => .inl (.inl x)
      | .inl (.inr x) => .inr (.inl x)
      | .inr (.inl x) => .inl (.inr x)
      | .inr (.inr x) => .inr (.inr x)
    invFun := fun x => match x with
      | .inl (.inl x) => .inl (.inl x)
      | .inl (.inr x) => .inr (.inl x)
      | .inr (.inl x) => .inl (.inr x)
      | .inr (.inr x) => .inr (.inr x)
    left_inv := by rintro ((x | x) | (x | x)) <;> rfl
    right_inv := by rintro ((x | x) | (x | x)) <;> rfl }

def permutation {a b : Type u} [DecidableEq b] (e : a ≃ b) : Matrix b a Nat :=
  fun i j => if i = e j then 1 else 0

theorem permutation_mul {a b c : Type u} [Fintype b] [DecidableEq b] [DecidableEq c]
    (e : a ≃ b) (d : b ≃ c) : permutation d * permutation e = permutation (e.trans d) := by
  funext i j
  simp [Matrix.mul_apply, permutation]

theorem permutation_id {a : Type u} [DecidableEq a] : permutation (Equiv.refl a) = (1 : Matrix a a Nat) := by
  funext i j
  simp [permutation, Matrix.one_apply]

def doublingProducts : ProductMap doublingMap (sourceProducts true) P := fun a b =>
  ⟨permutation (shuffle a b), permutation (shuffle a b).symm⟩

theorem doublingProducts_inverse (a b : Source.{u} true) :
    ComparisonLaws (equality M) (doublingProducts a b) where
  hom_inv := by
    change permutation (shuffle a b) * permutation (shuffle a b).symm = 1
    rw [permutation_mul]
    simpa using (permutation_id (a := (a ⊕ a) ⊕ (b ⊕ b)))
  inv_hom := by
    change permutation (shuffle a b).symm * permutation (shuffle a b) = 1
    rw [permutation_mul]
    simpa using (permutation_id (a := (a ⊕ b) ⊕ (a ⊕ b)))

theorem mul_permutation {a b c : Type u} [Fintype b] [DecidableEq b]
    (f : Matrix c b Nat) (e : a ≃ b) : f * permutation e = f.submatrix id e := by
  funext i j
  simp [Matrix.mul_apply, permutation, Matrix.submatrix]

theorem permutation_mul_matrix {a b c : Type u} [Fintype b] [DecidableEq a] [DecidableEq b]
    (e : b ≃ a) (f : Matrix b c Nat) : permutation e * f = f.submatrix e.symm id := by
  funext i j
  change (∑ x, (if i = e x then 1 else 0) * f x j) = f (e.symm i) j
  calc
    _ = ∑ x, (if e.symm i = x then 1 else 0) * f x j := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases h : i = e x
      · have h' : e.symm i = x := e.symm_apply_eq.mpr h
        simp only [ite_eq_left h, ite_eq_left h']
      · have h' : ¬ e.symm i = x := fun hx => h (e.symm_apply_eq.mp hx)
        simp only [ite_eq_right h, ite_eq_right h']
    _ = _ := by simp

theorem doublingProducts_laws : ProductMapLaws (equality M) doublingProducts.{u} where
  fst := by
    intro a b
    change duplicate (sourceProducts true).fst = (_ : Matrix (a ⊕ a) ((a ⊕ a) ⊕ (b ⊕ b)) Nat) * permutation (shuffle a b)
    rw [mul_permutation]
    funext i j
    rcases i with i | i <;> rcases j with (j | j) | (j | j) <;>
      simp [duplicate, Matrix.fromBlocks, sourceProducts, P, MatrixCategory.products,
        Coordinates.sum, Matrix.submatrix, shuffle, Equiv.coe_fn_mk]
  snd := by
    intro a b
    change duplicate (sourceProducts true).snd = (_ : Matrix (b ⊕ b) ((a ⊕ a) ⊕ (b ⊕ b)) Nat) * permutation (shuffle a b)
    rw [mul_permutation]
    funext i j
    rcases i with i | i <;> rcases j with (j | j) | (j | j) <;>
      simp [duplicate, Matrix.fromBlocks, sourceProducts, P, MatrixCategory.products,
        Coordinates.sum, Matrix.submatrix, shuffle, Equiv.coe_fn_mk]
  pair := by
    intro a b c f g
    change duplicate (Matrix.fromRows f g) = permutation (shuffle b c).symm * Matrix.fromRows (duplicate f) (duplicate g)
    rw [permutation_mul_matrix]
    funext i j
    rcases i with (i | i) | (i | i) <;> rcases j with j | j <;>
      simp [duplicate, Matrix.fromBlocks, Matrix.fromRows, Matrix.submatrix, shuffle, Equiv.coe_fn_mk]

def identityProducts : ProductMap identityMap (sourceProducts false) P :=
  fun a b => ⟨(1 : Matrix (a ⊕ b) (a ⊕ b) Nat), (1 : Matrix (a ⊕ b) (a ⊕ b) Nat)⟩
theorem identityProducts_inverse (a b : Source.{u} false) :
    ComparisonLaws (equality M) (identityProducts a b) :=
  ⟨Matrix.one_mul _, Matrix.one_mul _⟩
theorem identityProducts_laws : ProductMapLaws (equality M) identityProducts.{u} where
  fst := (Matrix.mul_one _).symm
  snd := (Matrix.mul_one _).symm
  pair _f _g := (Matrix.one_mul _).symm

abbrev Object := Comma.Obj identityMap.{u} doublingMap
abbrev Arrow (a b : Object.{u}) := Comma.Hom (equality M) a b
abbrev categoryOps : CategoryOps Object.{u} := Comma.ops (equalityCongr M)
  (ofCategoryLaws _) identityMap_laws doublingMap_laws
abbrev products : ProductOps categoryOps.{u} := Comma.productOps (equalityCongr M)
  (ofCategoryLaws _) identityMap_laws doublingMap_laws identityProducts doublingProducts
  identityProducts_inverse doublingProducts_inverse identityProducts_laws doublingProducts_laws
  (MatrixCategory.productCongr Nat) (MatrixCategory.productLaws Nat)

/-- Embedding each matrix into the first copy gives squares for all matrices. -/
def embed (a : Coordinates.{u}) : Object :=
  ⟨⟨a⟩, ⟨a⟩, Matrix.fromRows 1 0⟩
def embedArrow {a b : Coordinates.{u}} (f : Matrix b a Nat) : Arrow (embed a) (embed b) where
  left := f
  right := f
  commutes := by
    change Matrix.fromRows (1 : Matrix b b Nat) (0 : Matrix b b Nat) * f = duplicate f * Matrix.fromRows (1 : Matrix a a Nat) (0 : Matrix a a Nat)
    simp [duplicate, Matrix.fromBlocks_mul_fromRows, Matrix.fromRows_mul]

@[simp] theorem embedArrow_identity (a : Coordinates.{u}) :
    embedArrow (1 : Matrix a a Nat) = categoryOps.ident := rfl
@[simp] theorem embedArrow_comp {a b c : Coordinates.{u}} (g : Matrix c b Nat) (f : Matrix b a Nat) :
    embedArrow (g * f) = categoryOps.comp (embedArrow g) (embedArrow f) := rfl

theorem matrix_product_commutes {a b c : Object.{u}} (f : Arrow a b) (g : Arrow a c) :
    M.comp (products.prod b c).connector (identityMap.map (products.pair f g).left) =
      M.comp (doublingMap.map (products.pair f g).right) a.connector :=
  (products.pair f g).commutes

theorem sourceProductLaws (tag) : ProductLaws (equality (sourceOps.{u} tag)) (sourceProducts tag) where
  fst_pair := by
    intro a b c f g
    exact (MatrixCategory.productLaws Nat).fst_pair
      (a := ⟨a.coordinates⟩) (b := ⟨b.coordinates⟩) (c := ⟨c.coordinates⟩) f g
  snd_pair := by
    intro a b c f g
    exact (MatrixCategory.productLaws Nat).snd_pair
      (a := ⟨a.coordinates⟩) (b := ⟨b.coordinates⟩) (c := ⟨c.coordinates⟩) f g
  pair_eta := by
    intro a b c f
    exact (MatrixCategory.productLaws Nat).pair_eta
      (a := ⟨a.coordinates⟩) (b := ⟨b.coordinates⟩) (c := ⟨c.coordinates⟩) f

theorem products_laws : ProductLaws (Comma.equiv (equalityCongr M) (ofCategoryLaws _)
    identityMap_laws doublingMap_laws) products.{u} :=
  Comma.productLaws _ _ _ _ _ _ _ _ _ _ _ _ (sourceProductLaws false) (sourceProductLaws true)

theorem first_fork {a b c : Object.{u}} (f : Arrow a b) (g : Arrow a c) :
    categoryOps.comp products.fst (products.pair f g) = f := by
  have h := products_laws.fst_pair f g
  exact Comma.Hom.ext h.1 h.2

theorem second_fork {a b c : Object.{u}} (f : Arrow a b) (g : Arrow a c) :
    categoryOps.comp products.snd (products.pair f g) = g := by
  have h := products_laws.snd_pair f g
  exact Comma.Hom.ext h.1 h.2

theorem fork_eta {a b c : Object.{u}} (f : Arrow a (products.prod b c)) :
    products.pair (categoryOps.comp products.fst f) (categoryOps.comp products.snd f) = f := by
  have h := products_laws.pair_eta f
  exact Comma.Hom.ext h.1 h.2

def oneCoordinate : Coordinates := ⟨Fin 1, inferInstance, inferInstance⟩
def triple : Arrow (embed oneCoordinate) (embed oneCoordinate) :=
  embedArrow (fun _ _ => 3)

theorem triple_nonidentity : triple ≠ categoryOps.ident := by
  intro h
  have k := congrArg (fun f : Arrow (embed oneCoordinate) (embed oneCoordinate) => f.left (0 : Fin 1) (0 : Fin 1)) h
  change (3 : Nat) = 1 at k
  contradiction

/-- The square has connector [1;0], left side [3], and right interpretation diag(3,3). -/
theorem triple_commutes : M.comp (embed oneCoordinate).connector (identityMap.map triple.left) =
    M.comp (doublingMap.map triple.right) (embed oneCoordinate).connector := triple.commutes

theorem shuffle_moves_middle :
    shuffle (Fin 1) (Fin 1) (.inl (.inr 0)) = .inr (.inl 0) := rfl

theorem comparison_middle_entry :
    (doublingProducts (⟨oneCoordinate⟩ : Source true) ⟨oneCoordinate⟩).hom
      (.inr (.inl (0 : Fin 1))) (.inl (.inr (0 : Fin 1))) = 1 := by
  rfl

theorem comparison_nonidentity :
    (doublingProducts (⟨oneCoordinate⟩ : Source true) ⟨oneCoordinate⟩).hom ≠
      (1 : Matrix ((Fin 1 ⊕ Fin 1) ⊕ (Fin 1 ⊕ Fin 1))
        ((Fin 1 ⊕ Fin 1) ⊕ (Fin 1 ⊕ Fin 1)) Nat) := by
  intro h
  have k := congrArg (fun f : Matrix ((Fin 1 ⊕ Fin 1) ⊕ (Fin 1 ⊕ Fin 1))
    ((Fin 1 ⊕ Fin 1) ⊕ (Fin 1 ⊕ Fin 1)) Nat => f (.inr (.inl 0)) (.inl (.inr 0))) h
  change (1 : Nat) = 0 at k
  contradiction

theorem matrix_identity_commutes (a : Object.{u}) :
    M.comp a.connector (identityMap.map (categoryOps.ident (a := a)).left) =
      M.comp (doublingMap.map (categoryOps.ident (a := a)).right) a.connector :=
  (categoryOps.ident (a := a)).commutes

theorem matrix_comp_commutes {a b c : Object.{u}} (g : Arrow b c) (f : Arrow a b) :
    M.comp c.connector (identityMap.map (categoryOps.comp g f).left) =
      M.comp (doublingMap.map (categoryOps.comp g f).right) a.connector :=
  (categoryOps.comp g f).commutes

abbrev sourceTerminal (tag) : TerminalOps (sourceOps.{u} tag) where
  unit := ⟨Coordinates.empty⟩
  terminal := fun e => nomatch e

def identityTerminal : TerminalMap identityMap (sourceTerminal false) (MatrixCategory.terminal Nat) :=
  ⟨(fun e => nomatch e), (fun e => nomatch e)⟩
def doublingTerminal : TerminalMap doublingMap (sourceTerminal true) (MatrixCategory.terminal Nat) :=
  ⟨(fun e => nomatch e), (fun e => match e with | .inl e => nomatch e | .inr e => nomatch e)⟩
theorem identityTerminal_inverse : ComparisonLaws (equality M) identityTerminal.{u} where
  hom_inv := by funext e; exact nomatch e
  inv_hom := by funext e; exact nomatch e
theorem doublingTerminal_inverse : ComparisonLaws (equality M) doublingTerminal.{u} where
  hom_inv := by funext e; exact nomatch e
  inv_hom := by funext e; rcases e with e | e <;> exact nomatch e
theorem identityTerminal_laws : TerminalMapLaws (equality M) identityTerminal.{u} where
  terminal := by intros; funext e; exact nomatch e
theorem doublingTerminal_laws : TerminalMapLaws (equality M) doublingTerminal.{u} where
  terminal := by intros; funext e; rcases e with e | e <;> exact nomatch e
abbrev terminal : TerminalOps categoryOps.{u} := Comma.terminalOps (equalityCongr M)
  (ofCategoryLaws _) identityMap_laws doublingMap_laws identityTerminal doublingTerminal
  identityTerminal_inverse identityTerminal_laws doublingTerminal_laws (MatrixCategory.terminalLaws Nat)

end SquareKit.MatrixDoubling
