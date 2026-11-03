import SquareKit.STLCImage
import SquareKit.STLCExact
import SquareKit.FunctionOptional

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace Examples.FullSourceNaturality
open SquareKit CategoricalCompiler
/-- Reuse an arbitrary function model with Mathlib's bundled function arrows. -/
def bundle {Prim : Ty → Ty → Type} {A : Ty → Type}
    (M : STLCNaturality.Model FunctionCategory.ops Prim A) :
    STLCNaturality.Model (ofCategory (Type)) Prim A where
  terminal := TypeCat.ofHom M.terminal
  fst := TypeCat.ofHom M.fst
  snd := TypeCat.ofHom M.snd
  pair f g := TypeCat.ofHom (M.pair f.hom.toFun g.hom.toFun)
  inl := TypeCat.ofHom M.inl
  inr := TypeCat.ofHom M.inr
  copair f g := TypeCat.ofHom (M.copair f.hom.toFun g.hom.toFun)
  dist := TypeCat.ofHom M.dist
  curry f := TypeCat.ofHom (M.curry f.hom.toFun)
  apply := TypeCat.ofHom M.apply
  primitive p := TypeCat.ofHom (M.primitive p)

theorem bundle_preserves {Prim : Ty → Ty → Type} {A : Ty → Type}
    (M : STLCNaturality.Model FunctionCategory.ops Prim A) :
    STLCNaturality.Preserves FunctionCategory.toTypes (equality _) M (bundle M) where
  terminal := rfl
  fst := rfl
  snd := rfl
  pair _ _ := rfl
  inl := rfl
  inr := rfl
  copair _ _ := rfl
  dist := rfl
  curry _ := rfl
  apply := rfl
  primitive _ := rfl

theorem bundle_congr {Prim : Ty → Ty → Type} {A : Ty → Type}
    (M : STLCNaturality.Model FunctionCategory.ops Prim A) :
    STLCNaturality.ModelCongr (equality _) (bundle M) where
  pair := by intros; subst_vars; rfl
  copair := by intros; subst_vars; rfl
  curry := by intros; subst_vars; rfl

namespace Lift
open FunctionCategory

/-- A non-strict interpretation: a lifted sum/product/function is a different
object from the sum/product/function of lifted objects. -/
def map : RawMap ops.{0} ops.{0} where
  obj a := ULift a
  map f x := ⟨f x.down⟩

theorem map_laws : MapLaws map (equality _) (equality _) where
  congr := by intros; subst_vars; rfl
  ident := rfl
  comp _ _ := rfl

def unitComparison : TerminalMap map terminal terminal where
  hom _ := PUnit.unit
  inv _ := ⟨PUnit.unit⟩

def productComparison : ProductMap map products products := fun _ _ => {
  hom := fun p => (⟨p.down.1⟩, ⟨p.down.2⟩)
  inv := fun p => ⟨(p.1.down, p.2.down)⟩ }

def sumComparison : CoproductMap map coproducts coproducts := fun _ _ => {
  hom := fun p => match p.down with | .inl a => .inl ⟨a⟩ | .inr b => .inr ⟨b⟩
  inv := fun p => ⟨match p with | .inl a => .inl a.down | .inr b => .inr b.down⟩ }

def closedComparison : ClosedMap map closed closed := fun _ _ => {
  hom := fun f x => ⟨f.down x.down⟩
  inv := fun f => ⟨fun x => (f ⟨x⟩).down⟩ }

theorem unit_inverse : ComparisonLaws (equality _) unitComparison where
  hom_inv := rfl
  inv_hom := rfl

theorem product_inverse (a b : Type) : ComparisonLaws (equality _) (productComparison a b) where
  hom_inv := rfl
  inv_hom := rfl

theorem sum_inverse (a b : Type) : ComparisonLaws (equality _) (sumComparison a b) where
  hom_inv := by funext p; cases p <;> rfl
  inv_hom := by funext p; rcases p with ⟨a | b⟩ <;> rfl

theorem closed_inverse (a b : Type) : ComparisonLaws (equality _) (closedComparison a b) where
  hom_inv := rfl
  inv_hom := rfl

theorem terminal_preserves : TerminalMapLaws (equality _) unitComparison where
  terminal := rfl

theorem products_preserve : ProductMapLaws (equality _) productComparison where
  fst := rfl
  snd := rfl
  pair _ _ := rfl

theorem sums_preserve : CoproductMapLaws (equality _) sumComparison where
  inl := rfl
  inr := rfl
  copair f g := by funext p; rcases p with ⟨a | b⟩ <;> rfl

theorem closed_preserves : ClosedMapLaws (equality _) productComparison closedComparison where
  curry _ := rfl
  evaluation := rfl

theorem distribution_preserves : DistributionMapLaws (equality _) productComparison sumComparison
    distribution distribution where
  distribute {a b c} := by funext p; rcases p with ⟨a, b | c⟩ <;> rfl

inductive Primitive : Ty → Ty → Type where
  | increment : Primitive .base .base

abbrev object := STLCNaturality.objects terminal products coproducts closed Nat

def primitive : {a b : Ty} → Primitive a b → ops.Hom (object a) (object b)
  | _, _, .increment => fun n => Nat.add n 1

abbrev source := STLCNaturality.structured terminal products coproducts distribution closed Nat primitive
abbrev image := STLCNaturality.image map terminal products coproducts closed
  terminal products coproducts distribution closed unitComparison productComparison sumComparison closedComparison
  Nat (fun p => map.map (primitive p))

theorem preserves : STLCNaturality.Preserves map (equality _) source image :=
  STLCNaturality.image_preserves distribution terminal_preserves products_preserve sums_preserve
    distribution_preserves closed_preserves Nat primitive _ (fun _ => rfl)

theorem image_congr : STLCNaturality.ModelCongr (equality _) image :=
  STLCNaturality.image_congr (equalityCongr _) productCongr coproductCongr closedCongr Nat _

/-- All full-source terms, with explicit non-strict optional comparison obligations. -/
theorem naturality (t : Term Primitive Γ a) :
    map.map (STLCNaturality.compile source t) = STLCNaturality.compile image t :=
  STLCNaturality.structured_naturality distribution map_laws (equalityCongr _)
    productCongr coproductCongr closedCongr terminal_preserves products_preserve sums_preserve
    distribution_preserves closed_preserves Nat primitive _ (fun _ => rfl) t

/-- Composition of the non-strict lift with Mathlib's function adapter needs
no new induction over terms. -/
theorem composed_naturality (t : Term Primitive Γ a) :
    FunctionCategory.toTypes.map (map.map (STLCNaturality.compile source t)) =
      STLCNaturality.compile (bundle image) t :=
  STLCNaturality.naturality_comp map_laws FunctionCategory.toTypes_laws
    (equalityCongr _) (bundle_congr image) preserves (bundle_preserves image) t

/-- A lambda captures the older variable and uses a local primitive. -/
def capture : Term Primitive [.base] (.arr .base .base) :=
  .lam (.prim .increment (.var (.there .here)))

def applied : Term Primitive [.base] .base := .app capture (.prim .increment (.var .here))

example : STLCNaturality.compile image applied ⟨(PUnit.unit, (7 : Nat))⟩ = ULift.up (8 : Nat) := by
  rw [← naturality]; rfl

def capturedCase : Term Primitive [.base, .sum .base .base] .base :=
  .caseE (.var (.there .here)) (.prim .increment (.var .here)) (.var (.there .here))

example : STLCNaturality.compile image capturedCase ⟨((PUnit.unit, Sum.inl (5 : Nat)), (99 : Nat))⟩ = ULift.up (6 : Nat) := by
  rw [← naturality]; rfl
example : STLCNaturality.compile image capturedCase ⟨((PUnit.unit, Sum.inr (5 : Nat)), (99 : Nat))⟩ = ULift.up (99 : Nat) := by
  rw [← naturality]; rfl
example : (STLCNaturality.compile (bundle image) applied).hom ⟨(PUnit.unit, (7 : Nat))⟩ = ULift.up (8 : Nat) := by
  rw [← composed_naturality]; rfl
end Lift

namespace Exact
open SquareCompiler

/-- A captured environment is carried in the existing enriched FunctionRep. -/
def capture : Term Prim [.base] (.arr .base .base) :=
  .lam (.prim .increment (.var (.there .here)))
def applied : Term Prim [.base] .base := .app capture (.prim .increment (.var .here))

theorem captured_lambda (n x : Nat) (tag inputTag : Bool) :
    taggedNat.decode (((STLCNaturality.compile (STLCExact.model primitives) capture).left
      ((), (n, tag))).val.1 (x, inputTag)) = n + 1 :=
  STLCExact.compile_apply_commutes primitives capture ((), (n, tag)) (x, inputTag)

theorem captured_application (n : Nat) (tag : Bool) :
    taggedNat.decode ((STLCNaturality.compile (STLCExact.model primitives) applied).left ((), (n, tag))) = n + 1 :=
  STLCExact.compile_commutes primitives applied ((), (n, tag))

theorem left_branch (n outer : Nat) (tag outerTag : Bool) :
    taggedNat.decode ((STLCNaturality.compile (STLCExact.model primitives) branchWithCapture).left
      (((), Sum.inl (n, tag)), (outer, outerTag))) = n + 1 :=
  STLCExact.compile_commutes primitives branchWithCapture (((), Sum.inl (n, tag)), (outer, outerTag))

theorem right_branch (n outer : Nat) (tag outerTag : Bool) :
    taggedNat.decode ((STLCNaturality.compile (STLCExact.model primitives) branchWithCapture).left
      (((), Sum.inr (n, tag)), (outer, outerTag))) = outer :=
  STLCExact.compile_commutes primitives branchWithCapture (((), Sum.inr (n, tag)), (outer, outerTag))
end Exact
end Examples.FullSourceNaturality
