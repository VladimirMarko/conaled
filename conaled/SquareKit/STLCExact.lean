import SquareKit.STLCNaturality
import SquareKit.CommaOptionalExact
import SquareCompiler

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SquareKit.STLCExact
open CategoricalCompiler
open Comma.Exact
variable {base : Squares.Rep.{0}} {Prim : Ty → Ty → Type}
variable {meaning : {a b : Ty} → Prim a b → Val base.S a → Val base.S b}
variable (P : SquareCompiler.PrimitiveImpl base Prim meaning)

/-- The legacy target enters the shared exact comma presentation with both arrows. -/
def inclusion : RawMap (STLCCategory.ops (SquareCompiler.target base P)) categoryOps where
  obj a := ofRep (SquareCompiler.objectInterp base a)
  map f := ofSquare f

theorem inclusion_laws : MapLaws (inclusion P) (equality _) (equality _) where
  congr := by intros; subst_vars; rfl
  ident := rfl
  comp _ _ := rfl

/-- Existing carriers, with optional operations supplied by the shared square API. -/
def model : STLCNaturality.Model categoryOps Prim (inclusion P).obj where
  terminal := ofSquare ⟨fun _ => (), fun _ => (), fun _ => rfl⟩
  fst {a b} := products.fst (a := (inclusion P).obj a) (b := (inclusion P).obj b)
  snd {a b} := products.snd (a := (inclusion P).obj a) (b := (inclusion P).obj b)
  pair {a b c} := products.pair (a := (inclusion P).obj a) (b := (inclusion P).obj b) (c := (inclusion P).obj c)
  inl {a b} := coproducts.inl (a := (inclusion P).obj a) (b := (inclusion P).obj b)
  inr {a b} := coproducts.inr (a := (inclusion P).obj a) (b := (inclusion P).obj b)
  copair {a b c} := coproducts.copair (a := (inclusion P).obj a) (b := (inclusion P).obj b) (c := (inclusion P).obj c)
  dist {a b c} := distribution.distribute (a := (inclusion P).obj a) (b := (inclusion P).obj b) (c := (inclusion P).obj c)
  curry {x a b} := closed.curry (x := (inclusion P).obj x) (a := (inclusion P).obj a) (b := (inclusion P).obj b)
  apply {a b} := closed.evaluation (a := (inclusion P).obj a) (b := (inclusion P).obj b)
  primitive p := ofSquare (SquareCompiler.primitiveSquare P p)

theorem model_congr : STLCNaturality.ModelCongr (equality _) (model P) where
  pair := by intros; subst_vars; rfl
  copair := by intros; subst_vars; rfl
  curry := by intros; subst_vars; rfl

theorem preserves : STLCNaturality.Preserves (inclusion P) (equality _)
    (STLCNaturality.ofTarget (SquareCompiler.target base P)) (model P) where
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

/-- Every legacy exact compiled square is recovered through shared naturality. -/
theorem compile_comparison (t : Term Prim Γ a) :
    ofSquare (compile (SquareCompiler.target base P) t) = STLCNaturality.compile (model P) t := by
  have h := STLCNaturality.naturality (inclusion_laws P) (equalityCongr _)
    (model_congr P) (preserves P) t
  change ofSquare (STLCNaturality.compile (STLCNaturality.ofTarget (SquareCompiler.target base P)) t) = _ at h
  rw [STLCNaturality.compile_ofTarget] at h
  exact h

/-- Semantic recovery uses the shared full-source theorem, then the comparison. -/
theorem compile_spec (t : Term Prim Γ a) (ρ : Val base.S (context Γ)) :
    (STLCNaturality.compile (model P) t).right ρ = eval meaning t ρ := by
  rw [← compile_comparison]
  exact STLCNaturality.compile_sound (SquareCompiler.target base P) (SquareCompiler.sound base P) t ρ

theorem compile_commutes (t : Term Prim Γ a) (ρ : (SquareCompiler.objectInterp base (context Γ)).R) :
    (SquareCompiler.objectInterp base a).decode ((STLCNaturality.compile (model P) t).left ρ) =
      eval meaning t ((SquareCompiler.objectInterp base (context Γ)).decode ρ) :=
  (congrFun (STLCNaturality.compile (model P) t).commutes ρ).trans (compile_spec P t _)
/-- Application retains the represented function's specification and uses its
compatibility proof; neither function nor witness erasure is assumed. -/
theorem compile_apply_commutes (t : Term Prim Γ (.arr a b))
    (ρ : (SquareCompiler.objectInterp base (context Γ)).R)
    (x : (SquareCompiler.objectInterp base a).R) :
    (SquareCompiler.objectInterp base b).decode
      (((STLCNaturality.compile (model P) t).left ρ).val.1 x) =
      eval meaning t ((SquareCompiler.objectInterp base (context Γ)).decode ρ)
        ((SquareCompiler.objectInterp base a).decode x) :=
  (((STLCNaturality.compile (model P) t).left ρ).property x).trans
    (congrFun (compile_commutes P t ρ) ((SquareCompiler.objectInterp base a).decode x))
end SquareKit.STLCExact
