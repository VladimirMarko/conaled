import SquareKit.Internal.Cubical.CubeProducts

/-! Cartesian dimensions and their inclusion into De Morgan dimensions. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Cartesian
open CategoryTheory

inductive Dim (n : ℕ) where
  | endpoint (b : Bool)
  | var (i : Fin n)
  deriving DecidableEq

namespace Dim
variable {n m k : ℕ}

def subst (f : Fin n → Dim m) : Dim n → Dim m
  | .endpoint b => .endpoint b
  | .var i => f i

@[simp] theorem subst_var (r : Dim n) : subst var r = r := by cases r <;> rfl
@[simp] theorem subst_subst (f : Fin n → Dim m) (g : Fin m → Dim k) (r : Dim n) :
    subst g (subst f r) = subst (fun i => subst g (f i)) r := by cases r <;> rfl

def expr : Dim n → Expr (Fin n)
  | .endpoint false => .zero
  | .endpoint true => .one
  | .var i => .var i

@[simp] theorem expr_subst (f : Fin n → Dim m) (r : Dim n) :
    (subst f r).expr = Expr.subst (fun i => (f i).expr) r.expr := by
  cases r with
  | endpoint b => cases b <;> rfl
  | var i => rfl
end Dim

structure Cube where
  dimension : ℕ
  deriving DecidableEq

namespace Cube
abbrev Hom (I J : Cube) := Fin J.dimension → Dim I.dimension

def comp {I J K : Cube} (f : Hom I J) (g : Hom J K) : Hom I K :=
  fun i => Dim.subst f (g i)

instance : Category Cube where
  Hom := Hom
  id _ := Dim.var
  comp := comp
  id_comp _ := by funext i; exact Dim.subst_var _
  comp_id _ := rfl
  assoc _ _ _ := by funext i; exact (Dim.subst_subst _ _ _).symm

abbrev extend (I : Cube) : Cube := ⟨I.dimension + 1⟩
def drop (I : Cube) : Hom (extend I) I := fun i => .var i.succ
def fresh (I : Cube) : Hom (extend I) ⟨1⟩ := fun _ => .var 0
def pair {I J : Cube} (f : Hom I J) (r : Hom I ⟨1⟩) : Hom I (extend J) :=
  Fin.cases (r 0) f
def endpoint (I : Cube) (b : Bool) : Hom I ⟨1⟩ := fun _ => .endpoint b

@[simp] theorem pair_drop {I J : Cube} (f : Hom I J) (r : Hom I ⟨1⟩) :
    comp (pair f r) (drop J) = f := rfl
@[simp] theorem pair_fresh {I J : Cube} (f : Hom I J) (r : Hom I ⟨1⟩) :
    comp (pair f r) (fresh J) = r := by funext i; rw [Fin.eq_zero i]; rfl
@[simp] theorem pair_eta (I : Cube) : pair (drop I) (fresh I) = 𝟙 (extend I) := by
  funext i; cases i using Fin.cases <;> rfl
@[simp] theorem comp_endpoint {I J : Cube} (f : Hom I J) (b : Bool) :
    comp f (endpoint J b) = endpoint I b := rfl

theorem comp_pair {I J K : Cube} (f : Hom I J) (g : Hom J K) (r : Hom J ⟨1⟩) :
    comp f (pair g r) = pair (comp f g) (comp f r) := by
  funext i; cases i using Fin.cases <;> rfl
end Cube

/-- Constants and variables interpret as the same De Morgan expressions. -/
def inclusion : Cube ⥤ SquareKit.Cubical.Cube where
  obj I := ⟨I.dimension⟩
  map f := SquareKit.Cubical.Cube.ofRaw (fun i => (f i).expr)
  map_id _ := rfl
  map_comp f g := by
    apply Quotient.sound
    intro i
    change Expr.Conv (Dim.expr (Dim.subst f (g i))) _
    rw [Dim.expr_subst]
    exact .refl _

@[simp] theorem inclusion_drop (I : Cube) :
    inclusion.map (Cube.drop I) = SquareKit.Cubical.Cube.drop (inclusion.obj I) := rfl
@[simp] theorem inclusion_fresh (I : Cube) :
    inclusion.map (Cube.fresh I) = SquareKit.Cubical.Cube.fresh (inclusion.obj I) := rfl
@[simp] theorem inclusion_endpoint (I : Cube) (b : Bool) :
    inclusion.map (Cube.endpoint I b) = SquareKit.Cubical.Cube.endpoint (inclusion.obj I) b := by
  cases b <;> rfl
@[simp] theorem inclusion_pair {I J : Cube} (f : I ⟶ J) (r : I ⟶ ⟨1⟩) :
    inclusion.map (Cube.pair f r) =
      SquareKit.Cubical.Cube.pair (inclusion.map f) (inclusion.map r) := by
  apply Quotient.sound
  intro i
  cases i using Fin.cases <;> exact .refl _

end SquareKit.Cubical.Cartesian
