import SquareKit.CommaExact
import Mathlib.CategoryTheory.Comma.Arrow

/-! Exact function squares and Mathlib's arrow category have the same data.
Mathlib bundles its function arrows, so this bridge explicitly wraps and unwraps
them. Both raw arrows survive; no quotient or inverse decoder is required. -/

namespace SquareKit.Comma.Exact

open CategoryTheory
universe u

def toArrow (a : Object.{u}) : CategoryTheory.Arrow (Type u) :=
  CategoryTheory.Arrow.mk (TypeCat.ofHom a.connector)

def fromArrow (a : CategoryTheory.Arrow (Type u)) : Object.{u} :=
  ⟨a.left, a.right, fun x => a.hom x⟩

@[simp] theorem fromArrow_toArrow (a : Object.{u}) : fromArrow (toArrow a) = a := rfl
@[simp] theorem toArrow_fromArrow (a : CategoryTheory.Arrow (Type u)) :
    toArrow (fromArrow a) = a := rfl

def homToArrow {a b : Object.{u}} (f : Arrow a b) : toArrow a ⟶ toArrow b :=
  CategoryTheory.Arrow.homMk (TypeCat.ofHom f.left) (TypeCat.ofHom f.right)
    (by ext x; exact congrFun f.commutes x)

def homFromArrow {a b : CategoryTheory.Arrow (Type u)} (f : a ⟶ b) :
    Arrow (fromArrow a) (fromArrow b) :=
  ⟨(fun x => f.left x), (fun x => f.right x), funext (fun x => congrArg (fun k => k x) f.w)⟩

@[simp] theorem homFromArrow_toArrow {a b : Object.{u}} (f : Arrow a b) :
    homFromArrow (homToArrow f) = f := rfl

@[simp] theorem homToArrow_fromArrow {a b : CategoryTheory.Arrow (Type u)} (f : a ⟶ b) :
    homToArrow (homFromArrow f) = f := rfl

@[simp] theorem homToArrow_ident (a : Object.{u}) :
    homToArrow (categoryOps.ident (a := a)) = 𝟙 (toArrow a) := rfl

@[simp] theorem homToArrow_comp {a b c : Object.{u}} (g : Arrow b c) (f : Arrow a b) :
    homToArrow (categoryOps.comp g f) = homToArrow f ≫ homToArrow g := rfl

/-- A composable interpretation of the raw exact category, with laws below. -/
def arrowMap : RawMap categoryOps.{u} (ofCategory (CategoryTheory.Arrow (Type u))) :=
  ⟨toArrow, homToArrow⟩

theorem arrowMap_laws : MapLaws arrowMap.{u} (equality categoryOps) (equality _) where
  congr := by intros; subst_vars; rfl
  ident := rfl
  comp _ _ := rfl

end SquareKit.Comma.Exact
