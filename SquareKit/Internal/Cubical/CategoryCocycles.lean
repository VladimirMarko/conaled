import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.Data.Int.Basic
import Lean.Elab.Tactic.Omega

/-! Integer cochains in degrees zero through three on a category nerve.
These low-degree formulas support the explicit two-cocycle cubical candidate. -/
namespace SquareKit.Cubical.CategoryCocycles
open CategoryTheory
universe u v u' v'
variable (C : Type u) [Category.{v} C]
abbrev Cochain0 := C → ℤ
abbrev Cochain1 := ∀ {X Y : C}, (X ⟶ Y) → ℤ
abbrev Cochain2 := ∀ {X Y Z : C}, (X ⟶ Y) → (Y ⟶ Z) → ℤ
abbrev Cochain3 := ∀ {W X Y Z : C}, (W ⟶ X) → (X ⟶ Y) → (Y ⟶ Z) → ℤ
variable {C}
def δ0 (a : Cochain0 C) : Cochain1 C := fun {X Y} _ => a Y - a X
def δ1 (a : Cochain1 C) : Cochain2 C := fun f g => a g - a (f ≫ g) + a f
def δ2 (a : Cochain2 C) : Cochain3 C := fun f g h =>
  a g h - a (f ≫ g) h + a f (g ≫ h) - a f g

theorem δ1_δ0 (a : Cochain0 C) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    δ1 (δ0 a) f g = 0 := by simp only [δ1,δ0]; omega

theorem δ2_δ1 (a : Cochain1 C) {W X Y Z : C}
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) : δ2 (δ1 a) f g h = 0 := by
  simp only [δ2,δ1,Category.assoc]
  omega

structure Cocycle2 (C : Type u) [Category.{v} C] where
  cochain : Cochain2 C
  closed : ∀ {W X Y Z : C} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),
    δ2 cochain f g h = 0

@[ext] theorem Cocycle2.ext {a b : Cocycle2 C} (h : @a.cochain = @b.cochain) : a = b := by
  cases a; cases b; cases h; rfl

def coboundary (a : Cochain1 C) : Cocycle2 C where
  cochain := δ1 a
  closed f g h := δ2_δ1 a f g h

variable {D : Type u'} [Category.{v'} D]
def Cocycle2.pullback (z : Cocycle2 D) (F : C ⥤ D) : Cocycle2 C where
  cochain f g := z.cochain (F.map f) (F.map g)
  closed f g h := by simpa [δ2,F.map_comp] using z.closed (F.map f) (F.map g) (F.map h)

/-- The degree-one prism associated to a natural transformation. -/
def prism (z : Cocycle2 D) {F G : C ⥤ D} (η : F ⟶ G) : Cochain1 C :=
  fun {X Y} f => z.cochain (η.app X) (G.map f) - z.cochain (F.map f) (η.app Y)

/-- A categorical homotopy gives the actual cochain difference of its endpoints. -/
theorem prism_boundary (z : Cocycle2 D) {F G : C ⥤ D} (η : F ⟶ G)
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    δ1 (prism z η) f g = (z.pullback G).cochain f g - (z.pullback F).cochain f g := by
  have h₁ := z.closed (F.map f) (F.map g) (η.app Z)
  have h₂ := z.closed (F.map f) (η.app Y) (G.map g)
  have h₃ := z.closed (η.app X) (G.map f) (G.map g)
  simp only [δ2] at h₁ h₂ h₃
  rw [η.naturality g] at h₁
  rw [η.naturality f] at h₂
  simp only [δ1,prism,Cocycle2.pullback,Functor.map_comp]
  omega

end SquareKit.Cubical.CategoryCocycles
