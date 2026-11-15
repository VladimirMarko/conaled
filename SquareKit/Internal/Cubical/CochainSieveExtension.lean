import SquareKit.Internal.Cubical.CategoryCocycles

/-! Extension by zero for partial degree-one cochains on a categorical sieve.
Its pullback law uses membership in the sieve, not membership of vertices. -/
namespace SquareKit.Cubical.CategoryCocycles
open CategoryTheory
universe u v u' v'
variable {C : Type u} [Category.{v} C]

structure SieveObjects (C : Type u) [Category.{v} C] where
  contains : C → Prop
  downward : ∀ {X Y : C}, (X ⟶ Y) → contains Y → contains X

abbrev PartialCochain1 (S : SieveObjects C) := ∀ {X Y : C}, (X ⟶ Y) → S.contains Y → ℤ

noncomputable def extendZero {S : SieveObjects C} (b : PartialCochain1 S) : Cochain1 C := by
  classical
  exact fun {X Y} f => if h : S.contains Y then b f h else 0

theorem extendZero_inside {S : SieveObjects C} (b : PartialCochain1 S)
    {X Y : C} (f : X ⟶ Y) (h : S.contains Y) : extendZero b f = b f h := by
  simp [extendZero,h]

theorem δ1_extendZero_inside {S : SieveObjects C} (b : PartialCochain1 S)
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : S.contains Z) :
    δ1 (extendZero b) f g = b g h - b (f ≫ g) h + b f (S.downward g h) := by
  simp only [δ1,extendZero_inside b g h,extendZero_inside b (f ≫ g) h,
    extendZero_inside b f (S.downward g h)]

variable {D : Type u'} [Category.{v'} D]
def SieveObjects.pullback (S : SieveObjects D) (F : C ⥤ D) : SieveObjects C where
  contains X := S.contains (F.obj X)
  downward f := S.downward (F.map f)

def PartialCochain1.pullback {S : SieveObjects D} (b : PartialCochain1 S)
    (F : C ⥤ D) : PartialCochain1 (S.pullback F) := fun f h => b (F.map f) h

theorem extendZero_pullback {S : SieveObjects D} (b : PartialCochain1 S)
    (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) :
    extendZero (b.pullback F) f = extendZero b (F.map f) := rfl

end SquareKit.Cubical.CategoryCocycles
