import SquareKit.Internal.Cubical.CategoryCocycles
import SquareKit.Internal.Cubical.Presheaf
import Mathlib.CategoryTheory.Comma.Over.Basic

/-! Two-cocycles on the nerves of the actual De Morgan cube slices.
Reindexing retains arbitrary formal cube substitutions. Fibrancy is separate. -/
namespace SquareKit.Cubical.CategoryCocycles
open CategoryTheory

@[simp] theorem Cocycle2.pullback_id {C : Type*} [Category C] (z : Cocycle2 C) :
    z.pullback (𝟭 C) = z := by apply Cocycle2.ext; rfl

@[simp] theorem Cocycle2.pullback_comp {C D E : Type*} [Category C] [Category D] [Category E]
    (z : Cocycle2 E) (F : C ⥤ D) (G : D ⥤ E) :
    (z.pullback G).pullback F = z.pullback (F ⋙ G) := by apply Cocycle2.ext; rfl

def cocycles : Presheaf.Context where
  obj I := Cocycle2 (Over I.unop)
  map f := TypeCat.ofHom fun z => z.pullback (Over.map f.unop)
  map_id I := by
    apply ConcreteCategory.hom_ext
    intro z
    change z.pullback (Over.map (𝟙 I.unop)) = z
    rw [Over.mapId_eq,Cocycle2.pullback_id]
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro z
    change z.pullback (Over.map (g.unop ≫ f.unop)) =
      (z.pullback (Over.map f.unop)).pullback (Over.map g.unop)
    rw [Over.mapComp_eq,Cocycle2.pullback_comp]

end SquareKit.Cubical.CategoryCocycles
