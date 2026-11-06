import SquareKit.Internal.Cubical.SliceFreshening

/-! The two graph specializations compare a slice cocycle with its cap. -/
namespace SquareKit.Cubical.CategoryCocycles
open CategoryTheory Cube

@[simp] theorem comp_endpoint_cat {I J : Cube} (f : I ⟶ J) (b : Bool) :
    f ≫ Cube.endpoint J b = Cube.endpoint I b := Cube.comp_endpoint f b

def capMap (N : Cube) (b : Bool) : extend N ⟶ extend N :=
  pair (drop N) (Cube.endpoint (extend N) b)

def cap (N : Cube) (b : Bool) : Over (extend N) ⥤ Over (extend N) :=
  Over.map (capMap N b)

def capToFresh (N : Cube) (b : Bool) : cap N b ⟶ freshen N where
  app X := Over.homMk (graph (Cube.endpoint X.left b)) (by
    change graph (Cube.endpoint X.left b) ≫
      pair (drop X.left ≫ X.hom ≫ drop N) (fresh X.left) = X.hom ≫ capMap N b
    apply pair_ext
    · simp only [Category.assoc,pair_drop_cat,capMap]
      rw [← Category.assoc,graph_drop,Category.id_comp]
    · simp [capMap,Category.assoc])
  naturality {X Y} f := by
    apply Over.OverMorphism.ext
    change f.left ≫ graph (Cube.endpoint Y.left b) =
      graph (Cube.endpoint X.left b) ≫ extensionMap f.left
    rw [← graph_naturality,comp_endpoint_cat]

/-- The difference of the two prisms is a primitive of the cap difference. -/
def capPrimitive {N : Cube} (b : Bool) (z : Cocycle2 (Over (extend N))) :
    Cochain1 (Over (extend N)) := fun f =>
  prism z (capToFresh N b) f - prism z (graphToFresh N) f

theorem capPrimitive_boundary {N : Cube} (b : Bool) (z : Cocycle2 (Over (extend N)))
    {X Y Z : Over (extend N)} (f : X ⟶ Y) (g : Y ⟶ Z) :
    δ1 (capPrimitive b z) f g = z.cochain f g - (z.pullback (cap N b)).cochain f g := by
  have h₁ := prism_boundary z (capToFresh N b) f g
  have h₂ := prism_boundary z (graphToFresh N) f g
  simp only [δ1,capPrimitive] at *
  dsimp [Cocycle2.pullback] at *
  omega

end SquareKit.Cubical.CategoryCocycles
