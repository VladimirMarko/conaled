import SquareKit.Internal.Cubical.CubeProductFunctor
import SquareKit.Internal.Cubical.CocyclePresheaf

/-! Freshening a slice cube supplies the two graph maps used by the prism. -/
namespace SquareKit.Cubical.CategoryCocycles
open CategoryTheory Cube

/-- Preserve the base coordinates and replace the last coordinate by a fresh one. -/
def freshen (N : Cube) : Over (extend N) ⥤ Over (extend N) where
  obj X := Over.mk (pair (drop X.left ≫ X.hom ≫ drop N) (fresh X.left))
  map f := Over.homMk (extensionMap f.left) (by
    dsimp
    apply pair_ext
    · simp only [Category.assoc, pair_drop_cat]
      rw [← Category.assoc, extensionMap_drop]
      simp only [Category.assoc]
      rw [← Category.assoc f.left, Over.w f]
    · simp [Category.assoc])
  map_id X := by ext; exact extensionMap_id X.left
  map_comp f g := by ext; exact extensionMap_comp f.left g.left

/-- The original coordinate is a graph specialization of the fresh one. -/
def graphToFresh (N : Cube) : 𝟭 (Over (extend N)) ⟶ freshen N where
  app X := Over.homMk (graph (X.hom ≫ fresh N)) (by
    change graph (X.hom ≫ fresh N) ≫ pair (drop X.left ≫ X.hom ≫ drop N) (fresh X.left) = X.hom
    apply pair_ext
    · simp only [Category.assoc,pair_drop_cat]
      rw [← Category.assoc,graph_drop,Category.id_comp]
    · simp [Category.assoc])
  naturality {X Y} f := by
    apply Over.OverMorphism.ext
    change f.left ≫ graph (_ ≫ fresh N) = graph (_ ≫ fresh N) ≫ extensionMap f.left
    rw [← graph_naturality]
    congr 1
    rw [← Category.assoc,Over.w f]

end SquareKit.Cubical.CategoryCocycles
