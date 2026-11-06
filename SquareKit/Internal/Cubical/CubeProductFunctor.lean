import SquareKit.Internal.Cubical.CubeProducts
import Mathlib.CategoryTheory.Functor.Category

/-! Functorial fresh dimensions and their graph specializations. -/
namespace SquareKit.Cubical.Cube
open CategoryTheory

theorem pair_ext {I J : Cube} {f g : I ⟶ extend J}
    (hd : f ≫ drop J = g ≫ drop J) (hr : f ≫ fresh J = g ≫ fresh J) : f = g := by
  have reconstruct (h : I ⟶ extend J) : pair (h ≫ drop J) (h ≫ fresh J) = h :=
    (comp_pair h (drop J) (fresh J)).symm.trans (by rw [pair_eta]; exact Category.comp_id h)
  rw [← reconstruct f,← reconstruct g,hd,hr]

@[simp] theorem pair_drop_cat {I J : Cube} (f : I ⟶ J) (r : I ⟶ (⟨1⟩ : Cube)) :
    pair f r ≫ drop J = f := pair_drop f r
@[simp] theorem pair_fresh_cat {I J : Cube} (f : I ⟶ J) (r : I ⟶ (⟨1⟩ : Cube)) :
    pair f r ≫ fresh J = r := pair_fresh f r

def extensionMap {I J : Cube} (f : I ⟶ J) : extend I ⟶ extend J :=
  pair (drop I ≫ f) (fresh I)
@[simp] theorem extensionMap_drop {I J : Cube} (f : I ⟶ J) :
    extensionMap f ≫ drop J = drop I ≫ f := pair_drop_cat _ _
@[simp] theorem extensionMap_fresh {I J : Cube} (f : I ⟶ J) :
    extensionMap f ≫ fresh J = fresh I := pair_fresh_cat _ _

@[simp] theorem extensionMap_id (I : Cube) : extensionMap (𝟙 I) = 𝟙 (extend I) := by
  apply pair_ext <;> simp
@[simp] theorem extensionMap_comp {I J K : Cube} (f : I ⟶ J) (g : J ⟶ K) :
    extensionMap (f ≫ g) = extensionMap f ≫ extensionMap g := by
  apply pair_ext <;> simp [Category.assoc,← Category.assoc (extensionMap f) (drop J) g]

def extension : Cube ⥤ Cube where
  obj := extend
  map := extensionMap
  map_id := extensionMap_id
  map_comp := extensionMap_comp

def graph {I : Cube} (r : I ⟶ (⟨1⟩ : Cube)) : I ⟶ extend I := pair (𝟙 I) r
@[simp] theorem graph_drop {I : Cube} (r : I ⟶ (⟨1⟩ : Cube)) : graph r ≫ drop I = 𝟙 I := pair_drop_cat _ _
@[simp] theorem graph_fresh {I : Cube} (r : I ⟶ (⟨1⟩ : Cube)) : graph r ≫ fresh I = r := pair_fresh_cat _ _

theorem graph_naturality {I J : Cube} (f : I ⟶ J) (r : J ⟶ (⟨1⟩ : Cube)) :
    graph (f ≫ r) ≫ extensionMap f = f ≫ graph r := by
  apply pair_ext <;> simp [Category.assoc,← Category.assoc (graph (f ≫ r)) (drop I) f]

end SquareKit.Cubical.Cube
