import SquareKit.SmoothManifoldModel
import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-! Interpret both maps and inverse laws of a smooth diffeomorphism. -/
noncomputable section
open CategoryTheory
open scoped Manifold ContDiff
namespace SquareKit.ManifoldRealization
variable {m n : ℕ} {M N : Type}
  [TopologicalSpace M] [ChartedSpace (Space m) M] [IsManifold (modelWithCorners m) ∞ M]
  [TopologicalSpace N] [ChartedSpace (Space n) N] [IsManifold (modelWithCorners n) ∞ N]

/-- Interpret both actual maps of a diffeomorphism. -/
def diffeomorphIso (e : Diffeomorph (modelWithCorners m) (modelWithCorners n) M N ∞) :
    object m M ≅ object n N where
  hom := map e e.contMDiff_toFun
  inv := map e.symm e.symm.contMDiff_toFun
  hom_inv_id := by
    rw [← map_comp]
    have h : (⇑e.symm ∘ ⇑e) = id := funext e.symm_apply_apply
    simpa only [h] using (map_id (n := m) (M := M))
  inv_hom_id := by
    rw [← map_comp]
    have h : (⇑e ∘ ⇑e.symm) = id := funext e.apply_symm_apply
    simpa only [h] using (map_id (n := n) (M := N))

end SquareKit.ManifoldRealization
