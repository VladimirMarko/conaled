import SquareKit.SmoothManifoldFullFaithfulness
import Examples.MathlibManifoldRealization
import Examples.EuclideanOpenEmbedding
import Mathlib.Geometry.Manifold.ContMDiff.Constructions

/-! Consumers of manifold full faithfulness, including arbitrary arrows,
local target-chart splitting, nonextendable maps, and dimension boundaries. -/
noncomputable section
open CategoryTheory SquareKit SquareKit.ManifoldRealization
open scoped Manifold ContDiff
namespace Examples.ManifoldFullFaithfulness

abbrev TwoPoints := Space 0 ⊕ Space 0

/-- This Mathlib manifold cannot be covered by a single Euclidean chart. -/
theorem twoPoints_no_global_chart (e : OpenPartialHomeomorph TwoPoints (Space 0)) :
    e.source ≠ Set.univ := by
  intro he
  have h := e.injOn (x₁ := Sum.inl Fin.elim0) (x₂ := Sum.inr Fin.elim0)
    (he ▸ Set.mem_univ _) (he ▸ Set.mem_univ _) (Subsingleton.elim _ _)
  cases h

def tag : TwoPoints → Space 1 := Sum.elim (fun _ => 0) (fun _ => 1)

theorem tag_smooth : ContMDiff (Model 0) (Model 1) ∞ tag :=
  contMDiff_const.sumElim contMDiff_const

theorem recover_tag : reconstruct (map tag tag_smooth) = tag :=
  reconstruct_map tag tag_smooth

/-- All arrows are quantified, with a non-global-chart source and different
source and target dimensions. -/
theorem arbitrary_arrow (h : object 0 TwoPoints ⟶ object 1 (Space 1)) :
    ContMDiff (Model 0) (Model 1) ∞ (reconstruct h) ∧
      map (reconstruct h) (reconstruct_smooth h) = h :=
  ⟨reconstruct_smooth h, map_reconstruct h⟩

theorem distinguish_constants :
    map (n := 1) (m := 1) (fun _ : Space 1 => (0 : Space 1)) contMDiff_const ≠
      map (n := 1) (m := 1) (fun _ : Space 1 => (1 : Space 1)) contMDiff_const := by
  intro h
  have he := congrFun (congrFun (map_injective contMDiff_const contMDiff_const h) 0) 0
  exact zero_ne_one he

open MathlibManifoldRealization

/-- The existing target atlas cannot receive the entire global source chart;
the inverse still recovers its interpreted identity. -/
theorem recover_split_identity :
    (globalFamily 1).reconstruct splitFamily splitIdentity = id :=
  (globalFamily 1).reconstruct_interpret splitFamily id contMDiff_id

theorem arbitrary_split_arrow
    (h : (globalFamily 1).realization ⟶ splitFamily.realization) :
    (globalFamily 1).interpret splitFamily ((globalFamily 1).reconstruct splitFamily h)
      ((globalFamily 1).reconstruct_smooth splitFamily h) = h :=
  (globalFamily 1).interpret_reconstruct splitFamily h

/-- The reciprocal has no continuous ambient extension, proved in the reused
ordinary-open example. Reconstruction retains its actual open domain. -/
theorem recover_nonextendable_reciprocal :
    reconstruct
      (map (show ordinaryOpen EuclideanOpenEmbedding.punctured →
          ordinaryOpen (EuclideanOpen.full 1) from
          (show EuclideanOpen.Map _ _ from EuclideanOpenEmbedding.reciprocal).toFun)
        (openMap_contMDiff EuclideanOpenEmbedding.reciprocal)) =
      (show EuclideanOpen.Map _ _ from EuclideanOpenEmbedding.reciprocal).toFun :=
  reconstruct_map _ _

theorem arbitrary_principal_arrow (U V : EuclideanOpen.Domain)
    (h : object U.dimension (ordinaryOpen U) ⟶ object V.dimension (ordinaryOpen V)) :
    (ManifoldRealization.homEquiv).symm h = (principalHomEquiv U V).symm h := by
  rw [homEquiv_principal]

theorem atlas_inverse_agrees (h : object 1 (Space 1) ⟶ object 1 (Space 1)) :
    (globalFamily 1).reconstruct splitFamily
      ((atlasIso (globalFamily 1)).inv ≫ h ≫ (atlasIso splitFamily).hom) = reconstruct h :=
  reconstruct_atlas _ _ h

theorem reconstruct_after_tag (h : object 1 (Space 1) ⟶ object 1 (Space 1)) :
    reconstruct (map tag tag_smooth ≫ h) = reconstruct h ∘ tag := by
  rw [reconstruct_comp, reconstruct_map]

theorem empty_arrow (h : object 1 Empty ⟶ object 0 TwoPoints) :
    map (reconstruct h) (reconstruct_smooth h) = h := map_reconstruct h

theorem no_point_to_empty : IsEmpty (object 0 (Space 0) ⟶ object 1 Empty) :=
  ⟨fun h => (reconstruct h Fin.elim0).elim⟩

end Examples.ManifoldFullFaithfulness
