import SquareKit.SmoothChartOverlapRefinement

/-! Experimental one-domain atlases and genuine ordinary covering atlases. -/
noncomputable section
open CategoryTheory SquareKit.SmoothAlgebra
namespace SquareKit.EuclideanOpen

theorem subInclusion_openEmbedding (U : Domain) (g : Free U.dimension) :
    Topology.IsOpenEmbedding (show Map _ _ from subInclusion U g) := by
  apply Topology.IsOpenEmbedding.of_comp _ (domain_open U).isOpenEmbedding_subtypeVal
  exact (domain_open (subdomain U g)).isOpenEmbedding_subtypeVal

abbrev singleAtlas (U : Domain) : Atlas (Points U) where
  Index := Unit
  domain _ := U
  coordinate _ := id
  openEmbedding _ := Topology.IsOpenEmbedding.id
  covers x := ⟨(),x,rfl⟩
  transition _ _ x _ _ := ⟨1, by simp, subInclusion U 1, fun _ => rfl⟩

namespace Charts

def singleDesc (U : Domain) : (singleAtlas U).toCharts.realization ⟶ embedding.obj U :=
  (singleAtlas U).toCharts.descend (fun _ : Unit => 𝟙 (embedding.obj U))
    (fun r => by
      have he : r.left = r.right := OpenFunctions.Map.ext r.agreement
      change embedding.map r.left ≫ 𝟙 (embedding.obj U) = embedding.map r.right ≫ 𝟙 (embedding.obj U)
      rw [he])

@[reassoc] theorem singleDesc_chart (U : Domain) (i : Unit) :
    (singleAtlas U).toCharts.chart i ≫ singleDesc U = 𝟙 (embedding.obj U) :=
  (singleAtlas U).toCharts.chart_descend (fun _ : Unit => 𝟙 (embedding.obj U)) _ i

def singleIso (U : Domain) : (singleAtlas U).toCharts.realization ≅ embedding.obj U where
  hom := singleDesc U
  inv := (singleAtlas U).toCharts.chart ()
  hom_inv_id := by
    apply Charts.hom_ext
    intro i
    cases i
    rw [← Category.assoc, singleDesc_chart, Category.id_comp, Category.comp_id]
  inv_hom_id := singleDesc_chart U ()

@[reassoc (attr := simp)] theorem single_chart (U : Domain) :
    (singleAtlas U).toCharts.chart () ≫ (singleIso U).hom = 𝟙 (embedding.obj U) :=
  singleDesc_chart U ()
end Charts

/-- Every ordinary principal cover gives an atlas on the covered open domain.
The transition is the actual overlap inclusion, not an ambient global map. -/
abbrev coverAtlas (U : Domain) {ι : Type} (g : ι → Free U.dimension) (hc : Covers U g) :
    Atlas (Points U) where
  Index := ι
  domain i := subdomain U (g i)
  coordinate i := (show Map _ _ from subInclusion U (g i))
  openEmbedding i := subInclusion_openEmbedding U (g i)
  covers x := by
    obtain ⟨i,hi⟩ := hc x
    exact ⟨i, localPoint U g x hi, rfl⟩
  transition i j x y he := by
    have hx : (g j).val x.val ≠ 0 := by
      have hv : x.val = y.val := congrArg Subtype.val he
      rw [hv]
      exact right_ne_zero_of_mul y.property
    exact ⟨g j, hx, overlapRight U (g i) (g j), fun _ => rfl⟩

def coverAtlasRefinement (U : Domain) {ι : Type} (g : ι → Free U.dimension) (hc : Covers U g) :
    Charts.Refinement (coverAtlas U g hc).toCharts (singleAtlas U).toCharts where
  map := ⟨id, fun _ => (), fun i => subInclusion U (g i), fun _ _ => rfl⟩
  point_identity := rfl
  Cover _ := ι
  defining _ := g
  covers _ := hc
  index _ i := i
  lift _ _ := 𝟙 _
  agreement _ _ _ := rfl

def coverAtlasIso (U : Domain) {ι : Type} (g : ι → Free U.dimension) (hc : Covers U g) :
    (coverAtlas U g hc).toCharts.realization ≅ embedding.obj U :=
  (coverAtlasRefinement U g hc).iso ≪≫ Charts.singleIso U

@[reassoc] theorem coverAtlas_chart (U : Domain) {ι : Type} (g : ι → Free U.dimension)
    (hc : Covers U g) (i : ι) :
    (coverAtlas U g hc).toCharts.chart i ≫ (coverAtlasIso U g hc).hom =
      embedding.map (subInclusion U (g i)) := by
  change _ ≫ ((coverAtlasRefinement U g hc).map.realize ≫ (Charts.singleIso U).hom) = _
  rw [← Category.assoc, Charts.Map.chart_realize, Category.assoc, Charts.single_chart,
    Category.comp_id]
  rfl

end SquareKit.EuclideanOpen
