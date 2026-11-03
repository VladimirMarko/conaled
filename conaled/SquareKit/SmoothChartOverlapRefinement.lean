import SquareKit.SmoothChartSubdivision

/-! Experimental replacement of overlap tests by arbitrary ordinary principal
covers. Sheaf separatedness proves the comparison, not preservation of colimits. -/
noncomputable section
open CategoryTheory CategoryTheory.Limits SquareKit.SmoothAlgebra
namespace SquareKit.EuclideanOpen.Charts
variable {M : Type} (A : Charts M)
    (K : A.Relation → Type) (g : ∀ r, K r → Free r.domain.dimension)
    (hc : ∀ r, Covers r.domain (g r))

abbrev refinedShape : MultispanShape :=
  ⟨Σ r, K r, A.Index, fun p => p.1.first, fun p => p.1.second⟩

abbrev refinedDiagram : MultispanIndex (A.refinedShape K) (Sheaf SmoothOpenSite.topology (Type)) where
  left p := embedding.obj (subdomain p.1.domain (g p.1 p.2))
  right i := embedding.obj (A.domain i)
  fst p := embedding.map (subInclusion p.1.domain (g p.1 p.2) ≫ p.1.left)
  snd p := embedding.map (subInclusion p.1.domain (g p.1 p.2) ≫ p.1.right)

include hc in
theorem compatible_iff_refined {F : Sheaf SmoothOpenSite.topology (Type)}
    (a : ∀ i, embedding.obj (A.domain i) ⟶ F) :
    A.Compatible a ↔ ∀ r k,
      embedding.map (subInclusion r.domain (g r k) ≫ r.left) ≫ a r.first =
      embedding.map (subInclusion r.domain (g r k) ≫ r.right) ≫ a r.second := by
  constructor
  · intro h r k
    simpa only [Functor.map_comp, Category.assoc] using
      congrArg (fun f => embedding.map (subInclusion r.domain (g r k)) ≫ f) (h r)
  · intro h r
    apply cover_jointly_epic r.domain (g r) (hc r) F
    intro k
    simpa only [Functor.map_comp, Category.assoc] using h r k

abbrev refinedRealization : Sheaf SmoothOpenSite.topology (Type) :=
  multicoequalizer (A.refinedDiagram K g)

def overlapRefinementIso : A.refinedRealization K g ≅ A.realization where
  hom := Multicoequalizer.desc (A.refinedDiagram K g) A.realization A.chart
    (fun p => (A.compatible_iff_refined K g hc A.chart).mp A.chart_compatible p.1 p.2)
  inv := A.descend (Multicoequalizer.π (A.refinedDiagram K g))
    ((A.compatible_iff_refined K g hc _).mpr (fun r k =>
      Multicoequalizer.condition (A.refinedDiagram K g) ⟨r,k⟩))
  hom_inv_id := by
    apply Multicoequalizer.hom_ext (A.refinedDiagram K g)
    intro i
    rw [← Category.assoc, Multicoequalizer.π_desc, chart_descend, Category.comp_id]
  inv_hom_id := by
    apply A.hom_ext
    intro i
    rw [← Category.assoc, chart_descend, Multicoequalizer.π_desc, Category.comp_id]

theorem overlapRefinement_chart (i : A.Index) :
    Multicoequalizer.π (A.refinedDiagram K g) i ≫ (A.overlapRefinementIso K g hc).hom = A.chart i :=
  Multicoequalizer.π_desc (A.refinedDiagram K g) A.realization A.chart _ i

end SquareKit.EuclideanOpen.Charts
