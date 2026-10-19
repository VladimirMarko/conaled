import SquareKit.SmoothManifoldInterpretation
import SquareKit.SmoothAtlasSubdivision

/-! Experimental actual common refinements of manifold-generated atlases. -/
noncomputable section
open CategoryTheory
open scoped Manifold ContDiff
namespace SquareKit.EuclideanOpen
open SmoothAlgebra

def restrictCodomain {U V : Domain} (f : U ⟶ V) (q : Free V.dimension)
    (h : ∀ x, q.val ((show Map _ _ from f) x).val ≠ 0) : U ⟶ subdomain V q where
  toFun x := ⟨((show Map _ _ from f) x).val,mul_ne_zero ((show Map _ _ from f) x).property (h x)⟩
  smooth := (show Map _ _ from f).smooth

end SquareKit.EuclideanOpen
namespace SquareKit.ManifoldRealization.ChartFamily
open EuclideanOpen
variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Space n) M]
    (A B : ChartFamily n M)

abbrev commonAtlas : Atlas M :=
  A.atlas.subdivision (fun _ => B.Index)
    (fun i j => coordinateDefining (e := A.chart i) (B.chart j) id continuous_id)
    (A.localMap B id contMDiff_id).covers

def commonLeft : Charts.Refinement (A.commonAtlas B).toCharts A.charts :=
  A.charts.subdivisionRefinement _ _ (A.localMap B id contMDiff_id).covers

def commonMap : Charts.Map (A.commonAtlas B).toCharts B.charts where
  point := id
  index p := p.2
  coordinate p := coordinateMap (B.chart p.2) id (A.smooth p.1) (B.smooth p.2) contMDiff_id
  agreement p := coordinateMap_agreement (B.chart p.2) id (A.smooth p.1) (B.smooth p.2) contMDiff_id

def commonLift (j : B.Index) (i : A.Index) :
    subdomain (chartDomain (B.chart j))
      (coordinateDefining (e := B.chart j) (A.chart i) id continuous_id) ⟶
      (A.commonAtlas B).domain ⟨i,j⟩ :=
  restrictCodomain (coordinateMap (A.chart i) id (B.smooth j) (A.smooth i) contMDiff_id)
    (coordinateDefining (e := A.chart i) (B.chart j) id continuous_id) (fun x => by
      apply (coordinateDefining_iff (B.chart j) id continuous_id _).mpr
      refine ⟨?_,?_⟩
      · exact (chartDomain_locus (A.chart i)) ▸
          ((show EuclideanOpen.Map _ _ from coordinateMap (A.chart i) id
            (B.smooth j) (A.smooth i) contMDiff_id) x).property
      · have h := coordinateMap_agreement (A.chart i) id (B.smooth j) (A.smooth i) contMDiff_id x
        change chartPoint (A.chart i) _ ∈ (B.chart j).source
        rw [← h]
        exact chartPoint_source (B.chart j) ((show EuclideanOpen.Map _ _ from subInclusion _ _) x))

def commonRight : Charts.Refinement (A.commonAtlas B).toCharts B.charts where
  map := A.commonMap B
  point_identity := rfl
  Cover _ := A.Index
  defining j i := coordinateDefining (e := B.chart j) (A.chart i) id continuous_id
  covers := (B.localMap A id contMDiff_id).covers
  index j i := ⟨i,j⟩
  lift j i := A.commonLift B j i
  agreement j i := coordinateMap_agreement (A.chart i) id (B.smooth j) (A.smooth i) contMDiff_id

/-- The map induced by an arbitrary smooth identity chart comparison agrees
with the actual ordinary common-refinement isomorphism. -/
theorem comparison_common : A.comparison B =
    Charts.commonRefinementIso (A.commonLeft B) (A.commonRight B) := by
  apply Iso.ext
  apply (cancel_epi (A.commonLeft B).iso.hom).mp
  change (A.commonLeft B).map.realize ≫ (A.comparison B).hom =
    (A.commonLeft B).map.realize ≫ _
  rw [Charts.commonRefinement_commutes]
  apply (A.commonAtlas B).toCharts.hom_ext
  intro p
  rw [← Category.assoc,Charts.Map.chart_realize,Category.assoc,Charts.Map.chart_realize]
  exact A.interpret_chart B id contMDiff_id p.1 p.2

end SquareKit.ManifoldRealization.ChartFamily
