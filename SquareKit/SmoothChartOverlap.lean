import SquareKit.SmoothOpenPullback
import SquareKit.SmoothManifoldRefinement

/-! Represented intersections and composition domains derived from ordinary manifold charts. -/
noncomputable section
open CategoryTheory
namespace SquareKit.EuclideanOpen
open SmoothAlgebra
theorem restrictCodomain_inclusion {U V : Domain} (f : U ⟶ V) (q : freeAlgebra V.dimension)
   (h : ∀ x, q.val ((show Map U V from f) x).val ≠ 0) :
   restrictCodomain f q h ≫ subInclusion V q = f := OpenFunctions.Map.ext (fun _ => rfl)
end SquareKit.EuclideanOpen
namespace SquareKit.ManifoldRealization.ChartFamily
open EuclideanOpen SmoothAlgebra
open scoped Manifold ContDiff
variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Space n) M]
variable (A : ChartFamily n M)
def overlapDefining (i j : A.Index) : freeAlgebra n :=
  coordinateDefining (e := A.chart i) (A.chart j) id continuous_id
abbrev pair (i j : A.Index) : Domain := subdomain (A.charts.domain i) (A.overlapDefining i j)
abbrev left (i j : A.Index) : A.pair i j ⟶ A.charts.domain i := subInclusion _ _
def right (i j : A.Index) : A.pair i j ⟶ A.charts.domain j :=
  coordinateMap (A.chart j) id (A.smooth i) (A.smooth j) contMDiff_id
theorem agreement (i j : A.Index) (x : Points (A.pair i j)) :
    A.charts.coordinate i ((show Map _ _ from A.left i j) x) =
      A.charts.coordinate j ((show Map _ _ from A.right i j) x) :=
  coordinateMap_agreement (A.chart j) id (A.smooth i) (A.smooth j) contMDiff_id x
def relation (i j : A.Index) : A.charts.Relation :=
  ⟨i,j,A.pair i j,A.left i j,A.right i j,A.agreement i j⟩
def factor (r : A.charts.Relation) : r.domain ⟶ A.pair r.first r.second :=
  restrictCodomain r.left (A.overlapDefining r.first r.second) (by
    intro x
    apply (coordinateDefining_iff (A.chart r.second) id continuous_id _).mpr
    refine ⟨(chartDomain_locus (A.chart r.first)) ▸ ((show Map _ _ from r.left) x).property, ?_⟩
    change A.charts.coordinate r.first ((show Map _ _ from r.left) x) ∈ _
    rw [r.agreement]
    exact chartPoint_source (A.chart r.second) _)
theorem factor_left (r : A.charts.Relation) : A.factor r ≫ A.left r.first r.second = r.left :=
  restrictCodomain_inclusion _ _ _
theorem factor_right (r : A.charts.Relation) : A.factor r ≫ A.right r.first r.second = r.right := by
  apply OpenFunctions.Map.ext
  intro x
  apply (chartPoint_openEmbedding (A.chart r.second)).injective
  exact (A.agreement r.first r.second ((show Map _ _ from A.factor r) x)).symm.trans (r.agreement x)
end SquareKit.ManifoldRealization.ChartFamily
namespace SquareKit.ManifoldRealization.ChartFamily
open EuclideanOpen SmoothAlgebra
open scoped Manifold ContDiff
variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Space n) M]
variable (A : ChartFamily n M)
def diagonal (i : A.Index) : A.charts.domain i ⟶ A.pair i i :=
  A.factor ⟨i,i,_,𝟙 _,𝟙 _,fun _ => rfl⟩
def reverse (i j : A.Index) : A.pair i j ⟶ A.pair j i :=
  A.factor ⟨j,i,_,A.right i j,A.left i j,fun x => (A.agreement i j x).symm⟩
abbrev composable (i j k : A.Index) : Domain :=
  subdomain (A.pair i j) (inverseDefining (A.right i j) (A.overlapDefining j k))
abbrev composeFirst (i j k : A.Index) : A.composable i j k ⟶ A.pair i j := subInclusion _ _
abbrev composeSecond (i j k : A.Index) : A.composable i j k ⟶ A.pair j k :=
  inverseRestriction (A.right i j) (A.overlapDefining j k)
def compositeRelation (i j k : A.Index) : A.charts.Relation where
  first := i
  second := k
  domain := A.composable i j k
  left := A.composeFirst i j k ≫ A.left i j
  right := A.composeSecond i j k ≫ A.right j k
  agreement x := (A.agreement i j ((show Map _ _ from A.composeFirst i j k) x)).trans
    (A.agreement j k ((show Map _ _ from A.composeSecond i j k) x))
def compose (i j k : A.Index) : A.composable i j k ⟶ A.pair i k :=
  A.factor (A.compositeRelation i j k)
end SquareKit.ManifoldRealization.ChartFamily
