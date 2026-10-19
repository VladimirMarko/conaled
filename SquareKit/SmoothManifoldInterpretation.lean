import SquareKit.SmoothManifoldCharts

/-! Experimental indexed interpretation of all Mathlib smooth maps between
finite-dimensional real boundaryless manifolds, for arbitrary smooth chart families. -/
noncomputable section
open CategoryTheory
open scoped Manifold ContDiff
namespace SquareKit.ManifoldRealization.ChartFamily
open EuclideanOpen
variable {n m p : ℕ} {M N P : Type}
    [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace P]
    [ChartedSpace (Space n) M] [ChartedSpace (Space m) N] [ChartedSpace (Space p) P]
    (A : ChartFamily n M) (B : ChartFamily m N) (C : ChartFamily p P)

abbrev realization : Sheaf SmoothOpenSite.topology (Type) := A.charts.realization

def interpret (f : M → N) (hf : ContMDiff (Model n) (Model m) ∞ f) : A.realization ⟶ B.realization :=
  (A.localMap B f hf).realize

/-- Every local coordinate choice gives the actual interpretation of the map. -/
theorem interpret_choice (f : M → N) (hf : ContMDiff (Model n) (Model m) ∞ f)
    (l : Charts.LocalMap A.charts B.charts f) : A.interpret B f hf = l.realize :=
  Charts.LocalMap.realize_eq _ l

@[reassoc] theorem interpret_chart (f : M → N) (hf : ContMDiff (Model n) (Model m) ∞ f)
    (i : A.Index) (j : B.Index) :
    embedding.map (subInclusion (chartDomain (A.chart i))
      (coordinateDefining (e := A.chart i) (B.chart j) f hf.continuous)) ≫
      A.charts.chart i ≫ A.interpret B f hf =
        embedding.map (coordinateMap (B.chart j) f (A.smooth i) (B.smooth j) hf) ≫ B.charts.chart j := by
  exact (A.localMap B f hf).test i j _ (subInclusion _ _) _
    (coordinateMap_agreement (B.chart j) f (A.smooth i) (B.smooth j) hf)

theorem interpret_id : A.interpret A id contMDiff_id = 𝟙 A.realization :=
  Charts.LocalMap.realize_id _

theorem interpret_comp (f : M → N) (g : N → P)
    (hf : ContMDiff (Model n) (Model m) ∞ f) (hg : ContMDiff (Model m) (Model p) ∞ g) :
    A.interpret C (g ∘ f) (hg.comp hf) = A.interpret B f hf ≫ B.interpret C g hg :=
  Charts.LocalMap.realize_comp _ _ _

/-- Transport between any two actual maximal-atlas families on the manifold. -/
def comparison (A' : ChartFamily n M) : A.realization ≅ A'.realization where
  hom := A.interpret A' id contMDiff_id
  inv := A'.interpret A id contMDiff_id
  hom_inv_id := by
    rw [← interpret_comp]
    exact A.interpret_id
  inv_hom_id := by
    rw [← interpret_comp]
    exact A'.interpret_id

theorem comparison_refl : A.comparison A = Iso.refl _ := by
  apply Iso.ext
  exact A.interpret_id

theorem comparison_trans (A' A'' : ChartFamily n M) :
    A.comparison A' ≪≫ A'.comparison A'' = A.comparison A'' := by
  apply Iso.ext
  exact (A.interpret_comp A' A'' id id contMDiff_id contMDiff_id).symm

theorem comparison_naturality (A' : ChartFamily n M) (B' : ChartFamily m N)
    (f : M → N) (hf : ContMDiff (Model n) (Model m) ∞ f) :
    (A.comparison A').hom ≫ A'.interpret B' f hf =
      A.interpret B f hf ≫ (B.comparison B').hom := by
  change A.interpret A' id contMDiff_id ≫ A'.interpret B' f hf = _
  rw [← interpret_comp]
  change A.interpret B' f _ = A.interpret B f hf ≫ B.interpret B' id contMDiff_id
  exact A.interpret_comp B B' f id hf contMDiff_id

end SquareKit.ManifoldRealization.ChartFamily
