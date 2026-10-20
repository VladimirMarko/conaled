import SquareKit.SmoothManifoldOpenComparison
import SquareKit.SmoothManifoldLocalSmoothness
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! Experimental consumers of the actual Mathlib manifold bridge: smooth maps
that cross selected target charts, an open-submanifold inclusion, and boundaries. -/
noncomputable section
open CategoryTheory Set SquareKit SquareKit.EuclideanOpen SquareKit.ManifoldRealization
open scoped Manifold ContDiff
namespace Examples.MathlibManifoldRealization

/-- A single ordinary global chart, regarded as a Mathlib smooth atlas member. -/
def globalFamily (n : ℕ) : ChartFamily n (Space n) where
  Index := Unit
  chart _ := OpenPartialHomeomorph.refl _
  smooth _ := by
    apply (IsManifold.mem_maximalAtlas_iff_contMDiffOn _).mpr
    exact ⟨contMDiff_id.contMDiffOn,contMDiff_id.contMDiffOn⟩
  covers _ := ⟨(),Set.mem_univ _⟩

def half (b : Bool) : Set (Space 1) := if b then {x | -1 < x 0} else {x | x 0 < 1}

theorem half_open (b : Bool) : IsOpen (half b) := by
  cases b
  · exact isOpen_lt (continuous_apply 0) continuous_const
  · exact isOpen_lt continuous_const (continuous_apply 0)

def splitFamily : ChartFamily 1 (Space 1) where
  Index := Bool
  chart b := OpenPartialHomeomorph.ofSet (half b) (half_open b)
  smooth b := by
    apply (IsManifold.mem_maximalAtlas_iff_contMDiffOn _).mpr
    exact ⟨contMDiff_id.contMDiffOn,contMDiff_id.contMDiffOn⟩
  covers x := by
    by_cases h : x 0 < 1
    · exact ⟨false,h⟩
    · exact ⟨true,lt_of_lt_of_le (by norm_num) (not_lt.mp h)⟩

/-- The identity from the selected global source chart needs both target charts. -/
theorem no_whole_target_chart (b : splitFamily.Index) :
    ¬ ∀ x ∈ ((globalFamily 1).chart ()).source, (id x) ∈ (splitFamily.chart b).source := by
  cases b
  · intro h
    have he := h (fun _ => 2) (Set.mem_univ _)
    change (2 : ℝ) < 1 at he
    norm_num at he
  · intro h
    have he := h (fun _ => -2) (Set.mem_univ _)
    change (-1 : ℝ) < -2 at he
    norm_num at he

def splitIdentity : (globalFamily 1).realization ⟶ splitFamily.realization :=
  (globalFamily 1).interpret splitFamily id contMDiff_id

theorem splitIdentity_comparison : splitIdentity = ((globalFamily 1).comparison splitFamily).hom := rfl

theorem splitIdentity_local (b : Bool) :
    embedding.map (subInclusion (chartDomain ((globalFamily 1).chart ()))
      (coordinateDefining (e := (globalFamily 1).chart ()) (splitFamily.chart b) id continuous_id)) ≫
      (globalFamily 1).charts.chart () ≫ splitIdentity =
      embedding.map (coordinateMap (splitFamily.chart b) id ((globalFamily 1).smooth ())
        (splitFamily.smooth b) contMDiff_id) ≫ splitFamily.charts.chart b :=
  (globalFamily 1).interpret_chart splitFamily id contMDiff_id () b

/-- The local coordinate criterion accepts a cover that cannot be replaced by
a single target chart, as witnessed by `no_whole_target_chart`. -/
theorem splitIdentity_smooth_from_coordinates :
    ContMDiff (Model 1) (Model 1) ∞ (id : Space 1 → Space 1) :=
  (globalFamily 1).contMDiff_of_localMap splitFamily
    ((globalFamily 1).localMap splitFamily id contMDiff_id)

/-- Continuity and smoothness follow from an arbitrary coordinate description;
neither is an additional hypothesis of the reconstruction step. -/
theorem smooth_from_coordinates {n m : ℕ} {M N : Type}
    [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace (Space n) M] [ChartedSpace (Space m) N]
    (A : ChartFamily n M) (B : ChartFamily m N) (f : M → N)
    (l : Charts.LocalMap A.charts B.charts f) :
    Continuous f ∧ ContMDiff (Model n) (Model m) ∞ f :=
  ⟨(A.contMDiff_of_localMap B l).continuous, A.contMDiff_of_localMap B l⟩

def exponential (x : Space 1) : Space 1 := fun _ => Real.exp (x 0)

theorem exponential_smooth : ContMDiff (Model 1) (Model 1) ∞ exponential :=
  (contDiff_pi.mpr (fun _ => Real.contDiff_exp.comp (contDiff_apply ℝ (fun _ : Fin 1 => ℝ) 0))).contMDiff

def interpretedExponential : object 1 (Space 1) ⟶ object 1 (Space 1) :=
  ManifoldRealization.map exponential exponential_smooth

theorem exponential_transport :
    (atlasIso (globalFamily 1)).hom ≫ (globalFamily 1).interpret splitFamily exponential exponential_smooth =
      interpretedExponential ≫ (atlasIso splitFamily).hom :=
  atlas_naturality (globalFamily 1) splitFamily exponential exponential_smooth

/-- A nontrivial open submanifold with Mathlib's inherited charted-space instance. -/
def punctured : TopologicalSpace.Opens (Space 1) :=
  ⟨{x | x 0 ≠ 0},isOpen_ne_fun (continuous_apply 0) continuous_const⟩

def puncturedInclusion : object 1 punctured ⟶ object 1 (Space 1) :=
  ManifoldRealization.map (Subtype.val : punctured → Space 1) contMDiff_subtype_val

def puncturedComparison : object 1 punctured ≅
    embedding.obj (⟨1,SmoothAlgebra.generator 0⟩ : Domain) :=
  principalIso ⟨1,SmoothAlgebra.generator 0⟩

theorem punctured_identity : ManifoldRealization.map (id : punctured → punctured) contMDiff_id =
    𝟙 (object 1 punctured) := map_id

theorem dimension_zero_identity : ManifoldRealization.map (id : Space 0 → Space 0) contMDiff_id =
    𝟙 (object 0 (Space 0)) := map_id

instance emptyChartedSpace (n : ℕ) : ChartedSpace (Space n) Empty where
  atlas := ∅
  chartAt := Empty.elim
  mem_chart_source x := x.elim
  chart_mem_atlas x := x.elim

/-- The actual preferred Mathlib atlas of the empty manifold has no charts. -/
theorem empty_initial (n : ℕ) (F : Sheaf SmoothOpenSite.topology (Type)) :
    ∃! _f : object n Empty ⟶ F, True := by
  let A := ChartFamily.preferred (n := n) (M := Empty)
  refine ⟨A.charts.descend (fun i => i.elim) (fun r => r.first.elim),trivial,?_⟩
  intro f _
  apply A.charts.hom_ext
  intro i
  exact i.elim

end Examples.MathlibManifoldRealization
