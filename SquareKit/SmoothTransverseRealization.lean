import SquareKit.SmoothTransversePullbackSmooth
import SquareKit.SmoothTransverseRealizationNaturality
import SquareKit.SmoothTransverseLocalPullback
import SquareKit.SmoothManifoldChartMono
import SquareKit.SmoothManifoldRepresentedAtlas
import Mathlib.CategoryTheory.Sites.LocallyBijective

/-! Preservation of ordinary transverse fiber products at every sheaf stage.

The canonical comparison is locally surjective by principal normal-form covers
and injective by chart saturation and full-algebra cancellation. Local bijectivity
then gives the categorical pullback and its universal and stage lift APIs.

`lift_in_normalOpen` uses a measured declaration-local 400000-heartbeat allowance
for dependent projection recovery; all other resource limits remain unchanged.
-/
noncomputable section
set_option autoImplicit false
namespace SquareKit.SmoothTransversePullback.Realization
open CategoryTheory CategoryTheory.Limits Opposite ManifoldRealization
open scoped Manifold ContDiff

variable {m n p : ℕ} {M N P : Type}
  [TopologicalSpace M] [ChartedSpace (Space m) M] [IsManifold (modelWithCorners m) ∞ M]
  [TopologicalSpace N] [ChartedSpace (Space n) N] [IsManifold (modelWithCorners n) ∞ N]
  [TopologicalSpace P] [ChartedSpace (Space p) P] [IsManifold (modelWithCorners p) ∞ P]
  {f : M → P} {g : N → P}
  (hf : ContMDiff (modelWithCorners m) (modelWithCorners p) ∞ f)
  (hg : ContMDiff (modelWithCorners n) (modelWithCorners p) ∞ g)
  (ht : Transverse (m := m) (n := n) (p := p) f g)

abbrev source :=
  letI := chartedSpace hf hg ht
  letI := isManifold hf hg ht
  object (m+n-p) (Pullback f g)
abbrev target := pullback (ManifoldRealization.map f hf) (ManifoldRealization.map g hg)

def first : source hf hg ht ⟶ object m M := by
  letI := chartedSpace hf hg ht
  letI := isManifold hf hg ht
  exact ManifoldRealization.map fst (smooth_fst hf hg ht)

def second : source hf hg ht ⟶ object n N := by
  letI := chartedSpace hf hg ht
  letI := isManifold hf hg ht
  exact ManifoldRealization.map snd (smooth_snd hf hg ht)

theorem square : first hf hg ht ≫ ManifoldRealization.map f hf =
    second hf hg ht ≫ ManifoldRealization.map g hg := by
  let := chartedSpace hf hg ht
  let := isManifold hf hg ht
  unfold first second
  rw [← ManifoldRealization.map_comp, ← ManifoldRealization.map_comp]
  congr 1
  funext q
  exact q.property

def comparison : source hf hg ht ⟶ target hf hg :=
  pullback.lift (first hf hg ht) (second hf hg ht) (square hf hg ht)

@[reassoc (attr := simp)] theorem comparison_first :
    comparison hf hg ht ≫ pullback.fst _ _ = first hf hg ht :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem comparison_second :
    comparison hf hg ht ≫ pullback.snd _ _ = second hf hg ht :=
  pullback.lift_snd _ _ _

/-- This equality concerns complete sections at every presentation stage. -/
theorem comparison_restrict {V W : SmoothPresentationSite.Site} (r : W ⟶ V)
    (x : (source hf hg ht).obj.obj (op V)) :
    (comparison hf hg ht).hom.app (op W) ((source hf hg ht).obj.map r.op x) =
      (target hf hg).obj.map r.op ((comparison hf hg ht).hom.app (op V) x) :=
  NatTrans.naturality_apply (comparison hf hg ht).hom r.op x

/-- The actual regular-level chart in the preferred atlas on the equality subtype. -/
def sourceChart (q : Pullback f g) :
    EuclideanOpen.embedding.obj (chartDomain (localModel hf hg ht q).chart) ⟶ source hf hg ht := by
  letI := chartedSpace hf hg ht
  letI := isManifold hf hg ht
  exact (ChartFamily.preferred (n := m+n-p) (M := Pullback f g)).charts.chart q

set_option backward.isDefEq.respectTransparency false in
theorem sourceChart_first (q : Pullback f g) :
    sourceChart hf hg ht q ≫ first hf hg ht =
      EuclideanOpen.embedding.map ((localModel hf hg ht q).normalParameterMap ≫
        (localModel hf hg ht q).ambientFirst) ≫
      (ChartFamily.preferred (n := m) (M := M)).charts.chart q.val.1 := by
  let := chartedSpace hf hg ht
  let := isManifold hf hg ht
  have he := ((ChartFamily.preferred (n := m+n-p) (M := Pullback f g)).localMap
    (ChartFamily.preferred (n := m) (M := M)) fst (smooth_fst hf hg ht)).test q q.val.1
      (chartDomain (localModel hf hg ht q).chart) (𝟙 _)
      ((localModel hf hg ht q).normalParameterMap ≫ (localModel hf hg ht q).ambientFirst)
      (fun v => ((localModel hf hg ht q).normalParameterMap_first_agreement v).symm)
  simpa only [EuclideanOpen.embedding.map_id, Category.id_comp, sourceChart, first,
    ManifoldRealization.map, ChartFamily.interpret] using he

set_option backward.isDefEq.respectTransparency false in
theorem sourceChart_second (q : Pullback f g) :
    sourceChart hf hg ht q ≫ second hf hg ht =
      EuclideanOpen.embedding.map ((localModel hf hg ht q).normalParameterMap ≫
        (localModel hf hg ht q).ambientSecond) ≫
      (ChartFamily.preferred (n := n) (M := N)).charts.chart q.val.2 := by
  let := chartedSpace hf hg ht
  let := isManifold hf hg ht
  have he := ((ChartFamily.preferred (n := m+n-p) (M := Pullback f g)).localMap
    (ChartFamily.preferred (n := n) (M := N)) snd (smooth_snd hf hg ht)).test q q.val.2
      (chartDomain (localModel hf hg ht q).chart) (𝟙 _)
      ((localModel hf hg ht q).normalParameterMap ≫ (localModel hf hg ht q).ambientSecond)
      (fun v => ((localModel hf hg ht q).normalParameterMap_second_agreement v).symm)
  simpa only [EuclideanOpen.embedding.map_id, Category.id_comp, sourceChart, second,
    ManifoldRealization.map, ChartFamily.interpret] using he

end SquareKit.SmoothTransversePullback.Realization

namespace SquareKit.SmoothTransversePullback.Realization
open CategoryTheory Opposite ManifoldRealization EuclideanOpen SmoothAlgebra
open SmoothAlgebra.Localization SmoothPresentationSite
open scoped Manifold ContDiff
variable {m n p : ℕ} {M N P : Type}
  [TopologicalSpace M] [ChartedSpace (Space m) M] [IsManifold (modelWithCorners m) ∞ M]
  [TopologicalSpace N] [ChartedSpace (Space n) N] [IsManifold (modelWithCorners n) ∞ N]
  [TopologicalSpace P] [ChartedSpace (Space p) P] [IsManifold (modelWithCorners p) ∞ P]
  {f : M → P} {g : N → P}
  (hf : ContMDiff (modelWithCorners m) (modelWithCorners p) ∞ f)
  (hg : ContMDiff (modelWithCorners n) (modelWithCorners p) ∞ g)
  (ht : Transverse (m := m) (n := n) (p := p) f g)

abbrev pairDomain (i : M) (j : N) :=
  EuclideanOpen.Product.domain (chartDomain (chartAt (Space m) i))
    (chartDomain (chartAt (Space n) j))

def pairPoint (i : M) (j : N) (x : Points (pairDomain (m := m) (n := n) i j)) : M × N :=
  (chartPoint (chartAt (Space m) i) ((EuclideanOpen.Product.fst _ _).toFun x),
   chartPoint (chartAt (Space n) j) ((EuclideanOpen.Product.snd _ _).toFun x))

omit [IsManifold (modelWithCorners m) ∞ M] [IsManifold (modelWithCorners n) ∞ N] in
theorem pairPoint_continuous (i : M) (j : N) : Continuous (pairPoint (m := m) (n := n) i j) :=
  ((chartPoint_openEmbedding _).continuous.comp (map_continuous (EuclideanOpen.Product.fst _ _))).prodMk
    ((chartPoint_openEmbedding _).continuous.comp (map_continuous (EuclideanOpen.Product.snd _ _)))

def normalOpen (q : Pullback f g) : Set (M × N) :=
  (localModel hf hg ht q).ambientChart.source ∩
    (localModel hf hg ht q).ambientChart ⁻¹' (localModel hf hg ht q).normal.chart.source

theorem normalOpen_open (q : Pullback f g) : IsOpen (normalOpen hf hg ht q) :=
  (localModel hf hg ht q).ambientChart.isOpen_inter_preimage
    (localModel hf hg ht q).normal.chart.open_source

def pairSupport (i : M) (j : N) (q : Pullback f g) : freeAlgebra (m+n) :=
  relativeSupport (pairDomain (m := m) (n := n) i j) ((pairPoint (m := m) (n := n) i j) ⁻¹' normalOpen hf hg ht q)
    ((normalOpen_open hf hg ht q).preimage (pairPoint_continuous (m := m) (n := n) i j))

omit [IsManifold (modelWithCorners m) ∞ M] [IsManifold (modelWithCorners n) ∞ N] in
set_option backward.isDefEq.respectTransparency false in
theorem pairPoint_real (i : M) (j : N) (B : Code)
    (a : Hom (Principal (chartDomain (chartAt (Space m) i)).defining) (Carrier B))
    (b : Hom (Principal (chartDomain (chartAt (Space n) j)).defining) (Carrier B))
    (h : Hom (Carrier B) ℝ) :
    pairPoint (m := m) (n := n) i j (realPoints (pairDomain (m := m) (n := n) i j).defining
      (h.comp (EuclideanOpen.Product.pair _ _ a b))) =
    (chartPoint (chartAt (Space m) i) (realPoints _ (h.comp a)),
      chartPoint (chartAt (Space n) j) (realPoints _ (h.comp b))) := by
  unfold pairPoint
  rw [← real_map, ← real_map]
  simp only [← Hom.comp_assoc, EuclideanOpen.Product.pair_fst, EuclideanOpen.Product.pair_snd]

set_option backward.isDefEq.respectTransparency false in
theorem pairSupport_covers (i : M) (j : N) (B : Code)
    (a : Hom (Principal (chartDomain (chartAt (Space m) i)).defining) (Carrier B))
    (b : Hom (Principal (chartDomain (chartAt (Space n) j)).defining) (Carrier B))
    (hc : (ManifoldRealization.map f hf).hom.app (op (op B))
        ((ChartFamily.preferred (n := m) (M := M)).charts.chart i |>.hom.app (op (op B))
          (show code (chartDomain (chartAt (Space m) i)) ⟶ B from a).op) =
      (ManifoldRealization.map g hg).hom.app (op (op B))
        ((ChartFamily.preferred (n := n) (M := N)).charts.chart j |>.hom.app (op (op B))
          (show code (chartDomain (chartAt (Space n) j)) ⟶ B from b).op)) :
    OpenCover.Covers (fun q : Pullback f g => EuclideanOpen.Product.pair _ _ a b
      (principalBase (pairDomain (m := m) (n := n) i j).defining (pairSupport hf hg ht i j q))) := by
  intro h
  have he := congrArg (fun x => (ChartFamily.preferred (n := p) (M := P)).realReduction B x h) hc
  change (ChartFamily.preferred (n := p) (M := P)).realReduction B
    (((ChartFamily.preferred (n := m) (M := M)).interpret .preferred f hf).hom.app _ _) h =
    (ChartFamily.preferred (n := p) (M := P)).realReduction B
      (((ChartFamily.preferred (n := n) (M := N)).interpret .preferred g hg).hom.app _ _) h at he
  rw [ChartFamily.realReduction_interpret, ChartFamily.realReduction_interpret,
    ChartFamily.realReduction_chart, ChartFamily.realReduction_chart] at he
  let q : Pullback f g := ⟨(chartPoint (chartAt (Space m) i) (realPoints _ (h.comp a)),
    chartPoint (chartAt (Space n) j) (realPoints _ (h.comp b))), he⟩
  refine ⟨q, ?_⟩
  change (h.comp (EuclideanOpen.Product.pair _ _ a b))
    (principalBase (pairDomain (m := m) (n := n) i j).defining (pairSupport hf hg ht i j q)) ≠ 0
  rw [point_base (U := pairDomain (m := m) (n := n) i j)
    (h.comp (EuclideanOpen.Product.pair _ _ a b)) (pairSupport hf hg ht i j q)]
  apply (relativeSupport_iff _ _ _ _).mpr
  change pairPoint (m := m) (n := n) i j _ ∈ normalOpen hf hg ht q
  rw [pairPoint_real]
  exact (localModel hf hg ht q).mem_source

end SquareKit.SmoothTransversePullback.Realization

namespace SquareKit.SmoothTransversePullback.LocalModel
open CategoryTheory ManifoldRealization SmoothNormalFormPrincipal EuclideanOpen SmoothAlgebra
open SmoothAlgebra.Localization SmoothPresentationSite
open scoped Manifold ContDiff
variable {m n p : ℕ} {M N P : Type}
  [TopologicalSpace M] [ChartedSpace (Space m) M]
  [TopologicalSpace N] [ChartedSpace (Space n) N]
  [TopologicalSpace P] [ChartedSpace (Space p) P]
  {f : M → P} {g : N → P} {q : Pullback f g}
  (A : LocalModel (m := m) (n := n) (p := p) q) (B : Code)
  (a : Hom (Principal (chartDomain (chartAt (Space m) q.val.1)).defining) (Carrier B))
  (b : Hom (Principal (chartDomain (chartAt (Space n) q.val.2)).defining) (Carrier B))
  (ha : ∀ h : Hom (Carrier B) ℝ,
    Fin.addCases (realPoints _ (h.comp a)).val (realPoints _ (h.comp b)).val ∈ A.finiteChart.source)

include ha in
theorem ambientStage_unit :
    IsUnit (EuclideanOpen.Product.coordinates _ _ a b (sourceDomain A.finiteChart).defining) := by
  apply unit_of_real_points B
  intro h
  change h (SmoothTransverseStageCover.coordinatePair B a b
    (sourceDomain A.finiteChart).defining) ≠ 0
  rw [SmoothTransverseStageCover.real_coordinate, SmoothTransverseStageCover.real_pair]
  change Fin.addCases (realPoints _ (h.comp a)).val (realPoints _ (h.comp b)).val ∈
    Points (sourceDomain A.finiteChart)
  rw [sourceDomain_points]
  exact ha h

def ambientStage : Hom (Principal (sourceDomain A.finiteChart).defining) (Carrier B) :=
  principalLift (sourceDomain A.finiteChart).defining
    (EuclideanOpen.Product.coordinates _ _ a b) (A.ambientStage_unit B a b ha)

theorem ambientStage_base : (A.ambientStage B a b ha).comp
    (principalBase (sourceDomain A.finiteChart).defining) = EuclideanOpen.Product.coordinates _ _ a b :=
  lift_base _ _ (fun _ => A.ambientStage_unit B a b ha)

theorem ambientStage_first :
    (A.ambientStage B a b ha).comp (Localization.pullback A.ambientFirst) = a := by
  apply principal_unique
  apply hom_ext_generators
  intro i
  change A.ambientStage B a b ha (Localization.pullback A.ambientFirst
    (principalBase _ (generator i))) = _
  rw [A.ambientFirst_base]
  have he := congrArg (fun k : Hom (freeAlgebra (m+n)) (Carrier B) => k (generator (Fin.castAdd n i)))
    (A.ambientStage_base B a b ha)
  simpa only [Hom.comp, Function.comp_apply, EuclideanOpen.Product.coordinates,
    SmoothAlgebra.Coordinates.pair, evaluate_generator, Fin.addCases_left] using he

theorem ambientStage_second :
    (A.ambientStage B a b ha).comp (Localization.pullback A.ambientSecond) = b := by
  apply principal_unique
  apply hom_ext_generators
  intro i
  change A.ambientStage B a b ha (Localization.pullback A.ambientSecond
    (principalBase _ (generator i))) = _
  rw [A.ambientSecond_base]
  have he := congrArg (fun k : Hom (freeAlgebra (m+n)) (Carrier B) => k (generator (Fin.natAdd m i)))
    (A.ambientStage_base B a b ha)
  simpa only [Hom.comp, Function.comp_apply, EuclideanOpen.Product.coordinates,
    SmoothAlgebra.Coordinates.pair, evaluate_generator, Fin.addCases_right] using he

end SquareKit.SmoothTransversePullback.LocalModel

namespace SquareKit.SmoothTransversePullback.Realization
open CategoryTheory CategoryTheory.Limits Opposite ManifoldRealization EuclideanOpen SmoothAlgebra
open SmoothAlgebra.Localization SmoothPresentationSite
open scoped Manifold ContDiff
variable {m n p : ℕ} {M N P : Type}
  [TopologicalSpace M] [ChartedSpace (Space m) M] [IsManifold (modelWithCorners m) ∞ M]
  [TopologicalSpace N] [ChartedSpace (Space n) N] [IsManifold (modelWithCorners n) ∞ N]
  [TopologicalSpace P] [ChartedSpace (Space p) P] [IsManifold (modelWithCorners p) ∞ P]
  {f : M → P} {g : N → P}
  (hf : ContMDiff (modelWithCorners m) (modelWithCorners p) ∞ f)
  (hg : ContMDiff (modelWithCorners n) (modelWithCorners p) ∞ g)
  (ht : Transverse (m := m) (n := n) (p := p) f g)

theorem comparison_projections_eq (V : Site) (x y : (source hf hg ht).obj.obj (op V))
    (h : (comparison hf hg ht).hom.app (op V) x = (comparison hf hg ht).hom.app (op V) y) :
    (first hf hg ht).hom.app (op V) x = (first hf hg ht).hom.app (op V) y ∧
      (second hf hg ht).hom.app (op V) x = (second hf hg ht).hom.app (op V) y := by
  constructor
  · have he := congrArg (fun z => (pullback.fst (ManifoldRealization.map f hf)
      (ManifoldRealization.map g hg)).hom.app (op V) z) h
    change (comparison hf hg ht ≫ pullback.fst _ _).hom.app _ x =
      (comparison hf hg ht ≫ pullback.fst _ _).hom.app _ y at he
    rwa [comparison_first] at he
  · have he := congrArg (fun z => (pullback.snd (ManifoldRealization.map f hf)
      (ManifoldRealization.map g hg)).hom.app (op V) z) h
    change (comparison hf hg ht ≫ pullback.snd _ _).hom.app _ x =
      (comparison hf hg ht ≫ pullback.snd _ _).hom.app _ y at he
    rwa [comparison_second] at he

set_option backward.isDefEq.respectTransparency false in
theorem sourceChart_comparison_cancel (q : Pullback f g) (B : Code)
    (a b : Hom (Principal (chartDomain (localModel hf hg ht q).chart).defining) (Carrier B))
    (h : (comparison hf hg ht).hom.app (op (op B))
        ((sourceChart hf hg ht q).hom.app _ (show code _ ⟶ B from a).op) =
      (comparison hf hg ht).hom.app (op (op B))
        ((sourceChart hf hg ht q).hom.app _ (show code _ ⟶ B from b).op)) : a = b := by
  obtain ⟨hl,hr⟩ := comparison_projections_eq hf hg ht (op B) _ _ h
  let A := localModel hf hg ht q
  apply A.normalParameterMap_cancel
  apply A.ambient_joint_cancel
  · change (show code (chartDomain (chartAt (Space m) q.val.1)) ⟶ B from
      (a.comp (Localization.pullback A.normalParameterMap)).comp (Localization.pullback A.ambientFirst)) =
      (show code (chartDomain (chartAt (Space m) q.val.1)) ⟶ B from
      (b.comp (Localization.pullback A.normalParameterMap)).comp (Localization.pullback A.ambientFirst))
    apply Quiver.Hom.op_inj
    apply (ChartFamily.preferred (n := m) (M := M)).chart_stage_injective q.val.1 (op B)
    change (embedding.map A.normalParameterMap ≫ embedding.map A.ambientFirst ≫
      (ChartFamily.preferred (n := m) (M := M)).charts.chart q.val.1).hom.app _
        (show code _ ⟶ B from a).op =
      (embedding.map A.normalParameterMap ≫ embedding.map A.ambientFirst ≫
      (ChartFamily.preferred (n := m) (M := M)).charts.chart q.val.1).hom.app _
        (show code _ ⟶ B from b).op
    rw [← Category.assoc, ← embedding.map_comp, ← sourceChart_first]
    exact hl
  · change (show code (chartDomain (chartAt (Space n) q.val.2)) ⟶ B from
      (a.comp (Localization.pullback A.normalParameterMap)).comp (Localization.pullback A.ambientSecond)) =
      (show code (chartDomain (chartAt (Space n) q.val.2)) ⟶ B from
      (b.comp (Localization.pullback A.normalParameterMap)).comp (Localization.pullback A.ambientSecond))
    apply Quiver.Hom.op_inj
    apply (ChartFamily.preferred (n := n) (M := N)).chart_stage_injective q.val.2 (op B)
    change (embedding.map A.normalParameterMap ≫ embedding.map A.ambientSecond ≫
      (ChartFamily.preferred (n := n) (M := N)).charts.chart q.val.2).hom.app _
        (show code _ ⟶ B from a).op =
      (embedding.map A.normalParameterMap ≫ embedding.map A.ambientSecond ≫
      (ChartFamily.preferred (n := n) (M := N)).charts.chart q.val.2).hom.app _
        (show code _ ⟶ B from b).op
    rw [← Category.assoc, ← embedding.map_comp, ← sourceChart_second]
    exact hr


def sourceReduction (B : Code) (x : (source hf hg ht).obj.obj (op (op B)))
    (h : Hom (Carrier B) ℝ) : Pullback f g := by
  letI := chartedSpace hf hg ht
  letI := isManifold hf hg ht
  exact (ChartFamily.preferred (n := m+n-p) (M := Pullback f g)).realReduction B x h

set_option backward.isDefEq.respectTransparency false in
theorem sourceReduction_chart (q : Pullback f g) (B : Code)
    (a : Hom (Principal (chartDomain (localModel hf hg ht q).chart).defining) (Carrier B))
    (h : Hom (Carrier B) ℝ) :
    sourceReduction hf hg ht B ((sourceChart hf hg ht q).hom.app _
      (show code _ ⟶ B from a).op) h =
      chartPoint (localModel hf hg ht q).chart (realPoints _ (h.comp a)) := by
  let := chartedSpace hf hg ht
  let := isManifold hf hg ht
  exact (ChartFamily.preferred (n := m+n-p) (M := Pullback f g)).realReduction_chart q B a h

set_option backward.isDefEq.respectTransparency false in
theorem comparison_reductions_eq (B : Code) (x y : (source hf hg ht).obj.obj (op (op B)))
    (hc : (comparison hf hg ht).hom.app _ x = (comparison hf hg ht).hom.app _ y)
    (h : Hom (Carrier B) ℝ) : sourceReduction hf hg ht B x h = sourceReduction hf hg ht B y h := by
  let := chartedSpace hf hg ht
  let := isManifold hf hg ht
  obtain ⟨hl,hr⟩ := comparison_projections_eq hf hg ht (op B) x y hc
  have hl' := congrArg ((ChartFamily.preferred (n := m) (M := M)).realReduction B · h) hl
  have hr' := congrArg ((ChartFamily.preferred (n := n) (M := N)).realReduction B · h) hr
  change (ChartFamily.preferred (n := m) (M := M)).realReduction B
    (((ChartFamily.preferred (n := m+n-p) (M := Pullback f g)).interpret .preferred fst
      (smooth_fst hf hg ht)).hom.app _ x) h =
    (ChartFamily.preferred (n := m) (M := M)).realReduction B
      (((ChartFamily.preferred (n := m+n-p) (M := Pullback f g)).interpret .preferred fst
        (smooth_fst hf hg ht)).hom.app _ y) h at hl'
  change (ChartFamily.preferred (n := n) (M := N)).realReduction B
    (((ChartFamily.preferred (n := m+n-p) (M := Pullback f g)).interpret .preferred snd
      (smooth_snd hf hg ht)).hom.app _ x) h =
    (ChartFamily.preferred (n := n) (M := N)).realReduction B
      (((ChartFamily.preferred (n := m+n-p) (M := Pullback f g)).interpret .preferred snd
        (smooth_snd hf hg ht)).hom.app _ y) h at hr'
  rw [ChartFamily.realReduction_interpret, ChartFamily.realReduction_interpret] at hl' hr'
  exact Subtype.ext (Prod.ext hl' hr')

set_option backward.isDefEq.respectTransparency false in
theorem comparison_injective (V : Site) : Function.Injective ((comparison hf hg ht).hom.app (op V)) := by
  let := chartedSpace hf hg ht
  let := isManifold hf hg ht
  let F := ChartFamily.preferred (n := m+n-p) (M := Pullback f g)
  apply F.chartwise_injective (comparison hf hg ht)
  intro W i j a b hc
  have hb : ∀ h : Hom (Carrier W.unop) ℝ,
      chartPoint (F.chart j) (realPoints (F.charts.domain j).defining (h.comp b.unop)) ∈
        (F.chart i).source := by
    intro h
    have he := comparison_reductions_eq hf hg ht W.unop _ _ hc h
    change sourceReduction hf hg ht W.unop
      ((sourceChart hf hg ht i).hom.app _ a) h =
      sourceReduction hf hg ht W.unop ((sourceChart hf hg ht j).hom.app _ b) h at he
    have he' := (sourceReduction_chart hf hg ht i W.unop a.unop h).symm.trans
      (he.trans (sourceReduction_chart hf hg ht j W.unop b.unop h))
    change chartPoint (localModel hf hg ht j).chart
      (realPoints (chartDomain (localModel hf hg ht j).chart).defining (h.comp b.unop)) ∈
      (localModel hf hg ht i).chart.source
    exact he' ▸ chartPoint_source (localModel hf hg ht i).chart
      (realPoints _ (h.comp a.unop))
  let b' := F.chartSaturation i j W.unop b.unop hb
  have he := F.chartSaturation_chart i j W.unop b.unop hb
  have hab : a.unop = b' := by
    apply sourceChart_comparison_cancel hf hg ht i W.unop
    exact hc.trans (congrArg ((comparison hf hg ht).hom.app (op W)) he.symm)
  calc
    (F.charts.chart i).hom.app (op W) a =
        (F.charts.chart i).hom.app (op W) (show code (F.charts.domain i) ⟶ W.unop from b').op :=
      congrArg ((F.charts.chart i).hom.app (op W)) (congrArg Quiver.Hom.op hab)
    _ = (F.charts.chart j).hom.app (op W) b := he


set_option backward.isDefEq.respectTransparency false in
theorem normalStage_factor (q : Pullback f g) (B : Code)
    (w : Hom (Principal (SmoothNormalFormPrincipal.sourceDomain
      (localModel hf hg ht q).finiteChart).defining) (Carrier B))
    (hc : (ManifoldRealization.map f hf).hom.app (op (op B))
        ((ChartFamily.preferred (n := m) (M := M)).charts.chart q.val.1 |>.hom.app _
          (show code _ ⟶ B from w.comp (Localization.pullback
            (localModel hf hg ht q).ambientFirst)).op) =
      (ManifoldRealization.map g hg).hom.app (op (op B))
        ((ChartFamily.preferred (n := n) (M := N)).charts.chart q.val.2 |>.hom.app _
          (show code _ ⟶ B from w.comp (Localization.pullback
            (localModel hf hg ht q).ambientSecond)).op)) :
    ∃! v : Hom (Principal (chartDomain (localModel hf hg ht q).chart).defining) (Carrier B),
      v.comp (Localization.pullback (localModel hf hg ht q).normalParameterMap) = w := by
  let A := localModel hf hg ht q
  apply A.normalFactorization hf hg B w
  have hfirst := ((ChartFamily.preferred (n := m) (M := M)).localMap
    (ChartFamily.preferred (n := p) (M := P)) f hf).test q.val.1 (f q.val.1)
      (SmoothNormalFormPrincipal.sourceDomain A.finiteChart) A.ambientFirst
      (A.ambientTargetFirst hf) (A.ambientTargetFirst_agreement hf)
  have hsecond := ((ChartFamily.preferred (n := n) (M := N)).localMap
    (ChartFamily.preferred (n := p) (M := P)) g hg).test q.val.2 (f q.val.1)
      (SmoothNormalFormPrincipal.sourceDomain A.finiteChart) A.ambientSecond
      (A.ambientTargetSecond hg) (A.ambientTargetSecond_agreement hg)
  change (show code (chartDomain (chartAt (Space p) (f q.val.1))) ⟶ B from
    w.comp (Localization.pullback (A.ambientTargetFirst hf))) =
    (show code (chartDomain (chartAt (Space p) (f q.val.1))) ⟶ B from
      w.comp (Localization.pullback (A.ambientTargetSecond hg)))
  apply Quiver.Hom.op_inj
  apply (ChartFamily.preferred (n := p) (M := P)).chart_stage_injective (f q.val.1) (op B)
  change (embedding.map (A.ambientTargetFirst hf) ≫
    (ChartFamily.preferred (n := p) (M := P)).charts.chart (f q.val.1)).hom.app _
      (show code _ ⟶ B from w).op =
    (embedding.map (A.ambientTargetSecond hg) ≫
    (ChartFamily.preferred (n := p) (M := P)).charts.chart (f q.val.1)).hom.app _
      (show code _ ⟶ B from w).op
  rw [← hfirst, ← hsecond]
  exact hc


set_option maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency false in
theorem lift_in_normalOpen (i : M) (j : N) (q : Pullback f g) (B : Code)
    (a : Hom (Principal (chartDomain (chartAt (Space m) i)).defining) (Carrier B))
    (b : Hom (Principal (chartDomain (chartAt (Space n) j)).defining) (Carrier B))
    (hc : (ManifoldRealization.map f hf).hom.app (op (op B))
        ((ChartFamily.preferred (n := m) (M := M)).charts.chart i |>.hom.app _
          (show code _ ⟶ B from a).op) =
      (ManifoldRealization.map g hg).hom.app (op (op B))
        ((ChartFamily.preferred (n := n) (M := N)).charts.chart j |>.hom.app _
          (show code _ ⟶ B from b).op))
    (ho : ∀ h : Hom (Carrier B) ℝ,
      (chartPoint (chartAt (Space m) i) (realPoints _ (h.comp a)),
       chartPoint (chartAt (Space n) j) (realPoints _ (h.comp b))) ∈ normalOpen hf hg ht q) :
    ∃ x : (source hf hg ht).obj.obj (op (op B)),
      (first hf hg ht).hom.app _ x =
        ((ChartFamily.preferred (n := m) (M := M)).charts.chart i).hom.app _
          (show code _ ⟶ B from a).op ∧
      (second hf hg ht).hom.app _ x =
        ((ChartFamily.preferred (n := n) (M := N)).charts.chart j).hom.app _
          (show code _ ⟶ B from b).op := by
  let CM := ChartFamily.preferred (n := m) (M := M)
  let CN := ChartFamily.preferred (n := n) (M := N)
  let A := localModel hf hg ht q
  have hma : ∀ h : Hom (Carrier B) ℝ,
      chartPoint (CM.chart i) (realPoints (CM.charts.domain i).defining (h.comp a)) ∈
        (CM.chart q.val.1).source := fun h => (ho h).1.1
  have hnb : ∀ h : Hom (Carrier B) ℝ,
      chartPoint (CN.chart j) (realPoints (CN.charts.domain j).defining (h.comp b)) ∈
        (CN.chart q.val.2).source := fun h => (ho h).1.2
  let a' := CM.chartSaturation q.val.1 i B a hma
  let b' := CN.chartSaturation q.val.2 j B b hnb
  have hea := CM.chartSaturation_chart q.val.1 i B a hma
  have heb := CN.chartSaturation_chart q.val.2 j B b hnb
  have hcoords : ∀ h : Hom (Carrier B) ℝ,
      Fin.addCases (realPoints _ (h.comp a')).val (realPoints _ (h.comp b')).val ∈ A.finiteChart.source := by
    intro h
    have har := (CM.realReduction_chart q.val.1 B a' h).symm.trans
      ((congrArg (CM.realReduction B · h) hea).trans (CM.realReduction_chart i B a h))
    have hbr := (CN.realReduction_chart q.val.2 B b' h).symm.trans
      ((congrArg (CN.realReduction B · h) heb).trans (CN.realReduction_chart j B b h))
    have hp := ho h
    rw [← har, ← hbr] at hp
    rw [A.finiteChart_source]
    change SmoothNormalFormPrincipal.split m n
      (Fin.addCases (realPoints _ (h.comp a')).val (realPoints _ (h.comp b')).val) ∈ A.normal.chart.source
    rw [SmoothNormalFormPrincipal.split_addCases]
    have htgt : ((realPoints _ (h.comp a')).val, (realPoints _ (h.comp b')).val) ∈ A.ambientChart.target := by
      constructor
      · exact (chartDomain_locus (chartAt (Space m) q.val.1)) ▸ (realPoints _ (h.comp a')).property
      · exact (chartDomain_locus (chartAt (Space n) q.val.2)) ▸ (realPoints _ (h.comp b')).property
    have hp' := hp.2
    change A.ambientChart (A.ambientChart.symm
      ((realPoints _ (h.comp a')).val, (realPoints _ (h.comp b')).val)) ∈ A.normal.chart.source at hp'
    rwa [A.ambientChart.right_inv htgt] at hp'
  let w := A.ambientStage B a' b' hcoords
  have hwc : (ManifoldRealization.map f hf).hom.app (op (op B))
      ((CM.charts.chart q.val.1).hom.app _
        (show code _ ⟶ B from w.comp (Localization.pullback A.ambientFirst)).op) =
    (ManifoldRealization.map g hg).hom.app (op (op B))
      ((CN.charts.chart q.val.2).hom.app _
        (show code _ ⟶ B from w.comp (Localization.pullback A.ambientSecond)).op) := by
    dsimp only [w]
    rw [A.ambientStage_first, A.ambientStage_second, hea, heb]
    exact hc
  obtain ⟨v,hv,_⟩ := normalStage_factor hf hg ht q B w hwc
  refine ⟨(sourceChart hf hg ht q).hom.app _ (show code _ ⟶ B from v).op, ?_, ?_⟩
  · change (sourceChart hf hg ht q ≫ first hf hg ht).hom.app _
      (show code _ ⟶ B from v).op = _
    rw [sourceChart_first, embedding.map_comp]
    change (CM.charts.chart q.val.1).hom.app _
      (show code _ ⟶ B from (v.comp (Localization.pullback A.normalParameterMap)).comp
        (Localization.pullback A.ambientFirst)).op = _
    rw [hv, A.ambientStage_first]
    exact hea
  · change (sourceChart hf hg ht q ≫ second hf hg ht).hom.app _
      (show code _ ⟶ B from v).op = _
    rw [sourceChart_second, embedding.map_comp]
    change (CN.charts.chart q.val.2).hom.app _
      (show code _ ⟶ B from (v.comp (Localization.pullback A.normalParameterMap)).comp
        (Localization.pullback A.ambientSecond)).op = _
    rw [hv, A.ambientStage_second]
    exact heb

set_option backward.isDefEq.respectTransparency false in
theorem comparison_eq_of_projections (V : Site) (x : (source hf hg ht).obj.obj (op V))
    (z : (target hf hg).obj.obj (op V))
    (hl : (first hf hg ht).hom.app _ x = (pullback.fst (ManifoldRealization.map f hf)
      (ManifoldRealization.map g hg)).hom.app _ z)
    (hr : (second hf hg ht).hom.app _ x = (pullback.snd (ManifoldRealization.map f hf)
      (ManifoldRealization.map g hg)).hom.app _ z) :
    (comparison hf hg ht).hom.app (op V) x = z := by
  have hp := ((sheafToPresheaf SmoothOpenSite.topology Type) ⋙
    (evaluation _ Type).obj (op V)).map_isPullback
      (IsPullback.of_hasPullback (ManifoldRealization.map f hf) (ManifoldRealization.map g hg))
  apply Limits.Types.ext_of_isPullback hp
  · change (comparison hf hg ht ≫ pullback.fst _ _).hom.app _ x = _
    rwa [comparison_first]
  · change (comparison hf hg ht ≫ pullback.snd _ _).hom.app _ x = _
    rwa [comparison_second]

set_option backward.isDefEq.respectTransparency false in
theorem comparison_locallySurjective :
    Presheaf.IsLocallySurjective SmoothOpenSite.topology (comparison hf hg ht).hom := by
  let CM := ChartFamily.preferred (n := m) (M := M)
  let CN := ChartFamily.preferred (n := n) (M := N)
  apply CM.chartwise_locallySurjective CN (comparison hf hg ht)
    (pullback.fst (ManifoldRealization.map f hf) (ManifoldRealization.map g hg))
    (pullback.snd (ManifoldRealization.map f hf) (ManifoldRealization.map g hg))
  intro V z i j a b ha hb
  have hc : (ManifoldRealization.map f hf).hom.app _ ((CM.charts.chart i).hom.app _ a) =
      (ManifoldRealization.map g hg).hom.app _ ((CN.charts.chart j).hom.app _ b) := by
    rw [ha, hb]
    exact congrArg (fun k : target hf hg ⟶ object p P => k.hom.app (op V) z)
      (pullback.condition (f := ManifoldRealization.map f hf) (g := ManifoldRealization.map g hg))
  let s := fun q : Pullback f g => EuclideanOpen.Product.pair _ _ a.unop b.unop
    (principalBase (pairDomain (m := m) (n := n) i j).defining (pairSupport hf hg ht i j q))
  apply SmoothOpenSite.imageSieve_of_principal_lifts (comparison hf hg ht) V.unop z s
    (pairSupport_covers hf hg ht i j V.unop a.unop b.unop hc)
  intro q
  let C := localization V.unop (s q)
  let r := localizationBase V.unop (s q)
  let a' := r.comp a.unop
  let b' := r.comp b.unop
  have har : (CM.charts.chart i).hom.app (op (op C)) (show code _ ⟶ C from a').op =
      (object m M).obj.map r.op.op ((CM.charts.chart i).hom.app (op V) a) :=
    NatTrans.naturality_apply (CM.charts.chart i).hom r.op.op a
  have hbr : (CN.charts.chart j).hom.app (op (op C)) (show code _ ⟶ C from b').op =
      (object n N).obj.map r.op.op ((CN.charts.chart j).hom.app (op V) b) :=
    NatTrans.naturality_apply (CN.charts.chart j).hom r.op.op b
  have hc' : (ManifoldRealization.map f hf).hom.app _
      ((CM.charts.chart i).hom.app _ (show code _ ⟶ C from a').op) =
    (ManifoldRealization.map g hg).hom.app _
      ((CN.charts.chart j).hom.app _ (show code _ ⟶ C from b').op) := by
    rw [har, hbr, NatTrans.naturality_apply, NatTrans.naturality_apply, hc]
  have ho : ∀ h : Hom (Carrier C) ℝ,
      (chartPoint (chartAt (Space m) i) (realPoints _ (h.comp a')),
        chartPoint (chartAt (Space n) j) (realPoints _ (h.comp b'))) ∈ normalOpen hf hg ht q := by
    intro h
    have hp := relativeSupport_local_real (pairDomain (m := m) (n := n) i j)
      ((pairPoint (m := m) (n := n) i j) ⁻¹' normalOpen hf hg ht q)
      ((normalOpen_open hf hg ht q).preimage (pairPoint_continuous (m := m) (n := n) i j))
      V.unop (EuclideanOpen.Product.pair _ _ a.unop b.unop) h
    change pairPoint (m := m) (n := n) i j
      (realPoints (pairDomain (m := m) (n := n) i j).defining _) ∈ normalOpen hf hg ht q at hp
    rw [EuclideanOpen.Product.pair_comp, pairPoint_real] at hp
    exact hp
  obtain ⟨x,hx,hy⟩ := lift_in_normalOpen hf hg ht i j q C a' b' hc' ho
  refine ⟨x, comparison_eq_of_projections hf hg ht (op C) x
    ((target hf hg).obj.map r.op.op z) ?_ ?_⟩
  · rw [hx, har, ha]
    exact (NatTrans.naturality_apply
      (pullback.fst (ManifoldRealization.map f hf) (ManifoldRealization.map g hg)).hom r.op.op z).symm
  · rw [hy, hbr, hb]
    exact (NatTrans.naturality_apply
      (pullback.snd (ManifoldRealization.map f hf) (ManifoldRealization.map g hg)).hom r.op.op z).symm

/-- The canonical comparison retains every section, including nilpotent directions. -/
instance comparison_isIso : IsIso (comparison hf hg ht) := by
  apply (Sheaf.isLocallyBijective_iff_isIso (comparison hf hg ht)).mp
  exact ⟨Presheaf.isLocallyInjective_of_injective _ _
    (fun V => comparison_injective hf hg ht V.unop), comparison_locallySurjective hf hg ht⟩

def comparisonIso : source hf hg ht ≅ target hf hg := asIso (comparison hf hg ht)

/-- Realization preserves the ordinary transverse fiber product with its actual projections. -/
theorem isPullback : IsPullback (first hf hg ht) (second hf hg ht)
    (ManifoldRealization.map f hf) (ManifoldRealization.map g hg) := by
  apply (IsPullback.of_hasPullback (ManifoldRealization.map f hf)
    (ManifoldRealization.map g hg)).of_iso' (comparisonIso hf hg ht)
      (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simp [comparisonIso]
  · simp [comparisonIso]
  · simp
  · simp

/-- The universal lift is defined for arbitrary sheaf tests. -/
def lift {T : Sheaf SmoothOpenSite.topology Type}
    (a : T ⟶ object m M) (b : T ⟶ object n N)
    (h : a ≫ ManifoldRealization.map f hf = b ≫ ManifoldRealization.map g hg) :
    T ⟶ source hf hg ht := (isPullback hf hg ht).lift a b h

@[reassoc (attr := simp)] theorem lift_first {T : Sheaf SmoothOpenSite.topology Type}
    (a : T ⟶ object m M) (b : T ⟶ object n N)
    (h : a ≫ ManifoldRealization.map f hf = b ≫ ManifoldRealization.map g hg) :
    lift hf hg ht a b h ≫ first hf hg ht = a := (isPullback hf hg ht).lift_fst a b h

@[reassoc (attr := simp)] theorem lift_second {T : Sheaf SmoothOpenSite.topology Type}
    (a : T ⟶ object m M) (b : T ⟶ object n N)
    (h : a ≫ ManifoldRealization.map f hf = b ≫ ManifoldRealization.map g hg) :
    lift hf hg ht a b h ≫ second hf hg ht = b := (isPullback hf hg ht).lift_snd a b h

theorem lift_unique {T : Sheaf SmoothOpenSite.topology Type}
    (a : T ⟶ object m M) (b : T ⟶ object n N)
    (h : a ≫ ManifoldRealization.map f hf = b ≫ ManifoldRealization.map g hg)
    (x : T ⟶ source hf hg ht) (hx : x ≫ first hf hg ht = a)
    (hy : x ≫ second hf hg ht = b) : x = lift hf hg ht a b h :=
  (isPullback hf hg ht).hom_ext (hx.trans (lift_first hf hg ht a b h).symm)
    (hy.trans (lift_second hf hg ht a b h).symm)

theorem lift_precomp {T S : Sheaf SmoothOpenSite.topology Type} (r : S ⟶ T)
    (a : T ⟶ object m M) (b : T ⟶ object n N)
    (h : a ≫ ManifoldRealization.map f hf = b ≫ ManifoldRealization.map g hg) :
    r ≫ lift hf hg ht a b h = lift hf hg ht (r ≫ a) (r ≫ b)
      (by simpa only [Category.assoc] using congrArg (r ≫ ·) h) := by
  apply lift_unique <;> simp

open SmoothPresentationSite

abbrev StagePairs (V : Site) :=
  {ab : (object m M).obj.obj (op V) × (object n N).obj.obj (op V) //
    (ManifoldRealization.map f hf).hom.app (op V) ab.1 =
      (ManifoldRealization.map g hg).hom.app (op V) ab.2}

def stageEquiv (V : Site) : (source hf hg ht).obj.obj (op V) ≃ StagePairs hf hg V :=
  PullbackCone.IsLimit.equivPullbackObj
    (((sheafToPresheaf SmoothOpenSite.topology Type) ⋙ (evaluation _ Type).obj (op V)).map_isPullback (isPullback hf hg ht)).isLimit

@[simp] theorem stageEquiv_first (V : Site) (x : (source hf hg ht).obj.obj (op V)) :
    (stageEquiv hf hg ht V x).val.1 = (first hf hg ht).hom.app (op V) x :=
  PullbackCone.IsLimit.equivPullbackObj_apply_fst _ _

@[simp] theorem stageEquiv_second (V : Site) (x : (source hf hg ht).obj.obj (op V)) :
    (stageEquiv hf hg ht V x).val.2 = (second hf hg ht).hom.app (op V) x :=
  PullbackCone.IsLimit.equivPullbackObj_apply_snd _ _

def stageLift (V : Site) (ab : StagePairs hf hg V) : (source hf hg ht).obj.obj (op V) :=
  (stageEquiv hf hg ht V).symm ab

@[simp] theorem stageLift_first (V : Site) (ab : StagePairs hf hg V) :
    (first hf hg ht).hom.app (op V) (stageLift hf hg ht V ab) = ab.val.1 :=
  by
    obtain ⟨x, rfl⟩ := (stageEquiv hf hg ht V).surjective ab
    simp only [stageLift, Equiv.symm_apply_apply, stageEquiv_first]

@[simp] theorem stageLift_second (V : Site) (ab : StagePairs hf hg V) :
    (second hf hg ht).hom.app (op V) (stageLift hf hg ht V ab) = ab.val.2 :=
  by
    obtain ⟨x, rfl⟩ := (stageEquiv hf hg ht V).surjective ab
    simp only [stageLift, Equiv.symm_apply_apply, stageEquiv_second]

theorem stageLift_unique (V : Site) (ab : StagePairs hf hg V)
    (x : (source hf hg ht).obj.obj (op V))
    (hx : (first hf hg ht).hom.app (op V) x = ab.val.1)
    (hy : (second hf hg ht).hom.app (op V) x = ab.val.2) :
    x = stageLift hf hg ht V ab := by
  apply (stageEquiv hf hg ht V).injective
  apply Subtype.ext
  apply Prod.ext
  · simpa only [stageEquiv_first, stageLift_first] using hx
  · simpa only [stageEquiv_second, stageLift_second] using hy

def stagePairsRestrict {V W : Site} (r : W ⟶ V) (ab : StagePairs hf hg V) : StagePairs hf hg W :=
  ⟨((object m M).obj.map r.op ab.val.1, (object n N).obj.map r.op ab.val.2), by
    rw [NatTrans.naturality_apply, NatTrans.naturality_apply, ab.property]⟩

theorem stageLift_restrict {V W : Site} (r : W ⟶ V) (ab : StagePairs hf hg V) :
    (source hf hg ht).obj.map r.op (stageLift hf hg ht V ab) =
      stageLift hf hg ht W (stagePairsRestrict hf hg r ab) := by
  apply stageLift_unique
  · rw [NatTrans.naturality_apply, stageLift_first]
    rfl
  · rw [NatTrans.naturality_apply, stageLift_second]
    rfl

@[simp] theorem stagePairsRestrict_id {V : Site} (ab : StagePairs hf hg V) :
    stagePairsRestrict hf hg (𝟙 V) ab = ab := by
  apply Subtype.ext
  simp [stagePairsRestrict]

theorem stagePairsRestrict_comp {V W X : Site} (r : W ⟶ V) (s : X ⟶ W)
    (ab : StagePairs hf hg V) :
    stagePairsRestrict hf hg (s ≫ r) ab =
      stagePairsRestrict hf hg s (stagePairsRestrict hf hg r ab) := by
  apply Subtype.ext
  simp [stagePairsRestrict]

@[simp] theorem stageLift_restrict_id {V : Site} (ab : StagePairs hf hg V) :
    stageLift hf hg ht V (stagePairsRestrict hf hg (𝟙 V) ab) =
      stageLift hf hg ht V ab := by rw [stagePairsRestrict_id]

theorem stageLift_restrict_comp {V W X : Site} (r : W ⟶ V) (s : X ⟶ W)
    (ab : StagePairs hf hg V) :
    (source hf hg ht).obj.map (s ≫ r).op (stageLift hf hg ht V ab) =
      stageLift hf hg ht X (stagePairsRestrict hf hg s (stagePairsRestrict hf hg r ab)) := by
  rw [stageLift_restrict, stagePairsRestrict_comp]

/-- Every choice of covering smooth atlases gives the same pullback square,
through the existing common-refinement comparisons. -/
theorem atlas_isPullback :
    letI := chartedSpace hf hg ht
    letI := isManifold hf hg ht
    ∀ (A : ChartFamily (m+n-p) (Pullback f g)) (B : ChartFamily m M)
      (C : ChartFamily n N) (D : ChartFamily p P),
      IsPullback (A.interpret B fst (smooth_fst hf hg ht))
        (A.interpret C snd (smooth_snd hf hg ht)) (B.interpret D f hf) (C.interpret D g hg) := by
  let := chartedSpace hf hg ht
  let := isManifold hf hg ht
  intro A B C D
  exact (isPullback hf hg ht).of_iso (atlasIso A) (atlasIso B) (atlasIso C) (atlasIso D)
    (atlas_naturality A B fst (smooth_fst hf hg ht)).symm
    (atlas_naturality A C snd (smooth_snd hf hg ht)).symm
    (atlas_naturality B D f hf).symm (atlas_naturality C D g hg).symm

/-- On each ordinary regular-level chart, the global comparison has the proved
principal-domain first projection. -/
theorem sourceChart_comparison_first (q : Pullback f g) :
    sourceChart hf hg ht q ≫ (comparisonIso hf hg ht).hom ≫ pullback.fst _ _ =
      embedding.map ((localModel hf hg ht q).normalParameterMap ≫
        (localModel hf hg ht q).ambientFirst) ≫
        (ChartFamily.preferred (n := m) (M := M)).charts.chart q.val.1 := by
  simpa only [comparisonIso, asIso_hom, comparison_first] using sourceChart_first hf hg ht q

theorem sourceChart_comparison_second (q : Pullback f g) :
    sourceChart hf hg ht q ≫ (comparisonIso hf hg ht).hom ≫ pullback.snd _ _ =
      embedding.map ((localModel hf hg ht q).normalParameterMap ≫
        (localModel hf hg ht q).ambientSecond) ≫
        (ChartFamily.preferred (n := n) (M := N)).charts.chart q.val.2 := by
  simpa only [comparisonIso, asIso_hom, comparison_second] using sourceChart_second hf hg ht q

end SquareKit.SmoothTransversePullback.Realization
