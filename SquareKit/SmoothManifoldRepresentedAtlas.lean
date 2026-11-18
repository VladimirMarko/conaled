import SquareKit.SmoothChartPullback
import SquareKit.SmoothRepresentedCover
import SquareKit.SmoothCechRefinement

/-! Represented covering atlases derived from actual ordinary manifold charts. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SquareKit.ManifoldRealization.ChartFamily
open CategoryTheory CategoryTheory.Limits Opposite EuclideanOpen SmoothAlgebra SmoothOpenSite
open scoped Manifold ContDiff
variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Space n) M]
variable (A : ChartFamily n M)

theorem chart_covering (V : SmoothPresentationSite.Site) (x : A.charts.realization.obj.obj (op V)) :
    SheafCoproductLocal.liftSieve (fun i => embedding.obj (A.charts.domain i)) A.charts.chart x ∈ topology V := by
  apply topology.superset_covering _ (Presheaf.imageSieve_mem topology A.charts.rawMap x)
  intro W r hr
  obtain ⟨z,hz⟩ := hr
  obtain ⟨i,b,hb⟩ := A.charts.rawMap_chart z
  exact ⟨i,b,hb.symm.trans hz⟩

abbrev triple (i j k : A.Index) : Domain :=
  overlap (A.charts.domain i) (A.overlapDefining i j) (A.overlapDefining i k)
abbrev firstSecond (i j k : A.Index) : A.triple i j k ⟶ A.pair i j :=
  overlapLeft _ _ _
def third (i j k : A.Index) : A.triple i j k ⟶ A.charts.domain k :=
  overlapRight (A.charts.domain i) (A.overlapDefining i j) (A.overlapDefining i k) ≫ A.right i k
theorem triple_pullback (i j k : A.Index) :
    IsPullback (embedding.map (A.firstSecond i j k)) (embedding.map (A.third i j k))
      (embedding.map (A.left i j) ≫ A.charts.chart i) (A.charts.chart k) := by
  have h := (overlap_sheaf_pullback (A.charts.domain i)
    (A.overlapDefining i j) (A.overlapDefining i k)).paste_vert (A.chart_pullback i k)
  simpa only [third, embedding.map_comp] using h

/-- All site covering and pullback fields are derived from the ordinary charts. -/
def representedAtlas : SmoothRepresentedCover.Atlas A.charts.realization A.Index where
  domain := A.charts.domain
  chart := A.charts.chart
  covering := A.chart_covering
  pair := A.pair
  left := A.left
  right := A.right
  square := A.chart_pullback
  triple := A.triple
  firstSecond := A.firstSecond
  third := A.third
  tripleSquare := A.triple_pullback

end SquareKit.ManifoldRealization.ChartFamily

namespace SquareKit.ManifoldRealization
open CategoryTheory EuclideanOpen SmoothAlgebra
open scoped Manifold ContDiff
variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Space n) M]
def restrictChart (e : OpenPartialHomeomorph M (Space n)) (q : Free n) :
    OpenPartialHomeomorph M (Space n) :=
  e.trans (OpenPartialHomeomorph.ofSet (Localization.locus q) (Localization.locus_open q))
theorem restrictChart_smooth (e : OpenPartialHomeomorph M (Space n)) (q : Free n)
    (he : e ∈ IsManifold.maximalAtlas (Model n) ∞ M) :
    restrictChart e q ∈ IsManifold.maximalAtlas (Model n) ∞ M := by
  have hs : IsOpen (Localization.locus q : Set (Space n)) := Localization.locus_open q
  have h := restr_mem_maximalAtlas _ he (e.isOpen_inter_preimage hs)
  exact Eq.mp (congrArg (fun c => c ∈ IsManifold.maximalAtlas (Model n) ∞ M)
    (e.trans_of_set' hs).symm) h
omit [ChartedSpace (Space n) M] in
theorem restrictChart_target (e : OpenPartialHomeomorph M (Space n)) (q : Free n) :
    (restrictChart e q).target = Localization.locus q ∩ e.target := rfl
def restrictChartDomainIso (e : OpenPartialHomeomorph M (Space n)) (q : Free n) :
    chartDomain (restrictChart e q) ≅ subdomain (chartDomain e) q where
  hom := domainInclusion _ _ (by
    intro x hx
    change x ∈ Points (chartDomain (restrictChart e q)) at hx
    rw [chartDomain_locus, restrictChart_target] at hx
    have h : x ∈ Points (chartDomain e) := (chartDomain_locus e).symm ▸ hx.2
    exact mul_ne_zero h hx.1)
  inv := domainInclusion _ _ (by
    intro x hx
    change x ∈ Points (chartDomain (restrictChart e q))
    rw [chartDomain_locus, restrictChart_target]
    exact ⟨right_ne_zero_of_mul hx, (chartDomain_locus e) ▸ left_ne_zero_of_mul hx⟩)
  hom_inv_id := OpenFunctions.Map.ext (fun _ => rfl)
  inv_hom_id := OpenFunctions.Map.ext (fun _ => rfl)
namespace ChartFamily
variable (A : ChartFamily n M) (K : A.Index → Type) (q : ∀ i, K i → Free n)
    (hq : ∀ i, Covers (A.charts.domain i) (q i))
def subdivision : ChartFamily n M where
  Index := Σ i, K i
  chart p := restrictChart (A.chart p.1) (q p.1 p.2)
  smooth p := restrictChart_smooth _ _ (A.smooth p.1)
  covers x := by
    obtain ⟨i,hi⟩ := A.covers x
    let y : Points (chartDomain (A.chart i)) :=
      ⟨A.chart i x, (chartDomain_locus (A.chart i)).symm ▸ (A.chart i).map_source hi⟩
    obtain ⟨k,hk⟩ := hq i y
    exact ⟨⟨i,k⟩,hi,hk⟩
def subdivisionMap : Charts.Map (A.subdivision K q hq).charts A.charts where
  point := id
  index p := p.1
  coordinate p := (restrictChartDomainIso (A.chart p.1) (q p.1 p.2)).hom ≫ subInclusion _ _
  agreement _ _ := rfl
set_option backward.isDefEq.respectTransparency false in
theorem subdivision_chart (p : (A.subdivision K q hq).Index) :
    (A.subdivision K q hq).charts.chart p ≫ ((A.subdivision K q hq).comparison A).hom =
      embedding.map ((A.subdivisionMap K q hq).coordinate p) ≫ A.charts.chart p.1 := by
  have h := ((A.subdivision K q hq).localMap A id contMDiff_id).test p p.1 _ (𝟙 _)
    ((A.subdivisionMap K q hq).coordinate p) (fun _ => rfl)
  simpa only [realization, comparison, interpret, embedding.map_id, Category.id_comp] using h
end ChartFamily
end SquareKit.ManifoldRealization

namespace SquareKit.SmoothRepresentedCover.Atlas
open CategoryTheory CategoryTheory.Limits Opposite EuclideanOpen SmoothOpenSite
variable {X Y : Sheaf topology Type} {I : Type} (A : Atlas X I) (e : X ≅ Y)

/-- Transport only the base, retaining every represented domain and projection. -/
def transport : Atlas Y I where
  domain := A.domain
  chart i := A.chart i ≫ e.hom
  covering V x := by
    apply topology.superset_covering _ (A.covering V (e.inv.hom.app (op V) x))
    intro W r hr
    obtain ⟨i,b,hb⟩ := hr
    refine ⟨i,b,?_⟩
    change e.hom.hom.app _ ((A.chart i).hom.app _ b) = _
    have he : e.hom.hom.app (op V) (e.inv.hom.app (op V) x) = x :=
      congrArg (fun f => f.hom.app (op V) x) e.inv_hom_id
    rw [hb, NatTrans.naturality_apply e.hom.hom r.op (e.inv.hom.app (op V) x), he]
  pair := A.pair
  left := A.left
  right := A.right
  square i j := (A.square i j).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) e
    (by simp) (by simp) (by simp) (by simp)
  triple := A.triple
  firstSecond := A.firstSecond
  third := A.third
  tripleSquare i j k := by
    have h := (A.tripleSquare i j k).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) e
      (fst' := embedding.map (A.firstSecond i j k)) (snd' := embedding.map (A.third i j k))
      (f' := (embedding.map (A.left i j) ≫ A.chart i) ≫ e.hom)
      (g' := A.chart k ≫ e.hom) (by simp) (by simp) (by simp) (by simp)
    simpa only [Category.assoc] using h
end SquareKit.SmoothRepresentedCover.Atlas

namespace SquareKit.ManifoldRealization.ChartFamily
open CategoryTheory EuclideanOpen SmoothAlgebra SmoothRepresentedCover
open scoped Manifold ContDiff
variable {n m : ℕ} {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (Space n) M] [ChartedSpace (Space m) N]
variable (A : ChartFamily n M)
  (K : A.Index → Type) (q : ∀ i, K i → Free n) (hq : ∀ i, Covers (A.charts.domain i) (q i))

/-- A subdivision is retained over the original realized manifold. -/
def subdivisionAtlas : Atlas A.realization (Σ i, K i) :=
  (A.subdivision K q hq).representedAtlas.transport ((A.subdivision K q hq).comparison A)

/-- The actual coordinate inclusions give the refinement over the identity. -/
def subdivisionRefinement : AtlasMap A.representedAtlas (A.subdivisionAtlas K q hq) (𝟙 _) where
  index p := p.1
  chart p := (A.subdivisionMap K q hq).coordinate p
  commutes p := by
    rw [Category.comp_id]
    exact (A.subdivision_chart K q hq p).symm

variable (B : ChartFamily m N) (f : M → N) (hf : ContMDiff (Model n) (Model m) ∞ f)

/-- Actual inverse images of target charts cover the source manifold. -/
def inverseCharts : ChartFamily n M :=
  A.subdivision (fun _ => B.Index) (fun i j => coordinateDefining (e := A.chart i) (B.chart j) f hf.continuous)
    (A.localMap B f hf).covers

def inverseAtlas : Atlas A.realization (Σ _ : A.Index, B.Index) :=
  A.subdivisionAtlas (fun _ => B.Index) (fun i j => coordinateDefining (e := A.chart i) (B.chart j) f hf.continuous)
    (A.localMap B f hf).covers

def inverseSource : AtlasMap A.representedAtlas (A.inverseAtlas B f hf) (𝟙 _) :=
  A.subdivisionRefinement _ _ _

/-- Base change uses actual coordinate maps on the inverse-image domains. -/
def inverseTarget : AtlasMap B.representedAtlas (A.inverseAtlas B f hf) (A.interpret B f hf) where
  index p := p.2
  chart p := (restrictChartDomainIso (A.chart p.1)
    (coordinateDefining (e := A.chart p.1) (B.chart p.2) f hf.continuous)).hom ≫
    coordinateMap (B.chart p.2) f (A.smooth p.1) (B.smooth p.2) hf
  commutes p := by
    have h := (A.inverseSource B f hf).commutes p
    simp only [Category.comp_id] at h
    rw [← h]
    dsimp only [inverseSource, subdivisionRefinement, subdivisionMap, representedAtlas]
    simp only [embedding.map_comp, Category.assoc]
    rw [A.interpret_chart B f hf]
end SquareKit.ManifoldRealization.ChartFamily

namespace SquareKit.ManifoldRealization.ChartFamily
open CategoryTheory EuclideanOpen SmoothRepresentedCover
open scoped Manifold ContDiff
variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Space n) M]
variable (A B C : ChartFamily n M)

/-- A represented common refinement over the chosen realization of the manifold. -/
def commonRepresented : Atlas A.realization (Σ _ : B.Index, C.Index) :=
  (B.inverseAtlas C id contMDiff_id).transport (B.comparison A)

def commonRepresentedLeft : AtlasMap (B.representedAtlas.transport (B.comparison A))
    (A.commonRepresented B C) (𝟙 _) where
  index p := p.1
  chart p := (B.inverseSource C id contMDiff_id).chart p
  commutes p := by
    rw [Category.comp_id]
    exact (Category.assoc _ _ _).symm.trans
      (congrArg (fun h => h ≫ (B.comparison A).hom)
        (by
          have h := (B.inverseSource C id contMDiff_id).commutes p
          rw [Category.comp_id] at h
          exact h))

def commonRepresentedRight : AtlasMap (C.representedAtlas.transport (C.comparison A))
    (A.commonRepresented B C) (𝟙 _) where
  index p := p.2
  chart p := (B.inverseTarget C id contMDiff_id).chart p
  commutes p := by
    rw [Category.comp_id]
    have h := congrArg (fun h => h ≫ (C.comparison A).hom)
      ((B.inverseTarget C id contMDiff_id).commutes p)
    have he : (B.comparison C).hom ≫ (C.comparison A).hom = (B.comparison A).hom :=
      congrArg Iso.hom (B.comparison_trans C A)
    change (embedding.map ((B.inverseTarget C id contMDiff_id).chart p) ≫ C.charts.chart p.2) ≫
      (C.comparison A).hom = ((B.inverseAtlas C id contMDiff_id).chart p ≫ (B.comparison C).hom) ≫
        (C.comparison A).hom at h
    simp only [Category.assoc, he] at h
    exact h
end SquareKit.ManifoldRealization.ChartFamily

namespace SquareKit.SmoothRepresentedCover.AtlasMap
open CategoryTheory EuclideanOpen SmoothOpenSite
variable {X Y Z : Sheaf topology Type} {I J : Type}
  {A : Atlas X I} {B : Atlas Y J} {f : Y ⟶ X}

/-- Changing the target realization retains the actual composite base map. -/
def transportTarget (r : AtlasMap A B f) (e : X ≅ Z) : AtlasMap (A.transport e) B (f ≫ e.hom) where
  index := r.index
  chart := r.chart
  commutes j := by
    change embedding.map (r.chart j) ≫ (A.chart (r.index j) ≫ e.hom) = _
    rw [← Category.assoc, r.commutes, Category.assoc]
end SquareKit.SmoothRepresentedCover.AtlasMap

namespace SquareKit.ManifoldRealization.ChartFamily
open CategoryTheory EuclideanOpen SmoothRepresentedCover
open scoped Manifold ContDiff
variable {n m k : ℕ} {M N L : Type} [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace L]
  [ChartedSpace (Space n) M] [ChartedSpace (Space m) N] [ChartedSpace (Space k) L]
variable (A : ChartFamily n M) (B : ChartFamily m N) (C : ChartFamily k L)
  (f : M → N) (hf : ContMDiff (Model n) (Model m) ∞ f)
  (g : L → M) (hg : ContMDiff (Model k) (Model n) ∞ g)

/-- The second base change maps into the already constructed inverse-image atlas. -/
def inverseSecond : AtlasMap (A.inverseAtlas B f hf)
    (C.inverseAtlas (A.inverseCharts B f hf) g hg)
    (C.interpret (A.inverseCharts B f hf) g hg ≫ ((A.inverseCharts B f hf).comparison A).hom) :=
  (C.inverseTarget (A.inverseCharts B f hf) g hg).transportTarget ((A.inverseCharts B f hf).comparison A)

theorem inverseSecond_base :
    C.interpret (A.inverseCharts B f hf) g hg ≫ ((A.inverseCharts B f hf).comparison A).hom =
      C.interpret A g hg := by
  change _ ≫ (A.inverseCharts B f hf).interpret A id contMDiff_id = _
  rw [← C.interpret_comp]
  rfl

theorem inverseComposite_base :
    (C.interpret (A.inverseCharts B f hf) g hg ≫ ((A.inverseCharts B f hf).comparison A).hom) ≫
      A.interpret B f hf = C.interpret B (f ∘ g) (hf.comp hg) := by
  rw [A.inverseSecond_base B C f hf g hg]
  exact (C.interpret_comp A B g f hg hf).symm
end SquareKit.ManifoldRealization.ChartFamily

namespace SquareKit.ManifoldRealization.ChartFamily
open CategoryTheory EuclideanOpen SmoothRepresentedCover
open scoped Manifold ContDiff
variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Space n) M]
variable (A : ChartFamily n M)

/-- The second projection of the chart-intersection refinement, with the
identity base-map equality transported explicitly. -/
def selfCommonRight : AtlasMap A.representedAtlas (A.inverseAtlas A id contMDiff_id) (𝟙 _) :=
  Eq.mp (congrArg (AtlasMap A.representedAtlas (A.inverseAtlas A id contMDiff_id)) A.interpret_id)
    (A.inverseTarget A id contMDiff_id)
end SquareKit.ManifoldRealization.ChartFamily
