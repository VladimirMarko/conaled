import SquareKit.SmoothTorsorReconstruction
import SquareKit.SheafTorsorReindexMaps
/-! All-stage recovery from the reconstructed ordinary total manifold. -/
noncomputable section
namespace SquareKit.SmoothTorsorReconstruction
open Topology CategoryTheory ManifoldRealization SmoothOpenSite SmoothManifoldAction EuclideanOpen IsManifold
open scoped Manifold ContDiff
variable {n : ℕ} {G B : Type} [Group G] [TopologicalSpace B]
  [ChartedSpace (Space n) B] [IsManifold (modelWithCorners n) ∞ B]
variable (P : SheafTorsor.Torsor (locallyConstantGroup G) (object n B))
variable [TopologicalSpace G] [DiscreteTopology G]
local instance : ChartedSpace (Space n) (Total P) := chartedSpace P
local instance : IsManifold (modelWithCorners n) ∞ (Total P) := isManifold P
def reconstructionChart (i : (sectionCharts P).Index) (g : G) :
    OpenPartialHomeomorph (Total P) (Space n) :=
  (localSheet P i g).trans ((sectionCharts P).chart i)
theorem reconstructionChart_smooth (i : (sectionCharts P).Index) (g : G) :
    reconstructionChart P i g ∈ maximalAtlas (modelWithCorners n) ∞ (Total P) := by
  have hs : ContMDiffOn (modelWithCorners n) (modelWithCorners n) ∞ (localSheet P i g) (localSheet P i g).source :=
    (bundle P).smooth_projection.contMDiffOn
  apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
  · exact (contMDiffOn_of_mem_maximalAtlas ((sectionCharts P).smooth i)).comp
      (hs.mono (fun _ h => h.1)) (fun _ h => h.2)
  · exact (smooth_localSheet_inverse P i g).comp
      ((contMDiffOn_symm_of_mem_maximalAtlas ((sectionCharts P).smooth i)).mono (fun _ h => h.1))
      (fun x hx => localSheet_target P i g ▸ hx.2)
def reconstructionCharts : ChartFamily n (Total P) where
  Index := (sectionCharts P).Index × G
  chart ig := reconstructionChart P ig.1 ig.2
  smooth ig := reconstructionChart_smooth P ig.1 ig.2
  covers z := by
    obtain ⟨i,hi⟩ := (sectionCharts P).covers z.proj
    obtain ⟨g,hg,_⟩ := (localTrivialization P i).sheets z hi
    exact ⟨(i,g),hg,hi⟩
theorem reconstructionChart_target (i : (sectionCharts P).Index) (g : G) :
    (reconstructionChart P i g).target = ((sectionCharts P).chart i).target := by
  ext x
  constructor
  · exact fun h => h.1
  · intro hx
    exact ⟨hx,(localSheet_target P i g).symm ▸ ((sectionCharts P).chart i).map_target hx⟩
def reconstructionDomainMap (i : (sectionCharts P).Index) (g : G) :
    chartDomain (reconstructionChart P i g) ⟶ (sectionCharts P).charts.domain i :=
  domainInclusion _ _ (by
    intro x hx
    change x ∈ Points (chartDomain (reconstructionChart P i g)) at hx
    change x ∈ Points (chartDomain ((sectionCharts P).chart i))
    rw [chartDomain_locus, reconstructionChart_target] at hx
    rw [chartDomain_locus]
    exact hx)
theorem reconstructionChart_point (i : (sectionCharts P).Index) (g : G)
    (x : Points (chartDomain (reconstructionChart P i g))) :
    chartPoint (reconstructionChart P i g) x =
      g • sectionPoint P i ((show Map _ _ from reconstructionDomainMap P i g) x) := by
  let y := (show Map _ _ from reconstructionDomainMap P i g) x
  let b := chartPoint ((sectionCharts P).chart i) y
  have hb := chartPoint_source ((sectionCharts P).chart i) y
  have hy : sectionInput P i b hb = y := by
    apply Subtype.ext
    apply ((sectionCharts P).chart i).right_inv
    rw [← chartDomain_locus]
    exact y.property
  have hs := (sectionValue_spec P i b hb).trans (congrArg (sectionPoint P i) hy)
  exact congrArg (fun z : Total P => g • z) hs

def reconstructionChartLift (i : (sectionCharts P).Index) (g : G) :
    embedding.obj (chartDomain (reconstructionChart P i g)) ⟶ SplitSheaf.extension P.family :=
  embedding.map (reconstructionDomainMap P i g) ≫
    ChartFamily.TorsorAtlas.localLift .preferred P i ≫ totalShift P g

theorem reconstructionChartLift_point (i : (sectionCharts P).Index) (g : G)
    (x : Points (chartDomain (reconstructionChart P i g))) :
    realSections.map (reconstructionChartLift P i g) (ordinaryPoint _ x) =
      totalPointEquiv P (chartPoint (reconstructionChart P i g) x) := by
  exact (realSections_map_totalShift_comp P (reconstructionDomainMap P i g)
    (ChartFamily.TorsorAtlas.localLift .preferred P i) g x).trans
      (congrArg (totalPointEquiv P) (reconstructionChart_point P i g x).symm)

theorem reconstructionChartLift_compatible :
    (reconstructionCharts P).charts.Compatible (fun i => reconstructionChartLift P i.1 i.2) := by
  exact chart_lifts_compatible P (reconstructionCharts P).charts (totalPointEquiv P)
    _ (fun i x => reconstructionChartLift_point P i.1 i.2 x)

def recoveryMap : object n (Total P) ⟶ SplitSheaf.extension P.family :=
  (atlasIso (reconstructionCharts P)).hom ≫
    (reconstructionCharts P).charts.descend _ (reconstructionChartLift_compatible P)

theorem recoveryMap_chart (i : (reconstructionCharts P).Index) :
    (reconstructionCharts P).charts.chart i ≫ (atlasIso (reconstructionCharts P)).inv ≫
      recoveryMap P = reconstructionChartLift P i.1 i.2 := by
  simp only [recoveryMap, Iso.inv_hom_id_assoc]
  exact (reconstructionCharts P).charts.chart_descend _ _ i
theorem recoveryMap_point (z : Total P) :
    realSections.map (recoveryMap P) (pointEquiv.symm z) = totalPointEquiv P z := by
  apply chart_recovery_point (reconstructionCharts P) (recoveryMap P) (totalPointEquiv P)
  intro i x
  exact (congrArg
    (fun k : embedding.obj ((reconstructionCharts P).charts.domain i) ⟶ SplitSheaf.extension P.family =>
      realSections.map k (ordinaryPoint _ x)) (recoveryMap_chart P i)).trans
    (reconstructionChartLift_point P i.1 i.2 x)

end SquareKit.SmoothTorsorReconstruction

namespace SquareKit.SmoothTorsorReconstruction
open CategoryTheory Opposite ManifoldRealization SmoothManifoldAction SmoothOpenSite
open scoped Manifold ContDiff
variable {G : Type} [Group G]
variable {M X : Sheaf topology Type}
variable (P : SheafTorsor.Torsor (locallyConstantGroup G) X)
variable (r : SmoothConstantAction.Representation G M) (k : M ⟶ SplitSheaf.extension P.family)

theorem total_intertwines
    (hc : ∀ (c : G) (U : SmoothPresentationSite.Siteᵒᵖ) (m : M.obj.obj U),
      k.hom.app U ((r.map c).hom.app U m) =
        P.toAction.totalAct U ((constantLabel G).app U c) (k.hom.app U m))
    (U : SmoothPresentationSite.Siteᵒᵖ) (g : (locallyConstantGroup G).obj.obj U)
    (m : M.obj.obj U) :
    k.hom.app U (r.act U g m) = P.toAction.totalAct U g (k.hom.app U m) := by
  apply (((isSheaf_iff_isSheaf_of_type _ _).mp (SplitSheaf.extension P.family).property)
    (Presheaf.imageSieve (constantLabel G) g)
    (Presheaf.imageSieve_mem topology (constantLabel G) g)).isSeparatedFor.ext
  intro V f hf
  obtain ⟨c,hc'⟩ := hf
  rw [← NatTrans.naturality_apply k.hom, r.act_natural, P.toAction.totalAct_natural,
    ← NatTrans.naturality_apply k.hom, ← hc', r.act_constant]
  exact hc c (op V) (M.obj.map f.op m)
end SquareKit.SmoothTorsorReconstruction

namespace SquareKit.SmoothTorsorReconstruction
open CategoryTheory Opposite ManifoldRealization SmoothManifoldAction SmoothOpenSite
open scoped Manifold ContDiff
variable {n : ℕ} {G B E : Type} [Group G] [MulAction G E]
  [TopologicalSpace G] [DiscreteTopology G]
  [TopologicalSpace B] [TopologicalSpace E]
  [ChartedSpace (Space n) B] [ChartedSpace (Space n) E]
  [IsManifold (modelWithCorners n) ∞ B] [IsManifold (modelWithCorners n) ∞ E]
variable (P : SheafTorsor.Torsor (locallyConstantGroup G) (object n B))
variable (Q : SmoothPrincipalBundle.Bundle (n := n) (G := G) (B := B) (E := E))
variable (k : object n E ⟶ SplitSheaf.extension P.family)
variable (hk : k ≫ SplitSheaf.p P.family = ManifoldRealization.map Q.projection Q.smooth_projection)
variable (hc : ∀ g, ManifoldRealization.map (fun e : E => g • e) (Q.smooth_action g) ≫ k =
  k ≫ totalShift P g)

def recoveryFiberMap : Q.realizedTorsor.family.family ⟶ P.family.family :=
  SplitSheaf.mapOfTotal (Q.realizedTotalIso.hom ≫ k) (by
    rw [Category.assoc, hk, Q.realizedTotalIso_projection])

theorem recoveryFiberMap_total : SplitSheaf.totalMap (recoveryFiberMap P Q k hk) =
    Q.realizedTotalIso.hom ≫ k := SplitSheaf.totalMap_mapOfTotal _ _

theorem recoveryFiberMap_value (x : (object n B).obj.Elements)
    (p : Q.realizedTorsor.family.family.obj x) :
    (⟨x.val, (recoveryFiberMap P Q k hk).app x p⟩ : (SplitSheaf.extension P.family).obj.obj x.obj) =
      k.hom.app x.obj (Q.realizedTotalIso.hom.hom.app x.obj ⟨x.val,p⟩) :=
  congrArg (fun f => f.hom.app x.obj ⟨x.val,p⟩) (recoveryFiberMap_total P Q k hk)

include hc in
theorem recoveryFiberMap_equivariant (x : (object n B).obj.Elements)
    (g : (locallyConstantGroup G).obj.obj x.obj) (p : Q.realizedTorsor.family.family.obj x) :
    (recoveryFiberMap P Q k hk).app x (Q.realizedTorsor.act x g p) =
      P.act x g ((recoveryFiberMap P Q k hk).app x p) := by
  have h : (⟨x.val, (recoveryFiberMap P Q k hk).app x (Q.realizedTorsor.act x g p)⟩ :
      (SplitSheaf.extension P.family).obj.obj x.obj) =
      ⟨x.val, P.act x g ((recoveryFiberMap P Q k hk).app x p)⟩ := by
    rw [recoveryFiberMap_value, Q.realizedTotalIso_equivariant]
    have hh := total_intertwines P (representation Q.smooth_action) k
      (fun c U m => congrArg (fun f => f.hom.app U m) (hc c)) x.obj g
      (Q.realizedTotalIso.hom.hom.app x.obj ⟨x.val,p⟩)
    rw [← recoveryFiberMap_value P Q k hk x p] at hh
    exact hh
  exact eq_of_heq (Sigma.mk.inj_iff.mp h).2

def recoveryEquivariantMap : SheafTorsor.EquivariantMap Q.realizedTorsor P where
  hom := recoveryFiberMap P Q k hk
  equivariant := recoveryFiberMap_equivariant P Q k hk hc

def recoveryArrow : SheafTorsor.Arrow Q.realizedTorsor P :=
  (recoveryEquivariantMap P Q k hk hc).toArrow

theorem recoveryArrow_total : SplitSheaf.totalMap (recoveryArrow P Q k hk hc).iso.hom =
    Q.realizedTotalIso.hom ≫ k := recoveryFiberMap_total P Q k hk
end SquareKit.SmoothTorsorReconstruction

namespace SquareKit.SmoothTorsorReconstruction
open CategoryTheory ManifoldRealization SmoothOpenSite SmoothManifoldAction EuclideanOpen
open scoped Manifold ContDiff
variable {n : ℕ} {G B : Type} [Group G] [TopologicalSpace B]
  [ChartedSpace (Space n) B] [IsManifold (modelWithCorners n) ∞ B]
variable (P : SheafTorsor.Torsor (locallyConstantGroup G) (object n B))
variable [TopologicalSpace G] [DiscreteTopology G]
local instance : ChartedSpace (Space n) (Total P) := chartedSpace P
local instance : IsManifold (modelWithCorners n) ∞ (Total P) := isManifold P

theorem recoveryMap_projection : recoveryMap P ≫ SplitSheaf.p P.family =
    ManifoldRealization.map (bundle P).projection (bundle P).smooth_projection := by
  apply projection_eq_of_points P
  intro z
  exact (congrArg (fun x => pointEquiv (realSections.map (SplitSheaf.p P.family) x))
    (recoveryMap_point P z)).trans (totalPointEquiv_projection P z)

theorem recoveryMap_action (g : G) :
    ManifoldRealization.map (fun z : Total P => g • z) ((bundle P).smooth_action g) ≫
      recoveryMap P = recoveryMap P ≫ totalShift P g := by
  apply manifold_total_hom_ext P
  intro z
  have hp : realSections.map (recoveryMap P) z = totalPointEquiv P (pointEquiv z) :=
    (congrArg (realSections.map (recoveryMap P)) (pointEquiv.symm_apply_apply z)).symm.trans
      (recoveryMap_point P (pointEquiv z))
  have ha := recoveryMap_point P (g • pointEquiv z)
  have he : realSections.map (ManifoldRealization.map (fun z : Total P => g • z)
      ((bundle P).smooth_action g)) z = pointEquiv.symm (g • pointEquiv z) := by
    apply pointEquiv.injective
    exact (map_eval _ _ z).trans (pointEquiv.apply_symm_apply _).symm
  exact (congrArg (realSections.map (recoveryMap P)) he).trans
    (ha.trans ((congrArg (realSections.map (totalShift P g)) hp).trans
      (totalShift_point P g _)).symm)

/-- Equivariance derives the inverse; no ordinary total space or inverse is supplied. -/
def reconstructedArrow : SheafTorsor.Arrow (bundle P).realizedTorsor P :=
  recoveryArrow P (bundle P) (recoveryMap P) (recoveryMap_projection P) (recoveryMap_action P)
end SquareKit.SmoothTorsorReconstruction

namespace SquareKit.SmoothTorsorReconstruction
open CategoryTheory ManifoldRealization SmoothOpenSite SmoothManifoldAction EuclideanOpen
open scoped Manifold ContDiff
variable {n : ℕ} {G B : Type} [Group G] [TopologicalSpace B]
  [ChartedSpace (Space n) B] [IsManifold (modelWithCorners n) ∞ B]
variable (P : SheafTorsor.Torsor (locallyConstantGroup G) (object n B))
variable [TopologicalSpace G] [DiscreteTopology G]
local instance : ChartedSpace (Space n) (Total P) := chartedSpace P
local instance : IsManifold (modelWithCorners n) ∞ (Total P) := isManifold P

/-- Recovery retains the entire total sheaf, including every test stage. -/
def reconstructedTotalIso : object n (Total P) ≅ SplitSheaf.extension P.family :=
  (bundle P).realizedTotalIso.symm ≪≫
    SplitSheaf.totalIso (reconstructedArrow P).iso

theorem reconstructedTotalIso_hom : (reconstructedTotalIso P).hom = recoveryMap P := by
  change (bundle P).realizedTotalIso.inv ≫ SplitSheaf.totalMap (reconstructedArrow P).iso.hom = _
  rw [show SplitSheaf.totalMap (reconstructedArrow P).iso.hom =
    (bundle P).realizedTotalIso.hom ≫ recoveryMap P from
      recoveryArrow_total P (bundle P) _ _ _]
  simp

theorem reconstructedTotalIso_projection : (reconstructedTotalIso P).hom ≫ SplitSheaf.p P.family =
    ManifoldRealization.map (bundle P).projection (bundle P).smooth_projection := by
  rw [reconstructedTotalIso_hom]
  exact recoveryMap_projection P
end SquareKit.SmoothTorsorReconstruction

namespace SquareKit.SmoothTorsorReconstruction
open CategoryTheory Opposite ManifoldRealization SmoothOpenSite SmoothManifoldAction EuclideanOpen
open scoped Manifold ContDiff
variable {n : ℕ} {G B : Type} [Group G] [TopologicalSpace B]
  [ChartedSpace (Space n) B] [IsManifold (modelWithCorners n) ∞ B]
variable (P : SheafTorsor.Torsor (locallyConstantGroup G) (object n B))
variable [TopologicalSpace G] [DiscreteTopology G]
local instance : ChartedSpace (Space n) (Total P) := chartedSpace P
local instance : IsManifold (modelWithCorners n) ∞ (Total P) := isManifold P

theorem reconstructedTotalIso_equivariant (U : SmoothPresentationSite.Siteᵒᵖ)
    (g : (locallyConstantGroup G).obj.obj U) (z : (object n (Total P)).obj.obj U) :
    (reconstructedTotalIso P).hom.hom.app U ((representation (bundle P).smooth_action).act U g z) =
      P.toAction.totalAct U g ((reconstructedTotalIso P).hom.hom.app U z) := by
  rw [reconstructedTotalIso_hom]
  exact total_intertwines P (representation (bundle P).smooth_action) (recoveryMap P)
    (fun c V x => congrArg (fun f => f.hom.app V x) (recoveryMap_action P c)) U g z

theorem reconstructedTotalIso_inverse_projection :
    (reconstructedTotalIso P).inv ≫ ManifoldRealization.map (bundle P).projection
      (bundle P).smooth_projection = SplitSheaf.p P.family := by
  rw [← reconstructedTotalIso_projection]
  simp
end SquareKit.SmoothTorsorReconstruction
