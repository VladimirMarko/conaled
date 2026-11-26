import SquareKit.SmoothBundleMapsRealization
import SquareKit.SheafTorsorLabels
import SquareKit.SmoothOrdinaryQuotient
import Mathlib.Data.Bundle
/-! Real-point fibers and their principal group action, before any topology on the total space. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SquareKit.SmoothOpenSite
open CategoryTheory Opposite SmoothPresentationSite

theorem realSections_map_surjective {E X : Sheaf topology Type} (p : E ⟶ X)
    [Presheaf.IsLocallySurjective topology p.hom] :
    Function.Surjective (realSections.map p) := by
  intro x
  obtain ⟨Y, f, ⟨z, hz⟩, y, hy⟩ := realPoint_lift _
    (Presheaf.imageSieve_mem topology p.hom x) (𝟙 _)
  refine ⟨E.obj.map y.op z, ?_⟩
  have h := congrArg (X.obj.map y.op) hz
  have hn := NatTrans.naturality_apply p.hom y.op z
  have hh := congrArg (fun t => t x) (X.obj.map_comp f.op y.op)
  have hid := congrArg (fun t => t x) (X.obj.map_id (op (op (free 0))))
  rw [← op_comp, hy] at hh
  exact hn.trans (h.trans (hh.symm.trans hid))
end SquareKit.SmoothOpenSite
namespace SquareKit.SmoothTorsorReconstruction
open CategoryTheory Opposite ManifoldRealization SmoothManifoldAction SmoothOpenSite
open scoped Manifold ContDiff
variable {n : ℕ} {G B : Type} [Group G] [TopologicalSpace B]
  [ChartedSpace (Space n) B] [IsManifold (modelWithCorners n) ∞ B]
variable (P : SheafTorsor.Torsor (locallyConstantGroup G) (object n B))
def baseElement (b : B) : (object n B).obj.Elements :=
  (object n B).obj.elementsMk _ (pointEquiv.symm b)
abbrev Fiber (b : B) : Type := P.family.family.obj (baseElement b)
abbrev Total : Type := Bundle.TotalSpace G (Fiber P)
instance (b : B) : MulAction G (Fiber P b) where
  smul g p := P.act (baseElement b) ((constantLabel G).app _ g) p
  one_smul p := by
    change P.act _ ((constantLabel G).app _ 1) p = p
    rw [((constantLabel G).app _).hom.map_one]
    exact P.one_act _ p
  mul_smul g h p := by
    change P.act _ ((constantLabel G).app _ (g*h)) p = _
    rw [((constantLabel G).app _).hom.map_mul]
    exact P.mul_act _ _ _ p
instance : MulAction G (Total P) where
  smul g z := ⟨z.proj, g • z.snd⟩
  one_smul z := by
    change (⟨z.proj, (1 : G) • z.snd⟩ : Total P) = z
    rw [one_smul]

  mul_smul g h z := by
    change (⟨z.proj, (g*h) • z.snd⟩ : Total P) = ⟨z.proj, g • h • z.snd⟩
    rw [mul_smul]

/-- The underlying total set is exactly the real sections of the sheaf total space. -/
def totalPointEquiv : Total P ≃ realSections.obj (SplitSheaf.extension P.family) :=
  (Equiv.mk (fun z => ⟨z.proj, z.snd⟩) (fun z => ⟨z.1,z.2⟩)
    (fun _ => rfl) (fun _ => rfl)).trans (Equiv.sigmaCongrLeft pointEquiv.symm)

instance fiber_nonempty (b : B) : Nonempty (Fiber P b) := by
  obtain ⟨⟨x,p⟩,hx⟩ := realSections_map_surjective (SplitSheaf.p P.family) (pointEquiv.symm b)
  change x = pointEquiv.symm b at hx
  cases hx
  exact ⟨p⟩

theorem fiber_principal (b : B) (p q : Fiber P b) : ∃! g : G, g • p = q := by
  obtain ⟨h,hh,hu⟩ := P.principal (baseElement b) p q
  obtain ⟨g,rfl⟩ := (constantLabelRealEquiv G).surjective h
  refine ⟨g,hh,?_⟩
  intro k hk
  apply (constantLabelRealEquiv G).injective
  exact hu _ hk

def fiberEquiv (b : B) (p : Fiber P b) : G ≃ Fiber P b :=
  (constantLabelRealEquiv G).trans (SheafTorsor.fiberEquiv P (baseElement b) p)

theorem totalPointEquiv_projection (z : Total P) :
    pointEquiv (realSections.map (SplitSheaf.p P.family) (totalPointEquiv P z)) = z.proj :=
  pointEquiv.apply_symm_apply z.proj

theorem projection_smul (g : G) (z : Total P) : (g • z).proj = z.proj := rfl

end SquareKit.SmoothTorsorReconstruction

namespace SquareKit.SmoothTorsorReconstruction
open CategoryTheory Opposite ManifoldRealization SmoothManifoldAction SmoothOpenSite EuclideanOpen
open scoped Manifold ContDiff
variable {n : ℕ} {G B : Type} [Group G] [TopologicalSpace B]
  [ChartedSpace (Space n) B] [IsManifold (modelWithCorners n) ∞ B]
variable (P : SheafTorsor.Torsor (locallyConstantGroup G) (object n B))
abbrev sectionCharts := ChartFamily.TorsorAtlas.charts (ChartFamily.preferred (n := n) (M := B)) P
abbrev sectionAtlas := ChartFamily.TorsorAtlas.atlas (ChartFamily.preferred (n := n) (M := B)) P

theorem chart_eval (A : ChartFamily n B) (i : A.Index) (x : Points (A.charts.domain i)) :
    pointEquiv (realSections.map ((A.charts.chart i) ≫ (atlasIso A).inv) (ordinaryPoint _ x)) =
      chartPoint (A.chart i) x := by
  have h := A.charts.realMap_chart (ChartFamily.preferred (n := n) (M := B)).charts
    A.atlas.covers (ChartFamily.preferred (n := n) (M := B)).atlas.covers
    (atlasIso A).inv i x
  change A.reconstruct .preferred (atlasIso A).inv (chartPoint (A.chart i) x) = _ at h
  rw [show A.reconstruct .preferred (atlasIso A).inv = id from
    A.reconstruct_interpret .preferred id contMDiff_id] at h
  exact h.symm

def sectionPoint (i : (sectionCharts P).Index) (x : Points ((sectionCharts P).charts.domain i)) : Total P :=
  (totalPointEquiv P).symm (realSections.map
    (ChartFamily.TorsorAtlas.localLift .preferred P i) (ordinaryPoint _ x))

theorem sectionPoint_projection (i : (sectionCharts P).Index)
    (x : Points ((sectionCharts P).charts.domain i)) :
    (sectionPoint P i x).proj = chartPoint ((sectionCharts P).chart i) x := by
  rw [← totalPointEquiv_projection P (sectionPoint P i x)]
  change pointEquiv (realSections.map (SplitSheaf.p P.family)
    (totalPointEquiv P ((totalPointEquiv P).symm _))) = _
  rw [Equiv.apply_symm_apply]
  change pointEquiv (realSections.map (ChartFamily.TorsorAtlas.localLift .preferred P i ≫
    SplitSheaf.p P.family) (ordinaryPoint _ x)) = _
  rw [ChartFamily.TorsorAtlas.localLift_projection]
  exact chart_eval (sectionCharts P) i x
theorem totalPointEquiv_smul (g : G) (z : Total P) :
    totalPointEquiv P (g • z) = P.toAction.totalAct _ ((constantLabelRealEquiv G) g)
      (totalPointEquiv P z) := rfl

theorem ordinaryPoint_map {U V : Domain} (f : U ⟶ V) (x : Points U) :
    realSections.map (embedding.map f) (ordinaryPoint U x) =
      ordinaryPoint V ((show EuclideanOpen.Map U V from f) x) := by
  apply (realSectionEquiv V).injective
  rw [realSectionEquiv_naturality]
  exact congrArg (show EuclideanOpen.Map U V from f) ((realSectionEquiv U).apply_symm_apply x) |>.trans
    ((realSectionEquiv V).apply_symm_apply _).symm

theorem sectionDifference_totalAct {Y : Sheaf SmoothOpenSite.topology Type} (f : Y ⟶ object n B)
    (s t : SplitSheaf.Tm (SheafTorsor.reindex P f).family)
    (U : SmoothPresentationSite.Siteᵒᵖ) (x : Y.obj.obj U) :
    P.toAction.totalAct U ((SheafTorsor.sectionDifference (SheafTorsor.reindex P f) s t).hom.app U x)
      ((SplitSheaf.pair P.family f s).hom.app U x) =
      (SplitSheaf.pair P.family f t).hom.app U x :=
  congrArg (Sigma.mk (f.hom.app U x))
    (SheafTorsor.sectionDifference_act (SheafTorsor.reindex P f) s t (Y.obj.elementsMk U x))

theorem sectionDifference_point_action {Y : Sheaf SmoothOpenSite.topology Type}
    (f : Y ⟶ object n B) (s t : SplitSheaf.Tm (SheafTorsor.reindex P f).family)
    (l r : Y ⟶ SplitSheaf.extension P.family)
    (hl : SplitSheaf.pair P.family f s = l) (hr : SplitSheaf.pair P.family f t = r)
    (x : realSections.obj Y) (g : G)
    (hg : constantLabelRealEquiv G g =
      (SheafTorsor.sectionDifference (SheafTorsor.reindex P f) s t).hom.app _ x) :
    g • (totalPointEquiv P).symm (realSections.map l x) =
      (totalPointEquiv P).symm (realSections.map r x) := by
  apply (totalPointEquiv P).injective
  rw [totalPointEquiv_smul, Equiv.apply_symm_apply, Equiv.apply_symm_apply, hg]
  have h := sectionDifference_totalAct P f s t _ x
  rw [hl, hr] at h
  exact h

theorem pointLift_comp {U V : Domain} (f : U ⟶ V) (l : embedding.obj V ⟶ SplitSheaf.extension P.family)
    (x : Points U) :
    (totalPointEquiv P).symm (realSections.map l (ordinaryPoint V ((show EuclideanOpen.Map U V from f) x))) =
      (totalPointEquiv P).symm (realSections.map (embedding.map f ≫ l) (ordinaryPoint U x)) :=
  congrArg (fun z => (totalPointEquiv P).symm (realSections.map l z)) (ordinaryPoint_map f x).symm

theorem total_smul_eq_self (a : G) (z : Total P) (h : a • z = z) : a = 1 :=
  (fiberEquiv P z.proj z.snd).injective
    ((Bundle.TotalSpace.mk_inj.mp h).trans (one_smul G z.snd).symm)

theorem ordinaryHomLabelEquiv_one (U : Domain) (x : Points U) :
    ordinaryHomLabelEquiv G U (SheafTorsor.labelOne (G := locallyConstantGroup G) (embedding.obj U)) x = 1 := by
  apply (constantLabelRealEquiv G).injective
  exact (SmoothOrdinaryQuotient.homLabel_point U _ x).trans
    (((constantLabel G).app _).hom.map_one).symm

theorem sections_eq_of_difference_one {Y : Sheaf SmoothOpenSite.topology Type}
    (f : Y ⟶ object n B) (s t : SplitSheaf.Tm (SheafTorsor.reindex P f).family)
    (h : SheafTorsor.sectionDifference (SheafTorsor.reindex P f) s t =
      SheafTorsor.labelOne Y) : s = t := by
  apply SplitPresheaf.Tm.ext
  funext x
  have hh := SheafTorsor.sectionDifference_act (SheafTorsor.reindex P f) s t x
  have he : (SheafTorsor.sectionDifference (SheafTorsor.reindex P f) s t).hom.app x.obj x.val = (1 : (locallyConstantGroup G).obj.obj x.obj) :=
    congrArg (fun k => k.hom.app x.obj x.val) h
  rw [he, (SheafTorsor.reindex P f).one_act] at hh
  exact hh

theorem pair_hom_ext {U : Domain} (b : embedding.obj U ⟶ object n B)
    (s t : SplitSheaf.Tm (SheafTorsor.reindex P b).family)
    (h : ∀ x : Points U,
      realSections.map (SplitSheaf.pair P.family b s) (ordinaryPoint U x) =
      realSections.map (SplitSheaf.pair P.family b t) (ordinaryPoint U x)) :
    SplitSheaf.pair P.family b s = SplitSheaf.pair P.family b t := by
  apply congrArg (SplitSheaf.pair P.family b)
  apply sections_eq_of_difference_one P b s t
  apply (ordinaryHomLabelEquiv G U).injective
  apply LocallyConstant.ext
  intro x
  rw [ordinaryHomLabelEquiv_one]
  apply total_smul_eq_self P _ ((totalPointEquiv P).symm
    (realSections.map (SplitSheaf.pair P.family b s) (ordinaryPoint U x)))
  exact (sectionDifference_point_action P b s t _ _ rfl rfl (ordinaryPoint U x) _
    (SmoothOrdinaryQuotient.homLabel_point U _ x)).trans
      (congrArg (totalPointEquiv P).symm (h x).symm)

theorem total_hom_ext {U : Domain} (f g : embedding.obj U ⟶ SplitSheaf.extension P.family)
    (h : ∀ x : Points U, realSections.map f (ordinaryPoint U x) =
      realSections.map g (ordinaryPoint U x)) : f = g := by
  have hb : f ≫ SplitSheaf.p P.family = g ≫ SplitSheaf.p P.family :=
    SmoothManifoldAction.hom_ext _ _ (fun x =>
      congrArg (realSections.map (SplitSheaf.p P.family)) (h x))
  let s := SplitSheaf.readTerm P.family f rfl
  let t := SplitSheaf.readTerm P.family g hb.symm
  have hs : SplitSheaf.pair P.family (f ≫ SplitSheaf.p P.family) s = f := SplitSheaf.pair_read _ _ _
  have ht : SplitSheaf.pair P.family (f ≫ SplitSheaf.p P.family) t = g := SplitSheaf.pair_read _ _ _
  have he : SplitSheaf.pair P.family (f ≫ SplitSheaf.p P.family) s =
      SplitSheaf.pair P.family (f ≫ SplitSheaf.p P.family) t := by
    apply pair_hom_ext P _ s t
    intro x
    exact (congrArg (fun k : embedding.obj U ⟶ SplitSheaf.extension P.family => realSections.map k (ordinaryPoint U x)) hs).trans
      ((h x).trans (congrArg (fun k : embedding.obj U ⟶ SplitSheaf.extension P.family => realSections.map k (ordinaryPoint U x)) ht).symm)
  exact hs.symm.trans (he.trans ht)
def totalShift (g : G) : SplitSheaf.extension P.family ⟶ SplitSheaf.extension P.family := ⟨{
  app U := ↾fun z => P.toAction.totalAct U ((constantLabel G).app U g) z
  naturality {U V} f := by
    apply ConcreteCategory.hom_ext
    intro z
    change P.toAction.totalAct V ((constantLabel G).app V g)
      ((SplitSheaf.extension P.family).obj.map f z) =
      (SplitSheaf.extension P.family).obj.map f (P.toAction.totalAct U ((constantLabel G).app U g) z)
    rw [P.toAction.totalAct_natural]
    have h := NatTrans.naturality_apply (constantLabel G) f g
    exact congrArg (fun a => P.toAction.totalAct V a ((SplitSheaf.extension P.family).obj.map f z)) h }⟩
theorem totalShift_point (g : G) (z : Total P) :
    realSections.map (totalShift P g) (totalPointEquiv P z) = totalPointEquiv P (g • z) := rfl
theorem totalShift_projection (g : G) :
    totalShift P g ≫ SplitSheaf.p P.family = SplitSheaf.p P.family := rfl
theorem pointLift_shift_comp {U V : Domain} (f : U ⟶ V)
    (l : embedding.obj V ⟶ SplitSheaf.extension P.family) (g : G) (x : Points U) :
    realSections.map (embedding.map f ≫ l ≫ totalShift P g) (ordinaryPoint U x) =
      totalPointEquiv P (g • (totalPointEquiv P).symm
        (realSections.map l (ordinaryPoint V ((show EuclideanOpen.Map U V from f) x)))) := by
  have he := (congrArg (totalPointEquiv P) (pointLift_comp P f l x)).symm
  have hh := ((totalPointEquiv P).apply_symm_apply _).symm.trans he
  exact (congrArg (realSections.map (totalShift P g)) hh).trans (totalShift_point P g _)

end SquareKit.SmoothTorsorReconstruction

namespace SquareKit.SmoothTorsorReconstruction
open CategoryTheory ManifoldRealization SmoothOpenSite SmoothManifoldAction EuclideanOpen
open scoped Manifold ContDiff
variable {n : ℕ} {G B : Type} [Group G] [TopologicalSpace B]
  [ChartedSpace (Space n) B] [IsManifold (modelWithCorners n) ∞ B]
variable (P : SheafTorsor.Torsor (locallyConstantGroup G) (object n B))
theorem chart_lifts_compatible {M : Type} (A : Charts M)
    (v : M → realSections.obj (SplitSheaf.extension P.family))
    (k : ∀ i, embedding.obj (A.domain i) ⟶ SplitSheaf.extension P.family)
    (h : ∀ i x, realSections.map (k i) (ordinaryPoint _ x) = v (A.coordinate i x)) :
    A.Compatible k := by
  intro r
  apply total_hom_ext P
  intro x
  have hl := congrArg (realSections.map (k r.first)) (ordinaryPoint_map r.left x)
  have hr := congrArg (realSections.map (k r.second)) (ordinaryPoint_map r.right x)
  exact (hl.trans (h _ _)).trans
    ((congrArg v (r.agreement x)).trans (hr.trans (h _ _)).symm)
end SquareKit.SmoothTorsorReconstruction

namespace SquareKit.SmoothTorsorReconstruction
open CategoryTheory ManifoldRealization SmoothOpenSite SmoothManifoldAction EuclideanOpen
open scoped Manifold ContDiff
variable {m : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (Space m) M] [IsManifold (modelWithCorners m) ∞ M]
theorem chart_recovery_point {F : Sheaf topology Type} (A : ChartFamily m M)
    (k : object m M ⟶ F) (v : M → realSections.obj F)
    (h : ∀ i (x : Points (A.charts.domain i)),
      realSections.map (A.charts.chart i ≫ (atlasIso A).inv ≫ k) (ordinaryPoint _ x) =
        v (chartPoint (A.chart i) x)) (z : M) :
    realSections.map k (pointEquiv.symm z) = v z := by
  obtain ⟨i, x, hx⟩ := A.atlas.covers z
  have hp := chart_eval A i x
  have hh : realSections.map (A.charts.chart i ≫ (atlasIso A).inv) (ordinaryPoint _ x) =
      pointEquiv.symm z := by
    apply pointEquiv.injective
    exact hp.trans (hx.trans (pointEquiv.apply_symm_apply z).symm)
  exact (congrArg (realSections.map k) hh).symm.trans ((h i x).trans (congrArg v hx))
end SquareKit.SmoothTorsorReconstruction

namespace SquareKit.SmoothTorsorReconstruction
open CategoryTheory Opposite ManifoldRealization SmoothManifoldAction SmoothOpenSite
open scoped Manifold ContDiff
variable {n m : ℕ} {G B M : Type} [Group G]
  [TopologicalSpace B] [TopologicalSpace M]
  [ChartedSpace (Space n) B] [ChartedSpace (Space m) M]
  [IsManifold (modelWithCorners n) ∞ B] [IsManifold (modelWithCorners m) ∞ M]
variable (P : SheafTorsor.Torsor (locallyConstantGroup G) (object n B))

theorem manifold_total_hom_ext (f g : object m M ⟶ SplitSheaf.extension P.family)
    (h : ∀ z : realSections.obj (object m M), realSections.map f z = realSections.map g z) :
    f = g := by
  apply (ChartFamily.preferred (n := m) (M := M)).charts.hom_ext
  intro i
  apply total_hom_ext P
  intro x
  exact h (realSections.map ((ChartFamily.preferred (n := m) (M := M)).charts.chart i)
    (ordinaryPoint _ x))

theorem projection_eq_of_points (k : object m M ⟶ SplitSheaf.extension P.family)
    (q : M → B) (hq : ContMDiff (modelWithCorners m) (modelWithCorners n) ∞ q)
    (hpoint : ∀ z : M,
      pointEquiv (realSections.map (k ≫ SplitSheaf.p P.family) (pointEquiv.symm z)) = q z) :
    k ≫ SplitSheaf.p P.family = ManifoldRealization.map q hq := by
  have h : reconstruct (k ≫ SplitSheaf.p P.family) = q := funext hpoint
  rw [← map_reconstruct (k ≫ SplitSheaf.p P.family)]
  simp only [h]
end SquareKit.SmoothTorsorReconstruction
