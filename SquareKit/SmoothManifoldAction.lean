import SquareKit.SmoothManifoldFullFaithfulness
import SquareKit.SmoothOrdinaryQuotient

/-! Actions on interpreted Type-sized boundaryless real manifolds. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory Opposite
open scoped Manifold ContDiff
namespace SquareKit.SmoothManifoldAction
open ManifoldRealization EuclideanOpen SmoothOpenSite SmoothOrdinaryQuotient
variable {d : ℕ} {G M : Type} [Group G] [MulAction G M]
  [TopologicalSpace M] [ChartedSpace (Space d) M] [IsManifold (Model d) ∞ M]

/-- Interpret the supplied action maps; the group laws follow by functoriality. -/
def representation (smoothAction : ∀ g : G, ContMDiff (Model d) (Model d) ∞ (fun x : M => g • x)) :
    SmoothConstantAction.Representation G (object d M) where
  map g := ManifoldRealization.map (fun x => g • x) (smoothAction g)
  one := by
    have h : (fun x : M => (1 : G) • x) = id := funext (one_smul G)
    simp only [h]
    exact map_id
  mul g h := by
    simpa only [Function.comp_def, mul_smul] using
      (map_comp (fun x : M => h • x) (fun x : M => g • x) (smoothAction h) (smoothAction g))

/-- The literal interpretation of a smooth map from an admitted test domain. -/
def hat {U : Domain} (m : ordinaryOpen U → M)
    (hm : ContMDiff (Model U.dimension) (Model d) ∞ m) : embedding.obj U ⟶ object d M :=
  (principalIso U).inv ≫ ManifoldRealization.map m hm

/-- Point detection for manifold-valued maps uses full faithfulness, not a
separation assumption on the manifold. -/
theorem hom_ext {U : Domain} (f g : embedding.obj U ⟶ object d M)
    (h : ∀ x : Points U, f.hom.app (op (op (SmoothPresentationSite.free 0))) (ordinaryPoint U x) =
      g.hom.app (op (op (SmoothPresentationSite.free 0))) (ordinaryPoint U x)) : f = g := by
  apply (cancel_epi (principalIso U).hom).mp
  rw [← map_reconstruct ((principalIso U).hom ≫ f),
      ← map_reconstruct ((principalIso U).hom ≫ g)]
  congr 1
  funext x
  change (ChartFamily.preferred (n := d) (M := M)).charts.realEquiv _
      (f.hom.app _ ((principalIso U).hom.hom.app _ _)) =
    (ChartFamily.preferred (n := d) (M := M)).charts.realEquiv _
      (g.hom.app _ ((principalIso U).hom.hom.app _ _))
  congr 1
  have hx := (realSectionEquiv U).symm_apply_apply
    ((principalIso U).hom.hom.app _
      (((openFamily U).charts.realEquiv (openFamily U).atlas.covers).symm x))
  exact hx ▸ h _

/-- Ordinary points of the interpreted manifold. -/
abbrev pointEquiv :=
  (ChartFamily.preferred (n := d) (M := M)).charts.realEquiv
    (ChartFamily.preferred (n := d) (M := M)).atlas.covers

theorem map_eval {e : ℕ} {N : Type} [TopologicalSpace N]
    [ChartedSpace (Space e) N] [IsManifold (Model e) ∞ N]
    (f : M → N) (hf : ContMDiff (Model d) (Model e) ∞ f)
    (a : SmoothOpenSite.realSections.obj (object d M)) :
    pointEquiv (d := e) (M := N) ((ManifoldRealization.map f hf).hom.app _ a) =
      f (pointEquiv (d := d) (M := M) a) := by
  have h := congrFun (reconstruct_map f hf) (pointEquiv (d := d) (M := M) a)
  change pointEquiv ((ManifoldRealization.map f hf).hom.app _
    (pointEquiv.symm (pointEquiv a))) = f (pointEquiv a) at h
  simpa only [Equiv.symm_apply_apply] using h

theorem principal_eval (U : Domain) (x : Points U) :
    pointEquiv (d := U.dimension) (M := ordinaryOpen U)
      ((principalIso U).inv.hom.app _ (ordinaryPoint U x)) = x := by
  have h := (singleAtlas U).toCharts.realMap_chart (openFamily U).charts
    (singleAtlas U).covers (openFamily U).atlas.covers (fromSingle U).realize () x
  have k := congrFun ((singleAtlas U).toCharts.realMap_realize (openFamily U).charts
    (singleAtlas U).covers (openFamily U).atlas.covers (fromSingle U)) x
  exact h.symm.trans k

theorem hat_eval {U : Domain} (m : ordinaryOpen U → M)
    (hm : ContMDiff (Model U.dimension) (Model d) ∞ m) (x : Points U) :
    pointEquiv (d := d) (M := M) ((hat m hm).hom.app _ (ordinaryPoint U x)) = m x := by
  change pointEquiv ((ManifoldRealization.map m hm).hom.app _
    ((principalIso U).inv.hom.app _ (ordinaryPoint U x))) = _
  rw [map_eval, principal_eval]

/-- Reflection of the actual sheaf action equation, including locally varying labels. -/
theorem onMap_iff
    (smoothAction : ∀ g : G, ContMDiff (Model d) (Model d) ∞ (fun x : M => g • x))
    (U : Domain) (k : embedding.obj U ⟶ locallyConstantGroupSheaf G)
    (m n : ordinaryOpen U → M)
    (hm : ContMDiff (Model U.dimension) (Model d) ∞ m)
    (hn : ContMDiff (Model U.dimension) (Model d) ∞ n) :
    (representation smoothAction).action.onMap k (hat n hn) = hat m hm ↔
      ∀ x, ordinaryHomLabelEquiv G U k x • n x = m x := by
  have eval (x : Points U) : pointEquiv (d := d) (M := M)
      (((representation smoothAction).action.onMap k (hat n hn)).hom.app _ (ordinaryPoint U x)) =
      ordinaryHomLabelEquiv G U k x • n x := by
    change pointEquiv ((representation smoothAction).act _ (k.hom.app _ _) _) = _
    rw [← homLabel_point U k x]
    change pointEquiv ((representation smoothAction).act _ ((constantLabel G).app _ _) _) = _
    rw [SmoothConstantAction.Representation.act_constant]
    change pointEquiv ((ManifoldRealization.map _ (smoothAction _)).hom.app _ _) = _
    rw [map_eval, hat_eval]
  constructor
  · intro h x
    rw [← eval x, h, hat_eval]
  · intro h
    apply hom_ext
    intro x
    apply pointEquiv.injective
    exact (eval x).trans ((h x).trans (hat_eval m hm x).symm)

end SquareKit.SmoothManifoldAction
