import SquareKit.SmoothBundleTargetMaps
import SquareKit.SmoothTorsorReconstructionRecovery
/-! Recover ordinary smooth equivariant targets from quotient objects, using the
constructed total manifold and the existing manifold full-faithfulness bridge. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace SquareKit.SmoothTorsorReconstruction
open CategoryTheory Opposite ManifoldRealization SmoothManifoldAction SmoothOpenSite
open scoped Manifold ContDiff
variable {n d : ℕ} {G B E M : Type} [Group G] [MulAction G E] [MulAction G M]
  [TopologicalSpace G] [DiscreteTopology G]
  [TopologicalSpace B] [TopologicalSpace E] [TopologicalSpace M]
  [ChartedSpace (Space n) B] [ChartedSpace (Space n) E] [ChartedSpace (Space d) M]
  [IsManifold (modelWithCorners n) ∞ B] [IsManifold (modelWithCorners n) ∞ E] [IsManifold (modelWithCorners d) ∞ M]
variable (smoothAction : ∀ g : G, ContMDiff (modelWithCorners d) (modelWithCorners d) ∞ (fun x : M => g • x))
variable (Q : SmoothPrincipalBundle.Bundle (n := n) (G := G) (B := B) (E := E))
variable (R : SheafActionQuotient.Object (representation smoothAction).action (object n B))
variable (e : SheafTorsor.Arrow Q.realizedTorsor R.torsor)

def targetRecoveryMap : object n E ⟶ object d M :=
  Q.realizedTotalIso.inv ≫ (R.transfer e).totalMap

theorem targetRecoveryMap_total : Q.realizedTotalIso.hom ≫ targetRecoveryMap smoothAction Q R e =
    SplitSheaf.totalMap e.iso.hom ≫ R.totalMap := by
  simp only [targetRecoveryMap, Iso.hom_inv_id_assoc]
  rfl

theorem targetRecoveryMap_value (x : (object n B).obj.Elements)
    (p : Q.realizedTorsor.family.family.obj x) :
    (targetRecoveryMap smoothAction Q R e).hom.app x.obj
      (Q.realizedTotalIso.hom.hom.app x.obj ⟨x.val,p⟩) = R.value x (e.iso.hom.app x p) :=
  congrArg (fun k => k.hom.app x.obj ⟨x.val,p⟩) (targetRecoveryMap_total smoothAction Q R e)

theorem targetRecoveryMap_intertwines (g : G) :
    (representation Q.smooth_action).map g ≫ targetRecoveryMap smoothAction Q R e =
      targetRecoveryMap smoothAction Q R e ≫ (representation smoothAction).map g := by
  apply (cancel_epi Q.realizedTotalIso.hom).mp
  ext U z
  rcases z with ⟨b,p⟩
  let x := (object n B).obj.elementsMk U b
  let a := (constantLabel G).app U g
  have he := Q.realizedTotalIso_equivariant x a p
  rw [SmoothConstantAction.Representation.act_constant] at he
  change (targetRecoveryMap smoothAction Q R e).hom.app U
      (((representation Q.smooth_action).map g).hom.app U
        (Q.realizedTotalIso.hom.hom.app U ⟨b,p⟩)) =
    ((representation smoothAction).map g).hom.app U
      ((targetRecoveryMap smoothAction Q R e).hom.app U
        (Q.realizedTotalIso.hom.hom.app U ⟨b,p⟩))
  rw [← he]
  rw [targetRecoveryMap_value smoothAction Q R e x (Q.realizedTorsor.act x a p),
    targetRecoveryMap_value smoothAction Q R e x p, e.equivariant, R.equivariant]
  exact (representation smoothAction).act_constant U g _

def recoveredTarget : E → M := reconstruct (targetRecoveryMap smoothAction Q R e)

theorem recoveredTarget_smooth : ContMDiff (modelWithCorners n) (modelWithCorners d) ∞ (recoveredTarget smoothAction Q R e) :=
  reconstruct_smooth _

theorem recoveredTarget_map :
    ManifoldRealization.map (recoveredTarget smoothAction Q R e) (recoveredTarget_smooth smoothAction Q R e) =
      targetRecoveryMap smoothAction Q R e := map_reconstruct _

theorem recoveredTarget_equivariant (g : G) (z : E) :
    recoveredTarget smoothAction Q R e (g • z) = g • recoveredTarget smoothAction Q R e z := by
  have hh : recoveredTarget smoothAction Q R e ∘ (fun z : E => g • z) =
      (fun z : M => g • z) ∘ recoveredTarget smoothAction Q R e := by
    apply ManifoldRealization.map_injective (n := n) (m := d)
      ((recoveredTarget_smooth smoothAction Q R e).comp (Q.smooth_action g))
      ((smoothAction g).comp (recoveredTarget_smooth smoothAction Q R e))
    rw [ManifoldRealization.map_comp (fun z : E => g • z) (recoveredTarget smoothAction Q R e)
      (Q.smooth_action g) (recoveredTarget_smooth smoothAction Q R e),
      ManifoldRealization.map_comp (recoveredTarget smoothAction Q R e) (fun z : M => g • z)
      (recoveredTarget_smooth smoothAction Q R e) (smoothAction g), recoveredTarget_map]
    exact targetRecoveryMap_intertwines smoothAction Q R e g
  exact congrFun hh z

def recoveredQuotientArrow : SheafActionQuotient.Arrow
    (Q.realizedQuotient smoothAction (recoveredTarget smoothAction Q R e)
      (recoveredTarget_smooth smoothAction Q R e) (recoveredTarget_equivariant smoothAction Q R e)) R where
  torsorArrow := e
  preserves := by
    apply (SheafActionQuotient.preserves_iff_totalMap
      (P := Q.realizedQuotient smoothAction (recoveredTarget smoothAction Q R e)
        (recoveredTarget_smooth smoothAction Q R e) (recoveredTarget_equivariant smoothAction Q R e))
      (Q := R) e).mpr
    rw [Q.realizedQuotient_totalMap, recoveredTarget_map]
    exact (targetRecoveryMap_total smoothAction Q R e).symm
end SquareKit.SmoothTorsorReconstruction

namespace SquareKit.SmoothTorsorReconstruction
open CategoryTheory ManifoldRealization SmoothOpenSite SmoothManifoldAction
open scoped Manifold ContDiff
variable {n d : ℕ} {G B M : Type} [Group G] [MulAction G M]
  [TopologicalSpace G] [DiscreteTopology G]
  [TopologicalSpace B] [TopologicalSpace M]
  [ChartedSpace (Space n) B] [ChartedSpace (Space d) M]
  [IsManifold (modelWithCorners n) ∞ B] [IsManifold (modelWithCorners d) ∞ M]
variable (smoothAction : ∀ g : G, ContMDiff (modelWithCorners d) (modelWithCorners d) ∞ (fun x : M => g • x))
variable (R : SheafActionQuotient.Object (representation smoothAction).action (object n B))
local instance : ChartedSpace (Space n) (Total R.torsor) := chartedSpace R.torsor
local instance : IsManifold (modelWithCorners n) ∞ (Total R.torsor) := isManifold R.torsor

/-- The target function is reconstructed from the supplied sheaf quotient object. -/
def reconstructedTarget : Total R.torsor → M :=
  recoveredTarget smoothAction (bundle R.torsor) R (reconstructedArrow R.torsor)
theorem reconstructedTarget_smooth : ContMDiff (modelWithCorners n) (modelWithCorners d) ∞ (reconstructedTarget smoothAction R) :=
  recoveredTarget_smooth _ _ _ _
theorem reconstructedTarget_equivariant (g : G) (z : Total R.torsor) :
    reconstructedTarget smoothAction R (g • z) = g • reconstructedTarget smoothAction R z :=
  recoveredTarget_equivariant _ _ _ _ g z

def reconstructedQuotientArrow : SheafActionQuotient.Arrow
    ((bundle R.torsor).realizedQuotient smoothAction (reconstructedTarget smoothAction R)
      (reconstructedTarget_smooth smoothAction R) (reconstructedTarget_equivariant smoothAction R)) R :=
  recoveredQuotientArrow _ _ _ _

theorem reconstructedTarget_map :
    ManifoldRealization.map (reconstructedTarget smoothAction R) (reconstructedTarget_smooth smoothAction R) =
      (reconstructedTotalIso R.torsor).hom ≫ R.totalMap := by
  rw [reconstructedTotalIso_hom]
  change ManifoldRealization.map (recoveredTarget _ _ _ _) _ = _
  rw [recoveredTarget_map]
  apply (cancel_epi (bundle R.torsor).realizedTotalIso.hom).mp
  rw [targetRecoveryMap_total, ← Category.assoc]
  exact congrArg (fun k => k ≫ R.totalMap)
    (recoveryArrow_total R.torsor (bundle R.torsor) _ _ _)
end SquareKit.SmoothTorsorReconstruction
