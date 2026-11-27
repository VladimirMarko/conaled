import Examples.ProperLocalBranches
import Examples.SmoothTransverseRealization
import SquareKit.SmoothBranchRealization

/-! Full-section controls for the canonical branch coproduct. -/
noncomputable section
open CategoryTheory Opposite TopologicalSpace
open scoped Manifold ContDiff
namespace Examples.SmoothBranchRealization
open SquareKit SquareKit.ManifoldRealization SquareKit.SmoothPresentationSite
open SquareKit.SmoothGeometricKL
open SquareKit.SmoothBranchRealization

def unit := ProperLocalBranches.unitDiagram (modelWithCorners 1)
  (⊤ : Opens (Space 1)) ⊤

def unitCoordinates : Diffeomorph (modelWithCorners 1) (modelWithCorners 1)
    (Space 1) unit.region ∞ where
  toFun x := ⟨x, Set.mem_univ _, Set.mem_univ _⟩
  invFun := Subtype.val
  left_inv _ := rfl
  right_inv _ := rfl
  contMDiff_toFun := (ContMDiff.subtypeVal_comp_iff unit.region _).mp contMDiff_id
  contMDiff_invFun := contMDiff_subtype_val

/-- The unit presentation's branch coordinates recover the full smooth line sheaf. -/
def unitIso : object 1 (Space 1) ≅ branches unit :=
  diffeomorphIso unitCoordinates ≪≫ (assemblyIso unit).symm

def readCoordinate : branches unit ⟶ SmoothOpenSite.scalarPower 1 :=
  unitIso.inv ≫ (SmoothTransverseRealization.fullSpaceIso 1).hom

abbrev stage := SmoothCoordinatePullbacks.stage
abbrev d := SmoothCoordinatePullbacks.d

/-- A nonzero nilpotent section is retained by the branch coproduct. -/
def nilpotentBranch : (branches unit).obj.obj (atStage stage) :=
  unitIso.hom.hom.app (atStage stage)
    ((SmoothTransverseRealization.fullSpaceIso 1).inv.hom.app (atStage stage) (fun _ => d))

theorem nilpotentBranch_coordinate :
    readCoordinate.hom.app (atStage stage) nilpotentBranch = (fun _ => d) := by
  change (unitIso.hom ≫ unitIso.inv ≫
    (SmoothTransverseRealization.fullSpaceIso 1).hom).hom.app (atStage stage) _ = _
  rw [Iso.hom_inv_id_assoc]
  exact congrArg (fun k : SmoothOpenSite.scalarPower 1 ⟶ SmoothOpenSite.scalarPower 1 =>
    k.hom.app (atStage stage) (fun _ => d))
    (SmoothTransverseRealization.fullSpaceIso 1).inv_hom_id

theorem nilpotentBranch_not_real (r : ℝ) :
    readCoordinate.hom.app (atStage stage) nilpotentBranch 0 ≠
      algebraMap ℝ (Carrier stage) r := by
  rw [nilpotentBranch_coordinate]
  intro h
  have hk := congrArg (smoothMap SmoothCoordinatePullbacks.kill) h
  rw [SmoothCoordinatePullbacks.kill_d, SmoothAlgebra.Hom.map_scalar] at hk
  exact SmoothCoordinatePullbacks.d_nonzero (h.trans hk.symm)

/-- Reading the source endpoint agrees with the full line coordinate. -/
theorem unit_source_coordinate :
    branchSource unit ≫ map (Subtype.val : (⊤ : Opens (Space 1)) → Space 1)
      contMDiff_subtype_val ≫ (SmoothTransverseRealization.fullSpaceIso 1).hom =
      readCoordinate := by
  apply (cancel_epi unitIso.hom).mp
  change (map unitCoordinates unitCoordinates.contMDiff_toFun ≫ decompose unit) ≫ _ = _
  simp only [Category.assoc, decompose_source_assoc unit contMDiff_id, source]
  simp only [← Category.assoc, ← map_comp]
  have hid : ((Subtype.val : (⊤ : Opens (Space 1)) → Space 1) ∘ unit.source) ∘ unitCoordinates = id := rfl
  simp only [hid, map_id, Category.id_comp]
  symm
  change (unitIso.hom ≫ unitIso.inv ≫ (SmoothTransverseRealization.fullSpaceIso 1).hom) = _
  rw [Iso.hom_inv_id_assoc]

theorem nilpotentBranch_endpoints :
    (branchSource unit ≫ map (Subtype.val : (⊤ : Opens (Space 1)) → Space 1)
      contMDiff_subtype_val ≫ (SmoothTransverseRealization.fullSpaceIso 1).hom).hom.app
        (atStage stage) nilpotentBranch 0 = d ∧
    branchTarget unit contMDiff_id = branchSource unit := by
  constructor
  · rw [unit_source_coordinate, nilpotentBranch_coordinate]
  · rfl

theorem nilpotentBranch_restrict (r : stage ⟶ stage) :
    readCoordinate.hom.app (atStage stage)
      ((branches unit).obj.map (stageMap r) nilpotentBranch) 0 =
      smoothMap r d := by
  rw [NatTrans.naturality_apply, nilpotentBranch_coordinate]
  rfl

theorem nilpotentBranch_kill_changes :
    (branches unit).obj.map (stageMap SmoothCoordinatePullbacks.kill) nilpotentBranch ≠
      nilpotentBranch := by
  intro h
  have he := nilpotentBranch_restrict SmoothCoordinatePullbacks.kill
  rw [h, nilpotentBranch_coordinate, SmoothCoordinatePullbacks.kill_d] at he
  exact SmoothCoordinatePullbacks.d_nonzero he

/-- Assembly and decomposition retain this same infinitesimal section. -/
theorem nilpotentBranch_roundtrip :
    (stageEquiv unit (op stage))
      ((assembly unit).hom.app (atStage stage) nilpotentBranch) = nilpotentBranch :=
  (stageEquiv unit (op stage)).apply_symm_apply nilpotentBranch

/-- The comparison follows the nonidentity stage map on the full section. -/
theorem nilpotentBranch_comparison_restrict :
    (stageEquiv unit (op stage))
      ((arrowObject unit).obj.map (stageMap SmoothCoordinatePullbacks.kill)
        ((assembly unit).hom.app (atStage stage) nilpotentBranch)) =
      (branches unit).obj.map (stageMap SmoothCoordinatePullbacks.kill) nilpotentBranch := by
  rw [stageEquiv_restrict, nilpotentBranch_roundtrip]

end Examples.SmoothBranchRealization
