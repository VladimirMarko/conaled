import Examples.ProperLocalBranches
import Examples.SmoothManifoldAction
import SquareKit.SmoothBranchActionComparison

/-! Ineffective arrows and locally varying labels in the actual branch coproduct. -/
noncomputable section
open CategoryTheory TopologicalSpace
open scoped Manifold ContDiff Orbifolds.FiniteActionPresentation
namespace Examples.SmoothBranchAction
open SquareKit SquareKit.ManifoldRealization SquareKit.EuclideanOpen
open SquareKit.SmoothManifoldAction SquareKit.SmoothBranchRealization
open SquareKit.SmoothBranchActionComparison
open SquareKit.SmoothOpenSite

abbrev S3 := Equiv.Perm (Fin 3)
local instance : TopologicalSpace S3 := ⊥
local instance : DiscreteTopology S3 := ⟨rfl⟩
attribute [local instance] SmoothManifoldAction.trivial

def diagram : Orbifolds.LocalBranches.Diagram (modelWithCorners 1) (modelWithCorners 1)
    (actionSource (d := 1) (G := S3) (M := Space 1)) actionTarget ⊤ ⊤ S3 :=
  SmoothLocalDiffeomorphModel.diagram
  (Orbifolds.FiniteActionPresentation.source (G := S3) (M := Space 1))
  (Orbifolds.FiniteActionPresentation.source_etale (modelWithCorners 1))
  (ProperLocalBranches.finiteActionDiagram (G := S3) (modelWithCorners 1)
    (SmoothManifoldAction.smooth S3) ⊤ ⊤)

def zero (P : Domain) : External.SmoothMap P 1 (⊤ : Opens (Space 1)) :=
  ⟨fun _ => ⟨0, Set.mem_univ _⟩, contMDiff_const⟩

def nativeFamily (P : Domain) (labels : LocallyConstant (Points P) S3) :
    External.Family (G := S3) P (ambientMap (zero P)) (ambientMap (zero P)) :=
  SmoothManifoldAction.family P labels

def family (P : Domain) (labels : LocallyConstant (Points P) S3) :=
  familyBranchEquiv diagram (zero P) (zero P) (SmoothManifoldAction.smooth S3)
    (nativeFamily P labels)

def varying := family SmoothClutching.punctured
  (SmoothOrdinaryComparison.signLabel S3 SmoothManifoldAction.g)

def varyingRegion : External.SmoothMap SmoothClutching.punctured 1 diagram.region :=
  (actionRegionEquiv diagram (zero SmoothClutching.punctured) (zero SmoothClutching.punctured)
    (nativeFamily _ (SmoothOrdinaryComparison.signLabel S3 SmoothManifoldAction.g))).val

theorem varying_as_principal :
    varying.val = principalBranchEquiv diagram SmoothClutching.punctured varyingRegion := rfl

theorem assemble_label (i : S3) (x : diagram.domain i) :
    (diagram.assemble i x).val.1 = i := rfl

/-- The external quotient comparison reaches exactly the same coproduct arrow. -/
theorem quotient_comparison (P : Domain) (labels : LocallyConstant (Points P) S3) :
    chartBranchEquiv diagram (zero P) (zero P) (SmoothManifoldAction.smooth S3)
      (SmoothManifoldAction.arrow P labels) = family P labels := by
  exact congrArg (familyBranchEquiv diagram (zero P) (zero P)
    (SmoothManifoldAction.smooth S3)) (SmoothManifoldAction.recovered_family P labels)

/-- Distinct ineffective labels remain distinct maps into the branch coproduct. -/
theorem ineffective_distinct :
    family (full 1) (LocallyConstant.const _ SmoothManifoldAction.g) ≠
      family (full 1) (LocallyConstant.const _ (1 : S3)) := by
  intro h
  have hf := (familyBranchEquiv diagram (zero (full 1)) (zero (full 1))
    (SmoothManifoldAction.smooth S3)).injective h
  have he := congrArg (fun f => (f.val (realLinePoint 0)).1 0) hf
  change (Equiv.swap (0 : Fin 3) 1) 0 = 0 at he
  norm_num [Equiv.swap_apply_def] at he

/-- Both distinct arrows have identical source and target sections. -/
theorem ineffective_endpoints (labels : LocallyConstant (Points (full 1)) S3) :
    (family (full 1) labels).val ≫ branchSource diagram =
      hat (zero (full 1)).val (zero (full 1)).property ∧
    (family (full 1) labels).val ≫ branchTarget diagram
      (actionTarget_smooth (SmoothManifoldAction.smooth S3)) =
      hat (zero (full 1)).val (zero (full 1)).property :=
  (family (full 1) labels).property

/-- A disconnected principal test has a branch section with no single global label. -/
theorem varying_no_summand (i : S3) :
    ¬ ∃ b : embedding.obj SmoothClutching.punctured ⟶ object 1 (diagram.domain i),
      b ≫ SheafCoproductLocal.inclusion (fun j => object 1 (diagram.domain j)) i = varying.val := by
  intro hb
  rw [varying_as_principal] at hb
  obtain ⟨f, hf⟩ := (principalBranchEquiv_factors_iff diagram varyingRegion i).mp hb
  have hn := congrArg (fun z : diagram.region => z.val.1)
    (hf SmoothOrdinaryComparison.negativePoint)
  have hp' := congrArg (fun z : diagram.region => z.val.1)
    (hf SmoothOrdinaryComparison.positivePoint)
  change i = (if (-1 : ℝ) < 0 then (1 : S3) else SmoothManifoldAction.g) at hn
  change i = (if (1 : ℝ) < 0 then (1 : S3) else SmoothManifoldAction.g) at hp'
  norm_num at hn hp'
  have h0 := congrArg (fun k : S3 => k 0) (hn.symm.trans hp')
  norm_num [SmoothManifoldAction.g, Equiv.swap_apply_def] at h0

end Examples.SmoothBranchAction
