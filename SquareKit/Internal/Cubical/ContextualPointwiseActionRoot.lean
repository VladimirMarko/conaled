import SquareKit.Internal.Cubical.ContextualPointwiseAction
import SquareKit.Internal.Cubical.IdentityMapSubstitution
import SquareKit.Internal.DependentJudgments.PathFamilyConjugationSemantics

/-! Pointwise action has the exact selected reflexive branch of ordinary J-action. -/
noncomputable section
namespace SquareKit.Cubical.Contextual
open CategoryTheory Presheaf SquareKit.Internal.PathTransport.Typed
open SquareKit.Internal.DependentJudgments.Contextual.DerivedSemantics
set_option backward.isDefEq.respectTransparency false
universe u
variable (Base : LawfulFamily terminal.{u}) (Fiber : LawfulFamily (total Base.family))
local notation "M" => model Base Fiber
variable {Γ : Presheaf.Context.{u}} (A C : LawfulFamily Γ)
  (t : Term (reindex C.family (projection A.family))) (x : Term A.family)

private theorem convert_reindex_heq {Γ Δ : Presheaf.Context.{u}} {A B : Family Γ}
    (e : A = B) (s : Term A) (σ : Δ ⟶ Γ) : HEq ((s.convert e).reindex σ) (s.reindex σ) := by
  cases e; rfl
private theorem cast_down {Δ : Presheaf.Context.{u}} {D E : LawfulFamily Δ}
    (h : D = E) (s : ULift.{u+1} (Term D.family)) :
    HEq ((cast (congrArg (fun F : LawfulFamily Δ => ULift.{u+1} (Term F.family)) h) s).down) s.down := by
  cases h; rfl
private theorem refl_congr {Δ : Presheaf.Context.{u}} {D : Family Δ} {a b : Term D}
    (e : a = b) : HEq (normalizedIdentityRefl a) (normalizedIdentityRefl b) := by cases e; rfl
private theorem up_heq {X Y : Type u} {a : X} {b : Y}
    (h : HEq a b) : HEq (ULift.up.{u+1} a) (ULift.up.{u+1} b) := by cases h; rfl

theorem pointwiseInput_root :
    HEq ((pointwiseInput Base Fiber A x).reindex ((M).toStructuralModel.rootSub A ⟨x⟩).down)
      (normalizedIdentityRefl x) := by
  exact (convert_reindex_heq _ (generic (actionPathFamily Base Fiber A x).family)
    ((M).toStructuralModel.rootSub A ⟨x⟩).down).trans
    (cast_down ((M).toStructuralModel.pathFamily_root A ⟨x⟩).symm ⟨normalizedIdentityRefl x⟩)

theorem pointwiseResult_root : HEq
    ((pointwiseResult Base Fiber A C t x).reindex ((M).toStructuralModel.rootSub A ⟨x⟩).down)
    (normalizedIdentityRefl (x.map (functionMap A C t))) := by
  let σ := ((M).toStructuralModel.rootSub A ⟨x⟩).down
  have h := normalizedIdentityMap_reindex (pointwiseMap Base Fiber A C t x)
    (x.reindex (actionProjection Base Fiber A x))
    ((generic A.family).reindex (projection (actionPathFamily Base Fiber A x).family)) σ
    (pointwiseInput Base Fiber A x)
  have hi := pointwiseInput_root Base Fiber A x
  have hc := Term.convert_heq
    (normalizedIdentity_reindex (reindex A.family (actionProjection Base Fiber A x))
      (x.reindex (actionProjection Base Fiber A x))
      ((generic A.family).reindex (projection (actionPathFamily Base Fiber A x).family)) σ)
    ((pointwiseInput Base Fiber A x).reindex σ)
  have hi' := eq_of_heq (hc.trans hi)
  rw [hi'] at h
  exact (Term.convert_heq _ _).symm.trans ((heq_of_eq h).trans
    (heq_of_eq (normalizedIdentityMap_refl (functionMap A C t) x)))

theorem pointwiseApSection_root :
    HEq ((M).subTm (pointwiseApSection Base Fiber A C t x) ((M).toStructuralModel.rootSub A ⟨x⟩))
      ((M).reflexivity C (ordinaryApply M A C ⟨t⟩ ⟨x⟩)) := by
  apply up_heq
  apply (convert_reindex_heq (pointwiseMotive_eq Base Fiber A C t x).symm
    (pointwiseResult Base Fiber A C t x) ((M).toStructuralModel.rootSub A ⟨x⟩).down).trans
  apply (pointwiseResult_root Base Fiber A C t x).trans
  exact refl_congr (ordinaryApply_down Base Fiber A C t x).symm

end SquareKit.Cubical.Contextual
