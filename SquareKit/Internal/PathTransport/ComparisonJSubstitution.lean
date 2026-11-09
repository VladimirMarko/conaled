import SquareKit.Internal.PathTransport.ComparisonJProjections

noncomputable section
namespace SquareKit.Internal.PathTransport.GroupoidModel.Comparison
open CategoryTheory Typed Typed.StructuralModel
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable (S : Signature.{u})
local notation "M" => structuralModel S

theorem contextualJ_sub_left {Γ Δ : Context.{u}} {n} (A : Family Γ) (x : Section A)
    (T : Telescope M (StructuralModel.pathContext M A x) n) (σ : Substitution Δ Γ)
    (D : Family (Telescope.total M T))
    (d : Section (D.reindex (StructuralModel.rootTail M A x T))) :
    HEq ((leftProjection S).mapTm ((contextualJ S A x T D d).reindex
      (StructuralModel.pathTailMap M A x T σ)))
      ((leftProjection S).mapTm (contextualJ S (A.reindex σ) (x.reindex σ)
        (StructuralModel.pathTail M A x T σ)
        (D.reindex (StructuralModel.pathTailMap M A x T σ))
        (StructuralModel.reindexBranch M A x T σ D d))) := by
  let F := leftProjection S
  let N := Instance.fullModel S.base.left S.leftFiber
  have ht : HEq (F.pathTelescope (A.reindex σ) (x.reindex σ)
      (StructuralModel.pathTail M A x T σ))
      (N.toStructuralModel.pathTail (F.family A) (F.mapTm x)
        (F.pathTelescope A x T) (F.substitution σ)) :=
    (cast_heq _ _).trans (F.pathTail A x T σ)
  have hc := Telescope.total_heq N.toStructuralModel
    ((F.pathContext _ _).trans (N.toStructuralModel.pathContext_heq rfl
      (heq_of_eq (F.subTy A σ)) (F.subTm x σ)))
    (F.pathTail A x T σ)
  apply (F.subTm _ _).trans
  apply (N.toStructuralModel.subTm_heq (F.pathTelescope_total A x T)
    ((F.telescope_total _).trans hc) (cast_heq _ _).symm
    (contextualJ_left S A x T D d) (F.pathTailMap A x T σ)).trans
  apply (N.j_sub _ _ _ _ _ _).trans
  apply HEq.trans _ (contextualJ_left S (A.reindex σ) (x.reindex σ)
    (StructuralModel.pathTail M A x T σ)
    (D.reindex (StructuralModel.pathTailMap M A x T σ))
    (StructuralModel.reindexBranch M A x T σ D d)).symm
  apply HEq.symm
  apply N.j_heq rfl (heq_of_eq (F.subTy A σ)) (F.subTm x σ) ht
  · apply (cast_heq _ _).trans
    apply (heq_of_eq (F.subTy D _)).trans
    exact N.toStructuralModel.subTy_heq (F.pathTelescope_total A x T)
      ((F.telescope_total _).trans hc) (cast_heq _ _).symm (F.pathTailMap A x T σ)
  · exact (F.jBranch_heq _ _ _ _ _).trans (F.reindexBranch A x T σ D d)

theorem contextualJ_sub_right {Γ Δ : Context.{u}} {n} (A : Family Γ) (x : Section A)
    (T : Telescope M (StructuralModel.pathContext M A x) n) (σ : Substitution Δ Γ)
    (D : Family (Telescope.total M T))
    (d : Section (D.reindex (StructuralModel.rootTail M A x T))) :
    HEq ((rightProjection S).mapTm ((contextualJ S A x T D d).reindex
      (StructuralModel.pathTailMap M A x T σ)))
      ((rightProjection S).mapTm (contextualJ S (A.reindex σ) (x.reindex σ)
        (StructuralModel.pathTail M A x T σ)
        (D.reindex (StructuralModel.pathTailMap M A x T σ))
        (StructuralModel.reindexBranch M A x T σ D d))) := by
  let F := rightProjection S
  let N := Instance.fullModel S.base.right S.rightFiber
  have ht : HEq (F.pathTelescope (A.reindex σ) (x.reindex σ)
      (StructuralModel.pathTail M A x T σ))
      (N.toStructuralModel.pathTail (F.family A) (F.mapTm x)
        (F.pathTelescope A x T) (F.substitution σ)) :=
    (cast_heq _ _).trans (F.pathTail A x T σ)
  have hc := Telescope.total_heq N.toStructuralModel
    ((F.pathContext _ _).trans (N.toStructuralModel.pathContext_heq rfl
      (heq_of_eq (F.subTy A σ)) (F.subTm x σ)))
    (F.pathTail A x T σ)
  apply (F.subTm _ _).trans
  apply (N.toStructuralModel.subTm_heq (F.pathTelescope_total A x T)
    ((F.telescope_total _).trans hc) (cast_heq _ _).symm
    (contextualJ_right S A x T D d) (F.pathTailMap A x T σ)).trans
  apply (N.j_sub _ _ _ _ _ _).trans
  apply HEq.trans _ (contextualJ_right S (A.reindex σ) (x.reindex σ)
    (StructuralModel.pathTail M A x T σ)
    (D.reindex (StructuralModel.pathTailMap M A x T σ))
    (StructuralModel.reindexBranch M A x T σ D d)).symm
  apply HEq.symm
  apply N.j_heq rfl (heq_of_eq (F.subTy A σ)) (F.subTm x σ) ht
  · apply (cast_heq _ _).trans
    apply (heq_of_eq (F.subTy D _)).trans
    exact N.toStructuralModel.subTy_heq (F.pathTelescope_total A x T)
      ((F.telescope_total _).trans hc) (cast_heq _ _).symm (F.pathTailMap A x T σ)
  · exact (F.jBranch_heq _ _ _ _ _).trans (F.reindexBranch A x T σ D d)

theorem contextualJ_sub {Γ Δ : Context.{u}} {n} (A : Family Γ) (x : Section A)
    (T : Telescope M (StructuralModel.pathContext M A x) n) (σ : Substitution Δ Γ)
    (D : Family (Telescope.total M T))
    (d : Section (D.reindex (StructuralModel.rootTail M A x T))) :
    HEq ((contextualJ S A x T D d).reindex (StructuralModel.pathTailMap M A x T σ))
      (contextualJ S (A.reindex σ) (x.reindex σ) (StructuralModel.pathTail M A x T σ)
        (D.reindex (StructuralModel.pathTailMap M A x T σ))
        (StructuralModel.reindexBranch M A x T σ D d)) := by
  apply heq_of_eq
  apply Section.ext
  · exact congrArg ULift.down (eq_of_heq (contextualJ_sub_left S A x T σ D d))
  · exact congrArg ULift.down (eq_of_heq (contextualJ_sub_right S A x T σ D d))

/-- The ordinary-groupoid comparison interpretation, including contextual J. -/
def fullModel : Typed.Model.{u+1} where
  toStructuralModel := M
  j := contextualJ S
  j_beta := fun A x T D d => heq_of_eq (contextualJ_beta S A x T D d)
  j_sub := fun A x T D d σ => contextualJ_sub S A x T σ D d

def leftModelMap : Typed.ModelMap (fullModel S)
    (Instance.fullModel S.base.left S.leftFiber) where
  toStructuralMap := leftProjection S
  mapJ := contextualJ_left S

def rightModelMap : Typed.ModelMap (fullModel S)
    (Instance.fullModel S.base.right S.rightFiber) where
  toStructuralMap := rightProjection S
  mapJ := contextualJ_right S

end SquareKit.Internal.PathTransport.GroupoidModel.Comparison
