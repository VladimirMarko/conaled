import SquareKit.Internal.PathTransport.ComparisonDiagonal
import SquareKit.Internal.PathTransport.ComparisonInterpretation

/-! The diagonal interpretation preserves the complete existing source algebra.
J preservation is reflected through both constructed projection model maps. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.GroupoidModel.Comparison
open CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u

def diagonalStructuralMap (C : Grpd.{u,u}) (B : C ⥤ Type u) :
    Typed.StructuralMap (Instance.structuralModel C B) (structuralModel (Signature.diagonal C B)) where
  context := Context.diagonal
  family := Family.diagonal
  mapTm s := Section.diagonal s.down
  substitution σ := Substitution.diagonal σ.down
  empty := rfl
  extend A := (Family.diagonal_extend A).symm
  id _ := rfl
  comp _ _ := rfl
  subTy A σ := (Family.diagonal_reindex A σ.down).symm
  subTm s σ := Section.hext (Family.diagonal_reindex _ _).symm HEq.rfl HEq.rfl
  weaken A := Substitution.context_hext rfl (Family.diagonal_extend A).symm HEq.rfl HEq.rfl
  mapVariable A := Section.context_hext (Family.diagonal_extend A).symm
    (by
      apply (heq_of_eq (@Family.diagonal_reindex _ (@Grpd.of (Extend A) Groupoid.ofIsGroupoid) A (GroupoidModel.weaken A)).symm).trans
      exact Family.reindex_heq rfl (Family.diagonal_extend A).symm HEq.rfl
        (Substitution.context_hext rfl (Family.diagonal_extend A).symm HEq.rfl HEq.rfl)) HEq.rfl HEq.rfl
  identity A x y := (Family.diagonal_identity A x.down y.down).symm
  reflexivity A x := Section.hext (Family.diagonal_identity A x.down x.down).symm HEq.rfl HEq.rfl

theorem diagonal_left (C : Grpd.{u,u}) (B : C ⥤ Type u) :
    Typed.StructuralMap.compose (leftProjection (Signature.diagonal C B)) (diagonalStructuralMap C B) =
      Typed.StructuralMap.identityMap (Instance.structuralModel C B) := rfl

theorem diagonal_right (C : Grpd.{u,u}) (B : C ⥤ Type u) :
    Typed.StructuralMap.compose (rightProjection (Signature.diagonal C B)) (diagonalStructuralMap C B) =
      Typed.StructuralMap.identityMap (Instance.structuralModel C B) := rfl


private theorem projected_j {M N P : Typed.Model.{u}}
    (F : Typed.StructuralMap M.toStructuralModel N.toStructuralModel)
    (G : Typed.ModelMap N P) {Γ n} (A : M.Family Γ) (x : M.Section Γ A)
    (T : Typed.StructuralModel.Telescope M.toStructuralModel (M.toStructuralModel.pathContext A x) n)
    (D : M.Family (Typed.StructuralModel.Telescope.total M.toStructuralModel T))
    (d : M.Section _ (M.subTy D (M.toStructuralModel.rootTail A x T))) :
    HEq (G.mapTm (N.j (F.family A) (F.mapTm x) (F.pathTelescope A x T)
      (F.jMotive A x T D) (F.jBranch A x T D d)))
      (P.j ((Typed.StructuralMap.compose G.toStructuralMap F).family A)
        ((Typed.StructuralMap.compose G.toStructuralMap F).mapTm x)
        ((Typed.StructuralMap.compose G.toStructuralMap F).pathTelescope A x T)
        ((Typed.StructuralMap.compose G.toStructuralMap F).jMotive A x T D)
        ((Typed.StructuralMap.compose G.toStructuralMap F).jBranch A x T D d)) := by
  apply (G.mapJ _ _ _ _ _).trans
  apply P.j_heq rfl HEq.rfl HEq.rfl
    (heq_of_eq (Typed.StructuralMap.pathTelescope_compose G.toStructuralMap F A x T).symm)
  · apply (cast_heq _ _).trans
    apply HEq.trans _ (cast_heq _ _).symm
    exact G.family_heq (F.pathTelescope_total A x T).symm (cast_heq _ _)
  · apply (G.jBranch_heq _ _ _ _ _).trans
    apply HEq.trans _ (Typed.StructuralMap.jBranch_heq _ A x T D d).symm
    exact G.section_heq (F.rootTelescope_total A x T).symm (F.jBranch_type A x T D).symm
      (F.jBranch_heq A x T D d)


private theorem projected_j_identity {M N : Typed.Model.{u}}
    (F : Typed.StructuralMap M.toStructuralModel N.toStructuralModel)
    (G : Typed.ModelMap N M)
    (h : Typed.StructuralMap.compose G.toStructuralMap F = Typed.StructuralMap.identityMap M.toStructuralModel) {Γ n} (A : M.Family Γ) (x : M.Section Γ A)
    (T : Typed.StructuralModel.Telescope M.toStructuralModel (M.toStructuralModel.pathContext A x) n)
    (D : M.Family (Typed.StructuralModel.Telescope.total M.toStructuralModel T))
    (d : M.Section _ (M.subTy D (M.toStructuralModel.rootTail A x T))) :
    HEq (G.mapTm (N.j (F.family A) (F.mapTm x) (F.pathTelescope A x T)
      (F.jMotive A x T D) (F.jBranch A x T D d)))
      (M.j A x T D d) := by
  have hp := projected_j F G A x T D d
  rw [h] at hp
  exact hp.trans ((Typed.ModelMap.identityMap M).mapJ A x T D d).symm

private theorem projected_j_retract {M N : Typed.Model.{u}}
    (F : Typed.StructuralMap M.toStructuralModel N.toStructuralModel)
    (G : Typed.ModelMap N M)
    (h : Typed.StructuralMap.compose G.toStructuralMap F = Typed.StructuralMap.identityMap M.toStructuralModel) {Γ n} (A : M.Family Γ) (x : M.Section Γ A)
    (T : Typed.StructuralModel.Telescope M.toStructuralModel (M.toStructuralModel.pathContext A x) n)
    (D : M.Family (Typed.StructuralModel.Telescope.total M.toStructuralModel T))
    (d : M.Section _ (M.subTy D (M.toStructuralModel.rootTail A x T))) :
    HEq (G.mapTm (F.mapTm (M.j A x T D d)))
      (G.mapTm (N.j (F.family A) (F.mapTm x) (F.pathTelescope A x T)
        (F.jMotive A x T D) (F.jBranch A x T D d))) := by
  have hp := projected_j_identity F G h A x T D d
  apply HEq.trans _ hp.symm
  change HEq ((Typed.StructuralMap.compose G.toStructuralMap F).mapTm _) _
  rw [h]
  rfl

theorem Section.projections_hext {Γ Δ : Context.{u}} (hΓ : Γ = Δ)
    {A : Family Γ} {B : Family Δ} (hA : HEq A B)
    {s : Section A} {t : Section B}
    (hl : HEq (ULift.up.{u+1} s.left) (ULift.up.{u+1} t.left))
    (hr : HEq (ULift.up.{u+1} s.right) (ULift.up.{u+1} t.right)) : HEq s t := by
  cases hΓ; cases eq_of_heq hA
  apply heq_of_eq
  apply Section.ext
  · exact congrArg ULift.down (eq_of_heq hl)
  · exact congrArg ULift.down (eq_of_heq hr)

theorem model_projections_hext (S : Signature.{u}) {Γ Δ : Context.{u}} (hΓ : Γ = Δ)
    {A : Family Γ} {B : Family Δ} (hA : HEq A B)
    {s : Section A} {t : Section B}
    (hl : HEq ((leftModelMap S).mapTm s) ((leftModelMap S).mapTm t))
    (hr : HEq ((rightModelMap S).mapTm s) ((rightModelMap S).mapTm t)) : HEq s t :=
  Section.projections_hext hΓ hA hl hr

private def reflectedModelMap {M N : Typed.Model.{u}}
    (F : Typed.StructuralMap M.toStructuralModel N.toStructuralModel)
    (G H : Typed.ModelMap N M)
    (hG : Typed.StructuralMap.compose G.toStructuralMap F = Typed.StructuralMap.identityMap M.toStructuralModel)
    (hH : Typed.StructuralMap.compose H.toStructuralMap F = Typed.StructuralMap.identityMap M.toStructuralModel)
    (reflect : ∀ {Γ Δ : N.Context} (_hΓ : Γ = Δ) {A : N.Family Γ} {B : N.Family Δ}
      (_hA : HEq A B) {s : N.Section Γ A} {t : N.Section Δ B},
      HEq (G.mapTm s) (G.mapTm t) → HEq (H.mapTm s) (H.mapTm t) → HEq s t) :
    Typed.ModelMap M N where
  toStructuralMap := F
  mapJ A x T D d := reflect (F.pathTelescope_total A x T) (cast_heq _ _).symm
    (projected_j_retract F G hG A x T D d) (projected_j_retract F H hH A x T D d)

def diagonalModelMap (C : Grpd.{u,u}) (B : C ⥤ Type u) :
    Typed.ModelMap (Instance.fullModel C B) (fullModel (Signature.diagonal C B)) :=
  reflectedModelMap (diagonalStructuralMap C B)
    (leftModelMap (Signature.diagonal C B)) (rightModelMap (Signature.diagonal C B))
    (diagonal_left C B) (diagonal_right C B) (model_projections_hext (Signature.diagonal C B))

def diagonalSignatureMap (C : Grpd.{u,u}) (B : C ⥤ Type u) :
    Typed.SignatureMap (Instance.fullModel C B) (fullModel (Signature.diagonal C B)) where
  toModelMap := diagonalModelMap C B
  base _ := rfl
  fiber x := (Signature.diagonal_fiber B x.down).symm

end SquareKit.Internal.PathTransport.GroupoidModel.Comparison
