import SquareKit.Internal.DependentJudgments.Sigma.Stability

/-! Strict model maps preserve formation and the constructor. Preservation of
unpacking and dependent elimination is derived from those primitive laws. -/
namespace SquareKit.Internal.DependentJudgments.Sigma
open PathTransport.Typed StructuralModel
universe u v w
set_option backward.isDefEq.respectTransparency false

/-- A displayed family is transported across the existing extension comparison. -/
def displayFamily {M : StructuralModel.{u}} {N : StructuralModel.{v}}
    (F : StructuralMap M N) {Γ} (A : M.Family Γ) (B : M.Family (M.extend Γ A)) :
    N.Family (N.extend (F.context Γ) (F.family A)) :=
  cast (congrArg N.Family (F.extend A)) (F.family B)

theorem displayContext {M : StructuralModel.{u}} {N : StructuralModel.{v}}
    (F : StructuralMap M N) {Γ} (A : M.Family Γ) (B : M.Family (M.extend Γ A)) :
    F.context (M.extend (M.extend Γ A) B) =
      N.extend (N.extend (F.context Γ) (F.family A)) (displayFamily F A B) :=
  (F.extend B).trans (N.extend_heq (F.extend A) (cast_heq _ _).symm)

private theorem sectionType_eq {N : StructuralModel.{v}} {Γ Δ : N.Context}
    {A : N.Family Γ} {B : N.Family Δ} (hΓ : Γ = Δ) (hA : HEq A B) :
    N.Section Γ A = N.Section Δ B := by
  cases hΓ
  cases eq_of_heq hA
  rfl

structure Map {M : StructuralModel.{u}} {N : StructuralModel.{v}}
    (S : Capability M) (T : Capability N) extends StructuralMap M N where
  sigma : ∀ {Γ} (A : M.Family Γ) (B : M.Family (M.extend Γ A)),
    family (S.sigma A B) = T.sigma (family A) (displayFamily toStructuralMap A B)
  pack : ∀ {Γ} (A : M.Family Γ) (B : M.Family (M.extend Γ A)),
    HEq (substitution (S.pack A B)) (T.pack (family A) (displayFamily toStructuralMap A B))

namespace Map
variable {M : StructuralModel.{u}} {N : StructuralModel.{v}}
  {S : Capability M} {T : Capability N} (F : Map S T)
variable {Γ : M.Context} (A : M.Family Γ) (B : M.Family (M.extend Γ A))

theorem sumContext : F.context (M.extend Γ (S.sigma A B)) =
    N.extend (F.context Γ) (T.sigma (F.family A) (displayFamily F.toStructuralMap A B)) :=
  (F.extend _).trans (congrArg (N.extend _) (F.sigma A B))

theorem unpack : HEq (F.substitution (S.unpack A B))
    (T.unpack (F.family A) (displayFamily F.toStructuralMap A B)) := by
  let U := cast (congrArg₂ N.Substitution (F.sumContext A B)
    (displayContext F.toStructuralMap A B)) (F.substitution (S.unpack A B))
  have hU : HEq U (F.substitution (S.unpack A B)) := cast_heq _ _
  have hleft : N.compSub U (T.pack (F.family A) (displayFamily F.toStructuralMap A B)) =
      N.idSub (N.extend (N.extend (F.context Γ) (F.family A))
        (displayFamily F.toStructuralMap A B)) := by
    apply eq_of_heq
    apply (N.comp_heq (displayContext F.toStructuralMap A B).symm
      (F.sumContext A B).symm (displayContext F.toStructuralMap A B).symm
      hU (F.pack A B).symm).trans
    apply (heq_of_eq (F.comp _ _).symm).trans
    rw [S.unpack_pack, F.id]
    exact congr_arg_heq N.idSub (displayContext F.toStructuralMap A B)
  apply hU.symm.trans
  apply heq_of_eq
  calc
    U = N.compSub U (N.compSub (T.pack (F.family A) (displayFamily F.toStructuralMap A B))
        (T.unpack (F.family A) (displayFamily F.toStructuralMap A B))) := by
      rw [T.pack_unpack, N.comp_id_right]
    _ = _ := by rw [← N.comp_assoc, hleft, N.comp_id_left]

/-- The mapped motive, including the comparison of its indexing context. -/
def motive (C : M.Family (M.extend Γ (S.sigma A B))) :
    N.Family (N.extend (F.context Γ) (T.sigma (F.family A) (displayFamily F.toStructuralMap A B))) :=
  cast (congrArg N.Family (F.sumContext A B)) (F.family C)

theorem branch_type (C : M.Family (M.extend Γ (S.sigma A B))) :
    HEq (F.family (M.subTy C (S.pack A B)))
      (N.subTy (F.motive A B C) (T.pack (F.family A) (displayFamily F.toStructuralMap A B))) :=
  (heq_of_eq (F.subTy _ _)).trans
    (N.subTy_heq (F.sumContext A B) (displayContext F.toStructuralMap A B)
      (cast_heq _ _).symm (F.pack A B))

def branch (C : M.Family (M.extend Γ (S.sigma A B)))
    (d : M.Section (M.extend (M.extend Γ A) B) (M.subTy C (S.pack A B))) :
    N.Section (N.extend (N.extend (F.context Γ) (F.family A)) (displayFamily F.toStructuralMap A B))
      (N.subTy (F.motive A B C) (T.pack (F.family A) (displayFamily F.toStructuralMap A B))) :=
  cast (sectionType_eq (displayContext F.toStructuralMap A B)
    (F.branch_type A B C)) (F.mapTm d)

/-- Final dependent-eliminator preservation is a theorem, not a map field. -/
theorem split (C : M.Family (M.extend Γ (S.sigma A B)))
    (d : M.Section (M.extend (M.extend Γ A) B) (M.subTy C (S.pack A B))) :
    HEq (F.mapTm (S.split A B C d))
      (T.split (F.family A) (displayFamily F.toStructuralMap A B)
        (F.motive A B C) (F.branch A B C d)) := by
  apply (F.section_heq rfl (heq_of_eq (S.split_type A B C).symm)
    (S.split_heq A B C d)).trans
  apply (F.subTm _ _).trans
  apply HEq.trans _ (T.split_heq _ _ _ _).symm
  exact N.subTm_heq (displayContext F.toStructuralMap A B) (F.sumContext A B)
    (F.branch_type A B C) (cast_heq _ _).symm (F.unpack A B)

def identityMap (S : Capability M) : Map S S where
  toStructuralMap := StructuralMap.identityMap M
  sigma _ _ := rfl
  pack _ _ := HEq.rfl

variable {P : StructuralModel.{w}} {U : Capability P}

theorem display_comp (G : StructuralMap N P) (F : StructuralMap M N)
    {Γ} (A : M.Family Γ) (B : M.Family (M.extend Γ A)) :
    displayFamily G (F.family A) (displayFamily F A B) =
      displayFamily (G.compose F) A B := by
  apply eq_of_heq
  apply (cast_heq _ _).trans
  apply HEq.trans _ (cast_heq _ _).symm
  exact G.family_heq (F.extend A).symm (cast_heq _ _)

def compose (G : Map T U) (F : Map S T) : Map S U where
  toStructuralMap := G.toStructuralMap.compose F.toStructuralMap
  sigma A B := by
    change G.family (F.family (S.sigma A B)) = _
    rw [F.sigma, G.sigma, display_comp]
    rfl
  pack A B := by
    change HEq (G.substitution (F.substitution (S.pack A B))) _
    apply (G.substitution_heq (F.sumContext A B)
      (displayContext F.toStructuralMap A B) (F.pack A B)).trans
    apply (G.pack _ _).trans
    rw [display_comp]
    rfl

@[simp] theorem compose_identity (F : Map S T) : compose (identityMap T) F = F := by
  cases F; rfl

@[simp] theorem identity_compose (F : Map S T) : compose F (identityMap S) = F := by
  cases F; rfl

theorem compose_assoc {Q : StructuralModel} {V : Capability Q}
    (H : Map U V) (G : Map T U) (F : Map S T) :
    compose (compose H G) F = compose H (compose G F) := by
  cases F; cases G; cases H; rfl

end Map
end SquareKit.Internal.DependentJudgments.Sigma
