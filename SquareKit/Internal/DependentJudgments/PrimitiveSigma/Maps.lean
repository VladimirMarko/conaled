import SquareKit.Internal.DependentJudgments.PrimitiveSigma.Stability
import SquareKit.Internal.DependentJudgments.Sigma.Maps

/-! Formation maps and chosen primitive-eliminator preservation. -/
namespace SquareKit.Internal.DependentJudgments.PrimitiveSigma
open PathTransport.Typed StructuralModel
universe u v w
set_option backward.isDefEq.respectTransparency false

open _root_.SquareKit.Internal.DependentJudgments.Sigma (displayFamily displayContext)

private theorem sectionType_eq {N : StructuralModel.{v}} {Γ Δ : N.Context}
    {A : N.Family Γ} {B : N.Family Δ} (hΓ : Γ = Δ) (hA : HEq A B) :
    N.Section Γ A = N.Section Δ B := by
  cases hΓ
  cases eq_of_heq hA
  rfl

structure FormationMap {M : StructuralModel.{u}} {N : StructuralModel.{v}}
    (S : Capability M) (T : Capability N) extends StructuralMap M N where
  sigma : ∀ {Γ} (A : M.Family Γ) (B : M.Family (M.extend Γ A)),
    family (S.sigma A B) = T.sigma (family A) (displayFamily toStructuralMap A B)
  pack : ∀ {Γ} (A : M.Family Γ) (B : M.Family (M.extend Γ A)),
    HEq (substitution (S.pack A B)) (T.pack (family A) (displayFamily toStructuralMap A B))

namespace FormationMap
variable {M : StructuralModel.{u}} {N : StructuralModel.{v}}
  {S : Capability M} {T : Capability N} (F : FormationMap S T)
variable {Γ : M.Context} (A : M.Family Γ) (B : M.Family (M.extend Γ A))

theorem sumContext : F.context (M.extend Γ (S.sigma A B)) =
    N.extend (F.context Γ) (T.sigma (F.family A) (displayFamily F.toStructuralMap A B)) :=
  (F.extend _).trans (congrArg (N.extend _) (F.sigma A B))

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

def identityMap (S : Capability M) : FormationMap S S where
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

def compose (G : FormationMap T U) (F : FormationMap S T) : FormationMap S U where
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

@[simp] theorem compose_identity (F : FormationMap S T) : compose (identityMap T) F = F := by
  cases F; rfl

@[simp] theorem identity_compose (F : FormationMap S T) : compose F (identityMap S) = F := by
  cases F; rfl

theorem compose_assoc {Q : StructuralModel} {V : Capability Q}
    (H : FormationMap U V) (G : FormationMap T U) (F : FormationMap S T) :
    compose (compose H G) F = compose H (compose G F) := by
  cases F; cases G; cases H; rfl

end FormationMap
/-- Preservation of a chosen primitive eliminator is required separately from
formation and introduction. It cannot be derived using strong split uniqueness. -/
structure Map {M : StructuralModel.{u}} {N : StructuralModel.{v}}
    (S : Capability M) (T : Capability N) extends FormationMap S T where
  split : ∀ {Γ} (A : M.Family Γ) (B : M.Family (M.extend Γ A))
    (C : M.Family (M.extend Γ (S.sigma A B)))
    (d : M.Section (M.extend (M.extend Γ A) B) (M.subTy C (S.pack A B))),
    HEq (mapTm (S.split A B C d))
      (T.split (family A) (displayFamily toStructuralMap A B)
        (toFormationMap.motive A B C) (toFormationMap.branch A B C d))

namespace Map
variable {M : StructuralModel.{u}} {N : StructuralModel.{v}}

/-- Strong maps recover the chosen eliminator law without an extra caller proof. -/
abbrev ofStrong {S : Sigma.Capability M} {T : Sigma.Capability N} (F : Sigma.Map S T) :
    Map (PrimitiveSigma.ofStrong S) (PrimitiveSigma.ofStrong T) where
  toStructuralMap := F.toStructuralMap
  sigma := F.sigma
  pack := F.pack
  split := F.split

variable {S : Capability M} {T : Capability N}

def identityMap (S : Capability M) : Map S S where
  toFormationMap := FormationMap.identityMap S
  split _ _ _ _ := HEq.rfl

variable {P : StructuralModel.{w}} {U : Capability P}

def compose (G : Map T U) (F : Map S T) : Map S U where
  toFormationMap := G.toFormationMap.compose F.toFormationMap
  split A B C d := by
    apply (G.section_heq (F.toFormationMap.sumContext A B)
      (cast_heq _ _).symm (F.split A B C d)).trans
    apply (G.split _ _ _ _).trans
    apply U.split_congr _ _ rfl HEq.rfl (heq_of_eq (FormationMap.display_comp _ _ _ _))
    · apply (cast_heq _ _).trans
      apply HEq.trans _ (cast_heq _ _).symm
      exact G.family_heq (F.toFormationMap.sumContext A B).symm (cast_heq _ _)
    · apply (cast_heq _ _).trans
      apply HEq.trans _ (cast_heq _ _).symm
      exact G.section_heq (displayContext F.toStructuralMap A B).symm
        (F.toFormationMap.branch_type A B C).symm (cast_heq _ _)

end Map

end SquareKit.Internal.DependentJudgments.PrimitiveSigma
