import SquareKit.Internal.DependentJudgments.Sigma.Capability

/-! Dependent sums with primitive dependent elimination and beta. Projection
operations and their laws are derived; no repacking equality is assumed. -/
namespace SquareKit.Internal.DependentJudgments.PrimitiveSigma
open PathTransport.Typed StructuralModel
set_option backward.isDefEq.respectTransparency false
universe u

structure Capability (M : StructuralModel.{u}) where
  sigma : {Γ : M.Context} → (A : M.Family Γ) → M.Family (M.extend Γ A) → M.Family Γ
  pack : ∀ {Γ} (A : M.Family Γ) (B : M.Family (M.extend Γ A)),
    M.Substitution (M.extend (M.extend Γ A) B) (M.extend Γ (sigma A B))
  pack_over : ∀ {Γ} (A : M.Family Γ) (B : M.Family (M.extend Γ A)),
    M.compSub (M.weaken Γ (sigma A B)) (pack A B) =
      M.compSub (M.weaken Γ A) (M.weaken (M.extend Γ A) B)
  split : ∀ {Γ} (A : M.Family Γ) (B : M.Family (M.extend Γ A))
    (C : M.Family (M.extend Γ (sigma A B))),
    M.Section (M.extend (M.extend Γ A) B) (M.subTy C (pack A B)) →
      M.Section (M.extend Γ (sigma A B)) C
  split_beta : ∀ {Γ} (A : M.Family Γ) (B : M.Family (M.extend Γ A))
    (C : M.Family (M.extend Γ (sigma A B)))
    (d : M.Section (M.extend (M.extend Γ A) B) (M.subTy C (pack A B))),
    HEq (M.subTm (split A B C d) (pack A B)) d

namespace Capability
variable {M : StructuralModel.{u}} (S : Capability M)
variable {Γ : M.Context} (A : M.Family Γ) (B : M.Family (M.extend Γ A))

def firstMotive : M.Family (M.extend Γ (S.sigma A B)) :=
  M.subTy A (M.weaken Γ (S.sigma A B))

theorem firstBranch_type :
    M.subTy (M.subTy A (M.weaken Γ A)) (M.weaken (M.extend Γ A) B) =
      M.subTy (S.firstMotive A B) (S.pack A B) := by
  rw [firstMotive, M.subTy_comp, M.subTy_comp, S.pack_over]

def firstBranch : M.Section (M.extend (M.extend Γ A) B)
    (M.subTy (S.firstMotive A B) (S.pack A B)) :=
  cast (congrArg (M.Section _) (S.firstBranch_type A B))
    (M.subTm (M.genericVariable Γ A) (M.weaken (M.extend Γ A) B))

def first : M.Section (M.extend Γ (S.sigma A B)) (S.firstMotive A B) :=
  S.split A B (S.firstMotive A B) (S.firstBranch A B)

theorem first_beta : HEq (M.subTm (S.first A B) (S.pack A B))
    (M.subTm (M.genericVariable Γ A) (M.weaken (M.extend Γ A) B)) :=
  (S.split_beta A B _ _).trans (cast_heq _ _)

def firstMap : M.Substitution (M.extend Γ (S.sigma A B)) (M.extend Γ A) :=
  M.pairSub A (M.weaken Γ (S.sigma A B)) (S.first A B)

theorem firstMap_over : M.compSub (M.weaken Γ A) (S.firstMap A B) =
    M.weaken Γ (S.sigma A B) := M.weaken_pair _ _ _

theorem firstMap_pack : M.compSub (S.firstMap A B) (S.pack A B) =
    M.weaken (M.extend Γ A) B := by
  apply M.pair_ext A
  · rw [← M.comp_assoc, S.firstMap_over, S.pack_over]
  · apply (M.subTm_comp _ _ _).symm.trans
    apply (M.subTm_congr (by rw [M.subTy_comp, M.weaken_pair]) (M.variable_pair _ _ _) _).trans
    exact S.first_beta A B

def secondMotive : M.Family (M.extend Γ (S.sigma A B)) :=
  M.subTy B (S.firstMap A B)

theorem secondBranch_type : M.subTy B (M.weaken (M.extend Γ A) B) =
    M.subTy (S.secondMotive A B) (S.pack A B) := by
  rw [secondMotive, M.subTy_comp, S.firstMap_pack]

def secondBranch : M.Section (M.extend (M.extend Γ A) B)
    (M.subTy (S.secondMotive A B) (S.pack A B)) :=
  cast (congrArg (M.Section _) (S.secondBranch_type A B))
    (M.genericVariable (M.extend Γ A) B)

def second : M.Section (M.extend Γ (S.sigma A B)) (S.secondMotive A B) :=
  S.split A B (S.secondMotive A B) (S.secondBranch A B)

theorem second_beta : HEq (M.subTm (S.second A B) (S.pack A B))
    (M.genericVariable (M.extend Γ A) B) :=
  (S.split_beta A B _ _).trans (cast_heq _ _)

/-- The second component has B pulled back along the derived first projection. -/
def unpack : M.Substitution (M.extend Γ (S.sigma A B)) (M.extend (M.extend Γ A) B) :=
  M.pairSub B (S.firstMap A B) (S.second A B)

theorem unpack_over :
    M.compSub (M.compSub (M.weaken Γ A) (M.weaken (M.extend Γ A) B)) (S.unpack A B) =
      M.weaken Γ (S.sigma A B) := by
  rw [M.comp_assoc, unpack, M.weaken_pair, S.firstMap_over]

theorem unpack_pack : M.compSub (S.unpack A B) (S.pack A B) =
    M.idSub (M.extend (M.extend Γ A) B) := by
  apply M.pair_ext B
  · rw [← M.comp_assoc, unpack, M.weaken_pair, S.firstMap_pack, M.comp_id_right]
  · apply (M.subTm_comp _ _ _).symm.trans
    apply (M.subTm_congr (by rw [M.subTy_comp, M.weaken_pair]) (M.variable_pair _ _ _) _).trans
    exact (S.second_beta A B).trans (M.subTm_id _).symm

def repack : M.Substitution (M.extend Γ (S.sigma A B)) (M.extend Γ (S.sigma A B)) :=
  M.compSub (S.pack A B) (S.unpack A B)

theorem repack_over : M.compSub (M.weaken Γ (S.sigma A B)) (S.repack A B) =
    M.weaken Γ (S.sigma A B) := by
  rw [repack, ← M.comp_assoc, S.pack_over, S.unpack_over]

theorem repack_pack : M.compSub (S.repack A B) (S.pack A B) = S.pack A B := by
  rw [repack, M.comp_assoc, S.unpack_pack, M.comp_id_right]

theorem repacked_type :
    M.subTy (M.subTy (S.sigma A B) (M.weaken Γ (S.sigma A B))) (S.repack A B) =
      M.subTy (S.sigma A B) (M.weaken Γ (S.sigma A B)) := by
  rw [M.subTy_comp, S.repack_over]

/-- Repacking expressed as an element in the same fiber as the given pair. -/
def repacked : M.Section (M.extend Γ (S.sigma A B))
    (M.subTy (S.sigma A B) (M.weaken Γ (S.sigma A B))) :=
  cast (congrArg (M.Section _) (S.repacked_type A B))
    (M.subTm (M.genericVariable Γ (S.sigma A B)) (S.repack A B))

theorem repacked_beta : HEq (M.subTm (S.repacked A B) (S.pack A B))
    (M.subTm (M.genericVariable Γ (S.sigma A B)) (S.pack A B)) := by
  apply (M.subTm_congr (S.repacked_type A B).symm (cast_heq _ _) _).trans
  apply (M.subTm_comp _ _ _).trans
  rw [S.repack_pack]

/-- Object identity, distinct from host equality of substitutions. -/
def etaMotive : M.Family (M.extend Γ (S.sigma A B)) :=
  M.identity (M.subTy (S.sigma A B) (M.weaken Γ (S.sigma A B)))
    (S.repacked A B) (M.genericVariable Γ (S.sigma A B))

theorem etaBranch_type : M.subTy (S.etaMotive A B) (S.pack A B) =
    M.identity (M.subTy (M.subTy (S.sigma A B) (M.weaken Γ (S.sigma A B))) (S.pack A B))
      (M.subTm (M.genericVariable Γ (S.sigma A B)) (S.pack A B))
      (M.subTm (M.genericVariable Γ (S.sigma A B)) (S.pack A B)) := by
  rw [etaMotive, M.identity_sub, eq_of_heq (S.repacked_beta A B)]

def etaBranch : M.Section (M.extend (M.extend Γ A) B) (M.subTy (S.etaMotive A B) (S.pack A B)) :=
  cast (congrArg (M.Section _) (S.etaBranch_type A B).symm)
    (M.reflexivity _ (M.subTm (M.genericVariable Γ (S.sigma A B)) (S.pack A B)))

/-- Propositional repacking is derived from primitive elimination and beta. -/
def eta : M.Section (M.extend Γ (S.sigma A B)) (S.etaMotive A B) :=
  S.split A B (S.etaMotive A B) (S.etaBranch A B)

theorem eta_beta : HEq (M.subTm (S.eta A B) (S.pack A B))
    (M.reflexivity _ (M.subTm (M.genericVariable Γ (S.sigma A B)) (S.pack A B))) :=
  (S.split_beta A B _ _).trans (cast_heq _ _)

/-- Dependent congruence retains the motive and the selected branch. -/
theorem split_congr {Γ' : M.Context} {A' : M.Family Γ'}
    {B' : M.Family (M.extend Γ' A')} (hΓ : Γ = Γ')
    (hA : HEq A A') (hB : HEq B B')
    {C : M.Family (M.extend Γ (S.sigma A B))}
    {C' : M.Family (M.extend Γ' (S.sigma A' B'))}
    {d : M.Section (M.extend (M.extend Γ A) B) (M.subTy C (S.pack A B))}
    {d' : M.Section (M.extend (M.extend Γ' A') B') (M.subTy C' (S.pack A' B'))}
    (hC : HEq C C') (hd : HEq d d') : HEq (S.split A B C d) (S.split A' B' C' d') := by
  cases hΓ
  cases eq_of_heq hA
  cases eq_of_heq hB
  cases eq_of_heq hC
  cases eq_of_heq hd
  rfl

end Capability

/-- The existing inverse-based eliminator provides this primitive interface
with exactly its selected split, without changing its stronger laws. -/
abbrev ofStrong {M : StructuralModel.{u}} (S : Sigma.Capability M) : Capability M where
  sigma := S.sigma
  pack := S.pack
  pack_over := S.pack_over
  split := S.split
  split_beta := S.split_beta

@[simp] theorem ofStrong_split {M : StructuralModel.{u}} (S : Sigma.Capability M)
    {Γ : M.Context} (A : M.Family Γ) (B : M.Family (M.extend Γ A))
    (C : M.Family (M.extend Γ (S.sigma A B)))
    (d : M.Section (M.extend (M.extend Γ A) B) (M.subTy C (S.pack A B))) :
    (ofStrong S).split A B C d = S.split A B C d := rfl

theorem ofStrong_unpack {M : StructuralModel.{u}} (S : Sigma.Capability M)
    {Γ : M.Context} (A : M.Family Γ) (B : M.Family (M.extend Γ A)) :
    (ofStrong S).unpack A B = S.unpack A B := by
  calc
    (ofStrong S).unpack A B = M.compSub ((ofStrong S).unpack A B)
        (M.compSub (S.pack A B) (S.unpack A B)) := by
      rw [S.pack_unpack, M.comp_id_right]
    _ = M.compSub (M.compSub ((ofStrong S).unpack A B) (S.pack A B)) (S.unpack A B) :=
      (M.comp_assoc _ _ _).symm
    _ = S.unpack A B := by rw [(ofStrong S).unpack_pack, M.comp_id_left]

end SquareKit.Internal.DependentJudgments.PrimitiveSigma
