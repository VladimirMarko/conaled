import SquareKit.Internal.PathTransport.InterpretationMaps

/-! Dependent sums are chosen isomorphisms between a two-step comprehension
and a single comprehension. Both inverse equations are part of this contract.
The second supplies the type equality needed by dependent elimination. -/
namespace SquareKit.Internal.DependentJudgments.Sigma
open PathTransport.Typed StructuralModel
universe u

structure Capability (M : StructuralModel.{u}) where
  sigma : {Γ : M.Context} → (A : M.Family Γ) → M.Family (M.extend Γ A) → M.Family Γ
  pack : ∀ {Γ} (A : M.Family Γ) (B : M.Family (M.extend Γ A)),
    M.Substitution (M.extend (M.extend Γ A) B) (M.extend Γ (sigma A B))
  unpack : ∀ {Γ} (A : M.Family Γ) (B : M.Family (M.extend Γ A)),
    M.Substitution (M.extend Γ (sigma A B)) (M.extend (M.extend Γ A) B)
  pack_over : ∀ {Γ} (A : M.Family Γ) (B : M.Family (M.extend Γ A)),
    M.compSub (M.weaken Γ (sigma A B)) (pack A B) =
      M.compSub (M.weaken Γ A) (M.weaken (M.extend Γ A) B)
  unpack_pack : ∀ {Γ} (A : M.Family Γ) (B : M.Family (M.extend Γ A)),
    M.compSub (unpack A B) (pack A B) = M.idSub (M.extend (M.extend Γ A) B)
  pack_unpack : ∀ {Γ} (A : M.Family Γ) (B : M.Family (M.extend Γ A)),
    M.compSub (pack A B) (unpack A B) = M.idSub (M.extend Γ (sigma A B))

namespace Capability
variable {M : StructuralModel.{u}} (S : Capability M)
variable {Γ : M.Context} (A : M.Family Γ) (B : M.Family (M.extend Γ A))

theorem unpack_over :
    M.compSub (M.compSub (M.weaken Γ A) (M.weaken (M.extend Γ A) B)) (S.unpack A B) =
      M.weaken Γ (S.sigma A B) := by
  rw [← S.pack_over, M.comp_assoc, S.pack_unpack, M.comp_id_right]

/-- Semantic judgmental eta, rather than an object identity proof, aligns the motive. -/
theorem split_type (C : M.Family (M.extend Γ (S.sigma A B))) :
    M.subTy (M.subTy C (S.pack A B)) (S.unpack A B) = C := by
  rw [M.subTy_comp, S.pack_unpack, M.subTy_id]

def split (C : M.Family (M.extend Γ (S.sigma A B)))
    (d : M.Section (M.extend (M.extend Γ A) B) (M.subTy C (S.pack A B))) :
    M.Section (M.extend Γ (S.sigma A B)) C :=
  cast (congrArg (M.Section _) (S.split_type A B C)) (M.subTm d (S.unpack A B))

theorem split_heq (C : M.Family (M.extend Γ (S.sigma A B)))
    (d : M.Section (M.extend (M.extend Γ A) B) (M.subTy C (S.pack A B))) :
    HEq (S.split A B C d) (M.subTm d (S.unpack A B)) := cast_heq _ _

theorem split_beta (C : M.Family (M.extend Γ (S.sigma A B)))
    (d : M.Section (M.extend (M.extend Γ A) B) (M.subTy C (S.pack A B))) :
    HEq (M.subTm (S.split A B C d) (S.pack A B)) d := by
  apply (M.subTm_congr (S.split_type A B C).symm (S.split_heq A B C d) _).trans
  apply (M.subTm_comp _ _ _).trans
  rw [S.unpack_pack]
  exact M.subTm_id d

theorem split_eta (C : M.Family (M.extend Γ (S.sigma A B)))
    (t : M.Section (M.extend Γ (S.sigma A B)) C) :
    S.split A B C (M.subTm t (S.pack A B)) = t := by
  apply eq_of_heq
  apply (S.split_heq A B C _).trans
  apply (M.subTm_comp _ _ _).trans
  rw [S.pack_unpack]
  exact M.subTm_id t

theorem split_unique (C : M.Family (M.extend Γ (S.sigma A B)))
    (d : M.Section (M.extend (M.extend Γ A) B) (M.subTy C (S.pack A B)))
    (t : M.Section (M.extend Γ (S.sigma A B)) C)
    (h : HEq (M.subTm t (S.pack A B)) d) : t = S.split A B C d := by
  rw [← eq_of_heq h, S.split_eta]

/-- Pullback along the constructor detects equality of dependent sections. -/
theorem subTm_pack_injective (C : M.Family (M.extend Γ (S.sigma A B)))
    {s t : M.Section (M.extend Γ (S.sigma A B)) C}
    (h : HEq (M.subTm s (S.pack A B)) (M.subTm t (S.pack A B))) : s = t := by
  rw [← S.split_eta A B C s, ← S.split_eta A B C t]
  exact congrArg (S.split A B C) (eq_of_heq h)

end Capability
end SquareKit.Internal.DependentJudgments.Sigma
