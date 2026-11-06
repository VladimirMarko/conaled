import SquareKit.Internal.PathTransport.Comprehension
namespace SquareKit.Internal.PathTransport.Typed.StructuralModel
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable (M : StructuralModel.{u})
theorem pathSub_lift_comparison {Γ Δ} (A : M.Family Γ) (x : M.Section Γ A)
    (σ : M.Substitution Δ Γ) :
    M.pathSub A x σ = M.compSub (M.lift (M.pathFamily A x) (M.lift A σ))
      (M.familyComparison (M.pathFamily_sub A x σ).symm) := by
  apply M.pair_ext (M.pathFamily A x)
  all_goals dsimp only [pathContext]
  · rw [M.weaken_pathSub, ← M.comp_assoc, M.weaken_lift, M.comp_assoc,
      M.familyComparison_projection]
  · apply (M.variable_pathSub A x σ).trans
    symm
    apply (M.subTm_comp _ _ _).symm.trans
    apply (M.subTm_congr (M.weaken_lift_type _ _) (M.variable_lift _ _) _).trans
    exact M.familyComparison_variable _
end SquareKit.Internal.PathTransport.Typed.StructuralModel
