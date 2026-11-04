import SquareKit.Internal.PathTransport.ContextualModel
import Mathlib.Logic.Equiv.Defs

/-! Consequences of comprehension beta/eta. None of these laws is an additional
model-builder obligation. No terminal context or signature operation is used. -/
namespace SquareKit.Internal.PathTransport.Typed.StructuralModel
universe u
set_option backward.isDefEq.respectTransparency false
variable (M : StructuralModel.{u})

theorem pair_naturality {Γ Δ Θ} (A : M.Family Γ)
    (σ : M.Substitution Δ Γ) (t : M.Section Δ (M.subTy A σ))
    (τ : M.Substitution Θ Δ) :
    M.compSub (M.pairSub A σ t) τ =
      M.pairSub A (M.compSub σ τ)
        (cast (congrArg (M.Section Θ) (M.subTy_comp A σ τ)) (M.subTm t τ)) := by
  apply M.pair_ext A
  · rw [← M.comp_assoc, M.weaken_pair, M.weaken_pair]
  · apply (M.subTm_comp _ _ _).symm.trans
    apply (M.subTm_congr (by rw [M.subTy_comp, M.weaken_pair])
      (M.variable_pair A σ t) τ).trans
    exact ((M.variable_pair _ _ _).trans (cast_heq _ _)).symm

/-- Reconstruct an arrow to a comprehension from its base and variable. -/
theorem pair_unique {Γ Δ} (A : M.Family Γ)
    (σ : M.Substitution Δ Γ) (t : M.Section Δ (M.subTy A σ))
    (f : M.Substitution Δ (M.extend Γ A))
    (hp : M.compSub (M.weaken Γ A) f = σ)
    (hq : HEq (M.subTm (M.genericVariable Γ A) f) t) :
    f = M.pairSub A σ t := by
  apply M.pair_ext A
  · rw [M.weaken_pair]; exact hp
  · exact hq.trans (M.variable_pair _ _ _).symm

/-- The mediating arrow in the pullback of a display map along any substitution. -/
def pullbackFactor {Γ Δ Θ} (A : M.Family Γ) (σ : M.Substitution Δ Γ)
    (f : M.Substitution Θ Δ) (g : M.Substitution Θ (M.extend Γ A))
    (h : M.compSub σ f = M.compSub (M.weaken Γ A) g) :
    M.Substitution Θ (M.extend Δ (M.subTy A σ)) :=
  M.pairSub (M.subTy A σ) f
    (cast (congrArg (M.Section Θ) (by rw [M.subTy_comp, ← h, ← M.subTy_comp]))
      (M.subTm (M.genericVariable Γ A) g))

theorem pullbackFactor_projection {Γ Δ Θ} (A : M.Family Γ) (σ : M.Substitution Δ Γ)
    (f : M.Substitution Θ Δ) (g : M.Substitution Θ (M.extend Γ A))
    (h : M.compSub σ f = M.compSub (M.weaken Γ A) g) :
    M.compSub (M.weaken Δ (M.subTy A σ)) (M.pullbackFactor A σ f g h) = f :=
  M.weaken_pair _ _ _

theorem pullbackFactor_variable {Γ Δ Θ} (A : M.Family Γ) (σ : M.Substitution Δ Γ)
    (f : M.Substitution Θ Δ) (g : M.Substitution Θ (M.extend Γ A))
    (h : M.compSub σ f = M.compSub (M.weaken Γ A) g) :
    HEq (M.subTm (M.genericVariable Δ (M.subTy A σ)) (M.pullbackFactor A σ f g h))
      (M.subTm (M.genericVariable Γ A) g) :=
  (M.variable_pair _ _ _).trans (cast_heq _ _)

theorem pullbackFactor_lift {Γ Δ Θ} (A : M.Family Γ) (σ : M.Substitution Δ Γ)
    (f : M.Substitution Θ Δ) (g : M.Substitution Θ (M.extend Γ A))
    (h : M.compSub σ f = M.compSub (M.weaken Γ A) g) :
    M.compSub (M.lift A σ) (M.pullbackFactor A σ f g h) = g := by
  apply M.pair_ext A
  · rw [← M.comp_assoc, M.weaken_lift, M.comp_assoc, M.pullbackFactor_projection]
    exact h
  · exact (M.subTm_comp _ _ _).symm.trans
      ((M.subTm_congr (M.weaken_lift_type A σ) (M.variable_lift A σ) _).trans
        (M.pullbackFactor_variable A σ f g h))

theorem pullbackFactor_unique {Γ Δ Θ} (A : M.Family Γ) (σ : M.Substitution Δ Γ)
    (f : M.Substitution Θ Δ) (g : M.Substitution Θ (M.extend Γ A))
    (h : M.compSub σ f = M.compSub (M.weaken Γ A) g)
    (k : M.Substitution Θ (M.extend Δ (M.subTy A σ)))
    (hp : M.compSub (M.weaken Δ (M.subTy A σ)) k = f)
    (hq : M.compSub (M.lift A σ) k = g) : k = M.pullbackFactor A σ f g h := by
  apply M.pair_ext (M.subTy A σ)
  · rw [M.pullbackFactor_projection]; exact hp
  · apply HEq.trans _ (M.pullbackFactor_variable A σ f g h).symm
    apply (M.subTm_congr (M.weaken_lift_type A σ) (M.variable_lift A σ) k).symm.trans
    apply (M.subTm_comp _ _ _).trans
    rw [hq]

/-- The equality of reindexed families induces a canonical context comparison. -/
def familyComparison {Γ} {A B : M.Family Γ} (h : A = B) :
    M.Substitution (M.extend Γ A) (M.extend Γ B) := h ▸ M.idSub (M.extend Γ A)

@[simp] theorem familyComparison_refl {Γ} (A : M.Family Γ) :
    M.familyComparison (rfl : A = A) = M.idSub (M.extend Γ A) := rfl

theorem familyComparison_projection {Γ} {A B : M.Family Γ} (h : A = B) :
    M.compSub (M.weaken Γ B) (M.familyComparison h) = M.weaken Γ A := by
  cases h
  exact M.comp_id_right _

theorem familyComparison_variable {Γ} {A B : M.Family Γ} (h : A = B) :
    HEq (M.subTm (M.genericVariable Γ B) (M.familyComparison h))
      (M.genericVariable Γ A) := by
  cases h
  exact M.subTm_id _

theorem familyComparison_trans {Γ} {A B C : M.Family Γ} (h : A = B) (k : B = C) :
    M.compSub (M.familyComparison k) (M.familyComparison h) = M.familyComparison (h.trans k) := by
  cases h
  cases k
  exact M.comp_id_left _

theorem familyComparison_inverse {Γ} {A B : M.Family Γ} (h : A = B) :
    M.compSub (M.familyComparison h.symm) (M.familyComparison h) = M.idSub (M.extend Γ A) :=
  M.familyComparison_trans h h.symm

theorem lift_id {Γ} (A : M.Family Γ) :
    M.lift A (M.idSub Γ) = M.familyComparison (M.subTy_id A) := by
  apply M.pair_ext A
  · rw [M.weaken_lift, M.comp_id_left]; exact (M.familyComparison_projection _).symm
  · exact (M.variable_lift _ _).trans (M.familyComparison_variable _).symm

theorem lift_comp {Γ Δ Θ} (A : M.Family Γ)
    (σ : M.Substitution Δ Γ) (τ : M.Substitution Θ Δ) :
    M.compSub (M.lift A σ) (M.lift (M.subTy A σ) τ) =
      M.compSub (M.lift A (M.compSub σ τ))
        (M.familyComparison (M.subTy_comp A σ τ)) := by
  apply M.pair_ext A
  · simp only [← M.comp_assoc, M.weaken_lift]
    simp only [M.comp_assoc, M.weaken_lift, M.familyComparison_projection]
  · apply (M.subTm_comp _ _ _).symm.trans
    apply (M.subTm_congr (M.weaken_lift_type A σ) (M.variable_lift A σ) _).trans
    apply (M.variable_lift _ _).trans
    apply (M.familyComparison_variable (M.subTy_comp A σ τ)).symm.trans
    apply HEq.trans _ (M.subTm_comp _ _ _)
    exact (M.subTm_congr (M.weaken_lift_type A _) (M.variable_lift A _) _).symm

/-- Terms of a pulled-back family are exactly arrows over the selected base
substitution. In groupoid models these are actual functors over that base. -/
def sectionsOver {Γ Δ} (A : M.Family Γ) (σ : M.Substitution Δ Γ) :
    M.Section Δ (M.subTy A σ) ≃
      { f : M.Substitution Δ (M.extend Γ A) // M.compSub (M.weaken Γ A) f = σ } where
  toFun t := ⟨M.pairSub A σ t, M.weaken_pair _ _ _⟩
  invFun f := cast (congrArg (M.Section Δ)
    ((M.subTy_comp A (M.weaken Γ A) f.val).trans (congrArg (M.subTy A) f.property)))
      (M.subTm (M.genericVariable Γ A) f.val)
  left_inv t := eq_of_heq ((cast_heq _ _).trans (M.variable_pair _ _ _))
  right_inv f := by
    apply Subtype.ext
    exact (M.pair_unique A σ _ f.val f.property (cast_heq _ _).symm).symm

end SquareKit.Internal.PathTransport.Typed.StructuralModel
