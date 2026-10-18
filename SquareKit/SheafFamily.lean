import SquareKit.Family
import SquareKit.SheafRelation

/-! Experimental dependent sheaf families. Generic section and substitution
laws specialize to actual sheaf pullbacks; evaluation exposes their fibers. -/
noncomputable section
namespace SquareKit.SheafFamily
open CategoryTheory Limits Opposite Family SheafRelation
universe u v w
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {A Γ Δ : Sheaf J (Type w)}

/-- At each stage, the chosen pullback consists of compatible pairs. -/
def sectionsEquiv (p : A ⟶ Γ) (σ : Δ ⟶ Γ) (U : Cᵒᵖ) :
    (pullback p σ).obj.obj U ≃ Types.PullbackObj (p.hom.app U) (σ.hom.app U) :=
  PullbackCone.IsLimit.equivPullbackObj
    (SheafImage.sections_isPullback (IsPullback.of_hasPullback p σ) U).isLimit

@[simp] theorem sectionsEquiv_fst (p : A ⟶ Γ) (σ : Δ ⟶ Γ) (U : Cᵒᵖ)
    (x : (pullback p σ).obj.obj U) :
    (sectionsEquiv p σ U x).val.1 = (comparison p σ).hom.app U x := by
  apply PullbackCone.IsLimit.equivPullbackObj_apply_fst

@[simp] theorem sectionsEquiv_snd (p : A ⟶ Γ) (σ : Δ ⟶ Γ) (U : Cᵒᵖ)
    (x : (pullback p σ).obj.obj U) :
    (sectionsEquiv p σ U x).val.2 = (reindex p σ).hom.app U x := by
  apply PullbackCone.IsLimit.equivPullbackObj_apply_snd

private theorem lift_display {T : Sheaf J (Type w)} (a : T ⟶ A) (d : T ⟶ Γ) :
    lift a d ≫ snd A Γ = d := rfl

/-- Pulling a constant family back yields the explicit pair sheaf. -/
def constantIso (A : Sheaf J (Type w)) (σ : Δ ⟶ Γ) :
    pullback (snd A Γ) σ ≅ product A Δ where
  hom := lift (comparison (snd A Γ) σ ≫ fst A Γ) (reindex (snd A Γ) σ)
  inv := pair (snd A Γ) σ (lift (fst A Δ) (snd A Δ ≫ σ)) (snd A Δ) (lift_display _ _)
  hom_inv_id := by
    apply pullback.hom_ext
    · simp only [Family.pair, Category.assoc, Category.id_comp]
      rw [pullback.lift_fst (f := snd A Γ) (g := σ)]
      ext U x
      apply Prod.ext
      · rfl
      · exact (congrArg (fun k => k.hom.app U x) (pullback.condition (f := snd A Γ) (g := σ))).symm
    · simp only [Family.pair, Category.assoc, Category.id_comp]
      rw [pullback.lift_snd (f := snd A Γ) (g := σ)]
      rfl
  inv_hom_id := by
    ext U x
    apply Prod.ext
    · exact congrArg (fun k => (k.hom.app U x).1)
        (pair_comparison (snd A Γ) σ (lift (fst A Δ) (snd A Δ ≫ σ)) (snd A Δ) (lift_display _ _))
    · exact congrArg (fun k => k.hom.app U x)
        (pair_reindex (snd A Γ) σ (lift (fst A Δ) (snd A Δ ≫ σ)) (snd A Δ) (lift_display _ _))

@[simp] theorem constantIso_display (A : Sheaf J (Type w)) (σ : Δ ⟶ Γ) :
    (constantIso A σ).hom ≫ snd A Δ = reindex (snd A Γ) σ := rfl

@[simp] theorem constantIso_comparison (A : Sheaf J (Type w)) (σ : Δ ⟶ Γ) :
    (constantIso A σ).hom ≫ fst A Δ = comparison (snd A Γ) σ ≫ fst A Γ := rfl

/-- Pairing under the comparison retains the ordinary value and base map. -/
theorem constant_pair (A : Sheaf J (Type w)) (σ : Δ ⟶ Γ)
    {T : Sheaf J (Type w)} (a : T ⟶ A) (d : T ⟶ Δ) :
    pair (snd A Γ) σ (lift a (d ≫ σ)) d (lift_display _ _) ≫ (constantIso A σ).hom = lift a d := by
  ext U x
  apply Prod.ext
  · exact congrArg (fun k => (k.hom.app U x).1)
      (pair_comparison (snd A Γ) σ (lift a (d ≫ σ)) d (lift_display _ _))
  · exact congrArg (fun k => k.hom.app U x)
      (pair_reindex (snd A Γ) σ (lift a (d ≫ σ)) d (lift_display _ _))

/-- Substitution of a nondependent section is ordinary precomposition. -/
theorem constant_termSub (A : Sheaf J (Type w)) (σ : Δ ⟶ Γ) (a : Γ ⟶ A) :
    (termSub (snd A Γ) σ ⟨lift a (𝟙 Γ), rfl⟩).val ≫ (constantIso A σ).hom =
      lift (σ ≫ a) (𝟙 Δ) := by
  have h := constant_pair A σ (σ ≫ a) (𝟙 Δ)
  exact h
end SquareKit.SheafFamily
