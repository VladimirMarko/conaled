import SquareKit.Internal.Presheaf
import SquareKit.SheafBaseChange

/-! Experimental sheaf contexts for the existing regular syntax.
Inputs are a presheaf interpretation and sheaf proofs for its sort carriers.
No relation closure is required until formula interpretation is introduced.
-/
namespace SquareKit.Internal.SheafContexts
open CategoryTheory Opposite
universe u v w
variable {J : Type v} [SmallCategory J] {K : GrothendieckTopology J}
variable {S : Type u} {F P : S → S → Type u}
variable (M : Presheaf.Model.{u,v,w} (J := J) F P)
variable (hM : ∀ s, CategoryTheory.Presieve.IsSheaf K (M.carrier s))

include hM in
/-- Environments glue componentwise, including the vacuous empty context. -/
theorem context_isSheaf (Γ : List S) : CategoryTheory.Presieve.IsSheaf K (M.context Γ) := by
  classical
  intro U R hR x hx
  let xi {s} (i : Var Γ s) : CategoryTheory.Presieve.FamilyOfElements (M.carrier s) R.arrows :=
    fun {_} f hf => x f hf i
  have hi {s} (i : Var Γ s) : (xi i).Compatible := by
    intro V₁ V₂ W g₁ g₂ f₁ f₂ h₁ h₂ he
    exact congrArg (fun ρ => ρ i) (hx g₁ g₂ h₁ h₂ he)
  have hs {s} (i : Var Γ s) := hM s R hR (xi i) (hi i)
  let glue : Env (M.fiber (op U)) Γ := fun {s} i => (hs i).choose
  refine ⟨glue, ?_, ?_⟩
  · intro V f hf
    funext s i
    exact (hs i).choose_spec.1 f hf
  · intro t ht
    funext s i
    exact (hs i).choose_spec.2 (t i) (by
      intro V f hf
      exact congrArg (fun ρ => ρ i) (ht f hf))

abbrev context (Γ : List S) : Sheaf K (Type (max u w)) :=
  ⟨M.context Γ, (isSheaf_iff_isSheaf_of_type _ _).mpr (context_isSheaf M hM Γ)⟩

abbrev sort (s : S) : Sheaf K (Type (max u w)) :=
  ⟨M.carrier s, (isSheaf_iff_isSheaf_of_type _ _).mpr (hM s)⟩

def term (t : Term F Γ s) : context M hM Γ ⟶ sort M hM s := ⟨M.term t⟩
def substitution (σ : Sub F Γ Δ) : context M hM Δ ⟶ context M hM Γ := ⟨M.substitution σ⟩
def projection : context M hM (s :: Γ) ⟶ context M hM Γ := ⟨M.projection⟩

theorem substitution_id : substitution M hM (Γ := Γ) (fun i => .var i) = 𝟙 _ := rfl

theorem substitution_comp (σ : Sub F Γ Δ) (τ : Sub F Δ Ξ) :
    substitution M hM (fun i => (σ i).subst τ) =
      substitution M hM τ ≫ substitution M hM σ := by
  apply Sheaf.hom_ext
  exact M.substitution_comp σ τ

theorem term_substitution (σ : Sub F Γ Δ) (t : Term F Γ s) :
    term M hM (t.subst σ) = substitution M hM σ ≫ term M hM t := by
  apply Sheaf.hom_ext
  exact M.term_substitution σ t

theorem projection_substitution (σ : Sub F Γ Δ) :
    substitution M hM (σ.lift (b := s)) ≫ projection M hM =
      projection M hM ≫ substitution M hM σ := by
  apply Sheaf.hom_ext
  exact M.projection_substitution σ

/-- Lifted substitution and projection form a categorical pullback. -/
theorem context_pullback (σ : Sub F Γ Δ) (s : S) :
    IsPullback (substitution M hM (σ.lift (b := s))) (projection M hM)
      (projection M hM) (substitution M hM σ) := by
  apply IsPullback.mk' (projection_substitution M hM σ)
  · intro T a b ht hp
    ext j x t i
    cases i with
    | zero => exact congrArg (fun f => f.hom.app j x Var.zero) ht
    | succ i => exact congrArg (fun f => f.hom.app j x i) hp
  · intro T a b hab
    let l : T ⟶ context M hM (s :: Δ) := ⟨{
      app j := ↾fun x => Env.extend (a.hom.app j x .zero) (b.hom.app j x)
      naturality := by
        intro j k f
        ext x t i
        cases i with
        | zero => exact congrArg (fun ρ => ρ Var.zero) (NatTrans.naturality_apply a.hom f x)
        | succ i => exact congrArg (fun ρ => ρ i) (NatTrans.naturality_apply b.hom f x) }⟩
    refine ⟨l, ?_, ?_⟩
    · ext j x t i
      change (M.substitution σ.lift).app j (Env.extend _ _) i = _
      have he := congrArg (fun ρ => ρ i)
        (M.substitution_lift σ (b.hom.app j x) (a.hom.app j x .zero))
      apply he.trans
      cases i with
      | zero => rfl
      | succ i => exact (congrArg (fun f => f.hom.app j x i) hab).symm
    · rfl

/-- Contextual substitution for local existentials uses the general sheaf law. -/
theorem exists_substitution (Q : Subfunctor (M.context (s :: Γ))) (σ : Sub F Γ Δ) :
    (SquareKit.SheafImage.localImage Q (projection M hM)).preimage
        (substitution M hM σ).hom =
      SquareKit.SheafImage.localImage
        (Q.preimage (substitution M hM σ.lift).hom) (projection M hM) :=
  SquareKit.SheafImage.beckChevalley Q (context_pullback M hM σ s)

end SquareKit.Internal.SheafContexts
