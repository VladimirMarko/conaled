import SquareKit.Internal.PathTransport.RawContext

namespace SquareKit.Internal.PathTransport.Typed
universe u

/-- Structural operations and equations shared by interpretations of the typed fragment. -/
structure StructuralModel where
  Context : Type u
  Family : Context → Type u
  Section : (Γ : Context) → Family Γ → Type u
  Substitution : Context → Context → Type u
  empty : Context
  extend : (Γ : Context) → Family Γ → Context
  idSub : (Γ : Context) → Substitution Γ Γ
  compSub : {Γ Δ Θ : Context} → Substitution Δ Γ → Substitution Θ Δ → Substitution Θ Γ
  subTy : {Γ Δ : Context} → Family Γ → Substitution Δ Γ → Family Δ
  subTm : {Γ Δ : Context} → {A : Family Γ} → (t : Section Γ A) →
    (σ : Substitution Δ Γ) → Section Δ (subTy A σ)
  weaken : (Γ : Context) → (A : Family Γ) → Substitution (extend Γ A) Γ
  genericVariable : (Γ : Context) → (A : Family Γ) →
    Section (extend Γ A) (subTy A (weaken Γ A))
  pairSub : {Γ Δ : Context} → (A : Family Γ) → (σ : Substitution Δ Γ) →
    Section Δ (subTy A σ) → Substitution Δ (extend Γ A)
  base : (Γ : Context) → Family Γ
  fiber : {Γ : Context} → Section Γ (base Γ) → Family Γ
  identity : {Γ : Context} → (A : Family Γ) → Section Γ A → Section Γ A → Family Γ
  reflexivity : {Γ : Context} → (A : Family Γ) → (x : Section Γ A) → Section Γ (identity A x x)
  comp_id_left : ∀ {Γ Δ} (σ : Substitution Δ Γ), compSub (idSub Γ) σ = σ
  comp_id_right : ∀ {Γ Δ} (σ : Substitution Δ Γ), compSub σ (idSub Δ) = σ
  comp_assoc : ∀ {Γ Δ Θ Ξ} (σ : Substitution Δ Γ) (τ : Substitution Θ Δ) (υ : Substitution Ξ Θ),
    compSub (compSub σ τ) υ = compSub σ (compSub τ υ)
  subTy_id : ∀ {Γ} (A : Family Γ), subTy A (idSub Γ) = A
  subTy_comp : ∀ {Γ Δ Θ} (A : Family Γ) (σ : Substitution Δ Γ) (τ : Substitution Θ Δ),
    subTy (subTy A σ) τ = subTy A (compSub σ τ)
  subTm_id : ∀ {Γ A} (t : Section Γ A), HEq (subTm t (idSub Γ)) t
  subTm_comp : ∀ {Γ Δ Θ A} (t : Section Γ A) (σ : Substitution Δ Γ) (τ : Substitution Θ Δ),
    HEq (subTm (subTm t σ) τ) (subTm t (compSub σ τ))
  base_sub : ∀ {Γ Δ} (σ : Substitution Δ Γ), subTy (base Γ) σ = base Δ
  fiber_sub : ∀ {Γ Δ} (x : Section Γ (base Γ)) (σ : Substitution Δ Γ),
    subTy (fiber x) σ = fiber (cast (congrArg (Section Δ) (base_sub σ)) (subTm x σ))
  identity_sub : ∀ {Γ Δ} (A : Family Γ) (x y : Section Γ A) (σ : Substitution Δ Γ),
    subTy (identity A x y) σ = identity (subTy A σ) (subTm x σ) (subTm y σ)
  refl_sub : ∀ {Γ Δ} (A : Family Γ) (x : Section Γ A) (σ : Substitution Δ Γ),
    HEq (subTm (reflexivity A x) σ) (reflexivity (subTy A σ) (subTm x σ))
  weaken_pair : ∀ {Γ Δ} (A : Family Γ) (σ : Substitution Δ Γ) (t : Section Δ (subTy A σ)),
    compSub (weaken Γ A) (pairSub A σ t) = σ
  variable_pair : ∀ {Γ Δ} (A : Family Γ) (σ : Substitution Δ Γ) (t : Section Δ (subTy A σ)),
    HEq (subTm (genericVariable Γ A) (pairSub A σ t)) t
  pair_eta : ∀ {Γ Δ} (A : Family Γ) (σ : Substitution Δ (extend Γ A)),
    pairSub A (compSub (weaken Γ A) σ)
      (cast (congrArg (Section Δ) (subTy_comp A (weaken Γ A) σ))
        (subTm (genericVariable Γ A) σ)) = σ

end SquareKit.Internal.PathTransport.Typed
