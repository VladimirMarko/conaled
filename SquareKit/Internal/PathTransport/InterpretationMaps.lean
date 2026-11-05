import SquareKit.Internal.PathTransport.Comprehension

/-! Strict maps of the structural interpretation algebra. These maps concern
semantic judgments at two specified models; their indices do not range over
all models. Preservation of contextual J is added after telescope transport. -/

namespace SquareKit.Internal.PathTransport.Typed
universe u v w

structure StructuralMap (M : StructuralModel.{u}) (N : StructuralModel.{v}) where
  context : M.Context → N.Context
  family : {Γ : M.Context} → M.Family Γ → N.Family (context Γ)
  mapTm : {Γ : M.Context} → {A : M.Family Γ} →
    M.Section Γ A → N.Section (context Γ) (family A)
  substitution : {Δ Γ : M.Context} → M.Substitution Δ Γ →
    N.Substitution (context Δ) (context Γ)
  empty : context M.empty = N.empty
  extend : ∀ {Γ} (A : M.Family Γ), context (M.extend Γ A) = N.extend (context Γ) (family A)
  id : ∀ Γ, substitution (M.idSub Γ) = N.idSub (context Γ)
  comp : ∀ {Γ Δ Θ} (σ : M.Substitution Δ Γ) (τ : M.Substitution Θ Δ),
    substitution (M.compSub σ τ) = N.compSub (substitution σ) (substitution τ)
  subTy : ∀ {Γ Δ} (A : M.Family Γ) (σ : M.Substitution Δ Γ),
    family (M.subTy A σ) = N.subTy (family A) (substitution σ)
  subTm : ∀ {Γ Δ A} (t : M.Section Γ A) (σ : M.Substitution Δ Γ),
    HEq (mapTm (M.subTm t σ)) (N.subTm (mapTm t) (substitution σ))
  weaken : ∀ {Γ} (A : M.Family Γ),
    HEq (substitution (M.weaken Γ A)) (N.weaken (context Γ) (family A))
  mapVariable : ∀ {Γ} (A : M.Family Γ),
    HEq (mapTm (M.genericVariable Γ A)) (N.genericVariable (context Γ) (family A))
  pair : ∀ {Γ Δ} (A : M.Family Γ) (σ : M.Substitution Δ Γ)
    (t : M.Section Δ (M.subTy A σ)),
    HEq (substitution (M.pairSub A σ t))
      (N.pairSub (family A) (substitution σ)
        (cast (congrArg (N.Section _) (subTy A σ)) (mapTm t)))
  base : ∀ Γ, family (M.base Γ) = N.base (context Γ)
  fiber : ∀ {Γ} (x : M.Section Γ (M.base Γ)),
    family (M.fiber x) = N.fiber (cast (congrArg (N.Section _) (base Γ)) (mapTm x))
  identity : ∀ {Γ} (A : M.Family Γ) (x y : M.Section Γ A),
    family (M.identity A x y) = N.identity (family A) (mapTm x) (mapTm y)
  reflexivity : ∀ {Γ} (A : M.Family Γ) (x : M.Section Γ A),
    HEq (mapTm (M.reflexivity A x)) (N.reflexivity (family A) (mapTm x))

namespace StructuralModel
variable (M : StructuralModel.{u})

theorem subTy_heq {Γ Γ' Δ Δ' : M.Context} {A : M.Family Γ} {B : M.Family Γ'}
    {σ : M.Substitution Δ Γ} {τ : M.Substitution Δ' Γ'}
    (hΓ : Γ = Γ') (hΔ : Δ = Δ') (hA : HEq A B) (hσ : HEq σ τ) :
    HEq (M.subTy A σ) (M.subTy B τ) := by
  cases hΓ; cases hΔ; cases eq_of_heq hA; cases eq_of_heq hσ; rfl

theorem subTm_heq {Γ Γ' Δ Δ' : M.Context} {A : M.Family Γ} {B : M.Family Γ'}
    {s : M.Section Γ A} {t : M.Section Γ' B}
    {σ : M.Substitution Δ Γ} {τ : M.Substitution Δ' Γ'}
    (hΓ : Γ = Γ') (hΔ : Δ = Δ') (hA : HEq A B) (ht : HEq s t) (hσ : HEq σ τ) :
    HEq (M.subTm s σ) (M.subTm t τ) := by
  cases hΓ; cases hΔ; cases eq_of_heq hA; cases eq_of_heq ht; cases eq_of_heq hσ; rfl

end StructuralModel

namespace StructuralMap
variable {M : StructuralModel.{u}} {N : StructuralModel.{v}}

theorem family_heq (F : StructuralMap M N) {Γ Δ : M.Context}
    {A : M.Family Γ} {B : M.Family Δ} (hΓ : Γ = Δ) (hA : HEq A B) :
    HEq (F.family A) (F.family B) := by
  cases hΓ
  cases eq_of_heq hA
  rfl

theorem section_heq (F : StructuralMap M N) {Γ Δ : M.Context}
    {A : M.Family Γ} {B : M.Family Δ} {s : M.Section Γ A} {t : M.Section Δ B}
    (hΓ : Γ = Δ) (hA : HEq A B) (ht : HEq s t) :
    HEq (F.mapTm s) (F.mapTm t) := by
  cases hΓ
  cases eq_of_heq hA
  cases eq_of_heq ht
  rfl

theorem substitution_heq (F : StructuralMap M N) {Γ Γ' Δ Δ' : M.Context}
    {σ : M.Substitution Δ Γ} {τ : M.Substitution Δ' Γ'}
    (hΓ : Γ = Γ') (hΔ : Δ = Δ') (hσ : HEq σ τ) :
    HEq (F.substitution σ) (F.substitution τ) := by
  cases hΓ
  cases hΔ
  cases eq_of_heq hσ
  rfl

def identityMap (M : StructuralModel.{u}) : StructuralMap M M where
  context := fun x => x
  family := fun x => x
  mapTm := fun x => x
  substitution := fun x => x
  empty := rfl
  extend _ := rfl
  id _ := rfl
  comp _ _ := rfl
  subTy _ _ := rfl
  subTm _ _ := HEq.rfl
  weaken _ := HEq.rfl
  mapVariable _ := HEq.rfl
  pair _ _ _ := HEq.rfl
  base _ := rfl
  fiber _ := rfl
  identity _ _ _ := rfl
  reflexivity _ _ := HEq.rfl

theorem variable_type (F : StructuralMap M N) {Γ} (A : M.Family Γ) :
    HEq (F.family (M.subTy A (M.weaken Γ A)))
      (N.subTy (F.family A) (N.weaken (F.context Γ) (F.family A))) :=
  (heq_of_eq (F.subTy A _)).trans (N.subTy_heq rfl (F.extend A) HEq.rfl (F.weaken A))

variable {P : StructuralModel.{w}}

def compose (G : StructuralMap N P) (F : StructuralMap M N) : StructuralMap M P where
  context Γ := G.context (F.context Γ)
  family A := G.family (F.family A)
  mapTm t := G.mapTm (F.mapTm t)
  substitution σ := G.substitution (F.substitution σ)
  empty := (congrArg G.context F.empty).trans G.empty
  extend A := (congrArg G.context (F.extend A)).trans (G.extend (F.family A))
  id Γ := (congrArg G.substitution (F.id Γ)).trans (G.id (F.context Γ))
  comp σ τ := (congrArg G.substitution (F.comp σ τ)).trans (G.comp _ _)
  subTy A σ := (congrArg G.family (F.subTy A σ)).trans (G.subTy _ _)
  subTm t σ :=
    (G.section_heq rfl (heq_of_eq (F.subTy _ _)) (F.subTm t σ)).trans (G.subTm _ _)
  weaken A :=
    (G.substitution_heq rfl (F.extend A) (F.weaken A)).trans (G.weaken _)
  mapVariable A :=
    (G.section_heq (F.extend A) (F.variable_type A) (F.mapVariable A)).trans (G.mapVariable _)
  pair A σ t := by
    apply (G.substitution_heq (F.extend A) rfl (F.pair A σ t)).trans
    apply (G.pair _ _ _).trans
    apply heq_of_eq
    congr 1
    apply eq_of_heq
    apply (cast_heq _ _).trans
    apply HEq.trans _ (cast_heq _ _).symm
    exact G.section_heq rfl (heq_of_eq (F.subTy A σ).symm) (cast_heq _ _)
  base Γ := (congrArg G.family (F.base Γ)).trans (G.base _)
  fiber x := by
    rw [F.fiber, G.fiber]
    congr 1
    apply eq_of_heq
    apply (cast_heq _ _).trans
    apply HEq.trans _ (cast_heq _ _).symm
    exact G.section_heq rfl (heq_of_eq (F.base _).symm) (cast_heq _ _)
  identity A x y := (congrArg G.family (F.identity A x y)).trans (G.identity _ _ _)
  reflexivity A x :=
    (G.section_heq rfl (heq_of_eq (F.identity A x x)) (F.reflexivity A x)).trans
      (G.reflexivity _ _)

@[simp] theorem compose_identity (F : StructuralMap M N) :
    compose (identityMap N) F = F := by cases F; rfl

@[simp] theorem identity_compose (F : StructuralMap M N) :
    compose F (identityMap M) = F := by cases F; rfl

theorem compose_assoc {Q : StructuralModel} (H : StructuralMap P Q)
    (G : StructuralMap N P) (F : StructuralMap M N) :
    compose (compose H G) F = compose H (compose G F) := by
  cases F; cases G; cases H; rfl

open StructuralModel

private theorem total_cast {Γ Δ : N.Context} {n} (h : Γ = Δ)
    (T : Telescope N Γ n) :
    Telescope.total N (cast (congrArg (fun Ξ => Telescope N Ξ n) h) T) =
      Telescope.total N T := by cases h; rfl

/-- Transport every binder, using the specified extension comparison. -/
def telescope (F : StructuralMap M N) {Γ n} : Telescope M Γ n → Telescope N (F.context Γ) n
  | .nil => .nil
  | .cons A T => .cons (F.family A)
      (cast (congrArg (fun Ξ => Telescope N Ξ _) (F.extend A)) (F.telescope T))

theorem telescope_total (F : StructuralMap M N) {Γ n} (T : Telescope M Γ n) :
    F.context (Telescope.total M T) = Telescope.total N (F.telescope T) := by
  induction T with
  | nil => rfl
  | cons A T ih =>
    exact ih.trans (total_cast (F.extend A) (F.telescope T)).symm

end StructuralMap

end SquareKit.Internal.PathTransport.Typed
