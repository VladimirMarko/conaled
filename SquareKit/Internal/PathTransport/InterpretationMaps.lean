import SquareKit.Internal.PathTransport.Comprehension

/-! Strict maps of the structural interpretation algebra. These maps concern
semantic judgments at two specified models; their indices do not range over
all models. Telescope and branch transport are derived before primitive J
preservation is required. Signature assignments need no preservation law here. -/

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


theorem comp_heq {Γ Γ' Δ Δ' Θ Θ' : M.Context}
    {σ : M.Substitution Δ Γ} {σ' : M.Substitution Δ' Γ'}
    {τ : M.Substitution Θ Δ} {τ' : M.Substitution Θ' Δ'}
    (hΓ : Γ = Γ') (hΔ : Δ = Δ') (hΘ : Θ = Θ')
    (hσ : HEq σ σ') (hτ : HEq τ τ') :
    HEq (M.compSub σ τ) (M.compSub σ' τ') := by
  cases hΓ; cases hΔ; cases hΘ; cases eq_of_heq hσ; cases eq_of_heq hτ; rfl

theorem extend_heq {Γ Δ : M.Context} {A : M.Family Γ} {B : M.Family Δ}
    (hΓ : Γ = Δ) (hA : HEq A B) : M.extend Γ A = M.extend Δ B := by
  cases hΓ; cases eq_of_heq hA; rfl

theorem pair_heq {Γ Γ' Δ Δ' : M.Context} {A : M.Family Γ} {A' : M.Family Γ'}
    {σ : M.Substitution Δ Γ} {σ' : M.Substitution Δ' Γ'}
    {t : M.Section Δ (M.subTy A σ)} {t' : M.Section Δ' (M.subTy A' σ')}
    (hΓ : Γ = Γ') (hΔ : Δ = Δ') (hA : HEq A A') (hσ : HEq σ σ') (ht : HEq t t') :
    HEq (M.pairSub A σ t) (M.pairSub A' σ' t') := by
  cases hΓ; cases hΔ; cases eq_of_heq hA; cases eq_of_heq hσ; cases eq_of_heq ht; rfl


theorem weaken_heq {Γ Δ : M.Context} {A : M.Family Γ} {B : M.Family Δ}
    (hΓ : Γ = Δ) (hA : HEq A B) : HEq (M.weaken Γ A) (M.weaken Δ B) := by
  cases hΓ; cases eq_of_heq hA; rfl

theorem variable_heq {Γ Δ : M.Context} {A : M.Family Γ} {B : M.Family Δ}
    (hΓ : Γ = Δ) (hA : HEq A B) :
    HEq (M.genericVariable Γ A) (M.genericVariable Δ B) := by
  cases hΓ; cases eq_of_heq hA; rfl

theorem identity_heq {Γ Δ : M.Context} {A : M.Family Γ} {B : M.Family Δ}
    {x y : M.Section Γ A} {x' y' : M.Section Δ B}
    (hΓ : Γ = Δ) (hA : HEq A B) (hx : HEq x x') (hy : HEq y y') :
    HEq (M.identity A x y) (M.identity B x' y') := by
  cases hΓ; cases eq_of_heq hA; cases eq_of_heq hx; cases eq_of_heq hy; rfl


theorem Telescope.cons_heq {Γ Δ : M.Context} {n}
    {A : M.Family Γ} {B : M.Family Δ}
    {T : Telescope M (M.extend Γ A) n} {U : Telescope M (M.extend Δ B) n}
    (hΓ : Γ = Δ) (hA : HEq A B) (hT : HEq T U) :
    HEq (Telescope.cons A T) (Telescope.cons B U) := by
  cases hΓ; cases eq_of_heq hA; cases eq_of_heq hT; rfl

theorem Telescope.total_heq {Γ Δ : M.Context} {n}
    {T : Telescope M Γ n} {U : Telescope M Δ n} (hΓ : Γ = Δ) (hT : HEq T U) :
    T.total = U.total := by
  cases hΓ; cases eq_of_heq hT; rfl

theorem Telescope.projection_heq {Γ Δ : M.Context} {n}
    {T : Telescope M Γ n} {U : Telescope M Δ n} (hΓ : Γ = Δ) (hT : HEq T U) :
    HEq T.projection U.projection := by
  cases hΓ; cases eq_of_heq hT; rfl

theorem Telescope.pullback_heq {Γ Γ' Δ Δ' : M.Context} {n}
    {T : Telescope M Γ n} {U : Telescope M Γ' n}
    {σ : M.Substitution Δ Γ} {τ : M.Substitution Δ' Γ'}
    (hΓ : Γ = Γ') (hΔ : Δ = Δ') (hT : HEq T U) (hσ : HEq σ τ) :
    HEq (Telescope.pullback M T σ) (Telescope.pullback M U τ) := by
  cases hΓ; cases hΔ; cases eq_of_heq hT; cases eq_of_heq hσ; rfl

theorem Telescope.liftSub_heq {Γ Γ' Δ Δ' : M.Context} {n}
    {T : Telescope M Γ n} {U : Telescope M Γ' n}
    {σ : M.Substitution Δ Γ} {τ : M.Substitution Δ' Γ'}
    (hΓ : Γ = Γ') (hΔ : Δ = Δ') (hT : HEq T U) (hσ : HEq σ τ) :
    HEq (Telescope.liftSub M T σ) (Telescope.liftSub M U τ) := by
  cases hΓ; cases hΔ; cases eq_of_heq hT; cases eq_of_heq hσ; rfl


theorem pathFamily_heq {Γ Δ : M.Context} {A : M.Family Γ} {B : M.Family Δ}
    {x : M.Section Γ A} {y : M.Section Δ B}
    (hΓ : Γ = Δ) (hA : HEq A B) (hx : HEq x y) :
    HEq (M.pathFamily A x) (M.pathFamily B y) := by
  cases hΓ; cases eq_of_heq hA; cases eq_of_heq hx; rfl

theorem pathContext_heq {Γ Δ : M.Context} {A : M.Family Γ} {B : M.Family Δ}
    {x : M.Section Γ A} {y : M.Section Δ B}
    (hΓ : Γ = Δ) (hA : HEq A B) (hx : HEq x y) :
    M.pathContext A x = M.pathContext B y := by
  cases hΓ; cases eq_of_heq hA; cases eq_of_heq hx; rfl

theorem rootSub_heq {Γ Δ : M.Context} {A : M.Family Γ} {B : M.Family Δ}
    {x : M.Section Γ A} {y : M.Section Δ B}
    (hΓ : Γ = Δ) (hA : HEq A B) (hx : HEq x y) :
    HEq (M.rootSub A x) (M.rootSub B y) := by
  cases hΓ; cases eq_of_heq hA; cases eq_of_heq hx; rfl


theorem Telescope.square_heq
    {Γ Γ₁ Γ' Γ₁' Δ Δ₁ Δ' Δ₁' : M.Context}
    {S : M.Substitution Δ Γ} {S₁ : M.Substitution Δ₁ Γ₁}
    {S' : M.Substitution Δ' Γ'} {S₁' : M.Substitution Δ₁' Γ₁'}
    {K : M.Substitution Γ' Γ} {K₁ : M.Substitution Γ₁' Γ₁}
    {L : M.Substitution Δ' Δ} {L₁ : M.Substitution Δ₁' Δ₁}
    {h : M.compSub K S' = M.compSub S L} {h₁ : M.compSub K₁ S₁' = M.compSub S₁ L₁}
    {n} {T : Telescope M Γ n} {U : Telescope M Γ₁ n}
    (hΓ : Γ = Γ₁) (hΓ' : Γ' = Γ₁') (hΔ : Δ = Δ₁) (hΔ' : Δ' = Δ₁')
    (hS : HEq S S₁) (hS' : HEq S' S₁') (hK : HEq K K₁) (hL : HEq L L₁)
    (hT : HEq T U) :
    HEq (Telescope.square M S S' K L h T).val (Telescope.square M S₁ S₁' K₁ L₁ h₁ U).val := by
  cases hΓ; cases hΓ'; cases hΔ; cases hΔ'
  cases eq_of_heq hS; cases eq_of_heq hS'; cases eq_of_heq hK; cases eq_of_heq hL
  cases eq_of_heq hT; rfl


theorem lift_heq {Γ Γ' Δ Δ' : M.Context} {A : M.Family Γ} {B : M.Family Γ'}
    {σ : M.Substitution Δ Γ} {τ : M.Substitution Δ' Γ'}
    (hΓ : Γ = Γ') (hΔ : Δ = Δ') (hA : HEq A B) (hσ : HEq σ τ) :
    HEq (M.lift A σ) (M.lift B τ) := by
  cases hΓ; cases hΔ; cases eq_of_heq hA; cases eq_of_heq hσ; rfl


/-- Change metatheoretic indices without identifying object-language paths. -/
def castSection {Γ Δ : M.Context} {A : M.Family Γ} {B : M.Family Δ}
    (hΓ : Γ = Δ) (hA : HEq A B) (t : M.Section Γ A) : M.Section Δ B := by
  cases hΓ
  exact cast (congrArg (M.Section Γ) (eq_of_heq hA)) t

theorem castSection_heq {Γ Δ : M.Context} {A : M.Family Γ} {B : M.Family Δ}
    (hΓ : Γ = Δ) (hA : HEq A B) (t : M.Section Γ A) :
    HEq (M.castSection hΓ hA t) t := by
  cases hΓ; cases eq_of_heq hA; rfl

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
  identity _ _ _ := rfl
  reflexivity _ _ := HEq.rfl

theorem variable_type (F : StructuralMap M N) {Γ} (A : M.Family Γ) :
    HEq (F.family (M.subTy A (M.weaken Γ A)))
      (N.subTy (F.family A) (N.weaken (F.context Γ) (F.family A))) :=
  (heq_of_eq (F.subTy A _)).trans (N.subTy_heq rfl (F.extend A) HEq.rfl (F.weaken A))


/-- Pairing preservation follows from preservation of its two projections. -/
theorem pair (F : StructuralMap M N) {Γ Δ} (A : M.Family Γ)
    (σ : M.Substitution Δ Γ) (t : M.Section Δ (M.subTy A σ)) :
    HEq (F.substitution (M.pairSub A σ t))
      (N.pairSub (F.family A) (F.substitution σ)
        (cast (congrArg (N.Section _) (F.subTy A σ)) (F.mapTm t))) := by
  let f := cast (congrArg (N.Substitution (F.context Δ)) (F.extend A))
    (F.substitution (M.pairSub A σ t))
  apply (cast_heq _ _).symm.trans (heq_of_eq (N.pair_unique (F.family A) _ _ f ?_ ?_))
  · apply eq_of_heq
    apply (N.comp_heq rfl (F.extend A).symm rfl (F.weaken A).symm
      (cast_heq _ _)).trans
    exact (heq_of_eq (F.comp _ _).symm).trans (heq_of_eq (congrArg F.substitution (M.weaken_pair A σ t)))
  · apply (N.subTm_heq (F.extend A).symm rfl (F.variable_type A).symm
      (F.mapVariable A).symm (cast_heq _ _)).trans
    apply (F.subTm _ _).symm.trans
    apply HEq.trans _ (cast_heq _ _).symm
    exact F.section_heq rfl
      (heq_of_eq (by rw [M.subTy_comp, M.weaken_pair])) (M.variable_pair A σ t)


theorem sectionSub (F : StructuralMap M N) {Γ} (A : M.Family Γ) (x : M.Section Γ A) :
    HEq (F.substitution (M.sectionSub A x)) (N.sectionSub (F.family A) (F.mapTm x)) := by
  apply (F.pair A _ _).trans
  apply N.pair_heq rfl rfl HEq.rfl (heq_of_eq (F.id Γ))
  apply (cast_heq _ _).trans
  apply HEq.trans _ (cast_heq _ _).symm
  exact F.section_heq rfl (heq_of_eq (M.subTy_id A)) (cast_heq _ _)

theorem lift (F : StructuralMap M N) {Γ Δ} (A : M.Family Γ)
    (σ : M.Substitution Δ Γ) :
    HEq (F.substitution (M.lift A σ)) (N.lift (F.family A) (F.substitution σ)) := by
  have hctx : F.context (M.extend Δ (M.subTy A σ)) =
      N.extend (F.context Δ) (N.subTy (F.family A) (F.substitution σ)) :=
    (F.extend _).trans (N.extend_heq rfl (heq_of_eq (F.subTy A σ)))
  have hw : HEq (F.substitution (M.weaken Δ (M.subTy A σ)))
      (N.weaken (F.context Δ) (N.subTy (F.family A) (F.substitution σ))) :=
    (F.weaken _).trans (N.weaken_heq rfl (heq_of_eq (F.subTy A σ)))
  apply (F.pair A _ _).trans
  apply N.pair_heq rfl hctx HEq.rfl
    ((heq_of_eq (F.comp _ _)).trans (N.comp_heq rfl rfl hctx HEq.rfl hw))
  apply (cast_heq _ _).trans
  apply HEq.trans _ (cast_heq _ _).symm
  apply (F.section_heq rfl (heq_of_eq (M.subTy_comp _ _ _).symm) (cast_heq _ _)).trans
  exact (F.mapVariable _).trans (N.variable_heq rfl (heq_of_eq (F.subTy A σ)))

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


theorem telescope_heq (F : StructuralMap M N) {Γ Δ n}
    {T : Telescope M Γ n} {U : Telescope M Δ n} (hΓ : Γ = Δ) (hT : HEq T U) :
    HEq (F.telescope T) (F.telescope U) := by
  cases hΓ; cases eq_of_heq hT; rfl


theorem telescope_projection (F : StructuralMap M N) {Γ n} (T : Telescope M Γ n) :
    HEq (F.substitution T.projection) (F.telescope T).projection := by
  induction T with
  | nil => exact heq_of_eq (F.id _)
  | cons A T ih =>
    apply (heq_of_eq (F.comp _ _)).trans
    apply N.comp_heq rfl (F.extend A)
      ((F.telescope_total T).trans (total_cast (F.extend A) (F.telescope T)).symm)
      (F.weaken A)
    exact ih.trans (Telescope.projection_heq N (F.extend A) (cast_heq _ _).symm)

theorem telescope_pullback (F : StructuralMap M N) {Γ Δ n}
    (T : Telescope M Γ n) (σ : M.Substitution Δ Γ) :
    F.telescope (Telescope.pullback M T σ) = Telescope.pullback N (F.telescope T) (F.substitution σ) := by
  induction T generalizing Δ with
  | nil => rfl
  | cons A T ih =>
    apply eq_of_heq
    apply Telescope.cons_heq N rfl (heq_of_eq (F.subTy A σ))
    apply (cast_heq _ _).trans
    apply (heq_of_eq (ih (M.lift A σ))).trans
    apply Telescope.pullback_heq N (F.extend A)
      ((F.extend _).trans (N.extend_heq rfl (heq_of_eq (F.subTy A σ))))
      (cast_heq _ _).symm (F.lift A σ)

theorem telescope_liftSub (F : StructuralMap M N) {Γ Δ n}
    (T : Telescope M Γ n) (σ : M.Substitution Δ Γ) :
    HEq (F.substitution (Telescope.liftSub M T σ)) (Telescope.liftSub N (F.telescope T) (F.substitution σ)) := by
  induction T generalizing Δ with
  | nil => rfl
  | cons A T ih =>
    apply (ih (M.lift A σ)).trans
    exact Telescope.liftSub_heq N (F.extend A)
      ((F.extend _).trans (N.extend_heq rfl (heq_of_eq (F.subTy A σ))))
      (cast_heq _ _).symm (F.lift A σ)


theorem pathFamily (F : StructuralMap M N) {Γ} (A : M.Family Γ)
    (x : M.Section Γ A) :
    HEq (F.family (M.pathFamily A x)) (N.pathFamily (F.family A) (F.mapTm x)) := by
  apply (heq_of_eq (F.identity _ _ _)).trans
  apply N.identity_heq (F.extend A) (F.variable_type A) _ (F.mapVariable A)
  exact (F.subTm _ _).trans (N.subTm_heq rfl (F.extend A) HEq.rfl HEq.rfl (F.weaken A))

theorem pathContext (F : StructuralMap M N) {Γ} (A : M.Family Γ)
    (x : M.Section Γ A) :
    F.context (M.pathContext A x) = N.pathContext (F.family A) (F.mapTm x) :=
  (F.extend _).trans (N.extend_heq (F.extend A) (F.pathFamily A x))

theorem rootSub (F : StructuralMap M N) {Γ} (A : M.Family Γ)
    (x : M.Section Γ A) :
    HEq (F.substitution (M.rootSub A x)) (N.rootSub (F.family A) (F.mapTm x)) := by
  apply (F.pair _ _ _).trans
  apply N.pair_heq (F.extend A) rfl (F.pathFamily A x) (F.sectionSub A x)
  apply (cast_heq _ _).trans
  apply HEq.trans _ (cast_heq _ _).symm
  exact (F.section_heq rfl (heq_of_eq (M.pathFamily_root A x))
    (cast_heq _ _)).trans (F.reflexivity A x)

/-- The complete mapped telescope over the mapped identity context. -/
def pathTelescope (F : StructuralMap M N) {Γ n} (A : M.Family Γ) (x : M.Section Γ A)
    (T : Telescope M (M.pathContext A x) n) :
    Telescope N (N.pathContext (F.family A) (F.mapTm x)) n :=
  cast (congrArg (fun Ξ => Telescope N Ξ n) (F.pathContext A x)) (F.telescope T)

theorem pathTelescope_total (F : StructuralMap M N) {Γ n} (A : M.Family Γ)
    (x : M.Section Γ A) (T : Telescope M (M.pathContext A x) n) :
    F.context T.total = (F.pathTelescope A x T).total :=
  (F.telescope_total T).trans (total_cast (F.pathContext A x) (F.telescope T)).symm

theorem rootTelescope (F : StructuralMap M N) {Γ n} (A : M.Family Γ)
    (x : M.Section Γ A) (T : Telescope M (M.pathContext A x) n) :
    F.telescope (Telescope.pullback M T (M.rootSub A x)) =
      Telescope.pullback N (F.pathTelescope A x T) (N.rootSub (F.family A) (F.mapTm x)) := by
  apply (F.telescope_pullback T _).trans
  apply eq_of_heq
  exact Telescope.pullback_heq N (F.pathContext A x) rfl (cast_heq _ _).symm (F.rootSub A x)

theorem rootTail (F : StructuralMap M N) {Γ n} (A : M.Family Γ)
    (x : M.Section Γ A) (T : Telescope M (M.pathContext A x) n) :
    HEq (F.substitution (M.rootTail A x T))
      (N.rootTail (F.family A) (F.mapTm x) (F.pathTelescope A x T)) := by
  apply (F.telescope_liftSub T _).trans
  exact Telescope.liftSub_heq N (F.pathContext A x) rfl (cast_heq _ _).symm (F.rootSub A x)


theorem pathSub (F : StructuralMap M N) {Γ Δ} (A : M.Family Γ)
    (x : M.Section Γ A) (σ : M.Substitution Δ Γ) :
    HEq (F.substitution (M.pathSub A x σ))
      (N.pathSub (F.family A) (F.mapTm x) (F.substitution σ)) := by
  have hf : HEq (F.family (M.pathFamily (M.subTy A σ) (M.subTm x σ)))
      (N.pathFamily (N.subTy (F.family A) (F.substitution σ))
        (N.subTm (F.mapTm x) (F.substitution σ))) :=
    (F.pathFamily _ _).trans (N.pathFamily_heq rfl (heq_of_eq (F.subTy A σ)) (F.subTm x σ))
  have he : F.context (M.extend Δ (M.subTy A σ)) =
      N.extend (F.context Δ) (N.subTy (F.family A) (F.substitution σ)) :=
    (F.extend _).trans (N.extend_heq rfl (heq_of_eq (F.subTy A σ)))
  have hp : F.context (M.pathContext (M.subTy A σ) (M.subTm x σ)) =
      N.pathContext (N.subTy (F.family A) (F.substitution σ))
        (N.subTm (F.mapTm x) (F.substitution σ)) :=
    (F.pathContext _ _).trans (N.pathContext_heq rfl (heq_of_eq (F.subTy A σ)) (F.subTm x σ))
  apply (F.pair _ _ _).trans
  apply N.pair_heq (F.extend A) hp (F.pathFamily A x)
  · apply (heq_of_eq (F.comp _ _)).trans
    exact N.comp_heq (F.extend A) he hp (F.lift A σ)
      ((F.weaken _).trans (N.weaken_heq he hf))
  · apply (cast_heq _ _).trans
    apply HEq.trans _ (cast_heq _ _).symm
    apply (F.section_heq rfl (heq_of_eq (M.pathSub_type A x σ)) (cast_heq _ _)).trans
    exact (F.mapVariable _).trans (N.variable_heq he hf)

theorem pathTail (F : StructuralMap M N) {Γ Δ n} (A : M.Family Γ)
    (x : M.Section Γ A) (T : Telescope M (M.pathContext A x) n)
    (σ : M.Substitution Δ Γ) :
    HEq (F.telescope (M.pathTail A x T σ))
      (N.pathTail (F.family A) (F.mapTm x) (F.pathTelescope A x T) (F.substitution σ)) := by
  apply (heq_of_eq (F.telescope_pullback T _)).trans
  exact Telescope.pullback_heq N (F.pathContext A x)
    ((F.pathContext _ _).trans (N.pathContext_heq rfl (heq_of_eq (F.subTy A σ)) (F.subTm x σ)))
    (cast_heq _ _).symm (F.pathSub A x σ)

theorem pathTailMap (F : StructuralMap M N) {Γ Δ n} (A : M.Family Γ)
    (x : M.Section Γ A) (T : Telescope M (M.pathContext A x) n)
    (σ : M.Substitution Δ Γ) :
    HEq (F.substitution (M.pathTailMap A x T σ))
      (N.pathTailMap (F.family A) (F.mapTm x) (F.pathTelescope A x T) (F.substitution σ)) := by
  apply (F.telescope_liftSub T _).trans
  exact Telescope.liftSub_heq N (F.pathContext A x)
    ((F.pathContext _ _).trans (N.pathContext_heq rfl (heq_of_eq (F.subTy A σ)) (F.subTm x σ)))
    (cast_heq _ _).symm (F.pathSub A x σ)


theorem square_commutes (F : StructuralMap M N) {Γ Γ' Δ Δ'}
    (S : M.Substitution Δ Γ) (S' : M.Substitution Δ' Γ')
    (K : M.Substitution Γ' Γ) (L : M.Substitution Δ' Δ)
    (h : M.compSub K S' = M.compSub S L) :
    N.compSub (F.substitution K) (F.substitution S') =
      N.compSub (F.substitution S) (F.substitution L) := by
  rw [← F.comp, ← F.comp, h]

theorem squareLift (F : StructuralMap M N) {Γ Γ' Δ Δ'}
    (S : M.Substitution Δ Γ) (S' : M.Substitution Δ' Γ')
    (K : M.Substitution Γ' Γ) (L : M.Substitution Δ' Δ)
    (h : M.compSub K S' = M.compSub S L) (A : M.Family Γ) :
    HEq (F.substitution (M.squareLift S S' K L h A))
      (N.squareLift (F.substitution S) (F.substitution S') (F.substitution K)
        (F.substitution L) (F.square_commutes S S' K L h) (F.family A)) := by
  have ht : F.family (M.subTy (M.subTy A K) S') =
      N.subTy (N.subTy (F.family A) (F.substitution K)) (F.substitution S') := by
    rw [F.subTy, F.subTy]
  have hc : F.context (M.extend Δ' (M.subTy (M.subTy A K) S')) =
      N.extend (F.context Δ')
        (N.subTy (N.subTy (F.family A) (F.substitution K)) (F.substitution S')) :=
    (F.extend _).trans (N.extend_heq rfl (heq_of_eq ht))
  apply (F.pair _ _ _).trans
  apply N.pair_heq rfl hc (heq_of_eq (F.subTy A S))
  · apply (heq_of_eq (F.comp _ _)).trans
    exact N.comp_heq rfl rfl hc HEq.rfl
      ((F.weaken _).trans (N.weaken_heq rfl (heq_of_eq ht)))
  · apply (cast_heq _ _).trans
    apply HEq.trans _ (cast_heq _ _).symm
    apply (F.section_heq rfl (heq_of_eq (M.square_variable_type S S' K L h A))
      (cast_heq _ _)).trans
    exact (F.mapVariable _).trans (N.variable_heq rfl (heq_of_eq ht))

theorem telescope_square (F : StructuralMap M N) {Γ Γ' Δ Δ'}
    (S : M.Substitution Δ Γ) (S' : M.Substitution Δ' Γ')
    (K : M.Substitution Γ' Γ) (L : M.Substitution Δ' Δ)
    (h : M.compSub K S' = M.compSub S L) {n} (T : Telescope M Γ n) :
    HEq (F.substitution (Telescope.square M S S' K L h T).val)
      (Telescope.square N (F.substitution S) (F.substitution S') (F.substitution K)
        (F.substitution L) (F.square_commutes S S' K L h) (F.telescope T)).val := by
  induction T generalizing Γ' Δ Δ' with
  | nil => simp only [telescope, Telescope.square]; rfl
  | cons A T ih =>
    rw [Telescope.square, telescope, Telescope.square]
    apply (ih _ _ _ _ (M.squareLift_forward S S' K L h A)).trans
    apply Telescope.square_heq N (F.extend A)
      ((F.extend _).trans (N.extend_heq rfl (heq_of_eq (F.subTy A K))))
      ((F.extend _).trans (N.extend_heq rfl (heq_of_eq (F.subTy A S))))
      ((F.extend _).trans (N.extend_heq rfl (heq_of_eq (by rw [F.subTy, F.subTy]))))
      (F.lift A S) _ (F.lift A K) (F.squareLift S S' K L h A) (cast_heq _ _).symm
    apply (F.lift _ S').trans
    exact N.lift_heq rfl rfl (heq_of_eq (F.subTy A K)) HEq.rfl


theorem branchMap (F : StructuralMap M N) {Γ Δ n} (A : M.Family Γ)
    (x : M.Section Γ A) (T : Telescope M (M.pathContext A x) n)
    (σ : M.Substitution Δ Γ) :
    HEq (F.substitution (M.branchMap A x T σ))
      (N.branchMap (F.family A) (F.mapTm x) (F.pathTelescope A x T) (F.substitution σ)) := by
  apply (F.telescope_square _ _ _ _ _ T).trans
  apply Telescope.square_heq N (F.pathContext A x)
    ((F.pathContext _ _).trans (N.pathContext_heq rfl (heq_of_eq (F.subTy A σ)) (F.subTm x σ)))
    rfl rfl (F.rootSub A x) _ (F.pathSub A x σ) HEq.rfl (cast_heq _ _).symm
  exact (F.rootSub _ _).trans (N.rootSub_heq rfl (heq_of_eq (F.subTy A σ)) (F.subTm x σ))

def jMotive (F : StructuralMap M N) {Γ n} (A : M.Family Γ)
    (x : M.Section Γ A) (T : Telescope M (M.pathContext A x) n)
    (C : M.Family T.total) : N.Family (F.pathTelescope A x T).total :=
  cast (congrArg N.Family (F.pathTelescope_total A x T)) (F.family C)

theorem rootTelescope_total (F : StructuralMap M N) {Γ n} (A : M.Family Γ)
    (x : M.Section Γ A) (T : Telescope M (M.pathContext A x) n) :
    F.context (Telescope.total M (Telescope.pullback M T (M.rootSub A x))) =
      Telescope.total N (Telescope.pullback N (F.pathTelescope A x T)
        (N.rootSub (F.family A) (F.mapTm x))) :=
  (F.telescope_total _).trans (congrArg (Telescope.total N) (F.rootTelescope A x T))

theorem jBranch_type (F : StructuralMap M N) {Γ n} (A : M.Family Γ)
    (x : M.Section Γ A) (T : Telescope M (M.pathContext A x) n)
    (C : M.Family T.total) :
    HEq (F.family (M.subTy C (M.rootTail A x T)))
      (N.subTy (F.jMotive A x T C) (N.rootTail (F.family A) (F.mapTm x) (F.pathTelescope A x T))) :=
  (heq_of_eq (F.subTy C _)).trans
    (N.subTy_heq (F.pathTelescope_total A x T) (F.rootTelescope_total A x T)
      (cast_heq _ _).symm (F.rootTail A x T))

def jBranch (F : StructuralMap M N) {Γ n} (A : M.Family Γ)
    (x : M.Section Γ A) (T : Telescope M (M.pathContext A x) n)
    (C : M.Family T.total)
    (d : M.Section (Telescope.total M (Telescope.pullback M T (M.rootSub A x)))
      (M.subTy C (M.rootTail A x T))) :
    N.Section (Telescope.total N (Telescope.pullback N (F.pathTelescope A x T)
      (N.rootSub (F.family A) (F.mapTm x))))
      (N.subTy (F.jMotive A x T C) (N.rootTail (F.family A) (F.mapTm x) (F.pathTelescope A x T))) :=
  N.castSection (F.rootTelescope_total A x T) (F.jBranch_type A x T C) (F.mapTm d)

theorem jBranch_heq (F : StructuralMap M N) {Γ n} (A : M.Family Γ)
    (x : M.Section Γ A) (T : Telescope M (M.pathContext A x) n)
    (C : M.Family T.total)
    (d : M.Section (Telescope.total M (Telescope.pullback M T (M.rootSub A x)))
      (M.subTy C (M.rootTail A x T))) : HEq (F.jBranch A x T C d) (F.mapTm d) :=
  N.castSection_heq _ _ _


theorem reindexedRootTelescope_total (F : StructuralMap M N) {Γ Δ n} (A : M.Family Γ)
    (x : M.Section Γ A) (T : Telescope M (M.pathContext A x) n)
    (σ : M.Substitution Δ Γ) :
    F.context (Telescope.total M (Telescope.pullback M (M.pathTail A x T σ)
      (M.rootSub (M.subTy A σ) (M.subTm x σ)))) =
    Telescope.total N (Telescope.pullback N
      (N.pathTail (F.family A) (F.mapTm x) (F.pathTelescope A x T) (F.substitution σ))
      (N.rootSub (N.subTy (F.family A) (F.substitution σ))
        (N.subTm (F.mapTm x) (F.substitution σ)))) := by
  apply (F.telescope_total _).trans
  apply Telescope.total_heq N rfl
  apply (heq_of_eq (F.telescope_pullback _ _)).trans
  exact Telescope.pullback_heq N
    ((F.pathContext _ _).trans (N.pathContext_heq rfl (heq_of_eq (F.subTy A σ)) (F.subTm x σ)))
    rfl (F.pathTail A x T σ)
    ((F.rootSub _ _).trans (N.rootSub_heq rfl (heq_of_eq (F.subTy A σ)) (F.subTm x σ)))

theorem reindexBranch (F : StructuralMap M N) {Γ Δ n} (A : M.Family Γ)
    (x : M.Section Γ A) (T : Telescope M (M.pathContext A x) n)
    (σ : M.Substitution Δ Γ) (C : M.Family T.total)
    (d : M.Section (Telescope.total M (Telescope.pullback M T (M.rootSub A x)))
      (M.subTy C (M.rootTail A x T))) :
    HEq (F.mapTm (M.reindexBranch A x T σ C d))
      (N.reindexBranch (F.family A) (F.mapTm x) (F.pathTelescope A x T)
        (F.substitution σ) (F.jMotive A x T C) (F.jBranch A x T C d)) := by
  apply (F.section_heq rfl (heq_of_eq (M.branchMap_type A x T σ C)) (cast_heq _ _)).trans
  apply (F.subTm _ _).trans
  apply HEq.trans _ (cast_heq _ _).symm
  exact N.subTm_heq (F.rootTelescope_total A x T) (F.reindexedRootTelescope_total A x T σ)
    (F.jBranch_type A x T C) (F.jBranch_heq A x T C d).symm (F.branchMap A x T σ)


@[simp] theorem telescope_identity {Γ n} (T : Telescope M Γ n) :
    (identityMap M).telescope T = T := by
  induction T with
  | nil => rfl
  | cons A T ih => exact congrArg (Telescope.cons A) ih

theorem telescope_compose (G : StructuralMap N P) (F : StructuralMap M N)
    {Γ n} (T : Telescope M Γ n) :
    G.telescope (F.telescope T) = (compose G F).telescope T := by
  induction T with
  | nil => rfl
  | cons A T ih =>
    apply eq_of_heq
    apply Telescope.cons_heq P rfl HEq.rfl
    apply (cast_heq _ _).trans
    apply (G.telescope_heq (F.extend A).symm (cast_heq _ _)).trans
    exact (heq_of_eq ih).trans (cast_heq _ _).symm

@[simp] theorem pathTelescope_identity {Γ n} (A : M.Family Γ) (x : M.Section Γ A)
    (T : Telescope M (M.pathContext A x) n) :
    (identityMap M).pathTelescope A x T = T := telescope_identity T

theorem pathTelescope_compose (G : StructuralMap N P) (F : StructuralMap M N)
    {Γ n} (A : M.Family Γ) (x : M.Section Γ A) (T : Telescope M (M.pathContext A x) n) :
    (compose G F).pathTelescope A x T =
      G.pathTelescope (F.family A) (F.mapTm x) (F.pathTelescope A x T) := by
  apply eq_of_heq
  apply (cast_heq _ _).trans
  apply (heq_of_eq (telescope_compose G F T).symm).trans
  apply HEq.trans _ (cast_heq _ _).symm
  exact G.telescope_heq (F.pathContext A x) (cast_heq _ _).symm

end StructuralMap


/-- A map of supported models preserves the primitive contextual eliminator.
All telescope, motive and branch comparisons used in this law are constructed
from its structural map. No derived client theorem is a field. -/
structure ModelMap (M : Model.{u}) (N : Model.{v}) extends
    StructuralMap M.toStructuralModel N.toStructuralModel where
  mapJ : ∀ {Γ n} (A : M.Family Γ) (x : M.Section Γ A)
    (T : StructuralModel.Telescope M.toStructuralModel (M.toStructuralModel.pathContext A x) n)
    (C : M.Family (StructuralModel.Telescope.total M.toStructuralModel T))
    (d : M.Section
      (StructuralModel.Telescope.total M.toStructuralModel
        (StructuralModel.Telescope.pullback M.toStructuralModel T (M.toStructuralModel.rootSub A x)))
      (M.subTy C (M.toStructuralModel.rootTail A x T))),
    HEq (mapTm (M.j A x T C d))
      (N.j (family A) (mapTm x) (toStructuralMap.pathTelescope A x T)
        (toStructuralMap.jMotive A x T C) (toStructuralMap.jBranch A x T C d))


namespace ModelMap
open StructuralModel
variable {M : Model.{u}} {N : Model.{v}} {P : Model.{w}}

def identityMap (M : Model.{u}) : ModelMap M M where
  toStructuralMap := StructuralMap.identityMap M.toStructuralModel
  mapJ A x T C d := by
    apply M.j_heq rfl HEq.rfl HEq.rfl
      (heq_of_eq (StructuralMap.pathTelescope_identity A x T).symm)
      (cast_heq _ _).symm
    exact (StructuralMap.jBranch_heq (StructuralMap.identityMap M.toStructuralModel) A x T C d).symm

def compose (G : ModelMap N P) (F : ModelMap M N) : ModelMap M P where
  toStructuralMap := StructuralMap.compose G.toStructuralMap F.toStructuralMap
  mapJ A x T C d := by
    apply (G.section_heq (F.pathTelescope_total A x T) (cast_heq _ _).symm (F.mapJ A x T C d)).trans
    apply (G.mapJ _ _ _ _ _).trans
    apply P.j_heq rfl HEq.rfl HEq.rfl
      (heq_of_eq (StructuralMap.pathTelescope_compose G.toStructuralMap F.toStructuralMap A x T).symm)
    · apply (cast_heq _ _).trans
      apply HEq.trans _ (cast_heq _ _).symm
      exact G.family_heq (F.pathTelescope_total A x T).symm (cast_heq _ _)
    · apply (G.jBranch_heq _ _ _ _ _).trans
      apply HEq.trans _ (StructuralMap.jBranch_heq _ A x T C d).symm
      exact G.section_heq (F.rootTelescope_total A x T).symm (F.jBranch_type A x T C).symm
        (F.jBranch_heq A x T C d)

@[simp] theorem compose_identity (F : ModelMap M N) : compose (identityMap N) F = F := by
  cases F; rfl

@[simp] theorem identity_compose (F : ModelMap M N) : compose F (identityMap M) = F := by
  cases F; rfl

theorem compose_assoc {Q : Model} (H : ModelMap P Q) (G : ModelMap N P) (F : ModelMap M N) :
    compose (compose H G) F = compose H (compose G F) := by
  cases F; cases G; cases H; rfl


/-- A mapped eliminator remains compatible with substitution of its entire
finite tail. This is an application of primitive J preservation and the derived
branch transport, not an extra map law. -/
theorem j_substitution (F : ModelMap M N) {Γ Δ n} (A : M.Family Γ)
    (x : M.Section Γ A)
    (T : Telescope M.toStructuralModel (M.toStructuralModel.pathContext A x) n)
    (C : M.Family T.total)
    (d : M.Section (Telescope.total M.toStructuralModel
      (Telescope.pullback M.toStructuralModel T (M.toStructuralModel.rootSub A x)))
      (M.subTy C (M.toStructuralModel.rootTail A x T)))
    (σ : M.Substitution Δ Γ) :
    HEq (F.mapTm (M.subTm (M.j A x T C d) (M.toStructuralModel.pathTailMap A x T σ)))
      (N.j (N.subTy (F.family A) (F.substitution σ))
        (N.subTm (F.mapTm x) (F.substitution σ))
        (N.toStructuralModel.pathTail (F.family A) (F.mapTm x)
          (F.pathTelescope A x T) (F.substitution σ))
        (N.subTy (F.jMotive A x T C)
          (N.toStructuralModel.pathTailMap (F.family A) (F.mapTm x)
            (F.pathTelescope A x T) (F.substitution σ)))
        (N.toStructuralModel.reindexBranch (F.family A) (F.mapTm x)
          (F.pathTelescope A x T) (F.substitution σ) (F.jMotive A x T C)
          (F.jBranch A x T C d))) := by
  apply (F.subTm _ _).trans
  apply HEq.trans _ (N.j_sub _ _ _ _ _ _)
  apply N.toStructuralModel.subTm_heq (F.pathTelescope_total A x T)
    ((F.telescope_total _).trans (Telescope.total_heq N.toStructuralModel
      ((F.pathContext _ _).trans (N.toStructuralModel.pathContext_heq rfl
        (heq_of_eq (F.subTy A σ)) (F.subTm x σ))) (F.pathTail A x T σ)))
    (cast_heq _ _).symm (F.mapJ A x T C d) (F.pathTailMap A x T σ)

end ModelMap

end SquareKit.Internal.PathTransport.Typed
