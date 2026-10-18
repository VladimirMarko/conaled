import SquareKit.Internal.Logic
import Mathlib.CategoryTheory.Subfunctor.Image

/-! Experimental presheaf semantics for the restricted internal language (#46).
Sorts have universe `u`, sections universe `max u w`, and the small indexing
category universe `v`. Existence ranges over sections at each object, not global sections.
-/
namespace SquareKit.Internal.Presheaf
open CategoryTheory Opposite
universe u v w
variable {J : Type v} [SmallCategory J]

/-- The pointwise product used for binary relation symbols. -/
def product (A B : Jᵒᵖ ⥤ Type u) : Jᵒᵖ ⥤ Type u where
  obj j := A.obj j × B.obj j
  map f := ↾fun x => (A.map f x.1, B.map f x.2)
  map_id j := by ext x <;> simp
  map_comp f g := by ext x <;> simp

variable {S : Type u} {F P : S → S → Type u}

structure Model (F : S → S → Type u) (P : S → S → Type u := NoRelations) where
  carrier : S → Jᵒᵖ ⥤ Type (max u w)
  arrow : F s t → (carrier s ⟶ carrier t)
  relation : P s t → Subfunctor (product (carrier s) (carrier t)) := fun _ => ⊥

namespace Model
variable (M : Model (J := J) F P)

def fiber (j : Jᵒᵖ) : Interpretation F P where
  Carrier s := (M.carrier s).obj j
  arrow f := (M.arrow f).app j
  relation r x y := (M.relation r).obj j (x, y)

def restrict {j k : Jᵒᵖ} (f : j ⟶ k) (ρ : Env (M.fiber j) Γ) : Env (M.fiber k) Γ :=
  fun {s} i => (M.carrier s).map f (ρ i)

/-- Finite typed environments, including the unique empty environment. -/
abbrev context (Γ : List S) : Jᵒᵖ ⥤ Type (max u w) where
  obj j := Env (M.fiber j) Γ
  map f := ↾M.restrict f
  map_id j := by
    apply ConcreteCategory.hom_ext
    intro ρ
    funext s i
    exact ConcreteCategory.congr_hom ((M.carrier s).map_id j) (ρ i)
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro ρ
    funext s i
    exact ConcreteCategory.congr_hom ((M.carrier s).map_comp f g) (ρ i)

theorem restrict_extend {j k : Jᵒᵖ} (f : j ⟶ k) (ρ : Env (M.fiber j) Γ)
    (x : (M.carrier s).obj j) :
    (fun {t} (i : Var (s :: Γ) t) => M.restrict f (ρ.extend x) i) =
      (fun {t} (i : Var (s :: Γ) t) => Env.extend ((M.carrier s).map f x) (M.restrict f ρ) i) := by
  funext t i; cases i <;> rfl

theorem eval_restrict {j k : Jᵒᵖ} (f : j ⟶ k) (ρ : Env (M.fiber j) Γ) (t : Term F Γ s) :
    t.eval (M.fiber k) (M.restrict f ρ) = (M.carrier s).map f (t.eval (M.fiber j) ρ) := by
  induction t with
  | var => rfl
  | app a t ih =>
    dsimp [Term.eval, fiber] at *
    rw [ih]
    exact NatTrans.naturality_apply (M.arrow a) f _

def term (t : Term F Γ s) : M.context Γ ⟶ M.carrier s where
  app j := ↾fun ρ => t.eval (M.fiber j) ρ
  naturality j k f := by ext ρ; exact M.eval_restrict f ρ t

def substitution (σ : Sub F Γ Δ) : M.context Δ ⟶ M.context Γ where
  app j := ↾fun ρ => fun i => (σ i).eval (M.fiber j) ρ
  naturality j k f := by ext ρ; rename_i s i; exact M.eval_restrict f ρ (σ i)

def projection : M.context (s :: Γ) ⟶ M.context Γ where
  app _ := ↾fun ρ => fun i => ρ (.succ i)

theorem extend_tail (ρ : Env (M.fiber j) (s :: Γ)) :
    (fun {t} (i : Var (s :: Γ) t) => Env.extend (ρ .zero) (fun i => ρ (.succ i)) i) = @ρ := by
  funext t i; cases i <;> rfl

theorem substitution_id : M.substitution (Γ := Γ) (fun i => .var i) = 𝟙 _ := rfl

theorem substitution_comp (σ : Sub F Γ Δ) (τ : Sub F Δ Ξ) :
    M.substitution (fun i => (σ i).subst τ) = M.substitution τ ≫ M.substitution σ := by
  ext j ρ
  rename_i s i
  exact term_subst (M.fiber j) τ ρ (σ i)

theorem term_substitution (σ : Sub F Γ Δ) (t : Term F Γ s) :
    M.term (t.subst σ) = M.substitution σ ≫ M.term t := by
  ext j ρ
  exact term_subst (M.fiber j) σ ρ t

theorem substitution_lift (σ : Sub F Γ Δ) (ρ : Env (M.fiber j) Δ)
    (x : (M.carrier s).obj j) :
    (fun {t} (i : Var (s :: Γ) t) => (M.substitution σ.lift).app j (ρ.extend x) i) =
      (fun {t} (i : Var (s :: Γ) t) => Env.extend x ((M.substitution σ).app j ρ) i) := by
  funext t i
  cases i with
  | zero => rfl
  | succ i => exact term_shift (M.fiber j) ρ x (σ i)

theorem projection_substitution (σ : Sub F Γ Δ) :
    M.substitution (σ.lift (b := s)) ≫ M.projection =
      M.projection ≫ M.substitution σ := by
  ext j ρ
  rename_i t i
  change ((σ i).shift).eval (M.fiber j) ρ = _
  rw [← M.extend_tail ρ]
  exact term_shift (M.fiber j) _ _ (σ i)

/-- Contextual equality of sections, stable by naturality of the terms. -/
def equality (a b : Term F Γ s) : Subfunctor (M.context Γ) where
  obj j ρ := a.eval (M.fiber j) ρ = b.eval (M.fiber j) ρ
  map f := by
    intro ρ h
    change a.eval _ (M.restrict f ρ) = b.eval _ (M.restrict f ρ)
    rw [M.eval_restrict, M.eval_restrict, h]

def atom (r : P s t) (a : Term F Γ s) (b : Term F Γ t) : Subfunctor (M.context Γ) :=
  (M.relation r).preimage
    { app j := ↾fun ρ => (a.eval (M.fiber j) ρ, b.eval (M.fiber j) ρ)
      naturality j k f := by
        ext ρ
        exact Prod.ext (M.eval_restrict f ρ a) (M.eval_restrict f ρ b) }

def formula (M : Model (J := J) F P) : {Γ : List S} → Formula F Γ P → Subfunctor (M.context Γ)
  | _, .atom r a b => M.atom r a b
  | _, .eq a b => M.equality a b
  | _, .conj p q => M.formula p ⊓ M.formula q
  | _, .ex p => (M.formula p).image M.projection

/-- Evaluation of an existential image retains an objectwise witness. -/
theorem image_projection (Q : Subfunctor (M.context (s :: Γ))) (j : Jᵒᵖ)
    (ρ : Env (M.fiber j) Γ) :
    (Q.image M.projection).obj j ρ ↔ ∃ x, Q.obj j (ρ.extend x) := by
  constructor
  · rintro ⟨η, hη, h⟩
    refine ⟨η .zero, ?_⟩
    change (fun {t} (i : Var Γ t) => η (.succ i)) = @ρ at h
    rw [← h, M.extend_tail]
    exact hη
  · rintro ⟨x, hx⟩
    exact ⟨ρ.extend x, hx, rfl⟩

/-- One comparison for every formula; applications need no formula induction. -/
theorem evaluation (p : Formula F Γ P) (j : Jᵒᵖ) (ρ : Env (M.fiber j) Γ) :
    (M.formula p).obj j ρ ↔ p.eval (M.fiber j) ρ := by
  induction p with
  | atom => rfl
  | eq => rfl
  | conj p q hp hq => exact and_congr (hp ρ) (hq ρ)
  | ex p ih =>
    change ((M.formula p).image M.projection).obj j ρ ↔ _
    rw [M.image_projection]
    exact exists_congr (fun x => ih (ρ.extend x))

theorem formula_substitution (p : Formula F Γ P) (σ : Sub F Γ Δ) :
    M.formula (p.subst σ) = (M.formula p).preimage (M.substitution σ) := by
  ext j ρ
  exact (M.evaluation _ j ρ).trans
    ((formula_subst (M.fiber j) p σ ρ).trans (M.evaluation p j _).symm)

/-- Equality substitution specializes the uniform formula comparison. -/
theorem equality_substitution (a b : Term F Γ s) (σ : Sub F Γ Δ) :
    M.equality (a.subst σ) (b.subst σ) = (M.equality a b).preimage (M.substitution σ) :=
  M.formula_substitution (.eq a b) σ

/-- Intersection commutes with reindexing for all context predicates. -/
theorem conjunction_substitution (Q R : Subfunctor (M.context Γ)) (σ : Sub F Γ Δ) :
    (Q ⊓ R).preimage (M.substitution σ) =
      Q.preimage (M.substitution σ) ⊓ R.preimage (M.substitution σ) := rfl

/-- The empty context has one section even when some sort has no sections. -/
theorem empty_context (j : Jᵒᵖ) (ρ η : (M.context []).obj j) : @ρ = @η := by
  funext s i
  nomatch i

/-- Model validity is inclusion of subfunctors, separate from derivability. -/
def Valid (p q : Formula F Γ P) : Prop := M.formula p ≤ M.formula q

theorem sound (d : Derives p q) : M.Valid p q := by
  intro j ρ hp
  exact (M.evaluation q j ρ).mpr
    (Internal.sound (M.fiber j) d ρ ((M.evaluation p j ρ).mp hp))

/-- All interpreted predicates, including existential witnesses, restrict. -/
theorem formula_restrict (p : Formula F Γ P) {j k : Jᵒᵖ} (f : j ⟶ k)
    (ρ : Env (M.fiber j) Γ) (h : (M.formula p).obj j ρ) :
    (M.formula p).obj k (M.restrict f ρ) := (M.formula p).map f h

/-- The existential/reindexing adjunction is Mathlib's image adjunction. -/
theorem exists_adjunction (Q : Subfunctor (M.context (s :: Γ)))
    (R : Subfunctor (M.context Γ)) :
    Q.image M.projection ≤ R ↔ Q ≤ R.preimage M.projection :=
  Subfunctor.image_le_iff _ _ _

/-- Frobenius holds for arbitrary stable predicates, not just syntactic ones. -/
theorem frobenius (Q : Subfunctor (M.context (s :: Γ)))
    (R : Subfunctor (M.context Γ)) :
    (Q ⊓ R.preimage M.projection).image M.projection = Q.image M.projection ⊓ R := by
  ext j ρ
  simp only [Subfunctor.image_obj, Subfunctor.min_obj, Subfunctor.preimage_obj,
    Set.mem_image, Set.mem_inter_iff, Set.mem_preimage]
  constructor
  · rintro ⟨η, ⟨hq, hr⟩, rfl⟩; exact ⟨⟨η, hq, rfl⟩, hr⟩
  · rintro ⟨⟨η, hq, rfl⟩, hr⟩; exact ⟨η, ⟨hq, hr⟩, rfl⟩

/-- Beck–Chevalley for context projection and lifted syntactic substitution. -/
theorem beck_chevalley (Q : Subfunctor (M.context (s :: Γ))) (σ : Sub F Γ Δ) :
    (Q.image M.projection).preimage (M.substitution σ) =
      (Q.preimage (M.substitution σ.lift)).image M.projection := by
  ext j ρ
  change (Q.image M.projection).obj j ((M.substitution σ).app j ρ) ↔
    ((Q.preimage (M.substitution σ.lift)).image M.projection).obj j ρ
  rw [M.image_projection, M.image_projection]
  apply exists_congr
  intro x
  change Q.obj j _ ↔ Q.obj j ((M.substitution σ.lift).app j (ρ.extend x))
  exact iff_of_eq (congrArg (Q.obj j) (M.substitution_lift σ ρ x).symm)

end Model
end SquareKit.Internal.Presheaf
