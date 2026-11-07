import Mathlib.Tactic

/-! Independent set-family models for the projection-pair and eliminator presentations.
The flag separator covers arbitrary dependent families, but deliberately has no
unrestricted dependent eliminator. It does not model PrimitiveSigma. -/
namespace SquareKit.DependentPairTheoryModels
universe w u v
variable {Γ : Type w} (A : Γ → Type u) (B : (γ : Γ) → A γ → Type v)

/-- Explicit common-fiber transport required by the second beta boundary. -/
def castFiber {X : Type u} (P : X → Type v) {x y : X} (h : x = y) (p : P x) : P y := h ▸ p

/-- Projection-only beta contract on arbitrary contextual families. -/
structure ProjectionModel where
  Pair : Γ → Type (max u v)
  pair : (γ : Γ) → (a : A γ) → B γ a → Pair γ
  first : (γ : Γ) → Pair γ → A γ
  second : (γ : Γ) → (p : Pair γ) → B γ (first γ p)
  first_beta : ∀ γ a b, first γ (pair γ a b) = a
  second_beta : ∀ γ a b,
    castFiber (B γ) (first_beta γ a b) (second γ (pair γ a b)) = b

/-- The ordinary full-family interpretation; both betas are computation. -/
def ordinary : ProjectionModel A B where
  Pair γ := Sigma (B γ)
  pair _ a b := ⟨a,b⟩
  first _ p := p.1
  second _ p := p.2
  first_beta _ _ _ := rfl
  second_beta _ _ _ := rfl

/-- The flag model validates beta in every family, without constant-family restrictions. -/
def flagged : ProjectionModel A B where
  Pair γ := Sigma (B γ) × Bool
  pair _ a b := (⟨a,b⟩,false)
  first _ p := p.1.1
  second _ p := p.1.2
  first_beta _ _ _ := rfl
  second_beta _ _ _ := rfl

namespace ProjectionModel
variable {A B}

/-- Reindex all dependent data by the same context substitution. -/
def reindex (M : ProjectionModel A B) {Δ : Type*} (σ : Δ → Γ) :
    ProjectionModel (A ∘ σ) (fun δ a => B (σ δ) a) where
  Pair δ := M.Pair (σ δ)
  pair δ := M.pair (σ δ)
  first δ := M.first (σ δ)
  second δ := M.second (σ δ)
  first_beta δ := M.first_beta (σ δ)
  second_beta δ := M.second_beta (σ δ)

@[simp] theorem pair_reindex (M : ProjectionModel A B) {Δ : Type*} (σ : Δ → Γ)
    (δ : Δ) (a : A (σ δ)) (b : B (σ δ) a) :
    (M.reindex σ).pair δ a b = M.pair (σ δ) a b := rfl

theorem reindex_comp (M : ProjectionModel A B) {Δ Θ : Type*} (σ : Δ → Γ) (τ : Θ → Δ) :
    (M.reindex σ).reindex τ = M.reindex (σ ∘ τ) := rfl

/-- Eta is a separate specification obligation, not included in ProjectionModel. -/
def Eta (M : ProjectionModel A B) : Prop :=
  ∀ γ p, M.pair γ (M.first γ p) (M.second γ p) = p
end ProjectionModel

theorem ordinary_eta : (ordinary A B).Eta := by intro γ p; cases p; rfl

/-- Dependent elimination for the ordinary interpretation, independent of projection syntax. -/
def splitOrdinary {γ : Γ} (D : (ordinary A B).Pair γ → Type*)
    (branch : ∀ a b, D ((ordinary A B).pair γ a b)) (p : (ordinary A B).Pair γ) : D p :=
  match p with | ⟨a,b⟩ => branch a b

@[simp] theorem splitOrdinary_beta {γ : Γ} (D : (ordinary A B).Pair γ → Type*)
    (branch : ∀ a b, D ((ordinary A B).pair γ a b)) (a : A γ) (b : B γ a) :
    splitOrdinary A B D branch ((ordinary A B).pair γ a b) = branch a b := rfl

/-- Eta fails whenever a fiber is inhabited: the true flag survives in p only. -/
theorem flagged_eta_failure (γ : Γ) (a : A γ) (b : B γ a) : ¬ (flagged A B).Eta := by
  intro h
  have hp := h γ (⟨a,b⟩, true)
  have he := congrArg Prod.snd hp
  change false = true at he
  cases he

/-- Forgetting the flag changes the semantic equality and makes repacking valid. -/
theorem flagged_eta_after_forgetting (γ : Γ) (p : (flagged A B).Pair γ) :
    ((flagged A B).pair γ ((flagged A B).first γ p) ((flagged A B).second γ p)).1 = p.1 := by
  cases p with
  | mk p flag => cases p; rfl

/-- A motive with no inhabitants at the true flag rejects arbitrary dependent elimination. -/
def flagMotive {γ : Γ} (p : (flagged A B).Pair γ) : Type :=
  if p.2 then Empty else PUnit

theorem flagged_no_split (γ : Γ) (a : A γ) (b : B γ a) :
    ¬ Nonempty ((D : (flagged A B).Pair γ → Type) →
      (∀ a b, D ((flagged A B).pair γ a b)) → ∀ p, D p) := by
  rintro ⟨split⟩
  have impossible : Empty := split (flagMotive A B) (fun _ _ => PUnit.unit) (⟨a,b⟩,true)
  exact impossible.elim

/-- Families and sections fixed by the report before choosing syntax or interpretation. -/
abbrev N := Nat
def ClientB (n : N) := Fin (n+2)
def ClientC (n : N) (i : ClientB n) := Fin (i.val+2)
def s (m : N) : N := m+1
def d (k : N) : N := 2*k
def t (m : N) : ClientB (s m) := ⟨m+1, by simp [s]⟩
def sectionU (m : N) : ClientC (s m) (t m) := ⟨m+2, by simp [t]⟩

abbrev ClientContext := (n : N) × (y : ClientB n) × ClientC n y

def sigma (m : N) : ClientContext := ⟨s m, t m, sectionU m⟩
def tau : N → N := d

def selectedSection (γ : ClientContext) : ClientC γ.1 γ.2.1 := γ.2.2

/-- First substitution retains the selected input; the proof is not inhabitant search. -/
theorem selected_sigma (m : N) : selectedSection (sigma m) = sectionU m := rfl

theorem selected_twice (k : N) : selectedSection (sigma (tau k)) = sectionU (d k) := rfl

example : (sigma (tau 2)).1 = 5 := rfl
example : (sigma (tau 2)).2.1 = (⟨5, by decide⟩ : Fin 7) := rfl
example : selectedSection (sigma (tau 2)) = (⟨6, by decide⟩ : Fin 7) := rfl

/-- A different inhabitant fails the selected-value contract. -/
example : selectedSection (sigma (tau 2)) ≠ (⟨0, by decide⟩ : Fin 7) := by
  intro h
  have hv := congrArg Fin.val h
  change (6 : Nat) = 0 at hv
  omega

end SquareKit.DependentPairTheoryModels
