import Applications.Progress.Feedback
import Dependent

/-! Type-valued certificates over initialized feedback solutions. The Sigma
machine reuses ordinary feedback; projection transports its actual witness. -/
namespace Progress.Feedback.Dependent
open DependentSquares
variable {A B S A' B' T : Type}

def lift (f : Initialized A B S) (C : S → Type)
    (advance : (a : A) → (s : S) → C s → C (f.step (a,s)).2)
    (initial : C f.initial) : Initialized A B (Sigma C) where
  initial := ⟨f.initial,initial⟩
  step := fun (a,z) => ((f.step (a,z.1)).1,⟨(f.step (a,z.1)).2,advance a z.1 z.2⟩)

theorem projection (f : Initialized A B S) (C : S → Type)
    (advance : (a : A) → (s : S) → C s → C (f.step (a,s)).2)
    (initial : C f.initial) (a : Stream A) (n : Nat) :
    (state (lift f C advance initial) a n).1 = state f a n := by
  exact (Feedback.transport (lift f C advance initial) f Eq
    (fun z s => z.1 = s) Eq rfl
    (by rintro x _ ⟨s,c⟩ _ rfl rfl; exact ⟨rfl,rfl⟩) a a (fun _ => rfl)).1 n

def castWitness {C : S → Type} {s t : S} (h : s = t) (c : C s) : C t := h ▸ c

def certificate (f : Initialized A B S) (C : S → Type)
    (advance : (a : A) → (s : S) → C s → C (f.step (a,s)).2)
    (initial : C f.initial) (a : Stream A) (n : Nat) : C (state f a n) :=
  castWitness (projection f C advance initial a n) (state (lift f C advance initial) a n).2

@[simp] theorem certificate_zero (f : Initialized A B S) (C : S → Type)
    (advance : (a : A) → (s : S) → C s → C (f.step (a,s)).2)
    (initial : C f.initial) (a : Stream A) : certificate f C advance initial a 0 = initial := rfl

theorem advance_cast (f : Initialized A B S) (C : S → Type)
    (advance : (a : A) → (s : S) → C s → C (f.step (a,s)).2)
    (a : A) {s t : S} (h : s = t) (c : C s) :
    castWitness (congrArg (fun s => (f.step (a,s)).2) h) (advance a s c) =
      advance a t (castWitness h c) := by
  cases h; rfl

/-- The transported section obeys the supplied dependent recurrence itself. -/
theorem certificate_step (f : Initialized A B S) (C : S → Type)
    (advance : (a : A) → (s : S) → C s → C (f.step (a,s)).2)
    (initial : C f.initial) (a : Stream A) (n : Nat) :
    certificate f C advance initial a (n+1) =
      advance (a n) (state f a n) (certificate f C advance initial a n) :=
  advance_cast f C advance (a n) (projection f C advance initial a n) _

/-- Reindex the actual witnesses, rather than weakening them to mere existence. -/
theorem cast_related {C : S → Type} {D : T → Type} {R : S → T → Prop}
    (E : TyRel R C D) (z : Sigma C) (w : Sigma D) {s : S} {t : T}
    (hs : z.1 = s) (ht : w.1 = t) (related : extRel E z w) :
    ∃ h : R s t, E s t h (castWitness hs z.2) (castWitness ht w.2) := by
  cases hs; cases ht
  exact related

/-- One reusable relational result for arbitrary state-indexed certificates.
The chosen base-step proof also indexes the fiber-step obligation. -/
theorem transport (f : Initialized A B S) (g : Initialized A' B' T)
    (C : S → Type) (D : T → Type)
    (advance : (a : A) → (s : S) → C s → C (f.step (a,s)).2)
    (advance' : (a : A') → (s : T) → D s → D (g.step (a,s)).2)
    (c₀ : C f.initial) (d₀ : D g.initial)
    (I : A → A' → Prop) (R : S → T → Prop) (O : B → B' → Prop)
    (E : TyRel R C D) (h₀ : R f.initial g.initial) (initial : E _ _ h₀ c₀ d₀)
    (baseStep : ∀ a b s t, I a b → R s t →
      O (f.step (a,s)).1 (g.step (b,t)).1 ∧ R (f.step (a,s)).2 (g.step (b,t)).2)
    (fiberStep : ∀ a b s t (hi : I a b) (hr : R s t) c d, E s t hr c d →
      E _ _ (baseStep a b s t hi hr).2 (advance a s c) (advance' b t d))
    (a : Stream A) (b : Stream A') (inputs : ∀ n, I (a n) (b n)) :
    ∀ n, ∃ h : R (state f a n) (state g b n), E _ _ h
      (certificate f C advance c₀ a n) (certificate g D advance' d₀ b n) := by
  have lifted := Feedback.transport (lift f C advance c₀) (lift g D advance' d₀)
    I (extRel E) O ⟨h₀,initial⟩
    (by
      rintro x y ⟨s,c⟩ ⟨t,d⟩ hi ⟨hr,he⟩
      exact ⟨(baseStep x y s t hi hr).1,
        ⟨(baseStep x y s t hi hr).2,fiberStep x y s t hi hr c d he⟩⟩)
    a b inputs
  intro n
  exact cast_related E _ _ (projection f C advance c₀ a n)
    (projection g D advance' d₀ b n) (lifted.1 n)

end Progress.Feedback.Dependent
