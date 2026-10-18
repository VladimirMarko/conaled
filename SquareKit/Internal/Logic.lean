/-! Opt-in many-sorted equality, conjunction and existential derivations.
Syntax carries no Set interpretation. Contexts may be empty.
Experimental Set graph slice of issue #38. Scope and remaining model work:
`docs/research/internal-languages-lean.md`, Implemented Set graph slice.
-/
namespace SquareKit.Internal
universe u v
variable {S : Type u} {F : S → S → Type u}

inductive Var : List S → S → Type u where
  | zero : Var (s :: Γ) s
  | succ : Var Γ s → Var (t :: Γ) s

inductive Term (F : S → S → Type u) (Γ : List S) : S → Type u where
  | var : Var Γ s → Term F Γ s
  | app : F s t → Term F Γ s → Term F Γ t

abbrev Sub (F : S → S → Type u) (Γ Δ : List S) := ∀ {s}, Var Γ s → Term F Δ s

def Term.subst (σ : Sub F Γ Δ) : Term F Γ s → Term F Δ s
  | .var x => σ x
  | .app f t => .app f (t.subst σ)

def Term.shift (t : Term F Γ s) : Term F (b :: Γ) s :=
  t.subst (fun x => .var (.succ x))

def Sub.lift (σ : Sub F Γ Δ) : Sub F (b :: Γ) (b :: Δ)
  | _, .zero => .var .zero
  | _, .succ x => (σ x).shift

inductive Formula (F : S → S → Type u) : List S → Type u where
  | eq : Term F Γ s → Term F Γ s → Formula F Γ
  | conj : Formula F Γ → Formula F Γ → Formula F Γ
  | ex : Formula F (s :: Γ) → Formula F Γ

def Formula.subst (σ : Sub F Γ Δ) : Formula F Γ → Formula F Δ
  | .eq a b => .eq (a.subst σ) (b.subst σ)
  | .conj p q => .conj (p.subst σ) (q.subst σ)
  | .ex p => .ex (p.subst σ.lift)

def Formula.shift (p : Formula F Γ) : Formula F (s :: Γ) :=
  p.subst (fun x => .var (.succ x))

def single (t : Term F Γ s) : Sub F (s :: Γ) Γ
  | _, .zero => t
  | _, .succ x => .var x

def Formula.instantiate (p : Formula F (s :: Γ)) (t : Term F Γ s) :=
  p.subst (single t)

/-- Restricted sequent calculus; no semantic-validity constructor. -/
inductive Derives : {Γ : List S} → Formula F Γ → Formula F Γ → Prop where
  | ident : Derives p p
  | cut : Derives p q → Derives q r → Derives p r
  | left : Derives (.conj p q) p
  | right : Derives (.conj p q) q
  | pair : Derives p q → Derives p r → Derives p (.conj q r)
  | refl : Derives p (.eq t t)
  | symm : Derives p (.eq a b) → Derives p (.eq b a)
  | trans : Derives p (.eq a b) → Derives p (.eq b c) → Derives p (.eq a c)
  | congr : Derives p (.eq a b) → Derives p (.eq (.app f a) (.app f b))
  | intro (p : Formula F (s :: Γ)) (t : Term F Γ s) :
      Derives (p.instantiate t) (.ex p)
  | elim : Derives p q.shift → Derives (.ex p) q

/- Named author-facing rules produce explicit derivations. -/
namespace Rules
theorem hypothesis : Derives p p := .ident
theorem cut (h : Derives p q) (k : Derives q r) : Derives p r := .cut h k
theorem andLeft : Derives (.conj p q) p := .left
theorem andRight : Derives (.conj p q) q := .right
theorem andIntro (h : Derives p q) (k : Derives p r) : Derives p (.conj q r) := .pair h k
theorem eqRefl : Derives p (.eq t t) := .refl
theorem eqSymm (h : Derives p (.eq a b)) : Derives p (.eq b a) := .symm h
theorem eqTrans (h : Derives p (.eq a b)) (k : Derives p (.eq b c)) :
     Derives p (.eq a c) := .trans h k
theorem eqCongr (f : F s t) (h : Derives p (.eq a b)) :
     Derives p (.eq (.app f a) (.app f b)) := .congr h
theorem existsIntro (p : Formula F (s :: Γ)) (t : Term F Γ s) :
     Derives (p.instantiate t) (.ex p) := .intro p t
theorem existsElim (h : Derives p q.shift) : Derives (.ex p) q := .elim h
end Rules

structure Interpretation (F : S → S → Type u) where
  Carrier : S → Type v
  arrow : F s t → Carrier s → Carrier t

abbrev Env (M : Interpretation.{u,v} F) (Γ : List S) := ∀ {s}, Var Γ s → M.Carrier s

def Env.extend {M : Interpretation F} (x : M.Carrier s) (ρ : Env M Γ) : Env M (s :: Γ)
  | _, .zero => x
  | _, .succ i => ρ i

def Term.eval (M : Interpretation F) (ρ : Env M Γ) : Term F Γ s → M.Carrier s
  | .var x => ρ x
  | .app f t => M.arrow f (t.eval M ρ)

def Formula.eval (M : Interpretation F) (ρ : Env M Γ) : Formula F Γ → Prop
  | .eq a b => a.eval M ρ = b.eval M ρ
  | .conj p q => p.eval M ρ ∧ q.eval M ρ
  | .ex p => ∃ x, p.eval M (ρ.extend x)

theorem term_subst (M : Interpretation F) (σ : Sub F Γ Δ) (ρ : Env M Δ) (t : Term F Γ s) :
    (t.subst σ).eval M ρ = t.eval M (fun x => (σ x).eval M ρ) := by
  induction t with
  | var => rfl
  | app f t ih => simp only [Term.subst, Term.eval, ih]

theorem term_shift (M : Interpretation F) (ρ : Env M Γ) (x : M.Carrier b) (t : Term F Γ s) :
    t.shift.eval M (ρ.extend x) = t.eval M ρ := by
  simp only [Term.shift, term_subst, Term.eval, Env.extend]

theorem formula_subst (M : Interpretation F) (p : Formula F Γ) (σ : Sub F Γ Δ) (ρ : Env M Δ) :
    (p.subst σ).eval M ρ ↔ p.eval M (fun x => (σ x).eval M ρ) := by
  induction p generalizing Δ with
  | eq a b => simp only [Formula.subst, Formula.eval, term_subst]
  | conj p q hp hq => simp only [Formula.subst, Formula.eval, hp, hq]
  | ex p ih =>
    simp only [Formula.subst, Formula.eval]
    apply exists_congr
    intro x
    rw [ih]
    have h : (fun {s} (i : Var _ s) => (σ.lift i).eval M (ρ.extend x)) =
        (fun {s} (i : Var _ s) => Env.extend x (fun i => (σ i).eval M ρ) i) := by
      funext s i
      cases i with
      | zero => rfl
      | succ i => exact term_shift M ρ x (σ i)
    rw [h]

theorem formula_shift (M : Interpretation F) (p : Formula F Γ) (ρ : Env M Γ) (x : M.Carrier s) :
    p.shift.eval M (ρ.extend x) ↔ p.eval M ρ := by
  simpa only [Formula.shift, Term.eval, Env.extend] using
    formula_subst M p (fun i => .var (.succ i)) (ρ.extend x)

theorem formula_instantiate (M : Interpretation F) (p : Formula F (s :: Γ))
    (t : Term F Γ s) (ρ : Env M Γ) :
    (p.instantiate t).eval M ρ ↔ p.eval M (ρ.extend (t.eval M ρ)) := by
  rw [Formula.instantiate, formula_subst]
  have h : (fun {s} (i : Var _ s) => (single t i).eval M ρ) = (fun {s} (i : Var _ s) => ρ.extend (t.eval M ρ) i) := by
    funext s i
    cases i <;> rfl
  rw [h]

def Valid (M : Interpretation F) (p q : Formula F Γ) : Prop :=
  ∀ ρ, p.eval M ρ → q.eval M ρ

theorem sound (M : Interpretation F) (d : Derives p q) : Valid M p q := by
  induction d with
  | ident => exact fun _ h => h
  | cut _ _ hp hq => exact fun ρ h => hq ρ (hp ρ h)
  | left => exact fun _ h => h.1
  | right => exact fun _ h => h.2
  | pair _ _ hp hq => exact fun ρ h => ⟨hp ρ h, hq ρ h⟩
  | refl => exact fun _ _ => rfl
  | symm _ ih => exact fun ρ h => (ih ρ h).symm
  | trans _ _ hp hq => exact fun ρ h => (hp ρ h).trans (hq ρ h)
  | congr _ ih => exact fun ρ h => congrArg (M.arrow _) (ih ρ h)
  | intro p t => exact fun ρ h => ⟨t.eval M ρ, (formula_instantiate M p t ρ).mp h⟩
  | elim _ ih =>
    intro ρ ⟨x, hx⟩
    exact (formula_shift M _ ρ x).mp (ih (ρ.extend x) hx)
end SquareKit.Internal
