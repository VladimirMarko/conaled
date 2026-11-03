/-! Opt-in many-sorted binary atoms, equality, conjunction and existential proofs.
Syntax carries no Set interpretation. Contexts may be empty.
Experimental Set slices of issues #38 and #45. Scope and remaining model work:
`docs/research/internal-languages-lean.md`.
-/
namespace SquareKit.Internal
universe u v
variable {S : Type u} {F : S → S → Type u}

/-- The equality-only signature has no relation symbols to interpret. -/
abbrev NoRelations (_s _t : S) : Type u := PEmpty
variable {P : S → S → Type u}

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

inductive FormulaCore (F P : S → S → Type u) : List S → Type u where
  | atom : P s t → Term F Γ s → Term F Γ t → FormulaCore F P Γ
  | eq : Term F Γ s → Term F Γ s → FormulaCore F P Γ
  | conj : FormulaCore F P Γ → FormulaCore F P Γ → FormulaCore F P Γ
  | ex : FormulaCore F P (s :: Γ) → FormulaCore F P Γ

/-- Equality-only clients omit the empty relation signature. -/
abbrev Formula (F : S → S → Type u) (Γ : List S)
    (P : S → S → Type u := NoRelations) := FormulaCore F P Γ

def FormulaCore.subst (σ : Sub F Γ Δ) : Formula F Γ P → Formula F Δ P
  | .atom r a b => .atom r (a.subst σ) (b.subst σ)
  | .eq a b => .eq (a.subst σ) (b.subst σ)
  | .conj p q => .conj (p.subst σ) (q.subst σ)
  | .ex p => .ex (p.subst σ.lift)

def FormulaCore.shift (p : Formula F Γ P) : Formula F (s :: Γ) P :=
  p.subst (fun x => .var (.succ x))

def single (t : Term F Γ s) : Sub F (s :: Γ) Γ
  | _, .zero => t
  | _, .succ x => .var x

def FormulaCore.instantiate (p : Formula F (s :: Γ) P) (t : Term F Γ s) :=
  p.subst (single t)

/-- Restricted sequent calculus; no semantic-validity constructor. -/
inductive Derives : {Γ : List S} → Formula F Γ P → Formula F Γ P → Prop where
  | ident : Derives p p
  | cut : Derives p q → Derives q r → Derives p r
  | left : Derives (.conj p q) p
  | right : Derives (.conj p q) q
  | pair : Derives p q → Derives p r → Derives p (.conj q r)
  | refl : Derives p (.eq t t)
  | symm : Derives p (.eq a b) → Derives p (.eq b a)
  | trans : Derives p (.eq a b) → Derives p (.eq b c) → Derives p (.eq a c)
  | congr : Derives p (.eq a b) → Derives p (.eq (.app f a) (.app f b))
  | intro (p : Formula F (s :: Γ) P) (t : Term F Γ s) :
      Derives (p.instantiate t) (.ex p)
  | subst (σ : Sub F Γ Δ) : Derives p q → Derives (p.subst σ) (q.subst σ)
  | elimWith : Derives (.conj h.shift p) q.shift → Derives (.conj h (.ex p)) q
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
theorem existsIntro (p : Formula F (s :: Γ) P) (t : Term F Γ s) :
     Derives (p.instantiate t) (.ex p) := .intro p t
theorem existsWitness (t : Term F Γ s) (h : Derives q (p.instantiate t)) :
    Derives q (.ex p) := .cut h (.intro p t)
theorem existsElim (h : Derives p q.shift) : Derives (.ex p) q := .elim h
theorem substitute (σ : Sub F Γ Δ) (h : Derives p q) :
    Derives (p.subst σ) (q.subst σ) := .subst σ h
theorem weaken (h : Derives p q) : Derives (p.shift (s := s)) q.shift :=
  substitute (fun x => .var (.succ x)) h
theorem existsElimWith (d : Derives (.conj h.shift p) q.shift) :
    Derives (.conj h (.ex p)) q := .elimWith d
end Rules

structure Interpretation (F : S → S → Type u)
    (P : S → S → Type u := NoRelations) where
  Carrier : S → Type v
  arrow : F s t → Carrier s → Carrier t
  /-- Empty relation signatures need no adapter field. The default predicate
  is false; nonempty signatures can supply any intended interpretation. -/
  relation : P s t → Carrier s → Carrier t → Prop := fun _ _ _ => False

abbrev Env (M : Interpretation.{u,v} F P) (Γ : List S) := ∀ {s}, Var Γ s → M.Carrier s

def Env.extend {M : Interpretation F P} (x : M.Carrier s) (ρ : Env M Γ) : Env M (s :: Γ)
  | _, .zero => x
  | _, .succ i => ρ i

def Term.eval (M : Interpretation F P) (ρ : Env M Γ) : Term F Γ s → M.Carrier s
  | .var x => ρ x
  | .app f t => M.arrow f (t.eval M ρ)

def FormulaCore.eval (M : Interpretation F P) (ρ : Env M Γ) : Formula F Γ P → Prop
  | .atom r a b => M.relation r (a.eval M ρ) (b.eval M ρ)
  | .eq a b => a.eval M ρ = b.eval M ρ
  | .conj p q => p.eval M ρ ∧ q.eval M ρ
  | .ex p => ∃ x, p.eval M (ρ.extend x)

theorem term_subst (M : Interpretation F P) (σ : Sub F Γ Δ) (ρ : Env M Δ) (t : Term F Γ s) :
    (t.subst σ).eval M ρ = t.eval M (fun x => (σ x).eval M ρ) := by
  induction t with
  | var => rfl
  | app f t ih => simp only [Term.subst, Term.eval, ih]

theorem term_shift (M : Interpretation F P) (ρ : Env M Γ) (x : M.Carrier b) (t : Term F Γ s) :
    t.shift.eval M (ρ.extend x) = t.eval M ρ := by
  simp only [Term.shift, term_subst, Term.eval, Env.extend]

theorem formula_subst (M : Interpretation F P) (p : Formula F Γ P) (σ : Sub F Γ Δ) (ρ : Env M Δ) :
    (p.subst σ).eval M ρ ↔ p.eval M (fun x => (σ x).eval M ρ) := by
  induction p generalizing Δ with
  | atom r a b => simp only [FormulaCore.subst, FormulaCore.eval, term_subst]
  | eq a b => simp only [FormulaCore.subst, FormulaCore.eval, term_subst]
  | conj p q hp hq => simp only [FormulaCore.subst, FormulaCore.eval, hp, hq]
  | ex p ih =>
    simp only [FormulaCore.subst, FormulaCore.eval]
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

theorem formula_shift (M : Interpretation F P) (p : Formula F Γ P) (ρ : Env M Γ) (x : M.Carrier s) :
    p.shift.eval M (ρ.extend x) ↔ p.eval M ρ := by
  simpa only [FormulaCore.shift, Term.eval, Env.extend] using
    formula_subst M p (fun i => .var (.succ i)) (ρ.extend x)

theorem formula_instantiate (M : Interpretation F P) (p : Formula F (s :: Γ) P)
    (t : Term F Γ s) (ρ : Env M Γ) :
    (p.instantiate t).eval M ρ ↔ p.eval M (ρ.extend (t.eval M ρ)) := by
  rw [FormulaCore.instantiate, formula_subst]
  have h : (fun {s} (i : Var _ s) => (single t i).eval M ρ) = (fun {s} (i : Var _ s) => ρ.extend (t.eval M ρ) i) := by
    funext s i
    cases i <;> rfl
  rw [h]

def Valid (M : Interpretation F P) (p q : Formula F Γ P) : Prop :=
  ∀ ρ, p.eval M ρ → q.eval M ρ

theorem sound (M : Interpretation F P) (d : Derives p q) : Valid M p q := by
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
  | subst σ _ ih =>
    intro ρ h
    exact (formula_subst M _ σ ρ).mpr (ih _ ((formula_subst M _ σ ρ).mp h))
  | elimWith _ ih =>
    intro ρ ⟨hh, x, hx⟩
    exact (formula_shift M _ ρ x).mp
      (ih (ρ.extend x) ⟨(formula_shift M _ ρ x).mpr hh, hx⟩)
  | elim _ ih =>
    intro ρ ⟨x, hx⟩
    exact (formula_shift M _ ρ x).mp (ih (ρ.extend x) hx)

-- Namespace aliases preserve qualified #38 calls without wrapper definitions.
namespace Formula
export FormulaCore (atom eq conj ex subst shift instantiate eval)
end Formula
end SquareKit.Internal
