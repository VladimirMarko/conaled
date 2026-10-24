import SquareKit.Internal.Graph

/-! Experimental typed representation K of the bounded graph core image.
`Code p q` represents a lambda from a proof of p to a proof of q.
Its constructors are inspectable data, unlike the source `Derives : Prop`.
Native denotation validates the restricted primitive schemas; installed Lean
constant identification and expression emission remain separate obligations.
See `docs/research/graph-target-implementation.md`.
-/
namespace SquareKit.Internal.GraphTarget
universe v
abbrev Ty := Graph.GraphSort

inductive Term (Γ : List Ty) : Ty → Type where
  | var : Var Γ s → Term Γ s
  | app : Graph.Arrow s t → Term Γ s → Term Γ t

abbrev Sub (Γ Δ : List Ty) := ∀ {s}, Var Γ s → Term Δ s

def Term.subst (σ : Sub Γ Δ) : Term Γ s → Term Δ s
  | .var x => σ x
  | .app f t => .app f (t.subst σ)

def Term.shift (t : Term Γ s) : Term (b :: Γ) s :=
  t.subst (fun x => .var (.succ x))

def Sub.lift (σ : Sub Γ Δ) : Sub (b :: Γ) (b :: Δ)
  | _, .zero => .var .zero
  | _, .succ x => (σ x).shift

inductive Formula : List Ty → Type where
  | eq : Term Γ s → Term Γ s → Formula Γ
  | conj : Formula Γ → Formula Γ → Formula Γ
  | ex : Formula (s :: Γ) → Formula Γ

def Formula.subst (σ : Sub Γ Δ) : Formula Γ → Formula Δ
  | .eq a b => .eq (a.subst σ) (b.subst σ)
  | .conj p q => .conj (p.subst σ) (q.subst σ)
  | .ex p => .ex (p.subst σ.lift)

def Formula.shift (p : Formula Γ) : Formula (s :: Γ) :=
  p.subst (fun x => .var (.succ x))

def single (t : Term Γ s) : Sub (s :: Γ) Γ
  | _, .zero => t
  | _, .succ x => .var x

def Formula.instantiate (p : Formula (s :: Γ)) (t : Term Γ s) :=
  p.subst (single t)

/-- Typed core-image schemas. Every constructor denotes a proof lambda.
`cut` is application/composition; `subst` is capture-avoiding simultaneous
substitution before emission. No semantic-validity constructor is admitted. -/
inductive Code : {Γ : List Ty} → Formula Γ → Formula Γ → Type where
  | ident : Code p p
  | cut : Code p q → Code q r → Code p r
  | left : Code (.conj p q) p
  | right : Code (.conj p q) q
  | pair : Code p q → Code p r → Code p (.conj q r)
  | refl : Code p (.eq t t)
  | symm : Code p (.eq a b) → Code p (.eq b a)
  | trans : Code p (.eq a b) → Code p (.eq b c) → Code p (.eq a c)
  | congr : Code p (.eq a b) → Code p (.eq (.app f a) (.app f b))
  | intro (p : Formula (s :: Γ)) (t : Term Γ s) :
      Code (p.instantiate t) (.ex p)
  | subst (σ : Sub Γ Δ) : Code p q → Code (p.subst σ) (q.subst σ)
  | elimWith : Code (.conj h.shift p) q.shift → Code (.conj h (.ex p)) q
  | elim : Code p q.shift → Code (.ex p) q


def Term.eval (M : Interpretation Graph.Arrow) (ρ : Env M Γ) : Term Γ s → M.Carrier s
  | .var x => ρ x
  | .app f t => M.arrow f (t.eval M ρ)

def Formula.eval (M : Interpretation Graph.Arrow) (ρ : Env M Γ) : Formula Γ → Prop
  | .eq a b => a.eval M ρ = b.eval M ρ
  | .conj p q => p.eval M ρ ∧ q.eval M ρ
  | .ex p => ∃ x, p.eval M (ρ.extend x)

theorem term_subst (M : Interpretation Graph.Arrow) (σ : Sub Γ Δ) (ρ : Env M Δ) (t : Term Γ s) :
    (t.subst σ).eval M ρ = t.eval M (fun x => (σ x).eval M ρ) := by
  induction t with
  | var => rfl
  | app f t ih => simp only [Term.subst, Term.eval, ih]

theorem term_shift (M : Interpretation Graph.Arrow) (ρ : Env M Γ) (x : M.Carrier b) (t : Term Γ s) :
    t.shift.eval M (ρ.extend x) = t.eval M ρ := by
  simp only [Term.shift, term_subst, Term.eval, Env.extend]

theorem formula_subst (M : Interpretation Graph.Arrow) (p : Formula Γ) (σ : Sub Γ Δ) (ρ : Env M Δ) :
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

theorem formula_shift (M : Interpretation Graph.Arrow) (p : Formula Γ) (ρ : Env M Γ) (x : M.Carrier s) :
    p.shift.eval M (ρ.extend x) ↔ p.eval M ρ := by
  simpa only [Formula.shift, Term.eval, Env.extend] using
    formula_subst M p (fun i => .var (.succ i)) (ρ.extend x)

theorem formula_instantiate (M : Interpretation Graph.Arrow) (p : Formula (s :: Γ))
    (t : Term Γ s) (ρ : Env M Γ) :
    (p.instantiate t).eval M ρ ↔ p.eval M (ρ.extend (t.eval M ρ)) := by
  rw [Formula.instantiate, formula_subst]
  have h : (fun {s} (i : Var _ s) => (single t i).eval M ρ) = (fun {s} (i : Var _ s) => ρ.extend (t.eval M ρ) i) := by
    funext s i
    cases i <;> rfl
  rw [h]

def Valid (M : Interpretation Graph.Arrow) (p q : Formula Γ) : Prop :=
  ∀ ρ, p.eval M ρ → q.eval M ρ

theorem sound (M : Interpretation Graph.Arrow) (d : Code p q) : Valid M p q := by
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

/-- Native observation identifies proofs, but does not identify their code. -/
theorem proof_irrel (M : Interpretation Graph.Arrow) {p q : Formula Γ}
    (d e : Code p q) (ρ : Env M Γ) (h : p.eval M ρ) :
    sound M d ρ h = sound M e ρ h := Subsingleton.elim _ _

/-- Beta for the implication application represented by `cut`. -/
theorem cut_beta (M : Interpretation Graph.Arrow) {p q r : Formula Γ}
    (d : Code p q) (e : Code q r) (ρ : Env M Γ) (h : p.eval M ρ) :
    sound M (.cut d e) ρ h = sound M e ρ (sound M d ρ h) := Subsingleton.elim _ _

/-- Iota for the admitted conjunction eliminator. -/
theorem left_iota (M : Interpretation Graph.Arrow) {p q r : Formula Γ}
    (d : Code p q) (e : Code p r) (ρ : Env M Γ) (h : p.eval M ρ) :
    sound M (.cut (.pair d e) .left) ρ h = sound M d ρ h := Subsingleton.elim _ _

theorem right_iota (M : Interpretation Graph.Arrow) {p q r : Formula Γ}
    (d : Code p q) (e : Code p r) (ρ : Env M Γ) (h : p.eval M ρ) :
    sound M (.cut (.pair d e) .right) ρ h = sound M e ρ h := Subsingleton.elim _ _

/-- Existential introduction uses the evaluated term as witness. -/
theorem intro_beta (M : Interpretation Graph.Arrow) (p : Formula (s :: Γ))
    (t : Term Γ s) (ρ : Env M Γ) (h : (p.instantiate t).eval M ρ) :
    sound M (.intro p t) ρ h =
      (⟨t.eval M ρ, (formula_instantiate M p t ρ).mp h⟩ : (Formula.ex p).eval M ρ) :=
  Subsingleton.elim _ _

/-- Iota for existential elimination into the fixed proposition q. -/
theorem elim_iota (M : Interpretation Graph.Arrow) {p : Formula (s :: Γ)}
    {q : Formula Γ} (d : Code p q.shift) (ρ : Env M Γ) (x : M.Carrier s)
    (h : p.eval M (ρ.extend x)) :
    sound M (.elim d) ρ ⟨x, h⟩ =
      (formula_shift M q ρ x).mp (sound M d (ρ.extend x) h) := Subsingleton.elim _ _

/-- Declaration payload before assigning a fresh installed theorem name.
The external universe parameter is fixed by each interpretation. Carrier and
arrow parameters precede the ordered endpoint context and proof hypothesis. -/
structure Declaration where
  context : List Ty
  premise : Formula context
  conclusion : Formula context
  code : Code premise conclusion

/-- Universal closure over the declaration telescope in the native model. -/
def Declaration.denote (d : Declaration) : Prop :=
  ∀ (M : Interpretation.{0,v} Graph.Arrow) (ρ : Env M d.context),
    d.premise.eval M ρ → d.conclusion.eval M ρ

theorem declaration_sound (d : Declaration) : Declaration.denote.{v} d :=
  fun M => sound M d.code

end SquareKit.Internal.GraphTarget
