import Mathlib
import SquareKit.RelationalCategory
import Lean.Util.CollectAxioms

/-! Throwaway frontend comparison for #36. Single-sorted regular syntax only.
Not a production doctrine or a presheaf adapter. -/
namespace FrontendComparison

inductive Term where
  | var : Nat → Term
  | app : Nat → Term → Term
  deriving DecidableEq

def Term.subst (s : Nat → Term) : Term → Term
  | .var i => s i
  | .app f t => .app f (t.subst s)

def Term.shift (t : Term) : Term := t.subst (fun i => .var (i + 1))

inductive Formula where
  | eq : Term → Term → Formula
  | conj : Formula → Formula → Formula
  | ex : Formula → Formula
  deriving DecidableEq

def liftSubst (s : Nat → Term) : Nat → Term
  | 0 => .var 0
  | i + 1 => (s i).shift

def Formula.subst (s : Nat → Term) : Formula → Formula
  | .eq a b => .eq (a.subst s) (b.subst s)
  | .conj p q => .conj (p.subst s) (q.subst s)
  | .ex p => .ex (p.subst (liftSubst s))

def Formula.shift (p : Formula) : Formula := p.subst (fun i => .var (i + 1))
def Formula.instantiate (p : Formula) (t : Term) : Formula :=
  p.subst (fun | 0 => t | i + 1 => .var i)

/-- Each constructor is a rule, with no constructor accepting arbitrary Lean validity. -/
inductive Derives : Formula → Formula → Prop where
  | ident : Derives p p
  | cut : Derives p q → Derives q r → Derives p r
  | left : Derives (.conj p q) p
  | right : Derives (.conj p q) q
  | pair : Derives p q → Derives p r → Derives p (.conj q r)
  | refl : Derives p (.eq t t)
  | symm : Derives p (.eq a b) → Derives p (.eq b a)
  | trans : Derives p (.eq a b) → Derives p (.eq b c) → Derives p (.eq a c)
  | congr : Derives p (.eq a b) → Derives p (.eq (.app f a) (.app f b))
  | intro (p : Formula) (t : Term) : Derives (p.instantiate t) (.ex p)
  | elim : Derives p q.shift → Derives (.ex p) q

/-- Author-facing rule interface. This prototype does not include all regular rules. -/
structure Rules (D : Formula → Formula → Prop) : Prop where
  ident : ∀ {p}, D p p
  cut : ∀ {p q r}, D p q → D q r → D p r
  left : ∀ {p q}, D (.conj p q) p
  right : ∀ {p q}, D (.conj p q) q
  pair : ∀ {p q r}, D p q → D p r → D p (.conj q r)
  refl : ∀ {p t}, D p (.eq t t)
  trans : ∀ {p a b c}, D p (.eq a b) → D p (.eq b c) → D p (.eq a c)
  congr : ∀ {p a b f}, D p (.eq a b) → D p (.eq (.app f a) (.app f b))
  intro : ∀ p t, D (p.instantiate t) (.ex p)
  elim : ∀ {p q}, D p q.shift → D (.ex p) q

theorem derivationRules : Rules Derives where
  ident := .ident
  cut := .cut
  left := .left
  right := .right
  pair := .pair
  refl := .refl
  trans := .trans
  congr := .congr
  intro := .intro
  elim := .elim

-- Outside the binder: a = variable 0, c = variable 1.
-- Inside the binder: b = variable 0, a = variable 1, c = variable 2.
def graphBody : Formula :=
  .conj (.eq (.var 0) (.app 0 (.var 1)))
    (.eq (.var 2) (.app 1 (.var 0)))
def graphComposite : Formula := .ex graphBody
def graphResult : Formula := .eq (.var 1) (.app 1 (.app 0 (.var 0)))

-- Direct explicit frontend: the author constructs the restricted derivation.
theorem explicitForward : Derives graphComposite graphResult :=
  .elim (.trans .right (.congr .left))

theorem explicitBackward : Derives graphResult graphComposite :=
  .cut (.pair .refl .ident) (.intro graphBody (.app 0 (.var 0)))

-- Shallow frontend: the same operations are named lemmas behind an interface.
theorem shallowForward {D} (r : Rules D) : D graphComposite graphResult :=
  r.elim (r.trans r.right (r.congr r.left))

theorem shallowBackward {D} (r : Rules D) : D graphResult graphComposite :=
  r.cut (r.pair r.refl r.ident) (r.intro graphBody (.app 0 (.var 0)))

-- The shallow frontend can produce the explicit derivation for later interpretation.
theorem reusableForward : Derives graphComposite graphResult :=
  shallowForward derivationRules
theorem reusableBackward : Derives graphResult graphComposite :=
  shallowBackward derivationRules

variable {α : Type} (functions : Nat → α → α)

def Term.eval (env : Nat → α) : Term → α
  | .var i => env i
  | .app f t => functions f (t.eval env)

def extend (x : α) (env : Nat → α) : Nat → α
  | 0 => x
  | i + 1 => env i

def Formula.eval (env : Nat → α) : Formula → Prop
  | .eq a b => a.eval functions env = b.eval functions env
  | .conj p q => p.eval env ∧ q.eval env
  | .ex p => ∃ x, p.eval (extend x env)

theorem term_subst (s : Nat → Term) (env : Nat → α) (t : Term) :
    (t.subst s).eval functions env = t.eval functions (fun i => (s i).eval functions env) := by
  induction t with
  | var => rfl
  | app f t ih => simp only [Term.subst, Term.eval, ih]

theorem term_shift (x : α) (env : Nat → α) (t : Term) :
    t.shift.eval functions (extend x env) = t.eval functions env := by
  simp only [Term.shift, term_subst, Term.eval, extend]

theorem formula_subst (p : Formula) (s : Nat → Term) (env : Nat → α) :
    (p.subst s).eval functions env ↔
      p.eval functions (fun i => (s i).eval functions env) := by
  induction p generalizing s env with
  | eq a b => simp only [Formula.subst, Formula.eval, term_subst]
  | conj p q hp hq => simp only [Formula.subst, Formula.eval, hp, hq]
  | ex p ih =>
    simp only [Formula.subst, Formula.eval]
    apply exists_congr
    intro x
    rw [ih]
    have h : (fun i => (liftSubst s i).eval functions (extend x env)) =
        extend x (fun i => (s i).eval functions env) := by
      funext i
      cases i with
      | zero => rfl
      | succ i => exact term_shift functions x env (s i)
    rw [h]

theorem formula_shift (p : Formula) (x : α) (env : Nat → α) :
    p.shift.eval functions (extend x env) ↔ p.eval functions env := by
  simpa only [Formula.shift, Term.eval, extend] using
    formula_subst functions p (fun i => .var (i + 1)) (extend x env)

theorem formula_instantiate (p : Formula) (t : Term) (env : Nat → α) :
    (p.instantiate t).eval functions env ↔
      p.eval functions (extend (t.eval functions env) env) := by
  rw [Formula.instantiate, formula_subst]
  have h : (fun i => (match i with | 0 => t | i + 1 => Term.var i).eval functions env) =
      extend (t.eval functions env) env := by
    funext i
    cases i <;> rfl
  rw [h]

def Valid (p q : Formula) : Prop := ∀ env, p.eval functions env → q.eval functions env

theorem sound {p q} (d : Derives p q) : Valid functions p q := by
  induction d with
  | ident => exact fun _ h => h
  | cut _ _ hp hq => exact fun env h => hq env (hp env h)
  | left => exact fun _ h => h.1
  | right => exact fun _ h => h.2
  | pair _ _ hp hq => exact fun env h => ⟨hp env h, hq env h⟩
  | refl => exact fun _ _ => rfl
  | symm _ ih => exact fun env h => (ih env h).symm
  | trans _ _ hp hq => exact fun env h => (hp env h).trans (hq env h)
  | @congr p a b f _ ih => exact fun env h => congrArg (functions f) (ih env h)
  | intro p t =>
    exact fun env h => ⟨t.eval functions env, (formula_instantiate functions p t env).mp h⟩
  | elim d ih =>
    intro env ⟨x, hx⟩
    exact (formula_shift functions _ x env).mp (ih (extend x env) hx)

theorem setRules : Rules (Valid functions) where
  ident := sound functions .ident
  cut hp hq env h := hq env (hp env h)
  left := sound functions .left
  right := sound functions .right
  pair hp hq env h := ⟨hp env h, hq env h⟩
  refl := sound functions .refl
  trans hp hq env h := (hp env h).trans (hq env h)
  congr := by
    intro p a b f hp env h
    exact congrArg (functions f) (hp env h)
  intro p t := sound functions (.intro p t)
  elim hp env h := by
    obtain ⟨x, hx⟩ := h
    exact (formula_shift functions _ x env).mp (hp (extend x env) hx)

/-- Ordinary statement obtained by interpreting the reusable derivation. -/
theorem graph_in_set (f g : α → α) (a c : α) :
    (∃ b, b = f a ∧ c = g b) ↔ c = g (f a) := by
  let fs : Nat → α → α := fun | 0 => f | _ + 1 => g
  let env := extend a (fun _ => c)
  exact ⟨sound fs reusableForward env, sound fs reusableBackward env⟩

/-- The shallow proof can also target validity directly. -/
theorem shallow_in_set (f g : α → α) (a c : α) :
    (∃ b, b = f a ∧ c = g b) ↔ c = g (f a) := by
  let fs : Nat → α → α := fun | 0 => f | _ + 1 => g
  let env := extend a (fun _ => c)
  exact ⟨shallowForward (setRules fs) env, shallowBackward (setRules fs) env⟩

-- 3 -> 4 -> 8 distinguishes composition order (the reverse order yields 7).
example : ∃ b : Nat, b = 3 + 1 ∧ 8 = b * 2 :=
  (graph_in_set (fun x : Nat => x + 1) (fun x => x * 2) 3 8).mpr rfl

example : ¬ (∃ b : Nat, b = 3 + 1 ∧ 7 = b * 2) := by
  intro h
  have impossible := (graph_in_set (fun x : Nat => x + 1) (fun x => x * 2) 3 7).mp h
  contradiction

-- An arbitrary replacement may mention variable 0; binders must not capture it.
example (env : Nat → α) (t : Term) :
    ((Formula.ex (.eq (.var 1) (.var 0))).subst (fun _ => t)).eval functions env ↔
      ∃ x, t.eval functions env = x := by
  rw [formula_subst]
  rfl

-- Ordinary relational clients still use the existing interface in this file.
example {a b c : Relational.RelRep} (g : Relational.RelSquare b c)
    (f : Relational.RelSquare a b) {r : a.R} {s : a.S} (h : a.Rel r s) :
    c.Rel (g.impl (f.impl r)) (g.spec (f.spec s)) :=
  SquareKit.RelationalCategory.compose_preserves g f h

/-
Comparison and statement review:

* Both graph proofs use only the exposed rules. The explicit calculus has no
  escape accepting arbitrary Lean proofs. The shallow proof can target either
  Set validity or the explicit calculus; choosing the latter retains derivability.
* Soundness quantifies over every carrier, function-symbol interpretation and
  environment. It does not reflect Set validity into derivability. Existential
  elimination shifts its conclusion, preventing dependence on the bound witness.
* Substitution lifts under binders. The retained capture-avoidance example and
  the 3 -> 4 -> 8 / impossible 7 cases exercise the proved interpretation.
* The displayed graph equivalence is two derivations, not an implication rule.
  The reverse proof supplies f(a) as a witness; no choice principle is required.
* Direct constructors and shallow named rules have the same logical steps here.
  Neither hides de Bruijn variables or the explicit witness term. Notation and
  context management remain production work; this experiment measures no speedup.
* This is a single-sorted unary signature with a subset of regular rules. It
  proves neither a complete regular calculus nor a many-sorted square comparison.
  The public Set theorem permits only endofunctions. The implementation slice
  must cover A -> B -> C with distinct types and arbitrary decoding maps.
* Reusing the derivation in presheaves requires a contextual interpretation and
  its soundness theorem. Quantification over global sections will not suffice.
  No presheaf adapter, preservation map or Beck-Chevalley result is established.
* The mixed-style example checks namespace coexistence and unchanged ordinary
  caller obligations. It does not establish import/elaboration cost neutrality.

Recommendation: named rule lemmas over a small explicit derivation core for the
first slice, without a custom elaborator. Keep derivability, Set soundness and
the external square comparison separate. Use many-sorted contexts from the
start. Scope the first deliverable to the graph proof, its constructed Set
interpretation, and comparison with vertical square pasting. Keep arbitrary
relations/witness data and the presheaf interpretation as subsequent slices.

Run from the repository: direnv exec . lake env lean /tmp/conaled-36-frontends/Frontend.lean
This scratch file is not included in the repository source-coverage check.
-/

#print axioms sound
#print axioms graph_in_set
#print axioms shallow_in_set
#print axioms reusableForward
#print axioms reusableBackward
end FrontendComparison

-- Audit every kernel-safe declaration owned by this scratch module, including
-- generated auxiliaries and unnamed examples, using the repository whitelist.
run_cmd do
  let env ← Lean.getEnv
  let mut count : Nat := 0
  for (name, info) in env.constants do
    if (env.getModuleIdxFor? name).isNone && !info.isUnsafe then
      count := count + 1
      for axiomName in (← Lean.collectAxioms name) do
        unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
          throwError "Forbidden axiom {axiomName} in {name}"
  Lean.logInfo m!"Scratch audit passed: {count} kernel-safe declarations."
