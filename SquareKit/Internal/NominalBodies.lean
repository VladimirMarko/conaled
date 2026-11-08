import SquareKit.Internal.NominalTelescope

/-! Varying arithmetic bodies beneath the dependent telescope of #369.
The selected result is the residue modulo the dependent result bound. -/
namespace SquareKit.Internal.NominalBodies
open NominalTelescope

inductive Body where
  | first | second
  | free : Expr → Body
  | add : Body → Body → Body
  deriving DecidableEq

namespace Body

def bound : Body → Nat
  | .first | .second => 0
  | .free e => e.bound
  | .add x y => max x.bound y.bound

def eval (ρ : Nat → Nat) (a b : Nat) : Body → Nat
  | .first => a
  | .second => b
  | .free e => e.eval ρ
  | .add x y => x.eval ρ a b + y.eval ρ a b

def subst (σ : Nat → Expr) : Body → Body
  | .first => .first
  | .second => .second
  | .free e => .free (e.subst σ)
  | .add x y => .add (x.subst σ) (y.subst σ)

@[simp] theorem subst_id (t : Body) : t.subst .var = t := by
  induction t <;> simp_all [subst]
@[simp] theorem subst_comp (t : Body) (σ τ : Nat → Expr) :
    (t.subst σ).subst τ = t.subst (fun x => (σ x).subst τ) := by
  induction t <;> simp_all [subst]
@[simp] theorem eval_subst (t : Body) (σ : Nat → Expr) (ρ) (a b : Nat) :
    (t.subst σ).eval ρ a b = t.eval (fun x => (σ x).eval ρ) a b := by
  induction t <;> simp_all [subst, eval]

/-- Concretion spells the two bound projections with the chosen fresh atoms. -/
def concretize {k} (f : Frame k) : Body → Expr
  | .first => .var (f.name 0)
  | .second => .var (f.name 1)
  | .free e => e
  | .add x y => .add (x.concretize f) (y.concretize f)

theorem concretize_eval {k} (t : Body) (f : Frame k) (ht : t.bound ≤ k)
    (ρ) (a b r : Nat) :
    (t.concretize f).eval (f.env ρ a b r) = t.eval ρ a b := by
  induction t with
  | first => simp [concretize, eval, Expr.eval]
  | second => simp [concretize, eval, Expr.eval]
  | free e => exact f.eval_free e ht ρ a b r
  | add x y ihx ihy =>
    simp only [bound, max_le_iff] at ht
    simp [concretize, eval, Expr.eval, ihx ht.1, ihy ht.2]

theorem concretize_action {k} (t : Body) (f : Frame k) (ht : t.bound ≤ k)
    (p : FinitePerm) (hp : p.Fixes k) :
    t.concretize (Frame.act p hp f) =
      (t.concretize f).subst (fun a => .var (p.perm a)) := by
  induction t with
  | first => rfl
  | second => rfl
  | free e => exact (rename_free e p k hp ht).symm
  | add x y ihx ihy =>
    simp only [bound, max_le_iff] at ht
    simp [concretize, Expr.subst, ihx ht.1, ihy ht.2]
end Body

/-- Intrinsic result family, specified independently of names. -/
def contextual {N ρ} (Z : Expr) (t : Body) (a : First N ρ) (b : Second a) :
    Result Z a :=
  ⟨t.eval ρ a.val b.val % (Z.eval ρ + a.val + 1), Nat.mod_lt _ (by omega)⟩

def observe {N ρ} (Z : Expr) (t : Body) (a : First N ρ) (b : Second a) :
    Observation := ⟨Z.eval ρ + a.val, contextual Z t a b⟩

def support (N Z : Expr) (t : Body) := max (NominalTelescope.support N Z) t.bound

structure Representative (N Z : Expr) where
  body : Body
  frame : Frame (support N Z body)

namespace Representative
/-- Named type annotations use the same frame as every body occurrence. -/
def annotations {N Z} (x : Representative N Z) : NominalTelescope.Annotations where
  first := N
  second := .var (x.frame.name 0)
  third := .var (x.frame.name 1)
  result := .add Z (.var (x.frame.name 0))
  body := x.body.concretize x.frame
  tail := .var (x.frame.name 2)

theorem annotations_eval {N Z} (x : Representative N Z) (ρ) (a b r : Nat) :
    let η := x.frame.env ρ a b r
    (annotations x).first.eval η = N.eval ρ ∧
    (annotations x).second.eval η = a ∧
    (annotations x).third.eval η = b ∧
    (annotations x).result.eval η = Z.eval ρ + a ∧
    (annotations x).body.eval η = x.body.eval ρ a b ∧
    (annotations x).tail.eval η = r := by
  have hN : N.bound ≤ support N Z x.body :=
    (Nat.le_max_left _ _).trans (Nat.le_max_left _ _)
  have hZ : Z.bound ≤ support N Z x.body :=
    (Nat.le_max_right _ _).trans (Nat.le_max_left _ _)
  simp [annotations, Expr.eval, x.frame.eval_free N hN ρ a b r,
    x.frame.eval_free Z hZ ρ a b r,
    Body.concretize_eval x.body x.frame (Nat.le_max_right _ _) ρ a b r]

/-- A simultaneous admissible renaming preserves the body constructors and moves
all its bound occurrences. This relation does not mention interpretation. -/
def Alpha {N Z} (x y : Representative N Z) : Prop :=
  ∃ h : x.body = y.body, Frame.Alpha (h ▸ x.frame) y.frame

theorem alpha_iff {N Z} (x y : Representative N Z) : Alpha x y ↔ x.body = y.body :=
  ⟨fun ⟨h, _⟩ => h, fun h => ⟨h, Frame.alpha _ _⟩⟩

instance setoid (N Z) : Setoid (Representative N Z) where
  r := Alpha
  iseqv := ⟨fun x => (alpha_iff x x).mpr rfl,
    fun h => (alpha_iff _ _).mpr ((alpha_iff _ _).mp h).symm,
    fun h k => (alpha_iff _ _).mpr (((alpha_iff _ _).mp h).trans ((alpha_iff _ _).mp k))⟩

def nominal {N Z ρ} (x : Representative N Z) (a : First N ρ) (b : Second a) :
    Observation :=
  let η := x.frame.env ρ a.val b.val 0
  let n := (annotations x).result.eval η
  let v := (annotations x).body.eval η
  ⟨n, ⟨v % (n + 1), Nat.mod_lt _ (by omega)⟩⟩

theorem comparison {N Z ρ} (x : Representative N Z) (a : First N ρ) (b : Second a) :
    x.nominal a b = observe Z x.body a b := by
  have h := annotations_eval x ρ a.val b.val 0
  simp only [nominal, h.2.2.2.1, h.2.2.2.2.1, observe, contextual]

theorem invariant {N Z ρ} (x y : Representative N Z) (h : Alpha x y)
    (a : First N ρ) (b : Second a) : x.nominal a b = y.nominal a b := by
  rw [comparison, comparison, (alpha_iff _ _).mp h]
end Representative

abbrev Abstraction (N Z : Expr) := Quotient (Representative.setoid N Z)

def abstractBody (N Z : Expr) (t : Body) : Abstraction N Z :=
  ⟦⟨t, Frame.canonical _⟩⟧

def body {N Z} (q : Abstraction N Z) : Body :=
  Quotient.lift Representative.body (fun x y h => (Representative.alpha_iff x y).mp h) q

@[simp] theorem body_abstract (N Z) (t : Body) : body (abstractBody N Z t) = t := rfl

theorem abstract_body {N Z} (q : Abstraction N Z) : abstractBody N Z (body q) = q := by
  induction q using Quotient.inductionOn with
  | h x => exact Quotient.sound ((Representative.alpha_iff _ _).mpr rfl)

def observeAbstract {N Z ρ} (q : Abstraction N Z) (a : First N ρ) (b : Second a) :
    Observation := Quotient.lift (fun x => x.nominal a b)
      (fun x y h => Representative.invariant x y h a b) q

theorem observeAbstract_eq {N Z ρ} (q : Abstraction N Z) (a : First N ρ) (b : Second a) :
    observeAbstract q a b = observe Z (body q) a b := by
  induction q using Quotient.inductionOn with
  | h x => exact x.comparison a b

/-- Capture avoidance constructs fresh names above the support of every
substituted free leaf, including leaves occurring only in the varying body. -/
def substitute {N Z} (σ : Nat → Expr) (q : Abstraction N Z) :
    Abstraction (N.subst σ) (Z.subst σ) :=
  abstractBody _ _ ((body q).subst σ)

abbrev Program := Σ N : Expr, Σ Z : Expr, Abstraction N Z

def substituteProgram (σ : Nat → Expr) (p : Program) : Program :=
  ⟨p.1.subst σ, p.2.1.subst σ, substitute σ p.2.2⟩

/-- The contextual presentation retains arbitrary generated bodies, not just
free bounds. Both translations preserve the entire syntax modulo bound names. -/
abbrev ContextualProgram := Expr × Expr × Body

def toContextual (p : Program) : ContextualProgram := (p.1, p.2.1, body p.2.2)
def fromContextual (p : ContextualProgram) : Program :=
  ⟨p.1, p.2.1, abstractBody _ _ p.2.2⟩

@[simp] theorem contextual_roundtrip (p : ContextualProgram) :
    toContextual (fromContextual p) = p := rfl
@[simp] theorem nominal_roundtrip (p : Program) : fromContextual (toContextual p) = p := by
  rcases p with ⟨N,Z,q⟩
  simp [toContextual, fromContextual, abstract_body]

theorem program_ext (p q : Program) (h : toContextual p = toContextual q) : p = q := by
  rw [← nominal_roundtrip p, ← nominal_roundtrip q, h]

theorem substitute_id (p : Program) : substituteProgram .var p = p := by
  apply program_ext
  simp [toContextual, substituteProgram, substitute]

theorem substitute_comp (p : Program) (σ τ : Nat → Expr) :
    substituteProgram τ (substituteProgram σ p) =
      substituteProgram (fun x => (σ x).subst τ) p := by
  apply program_ext
  simp [toContextual, substituteProgram, substitute]

theorem observe_substitute {N Z} (t : Body) (σ : Nat → Expr) (ρ)
    (a : First (N.subst σ) ρ) (b : Second a) :
    observe (Z.subst σ) (t.subst σ) a b =
      observe Z t (liftFirst N σ ρ a) (liftSecond b) := by
  apply Sigma.ext (by simp [observe, liftFirst])
  apply (Fin.heq_ext_iff (by simp [observe, liftFirst])).mpr
  simp [observe, contextual, liftFirst, liftSecond]

theorem substitute_preserves {N Z} (q : Abstraction N Z) (σ : Nat → Expr) (ρ)
    (a : First (N.subst σ) ρ) (b : Second a) :
    observeAbstract (substitute σ q) a b =
      observeAbstract q (liftFirst N σ ρ a) (liftSecond b) := by
  rw [observeAbstract_eq, observeAbstract_eq]
  exact observe_substitute (body q) σ ρ a b

theorem two_substitutions {N Z} (q : Abstraction N Z) (σ τ : Nat → Expr) (ρ)
    (a : First ((N.subst σ).subst τ) ρ) (b : Second a) :
    observeAbstract (substitute τ (substitute σ q)) a b =
      observeAbstract q
        (liftFirst N σ (fun x => (τ x).eval ρ) (liftFirst (N.subst σ) τ ρ a))
        (liftSecond (σ := σ) (liftSecond (σ := τ) b)) :=
  (substitute_preserves _ τ ρ a b).trans (substitute_preserves _ σ _ _ _)

theorem second_specialization {N Z ρ} (a : First N ρ) (b : Second a) :
    observeAbstract (abstractBody N Z .second) a b = NominalTelescope.observe Z a b := by
  rw [observeAbstract_eq]
  apply Sigma.ext (show Z.eval ρ + a.val = Z.eval ρ + a.val from rfl)
  apply (Fin.heq_ext_iff rfl).mpr
  change b.val % (Z.eval ρ + a.val + 1) = b.val
  exact Nat.mod_eq_of_lt (by have := b.isLt; omega)

/-- Raw substitution under the telescope sends bound occurrences to fresh
bound names, and free occurrences to the supplied expressions. -/
def under {k l} (f : Frame k) (g : Frame l) (σ : Nat → Expr) (x : Nat) : Expr :=
  if x = f.name 0 then .var (g.name 0)
  else if x = f.name 1 then .var (g.name 1) else σ x

theorem free_under {k l} (e : Expr) (he : e.bound ≤ k)
    (f : Frame k) (g : Frame l) (σ : Nat → Expr) :
    e.subst (under f g σ) = e.subst σ := by
  induction e with
  | var x =>
    have h0 := f.fresh 0
    have h1 := f.fresh 1
    have hx : x < k := by simp [Expr.bound] at he; omega
    simp [Expr.subst, under, show x ≠ f.name 0 by omega, show x ≠ f.name 1 by omega]
  | lit n => rfl
  | add x y ihx ihy =>
    simp only [Expr.bound, max_le_iff] at he
    simp [Expr.subst, ihx he.1, ihy he.2]

theorem concretize_subst {k l} (t : Body) (ht : t.bound ≤ k)
    (f : Frame k) (g : Frame l) (σ : Nat → Expr) :
    (t.subst σ).concretize g = (t.concretize f).subst (under f g σ) := by
  induction t with
  | first => simp [Body.subst, Body.concretize, Expr.subst, under]
  | second => simp [Body.subst, Body.concretize, Expr.subst, under, f.name_injective.eq_iff]
  | free e => exact (free_under e ht f g σ).symm
  | add x y ihx ihy =>
    simp only [Body.bound, max_le_iff] at ht
    simp [Body.subst, Body.concretize, Expr.subst, ihx ht.1, ihy ht.2]

/-- A chosen fresh spelling reopens an abstraction without changing its body. -/
def reopen {N Z} (q : Abstraction N Z) (f : Frame (support N Z (body q))) :
    Representative N Z := ⟨body q, f⟩

theorem reopen_abstract {N Z} (q : Abstraction N Z) (f : Frame (support N Z (body q))) :
    (⟦reopen q f⟧ : Abstraction N Z) = q := by
  calc
    (⟦reopen q f⟧ : Abstraction N Z) = abstractBody N Z (body q) :=
      Quotient.sound ((Representative.alpha_iff _ _).mpr rfl)
    _ = q := abstract_body q

/-- The original dependent tail is a specialization, retaining its selected
third component over the selected second component. -/
def selectedTail {N Z : Expr} {ρ : Nat → Nat} (a : First N ρ) (b : Second a) (r : Third b) : TailObservation :=
  NominalTelescope.observeTail Z a b r

theorem selectedTail_retains {N Z ρ} (a : First N ρ) (b : Second a) (r : Third b) :
    (⟨(selectedTail (Z := Z) a b r).1, (selectedTail (Z := Z) a b r).2.1⟩ : Observation) =
      observeAbstract (abstractBody N Z .second) a b :=
  (second_specialization a b).symm

/-- No observation of abstractions can expose the chosen first bound spelling,
even after fixing a varying body. -/
theorem no_bound_name_observer (N Z : Expr) (t : Body) :
    ¬ ∃ get : Abstraction N Z → Nat,
      ∀ f : Frame (support N Z t), get ⟦⟨t,f⟩⟧ = f.name 0 := by
  rintro ⟨get,h⟩
  let k := support N Z t
  let f := Frame.canonical k
  let p := FinitePerm.swap k (k+3)
  have hp : p.Fixes k := by
    intro x hx
    apply Equiv.swap_apply_of_ne_of_ne <;> omega
  let g := Frame.act p hp f
  have he : (⟦⟨t,f⟩⟧ : Abstraction N Z) = ⟦⟨t,g⟩⟧ :=
    Quotient.sound ((Representative.alpha_iff _ _).mpr rfl)
  have hn := congrArg get he
  rw [h f, h g] at hn
  have hf : f.name 0 = k := rfl
  have hg : g.name 0 = k+3 := by
    simp [g,p,f,Frame.name,Frame.act,Frame.canonical,FinitePerm.comp,FinitePerm.id,FinitePerm.swap]
  omega

end SquareKit.Internal.NominalBodies
