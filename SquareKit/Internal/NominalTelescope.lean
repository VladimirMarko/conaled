import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic

/-! Experimental nominal presentation of the bounded dependent telescope from #365.
The expression language has natural variables, literals and addition. The binder
schema selects its second argument, and its extension selects a third argument
in a family over that selected value. Alpha equivalence is a finite-permutation
orbit, specified before either interpretation. This is not a general nominal
lambda calculus. -/
namespace SquareKit.Internal.NominalTelescope

inductive Expr where
  | var : Nat → Expr
  | lit : Nat → Expr
  | add : Expr → Expr → Expr
  deriving DecidableEq

namespace Expr

def eval (ρ : Nat → Nat) : Expr → Nat
  | .var a => ρ a
  | .lit n => n
  | .add x y => eval ρ x + eval ρ y

def subst (σ : Nat → Expr) : Expr → Expr
  | .var a => σ a
  | .lit n => .lit n
  | .add x y => .add (subst σ x) (subst σ y)

/-- A finite initial segment containing every free atom. -/
def bound : Expr → Nat
  | .var a => a + 1
  | .lit _ => 0
  | .add x y => max x.bound y.bound

@[simp] theorem subst_id (e : Expr) : e.subst .var = e := by
  induction e <;> simp_all [subst]

@[simp] theorem subst_comp (e : Expr) (σ τ : Nat → Expr) :
    (e.subst σ).subst τ = e.subst (fun a => (σ a).subst τ) := by
  induction e <;> simp_all [subst]

@[simp] theorem eval_subst (e : Expr) (σ : Nat → Expr) (ρ : Nat → Nat) :
    (e.subst σ).eval ρ = e.eval (fun a => (σ a).eval ρ) := by
  induction e <;> simp_all [subst, eval]

theorem eval_congr (e : Expr) (ρ η : Nat → Nat)
    (h : ∀ a, a < e.bound → ρ a = η a) : e.eval ρ = e.eval η := by
  induction e with
  | var a => exact h a (Nat.lt_succ_self a)
  | lit n => rfl
  | add x y ihx ihy =>
    exact congrArg₂ (· + ·) (ihx fun a ha => h a (lt_of_lt_of_le ha (Nat.le_max_left _ _)))
      (ihy fun a ha => h a (lt_of_lt_of_le ha (Nat.le_max_right _ _)))
end Expr

/-- Actual permutations of an infinite atom set with a proved finite support
bound. Neither freshness nor capture avoidance is an axiom. -/
structure FinitePerm where
  perm : Equiv.Perm Nat
  finite : ∃ k, ∀ a, k ≤ a → perm a = a

namespace FinitePerm

def id : FinitePerm := ⟨Equiv.refl _, 0, by simp⟩

def comp (p q : FinitePerm) : FinitePerm :=
  ⟨q.perm.trans p.perm, by
    obtain ⟨k, hk⟩ := p.finite
    obtain ⟨l, hl⟩ := q.finite
    exact ⟨max k l, fun a ha => by
      simp only [Equiv.trans_apply, hl a (le_trans (Nat.le_max_right _ _) ha)]
      exact hk a (le_trans (Nat.le_max_left _ _) ha)⟩⟩

def inv (p : FinitePerm) : FinitePerm :=
  ⟨p.perm.symm, by
    obtain ⟨k, hk⟩ := p.finite
    refine ⟨k, fun a ha => ?_⟩
    apply p.perm.injective
    simp [hk a ha]⟩

def swap (a b : Nat) : FinitePerm :=
  ⟨Equiv.swap a b, max a b + 1, by
    intro x hx
    apply Equiv.swap_apply_of_ne_of_ne <;> omega⟩

/-- Fixing an explicit finite support is the freshness side condition. -/
def Fixes (p : FinitePerm) (k : Nat) : Prop := ∀ a, a < k → p.perm a = a

theorem fixes_comp {p q : FinitePerm} {k} (hp : p.Fixes k) (hq : q.Fixes k) :
    (p.comp q).Fixes k := by
  intro a ha
  simp [comp, hq a ha, hp a ha]

theorem fixes_inv {p : FinitePerm} {k} (hp : p.Fixes k) : p.inv.Fixes k := by
  intro a ha
  apply p.perm.injective
  simp [inv, hp a ha]
end FinitePerm

/-- A representative is a finite permutation of a canonical fresh telescope.
The support may overapproximate free atoms; this restricts representatives but
never prevents constructing one. The permutation acts on every annotation. -/
structure Frame (k : Nat) where
  permutation : FinitePerm
  fixes : permutation.Fixes k

namespace Frame

def canonical (k : Nat) : Frame k := ⟨FinitePerm.id, by simp [FinitePerm.Fixes, FinitePerm.id]⟩

def name {k} (f : Frame k) (i : Nat) : Nat := f.permutation.perm (k + i)

theorem name_injective {k} (f : Frame k) : Function.Injective f.name := by
  intro i j h
  have := f.permutation.perm.injective h
  omega

theorem fresh {k} (f : Frame k) (i : Nat) : k ≤ f.name i := by
  by_contra h
  have hf := f.fixes (f.name i) (by omega)
  have hi : f.name i = k + i := by
    apply f.permutation.perm.injective
    exact hf
  omega

def act {k} (p : FinitePerm) (hp : p.Fixes k) (f : Frame k) : Frame k :=
  ⟨p.comp f.permutation, FinitePerm.fixes_comp hp f.fixes⟩

/-- Orbit equality, independent of any contextual interpretation or erasure. -/
def Alpha {k} (f g : Frame k) : Prop :=
  ∃ p : FinitePerm, ∃ hp : p.Fixes k,
    ∀ a, (act p hp f).permutation.perm a = g.permutation.perm a

/-- All choices of bound spelling for this fixed schema lie in one orbit.
The witness is the finite permutation g f⁻¹, which fixes the free support. -/
theorem alpha {k} (f g : Frame k) : Alpha f g := by
  refine ⟨g.permutation.comp f.permutation.inv,
    FinitePerm.fixes_comp g.fixes (FinitePerm.fixes_inv f.fixes), ?_⟩
  intro a
  simp [act, FinitePerm.comp, FinitePerm.inv]

instance setoid (k : Nat) : Setoid (Frame k) where
  r := Alpha
  iseqv := ⟨fun f => alpha f f, fun _ => alpha _ _, fun _ _ => alpha _ _⟩

/-- Environments extend by the three actual bound atoms. -/
def env {k} (f : Frame k) (ρ : Nat → Nat) (a b r : Nat) : Nat → Nat :=
  fun x => if x = f.name 0 then a else if x = f.name 1 then b
    else if x = f.name 2 then r else ρ x

@[simp] theorem env_zero {k} (f : Frame k) (ρ) (a b r) :
    f.env ρ a b r (f.name 0) = a := by simp [env]
@[simp] theorem env_one {k} (f : Frame k) (ρ) (a b r) :
    f.env ρ a b r (f.name 1) = b := by
  simp [env, f.name_injective.eq_iff]
@[simp] theorem env_two {k} (f : Frame k) (ρ) (a b r) :
    f.env ρ a b r (f.name 2) = r := by
  simp [env, f.name_injective.eq_iff]

theorem eval_free {k} (f : Frame k) (e : Expr) (he : e.bound ≤ k) (ρ) (a b r) :
    e.eval (f.env ρ a b r) = e.eval ρ := by
  apply Expr.eval_congr
  intro x hx
  have h0 := f.fresh 0
  have h1 := f.fresh 1
  have h2 := f.fresh 2
  simp only [env]
  split_ifs <;> omega
end Frame

/-- The type annotations and selected body, in actual atom syntax. The first
three fields are Fin bounds minus one; result is also a Fin bound minus one. -/
structure Annotations where
  first : Expr
  second : Expr
  third : Expr
  result : Expr
  body : Expr
  tail : Expr
  deriving DecidableEq

def support (N Z : Expr) : Nat := max N.bound Z.bound

def annotations (N Z : Expr) (f : Frame (support N Z)) : Annotations where
  first := N
  second := .var (f.name 0)
  third := .var (f.name 1)
  result := .add Z (.var (f.name 0))
  body := .var (f.name 1)
  tail := .var (f.name 2)

/-- Contextual families, independently specified by their finite domains. -/
abbrev First (N : Expr) (ρ : Nat → Nat) := Fin (N.eval ρ + 1)
abbrev Second {N ρ} (a : First N ρ) := Fin (a.val + 1)
abbrev Third {N ρ} {a : First N ρ} (b : Second a) := Fin (b.val + 1)
abbrev Result {N ρ} (Z : Expr) (a : First N ρ) := Fin (Z.eval ρ + a.val + 1)
abbrev Observation := Σ k : Nat, Fin (k + 1)
abbrev TailObservation := Σ k : Nat, Σ b : Fin (k + 1), Fin (b.val + 1)

theorem tailObservation_ext (x y : TailObservation)
    (hk : x.1 = y.1) (hb : x.2.1.val = y.2.1.val)
    (hr : x.2.2.val = y.2.2.val) : x = y := by
  rcases x with ⟨k, b, r⟩
  rcases y with ⟨l, c, s⟩
  dsimp at hk hb hr
  subst l
  have hb' : b = c := Fin.ext hb
  subst c
  have hr' : r = s := Fin.ext hr
  subst s
  rfl

def contextual {N ρ} (Z : Expr) (a : First N ρ) (b : Second a) : Result Z a :=
  ⟨b.val, by have := b.isLt; omega⟩

def observe {N ρ} (Z : Expr) (a : First N ρ) (b : Second a) : Observation :=
  ⟨Z.eval ρ + a.val, contextual Z a b⟩

def observeTail {N ρ} (Z : Expr) (a : First N ρ) (b : Second a) (r : Third b) :
    TailObservation := ⟨Z.eval ρ + a.val, contextual Z a b, r⟩

/-- The named annotation really evaluates to the contextual dependent index.
In particular permutation the first atom also renames the second binder's type. -/
theorem annotations_eval (N Z : Expr) (f : Frame (support N Z)) (ρ) (a b r : Nat) :
    let t := annotations N Z f
    let η := f.env ρ a b r
    t.first.eval η = N.eval ρ ∧ t.second.eval η = a ∧ t.third.eval η = b ∧
    t.result.eval η = Z.eval ρ + a ∧ t.body.eval η = b ∧ t.tail.eval η = r := by
  simp only [annotations, Expr.eval, Frame.env_zero, Frame.env_one, Frame.env_two]
  exact ⟨f.eval_free N (Nat.le_max_left _ _) ρ a b r, trivial, trivial,
    congrArg (· + a) (f.eval_free Z (Nat.le_max_right _ _) ρ a b r), trivial, trivial⟩

/-- Well-typedness is derived from the finite inputs, not assumed as a
substitution or capture-avoidance law. -/
def nominal {N Z ρ} (f : Frame (support N Z)) (a : First N ρ) (b : Second a) :
    Fin ((annotations N Z f).result.eval (f.env ρ a.val b.val 0) + 1) :=
  ⟨(annotations N Z f).body.eval (f.env ρ a.val b.val 0), by
    have h := annotations_eval N Z f ρ a.val b.val 0
    rw [h.2.2.2.1, h.2.2.2.2.1]
    have := b.isLt
    omega⟩

def nominalObserve {N Z ρ} (f : Frame (support N Z)) (a : First N ρ)
    (b : Second a) : Observation :=
  ⟨(annotations N Z f).result.eval (f.env ρ a.val b.val 0), nominal f a b⟩

theorem comparison {N Z ρ} (f : Frame (support N Z)) (a : First N ρ) (b : Second a) :
    nominalObserve f a b = observe Z a b := by
  have h := annotations_eval N Z f ρ a.val b.val 0
  apply Sigma.ext h.2.2.2.1
  exact (Fin.heq_ext_iff (congrArg (· + 1) h.2.2.2.1)).mpr h.2.2.2.2.1

/-- Alpha invariance follows from named evaluation and typing. -/
theorem alpha_invariant {N Z ρ} (f g : Frame (support N Z)) (_h : Frame.Alpha f g)
    (a : First N ρ) (b : Second a) : nominalObserve f a b = nominalObserve g a b := by
  simp only [comparison]

abbrev Abstraction (N Z : Expr) := Quotient (Frame.setoid (support N Z))

def abstractObserve {N Z ρ} (q : Abstraction N Z) (a : First N ρ) (b : Second a) :
    Observation := Quotient.lift (fun f => nominalObserve f a b)
      (fun f g h => alpha_invariant f g h a b) q

/-- Programs retain their free expressions; only bound spelling is quotiented. -/
abbrev Program := Σ N : Expr, Σ Z : Expr, Abstraction N Z

def program (N Z : Expr) : Program := ⟨N, Z, ⟦Frame.canonical (support N Z)⟧⟩

theorem program_ext (p q : Program) (hN : p.1 = q.1) (hZ : p.2.1 = q.2.1) : p = q := by
  rcases p with ⟨N, Z, p⟩
  rcases q with ⟨N', Z', q⟩
  dsimp at hN hZ
  subst N'; subst Z'
  congr 1
  congr 1
  induction p using Quotient.inductionOn with | h f =>
    induction q using Quotient.inductionOn with | h g =>
      exact Quotient.sound (Frame.alpha f g)

/-- The contextual presentation records the two free index expressions. Its
binders and body are the intrinsic families First, Second and contextual above. -/
abbrev ContextualProgram := Expr × Expr

def toContextual (p : Program) : ContextualProgram := (p.1, p.2.1)
def fromContextual (p : ContextualProgram) : Program := program p.1 p.2

@[simp] theorem contextual_roundtrip (p : ContextualProgram) :
    toContextual (fromContextual p) = p := rfl

@[simp] theorem nominal_roundtrip (p : Program) :
    fromContextual (toContextual p) = p := program_ext _ _ rfl rfl

/-- This comparison reflects syntactic equality of N,Z. It does not claim that
equal numerical functions imply equal free-expression syntax. -/
theorem comparison_reflects (p q : Program) : toContextual p = toContextual q ↔ p = q := by
  constructor
  · intro h
    exact program_ext p q (congrArg Prod.fst h) (congrArg Prod.snd h)
  · rintro rfl; rfl

/-- Fresh representatives are constructed after substituting the free expressions.
The canonical names are above every free atom in the substitution images used
by N and Z; the selected body and all dependent annotations are reconstructed. -/
def substitute (σ : Nat → Expr) (p : Program) : Program :=
  program (p.1.subst σ) (p.2.1.subst σ)

theorem substitute_id (p : Program) : substitute .var p = p := by
  apply program_ext <;> simp [substitute, program]

theorem substitute_comp (σ τ : Nat → Expr) (p : Program) :
    substitute τ (substitute σ p) = substitute (fun a => (σ a).subst τ) p := by
  apply program_ext <;> simp [substitute, program]

/-- Typed lifting beneath both dependent binders. -/
def liftFirst (N : Expr) (σ : Nat → Expr) (ρ : Nat → Nat)
    (a : First (N.subst σ) ρ) : First N (fun x => (σ x).eval ρ) :=
  ⟨a.val, by simpa [First] using a.isLt⟩

def liftSecond {N σ ρ} {a : First (N.subst σ) ρ} (b : Second a) :
    Second (liftFirst N σ ρ a) := b

def liftThird {N : Expr} {σ : Nat → Expr} {ρ : Nat → Nat} {a : First (N.subst σ) ρ} {b : Second a} (r : Third b) :
    Third (liftSecond (σ := σ) b) := r

theorem observe_substitute (N Z : Expr) (σ : Nat → Expr) (ρ : Nat → Nat)
    (a : First (N.subst σ) ρ) (b : Second a) :
    observe (Z.subst σ) a b = observe Z (liftFirst N σ ρ a) (liftSecond b) := by
  apply Sigma.ext (by simp [observe, liftFirst])
  apply (Fin.heq_ext_iff (by simp [observe, liftFirst])).mpr
  rfl

theorem tail_substitute (N Z : Expr) (σ : Nat → Expr) (ρ : Nat → Nat)
    (a : First (N.subst σ) ρ) (b : Second a) (r : Third b) :
    observeTail (Z.subst σ) a b r =
      observeTail Z (liftFirst N σ ρ a) (liftSecond b) (liftThird r) := by
  apply tailObservation_ext
  · simp [observeTail, liftFirst]
  · rfl
  · rfl

/-- The maintenance extension checks the named third field in the family over
its selected second field, including the dependent result annotation. -/
def nominalTail {N Z ρ} (f : Frame (support N Z)) (a : First N ρ)
    (b : Second a) (r : Third b) : TailObservation :=
  let η := f.env ρ a.val b.val r.val
  let t := annotations N Z f
  ⟨t.result.eval η, ⟨t.body.eval η, by
    have h := annotations_eval N Z f ρ a.val b.val r.val
    rw [h.2.2.2.1, h.2.2.2.2.1]; have := b.isLt; omega⟩,
    ⟨t.tail.eval η, by
      have h := annotations_eval N Z f ρ a.val b.val r.val
      change t.tail.eval η < t.body.eval η + 1
      simpa [t, η, annotations, Expr.eval] using r.isLt⟩⟩

theorem tail_comparison {N Z ρ} (f : Frame (support N Z)) (a : First N ρ)
    (b : Second a) (r : Third b) : nominalTail f a b r = observeTail Z a b r := by
  have h := annotations_eval N Z f ρ a.val b.val r.val
  apply tailObservation_ext
  · exact h.2.2.2.1
  · exact h.2.2.2.2.1
  · exact h.2.2.2.2.2

/-- Replacing the free environment under a finite renaming fixes every
expression supported there. This is the representation-specific freshness law. -/
theorem rename_free (e : Expr) (p : FinitePerm) (k : Nat)
    (hp : p.Fixes k) (he : e.bound ≤ k) :
    e.subst (fun a => .var (p.perm a)) = e := by
  induction e with
  | var a => simp only [Expr.subst]; rw [hp a (by simp [Expr.bound] at he; omega)]
  | lit n => rfl
  | add x y ihx ihy =>
    simp only [Expr.bound, max_le_iff] at he
    simp [Expr.subst, ihx he.1, ihy he.2]

def Annotations.rename (p : FinitePerm) (t : Annotations) : Annotations :=
  let σ := fun a => Expr.var (p.perm a)
  ⟨t.first.subst σ, t.second.subst σ, t.third.subst σ,
    t.result.subst σ, t.body.subst σ, t.tail.subst σ⟩

/-- The finite action moves the annotated telescope, including the occurrence
of the outer binder in the second annotation and the selected body in the third. -/
theorem annotations_action (N Z : Expr) (f : Frame (support N Z))
    (p : FinitePerm) (hp : p.Fixes (support N Z)) :
    annotations N Z (Frame.act p hp f) = (annotations N Z f).rename p := by
  have hn := rename_free N p _ hp (Nat.le_max_left _ _)
  have hz := rename_free Z p _ hp (Nat.le_max_right _ _)
  simp [Annotations.rename, annotations, Frame.name, Frame.act, FinitePerm.comp,
    Expr.subst, hn, hz]

/-- There can be no observer of alpha classes returning the first bound atom. -/
theorem no_bound_name_observer (N Z : Expr) :
    ¬ ∃ get : Abstraction N Z → Nat, ∀ f, get ⟦f⟧ = f.name 0 := by
  rintro ⟨get, hget⟩
  let k := support N Z
  let f := Frame.canonical k
  let p := FinitePerm.swap k (k + 3)
  have hp : p.Fixes k := by
    intro a ha
    apply Equiv.swap_apply_of_ne_of_ne <;> omega
  let g := Frame.act p hp f
  have he : (⟦f⟧ : Abstraction N Z) = ⟦g⟧ := Quotient.sound (Frame.alpha f g)
  have hn := congrArg get he
  rw [hget f, hget g] at hn
  have hf : f.name 0 = k := rfl
  have hg : g.name 0 = k + 3 := by
    simp [g, p, f, Frame.name, Frame.act, Frame.canonical, FinitePerm.comp,
      FinitePerm.id, FinitePerm.swap]
  omega

/-- The quotient interpretation agrees with the contextual dependent function. -/
theorem abstractObserve_comparison {N Z ρ} (q : Abstraction N Z)
    (a : First N ρ) (b : Second a) : abstractObserve q a b = observe Z a b := by
  induction q using Quotient.inductionOn with
  | h f => exact comparison f a b

/-- Substitution on alpha classes is well typed beneath both binders and
preserves the chosen second argument, not just inhabitedness of the result. -/
theorem substitute_preserves (p : Program) (σ : Nat → Expr) (ρ : Nat → Nat)
    (a : First (p.1.subst σ) ρ) (b : Second a) :
    abstractObserve (substitute σ p).2.2 a b =
      abstractObserve p.2.2 (liftFirst p.1 σ ρ a) (liftSecond b) := by
  exact (abstractObserve_comparison (N := p.1.subst σ) (Z := p.2.1.subst σ)
    (substitute σ p).2.2 a b).trans
    ((observe_substitute p.1 p.2.1 σ ρ a b).trans
      (abstractObserve_comparison p.2.2 _ _).symm)

/-- The two successive dependent lifts and their named interpretation. -/
theorem two_substitutions (N Z : Expr) (σ τ : Nat → Expr) (ρ : Nat → Nat)
    (f : Frame (support ((N.subst σ).subst τ) ((Z.subst σ).subst τ)))
    (a : First ((N.subst σ).subst τ) ρ) (b : Second a) :
    nominalObserve f a b =
      observe Z (liftFirst N σ (fun x => (τ x).eval ρ) (liftFirst (N.subst σ) τ ρ a))
        (liftSecond (σ := σ) (liftSecond (σ := τ) b)) := by
  rw [comparison]
  exact (observe_substitute (N.subst σ) (Z.subst σ) τ ρ a b).trans
    (observe_substitute N Z σ (fun x => (τ x).eval ρ) _ _)

/-- The same base changes retain the third field in its dependent fiber. -/
theorem tail_two_substitutions (N Z : Expr) (σ τ : Nat → Expr) (ρ : Nat → Nat)
    (f : Frame (support ((N.subst σ).subst τ) ((Z.subst σ).subst τ)))
    (a : First ((N.subst σ).subst τ) ρ) (b : Second a) (r : Third b) :
    nominalTail f a b r =
      observeTail Z (liftFirst N σ (fun x => (τ x).eval ρ) (liftFirst (N.subst σ) τ ρ a))
        (liftSecond (σ := σ) (liftSecond (σ := τ) b))
        (liftThird (σ := σ) (liftThird (σ := τ) r)) := by
  rw [tail_comparison]
  exact (tail_substitute (N.subst σ) (Z.subst σ) τ ρ a b r).trans
    (tail_substitute N Z σ (fun x => (τ x).eval ρ) _ _ _)

/-- Third-field alpha invariance reuses evaluation, but the typing of its new
annotation is checked in nominalTail rather than inferred from quotienting. -/
theorem tail_alpha_invariant {N Z ρ} (f g : Frame (support N Z))
    (_h : Frame.Alpha f g) (a : First N ρ) (b : Second a) (r : Third b) :
    nominalTail f a b r = nominalTail g a b r := by
  simp only [tail_comparison]

/-- The stronger maintenance observation descends to the same alpha classes. -/
def abstractTail {N Z ρ} (q : Abstraction N Z) (a : First N ρ) (b : Second a)
    (r : Third b) : TailObservation :=
  Quotient.lift (fun f => nominalTail f a b r)
    (fun f g h => tail_alpha_invariant f g h a b r) q

theorem abstractTail_comparison {N Z ρ} (q : Abstraction N Z)
    (a : First N ρ) (b : Second a) (r : Third b) :
    abstractTail q a b r = observeTail Z a b r := by
  induction q using Quotient.inductionOn with
  | h f => exact tail_comparison f a b r

theorem tail_substitute_preserves (p : Program) (σ : Nat → Expr) (ρ : Nat → Nat)
    (a : First (p.1.subst σ) ρ) (b : Second a) (r : Third b) :
    abstractTail (substitute σ p).2.2 a b r =
      abstractTail p.2.2 (liftFirst p.1 σ ρ a) (liftSecond b) (liftThird r) := by
  exact (abstractTail_comparison (N := p.1.subst σ) (Z := p.2.1.subst σ)
    (substitute σ p).2.2 a b r).trans
    ((tail_substitute p.1 p.2.1 σ ρ a b r).trans
      (abstractTail_comparison p.2.2 _ _ _).symm)

/-- The new dependent field retains the old selected observation. -/
theorem tail_retains {N Z ρ} (f : Frame (support N Z))
    (a : First N ρ) (b : Second a) (r : Third b) :
    (⟨(nominalTail f a b r).1, (nominalTail f a b r).2.1⟩ : Observation) =
      nominalObserve f a b := by
  rw [tail_comparison, comparison]
  rfl

end SquareKit.Internal.NominalTelescope
