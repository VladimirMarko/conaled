import Compiler
import SquareKit.Relations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Ring

/-!
# Higher-order functions: a curve logical relation

Elliott's *Higher-order, higher-order automatic differentiation* is an early,
incomplete November 2019 draft. Its attempts to differentiate ordinary
function spaces expose a real object-representation issue. Here we discharge
a precise alternative: a logical relation on curves, recursively at every
source type, for the existing compiler's entire simply typed syntax.

At a scalar, a dual number must contain the curve's value and its true real
derivative. At a function type, it must preserve the relation for every related
argument curve. This includes jointly varying functions, captured variables,
and arguments. We prove the fundamental lemma for lambdas, application,
products, let, and sums; sum curves have a fixed constructor along the whole
curve. The scalar-observation theorem states `HasDerivAt`, not formal equality
of derivative expressions. No norm or cartesian closure on all function spaces
is assumed, and no reverse-mode claim for function types is made here.
-/

noncomputable section

namespace Applications.AD.HigherOrder

open CategoricalCompiler

abbrev Dual := ℝ × ℝ

/-- A scalar's tangent is the derivative of a curve at the observation point. -/
def Related (x : ℝ) : (a : Ty) → Val Dual a → (ℝ → Val ℝ a) → Prop
  | .base, d, f => d.1 = f x ∧ HasDerivAt f d.2 x
  | .unit, _, _ => True
  | .prod a b, d, f =>
      Related x a d.1 (fun s => (f s).1) ∧ Related x b d.2 (fun s => (f s).2)
  | .arr a b, d, f =>
      ∀ (da : Val Dual a) (fa : ℝ → Val ℝ a), Related x a da fa →
        Related x b (d da) (fun s => f s (fa s))
  | .sum a _, .inl d, f =>
      ∃ fa : ℝ → Val ℝ a, (∀ s, f s = .inl (fa s)) ∧ Related x a d fa
  | .sum _ b, .inr d, f =>
      ∃ fb : ℝ → Val ℝ b, (∀ s, f s = .inr (fb s)) ∧ Related x b d fb

theorem lookup_related (v : Var Γ a) (x : ℝ)
    {ρd : Val Dual (context Γ)} {ρ : ℝ → Val ℝ (context Γ)}
    (hρ : Related x (context Γ) ρd ρ) :
    Related x a (lookup v ρd) (fun s => lookup v (ρ s)) := by
  induction v with
  | here => exact hρ.2
  | there v ih => exact ih hρ.1

variable {Prim : Ty → Ty → Type}

abbrev PrimitiveMeaning (B : Type) (Prim : Ty → Ty → Type) :=
  {a b : Ty} → Prim a b → Val B a → Val B b

def PrimitivesRelated (real : PrimitiveMeaning ℝ Prim) (dual : PrimitiveMeaning Dual Prim) :=
  ∀ {a b : Ty} (p : Prim a b) (x : ℝ) (d : Val Dual a) (f : ℝ → Val ℝ a),
    Related x a d f → Related x b (dual p d) (fun s => real p (f s))

/-- The fundamental lemma covers every term, including higher-order source terms. -/
theorem eval_related (real : PrimitiveMeaning ℝ Prim) (dual : PrimitiveMeaning Dual Prim)
    (hprim : PrimitivesRelated real dual) (t : Term Prim Γ a) (x : ℝ)
    {ρd : Val Dual (context Γ)} {ρ : ℝ → Val ℝ (context Γ)}
    (hρ : Related x (context Γ) ρd ρ) :
    Related x a (eval dual t ρd) (fun s => eval real t (ρ s)) := by
  induction t with
  | var v => exact lookup_related v x hρ
  | unit => trivial
  | pair t u it iu => exact ⟨it hρ, iu hρ⟩
  | fst t it => exact (it hρ).1
  | snd t it => exact (it hρ).2
  | lam t it =>
      intro da fa ha
      exact it ⟨hρ, ha⟩
  | app t u it iu => exact it hρ _ _ (iu hρ)
  | letE t u it iu => exact iu ⟨hρ, it hρ⟩
  | inl t it => exact ⟨_, fun _ => rfl, it hρ⟩
  | inr t it => exact ⟨_, fun _ => rfl, it hρ⟩
  | caseE t l r it il ir =>
      have ht := it hρ
      cases hd : eval dual t ρd with
      | inl da =>
          rw [hd] at ht
          obtain ⟨fa, hf, ha⟩ := ht
          simpa only [eval, hd, hf] using il ⟨hρ, ha⟩
      | inr db =>
          rw [hd] at ht
          obtain ⟨fb, hf, hb⟩ := ht
          simpa only [eval, hd, hf] using ir ⟨hρ, hb⟩
  | prim p t it => exact hprim p x _ _ (it hρ)

/-- The original categorical compiler is reused with an enriched base interpretation. -/
def compileDual (dual : PrimitiveMeaning Dual Prim) (t : Term Prim Γ a) :
    Val Dual (context Γ) → Val Dual a :=
  run dual (compile (rawTarget Prim) t)

theorem compileDual_related (real : PrimitiveMeaning ℝ Prim)
    (dual : PrimitiveMeaning Dual Prim) (hprim : PrimitivesRelated real dual)
    (t : Term Prim Γ a) (x : ℝ)
    {ρd : Val Dual (context Γ)} {ρ : ℝ → Val ℝ (context Γ)}
    (hρ : Related x (context Γ) ρd ρ) :
    Related x a (compileDual dual t ρd) (fun s => eval real t (ρ s)) := by
  have hc := CategoricalCompiler.compile_sound (rawTarget Prim) (rawSound dual) t ρd
  change run dual (compile (rawTarget Prim) t) ρd = eval dual t ρd at hc
  rw [compileDual, hc]
  exact eval_related real dual hprim t x hρ

/-- Every scalar observation of every compiled higher-order program has a true derivative. -/
theorem compileDual_hasDerivAt (real : PrimitiveMeaning ℝ Prim)
    (dual : PrimitiveMeaning Dual Prim) (hprim : PrimitivesRelated real dual)
    (t : Term Prim Γ .base) (x : ℝ)
    {ρd : Val Dual (context Γ)} {ρ : ℝ → Val ℝ (context Γ)}
    (hρ : Related x (context Γ) ρd ρ) :
    HasDerivAt (fun s => eval real t (ρ s)) (compileDual dual t ρd).2 x :=
  (compileDual_related real dual hprim t x hρ).2

/-- Curves are semantic objects; dual values are their represented observations. -/
def curveRep (x : ℝ) (a : Ty) : Relational.RelRep where
  R := Val Dual a
  S := ℝ → Val ℝ a
  Rel := Related x a

/-- The higher-order fundamental lemma is an explicit representation square. -/
def compileCurveSquare (real : PrimitiveMeaning ℝ Prim)
    (dual : PrimitiveMeaning Dual Prim) (hprim : PrimitivesRelated real dual)
    (t : Term Prim Γ a) (x : ℝ) :
    Relational.RelSquare (curveRep x (context Γ)) (curveRep x a) where
  impl := compileDual dual t
  spec ρ s := eval real t (ρ s)
  preserves h := compileDual_related real dual hprim t x h

/-! ## All primitive obligations are discharged -/

inductive RealPrim : Ty → Ty → Type where
  | constant : ℝ → RealPrim .unit .base
  | add : RealPrim (.prod .base .base) .base
  | mul : RealPrim (.prod .base .base) .base

def realMeaning : PrimitiveMeaning ℝ RealPrim
  | _, _, .constant c, _ => c
  | _, _, .add, p => p.1 + p.2
  | _, _, .mul, p => p.1 * p.2

def dualMeaning : PrimitiveMeaning Dual RealPrim
  | _, _, .constant c, _ => (c, 0)
  | _, _, .add, p => (p.1.1 + p.2.1, p.1.2 + p.2.2)
  | _, _, .mul, p => (p.1.1 * p.2.1, p.1.2 * p.2.1 + p.1.1 * p.2.2)

theorem realPrimitives_related : PrimitivesRelated realMeaning dualMeaning := by
  intro a b p x d f h
  cases p with
  | constant c => exact ⟨rfl, hasDerivAt_const x c⟩
  | add =>
      exact ⟨congrArg₂ (· + ·) h.1.1 h.2.1, h.1.2.add h.2.2⟩
  | mul =>
      refine ⟨congrArg₂ (· * ·) h.1.1 h.2.1, ?_⟩
      change HasDerivAt (fun s => (f s).1 * (f s).2)
        (d.1.2 * d.2.1 + d.1.1 * d.2.2) x
      rw [h.1.1, h.2.1]
      exact h.1.2.mul h.2.2

/-! ## A function that varies with its captured environment -/

def twice (Γ : Ctx) : Term RealPrim Γ (.arr (.arr .base .base) (.arr .base .base)) :=
  .lam (.lam (.app (.var (.there .here))
    (.app (.var (.there .here)) (.var .here))))

/-- The function returned by the lambda is y ↦ x*y+x, where x is captured. -/
def capturedFunction : Term RealPrim [.base] (.arr .base .base) :=
  .lam (.prim .add (.pair
    (.prim .mul (.pair (.var (.there .here)) (.var .here)))
    (.var (.there .here))))

def higherOrderExample : Term RealPrim [.base] .base :=
  .app (.app (twice [.base]) capturedFunction) (.var .here)

theorem higherOrder_primal (x : ℝ) :
    eval realMeaning higherOrderExample ((), x) = x * (x * x + x) + x := rfl

theorem higherOrder_dual (x v : ℝ) :
    eval dualMeaning higherOrderExample ((), (x, v)) =
      (x * (x * x + x) + x, (3 * x * x + 2 * x + 1) * v) := by
  apply Prod.ext
  · rfl
  · change v * (x * x + x) + x * (v * x + x * v + v) + v = _
    ring

theorem higherOrder_hasDerivAt (x : ℝ) :
    HasDerivAt (fun s : ℝ => s * (s * s + s) + s) (3 * x * x + 2 * x + 1) x := by
  have henv : Related x (context [.base]) ((), (x, 1)) (fun s => ((), s)) :=
    ⟨trivial, rfl, hasDerivAt_id x⟩
  have h := (eval_related realMeaning dualMeaning realPrimitives_related
    higherOrderExample x henv).2
  rw [higherOrder_dual] at h
  change HasDerivAt (fun s : ℝ => s * (s * s + s) + s)
    ((3 * x * x + 2 * x + 1) * 1) x at h
  simpa only [mul_one] using h

end Applications.AD.HigherOrder
