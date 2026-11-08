import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic.Ring

/-! Experimental sensitivity-aware error composition. Functions and their selected
outputs remain explicit; equal bounds do not identify implementations. -/
namespace NumericalError
open scoped NNReal

/-- An error transformer, with nonnegative sensitivity and local error. -/
structure Bound where
  sensitivity : ℝ≥0
  localError : ℝ≥0

namespace Bound

def apply (b : Bound) (e : ℝ) : ℝ := b.sensitivity * e + b.localError

def identity : Bound := ⟨1, 0⟩

/-- First `a`, then `b`. -/
def comp (a b : Bound) : Bound :=
  ⟨b.sensitivity * a.sensitivity, b.sensitivity * a.localError + b.localError⟩

@[simp] theorem identity_apply (e : ℝ) : identity.apply e = e := by simp [apply, identity]
@[simp] theorem comp_apply (a b : Bound) (e : ℝ) :
    (a.comp b).apply e = b.apply (a.apply e) := by simp [apply, comp]; ring
@[simp] theorem identity_comp (a : Bound) : identity.comp a = a := by cases a; simp [comp, identity]
@[simp] theorem comp_identity (a : Bound) : a.comp identity = a := by cases a; simp [comp, identity]
theorem comp_assoc (a b c : Bound) : (a.comp b).comp c = a.comp (b.comp c) := by
  cases a; cases b; cases c
  simp only [comp, Bound.mk.injEq]
  constructor <;> ring

/-- Chronological multiplication: the left factor runs first. -/
instance : Monoid Bound where
  mul := comp
  one := identity
  mul_assoc := comp_assoc
  one_mul := identity_comp
  mul_one := comp_identity

@[simp] theorem mul_apply (a b : Bound) (e : ℝ) :
    (a * b).apply e = b.apply (a.apply e) := comp_apply a b e

theorem monotone (b : Bound) : Monotone b.apply := by
  intro x y h
  exact add_le_add (mul_le_mul_of_nonneg_left h b.sensitivity.coe_nonneg) le_rfl
end Bound

variable {A B C : Type*} [PseudoMetricSpace A] [PseudoMetricSpace B] [PseudoMetricSpace C]

/-- Propagate input error through a domain-sensitive map, then add the local
error to the selected target. This also applies to Euler truncation. -/
theorem propagate {f : A → B} {s : Set A} {L : ℝ≥0}
    (hf : LipschitzOnWith L f s) {xhat x : A} (hh : xhat ∈ s) (hx : x ∈ s)
    {y : B} {e d : ℝ} (he : dist xhat x ≤ e) (hd : dist (f x) y ≤ d) :
    dist (f xhat) y ≤ L * e + d :=
  (dist_triangle _ _ _).trans (add_le_add
    ((hf.dist_le_mul _ hh _ hx).trans (mul_le_mul_of_nonneg_left he L.coe_nonneg)) hd)

/-- Uniform errors are properties of specified maps, not quotients of them. -/
def UniformOn (s : Set A) (approx exact : A → B) (d : ℝ) : Prop :=
  ∀ x ∈ s, dist (approx x) (exact x) ≤ d

theorem estimate {f fhat : A → B} {s : Set A} {b : Bound}
    (hf : LipschitzOnWith b.sensitivity f s) (herr : UniformOn s fhat f b.localError)
    {xhat x : A} (hh : xhat ∈ s) (hx : x ∈ s) {e : ℝ} (he : dist xhat x ≤ e) :
    dist (fhat xhat) (f x) ≤ b.apply e := by
  rw [dist_comm]
  exact propagate hf hx hh (by rwa [dist_comm])
    (by rw [dist_comm]; exact herr _ hh)

/-- Both actual and exact intermediates must belong to the second domain. -/
theorem compose {f fhat : A → B} {g ghat : B → C} {s : Set A} {t : Set B}
    {a b : Bound} (hf : LipschitzOnWith a.sensitivity f s)
    (ef : UniformOn s fhat f a.localError)
    (hg : LipschitzOnWith b.sensitivity g t) (eg : UniformOn t ghat g b.localError)
    (closed : Set.MapsTo f s t) (closedHat : Set.MapsTo fhat s t)
    {xhat x : A} (hh : xhat ∈ s) (hx : x ∈ s) {e : ℝ} (he : dist xhat x ≤ e) :
    dist (ghat (fhat xhat)) (g (f x)) ≤ (a.comp b).apply e := by
  rw [Bound.comp_apply]
  exact estimate hg eg (closedHat hh) (closed hx) (estimate hf ef hh hx he)

/-- Zero-error identity retains the selected input. -/
theorem identity_estimate {xhat x : A} {e : ℝ} (he : dist xhat x ≤ e) :
    dist (id xhat) (id x) ≤ Bound.identity.apply e := by simpa using he

/-- Three stages may be associated either way; each actual and exact
intermediate must remain in the next certified domain. -/
theorem compose_three {D : Type*} [PseudoMetricSpace D]
    {f fhat : A → B} {g ghat : B → C} {h hhat : C → D}
    {s : Set A} {t : Set B} {u : Set C} {a b c : Bound}
    (hf : LipschitzOnWith a.sensitivity f s) (ef : UniformOn s fhat f a.localError)
    (hg : LipschitzOnWith b.sensitivity g t) (eg : UniformOn t ghat g b.localError)
    (hh : LipschitzOnWith c.sensitivity h u) (eh : UniformOn u hhat h c.localError)
    (cf : Set.MapsTo f s t) (cfhat : Set.MapsTo fhat s t)
    (cg : Set.MapsTo g t u) (cghat : Set.MapsTo ghat t u)
    {xhat x : A} (hxh : xhat ∈ s) (hx : x ∈ s) {e : ℝ} (he : dist xhat x ≤ e) :
    dist (hhat (ghat (fhat xhat))) (h (g (f x))) ≤ ((a.comp b).comp c).apply e ∧
    ((a.comp b).comp c).apply e = (a.comp (b.comp c)).apply e := by
  constructor
  · rw [Bound.comp_apply]
    exact estimate hh eh (cghat (cfhat hxh)) (cg (cf hx))
      (compose hf ef hg eg cf cfhat hxh hx he)
  · rw [Bound.comp_assoc]

end NumericalError
