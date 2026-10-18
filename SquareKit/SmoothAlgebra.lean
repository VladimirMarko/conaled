import SquareKit.SmoothOperations
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Data.Fin.VecNotation

/-!
Experimental smooth algebras and free finite-coordinate smooth functions.
The existing real algebra is retained with proved compatibility; smooth
homomorphisms start with operation preservation and derive their algebra maps.
-/
noncomputable section
open scoped ContDiff
namespace SquareKit.SmoothAlgebra

class Structure (A : Type*) [CommRing A] [Algebra ℝ A] where
  act : {n : ℕ} → Operation n → (Fin n → A) → A
  projection : ∀ {n} (i : Fin n) z, act (projection i) z = z i
  substitute : ∀ {m n} (f : Operation n) (g : Fin n → Operation m) z,
    act (substitute f g) z = act f (fun i => act (g i) z)
  constant : ∀ n a z, act (constant n a) z = algebraMap ℝ A a
  addition : ∀ z, act addition z = z 0 + z 1
  multiplication : ∀ z, act multiplication z = z 0 * z 1

export Structure (act)

variable {A B C D : Type*} [CommRing A] [Algebra ℝ A] [Structure A]
  [CommRing B] [Algebra ℝ B] [Structure B] [CommRing C] [Algebra ℝ C] [Structure C]
  [CommRing D] [Algebra ℝ D] [Structure D]

/-- Preservation of all smooth operations, not merely of the ring reduct. -/
structure Hom (A B : Type*) [CommRing A] [Algebra ℝ A] [Structure A]
    [CommRing B] [Algebra ℝ B] [Structure B] where
  toFun : A → B
  map_act : ∀ {n} (f : Operation n) z, toFun (act f z) = act f (fun i => toFun (z i))

instance : CoeFun (Hom A B) (fun _ => A → B) := ⟨Hom.toFun⟩

namespace Hom
@[ext] theorem ext {f g : Hom A B} (h : ∀ x, f x = g x) : f = g := by
  cases f
  cases g
  congr
  exact funext h

theorem map_scalar (f : Hom A B) (r : ℝ) : f (algebraMap ℝ A r) = algebraMap ℝ B r := by
  simpa only [Structure.constant] using f.map_act (constant 0 r) Fin.elim0

theorem map_add (f : Hom A B) (a b : A) : f (a+b) = f a + f b := by
  simpa only [Structure.addition, Matrix.cons_val_zero, Matrix.cons_val_one] using
    f.map_act addition ![a,b]

theorem map_mul (f : Hom A B) (a b : A) : f (a*b) = f a * f b := by
  simpa only [Structure.multiplication, Matrix.cons_val_zero, Matrix.cons_val_one] using
    f.map_act multiplication ![a,b]

def toAlgHom (f : Hom A B) : A →ₐ[ℝ] B where
  toFun := f
  map_zero' := by simpa using f.map_scalar 0
  map_one' := by simpa using f.map_scalar 1
  map_add' := f.map_add
  map_mul' := f.map_mul
  commutes' := f.map_scalar

def ident : Hom A A := ⟨id, fun _ _ => rfl⟩
def comp (g : Hom B C) (f : Hom A B) : Hom A C :=
  ⟨g ∘ f, fun p z => by change g (f (act p z)) = _; rw [f.map_act, g.map_act]; rfl⟩

theorem ident_comp (f : Hom A B) : comp ident f = f := ext (fun _ => rfl)
theorem comp_ident (f : Hom A B) : comp f ident = f := ext (fun _ => rfl)
theorem comp_assoc (f : Hom A B) (g : Hom B C) (h : Hom C D) :
    comp h (comp g f) = comp (comp h g) f := ext (fun _ => rfl)

theorem toAlgHom_ident : (ident : Hom A A).toAlgHom = AlgHom.id ℝ A := rfl

theorem toAlgHom_comp (g : Hom B C) (f : Hom A B) :
    (comp g f).toAlgHom = g.toAlgHom.comp f.toAlgHom := rfl

end Hom

/-- Actual smooth functions form a subalgebra of the pointwise function algebra. -/
def functions (n : ℕ) : Subalgebra ℝ ((Fin n → ℝ) → ℝ) where
  carrier := {f | ContDiff ℝ ∞ f}
  zero_mem' := by change ContDiff ℝ ∞ (fun _ : Fin n → ℝ => (0 : ℝ)); exact contDiff_const
  one_mem' := by change ContDiff ℝ ∞ (fun _ : Fin n → ℝ => (1 : ℝ)); exact contDiff_const
  add_mem' {f g} hf hg := (show ContDiff ℝ ∞ f from hf).add (show ContDiff ℝ ∞ g from hg)
  mul_mem' {f g} hf hg := (show ContDiff ℝ ∞ f from hf).mul (show ContDiff ℝ ∞ g from hg)
  algebraMap_mem' r := by change ContDiff ℝ ∞ (fun _ : Fin n → ℝ => r); exact contDiff_const

abbrev Free (n : ℕ) := functions n

instance (n : ℕ) : Structure (Free n) where
  act f g := ⟨fun x => f.val (fun i => (g i).val x),
    f.property.comp (contDiff_pi.mpr (fun i => (g i).property))⟩
  projection _ _ := rfl
  substitute _ _ _ := rfl
  constant _ _ _ := rfl
  addition _ := rfl
  multiplication _ := rfl

def generator {n : ℕ} (i : Fin n) : Free n := projection i

/-- Interpretation of a smooth function at a target tuple. -/
def evaluate {n : ℕ} (a : Fin n → A) : Hom (Free n) A where
  toFun f := act (show Operation n from f) a
  map_act f g := Structure.substitute f (fun i => show Operation n from g i) a

@[simp] theorem evaluate_generator {n : ℕ} (a : Fin n → A) (i : Fin n) :
    evaluate a (generator i) = a i := Structure.projection i a

/-- Every free function is its own operation applied to the coordinate generators. -/
theorem generators_generate {n : ℕ} (f : Free n) :
    act (show Operation n from f) (fun i => generator i) = f := rfl

theorem evaluate_unique {n : ℕ} (h : Hom (Free n) A) :
    evaluate (fun i => h (generator i)) = h := by
  apply Hom.ext
  intro f
  exact (h.map_act (show Operation n from f) (fun i => generator i)).symm

/-- Free smooth-algebra universal property, including no generators. -/
def freeEquiv (n : ℕ) : Hom (Free n) A ≃ (Fin n → A) where
  toFun h i := h (generator i)
  invFun := evaluate
  left_inv := evaluate_unique
  right_inv a := funext (evaluate_generator a)

theorem hom_ext_generators {n : ℕ} (h k : Hom (Free n) A)
    (hk : ∀ i, h (generator i) = k (generator i)) : h = k :=
  (freeEquiv n).injective (funext hk)

theorem evaluate_natural {n : ℕ} (h : Hom A B) (a : Fin n → A) :
    Hom.comp h (evaluate a) = evaluate (fun i => h (a i)) := by
  apply Hom.ext
  intro f
  exact h.map_act (show Operation n from f) a

/-- A coordinate map ℝ^m→ℝ^n induces contravariant pullback of actual functions. -/
def pullback {m n : ℕ} (g : Fin n → Operation m) : Hom (Free n) (Free m) :=
  evaluate (fun i => show Free m from g i)

@[simp] theorem pullback_generator {m n : ℕ} (g : Fin n → Operation m) (i : Fin n) :
    pullback g (generator i) = g i := evaluate_generator _ _

theorem pullback_apply {m n : ℕ} (g : Fin n → Operation m) (f : Free n) (x : Fin m → ℝ) :
    (pullback g f).val x = f.val (fun i => (g i).val x) := rfl

theorem pullback_ident (n : ℕ) : pullback (fun i : Fin n => projection i) = Hom.ident := by
  apply Hom.ext
  intro f
  rfl

theorem pullback_comp {l m n : ℕ} (f : Fin n → Operation m) (g : Fin m → Operation l) :
    Hom.comp (pullback g) (pullback f) = pullback (fun i => substitute (f i) g) := by
  apply Hom.ext
  intro h
  rfl

theorem evaluate_pullback {m n : ℕ} (g : Fin n → Operation m) (a : Fin m → A) :
    Hom.comp (evaluate a) (pullback g) = evaluate (fun i => act (g i) a) :=
  evaluate_natural (evaluate a) (fun i => show Free m from g i)

end SquareKit.SmoothAlgebra
