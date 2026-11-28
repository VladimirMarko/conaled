import Applications.Linear.Operations
import SquareKit.FirstOrderNaturality
import Mathlib.Algebra.MvPolynomial.Monad

/-! Polynomial maps, their contravariant coordinate homomorphisms and the
cartesian compiler. Coordinate encodings are shared with the matrix compiler. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace PolynomialMap
open MvPolynomial
universe u v w z
variable {R : Type u} [CommSemiring R]
variable {σ : Type v} {τ : Type w} {υ : Type z}

/-- A polynomial for each output coordinate. -/
abbrev Map (R : Type u) [CommSemiring R] (σ : Type v) (τ : Type w) :=
  τ → MvPolynomial σ R

def coordHom (f : Map R σ τ) : MvPolynomial τ R →ₐ[R] MvPolynomial σ R := aeval f

def identity : Map R σ σ := X

def comp (g : Map R τ υ) (f : Map R σ τ) : Map R σ υ := fun i => coordHom f (g i)

@[simp] theorem coordHom_X (f : Map R σ τ) (i : τ) : coordHom f (X i) = f i := by
  simp [coordHom]

/-- The polynomial universal property retains every coefficient and variable. -/
def coordEquiv : Map R σ τ ≃ (MvPolynomial τ R →ₐ[R] MvPolynomial σ R) where
  toFun := coordHom
  invFun h := fun i => h (X i)
  left_inv f := by funext i; exact coordHom_X f i
  right_inv h := (aeval_unique h).symm

@[simp] theorem coordHom_identity : coordHom (identity (R := R) (σ := σ)) = AlgHom.id R _ := by
  ext i; simp [identity]

@[simp] theorem coordHom_comp (g : Map R τ υ) (f : Map R σ τ) :
    coordHom (comp g f) = (coordHom f).comp (coordHom g) := by
  ext i; simp [comp]

@[simp] theorem identity_comp (f : Map R σ τ) : comp identity f = f := by
  funext i; simp [comp, identity]
@[simp] theorem comp_identity (f : Map R σ τ) : comp f identity = f := by
  funext i; simp [comp]

theorem comp_assoc {ω : Type*} (h : Map R υ ω) (g : Map R τ υ) (f : Map R σ τ) :
    comp (comp h g) f = comp h (comp g f) := by
  funext i; simp [comp, coordHom_comp]

variable {A : Type*} [CommSemiring A] [Algebra R A]

def evaluate (f : Map R σ τ) (x : σ → A) : τ → A := fun i => aeval x (f i)

@[simp] theorem evaluate_identity (x : σ → A) : evaluate (identity (R := R)) x = x := by
  funext i; simp [evaluate, identity]

@[simp] theorem evaluate_comp (g : Map R τ υ) (f : Map R σ τ) (x : σ → A) :
    evaluate (comp g f) x = evaluate g (evaluate f x) := by
  funext i
  exact congrArg (fun h : MvPolynomial τ R →ₐ[R] A => h (g i))
    (show (aeval x).comp (coordHom f) = aeval (evaluate f x) by
      ext j; simp [coordHom, evaluate])

theorem evaluate_natural {B : Type*} [CommSemiring B] [Algebra R B]
    (h : A →ₐ[R] B) (f : Map R σ τ) (x : σ → A) :
    (fun i => h (evaluate f x i)) = evaluate f (fun j => h (x j)) := by
  funext i
  exact congrArg (fun k : MvPolynomial σ R →ₐ[R] B => k (f i)) (MvPolynomial.comp_aeval x h)

/-- Polynomial-ring valued points recover the entire polynomial map. -/
theorem evaluate_generic (f : Map R σ τ) : evaluate f X = f := by
  funext i; simp [evaluate]

end PolynomialMap

namespace AffinePolynomialCompiler
open FirstOrderCompiler MvPolynomial
open MatrixCompiler (Slots encode decode encode_decode decode_encode)
variable (R : Type) [CommRing R]
abbrev Code (a b : Ty) := PolynomialMap.Map R (Slots a) (Slots b)

inductive Prim (R : Type) : Ty → Ty → Type where
  | constant : R → Prim R .unit .base
  | add : Prim R (.prod .base .base) .base
  | mul : Prim R (.prod .base .base) .base

def primitive : {a b : Ty} → Prim R a b → Code R a b
  | _, _, .constant r => fun _ => C r
  | _, _, .add => fun _ => X (.inl ()) + X (.inr ())
  | _, _, .mul => fun _ => X (.inl ()) * X (.inr ())

def first (a b : Ty) : Code R (.prod a b) a := fun i => X (.inl i)
def second (a b : Ty) : Code R (.prod a b) b := fun i => X (.inr i)
def pair {a b c : Ty} (f : Code R a b) (g : Code R a c) : Code R a (.prod b c) :=
  Sum.elim f g

def target : Target (Prim R) where
  Hom := Code R
  ident := PolynomialMap.identity
  comp := PolynomialMap.comp
  terminal := Empty.elim
  fst := first R _ _
  snd := second R _ _
  pair := pair R
  primitive := primitive R

variable (A : Type) [CommRing A] [Algebra R A]

def meaning : {a b : Ty} → Prim R a b → Val A a → Val A b
  | _, _, .constant r, _ => algebraMap R A r
  | _, _, .add, x => x.1 + x.2
  | _, _, .mul, x => x.1 * x.2

def denote {a b : Ty} (f : Code R a b) (x : Val A a) : Val A b :=
  decode b (PolynomialMap.evaluate f (encode a x))

/-- All commutative R-algebras supply the old compiler's Set-valued soundness. -/
def sound : Sound A (target R) (meaning R A) where
  denote := denote R A
  ident x := by simpa [denote, target] using decode_encode _ x
  comp g f x := by
    change decode _ (PolynomialMap.evaluate (PolynomialMap.comp g f) (encode _ x)) = _
    rw [PolynomialMap.evaluate_comp]
    simp only [denote, encode_decode]
  terminal x := rfl
  fst {a b} x := by
    change decode a (fun i => aeval (encode (.prod a b) x) (X (.inl i))) = x.1
    simpa [encode] using decode_encode a x.1
  snd {a b} x := by
    change decode b (fun i => aeval (encode (.prod a b) x) (X (.inr i))) = x.2
    simpa [encode] using decode_encode b x.2
  pair f g x := rfl
  primitive p x := by cases p <;> simp [denote, PolynomialMap.evaluate, target,
    primitive, meaning, encode, decode]

theorem compile_correct (t : Term (Prim R) Γ a) (x : Val A (context Γ)) :
    denote R A (compile (target R) t) x = eval (meaning R A) t x :=
  SquareKit.FirstOrderNaturality.compile_sound (target R) (sound R A) t x

end AffinePolynomialCompiler
