import Squares
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# All orders of derivatives, with an executable finite representation

This is a completed polynomial fragment of the derivative-tower proposal in
Elliott's incomplete higher-order AD draft. The finite polynomial represents
an infinite sequence of derivatives. `jet_correct` identifies *every* component
with the analytic iterated derivative, and `jet_leibniz` proves the all-order
product operation. Orders above the degree are exactly zero.

Polynomial expression composition, addition, and multiplication each have a
commuting square. `compile_jet_correct` connects the independent expression
evaluator to the entire derivative tower. This is neither a claimed solution
of the draft's general lazy tower algorithm nor a Taylor-convergence claim.
-/

noncomputable section

namespace Applications.AD.Jets

open Polynomial

abbrev Poly := Polynomial ℝ

@[reducible] def polynomialRep : Squares.Rep where
  R := Poly
  S := ℝ → ℝ
  decode p := fun x => p.eval x

def addSquare : Squares.Square (Squares.product polynomialRep polynomialRep) polynomialRep where
  impl p := (p.1 : Poly) + (p.2 : Poly)
  spec p := fun x => p.1 x + p.2 x
  commutes p := by funext x; exact Polynomial.eval_add

def mulSquare : Squares.Square (Squares.product polynomialRep polynomialRep) polynomialRep where
  impl p := (p.1 : Poly) * (p.2 : Poly)
  spec p := fun x => p.1 x * p.2 x
  commutes p := by funext x; exact Polynomial.eval_mul

def compositionSquare : Squares.Square
    (Squares.product polynomialRep polynomialRep) polynomialRep where
  impl p := p.1.comp p.2
  spec p := p.1 ∘ p.2
  commutes p := by funext x; exact Polynomial.eval_comp

/-- Symbolic differentiation is a square whose specification is analytic differentiation. -/
def derivativeSquare : Squares.Square polynomialRep polynomialRep where
  impl := Polynomial.derivative
  spec := deriv
  commutes p := by funext x; exact (p.deriv (x := x)).symm

def derivativeN (n : ℕ) (p : Poly) : Poly := Polynomial.derivative^[n] p
def jet (p : Poly) (n : ℕ) (x : ℝ) : ℝ := (derivativeN n p).eval x

/-- All orders, not just the first or a finite collection of examples. -/
theorem jet_correct (p : Poly) (n : ℕ) :
    jet p n = iteratedDeriv n (fun x => p.eval x) := by
  induction n with
  | zero =>
      rw [iteratedDeriv_zero]
      rfl
  | succ n ih =>
      rw [iteratedDeriv_succ, ← ih]
      funext x
      change (derivativeN (n + 1) p).eval x =
        deriv (fun y => (derivativeN n p).eval y) x
      rw [Polynomial.deriv]
      simp only [derivativeN, Function.iterate_succ_apply']

def iteratedDerivativeSquare (n : ℕ) : Squares.Square polynomialRep polynomialRep where
  impl := derivativeN n
  spec := iteratedDeriv n
  commutes p := jet_correct p n

/-- The whole infinite derivative tower is represented by a finite polynomial. -/
@[reducible] def towerRep : Squares.Rep where
  R := Poly
  S := ℕ → ℝ → ℝ
  decode := jet

theorem derivativeN_add (n : ℕ) (p q : Poly) :
    derivativeN n (p + q) = derivativeN n p + derivativeN n q := by
  induction n with
  | zero => rfl
  | succ n ih =>
      unfold derivativeN at *
      simp only [Function.iterate_succ_apply']
      rw [ih, map_add]

def towerAddSquare : Squares.Square (Squares.product towerRep towerRep) towerRep where
  impl p := (p.1 : Poly) + (p.2 : Poly)
  spec p := fun n x => p.1 n x + p.2 n x
  commutes p := by
    funext n x
    change (derivativeN n (p.1 + p.2)).eval x =
      (derivativeN n p.1).eval x + (derivativeN n p.2).eval x
    rw [derivativeN_add, Polynomial.eval_add]

theorem jet_successor (p : Poly) (n : ℕ) (x : ℝ) :
    HasDerivAt (jet p n) (jet p (n + 1) x) x := by
  simpa only [jet, derivativeN, Function.iterate_succ_apply'] using
    (derivativeN n p).hasDerivAt x

/-- The binomial/Leibniz convolution of derivative components. -/
theorem jet_leibniz (p q : Poly) (n : ℕ) (x : ℝ) :
    jet (p * q) n x =
      ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * (jet p (n - k) x * jet q k x) := by
  simp only [jet, derivativeN, Polynomial.iterate_derivative_mul,
    Polynomial.eval_finset_sum, Polynomial.eval_mul,
    nsmul_eq_mul, Nat.succ_eq_add_one, Polynomial.eval_natCast]

/-- Multiplying represented functions realizes binomial convolution of their derivative towers. -/
def towerMulSquare : Squares.Square (Squares.product towerRep towerRep) towerRep where
  impl p := (p.1 : Poly) * (p.2 : Poly)
  spec p := fun n x =>
    ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * (p.1 (n - k) x * p.2 k x)
  commutes p := by
    funext n x
    exact jet_leibniz p.1 p.2 n x

theorem jet_monomial (degree order : ℕ) (x : ℝ) :
    jet (Polynomial.X ^ degree) order x =
      (Nat.descFactorial degree order : ℝ) * x ^ (degree - order) := by
  simp only [jet, derivativeN, Polynomial.iterate_derivative_X_pow_eq_C_mul,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]

theorem jet_zero_above_degree (p : Poly) (n : ℕ) (hn : p.natDegree < n) (x : ℝ) :
    jet p n x = 0 := by
  simp only [jet, derivativeN, Polynomial.iterate_derivative_eq_zero hn, Polynomial.eval_zero]

/-! ## An independent expression language and its complete tower compiler -/

inductive Expr where
  | var
  | constant : ℝ → Expr
  | add : Expr → Expr → Expr
  | mul : Expr → Expr → Expr
  | comp : Expr → Expr → Expr

def denote : Expr → ℝ → ℝ
  | .var, x => x
  | .constant c, _ => c
  | .add e f, x => denote e x + denote f x
  | .mul e f, x => denote e x * denote f x
  | .comp e f, x => denote e (denote f x)

def compile : Expr → Poly
  | .var => Polynomial.X
  | .constant c => Polynomial.C c
  | .add e f => compile e + compile f
  | .mul e f => compile e * compile f
  | .comp e f => (compile e).comp (compile f)

theorem compile_correct (e : Expr) (x : ℝ) : (compile e).eval x = denote e x := by
  induction e generalizing x with
  | var => exact Polynomial.eval_X
  | constant c => exact Polynomial.eval_C
  | add e f ie iff => simp only [compile, denote, Polynomial.eval_add, ie, iff]
  | mul e f ie iff => simp only [compile, denote, Polynomial.eval_mul, ie, iff]
  | comp e f ie iff => simp only [compile, denote, Polynomial.eval_comp, ie, iff]

/-- Every order of the compiled representation is the true derivative of the source evaluator. -/
theorem compile_jet_correct (e : Expr) (n : ℕ) (x : ℝ) :
    jet (compile e) n x = iteratedDeriv n (denote e) x := by
  have heq : (fun y => (compile e).eval y) = denote e := funext (compile_correct e)
  rw [jet_correct, heq]

end Applications.AD.Jets
