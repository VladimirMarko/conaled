import Applications.AD.Jets
import Applications.Parallel.Polynomial
import SquareKit.Combinators
import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# Compile all-order derivatives to a shaped scan evaluator

The runtime package contains a scan plan and coefficients whose type depends
on that plan. Its decoder is polynomial denotation. This joins the analytic
AD proof to a distinct, scan-based evaluation algorithm by pasting squares.
-/
namespace Examples.JetScan
open Applications.Parallel

def planForLength : Nat → ScanPlan
  | 0 => .empty
  | n + 1 => .prod .leaf (planForLength n)

@[simp] theorem planForLength_size (n : Nat) : (planForLength n).shape.size = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [planForLength, ScanPlan.shape, Shape.size, ih, Nat.add_comm]

def coefficients {R : Type} [Semiring R] (s : Shape) (p : Polynomial R)
    (offset : Nat) : s.Data R :=
  match s with
  | .empty => PUnit.unit
  | .leaf => p.coeff offset
  | .prod s t => (coefficients s p offset, coefficients t p (offset + s.size))

theorem flatten_coefficients {R : Type} [Semiring R] (s : Shape) (p : Polynomial R)
    (offset : Nat) :
    s.flatten (coefficients s p offset) =
      (List.range s.size).map (fun i => p.coeff (offset + i)) := by
  induction s generalizing offset with
  | empty => rfl
  | leaf => simp [coefficients, Shape.flatten, Shape.size, List.range_succ]
  | prod s t ihs iht =>
    simp only [coefficients, Shape.flatten, Shape.size, ihs, iht,
      List.range_add, List.map_append, List.map_map, Function.comp_def, Nat.add_assoc]

private theorem sum_range_list {R : Type} [AddCommMonoid R] (f : Nat → R) (n : Nat) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, ih, Finset.sum_range_succ]

theorem coefficient_polynomial {R : Type} [CommSemiring R] (p : Polynomial R)
    (n : Nat) (hn : p.natDegree < n) (x : R) :
    polynomial ((List.range n).map p.coeff) x = p.eval x := by
  rw [polynomial]
  simp only [List.length_map, List.length_range, List.zipWith_map_left,
    List.zipWith_self]
  rw [sum_range_list]
  exact (Polynomial.eval_eq_sum_range' hn x).symm

/-- Any sufficiently large shape and any certified scan recipe can be used. -/
theorem shaped_evaluation_correct {R : Type} [CommSemiring R]
    (plan : ScanPlan) (p : Polynomial R) (h : p.natDegree < plan.shape.size) (x : R) :
    evaluatePolynomial plan (coefficients plan.shape p 0) x = p.eval x := by
  rw [evaluatePolynomial_correct, flatten_coefficients]
  simp only [Nat.zero_add]
  exact coefficient_polynomial p _ h x

structure Prepared (R : Type) where
  plan : ScanPlan
  data : plan.shape.Data R

@[reducible] def preparedRep (R : Type) [CommSemiring R] : Squares.Rep where
  R := Prepared R
  S := R → R
  decode p := polynomial (p.plan.shape.flatten p.data)

noncomputable def prepare {R : Type} [CommSemiring R] (p : Polynomial R) : Prepared R :=
  let plan := planForLength (p.natDegree + 1)
  ⟨plan, coefficients plan.shape p 0⟩

theorem prepare_correct {R : Type} [CommSemiring R] (p : Polynomial R) (x : R) :
    (preparedRep R).decode (prepare p) x = p.eval x := by
  change polynomial ((planForLength (p.natDegree + 1)).shape.flatten
    (coefficients _ p 0)) x = p.eval x
  rw [flatten_coefficients]
  simp only [Nat.zero_add, planForLength_size]
  exact coefficient_polynomial p _ (Nat.lt_succ_self _) x

noncomputable def prepareSquare :
    Squares.Square Applications.AD.Jets.polynomialRep (preparedRep ℝ) where
  impl := prepare
  spec := id
  commutes p := funext (prepare_correct p)

def evaluationSquare (R : Type) [CommSemiring R] :
    Squares.Square (Squares.product (preparedRep R) (Squares.exact R)) (Squares.exact R) where
  impl p := @evaluatePolynomial R _ p.1.plan p.1.data p.2
  spec p := p.1 p.2
  commutes p := evaluatePolynomial_correct p.1.plan p.1.data p.2

noncomputable def jetSquare (n : Nat) :
    Squares.Square
      (Squares.product Applications.AD.Jets.polynomialRep (Squares.exact ℝ))
      (Squares.exact ℝ) :=
  Squares.compose (evaluationSquare ℝ)
    (Squares.productMap
      (Squares.compose prepareSquare (Applications.AD.Jets.iteratedDerivativeSquare n))
      (Squares.identity (Squares.exact ℝ)))

/-- All derivative orders and all source expressions, evaluated by the scan backend. -/
theorem source_jet_scan (e : Applications.AD.Jets.Expr) (n : Nat) (x : ℝ) :
    (jetSquare n).impl (Applications.AD.Jets.compile e, x) =
      iteratedDeriv n (Applications.AD.Jets.denote e) x := by
  have h := (jetSquare n).commutes (Applications.AD.Jets.compile e, x)
  change (jetSquare n).impl (Applications.AD.Jets.compile e, x) =
    iteratedDeriv n (fun y => (Applications.AD.Jets.compile e).eval y) x at h
  rw [show (fun y => (Applications.AD.Jets.compile e).eval y) =
    Applications.AD.Jets.denote e from funext (Applications.AD.Jets.compile_correct e)] at h
  exact h

end Examples.JetScan
