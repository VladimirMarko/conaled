import Applications.Parallel.ScanPlan
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Ring.Basic

/-! # Powers and polynomial evaluation, derived from certified scan -/

namespace Applications.Parallel

universe u

theorem sequential_replicate {M : Type u} [Monoid M] (a : M) (n : Nat) :
    sequential 1 (List.replicate n a) =
      ((List.range n).map (a ^ ·), a ^ n) := by
  induction n with
  | zero => simp [sequential]
  | succ n ih =>
    simp only [List.replicate_succ, sequential_cons, one_mul]
    rw [sequential_seed a, ih]
    simp [List.range_succ_eq_map, List.map_map, Function.comp_def, pow_succ']

namespace Scanner

variable {M : Type u} [Monoid M] {s : Shape}

def powers (p : Scanner s M) (a : M) : s.Data M × M := p.run (s.pure a)

theorem powers_correct (p : Scanner s M) (a : M) :
    (s.flatten (p.powers a).1, (p.powers a).2) =
      ((List.range s.size).map (a ^ ·), a ^ s.size) := by
  rw [powers, p.correct, Shape.flatten_pure, sequential_replicate]

def powersSquare (p : Scanner s M) :
    Squares.Square ⟨M, M, id⟩ (Squares.product (s.rep M) ⟨M, M, id⟩) where
  impl := p.powers
  spec := fun a => ((List.range s.size).map (a ^ ·), a ^ s.size)
  commutes := p.powers_correct

end Scanner

section Polynomial

variable {R : Type u} [CommSemiring R]

/-- Ordinary coefficient-order polynomial denotation, independent of shape. -/
def polynomial (coefficients : List R) (x : R) : R :=
  (List.zipWith (fun a n => a * x ^ n) coefficients (List.range coefficients.length)).sum

/-- Evaluate by a parallel scan of repeated `x`, followed by a dot product. -/
def evaluatePolynomial (p : ScanPlan) (coefficients : p.shape.Data R) (x : R) : R :=
  let powers := p.scanner.powers x
  (p.shape.flatten (p.shape.zipWith (· * ·) coefficients powers.1)).sum

theorem evaluatePolynomial_correct (p : ScanPlan) (coefficients : p.shape.Data R) (x : R) :
    evaluatePolynomial p coefficients x = polynomial (p.shape.flatten coefficients) x := by
  have h := congrArg Prod.fst (p.scanner.powers_correct x)
  simp only at h
  simp only [evaluatePolynomial, Shape.flatten_zipWith, h, polynomial, Shape.flatten_length,
    List.zipWith_map_right]

def polynomialSquare (p : ScanPlan) :
    Squares.Square (Squares.product (p.shape.rep R) ⟨R, R, id⟩) ⟨R, R, id⟩ where
  impl := fun x => evaluatePolynomial p x.1 x.2
  spec := fun x => polynomial x.1 x.2
  commutes := fun x => evaluatePolynomial_correct p x.1 x.2

end Polynomial
end Applications.Parallel
