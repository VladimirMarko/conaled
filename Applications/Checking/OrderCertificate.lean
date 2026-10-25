import SquareKit.Combinators
import Mathlib.Data.List.Pairwise

/-!
# Experimental finite ordering certificates

The certificate is a finite list; its declarative meaning is `List.Pairwise R`.
The reference checks every later element. The realization checks neighbors.
Transitivity is required only for their equivalence, not for either algorithm.
This is a bounded certificate experiment, not a checker for Lean expressions.
-/
namespace OrderCertificate
open Squares (exact)

variable {α : Type} (cmp : α → α → Bool)

/-- Reference algorithm: compare each entry with every later entry. -/
def reference : List α → Bool
  | [] => true
  | x :: xs => xs.all (cmp x) && reference xs

/-- Realization: compare consecutive entries, stopping on failure. -/
def adjacent : List α → Bool
  | [] => true
  | [_] => true
  | x :: y :: xs => cmp x y && adjacent (y :: xs)

variable {cmp} {R : α → α → Prop}

/-- The comparator contract suffices for reference correctness. -/
theorem reference_correct (law : ∀ x y, cmp x y = true ↔ R x y) (xs : List α) :
    reference cmp xs = true ↔ xs.Pairwise R := by
  induction xs with
  | nil => simp [reference]
  | cons x xs ih => simp [reference, List.pairwise_cons, ih, law]

/-- Adjacent checks characterize chains even when the relation is not transitive. -/
theorem adjacent_correct (law : ∀ x y, cmp x y = true ↔ R x y) (xs : List α) :
    adjacent cmp xs = true ↔ xs.IsChain R := by
  induction xs with
  | nil => simp [adjacent]
  | cons x xs ih =>
    cases xs with
    | nil => simp [adjacent]
    | cons y ys => simp [adjacent, List.isChain_cons_cons, law, ih]

/-- Only the refinement needs transitivity. -/
theorem refinement [IsTrans α R]
    (law : ∀ x y, cmp x y = true ↔ R x y) (xs : List α) :
    adjacent cmp xs = reference cmp xs := by
  apply Bool.eq_iff_iff.mpr
  rw [adjacent_correct law, reference_correct law, List.isChain_iff_pairwise]

/-- The algorithm replacement is a shared square, available to any consumer. -/
def checkerSquare [IsTrans α R]
    (law : ∀ x y, cmp x y = true ↔ R x y) :
    Squares.Square (exact (List α)) (exact Bool) where
  impl := adjacent cmp
  spec := reference cmp
  commutes := refinement law

/-- A consumer releases the certificate's length only after acceptance. -/
def release (input : List α × Bool) : Option Nat :=
  if input.2 then some input.1.length else none

def releaseSquare : Squares.Square (Squares.product (exact (List α)) (exact Bool))
    (exact (Option Nat)) where
  impl := release
  spec := release
  commutes _ := rfl

/-- Pairing retains the input for the consumer; composition transports refinement. -/
def checkedLengthSquare [IsTrans α R]
    (law : ∀ x y, cmp x y = true ↔ R x y) :
    Squares.Square (exact (List α)) (exact (Option Nat)) :=
  Squares.compose releaseSquare
    (Squares.pair (Squares.identity _) (checkerSquare law))

/-- The composed consumer has no acceptance hypothesis hidden in its interface. -/
theorem checkedLength_correct [IsTrans α R]
    (law : ∀ x y, cmp x y = true ↔ R x y) (xs : List α) :
    (checkedLengthSquare law).impl xs = some xs.length ↔ xs.Pairwise R := by
  have h := (checkedLengthSquare law).commutes xs
  change (checkedLengthSquare law).impl xs = release (xs, reference cmp xs) at h
  rw [h]
  cases hcheck : reference cmp xs <;> simp [release, hcheck, ← reference_correct law]
  rfl

end OrderCertificate
