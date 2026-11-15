import SquareKit.TrackedRecursionAssembly
import SquareKit.TrackedRecursionSeparation
import Applications.OracleComputation.Compilation

/-! Public positive and separating clients of the bounded multivalued recursion theorem. -/
namespace Examples.TrackedRecursion
open Realizability Realizability.TrackedRecursion
open Nat.Partrec (Code)

/-- The same multivalued relation has two total, observationally distinct fixed points. -/
example : ∃ p q : Computation,
    PrefixRelation p p ∧ PrefixRelation q q ∧ p ≠ q ∧
    (∀ n, p.val n = Part.some 0) ∧ (∀ n, q.val n = Part.some 1) :=
  prefixRelation_two_fixed

example : ∃ c : Code, PrefixRelation (represented c) (represented c) :=
  realized_code_exists PrefixRelation (prefixCode 0) (prefixCode_computable 0)
    prefixRelation_zero_realizes

/-- Both independently supplied choices really realize the same relation. -/
example : ∃ p, PrefixRelation p p :=
  realized_recursion PrefixRelation (prefixCode 1) (prefixCode_computable 1)
    prefixRelation_one_realizes

example (p : Computation) : prepend 0 p ≠ prepend 1 p := prefix_outputs_distinct p
example : prepend 0 (constant 1) ≠ constant 1 := prefix_changes 0 1 (by decide)
example : prepend 1 (constant 0) ≠ constant 0 := prefix_changes 1 0 (by decide)

/-- Prefixing preserves divergence in the tail instead of forcing it at zero. -/
example (c : Code) (h : c.eval 7 = Part.none) :
    (prefixCode 1 c).eval 0 = Part.some 1 ∧ (prefixCode 1 c).eval 8 = Part.none := by
  constructor
  · exact prefixCode_zero 1 c
  · simpa using (prefixCode_succ 1 c 7).trans h

/-- The divergence premise above has an actual represented inhabitant. -/
example : ∃ c : Code, (∀ n, c.eval n = Part.none) ∧
    (prefixCode 1 c).eval 0 = Part.some 1 ∧ (prefixCode 1 c).eval 8 = Part.none := by
  obtain ⟨c, hc⟩ := Code.exists_code.mp Nat.Partrec.none
  refine ⟨c, fun n => congrFun hc n, prefixCode_zero 1 c, ?_⟩
  simpa only [hc] using prefixCode_succ 1 c 7

example : Nonempty (SquareKit.DiagonalConstruction.Selected row (prepend 0)) := by
  apply selected_endomap
  simpa only [represented_prefixCode, diagonalCode, row] using
    uniform_of_generator (fun n => prefixCode 0 (diagonalCode n))
      ((prefixCode_computable 0).comp diagonalCode_computable)

example (k : Nat) : ∃ h : Assembly.Hom (Assembly.encoded Nat) computationAssembly,
    h.toFun = row k := uniform_tracked (row_uniform k)

example (a : Nat → Computation) : Uniform a ↔
    ∃ h : Assembly.Hom (Assembly.encoded Nat) computationAssembly, h.toFun = a :=
  uniform_iff_tracked a

example (b n : Nat) : computationEvaluation.toFun (constant b, n) = some b := by
  classical
  change ((constant b).val n).toOption = some b
  exact Part.toOption_eq_some_iff.mpr (by simp)

example : computationEvaluation = computationPartialMap.classify :=
  computationEvaluation_classifies

example : (∀ p, ∃ q, AvoidRelation p q) ∧ ¬ (∃ p, AvoidRelation p p) :=
  ⟨avoidRelation_serial, avoidRelation_no_fixed⟩

example : ¬ ∃ F : Code → Code,
    Computable F ∧ ∀ c, AvoidRelation (represented c) (represented (F c)) :=
  avoidRelation_no_realizer

example : ¬ Uniform (fun n => avoid (row n n)) := avoid_diagonal_not_uniform
example : ¬ Function.Surjective row := row_not_surjective

example : ¬ ∃ h : Assembly.Hom (Assembly.encoded Nat) computationAssembly,
    h.toFun = fun n => avoid (row n n) := by
  intro h
  exact avoid_diagonal_not_uniform ((uniform_iff_tracked _).mpr h)

/-- A code-sensitive companion from Mathlib, with existential code selection. -/
example : ∃ c : Code, ∀ n, c.eval n = Part.some (Encodable.encode c) := exists_self_code

/-- An oracle client enters this ordinary representation only with its implementation. -/
example (q : Code) (c : OracleComputation.Code) (b n : Nat) :
    (prefixCode b (OracleComputation.toOrdinary q c)).eval (n+1) =
      OracleComputation.eval q.eval c n := by
  rw [prefixCode_succ, OracleComputation.toOrdinary_correct]

end Examples.TrackedRecursion
