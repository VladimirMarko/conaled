import Applications.Resources.RedBlack
import Applications.Representations.SignedComparison

/-!
# Connected source-operation cost cases

Left descent makes one comparison, while right descent and equality make two.
The cases distinguish those calls from comparator work and optional presence
from a stored default. Accumulator counts do not depend on the supplied suffix.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.RedBlackWork

open Resources Resources.RedBlack
open Representations.SignedComparison
open Search.RedBlack (Tree)

universe u v

private def singleton : Tree Int Nat := .node .black .nil (0, 0) .nil

/-- A completely arbitrary payload type requires no default to count a failed search. -/
theorem empty_lookup {κ : Type u} {ν : Type v}
    (cmp : κ → κ → Measured Bool Nat) (query : κ) :
    lookupRun cmp query (.nil : Tree κ ν) = (none, tick .terminalNils 1) :=
  lookupRun_nil cmp query

/-- Query -1 reaches the left nil after exactly one test against zero. -/
theorem singleton_left_miss :
    (lookupRun (unitComparator intLtb) (-1) singleton).1 = none ∧
    (lookupRun (unitComparator intLtb) (-1) singleton).2 .visits = 1 ∧
    (lookupRun (unitComparator intLtb) (-1) singleton).2 .comparisons = 1 ∧
    (lookupRun (unitComparator intLtb) (-1) singleton).2 .comparatorWork = 1 ∧
    (lookupRun (unitComparator intLtb) (-1) singleton).2 .terminalNils = 1 := by
  rw [singleton, lookupRun_node]
  norm_num [unitComparator, intLtb, comparisonRun_cost, tick, Pi.add_apply]

/-- Query 1 needs both source tests before reaching the right nil. -/
theorem singleton_right_miss :
    (lookupRun (unitComparator intLtb) 1 singleton).1 = none ∧
    (lookupRun (unitComparator intLtb) 1 singleton).2 .visits = 1 ∧
    (lookupRun (unitComparator intLtb) 1 singleton).2 .comparisons = 2 ∧
    (lookupRun (unitComparator intLtb) 1 singleton).2 .comparatorWork = 2 ∧
    (lookupRun (unitComparator intLtb) 1 singleton).2 .terminalNils = 1 := by
  rw [singleton, lookupRun_node]
  norm_num [unitComparator, intLtb, comparisonRun_cost, tick, Pi.add_apply]

/-- Stored zero is present, and equality returns before any nil call. -/
theorem singleton_stored_default :
    (lookupRun (unitComparator intLtb) 0 singleton).1 = some 0 ∧
    (lookupRun (unitComparator intLtb) 0 singleton).2 .comparisons = 2 ∧
    (lookupRun (unitComparator intLtb) 0 singleton).2 .terminalNils = 0 := by
  rw [singleton, lookupRun_node]
  norm_num [unitComparator, intLtb, comparisonRun_cost, tick, Pi.add_apply]

/-- Keys can stay small while the payload universe is arbitrarily large. -/
theorem higher_payload_universe (payload : Type u) :
    (lookupRun (unitComparator intLtb) 0
      (.node .black .nil (0, payload) .nil : Tree Int (Type u))).1 = some payload := by
  rw [lookupRun_value]
  rfl

private def asymmetricWork (a b : Int) : Measured Bool Nat :=
  (intLtb a b, a.natAbs + 1)

/-- The two calls have respective work 2 and 1, separate from the call count 2. -/
theorem comparator_work_is_separate :
    (lookupRun asymmetricWork 1 singleton).2 .comparisons = 2 ∧
    (lookupRun asymmetricWork 1 singleton).2 .comparatorWork = 3 := by
  rw [singleton, lookupRun_node]
  norm_num [asymmetricWork, intLtb, comparisonRun_cost, tick, Pi.add_apply]

/-- Only the two orientations against the actual stored key need a local bound. -/
theorem finite_input_comparator_bound :
    (lookupRun asymmetricWork 1 singleton).2 .comparatorWork ≤
      2 * 2 * Search.RedBlack.height singleton := by
  apply lookupRun_comparatorWork_le_height
  norm_num [singleton, Search.RedBlack.ForallT, RBTree.RBNode.All, asymmetricWork]

/-- A zero-priced comparator can still perform two abstract Boolean invocations. -/
theorem zero_work_comparisons :
    (lookupRun (fun a b : Int => (intLtb a b, 0)) 1 singleton).2 .comparisons = 2 ∧
    (lookupRun (fun a b : Int => (intLtb a b, 0)) 1 singleton).2 .comparatorWork = 0 := by
  rw [singleton, lookupRun_node]
  norm_num [intLtb, comparisonRun_cost, tick, Pi.add_apply]

private def rawTwo : Tree Int Nat :=
  .node .red (.node .black .nil (7, 70) .nil) (3, 30) .nil

/-- In-order enumeration also works on this incorrectly ordered raw tree. -/
theorem nonempty_suffix :
    (elementsAuxRun rawTwo [(99, 90)]).1 = [(7, 70), (3, 30), (99, 90)] ∧
    (elementsAuxRun rawTwo [(99, 90)]).2 .enumerationCalls = 5 ∧
    (elementsAuxRun rawTwo [(99, 90)]).2 .consConstructions = 2 ∧
    (elementsAuxRun rawTwo [(99, 90)]).2 = (elementsRun rawTwo).2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [elementsAuxRun_value]
    rfl
  · rw [elementsAuxRun_enumerationCalls]
    rfl
  · rw [elementsAuxRun_consConstructions]
    rfl
  · exact elementsAuxRun_cost_independent rawTwo [(99, 90)] []

/-- Even an already-black node incurs the declared syntactic root reconstruction. -/
theorem already_black_reconstruction :
    makeBlackRun singleton =
      (singleton, tick .rootInspections 1 + tick .nodeConstructions 1) :=
  makeBlackRun_node .black .nil (0, 0) .nil

/-- Empty insertion constructs the red leaf and then its black root, without comparisons. -/
theorem empty_insert_counts :
    (insertRun (unitComparator intLtb) 0 7 (.nil : Tree Int Nat)).1 =
      .node .black .nil (0, 7) .nil ∧
    (insertRun (unitComparator intLtb) 0 7 (.nil : Tree Int Nat)).2 .visits = 0 ∧
    (insertRun (unitComparator intLtb) 0 7 (.nil : Tree Int Nat)).2 .comparisons = 0 ∧
    (insertRun (unitComparator intLtb) 0 7 (.nil : Tree Int Nat)).2 .balanceCalls = 0 ∧
    (insertRun (unitComparator intLtb) 0 7 (.nil : Tree Int Nat)).2 .nodeConstructions = 2 ∧
    (insertRun (unitComparator intLtb) 0 7 (.nil : Tree Int Nat)).2 .terminalNils = 1 ∧
    (insertRun (unitComparator intLtb) 0 7 (.nil : Tree Int Nat)).2 .rootInspections = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [insertRun_value]
    rfl
  all_goals simp only [insertRun_cost, insRun_nil]; rfl

/-- Replacing the stored key does not balance or reach nil, but still reconstructs twice. -/
theorem replacement_counts :
    (insertRun (unitComparator intLtb) 0 9 singleton).1 =
      .node .black .nil (0, 9) .nil ∧
    (insertRun (unitComparator intLtb) 0 9 singleton).2 .visits = 1 ∧
    (insertRun (unitComparator intLtb) 0 9 singleton).2 .comparisons = 2 ∧
    (insertRun (unitComparator intLtb) 0 9 singleton).2 .balanceCalls = 0 ∧
    (insertRun (unitComparator intLtb) 0 9 singleton).2 .nodeConstructions = 2 ∧
    (insertRun (unitComparator intLtb) 0 9 singleton).2 .terminalNils = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [insertRun_value]
    rfl
  all_goals simp only [insertRun_cost, singleton, insRun_node]; rfl

private def twoIncreasing : Tree Int Nat :=
  .node .black .nil (0, 10) (.node .red .nil (1, 11) .nil)

/-- Inserting two descends twice and rotates the actual returned subtree. -/
theorem right_rotation_result :
    (insertRun (unitComparator intLtb) 2 22 twoIncreasing).1 =
      .node .black (.node .black .nil (0, 10) .nil) (1, 11)
        (.node .black .nil (2, 22) .nil) := by
  rw [insertRun_value]
  rfl

/-- The red unwind costs P1/D1/A1; the black RR unwind costs P5/D10/A3. -/
theorem right_rotation_counts :
    (insertRun (unitComparator intLtb) 2 22 twoIncreasing).2 .visits = 2 ∧
    (insertRun (unitComparator intLtb) 2 22 twoIncreasing).2 .comparisons = 4 ∧
    (insertRun (unitComparator intLtb) 2 22 twoIncreasing).2 .balanceCalls = 2 ∧
    (insertRun (unitComparator intLtb) 2 22 twoIncreasing).2 .patternAttempts = 6 ∧
    (insertRun (unitComparator intLtb) 2 22 twoIncreasing).2 .datatypeObservations = 11 ∧
    (insertRun (unitComparator intLtb) 2 22 twoIncreasing).2 .nodeConstructions = 6 ∧
    (insertRun (unitComparator intLtb) 2 22 twoIncreasing).2 .rootInspections = 1 := by
  simp only [insertRun_cost, twoIncreasing, insRun_node]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The general construction bound uses input height two; the actual count above is six. -/
theorem right_rotation_height_budget :
    (insertRun (unitComparator intLtb) 2 22 twoIncreasing).2 .nodeConstructions ≤ 8 :=
  insertRun_nodeConstructions_le_height (unitComparator intLtb) 2 22 twoIncreasing

/-- The measured insertion retains independently large payload universes. -/
theorem insert_higher_payload_universe (payload : Type u) :
    (insertRun (unitComparator intLtb) (-2) payload (.nil : Tree Int (Type u))).1 =
      .node .black .nil (-2, payload) .nil := by
  rw [insertRun_value]
  rfl

private def signedFourBit : Tree (BitVec 4) Nat :=
  .node .black (.node .red .nil (BitVec.ofInt 4 (-8), 80) .nil)
    (BitVec.ofInt 4 0, 0) (.node .red .nil (BitVec.ofInt 4 7, 70) .nil)

/-- Signed minimum follows the left branch and then equality: three calls, two visits. -/
theorem signed_minimum_path :
    (lookupRun (unitComparator wordLtb) (BitVec.ofInt 4 (-8)) signedFourBit).1 = some 80 ∧
    (lookupRun (unitComparator wordLtb) (BitVec.ofInt 4 (-8)) signedFourBit).2 .visits = 2 ∧
    (lookupRun (unitComparator wordLtb) (BitVec.ofInt 4 (-8)) signedFourBit).2 .comparisons = 3 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [lookupRun_value]
    rfl
  all_goals simp only [signedFourBit, lookupRun_node]; rfl

/-- The same signed maximum follows right then equality, so it needs four calls. -/
theorem signed_maximum_path :
    (lookupRun (unitComparator wordLtb) (BitVec.ofInt 4 7) signedFourBit).1 = some 70 ∧
    (lookupRun (unitComparator wordLtb) (BitVec.ofInt 4 7) signedFourBit).2 .visits = 2 ∧
    (lookupRun (unitComparator wordLtb) (BitVec.ofInt 4 7) signedFourBit).2 .comparisons = 4 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [lookupRun_value]
    rfl
  all_goals simp only [signedFourBit, lookupRun_node]; rfl

end Examples.RedBlackWork
