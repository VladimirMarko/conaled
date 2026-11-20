import Applications.Resources.RedBlackWorkload
import Examples.RedBlackHistory

/-!
# Priced operations and actual chronological histories

The prices below separate comparison calls from comparator work. The growing
integer families use their actual returned trees and sizes. The finite history
reuses the accepted four writes, including its repeated key and negative key.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.RedBlackWorkloads

open Resources Resources.RedBlack
open Representations.SignedComparison
open Search.RedBlack (Tree)

universe u

private def prices : Metric → Nat
  | .visits => 2
  | .comparisons => 3
  | .comparatorWork => 5
  | .nodeConstructions => 7
  | .terminalNils => 11
  | .rootInspections => 13
  | _ => 0

private def singleton : Tree Int Nat := .node .black .nil (0, 0) .nil

private theorem singleton_shape : Search.RedBlack.RB singleton .red 1 :=
  Search.RedBlack.RB.black .red 0 0
    (Search.RedBlack.RB.nil .black) (Search.RedBlack.RB.nil .black)

/-- Zero prices give zero even when the operations have nonzero observations. -/
theorem zero_prices :
    weighted (fun _ => 0) (lookupRun (unitComparator intLtb) 0 singleton).2 = 0 ∧
    weighted (fun _ => 0) (insertRun (unitComparator intLtb) 0 1 singleton).2 = 0 := by
  constructor <;> rw [weighted_eq] <;> simp

theorem small_lookup_prices :
    weighted prices (lookupRun (unitComparator intLtb) 0 (.nil : Tree Int Nat)).2 = 11 ∧
    weighted prices (lookupRun (unitComparator intLtb) 0 singleton).2 = 18 := by
  constructor
  · rw [weighted_eq, lookupRun_nil]
    rfl
  · rw [weighted_eq, singleton, lookupRun_node]
    rfl

theorem small_insert_prices :
    weighted prices (insertRun (unitComparator intLtb) 0 1 (.nil : Tree Int Nat)).2 = 38 ∧
    weighted prices (insertRun (unitComparator intLtb) 0 1 singleton).2 = 45 := by
  constructor
  · rw [weighted_eq, insertRun_cost, insRun_nil]
    rfl
  · rw [weighted_eq, insertRun_cost, singleton, insRun_node]
    rfl

/-- The logarithm is taken after adding one to the actual tree size. -/
theorem small_size_logarithms :
    ((.nil : Tree Int Nat).size + 1).log2 = 0 ∧ (singleton.size + 1).log2 = 1 := by
  decide

/-- At the empty input the height term vanishes; the terminal costs remain. -/
theorem empty_log_bounds :
    weighted prices (lookupRun (unitComparator intLtb) 0 (.nil : Tree Int Nat)).2 ≤ 11 ∧
    weighted prices (insertRun (unitComparator intLtb) 0 1 (.nil : Tree Int Nat)).2 ≤ 38 := by
  constructor
  · exact lookupRun_weighted_log prices (unitComparator intLtb) 0 .nil 1
      (unitComparator_localBound intLtb 0 .nil) (Search.RedBlack.RB.nil .red)
  · exact insertRun_weighted_log prices (unitComparator intLtb) 0 1 .nil 1
      (unitComparator_localBound intLtb 0 .nil) (Search.RedBlack.RB.nil .red)

/-- The singleton has log2(size+1)=1; these bounds use its actual shape proof. -/
theorem singleton_log_bounds :
    weighted prices (lookupRun (unitComparator intLtb) 0 singleton).2 ≤ 47 ∧
    weighted prices (insertRun (unitComparator intLtb) 0 1 singleton).2 ≤ 116 := by
  constructor
  · exact lookupRun_weighted_log prices (unitComparator intLtb) 0 singleton 1
      (unitComparator_localBound intLtb 0 singleton) singleton_shape
  · exact insertRun_weighted_log prices (unitComparator intLtb) 0 1 singleton 1
      (unitComparator_localBound intLtb 0 singleton) singleton_shape

/-- Index i builds the chronological integer keys 0 through i-1 with payload one. -/
private def integerPrefix (i : Nat) : Tree Int Nat :=
  (buildKeysRun (unitComparator intLtb) ((List.range i).map (fun key => (key : Int)))).1

private theorem integerPrefix_shape (i : Nat) :
    ∃ n, Search.RedBlack.RB (integerPrefix i) .red n :=
  buildRun_shape (unitComparator intLtb) _ ⟨0, Search.RedBlack.RB.nil .red⟩

/-- A concrete growing-key family keeps its actual size function in the majorant. -/
theorem growing_lookup_unit_family :
    Asymptotics.IsBigO Filter.atTop
      (fun i : Nat => (weighted prices
        (lookupRun (unitComparator intLtb) (i : Int) (integerPrefix i)).2 : ℝ))
      (fun i : Nat => ((1 + ((integerPrefix i).size + 1).log2 : Nat) : ℝ)) :=
  lookup_unit_family_isBigO prices intLtb (fun i => (i : Int)) integerPrefix integerPrefix_shape

theorem growing_insert_unit_family :
    Asymptotics.IsBigO Filter.atTop
      (fun i : Nat => (weighted prices
        (insertRun (unitComparator intLtb) (i : Int) (i + 1) (integerPrefix i)).2 : ℝ))
      (fun i : Nat => ((1 + ((integerPrefix i).size + 1).log2 : Nat) : ℝ)) :=
  insert_unit_family_isBigO prices intLtb (fun i => (i : Int)) (fun i => i + 1)
    integerPrefix integerPrefix_shape

private def varyingComparator (i : Nat) (a b : Int) : Measured Bool Nat :=
  (intLtb a b, i + 1)

private theorem varying_localBound (i : Nat) :
    Search.RedBlack.ForallT
      (fun old _ => (varyingComparator i (i : Int) old).2 ≤ i + 1 ∧
        (varyingComparator i old (i : Int)).2 ≤ i + 1) (integerPrefix i) := by
  apply (Search.RedBlack.forallT_elements_iff _ _).mpr
  intro _ _
  exact ⟨Nat.le_refl _, Nat.le_refl _⟩

/-- Work i+1 is actually returned by every comparator call in this family. -/
theorem growing_lookup_varying_family :
    Asymptotics.IsBigO Filter.atTop
      (fun i : Nat => (weighted prices
        (lookupRun (varyingComparator i) (i : Int) (integerPrefix i)).2 : ℝ))
      (fun i : Nat => (((1 + (i + 1)) * (1 + ((integerPrefix i).size + 1).log2) : Nat) : ℝ)) :=
  lookup_variable_family_isBigO prices varyingComparator (fun i => (i : Int)) integerPrefix
    (fun i => i + 1) varying_localBound integerPrefix_shape

theorem growing_insert_varying_family :
    Asymptotics.IsBigO Filter.atTop
      (fun i : Nat => (weighted prices
        (insertRun (varyingComparator i) (i : Int) (i + 1) (integerPrefix i)).2 : ℝ))
      (fun i : Nat => (((1 + (i + 1)) * (1 + ((integerPrefix i).size + 1).log2) : Nat) : ℝ)) :=
  insert_variable_family_isBigO prices varyingComparator (fun i => (i : Int)) (fun i => i + 1)
    integerPrefix (fun i => i + 1) varying_localBound integerPrefix_shape

/-- Nonzero comparator pricing retains its varying work even on a fixed shape. -/
theorem varying_singleton_lookup (i : Nat) :
    weighted prices (lookupRun (varyingComparator i) 0 singleton).2 = 8 + 10 * (i + 1) := by
  rw [weighted_eq, singleton, lookupRun_node]
  norm_num [varyingComparator, intLtb, comparisonRun_cost, prices, tick, Pi.add_apply]
  omega

theorem varying_singleton_insert (i : Nat) :
    weighted prices (insertRun (varyingComparator i) 0 1 singleton).2 = 35 + 10 * (i + 1) := by
  rw [weighted_eq, insertRun_cost, singleton, insRun_node]
  norm_num [varyingComparator, intLtb, comparisonRun_cost, prices, tick, Pi.add_apply]
  omega

/-- Execute the accepted four-write history, retaining both its value and vector. -/
def history : Measured (Tree Int Nat) Cost :=
  buildRun (unitComparator intLtb) Examples.RedBlackHistory.writes .nil

theorem history_value : history.1 = Examples.RedBlackHistory.balanced :=
  buildRun_value (unitComparator intLtb) Examples.RedBlackHistory.writes .nil

theorem history_prefix_sizes :
    (prefixTrees intLtb Examples.RedBlackHistory.writes (.nil : Tree Int Nat)).map
      RBTree.RBNode.size = [0, 1, 2, 2, 3] := rfl

/-- The third write changes the payload without increasing the actual size. -/
theorem history_prefix_values :
    (prefixTrees intLtb Examples.RedBlackHistory.writes (.nil : Tree Int Nat)).map
      (Search.RedBlack.lookup? intLtb 3) = [none, some 303, some 303, some 333, some 333] := rfl

theorem history_step_constructions :
    (stepCosts (unitComparator intLtb) Examples.RedBlackHistory.writes (.nil : Tree Int Nat)).map
      (fun cost => cost .nodeConstructions) = [2, 3, 2, 6] := rfl

/-- Every coordinate is checked, including the absent enumeration coordinates. -/
theorem history_cost : history.2 = fun
    | .visits => 4
    | .comparisons => 5
    | .comparatorWork => 5
    | .balanceCalls => 3
    | .patternAttempts => 8
    | .datatypeObservations => 15
    | .nodeConstructions => 13
    | .terminalNils => 3
    | .rootInspections => 4
    | .enumerationCalls => 0
    | .consConstructions => 0 := by
  funext metric
  cases metric <;> rfl

theorem history_step_prices :
    ((stepCosts (unitComparator intLtb) Examples.RedBlackHistory.writes
      (.nil : Tree Int Nat)).map (weighted prices)) = [38, 55, 45, 86] := by
  simp only [stepCosts, prefixTrees, Examples.RedBlackHistory.writes, List.scanl_cons,
    List.scanl_nil, List.zip_cons_cons, List.zip_nil_left, List.map_cons, List.map_nil,
    weighted_eq]
  rfl

/-- Reuse the general actual-prefix sum theorem to recover the independent total. -/
theorem history_weighted : weighted prices history.2 = 224 := by
  rw [history, buildRun_weighted_cost, history_step_prices]
  rfl

/-- The bound uses preceding sizes 0,1,2,2, including the replacement step. -/
theorem history_weighted_log_budget : weighted prices history.2 ≤ 386 := by
  exact buildRun_weighted_log_sum prices (unitComparator intLtb)
    Examples.RedBlackHistory.writes (.nil : Tree Int Nat) (fun _ _ => 1)
    (fun entry _ => unitComparator_localBound intLtb entry.1.1 entry.2)
    ⟨0, Search.RedBlack.RB.nil .red⟩

theorem history_prefix_invariants :
    (∀ state ∈ prefixTrees intLtb Examples.RedBlackHistory.writes (.nil : Tree Int Nat),
      Search.RedBlack.BST id state) ∧
    (∀ state ∈ prefixTrees intLtb Examples.RedBlackHistory.writes (.nil : Tree Int Nat),
      ∃ n, Search.RedBlack.RB state .red n) :=
  ⟨prefixTrees_bst id intLtb intLtb_true_iff Examples.RedBlackHistory.writes
      (Search.RedBlack.bst_nil id),
    prefixTrees_shape intLtb Examples.RedBlackHistory.writes
      ⟨0, Search.RedBlack.RB.nil .red⟩⟩

theorem history_heights_and_bindings :
    Search.RedBlack.height history.1 = 2 ∧
    Examples.RedBlackHistory.ordinary.height = 3 ∧
    Search.RedBlack.elements history.1 = [(-2, 202), (1, 101), (3, 333)] ∧
    Search.RedBlack.elements history.1 =
      Search.OrderedMap.DecodedKeys.elements Examples.RedBlackHistory.ordinary := by
  rw [history_value]
  exact ⟨Examples.RedBlackHistory.balanced_height, Examples.RedBlackHistory.ordinary_height,
    Examples.RedBlackHistory.balanced_elements, Examples.RedBlackHistory.history_elements_agree⟩

theorem history_complete_meaning :
    Search.RedBlack.enumAbs id intLtb int_decode_injective intLtb_true_iff history.1 =
      Search.OrderedMap.DecodedKeys.enumAbs id intLtb int_decode_injective intLtb_true_iff
        Examples.RedBlackHistory.ordinary := by
  have same := buildRun_meaning_agrees id (unitComparator intLtb) intLtb (fun _ _ => rfl)
    int_decode_injective intLtb_true_iff 0 Examples.RedBlackHistory.writes
  rw [DecodedSearchTreeWorkload.buildRun_value] at same
  exact same

/-- The measured history agrees with the ordinary history for every optional query. -/
theorem history_all_queries (query : Int) :
    (lookupRun (unitComparator intLtb) query history.1).1 =
      Search.OrderedMap.DecodedKeys.lookup? intLtb query Examples.RedBlackHistory.ordinary := by
  rw [lookupRun_value]
  have same := buildRun_lookup_agrees id (unitComparator intLtb) intLtb (fun _ _ => rfl)
    int_decode_injective intLtb_true_iff 0 Examples.RedBlackHistory.writes query
  rw [DecodedSearchTreeWorkload.buildRun_value] at same
  exact same

theorem history_optional_queries :
    ([-2, 1, 2, 3] : List Int).map
      (fun query => (lookupRun (unitComparator intLtb) query history.1).1) =
      [some 202, some 101, none, some 333] := by
  simp only [history_all_queries]
  exact Examples.RedBlackHistory.ordinary_queries

/-- The source hit counter tests payload one, so these present payloads do not count. -/
theorem history_query_phase :
    (queryRun (unitComparator intLtb) [-2, 1, 2, 3] history.1).1 = 0 ∧
    weighted prices (queryRun (unitComparator intLtb) [-2, 1, 2, 3] history.1).2 = 121 := by
  constructor
  · rfl
  · rw [queryRun_weighted_cost, history_value]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, weighted_eq]
    rfl

theorem history_query_log_budget :
    weighted prices (queryRun (unitComparator intLtb) [-2, 1, 2, 3] history.1).2 ≤ 332 := by
  rw [history_value]
  exact queryRun_weighted_log_sum prices (unitComparator intLtb) [-2, 1, 2, 3]
    Examples.RedBlackHistory.balanced (fun _ => 1)
    (fun query _ => unitComparator_localBound intLtb query Examples.RedBlackHistory.balanced)
    Examples.RedBlackHistory.balanced_rb

/-- Only enumeration calls and cons operations are priced here; the suffix is untouched. -/
theorem history_enumeration_price :
    weighted (fun metric => match metric with
      | .enumerationCalls => 2
      | .consConstructions => 3
      | _ => 0) (elementsAuxRun history.1 [(99, 0)]).2 = 23 := by
  rw [elementsAuxRun_weighted, history_value]
  rfl

/-- Repeated writes can carry independently larger payload universes. -/
theorem type_payload_history (first last : Type u) :
    (buildRun (unitComparator intLtb) [(0, first), (0, last)]
      (.nil : Tree Int (Type u))).1 = .node .black .nil (0, last) .nil := by
  rw [buildRun_value]
  rfl

theorem source_empty : sourceRun (unitComparator intLtb) [] [] = (0, 0) := rfl

theorem source_empty_misses :
    (sourceRun (unitComparator intLtb) [] [-1, 0, 1]).1 = 0 ∧
    (sourceRun (unitComparator intLtb) [] [-1, 0, 1]).2 .terminalNils = 3 := ⟨rfl, rfl⟩

theorem source_all_hit :
    (sourceRun (unitComparator intLtb) [3, 1, 3, -2] [3, -2, 1, 3]).1 = 4 := by
  have counted := sourceRun_independent_count id (unitComparator intLtb) intLtb
    (fun _ _ => rfl) int_decode_injective intLtb_true_iff [3, 1, 3, -2] [3, -2, 1, 3]
  norm_num [Search.OrderedMap.Workload.expectedHits] at counted
  exact counted

theorem source_mixed_queries :
    (sourceRun (unitComparator intLtb) [3, 1, 3, -2] [-2, 0, 3, 4, 3]).1 = 3 := by
  have counted := sourceRun_independent_count id (unitComparator intLtb) intLtb
    (fun _ _ => rfl) int_decode_injective intLtb_true_iff [3, 1, 3, -2] [-2, 0, 3, 4, 3]
  norm_num [Search.OrderedMap.Workload.expectedHits] at counted
  exact counted

/-- The two measured phases price the actual tree returned by source construction. -/
theorem source_priced_phases :
    weighted prices (buildKeysRun (unitComparator intLtb) [3, 1, 3, -2]).2 = 224 ∧
    weighted prices (queryRun (unitComparator intLtb) [-2, 0, 3, 4, 3]
      (buildKeysRun (unitComparator intLtb) [3, 1, 3, -2]).1).2 = 186 ∧
    weighted prices (sourceRun (unitComparator intLtb) [3, 1, 3, -2] [-2, 0, 3, 4, 3]).2 = 410 := by
  have built : weighted prices (buildKeysRun (unitComparator intLtb) [3, 1, 3, -2]).2 = 224 := by
    rw [weighted_eq]
    rfl
  have queried : weighted prices (queryRun (unitComparator intLtb) [-2, 0, 3, 4, 3]
      (buildKeysRun (unitComparator intLtb) [3, 1, 3, -2]).1).2 = 186 := by
    rw [weighted_eq]
    rfl
  refine ⟨built, queried, ?_⟩
  rw [sourceRun_weighted, built, queried]

theorem source_repeated_size :
    (buildKeysRun (unitComparator intLtb) [3, 1, 3, -2]).1.size = 3 := rfl

theorem source_indices_four :
    Search.OrderedMap.Workload.sourceIndices 4 = [4, 3, 2, 1] ∧
    (sourceRun (unitComparator (fun a b : Nat => decide (a < b)))
      ((Search.OrderedMap.Workload.sourceIndices 4).map (fun j => 4 - j))
      ((Search.OrderedMap.Workload.sourceIndices 4).map (fun j => 4 - j))).1 = 4 := by
  constructor
  · rfl
  · rw [sourceRun_consecutive_schedule]
    rfl

/-- This bounded signed carrier permits repetition; no unbounded-size claim is made. -/
theorem signed_source_endpoints :
    (sourceRun (unitComparator wordLtb)
      [BitVec.ofInt 4 (-8), BitVec.ofInt 4 7, BitVec.ofInt 4 (-8)]
      [BitVec.ofInt 4 (-8), BitVec.ofInt 4 0, BitVec.ofInt 4 7, BitVec.ofInt 4 7]).1 = 3 ∧
    (buildKeysRun (unitComparator wordLtb)
      [BitVec.ofInt 4 (-8), BitVec.ofInt 4 7, BitVec.ofInt 4 (-8)]).1.size = 2 := ⟨rfl, rfl⟩

end Examples.RedBlackWorkloads
