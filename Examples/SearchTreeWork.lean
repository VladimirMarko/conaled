import Applications.Resources.SearchTree
import Applications.Resources.TreeEnumeration
import Applications.Resources.UnaryComparison
import Applications.Search.SharedTree.Complete
import Examples.SearchTrees

/-!
# Connected clients of the SearchTree resource models

The observations below are named explicitly: nonempty search visits and strict
comparator calls; copied first-list cells for the two source appends; constructor
visits and cons cells for accumulator traversal; and lockstep constructor-pattern
calls for unary comparison. None of these numbers is wall-clock timing. Perfect
trees with repeated labels are enumeration examples, not a claimed BST family.
The increasing spine is the separate, genuinely ordered search family.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.SearchTreeWork

open Resources

universe u

/-- Empty payloads still permit empty search and traversal. -/
theorem empty_boundary :
    SearchTree.lookupRun 0 (.nil : BinaryTree (Nat × Empty)) = (none, (0, 0)) ∧
    SearchTree.lookupInspections 0 (.nil : BinaryTree (Nat × Empty)) = 1 ∧
    TreeEnumeration.copyRun (.nil : BinaryTree (Nat × Empty)) = ([], 0) ∧
    TreeEnumeration.accumulatorRun (.nil : BinaryTree (Nat × Empty)) [] = ([], (1, 0)) :=
  ⟨SearchTree.lookupRun_nil 0, SearchTree.lookupInspections_nil 0, TreeEnumeration.copyRun_nil,
    TreeEnumeration.accumulatorRun_nil []⟩

/-- A singleton copies its singleton append once. Accumulation visits both
empty children and the node, and builds just the one result cons. -/
theorem singleton_work {α : Type u} (a : α) (suffix : List α) :
    TreeEnumeration.copyRun (.node a .nil .nil) = ([a], 1) ∧
    TreeEnumeration.accumulatorRun (.node a .nil .nil) suffix = (a :: suffix, (3, 1)) := by
  constructor
  · simp [TreeEnumeration.copyRun_node]
  · simpa using TreeEnumeration.accumulatorRun_exact (.node a .nil .nil) suffix

/-- Independent payload universes need no payload equality, ordering or default. -/
theorem arbitrary_payload_erasure {ν : Type u} (value : ν) (key query : Nat)
    (tree : BinaryTree (Nat × ν)) :
    (SearchTree.insertRun key value tree).1 = Search.OrderedMap.bind key value tree ∧
    (SearchTree.lookupRun query tree).1 = Search.OrderedMap.lookup query tree :=
  ⟨SearchTree.insertRun_value key value tree, SearchTree.lookupRun_value query tree⟩

def three : BinaryTree (Nat × String) :=
  .node (1, "one") (.node (0, "zero") .nil .nil) (.node (2, "two") .nil .nil)

theorem three_ordered : Search.OrderedTree.OrderedBy Prod.fst three := by
  simp [three, Search.OrderedTree.OrderedBy, Search.OrderedTree.All]

theorem three_complete : Trees.Complete three := by
  simp [three, Trees.Complete]

/-- The left root decision short-circuits its reverse comparison. -/
theorem left_search : SearchTree.lookupRun 0 three = (some "zero", (2, 3)) := by
  simp [three, SearchTree.lookupRun_node]

/-- Both comparisons execute at the root and at the equal-key node. -/
theorem right_search : SearchTree.lookupRun 2 three = (some "two", (2, 4)) := by
  simp [three, SearchTree.lookupRun_node]

theorem root_search : SearchTree.lookupRun 1 three = (some "one", (1, 2)) := by
  simp [three, SearchTree.lookupRun_node]

theorem missing_search :
    SearchTree.lookupRun 3 three = (none, (2, 4)) ∧ SearchTree.lookupInspections 3 three = 3 := by
  constructor
  · simp [three, SearchTree.lookupRun_node]
  · simp [three, SearchTree.lookupInspections_node]

/-- Replacement rebuilds the selected left branch using the returned tree and
retains the right branch as a value; no heap-sharing claim is made. -/
theorem left_replacement :
    SearchTree.insertRun 0 "ZERO" three =
      (.node (1, "one") (.node (0, "ZERO") .nil .nil) (.node (2, "two") .nil .nil),
        (2, 3)) := by
  simp [three, SearchTree.insertRun_node]

theorem two_source_appends :
    TreeEnumeration.copyRun three = ([(0, "zero"), (1, "one"), (2, "two")], 4) := by
  simp [three, TreeEnumeration.copyRun_node]

/-- The arbitrary suffix is preserved in the returned value and contributes no
tree visits or cons charges to this traversal model. -/
theorem nonempty_accumulator :
    TreeEnumeration.accumulatorRun three [(9, "suffix")] =
      ([(0, "zero"), (1, "one"), (2, "two"), (9, "suffix")], (7, 3)) := by
  rw [TreeEnumeration.accumulatorRun_exact]
  rfl

theorem accumulator_source_agreement (suffix : List (Nat × String)) :
    (TreeEnumeration.accumulatorRun three suffix).1 = Search.OrderedMap.fastEntriesAcc three suffix :=
  TreeEnumeration.accumulatorRun_fastEntriesAcc three suffix

/-- A membership consumer transports through the public source erasure bridge. -/
theorem accumulator_contains_zero (suffix : List (Nat × String)) :
    (0, "zero") ∈ (TreeEnumeration.accumulatorRun three suffix).1 := by
  rw [TreeEnumeration.accumulatorRun_fastEntriesAcc, Search.OrderedMap.fastEntriesAcc_eq]
  exact List.mem_append_left _ (by simp [Search.OrderedTree.entries, three])

theorem contrasting_chains (n : Nat) :
    (TreeEnumeration.copyRun (Trees.leftChain "label" n)).2 = n * (n + 1) / 2 ∧
    (TreeEnumeration.copyRun (Trees.rightChain "label" n)).2 = n :=
  ⟨TreeEnumeration.leftChain_copies "label" n, TreeEnumeration.rightChain_copies "label" n⟩

theorem three_node_chain_counts :
    (TreeEnumeration.copyRun (Trees.leftChain "label" 3)).2 = 6 ∧
    (TreeEnumeration.copyRun (Trees.rightChain "label" 3)).2 = 3 := by
  simpa using contrasting_chains 3

/-- Reuse the existing complete value family; no second perfect-tree carrier
or recursion framework is introduced. -/
theorem completeValue_complete (h : Nat) :
    Trees.Complete (Search.SharedTree.completeValue "label" h) := by
  induction h with
  | zero => trivial
  | succ h ih => exact ⟨rfl, ih, ih⟩

theorem all_perfect_heights (h : Nat) :
    (Search.SharedTree.completeValue "label" h).numNodes = 2 ^ h - 1 ∧
    (TreeEnumeration.copyRun (Search.SharedTree.completeValue "label" h)).2 = h * 2 ^ (h - 1) := by
  constructor
  · simpa only [Search.SharedTree.completeValue_height] using
      TreeEnumeration.complete_numNodes _ (completeValue_complete h)
  · simpa only [Search.SharedTree.completeValue_height] using
      TreeEnumeration.complete_copies _ (completeValue_complete h)

theorem perfect_height_zero :
    (TreeEnumeration.copyRun (Search.SharedTree.completeValue "label" 0)).2 = 0 :=
  (all_perfect_heights 0).2

theorem perfect_height_three :
    (Search.SharedTree.completeValue "label" 3).numNodes = 7 ∧
    (TreeEnumeration.copyRun (Search.SharedTree.completeValue "label" 3)).2 = 12 := by
  simpa using all_perfect_heights 3

/-- The logarithmic-height premise is inhabited by the concrete perfect shape. -/
theorem three_logarithmic_copy_bound :
    (TreeEnumeration.copyRun three).2 ≤ three.numNodes * Nat.clog 2 (three.numNodes + 1) :=
  TreeEnumeration.almostComplete_copies three (Trees.complete_almostComplete three three_complete)

/-- Every height occurs in an ordered input that takes a linear search path. -/
theorem ordered_linear_family {ν : Type u} (value : ν) (n : Nat) :
    Search.OrderedTree.OrderedBy Prod.fst (SearchTree.rightSpine value 0 n) ∧
    (SearchTree.rightSpine value 0 n).numNodes = n ∧
    (SearchTree.rightSpine value 0 n).height = n ∧
    SearchTree.lookupRun n (SearchTree.rightSpine value 0 n) = (none, (n, 2 * n)) ∧
    SearchTree.lookupInspections n (SearchTree.rightSpine value 0 n) = n + 1 :=
  SearchTree.rightSpine_linear_path value n

theorem same_insertion_path {ν : Type u} (old new : ν) (n : Nat) :
    SearchTree.insertRun n new (SearchTree.rightSpine old 0 n) =
      (Search.OrderedMap.bind n new (SearchTree.rightSpine old 0 n), (n, 2 * n)) :=
  SearchTree.insertRun_rightSpine old new 0 n n (by omega)

/-- A comparator really charging seven units per call executes four calls. -/
theorem weighted_right_search :
    SearchTree.lookupWithRun (fun a b : Nat => (decide (a < b), 7)) 2 three =
      (some "two", (2, 28)) := by
  rw [SearchTree.lookupWithRun_constant, right_search]
  rfl

/-- The strict unary adapter runs its actual lockstep recursion at every tested
pair. Four comparator invocations account for eleven constructor-pattern calls. -/
theorem unary_right_search :
    SearchTree.lookupWithRun UnaryComparison.unaryLTRun 2 three = (some "two", (2, 11)) := by
  simp [three, SearchTree.lookupWithRun_node, UnaryComparison.unaryLTRun_spec]

theorem unary_local_bound : Search.OrderedTree.All
    (fun b : Nat × String => (UnaryComparison.unaryLTRun 2 b.1).2 ≤ 3 ∧
      (UnaryComparison.unaryLTRun b.1 2).2 ≤ 3) three := by
  simp [three, Search.OrderedTree.All, UnaryComparison.unaryLTRun_steps]

theorem unary_calibrated_erasure :
    (SearchTree.lookupWithRun UnaryComparison.unaryLTRun 2 three).1 = Search.OrderedMap.lookup 2 three := by
  apply SearchTree.lookupWithRun_value
  exact (Search.OrderedTree.all_iff _ _).2
    (fun _ _ => ⟨UnaryComparison.unaryLTRun_value _ _, UnaryComparison.unaryLTRun_value _ _⟩)

/-- The finite-input bound of three calls per comparator suffices even though
there is no global constant bound for the unary comparator on all Nat inputs. -/
theorem unary_weighted_height_bound :
    (SearchTree.lookupWithRun UnaryComparison.unaryLTRun 2 three).2.2 ≤ 12 := by
  simpa [three] using SearchTree.lookupWithRun_work_le_height UnaryComparison.unaryLTRun 2 three 3 unary_local_bound

theorem unary_conditional_log_bound :
    (SearchTree.lookupWithRun UnaryComparison.unaryLTRun 2 three).2.2 ≤
      6 * Nat.clog 2 (three.numNodes + 1) := by
  apply SearchTree.lookupWithRun_log_bound UnaryComparison.unaryLTRun 2 three 3 1 unary_local_bound
  simpa only [BinaryTree.numLeaves_eq_numNodes_succ, Nat.one_mul] using
    (Trees.height_eq_clog_numLeaves three
      (Trees.complete_almostComplete three three_complete)).le

theorem unary_zero_left : UnaryComparison.unaryLERun 0 7 = (true, 1) := by
  rw [UnaryComparison.unaryLERun_spec]
  rfl

theorem unary_zero_right : UnaryComparison.unaryLERun 7 0 = (false, 1) := by
  rw [UnaryComparison.unaryLERun_spec]
  rfl

theorem unary_equal_three : UnaryComparison.unaryLERun 3 3 = (true, 4) := by
  rw [UnaryComparison.unaryLERun_spec]
  rfl

theorem unary_less : UnaryComparison.unaryLERun 3 8 = (true, 4) := by
  rw [UnaryComparison.unaryLERun_spec]
  rfl

theorem unary_greater : UnaryComparison.unaryLERun 8 3 = (false, 4) := by
  rw [UnaryComparison.unaryLERun_spec]
  rfl

theorem unary_large_equal :
    (1000 - 1000) + (1000 - 1000) = (0 : Nat) ∧
      (UnaryComparison.unaryLERun 1000 1000).2 = 1001 := ⟨rfl, UnaryComparison.equal_inputs_steps 1000⟩

theorem unary_any_difference_bound_fails (bound : Nat → Nat) :
    ¬ ∀ n m, (UnaryComparison.unaryLERun n m).2 ≤ bound ((n - m) + (m - n)) :=
  UnaryComparison.no_difference_only_bound bound

theorem unary_square_client : (UnaryComparison.unaryLESquare.impl (8, 3)).1 = false := by
  rw [UnaryComparison.unaryLESquare_value]
  rfl

theorem unary_composed_directions : UnaryComparison.compareBothWays 3 8 = ((true, false), 8) := by
  rw [UnaryComparison.compareBothWays_spec]
  rfl

theorem strict_adapter_boundary : UnaryComparison.unaryLTRun 0 1 = (true, 2) := by
  rw [UnaryComparison.unaryLTRun_spec]
  rfl

theorem strict_adapter_equal : UnaryComparison.unaryLTRun 3 3 = (false, 4) := by
  rw [UnaryComparison.unaryLTRun_spec]
  rfl

theorem strict_square_client : (UnaryComparison.unaryLTSquare.impl (3, 3)).1 = false := by
  rw [UnaryComparison.unaryLTSquare_value]
  rfl

/-! Source-facing erasure clients preserve arbitrary raw inputs, caller defaults
and accumulator suffixes. No BST premise is introduced for these execution
equalities; the invariant remains necessary for independent-map semantics. -/

theorem source_lookup_erasure {V : Type u} (default : V) (key : Nat)
    (tree : SearchTrees.Tree V) :
    (SearchTree.lookupRun key tree).1.getD default = SearchTrees.lookup default key tree := by
  rw [SearchTree.lookupRun_value]
  rfl

theorem source_bound_erasure {V : Type u} (key : Nat) (tree : SearchTrees.Tree V) :
    (SearchTree.lookupRun key tree).1.isSome = SearchTrees.bound key tree := by
  rw [SearchTree.lookupRun_value]
  rfl

theorem source_insert_erasure {V : Type u} (key : Nat) (value : V)
    (tree : SearchTrees.Tree V) :
    (SearchTree.insertRun key value tree).1 = SearchTrees.insert key value tree :=
  SearchTree.insertRun_value key value tree

theorem source_elements_erasure {V : Type u} (tree : SearchTrees.Tree V) :
    (TreeEnumeration.copyRun tree).1 = SearchTrees.elements tree :=
  TreeEnumeration.copyRun_entries tree

theorem source_accumulator_erasure {V : Type u} (tree : SearchTrees.Tree V)
    (suffix : List (Nat × V)) :
    (TreeEnumeration.accumulatorRun tree suffix).1 = SearchTrees.fastElementsAcc tree suffix :=
  TreeEnumeration.accumulatorRun_fastEntriesAcc tree suffix

theorem source_fast_elements_erasure {V : Type u} (tree : SearchTrees.Tree V) :
    (TreeEnumeration.accumulatorRun tree []).1 = SearchTrees.fastElements tree :=
  TreeEnumeration.accumulatorRun_fastEntriesAcc tree []

/-- Exact source ex_tree execution, independently expected comparator counts,
and the source-facing two-append enumeration. -/
theorem source_ex_tree_runs :
    SearchTree.lookupRun 5 SearchTrees.exampleTree = (some "five", (2, 4)) ∧
    TreeEnumeration.copyRun SearchTrees.exampleTree =
      ([(2, "two"), (4, "four"), (5, "five")], 4) := by
  constructor
  · simp [SearchTrees.exampleTree, SearchTrees.node, SearchTrees.nil, SearchTree.lookupRun_node]
  · simp [SearchTrees.exampleTree, SearchTrees.node, SearchTrees.nil, TreeEnumeration.copyRun_node]

theorem source_nonempty_suffix :
    TreeEnumeration.accumulatorRun SearchTrees.exampleTree [(9, "suffix")] =
      (SearchTrees.fastElementsAcc SearchTrees.exampleTree [(9, "suffix")], (7, 3)) := by
  apply Prod.ext
  · exact source_accumulator_erasure _ _
  · rw [TreeEnumeration.accumulatorRun_work]
    rfl

/-- The earlier source lookup theorem is a client of the measured erasure,
retaining its concrete default and its independently specified returned value. -/
theorem source_default_lookup_client :
    (SearchTree.lookupRun 5 SearchTrees.exampleTree).1.getD "" = "five" := by
  rw [source_lookup_erasure]
  exact SearchTrees.lookup_exampleTree_present

end Examples.SearchTreeWork
