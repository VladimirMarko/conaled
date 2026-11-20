import Applications.Trees.AVL.Height
import Mathlib.Tactic.NormNum

/-! Connected AVL height and minimum-size cases. External leaves, internal nodes,
actual height and stored height have different roles. These cases consume the
general bounds and attaining-tree laws described in
`docs/research/fdsa-avl-height.md`.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.AVLHeight
open Trees.AVL
universe u
variable {α : Type u}

def singleton (a : α) : BinaryTree α := .node a .nil .nil

theorem singleton_balanced (a : α) : Balanced (singleton a) := by
  simp [singleton, balanced_node]

/-! H01: the empty tree has one external leaf and a zero logarithm. -/
theorem empty_bounds :
    Nat.fib 2 ≤ 1 ∧ Real.goldenRatio ^ 0 ≤ (1 : ℝ) ∧
      (0 : ℝ) ≤ (1 / Real.logb 2 Real.goldenRatio) * Real.logb 2 1 := by
  refine ⟨?_, ?_, ?_⟩
  · exact fib_height_le_numLeaves (.nil : BinaryTree Unit) balanced_nil
  · simpa only [BinaryTree.height, BinaryTree.numLeaves, Nat.cast_one] using
      goldenRatio_pow_height_le_numLeaves (.nil : BinaryTree Unit) balanced_nil
  · simpa only [BinaryTree.height, BinaryTree.numLeaves, Nat.cast_zero, Nat.cast_one] using
      height_le_logb_numLeaves (.nil : BinaryTree Unit) balanced_nil

theorem empty_logarithm : Real.logb 2 (1 : ℝ) = 0 := by simp

theorem cached_empty_bounds :
    Nat.fib (ht (.nil : BinaryTree (Unit × Nat)) + 2) ≤ 1 ∧
      (ht (.nil : BinaryTree (Unit × Nat)) : ℝ) ≤
        (1 / Real.logb 2 Real.goldenRatio) * Real.logb 2 1 := by
  refine ⟨fib_ht_le_numLeaves .nil valid_nil, ?_⟩
  simpa only [BinaryTree.numLeaves, Nat.cast_one] using
    ht_le_logb_numLeaves (.nil : BinaryTree (Unit × Nat)) valid_nil

/-! H02: nodes+1 gives the correct logarithm; nodes alone fails at a singleton. -/
theorem singleton_nodes_log_bound :
    ((singleton ()).height : ℝ) ≤ (1 / Real.logb 2 Real.goldenRatio) *
      Real.logb 2 (((singleton ()).numNodes : ℝ) + 1) :=
  height_le_logb_numNodes_add_one (singleton ()) (singleton_balanced ())

theorem singleton_node_only_log_fails :
    ¬((singleton ()).height : ℝ) ≤ (1 / Real.logb 2 Real.goldenRatio) *
      Real.logb 2 ((singleton ()).numNodes : ℝ) := by
  norm_num [singleton, BinaryTree.height, BinaryTree.numNodes]

theorem singleton_cached_height_bound :
    (ht (node .nil () .nil) : ℝ) ≤ (1 / Real.logb 2 Real.goldenRatio) *
      Real.logb 2 ((node .nil () .nil).numLeaves : ℝ) :=
  ht_le_logb_numLeaves (node .nil () .nil) (valid_singleton ())

def perfectTwo : BinaryTree Unit := .node () (singleton ()) (singleton ())
def perfectThree : BinaryTree Unit := .node () perfectTwo perfectTwo

theorem perfectTwo_balanced : Balanced perfectTwo := by
  simp [perfectTwo, singleton, balanced_node, BinaryTree.height]

theorem perfectThree_balanced : Balanced perfectThree := by
  simp [perfectThree, perfectTwo, singleton, balanced_node, BinaryTree.height]

/-! H03: height2 has an attaining three-leaf tree and a four-leaf comparison. -/
theorem minimum_two_observations :
    (fibTree 2).height = 2 ∧ (fibTree 2).numLeaves = 3 ∧ (fibTree 2).numNodes = 2 := by
  refine ⟨height_fibTree 2, ?_, ?_⟩
  · rw [numLeaves_fibTree]
    norm_num
  · have count := numNodes_fibTree_add_one 2
    norm_num at count
    omega

theorem perfectTwo_observations :
    perfectTwo.height = 2 ∧ perfectTwo.numLeaves = 4 := ⟨rfl, rfl⟩

theorem perfectTwo_minimum_comparison :
    (fibTree perfectTwo.height).numLeaves ≤ perfectTwo.numLeaves :=
  fibTree_minimal perfectTwo perfectTwo_balanced

theorem perfectTwo_strictly_more_leaves :
    (fibTree perfectTwo.height).numLeaves < perfectTwo.numLeaves := by
  rw [numLeaves_fibTree]
  norm_num [perfectTwo, singleton, BinaryTree.height, BinaryTree.numLeaves]

/-! H04: correct annotation does not make an unbalanced chain satisfy the bound. -/
def chainThree : BinaryTree Unit := .node () (.node () (singleton ()) .nil) .nil

theorem chainThree_observations :
    chainThree.height = 3 ∧ chainThree.numNodes = 3 ∧ chainThree.numLeaves = 4 :=
  ⟨rfl, rfl, rfl⟩

theorem chainThree_not_balanced : ¬Balanced chainThree := by
  intro balanced
  have bound := fib_height_le_numLeaves chainThree balanced
  norm_num [chainThree, singleton, BinaryTree.height, BinaryTree.numLeaves] at bound

theorem cached_chain_observations :
    CacheValid (annotate chainThree) ∧ ht (annotate chainThree) = 3 ∧
      ¬Valid (annotate chainThree) := by
  refine ⟨annotate_cacheValid chainThree, ?_, ?_⟩
  · rw [ht_annotate]
    rfl
  · intro valid
    exact chainThree_not_balanced ((valid_annotate_iff chainThree).mp valid)

/-! H05: equal leaf counts do not determine the attaining tree's height. -/
theorem equal_leaves_different_heights :
    (fibTree 4).numLeaves = 8 ∧ perfectThree.numLeaves = 8 ∧
      (fibTree 4).height = 4 ∧ perfectThree.height = 3 ∧
      (fibTree 4).height ≠ perfectThree.height := by
  refine ⟨?_, rfl, height_fibTree 4, rfl, ?_⟩
  · rw [numLeaves_fibTree]
    norm_num
  · rw [height_fibTree]
    decide

/-! H06: repeated Unit labels count as occurrences, not distinct set elements. -/
theorem repeated_witness_observations :
    Balanced (fibTree 3) ∧ (fibTree 3).height = 3 ∧
      (fibTree 3).numLeaves = 5 ∧ (fibTree 3).numNodes = 4 := by
  refine ⟨balanced_fibTree 3, height_fibTree 3, ?_, ?_⟩
  · rw [numLeaves_fibTree]
    norm_num
  · have count := numNodes_fibTree_add_one 3
    norm_num at count
    omega

theorem repeated_witness_payloads :
    Trees.inorder (fibTree 3) = [(), (), (), ()] := rfl

theorem repeated_witness_is_minimal :
    (fibTree (fibTree 3).height).numLeaves ≤ (fibTree 3).numLeaves :=
  fibTree_minimal (fibTree 3) (balanced_fibTree 3)

/-! H07: a malformed stored height must not replace the structural height. -/
def badSingleton : BinaryTree (Unit × Nat) := .node ((), 3) .nil .nil

theorem badSingleton_observations :
    ht badSingleton = 3 ∧ badSingleton.height = 1 ∧ badSingleton.numLeaves = 2 :=
  ⟨rfl, rfl, rfl⟩

theorem badSingleton_erased_balanced : Balanced (Trees.Cached.erase badSingleton) := by
  simp [badSingleton, balanced_node]

theorem badSingleton_actual_height_bound :
    Nat.fib (badSingleton.height + 2) ≤ badSingleton.numLeaves := by
  simpa only [Trees.Cached.height_erase, Trees.Cached.numLeaves_erase] using
    fib_height_le_numLeaves (Trees.Cached.erase badSingleton) badSingleton_erased_balanced

theorem badSingleton_stored_bound_fails :
    ¬Nat.fib (ht badSingleton + 2) ≤ badSingleton.numLeaves := by
  norm_num [badSingleton, ht, Trees.Cached.read, BinaryTree.numLeaves]

theorem badSingleton_cache_invalid : ¬CacheValid badSingleton := by
  intro cached
  have equal := ht_eq_height_of_cacheValid badSingleton cached
  norm_num [badSingleton, ht, Trees.Cached.read, BinaryTree.height] at equal

def repairedSingleton : BinaryTree (Unit × Nat) :=
  annotate (Trees.Cached.erase badSingleton)

theorem repairedSingleton_valid : Valid repairedSingleton :=
  (valid_annotate_iff _).mpr badSingleton_erased_balanced

theorem repairedSingleton_bounds :
    Nat.fib (ht repairedSingleton + 2) ≤ repairedSingleton.numLeaves ∧
      (ht repairedSingleton : ℝ) ≤ (1 / Real.logb 2 Real.goldenRatio) *
        Real.logb 2 (repairedSingleton.numLeaves : ℝ) :=
  ⟨fib_ht_le_numLeaves repairedSingleton repairedSingleton_valid,
    ht_le_logb_numLeaves repairedSingleton repairedSingleton_valid⟩

theorem repairedSingleton_erasure :
    Trees.Cached.erase repairedSingleton = Trees.Cached.erase badSingleton :=
  erase_annotate (Trees.Cached.erase badSingleton)

/-! H08: universal bounds include empty payload universes; attainment uses Unit. -/
theorem empty_payload_height (t : BinaryTree (PEmpty.{u + 1})) : t.height = 0 := by
  cases t with
  | nil => rfl
  | node a _ _ => exact PEmpty.elim a

theorem empty_payload_no_positive_height (n : Nat) (positive : 0 < n) :
    ¬∃ t : BinaryTree (PEmpty.{u + 1}), t.height = n := by
  rintro ⟨t, height⟩
  exact (Nat.ne_of_gt positive) (height.symm.trans (empty_payload_height t))

theorem empty_payload_bound :
    ((.nil : BinaryTree (PEmpty.{u + 1})).height : ℝ) ≤
      (1 / Real.logb 2 Real.goldenRatio) *
        Real.logb 2 ((.nil : BinaryTree (PEmpty.{u + 1})).numLeaves : ℝ) :=
  height_le_logb_numLeaves .nil balanced_nil

theorem empty_payload_cached_bound :
    (ht (.nil : BinaryTree (PEmpty.{u + 1} × Nat)) : ℝ) ≤
      (1 / Real.logb 2 Real.goldenRatio) * Real.logb 2 1 := by
  simpa only [BinaryTree.numLeaves, Nat.cast_one] using
    ht_le_logb_numLeaves (.nil : BinaryTree (PEmpty.{u + 1} × Nat)) valid_nil

/-! H09: the printed1.44 is an approximation, not an upper bound. -/
theorem coefficient_enclosure :
    (1440 / 1000 : ℝ) < 1 / Real.logb 2 Real.goldenRatio ∧
      1 / Real.logb 2 Real.goldenRatio < (1441 / 1000 : ℝ) :=
  height_coefficient_bounds

theorem coefficient_not_le_one_point_four_four :
    ¬1 / Real.logb 2 Real.goldenRatio ≤ (1440 / 1000 : ℝ) :=
  not_le.mpr height_coefficient_bounds.1

/-! H10: initial values are observations of the actual attaining program. -/
theorem initial_minimum_leaves :
    [0, 1, 2, 3, 4].map (fun n => (fibTree n).numLeaves) = [1, 2, 3, 5, 8] := by
  simp only [List.map_cons, List.map_nil, numLeaves_fibTree]
  norm_num

private theorem witness_nodes (n : Nat) :
    (fibTree n).numNodes = Nat.fib (n + 2) - 1 := by
  have count := numNodes_fibTree_add_one n
  omega

theorem initial_minimum_nodes :
    [0, 1, 2, 3, 4].map (fun n => (fibTree n).numNodes) = [0, 1, 2, 4, 7] := by
  simp only [List.map_cons, List.map_nil, witness_nodes]
  norm_num

theorem witness_bases_and_recurrence (n : Nat) :
    fibTree 0 = .nil ∧ fibTree 1 = .node () .nil .nil ∧
      fibTree (n + 2) = .node () (fibTree (n + 1)) (fibTree n) ∧
      (fibTree (n + 2)).numLeaves =
        (fibTree (n + 1)).numLeaves + (fibTree n).numLeaves :=
  ⟨fibTree_zero, fibTree_one, fibTree_add_two n, numLeaves_fibTree_add_two n⟩

theorem cached_attainment (n : Nat) :
    Valid (annotate (fibTree n)) ∧ (annotate (fibTree n)).height = n ∧
      (annotate (fibTree n)).numLeaves = Nat.fib (n + 2) :=
  ⟨valid_annotate_fibTree n, height_annotate_fibTree n, numLeaves_annotate_fibTree n⟩

theorem attained_shape_minimum (n : Nat) :
    ∃ t : BinaryTree Unit, Balanced t ∧ t.height = n ∧
      t.numLeaves = Nat.fib (n + 2) := exists_balanced_height_numLeaves n

theorem attained_cached_minimum (n : Nat) :
    ∃ t : BinaryTree (Unit × Nat), Valid t ∧ t.height = n ∧
      t.numLeaves = Nat.fib (n + 2) := exists_valid_height_numLeaves n

/-! H11: generic consumers retain the intended weak domain assumptions. -/
theorem arbitrary_payload_bounds (t : BinaryTree α) (balanced : Balanced t) :
    Nat.fib (t.height + 2) ≤ t.numLeaves ∧
      Real.goldenRatio ^ t.height ≤ (t.numLeaves : ℝ) ∧
      (t.height : ℝ) ≤ (1 / Real.logb 2 Real.goldenRatio) *
        Real.logb 2 (t.numLeaves : ℝ) :=
  ⟨fib_height_le_numLeaves t balanced,
    goldenRatio_pow_height_le_numLeaves t balanced, height_le_logb_numLeaves t balanced⟩

theorem arbitrary_cached_bounds (t : BinaryTree (α × Nat)) (valid : Valid t) :
    Nat.fib (t.height + 2) ≤ t.numLeaves ∧
      Real.goldenRatio ^ t.height ≤ (t.numLeaves : ℝ) ∧
      (t.height : ℝ) ≤ (1 / Real.logb 2 Real.goldenRatio) *
        Real.logb 2 (t.numLeaves : ℝ) ∧
      (ht t : ℝ) ≤ (1 / Real.logb 2 Real.goldenRatio) *
        Real.logb 2 (t.numLeaves : ℝ) :=
  ⟨fib_height_le_numLeaves_of_valid t valid,
    goldenRatio_pow_height_le_numLeaves_of_valid t valid,
    height_le_logb_numLeaves_of_valid t valid, ht_le_logb_numLeaves t valid⟩

theorem arbitrary_payload_minimum (t : BinaryTree α) (balanced : Balanced t) :
    (fibTree t.height).numLeaves ≤ t.numLeaves ∧
      (fibTree t.height).numNodes ≤ t.numNodes :=
  ⟨fibTree_minimal t balanced, fibTree_numNodes_minimal t balanced⟩

theorem arbitrary_cached_minimum (t : BinaryTree (α × Nat)) (valid : Valid t) :
    (fibTree t.height).numLeaves ≤ t.numLeaves ∧
      (fibTree t.height).numNodes ≤ t.numNodes :=
  ⟨fibTree_minimal_of_valid t valid, fibTree_numNodes_minimal_of_valid t valid⟩

end Examples.AVLHeight
