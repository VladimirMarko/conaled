import Applications.Trees.AVL.Basic
import Applications.Search.OrderedMap.Membership
import Applications.Resources.TreeCache

/-! Connected cached-height AVL foundation cases. Cache correctness, recursive
height balance and search order are independent conditions. The expected cases
and declared local-access tariff are recorded in
`docs/research/fdsa-avl-foundations.md`.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.AVLFoundations
open Trees.AVL
universe u
variable {α : Type u}

/-! A01: a raw stored zero is not the actual height of a singleton. -/
def zeroLeaf (a : α) : BinaryTree (α × Nat) := .node (a, 0) .nil .nil

theorem zeroLeaf_observations (a : α) :
    ht (zeroLeaf a) = 0 ∧ (zeroLeaf a).height = 1 :=
  ⟨ht_node a 0 .nil .nil, rfl⟩

theorem zeroLeaf_balanced (a : α) : Balanced (Trees.Cached.erase (zeroLeaf a)) := by
  simp [zeroLeaf, balanced_node]

theorem zeroLeaf_invalid (a : α) : ¬Valid (zeroLeaf a) := by
  intro valid
  have rootCache := ((valid_node_iff a 0 .nil .nil).mp valid).2.2.2
  exact (by decide : (0 : Nat) ≠ 1) rootCache

theorem singleton_repair (a : α) :
    Valid (node .nil a .nil) ∧ ht (node .nil a .nil) = 1 ∧
      Trees.Cached.erase (node .nil a .nil) = Trees.Cached.erase (zeroLeaf a) := by
  refine ⟨valid_singleton a, ?_, ?_⟩
  · rw [ht_node_smart]
    rfl
  · exact erase_node .nil a .nil

/-! A02: a correct root cache does not certify a malformed descendant. -/
def hugeLeaf : BinaryTree (Nat × Nat) := .node (1, 99) .nil .nil
def correctRoot : BinaryTree (Nat × Nat) := .node (2, 2) hugeLeaf .nil

theorem hugeLeaf_invalid : ¬Valid hugeLeaf := by
  intro valid
  have rootCache := ((valid_node_iff 1 99 .nil .nil).mp valid).2.2.2
  exact (by decide : (99 : Nat) ≠ 1) rootCache

theorem correctRoot_observations :
    ht correctRoot = 2 ∧ correctRoot.height = 2 ∧
      Balanced (Trees.Cached.erase correctRoot) := by
  refine ⟨ht_node 2 2 hugeLeaf .nil, rfl, ?_⟩
  simp [correctRoot, hugeLeaf, balanced_node]

theorem correctRoot_invalid : ¬Valid correctRoot := by
  intro valid
  exact hugeLeaf_invalid ((valid_node_iff 2 2 hugeLeaf .nil).mp valid).1

/-! A03: the smart constructor really reads the bad child cache locally. -/
def propagated : BinaryTree (Nat × Nat) := node hugeLeaf 2 .nil

theorem propagated_observations :
    ht propagated = 100 ∧ propagated.height = 2 ∧
      Trees.inorder (Trees.Cached.erase propagated) = [1, 2] := by
  refine ⟨?_, ?_, ?_⟩
  · rw [propagated, ht_node_smart]
    rfl
  · rw [propagated, height_node]
    rfl
  · rw [propagated, inorder_node]
    rfl

theorem propagated_erases :
    Trees.Cached.erase propagated = Trees.Cached.erase correctRoot :=
  erase_node hugeLeaf 2 .nil

theorem propagated_invalid : ¬Valid propagated := by
  intro valid
  exact hugeLeaf_invalid ((node_valid_iff hugeLeaf 2 .nil).mp valid).1

/-! A04/A06: valid children retain correct caches even when the parent is too tall. -/
def two : BinaryTree (Nat × Nat) := node (node .nil 1 .nil) 2 .nil
def leftChain : BinaryTree (Nat × Nat) := node two 3 .nil
def rightTall : BinaryTree (Nat × Nat) := node .nil 3 two

theorem two_valid : Valid two := by
  apply (node_valid_iff (node .nil 1 .nil) 2 .nil).mpr
  exact ⟨valid_singleton 1, valid_nil, by decide⟩

theorem two_height : two.height = 2 := rfl

theorem leftChain_cacheValid : CacheValid leftChain := by
  apply (node_cacheValid_iff two 3 .nil).mpr
  exact ⟨((valid_iff two).mp two_valid).2, cacheValid_nil⟩

theorem leftChain_correct_height : ht leftChain = leftChain.height :=
  ht_eq_height_of_cacheValid leftChain leftChain_cacheValid

theorem leftChain_ordered :
    (Trees.inorder (Trees.Cached.erase leftChain)).Pairwise (· < ·) := by
  change ([1, 2, 3] : List Nat).Pairwise (· < ·)
  decide

theorem leftChain_not_valid : ¬Valid leftChain := by
  intro valid
  have gap := ((node_valid_iff two 3 .nil).mp valid).2.2
  exact (by decide : ¬abs ((two.height : Int) - (0 : Int)) ≤ 1) gap

theorem rightTall_cacheValid : CacheValid rightTall := by
  apply (node_cacheValid_iff .nil 3 two).mpr
  exact ⟨cacheValid_nil, ((valid_iff two).mp two_valid).2⟩

theorem rightTall_not_valid : ¬Valid rightTall := by
  intro valid
  have gap := ((node_valid_iff .nil 3 two).mp valid).2.2
  exact (by decide : ¬abs ((0 : Int) - (two.height : Int)) ≤ 1) gap

/-! A05: the signed balance condition must retain both orientations. -/
theorem unit_height_gaps :
    abs ((0 : Int) - 1) ≤ 1 ∧ abs ((1 : Int) - 0) ≤ 1 :=
  ⟨(height_balance_iff 0 1).mpr (by decide),
    (height_balance_iff 1 0).mpr (by decide)⟩

theorem two_height_gaps_fail :
    ¬abs ((0 : Int) - 2) ≤ 1 ∧ ¬abs ((2 : Int) - 0) ≤ 1 := by
  constructor
  · intro gap
    exact (by decide : ¬((0 : Nat) ≤ 2 + 1 ∧ 2 ≤ 0 + 1))
      ((height_balance_iff 0 2).mp gap)
  · intro gap
    exact (by decide : ¬((2 : Nat) ≤ 0 + 1 ∧ 0 ≤ 2 + 1))
      ((height_balance_iff 2 0).mp gap)

theorem truncated_subtraction_loses_one_side : (0 : Nat) - 2 = 0 := rfl

/-! A07: ordered contents suffice for search even when every cache is wrong. -/
def badOrdered : BinaryTree (Nat × Nat) :=
  .node (2, 0) (.node (1, 99) .nil .nil) (.node (3, 42) .nil .nil)

theorem badOrdered_inorder :
    Trees.inorder (Trees.Cached.erase badOrdered) = [1, 2, 3] := rfl

theorem badOrdered_strict :
    (Trees.inorder (Trees.Cached.erase badOrdered)).Pairwise (· < ·) := by
  rw [badOrdered_inorder]
  decide

theorem badOrdered_invalid : ¬Valid badOrdered := by
  intro valid
  have rootCache := ((valid_node_iff 2 0
    (.node (1, 99) .nil .nil) (.node (3, 42) .nil .nil)).mp valid).2.2.2
  exact (by decide : (0 : Nat) ≠ 2) rootCache

theorem badOrdered_membership (query : Nat) :
    Search.OrderedMap.containsKey query badOrdered = true ↔ query ∈ [1, 2, 3] := by
  simpa only [badOrdered_inorder] using
    Search.OrderedMap.containsKey_eq_true_iff_of_inorder_pairwise badOrdered_strict query

theorem badOrdered_set_membership (query : Nat) :
    Search.OrderedMap.containsKey query badOrdered = true ↔
      query ∈ Trees.setTree (Trees.Cached.erase badOrdered) :=
  (Search.OrderedMap.containsKey_eq_true_iff_of_inorder_pairwise badOrdered_strict query).trans
    (Trees.mem_inorder_iff_mem_setTree query (Trees.Cached.erase badOrdered))

theorem badOrdered_raw_path (query : Nat) :
    Search.OrderedMap.containsKey query badOrdered =
      Search.OrderedTree.member query (Trees.Cached.erase badOrdered) :=
  Search.OrderedMap.containsKey_eq_member_erase query badOrdered

theorem badOrdered_answers :
    [1, 2, 3, 4].map (fun query => Search.OrderedMap.containsKey query badOrdered) =
      [true, true, true, false] := rfl

/-! A08: a correctly cached balanced shape can still be unordered. -/
def unordered : BinaryTree (Nat × Nat) :=
  node (node .nil 3 .nil) 2 (node .nil 1 .nil)

theorem unordered_valid : Valid unordered := by
  apply (node_valid_iff (node .nil 3 .nil) 2 (node .nil 1 .nil)).mpr
  exact ⟨valid_singleton 3, valid_singleton 1, by decide⟩

theorem unordered_not_strict :
    ¬(Trees.inorder (Trees.Cached.erase unordered)).Pairwise (· < ·) := by
  change ¬([3, 2, 1] : List Nat).Pairwise (· < ·)
  decide

theorem unordered_misses_present_key :
    Search.OrderedMap.containsKey 3 unordered = false ∧
      3 ∈ Trees.setTree (Trees.Cached.erase unordered) := by
  constructor
  · rfl
  · apply (Trees.mem_inorder_iff_mem_setTree 3 _).mp
    change 3 ∈ ([3, 2, 1] : List Nat)
    exact List.mem_cons_self

/-! A09: empty types, arbitrary universes and noninjective maps remain supported. -/
theorem empty_payload_valid :
    Valid (.nil : BinaryTree (PEmpty.{u + 1} × Nat)) := valid_nil

theorem generic_decoration (t : BinaryTree α) (balanced : Balanced t) :
    Valid (annotate t) ∧ Trees.Cached.erase (annotate t) = t ∧
      ht (annotate t) = t.height :=
  ⟨(valid_annotate_iff t).mpr balanced, erase_annotate t, ht_annotate t⟩

def collapse (_ : Nat) : Unit := ()

theorem collapse_not_injective : ¬Function.Injective collapse := by
  intro injective
  have zero_eq_one : (0 : Nat) = 1 := injective rfl
  exact Nat.zero_ne_one zero_eq_one

theorem collapse_balance_iff (t : BinaryTree Nat) :
    Balanced (t.map collapse) ↔ Balanced t := balanced_map collapse t

/-! A10: decoration fixes caches, and preserves the independent balance boundary. -/
def repeatedRaw : BinaryTree Nat :=
  .node 7 (.node 7 .nil .nil) (.node 7 .nil .nil)

def chainRaw : BinaryTree Nat :=
  .node 3 (.node 2 (.node 1 .nil .nil) .nil) .nil

theorem repeatedRaw_balanced : Balanced repeatedRaw := by
  simp [repeatedRaw, balanced_node]

theorem repeated_decoration :
    Valid (annotate repeatedRaw) ∧ Trees.Cached.erase (annotate repeatedRaw) = repeatedRaw ∧
      ht (annotate repeatedRaw) = 2 :=
  generic_decoration repeatedRaw repeatedRaw_balanced

theorem repeated_shape_counts :
    (annotate repeatedRaw).numNodes = 3 ∧
      (annotate repeatedRaw).numLeaves = 4 ∧ (annotate repeatedRaw).height = 2 := by
  rw [← Trees.Cached.numNodes_erase (annotate repeatedRaw),
    ← Trees.Cached.numLeaves_erase (annotate repeatedRaw),
    ← Trees.Cached.height_erase (annotate repeatedRaw), erase_annotate]
  exact ⟨rfl, rfl, rfl⟩

theorem repeated_payload_occurrences :
    Trees.inorder (Trees.Cached.erase (annotate repeatedRaw)) = [7, 7, 7] := by
  rw [erase_annotate]
  rfl

theorem repeated_collapse_balanced : Balanced (repeatedRaw.map collapse) :=
  (collapse_balance_iff repeatedRaw).mpr repeatedRaw_balanced

theorem chainRaw_not_balanced : ¬Balanced chainRaw := by
  intro balanced
  have gap := ((balanced_node 3 (.node 2 (.node 1 .nil .nil) .nil) .nil).mp balanced).2.2.1
  exact (by decide : ¬(2 : Nat) ≤ 0 + 1) gap

theorem chain_decoration_cacheValid : CacheValid (annotate chainRaw) :=
  annotate_cacheValid chainRaw

theorem chain_decoration_erases : Trees.Cached.erase (annotate chainRaw) = chainRaw :=
  erase_annotate chainRaw

theorem chain_decoration_not_valid : ¬Valid (annotate chainRaw) := by
  intro valid
  exact chainRaw_not_balanced ((valid_annotate_iff chainRaw).mp valid)

theorem collapsed_chain_not_balanced : ¬Balanced (chainRaw.map collapse) := by
  intro balanced
  exact chainRaw_not_balanced ((collapse_balance_iff chainRaw).mp balanced)

/-! Local work: one event for each root read, construction, max and addition.
Natural arithmetic is unit-cost in this declared observation. No machine-bit,
allocation, physical-sharing or whole-operation complexity claim is made. -/
def heightCombineRun (hl : Nat) (a : α) (hr : Nat) : Resources.Measured Nat Nat :=
  (heightCombine hl a hr, 2)

theorem local_node_value (l : BinaryTree (α × Nat)) (a : α) (r : BinaryTree (α × Nat)) :
    (Resources.TreeCache.nodeRun 0 heightCombineRun l a r).1 = node l a r :=
  Resources.TreeCache.nodeRun_value 0 heightCombine heightCombineRun l a r rfl

theorem local_node_cost (l : BinaryTree (α × Nat)) (a : α) (r : BinaryTree (α × Nat)) :
    (Resources.TreeCache.nodeRun 0 heightCombineRun l a r).2 = 5 := by
  rw [Resources.TreeCache.nodeRun_cost]
  rfl

theorem malformed_child_local_execution :
    Resources.TreeCache.nodeRun 0 heightCombineRun hugeLeaf 2 .nil = (propagated, 5) := by
  apply Prod.ext
  · exact local_node_value hugeLeaf 2 .nil
  · exact local_node_cost hugeLeaf 2 .nil

theorem empty_search (query : Nat) :
    Search.OrderedMap.containsKey query (.nil : BinaryTree (Nat × Nat)) = false ∧
      Trees.inorder (Trees.Cached.erase (.nil : BinaryTree (Nat × Nat))) = [] :=
  ⟨Search.OrderedMap.containsKey_nil query, rfl⟩

end Examples.AVLFoundations
