import Applications.Resources.TreeLeftmost
import Examples.OrderedTrees
import Mathlib.Data.List.Range
import Init.Data.List.Find

/-! Connected ordinary extraction clients. Expected residual shapes, semantic
map values, duplicate and malformed boundaries, and all-length chain results
come from the guarded source recurrence. Source and statement correspondence:
`docs/research/fdsa-tree-leftmost.md`.
-/
set_option autoImplicit false
set_option warningAsError true

namespace TreeLeftmostExamples
universe u v w z
variable {α : Type u} {β : Type v} {κ : Type w} {γ : Type z}

open Resources.TreeLeftmost

def promotedInput : BinaryTree Nat :=
  .node 2 (.node 0 .nil (.node 1 .nil .nil)) (.node 3 .nil .nil)

def promotedResidual : BinaryTree Nat :=
  .node 2 (.node 1 .nil .nil) (.node 3 .nil .nil)

def printedResidual : BinaryTree Nat :=
  .node 6 (.node 3 .nil (.node 5 .nil .nil))
    (.node 9 (.node 8 .nil .nil) .nil)

def taggedResidual : BinaryTree (Nat × Bool) :=
  .node (1, true) .nil (.node (2, false) .nil .nil)

def successorResidual : BinaryTree (Nat × Bool) :=
  .node (2, false) (.node (0, false) .nil .nil) .nil

def sameKeyResidual : BinaryTree (Nat × Nat) := .node (1, 20) .nil .nil

def malformedResidual : BinaryTree Nat := .node 0 .nil (.node 1 .nil .nil)

def nextResidual : BinaryTree Nat := .node 1 .nil (.node 2 .nil .nil)

def staleSizeResidual : BinaryTree (Nat × Nat) :=
  .node (1, 4) .nil (.node (3, 2) (.node (2, 1) .nil .nil) .nil)

/-- The parameters specify the actual increasing labels, not just a size. -/
def leftChain (start : Nat) : Nat → BinaryTree Nat
  | 0 => .nil
  | n + 1 => .node (start + n) (leftChain start n) .nil

def rightChain (start : Nat) : Nat → BinaryTree Nat
  | 0 => .nil
  | n + 1 => .node start .nil (rightChain (start + 1) n)

theorem leftChain_inorder (start n : Nat) :
    Trees.inorder (leftChain start n) = List.range' start n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change Trees.inorder (leftChain start n) ++ [start + n] = List.range' start (n + 1)
      rw [ih]
      exact List.range'_1_concat.symm

theorem rightChain_inorder (start n : Nat) :
    Trees.inorder (rightChain start n) = List.range' start n := by
  induction n generalizing start with
  | zero => rfl
  | succ n ih =>
      change start :: Trees.inorder (rightChain (start + 1) n) = List.range' start (n + 1)
      exact congrArg (List.cons start) (ih (start + 1))

theorem chain_inorders (n : Nat) :
    Trees.inorder (leftChain 0 n) = List.range n ∧
      Trees.inorder (rightChain 0 n) = List.range n := by
  simpa only [List.range_eq_range'] using
    And.intro (leftChain_inorder 0 n) (rightChain_inorder 0 n)

private theorem range'_strict (start n : Nat) :
    (List.range' start n).Pairwise (fun a b => a < b) := by
  induction n generalizing start with
  | zero => exact List.Pairwise.nil
  | succ n ih =>
      rw [List.range'_succ, List.pairwise_cons]
      refine ⟨?_, ih (start + 1)⟩
      intro b hb
      obtain ⟨i, _, hi⟩ := List.mem_range'.mp hb
      simp only [Nat.one_mul] at hi
      omega

theorem leftChain_ordered (start n : Nat) :
    Trees.Ordered (fun a b : Nat => a < b) (leftChain start n) := by
  apply Trees.ordered_of_pairwise_inorder
  rw [leftChain_inorder]
  exact range'_strict start n

theorem rightChain_ordered (start n : Nat) :
    Trees.Ordered (fun a b : Nat => a < b) (rightChain start n) := by
  apply Trees.ordered_of_pairwise_inorder
  rw [rightChain_inorder]
  exact range'_strict start n

theorem leftChain_numNodes (start n : Nat) : (leftChain start n).numNodes = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [leftChain, BinaryTree.numNodes, ih]

theorem rightChain_numNodes (start n : Nat) : (rightChain start n).numNodes = n := by
  induction n generalizing start with
  | zero => rfl
  | succ n ih => simp [rightChain, BinaryTree.numNodes, ih]

theorem leftChain_height (start n : Nat) : (leftChain start n).height = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [leftChain, BinaryTree.height, ih]

theorem rightChain_height (start n : Nat) : (rightChain start n).height = n := by
  induction n generalizing start with
  | zero => rfl
  | succ n ih => simp [rightChain, BinaryTree.height, ih]

theorem leftChain_ne_nil (start n : Nat) (hn : 0 < n) : leftChain start n ≠ .nil := by
  cases n with
  | zero => omega
  | succ n => simp [leftChain]

theorem rightChain_ne_nil (start n : Nat) (hn : 0 < n) : rightChain start n ≠ .nil := by
  cases n with
  | zero => omega
  | succ n => simp [rightChain]

/-- Equal residual inorders do not determine the residual root or child positions. -/
theorem shifted_chain_shapes_differ (n : Nat) (hn : 2 ≤ n) :
    leftChain 1 n ≠ rightChain 1 n := by
  cases n with
  | zero => omega
  | succ n =>
      intro h
      change BinaryTree.node (1 + n) (leftChain 1 n) .nil =
        BinaryTree.node 1 .nil (rightChain 2 n) at h
      have hv : 1 + n = 1 := (BinaryTree.node.inj h).1
      omega

theorem nil_run : run (.nil : BinaryTree α) = (none, 1) := run_nil

theorem arbitrary_base (a : α) (r : BinaryTree α) :
    run (.node a .nil r) = (some (a, r), 1) := run_node_nil a r

/-- The old minimum's right child becomes the actual new left child. -/
theorem opaque_promotion (a c : α) (B R : BinaryTree α) :
    run (.node c (.node a .nil B) R) = (some (a, .node c B R), 2) :=
  run_node_of_run c (.node a .nil B) R a B 1 (run_node_nil a B)

theorem every_node_defined (a : α) (l r : BinaryTree α) :
    (extract? (.node a l r)).isSome = true :=
  (extract?_isSome_iff _).2 (by simp)

theorem empty_payload_run (t : BinaryTree Empty) : run t = (none, 1) :=
  (congrArg run (TreeCacheExamples.empty_tree t)).trans run_nil

theorem empty_map_value_run (t : BinaryTree (Nat × Empty)) : run t = (none, 1) := by
  cases t with
  | nil => exact run_nil
  | node a _l _r => exact Empty.elim a.2

theorem promoted_run : run promotedInput = (some (0, promotedResidual), 2) :=
  opaque_promotion 0 2 (.node 1 .nil .nil) (.node 3 .nil .nil)

theorem promoted_extract : extract? promotedInput = some (0, promotedResidual) :=
  congrArg Prod.fst promoted_run

theorem printed_run :
    run OrderedTreeExamples.printedTree = (some (2, printedResidual), 3) := by
  have hl := opaque_promotion 2 3 (.nil : BinaryTree Nat) (.node 5 .nil .nil)
  exact run_node_of_run 6
    (.node 3 (.node 2 .nil .nil) (.node 5 .nil .nil))
    (.node 9 (.node 8 .nil .nil) .nil) 2
    (.node 3 .nil (.node 5 .nil .nil)) 2 hl

theorem printed_extract :
    extract? OrderedTreeExamples.printedTree = some (2, printedResidual) :=
  congrArg Prod.fst printed_run

theorem tagged_run :
    run OrderedTreeExamples.taggedTree = (some ((0, false), taggedResidual), 2) :=
  opaque_promotion (0, false) (1, true) .nil (.node (2, false) .nil .nil)

theorem tagged_extract :
    extract? OrderedTreeExamples.taggedTree = some ((0, false), taggedResidual) :=
  congrArg Prod.fst tagged_run

theorem sameKey_run :
    run OrderedTreeExamples.sameKeyRecords = (some ((1, 10), sameKeyResidual), 1) :=
  run_node_nil (1, 10) (.node (1, 20) .nil .nil)

theorem sameKey_extract :
    extract? OrderedTreeExamples.sameKeyRecords = some ((1, 10), sameKeyResidual) :=
  congrArg Prod.fst sameKey_run

theorem malformed_run :
    run (OrderedTreeExamples.three 2 0 1) = (some (2, malformedResidual), 2) :=
  opaque_promotion 2 0 .nil (.node 1 .nil .nil)

theorem malformed_extract :
    extract? (OrderedTreeExamples.three 2 0 1) = some (2, malformedResidual) :=
  congrArg Prod.fst malformed_run

theorem next_run :
    run (OrderedTreeExamples.three 0 1 2) = (some (0, nextResidual), 2) :=
  opaque_promotion 0 1 .nil (.node 2 .nil .nil)

theorem next_extract :
    extract? (OrderedTreeExamples.three 0 1 2) = some (0, nextResidual) :=
  congrArg Prod.fst next_run

theorem sizeSample_run :
    run TreeCacheExamples.sizeSample = (some ((0, 1), staleSizeResidual), 2) :=
  opaque_promotion (0, 1) (1, 4) .nil
    (.node (3, 2) (.node (2, 1) .nil .nil) .nil)

theorem sizeSample_extract :
    extract? TreeCacheExamples.sizeSample = some ((0, 1), staleSizeResidual) :=
  congrArg Prod.fst sizeSample_run

/-- Observe the semantic value of the full returned map entry. -/
def payloadRun (t : BinaryTree (κ × β)) : Resources.Measured (Option β) Nat :=
  Resources.bind (run t) fun result =>
    Resources.pure (result.map (fun p => p.1.2))

def presenceRun (t : BinaryTree α) : Resources.Measured Bool Nat :=
  Resources.bind (run t) fun result => Resources.pure result.isSome

theorem payloadRun_observation (t : BinaryTree (κ × β)) :
    payloadRun t = ((extract? t).map (fun p => p.1.2), entries t) :=
  Resources.CallCount.primitive_rule
    (fun result : Option ((κ × β) × BinaryTree (κ × β)) => result.map (fun p => p.1.2))
    (run t)

theorem presenceRun_observation (t : BinaryTree α) :
    presenceRun t = ((extract? t).isSome, entries t) :=
  Resources.CallCount.primitive_rule
    (fun result : Option (α × BinaryTree α) => result.isSome) (run t)

theorem tagged_payload_and_presence :
    payloadRun OrderedTreeExamples.taggedTree = (some false, 2) ∧
      presenceRun OrderedTreeExamples.taggedTree = (true, 2) := by
  rw [payloadRun_observation, presenceRun_observation]
  change (((run OrderedTreeExamples.taggedTree).1.map (fun p => p.1.2),
      (run OrderedTreeExamples.taggedTree).2) = (some false, 2)) ∧
    (((run OrderedTreeExamples.taggedTree).1.isSome,
      (run OrderedTreeExamples.taggedTree).2) = (true, 2))
  rw [tagged_run]
  exact ⟨rfl, rfl⟩

theorem nil_payload_and_presence :
    payloadRun (.nil : BinaryTree (κ × β)) = (none, 1) ∧
      presenceRun (.nil : BinaryTree (κ × β)) = (false, 1) := by
  rw [payloadRun_observation, presenceRun_observation]
  exact ⟨rfl, rfl⟩

/-- Only the nonrecursive replacement body: no recursive deletion is defined. -/
def successorBody : Resources.Measured (Option (BinaryTree (Nat × Bool))) Nat :=
  Resources.bind (run OrderedTreeExamples.taggedTree.right) fun result =>
    Resources.pure (result.map (fun p =>
      BinaryTree.node p.1 OrderedTreeExamples.taggedTree.left p.2))

theorem successor_child_run :
    run OrderedTreeExamples.taggedTree.right =
      (some ((2, false), (.nil : BinaryTree (Nat × Bool))), 1) :=
  run_node_nil (2, false) .nil

theorem successor_body_run : successorBody = (some successorResidual, 1) := by
  simpa only [successorBody, successor_child_run, Option.map_some] using
    Resources.CallCount.primitive_rule
      (fun result : Option ((Nat × Bool) × BinaryTree (Nat × Bool)) =>
        result.map (fun p =>
          BinaryTree.node p.1 OrderedTreeExamples.taggedTree.left p.2))
      (run OrderedTreeExamples.taggedTree.right)

theorem successor_body_inorder :
    successorBody.1.map Trees.inorder = some [(0, false), (2, false)] :=
  congrArg (fun r : Resources.Measured (Option (BinaryTree (Nat × Bool))) Nat =>
    r.1.map Trees.inorder) successor_body_run

theorem successor_body_lookup :
    successorBody.1.map (fun t => (Trees.inorder t).lookup 1) = some none ∧
      successorBody.1.map (fun t => (Trees.inorder t).lookup 2) = some (some false) := by
  rw [successor_body_run]
  exact ⟨rfl, rfl⟩

/-- All nonempty lengths, with the complete shifted residual and actual count. -/
theorem leftChain_run (start n : Nat) :
    run (leftChain start (n + 1)) =
      (some (start, leftChain (start + 1) n), n + 1) := by
  induction n with
  | zero => exact run_node_nil start (.nil : BinaryTree Nat)
  | succ n ih =>
      change run (.node (start + (n + 1)) (leftChain start (n + 1)) .nil) =
        (some (start, .node ((start + 1) + n) (leftChain (start + 1) n) .nil),
          (n + 1) + 1)
      rw [run_node_of_run (start + (n + 1)) (leftChain start (n + 1))
        .nil start (leftChain (start + 1) n) (n + 1) ih]
      have ha : start + (n + 1) = (start + 1) + n := by omega
      rw [ha]

theorem rightChain_run (start n : Nat) :
    run (rightChain start (n + 1)) =
      (some (start, rightChain (start + 1) n), 1) :=
  run_node_nil start (rightChain (start + 1) n)

theorem leftChain_run_of_pos (start n : Nat) (hn : 0 < n) :
    run (leftChain start n) =
      (some (start, leftChain (start + 1) (n - 1)), n) := by
  cases n with
  | zero => omega
  | succ n => simpa only [Nat.add_sub_cancel] using leftChain_run start n

theorem rightChain_run_of_pos (start n : Nat) (hn : 0 < n) :
    run (rightChain start n) =
      (some (start, rightChain (start + 1) (n - 1)), 1) := by
  cases n with
  | zero => omega
  | succ n => simpa only [Nat.add_sub_cancel] using rightChain_run start n

theorem chain_entries (n : Nat) (hn : 0 < n) :
    entries (leftChain 0 n) = n ∧ entries (rightChain 0 n) = 1 :=
  ⟨congrArg Prod.snd (leftChain_run_of_pos 0 n hn),
    congrArg Prod.snd (rightChain_run_of_pos 0 n hn)⟩

theorem chain_residual_inorders (n : Nat) :
    Trees.inorder (leftChain 1 (n - 1)) = Trees.inorder (rightChain 1 (n - 1)) :=
  (leftChain_inorder 1 (n - 1)).trans (rightChain_inorder 1 (n - 1)).symm

theorem chain_residual_shapes_differ (n : Nat) (hn : 3 ≤ n) :
    leftChain 1 (n - 1) ≠ rightChain 1 (n - 1) := by
  apply shifted_chain_shapes_differ
  omega

theorem chain_costs_differ (n : Nat) (hn : 1 < n) :
    entries (leftChain 0 n) ≠ entries (rightChain 0 n) := by
  rcases chain_entries n (by omega) with ⟨hl, hr⟩
  rw [hl, hr]
  omega

theorem chain_zero :
    run (leftChain 0 0) = (none, 1) ∧ run (rightChain 0 0) = (none, 1) :=
  ⟨run_nil, run_nil⟩

theorem chain_singleton :
    run (leftChain 0 1) = (some (0, .nil), 1) ∧
      run (rightChain 0 1) = (some (0, .nil), 1) :=
  ⟨leftChain_run 0 0, rightChain_run 0 0⟩

theorem chain_three :
    run (leftChain 0 3) = (some (0, .node 2 (.node 1 .nil .nil) .nil), 3) ∧
      run (rightChain 0 3) = (some (0, .node 1 .nil (.node 2 .nil .nil)), 1) :=
  ⟨leftChain_run 0 2, rightChain_run 0 2⟩

theorem promoted_observations :
    0 :: Trees.inorder promotedResidual = Trees.inorder promotedInput ∧
      Trees.inorder promotedResidual = [1, 2, 3] ∧
      promotedResidual.numNodes + 1 = promotedInput.numNodes ∧
      (promotedInput.numNodes = 4 ∧ promotedResidual.numNodes = 3) ∧
      (promotedInput.height = 3 ∧ promotedResidual.height = 2) ∧
      promotedResidual.height ≤ promotedInput.height :=
  ⟨inorder_of_extract? promotedInput 0 promotedResidual promoted_extract, rfl,
    numNodes_of_extract? promotedInput 0 promotedResidual promoted_extract,
    ⟨rfl, rfl⟩, ⟨rfl, rfl⟩,
    height_of_extract? promotedInput 0 promotedResidual promoted_extract⟩

theorem printed_residual_inorder : Trees.inorder printedResidual = [3, 5, 6, 8, 9] := by
  calc
    Trees.inorder printedResidual = (Trees.inorder OrderedTreeExamples.printedTree).tail :=
      (tail_inorder_of_extract? _ _ _ printed_extract).symm
    _ = [3, 5, 6, 8, 9] := congrArg List.tail OrderedTreeExamples.printed_inorder

theorem printed_residual_ordered :
    Trees.Ordered (fun a b : Nat => a < b) printedResidual :=
  ordered_of_extract? _ _ _ _ OrderedTreeExamples.printed_ordered printed_extract

theorem printed_minimum :
    IsLeast {q | q ∈ Trees.inorder OrderedTreeExamples.printedTree} 2 := by
  simpa only [List.map_id] using isLeast_key_of_extract? id
    OrderedTreeExamples.printedTree 2 printedResidual
    OrderedTreeExamples.printed_ordered printed_extract

theorem printed_strict_tail (b : Nat) (hb : b ∈ Trees.inorder printedResidual) : 2 < b :=
  key_lt_of_extract? id OrderedTreeExamples.printedTree 2 printedResidual
    OrderedTreeExamples.printed_ordered printed_extract b hb

theorem printed_removed_key : 2 ∉ Trees.inorder printedResidual := by
  simpa only [List.map_id] using key_not_mem_of_extract? id
    OrderedTreeExamples.printedTree 2 printedResidual
    OrderedTreeExamples.printed_ordered printed_extract

theorem printed_key_removal (q : Nat) :
    q ∈ Trees.inorder printedResidual ↔
      q ∈ Trees.inorder OrderedTreeExamples.printedTree ∧ q ≠ 2 := by
  simpa only [List.map_id] using mem_key_inorder_iff id
    OrderedTreeExamples.printedTree 2 printedResidual
    OrderedTreeExamples.printed_ordered printed_extract q

theorem printed_size_and_height :
    printedResidual.numNodes + 1 = OrderedTreeExamples.printedTree.numNodes ∧
      printedResidual.numNodes = 5 ∧
      OrderedTreeExamples.printedTree.height = 3 ∧ printedResidual.height = 3 ∧
      printedResidual.height ≤ OrderedTreeExamples.printedTree.height :=
  ⟨numNodes_of_extract? _ _ _ printed_extract, rfl, rfl, rfl,
    height_of_extract? _ _ _ printed_extract⟩

theorem printed_count_bounds :
    1 ≤ entries OrderedTreeExamples.printedTree ∧
      entries OrderedTreeExamples.printedTree ≤ OrderedTreeExamples.printedTree.height ∧
      entries OrderedTreeExamples.printedTree ≤ OrderedTreeExamples.printedTree.numNodes :=
  ⟨one_le_entries _, entries_le_height_of_extract? _ _ _ printed_extract,
    entries_le_numNodes _ (ne_nil_of_extract? _ _ _ printed_extract)⟩

/-- The sharper successful-input bound would be false on the selected nil extension. -/
theorem nil_count_boundary :
    entries (.nil : BinaryTree α) = 1 ∧
      ¬ entries (.nil : BinaryTree α) ≤ (BinaryTree.nil : BinaryTree α).height ∧
      entries (.nil : BinaryTree α) ≤ (BinaryTree.nil : BinaryTree α).height + 1 :=
  ⟨entries_nil, by decide, entries_le_height_add_one _⟩

/-- No equality law is needed for the exact Boolean lookup test. -/
theorem lookup_cons_of_extract [BEq κ] (t : BinaryTree (κ × β))
    (k : κ) (v : β) (r : BinaryTree (κ × β))
    (h : extract? t = some ((k, v), r)) (q : κ) :
    (Trees.inorder t).lookup q =
      (match q == k with | true => some v | false => (Trees.inorder r).lookup q) :=
  congrArg (fun xs : List (κ × β) => xs.lookup q)
    (inorder_of_extract? t (k, v) r h).symm

theorem lookup_extracted_value [BEq κ] [ReflBEq κ] (t : BinaryTree (κ × β))
    (k : κ) (v : β) (r : BinaryTree (κ × β))
    (h : extract? t = some ((k, v), r)) : (Trees.inorder t).lookup k = some v := by
  rw [← inorder_of_extract? t (k, v) r h]
  exact List.lookup_cons_self

/-- Absence uses strict key order and a lawful interpretation of the Boolean test. -/
theorem lookup_removed_key [Preorder κ] [BEq κ] [LawfulBEq κ]
    (t : BinaryTree (κ × β)) (k : κ) (v : β) (r : BinaryTree (κ × β))
    (ht : Trees.Ordered (fun a b : κ × β => a.1 < b.1) t)
    (h : extract? t = some ((k, v), r)) : (Trees.inorder r).lookup k = none := by
  apply List.lookup_eq_none_iff.mpr
  intro p hp
  have hne : k ≠ p.1 := by
    intro hk
    exact key_not_mem_of_extract? Prod.fst t (k, v) r ht h
      (List.mem_map.mpr ⟨p, hp, hk.symm⟩)
  simpa only [bne_iff_ne] using hne

theorem tagged_lookup_observations :
    (Trees.inorder OrderedTreeExamples.taggedTree).lookup 0 = some false ∧
      (Trees.inorder taggedResidual).lookup 0 = none ∧
      (Trees.inorder taggedResidual).lookup 1 = some true ∧
      (Trees.inorder taggedResidual).lookup 2 = some false := by
  have h1 := lookup_cons_of_extract OrderedTreeExamples.taggedTree
    0 false taggedResidual tagged_extract 1
  have h2 := lookup_cons_of_extract OrderedTreeExamples.taggedTree
    0 false taggedResidual tagged_extract 2
  change (Trees.inorder OrderedTreeExamples.taggedTree).lookup 1 =
    (Trees.inorder taggedResidual).lookup 1 at h1
  change (Trees.inorder OrderedTreeExamples.taggedTree).lookup 2 =
    (Trees.inorder taggedResidual).lookup 2 at h2
  refine ⟨lookup_extracted_value _ _ _ _ tagged_extract,
    lookup_removed_key _ _ _ _ OrderedTreeExamples.taggedTree_ordered tagged_extract, ?_, ?_⟩
  · calc
      (Trees.inorder taggedResidual).lookup 1 =
          (Trees.inorder OrderedTreeExamples.taggedTree).lookup 1 := h1.symm
      _ = some true := congrArg (fun xs : List (Nat × Bool) => xs.lookup 1)
        OrderedTreeExamples.taggedTree_inorder
  · calc
      (Trees.inorder taggedResidual).lookup 2 =
          (Trees.inorder OrderedTreeExamples.taggedTree).lookup 2 := h2.symm
      _ = some false := congrArg (fun xs : List (Nat × Bool) => xs.lookup 2)
        OrderedTreeExamples.taggedTree_inorder

theorem tagged_residual_ordered :
    Trees.Ordered (fun p q : Nat × Bool => p.1 < q.1) taggedResidual :=
  ordered_of_extract? _ _ _ _ OrderedTreeExamples.taggedTree_ordered tagged_extract

theorem discarded_run :
    run (OrderedTreeExamples.taggedTree.map OrderedTreeExamples.discardTag) =
      (some ((0, ()), .node (1, ()) .nil (.node (2, ()) .nil .nil)), 2) := by
  simpa only [tagged_run, Option.map_some] using
    run_map OrderedTreeExamples.discardTag OrderedTreeExamples.taggedTree

theorem discarded_order_boundary :
    ¬ Function.Injective OrderedTreeExamples.discardTag ∧
      Trees.Ordered (fun p q : Nat × Unit => p.1 < q.1)
        (taggedResidual.map OrderedTreeExamples.discardTag) := by
  refine ⟨OrderedTreeExamples.discardTag_not_injective, ?_⟩
  exact (Trees.ordered_map_key_iff Prod.fst Prod.fst OrderedTreeExamples.discardTag
    OrderedTreeExamples.discardTag_preserves_key taggedResidual).2 tagged_residual_ordered

/-- Erase only the outer annotation; the full inner semantic pair survives. -/
theorem outer_annotation_run (t : BinaryTree ((κ × β) × γ)) :
    run (Trees.Cached.erase t) =
      ((run t).1.map (fun p => (p.1.1, Trees.Cached.erase p.2)), (run t).2) := by
  simpa only [Trees.Cached.erase] using
    run_map (Prod.fst : ((κ × β) × γ) → κ × β) t

theorem outer_annotation_success (t : BinaryTree ((κ × β) × γ))
    (entry : κ × β) (tag : γ) (r : BinaryTree ((κ × β) × γ)) (cost : Nat)
    (h : run t = (some ((entry, tag), r), cost)) :
    run (Trees.Cached.erase t) = (some (entry, Trees.Cached.erase r), cost) := by
  rw [outer_annotation_run]
  simp only [h, Option.map_some]

theorem sameKey_boundary :
    (Trees.inorder OrderedTreeExamples.sameKeyRecords).Nodup ∧
      Trees.Ordered OrderedTreeExamples.pairLex OrderedTreeExamples.sameKeyRecords ∧
      ¬ Trees.Ordered (fun p q : Nat × Nat => p.1 < q.1)
        OrderedTreeExamples.sameKeyRecords ∧
      1 ∈ (Trees.inorder sameKeyResidual).map Prod.fst :=
  ⟨OrderedTreeExamples.sameKeyRecords_distinct,
    OrderedTreeExamples.sameKeyRecords_lex_ordered,
    OrderedTreeExamples.sameKeyRecords_not_key_ordered, by decide⟩

theorem projected_duplicate_run :
    run (OrderedTreeExamples.sameKeyRecords.map Prod.fst) =
      (some (1, .node 1 .nil .nil), 1) := by
  simpa only [sameKey_run, Option.map_some] using
    run_map (Prod.fst : Nat × Nat → Nat) OrderedTreeExamples.sameKeyRecords

theorem duplicate_occurrence_laws :
    1 :: Trees.inorder (BinaryTree.node 1 .nil .nil) =
        Trees.inorder (OrderedTreeExamples.sameKeyRecords.map Prod.fst) ∧
      (BinaryTree.node (1 : Nat) .nil .nil).numNodes + 1 =
        (OrderedTreeExamples.sameKeyRecords.map Prod.fst).numNodes := by
  have h : extract? (OrderedTreeExamples.sameKeyRecords.map Prod.fst) =
      some (1, .node 1 .nil .nil) := congrArg Prod.fst projected_duplicate_run
  exact ⟨inorder_of_extract? _ _ _ h, numNodes_of_extract? _ _ _ h⟩

/-- This is exactly the failed raw set-difference membership equivalence. -/
theorem duplicate_set_difference_fails :
    ¬ ∀ q : Nat, q ∈ Trees.inorder (BinaryTree.node 1 .nil .nil) ↔
      q ∈ Trees.inorder (OrderedTreeExamples.sameKeyRecords.map Prod.fst) ∧ q ≠ 1 := by
  intro h
  exact ((h 1).1 (by decide)).2 rfl

theorem malformed_boundary :
    2 :: Trees.inorder malformedResidual =
        Trees.inorder (OrderedTreeExamples.three 2 0 1) ∧
      ¬ Trees.Ordered (fun a b : Nat => a < b) (OrderedTreeExamples.three 2 0 1) ∧
      Trees.Ordered (fun a b : Nat => a < b) malformedResidual ∧
      ¬ IsLeast {q | q ∈ Trees.inorder (OrderedTreeExamples.three 2 0 1)} 2 := by
  refine ⟨inorder_of_extract? _ _ _ malformed_extract, ?_, ?_, ?_⟩
  · intro h
    have h20 : (2 : Nat) < 0 := h.2.2.1 2 (by decide)
    omega
  · apply Trees.ordered_of_pairwise_inorder
    decide
  · intro h
    have h20 : (2 : Nat) ≤ 0 := h.2 0 (by decide)
    omega

theorem next_boundary :
    Trees.Ordered OrderedTreeExamples.next nextResidual ∧
      ¬ (∀ b ∈ Trees.inorder nextResidual, OrderedTreeExamples.next 0 b) ∧
      ¬ Transitive OrderedTreeExamples.next := by
  refine ⟨ordered_of_extract? _ _ _ _ OrderedTreeExamples.next_ordered next_extract,
    ?_, OrderedTreeExamples.next_not_transitive⟩
  intro h
  exact (by decide : ¬ OrderedTreeExamples.next 0 2) (h 2 (by decide))

theorem stale_cache_boundary :
    Trees.Cached.Valid 0 TreeCacheExamples.sizeStep TreeCacheExamples.sizeSample ∧
      ¬ Trees.Cached.Valid 0 TreeCacheExamples.sizeStep staleSizeResidual ∧
      staleSizeResidual.numNodes = 3 ∧ Trees.Cached.read 0 staleSizeResidual = 4 := by
  refine ⟨TreeCacheExamples.sizeSample_valid, ?_, rfl, rfl⟩
  intro h
  have hc : (4 : Nat) = 3 := h.2.2
  exact (by decide : (4 : Nat) ≠ 3) hc

theorem sizeSample_erased_run :
    run (Trees.Cached.erase TreeCacheExamples.sizeSample) =
      (some (0, Trees.Cached.erase staleSizeResidual), 2) := by
  simpa only [Trees.Cached.erase, sizeSample_run, Option.map_some] using
    run_map (Prod.fst : Nat × Nat → Nat) TreeCacheExamples.sizeSample

theorem stale_erased_inorder :
    Trees.inorder (Trees.Cached.erase staleSizeResidual) = [1, 2, 3] := by
  have h : extract? (Trees.Cached.erase TreeCacheExamples.sizeSample) =
      some (0, Trees.Cached.erase staleSizeResidual) := congrArg Prod.fst sizeSample_erased_run
  calc
    Trees.inorder (Trees.Cached.erase staleSizeResidual) =
        (Trees.inorder (Trees.Cached.erase TreeCacheExamples.sizeSample)).tail :=
      (tail_inorder_of_extract? _ _ _ h).symm
    _ = [1, 2, 3] := congrArg List.tail
      ((congrArg Trees.inorder TreeCacheExamples.sizeSample_erases).trans
        TreeCacheExamples.sample_inorder)

theorem leftChain_attains_height (n : Nat) (hn : 0 < n) :
    entries (leftChain 0 n) ≤ (leftChain 0 n).height ∧
      entries (leftChain 0 n) = (leftChain 0 n).height := by
  refine ⟨entries_le_height _ (leftChain_ne_nil 0 n hn), ?_⟩
  rw [(chain_entries n hn).1, leftChain_height]

theorem rightChain_arbitrarily_tall (bound : Nat) :
    ∃ t : BinaryTree Nat, Trees.Ordered (fun a b => a < b) t ∧
      bound < t.height ∧ entries t = 1 ∧ entries t ≤ t.height := by
  refine ⟨rightChain 0 (bound + 1), rightChain_ordered 0 (bound + 1), ?_,
    (chain_entries (bound + 1) (by omega)).2,
    entries_le_height _ (rightChain_ne_nil 0 (bound + 1) (by omega))⟩
  rw [rightChain_height]
  omega

end TreeLeftmostExamples
