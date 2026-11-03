import Applications.Trees.Braun
import Examples.TreeShape

/-! Connected Braun shape, payload transport and cached-observation uses.
Independent calculations and source boundaries are recorded in
docs/research/fdsa-braun-shape.md.
-/
set_option autoImplicit false
set_option warningAsError true

namespace BraunShapeExamples
universe u v w
variable {α : Type u} {β : Type v} {γ : Type w}

open TreeCacheExamples TreeShapeExamples

/-- Five nodes with equally sized, left-biased two-node children. -/
def braunFive : BinaryTree Unit := .node () (chain 2) (chain 2)

/-- The same two external-leaf depths, but root child counts three and one. -/
def almostFive : BinaryTree Unit := .node () perfectThree single

/-- Equal root counts do not supply recursively well-shaped children. -/
def badEqualChildren : BinaryTree Nat := .node 1 leftThree leftThree

theorem braunFive_shape :
    braunFive.numNodes = 5 ∧ braunFive.numLeaves = 6 ∧
      braunFive.height = 3 ∧ Trees.minHeight braunFive = 2 :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem almostFive_shape :
    almostFive.numNodes = 5 ∧ almostFive.numLeaves = 6 ∧
      almostFive.height = 3 ∧ Trees.minHeight almostFive = 2 :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem almostFive_almostComplete : Trees.AlmostComplete almostFive := by
  change 3 ≤ 2 + 1
  decide

theorem almostFive_local_size_failure :
    ¬ (perfectThree.numNodes ≤ single.numNodes + 1 ∧
      single.numNodes ≤ perfectThree.numNodes + 1) := by
  change ¬ ((3 : Nat) ≤ 1 + 1 ∧ 1 ≤ 3 + 1)
  decide

theorem erased_five_shapes_ne :
    braunFive.map (fun _ => ()) ≠ almostFive.map (fun _ => ()) := by
  intro h
  have hc := congrArg (fun t : BinaryTree Unit => t.left.numNodes) h
  change (2 : Nat) = 3 at hc
  omega

theorem badEqualChildren_shape :
    badEqualChildren.left.numNodes = 3 ∧
      badEqualChildren.right.numNodes = 3 ∧
      badEqualChildren.height = 4 ∧ Trees.minHeight badEqualChildren = 2 ∧
      ¬ Trees.AlmostComplete badEqualChildren := by
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  change ¬ (4 : Nat) ≤ 2 + 1
  decide

theorem leftThree_not_almostComplete : ¬ Trees.AlmostComplete leftThree := by
  change ¬ (3 : Nat) ≤ 1 + 1
  decide

/-- A singleton admits any actual label; there is no payload typeclass. -/
theorem singleton_braun (a : α) :
    Trees.Braun (BinaryTree.node a .nil .nil) :=
  (Trees.braun_node a .nil .nil).2
    ⟨Or.inl rfl, Trees.braun_nil, Trees.braun_nil⟩

theorem single_braun : Trees.Braun single := singleton_braun ()

theorem chainTwo_braun : Trees.Braun (chain 2) := by
  change Trees.Braun (.node () single (.nil : BinaryTree Unit))
  exact (Trees.braun_node_iff () single .nil).2
    ⟨by decide, by decide, single_braun, Trees.braun_nil⟩

theorem perfectThree_braun : Trees.Braun perfectThree :=
  (Trees.braun_node () single single).2
    ⟨Or.inl rfl, single_braun, single_braun⟩

theorem balancedThree_braun : Trees.Braun balancedThree :=
  (Trees.braun_node 1 (.node 1 .nil .nil) (.node 1 .nil .nil)).2
    ⟨Or.inl rfl, singleton_braun 1, singleton_braun 1⟩

theorem braunFive_braun : Trees.Braun braunFive :=
  (Trees.braun_node () (chain 2) (chain 2)).2
    ⟨Or.inl rfl, chainTwo_braun, chainTwo_braun⟩

theorem rightTwo_not_braun : ¬ Trees.Braun rightTwo := by
  intro h
  have hrl := ((Trees.braun_node_iff () .nil single).1 h).1
  change (1 : Nat) ≤ 0 at hrl
  omega

theorem leftThree_not_braun : ¬ Trees.Braun leftThree := by
  intro h
  have hlr := ((Trees.braun_node_iff 1 leftThree.left leftThree.right).1 h).2.1
  change (2 : Nat) ≤ 0 + 1 at hlr
  omega

theorem sample_not_braun : ¬ Trees.Braun sample := by
  intro h
  have hrl := ((Trees.braun_node_iff 1 sample.left sample.right).1 h).1
  change (2 : Nat) ≤ 1 at hrl
  omega

theorem almostFive_not_braun : ¬ Trees.Braun almostFive := by
  intro h
  have hn := (Trees.braun_node_iff () perfectThree single).1 h
  exact almostFive_local_size_failure
    ⟨hn.2.1, hn.1.trans (Nat.le_succ perfectThree.numNodes)⟩

theorem badEqualChildren_not_braun : ¬ Trees.Braun badEqualChildren := by
  intro h
  exact badEqualChildren_shape.2.2.2.2
    (Trees.braun_almostComplete badEqualChildren h)

theorem repeated_payload_boundary :
    Trees.inorder balancedThree = Trees.inorder leftThree ∧
      Trees.Braun balancedThree ∧ ¬ Trees.Braun leftThree ∧
      balancedThree.height = 2 ∧ leftThree.height = 3 :=
  ⟨same_inorder_different_height.1, balancedThree_braun, leftThree_not_braun,
    same_inorder_different_height.2.1, same_inorder_different_height.2.2⟩

/-- The local constructor allows the opposite orientation from Braun. -/
theorem rightTwo_symmetric_constructor :
    Trees.AlmostComplete rightTwo ∧ ¬ Trees.Braun rightTwo :=
  ⟨Trees.almostComplete_node_of_numNodes_balance () .nil single
      Trees.almostComplete_nil single_almostComplete (by decide) (by decide),
    rightTwo_not_braun⟩

/-- Actual one-larger Nat and Real identities include a nil right child. -/
theorem chainTwo_source_heights :
    (chain 2).height = 2 ∧ Trees.minHeight (chain 2) = 1 ∧
      (chain 2).height = ⌈Real.logb 2 ((1 + 1 : Nat) : Real)⌉₊ + 1 ∧
      Trees.minHeight (chain 2) = ⌊Real.logb 2 ((1 : Nat) : Real)⌋₊ + 1 := by
  have hh : (chain 2).height = Nat.clog 2 (1 + 1) + 1 :=
    Trees.height_node_eq_clog_of_numNodes_succ () single .nil
      single_almostComplete Trees.almostComplete_nil rfl
  have hm : Trees.minHeight (chain 2) = Nat.log 2 1 + 1 :=
    Trees.minHeight_node_eq_log_of_numNodes_succ () single .nil
      single_almostComplete Trees.almostComplete_nil rfl
  exact ⟨hh.trans (by decide), hm.trans (by decide),
    Trees.height_node_eq_ceil_logb_of_numNodes_succ () single .nil
      single_almostComplete Trees.almostComplete_nil rfl,
    Trees.minHeight_node_eq_floor_logb_of_numNodes_succ () single .nil
      single_almostComplete Trees.almostComplete_nil rfl⟩

theorem empty_braun_observations (t : BinaryTree Empty) :
    Trees.Braun t ∧ Trees.AlmostComplete t ∧ t.numNodes = 0 ∧
      t.numLeaves = 1 ∧ t.height = 0 ∧ Trees.minHeight t = 0 := by
  rw [TreeCacheExamples.empty_tree t]
  exact ⟨Trees.braun_nil,
    Trees.braun_almostComplete (.nil : BinaryTree Empty) Trees.braun_nil,
    rfl, rfl, rfl, rfl⟩

/-- Both roundings use the one external leaf of the empty tree. -/
theorem empty_braun_rounding (t : BinaryTree Empty) :
    Nat.log 2 t.numLeaves = 0 ∧ Nat.clog 2 t.numLeaves = 0 ∧
      ⌊Real.logb 2 (t.numLeaves : Real)⌋₊ = 0 ∧
      ⌈Real.logb 2 (t.numLeaves : Real)⌉₊ = 0 := by
  have ht := (empty_braun_observations t).2.1
  have hh := (empty_braun_observations t).2.2.2.2.1
  have hm := (empty_braun_observations t).2.2.2.2.2
  exact ⟨(Trees.minHeight_eq_log_numLeaves t ht).symm.trans hm,
    (Trees.height_eq_clog_numLeaves t ht).symm.trans hh,
    (Trees.minHeight_eq_floor_logb_numLeaves t ht).symm.trans hm,
    (Trees.height_eq_ceil_logb_numLeaves t ht).symm.trans hh⟩

theorem braunFive_almostComplete : Trees.AlmostComplete braunFive :=
  Trees.braun_almostComplete braunFive braunFive_braun

theorem braunFive_rounding :
    Nat.log 2 6 = 2 ∧ Nat.clog 2 6 = 3 ∧
      ⌊Real.logb 2 (6 : Real)⌋₊ = 2 ∧
      ⌈Real.logb 2 (6 : Real)⌉₊ = 3 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [braunFive_shape.2.1, braunFive_shape.2.2.2] using
      (Trees.minHeight_eq_log_numLeaves braunFive braunFive_almostComplete).symm
  · simpa only [braunFive_shape.2.1, braunFive_shape.2.2.1] using
      (Trees.height_eq_clog_numLeaves braunFive braunFive_almostComplete).symm
  · simpa only [braunFive_shape.2.1, braunFive_shape.2.2.2] using
      (Trees.minHeight_eq_floor_logb_numLeaves braunFive braunFive_almostComplete).symm
  · simpa only [braunFive_shape.2.1, braunFive_shape.2.2.1] using
      (Trees.height_eq_ceil_logb_numLeaves braunFive braunFive_almostComplete).symm

theorem braunFive_height_nodes :
    braunFive.height = Nat.clog 2 (braunFive.numNodes + 1) := by
  simpa only [BinaryTree.numLeaves_eq_numNodes_succ] using
    Trees.height_eq_clog_numLeaves braunFive braunFive_almostComplete

/-- The competitor can have an unrelated payload universe and any shape. -/
theorem braunFive_optimal (t : BinaryTree α) (hsize : 5 ≤ t.numNodes) :
    3 ≤ t.height := by
  have hn : braunFive.numNodes ≤ t.numNodes := by
    simpa only [braunFive_shape.1] using hsize
  simpa only [braunFive_shape.2.2.1] using
    Trees.height_optimal braunFive t braunFive_almostComplete hn

/-- Label mapping commutes with inorder while reflecting Braun shape. -/
theorem mapped_observations (f : α → β) (t : BinaryTree α) :
    (Trees.Braun (t.map f) ↔ Trees.Braun t) ∧
      (t.map f).numNodes = t.numNodes ∧
      (t.map f).height = t.height ∧
      Trees.minHeight (t.map f) = Trees.minHeight t ∧
      Trees.inorder (t.map f) = (Trees.inorder t).map f :=
  ⟨Trees.braun_map f t, Trees.numNodes_map f t, Trees.height_map f t,
    Trees.minHeight_map f t, Trees.inorder_map f t⟩

/-- Relabelling and the height comparison have three independent payload types. -/
theorem mapped_braun_optimum (f : α → β) (s : BinaryTree α) (t : BinaryTree γ)
    (hs : Trees.Braun s) (hsize : s.numNodes ≤ t.numNodes) :
    Trees.Braun (s.map f) ∧ (s.map f).height ≤ t.height := by
  have hb := (Trees.braun_map f s).2 hs
  have hn : (s.map f).numNodes ≤ t.numNodes := by
    simpa only [Trees.numNodes_map] using hsize
  exact ⟨hb, Trees.height_optimal (s.map f) t
    (Trees.braun_almostComplete (s.map f) hb) hn⟩

/-- Erased-shape equality also identifies both heights across payload universes. -/
theorem equal_size_braun_observations (s : BinaryTree α) (t : BinaryTree β)
    (hs : Trees.Braun s) (ht : Trees.Braun t) (hsize : s.numNodes = t.numNodes) :
    s.map (fun _ : α => ()) = t.map (fun _ : β => ()) ∧
      s.height = t.height ∧ Trees.minHeight s = Trees.minHeight t := by
  have hshape := Trees.braun_shape_eq s t hs ht hsize
  refine ⟨hshape, ?_, ?_⟩
  · simpa only [Trees.height_map] using congrArg BinaryTree.height hshape
  · simpa only [Trees.minHeight_map] using congrArg Trees.minHeight hshape

/-- A concrete noninjective map connects the two existing three-node fixtures. -/
theorem collapsed_balanced_shape :
    ¬ Function.Injective (fun _ : Nat => ()) ∧
      Trees.Braun (balancedThree.map (fun _ => ())) ∧
      balancedThree.map (fun _ => ()) = perfectThree := by
  have hb := (Trees.braun_map (fun _ : Nat => ()) balancedThree).2 balancedThree_braun
  refine ⟨?_, hb, Trees.braun_eq_of_numNodes_eq
    (balancedThree.map (fun _ => ())) perfectThree hb perfectThree_braun
    ((Trees.numNodes_map (fun _ : Nat => ()) balancedThree).trans rfl)⟩
  intro hf
  have h01 : (0 : Nat) = 1 := hf rfl
  omega

theorem constant_sample_not_braun :
    ¬ Trees.Braun (sample.map (fun _ => ())) := by
  intro h
  exact sample_not_braun ((Trees.braun_map (fun _ : Nat => ()) sample).1 h)

/-- Identical erased shape does not identify semantic Bool payloads. -/
theorem bool_singleton_boundary :
    Trees.Braun (BinaryTree.node false .nil .nil) ∧
      Trees.Braun (BinaryTree.node true .nil .nil) ∧
      (BinaryTree.node false .nil .nil).map (fun _ => ()) =
        (BinaryTree.node true .nil .nil).map (fun _ => ()) ∧
      BinaryTree.node false .nil .nil ≠ BinaryTree.node true .nil .nil ∧
      Trees.inorder (BinaryTree.node false .nil .nil) = [false] ∧
      Trees.inorder (BinaryTree.node true .nil .nil) = [true] :=
  ⟨singleton_braun false, singleton_braun true,
    Trees.braun_shape_eq (.node false .nil .nil) (.node true .nil .nil)
      (singleton_braun false) (singleton_braun true) rfl,
    by decide, rfl, rfl⟩

/-- Erasure forgets annotations, not shape; cache validity is unnecessary. -/
theorem braun_erase_iff (t : BinaryTree (α × β)) :
    Trees.Braun (Trees.Cached.erase t) ↔ Trees.Braun t :=
  Trees.braun_map Prod.fst t

/-- The actual annotation output has exactly the input Braun shape for any algebra. -/
theorem braun_annotate_iff (empty : β) (combine : β → α → β → β)
    (t : BinaryTree α) :
    Trees.Braun (Trees.Cached.annotate empty combine t) ↔ Trees.Braun t := by
  have h := braun_erase_iff (Trees.Cached.annotate empty combine t)
  rw [Trees.Cached.erase_annotate empty combine t] at h
  exact h.symm

/-- The structural and cache claims have separate derivations on the actual output. -/
theorem annotated_size_contract (t : BinaryTree α) (ht : Trees.Braun t) :
    Trees.Braun (Trees.Cached.annotate 0 sizeStep t) ∧
      Trees.Cached.Valid 0 sizeStep (Trees.Cached.annotate 0 sizeStep t) ∧
      Trees.Cached.read 0 (Trees.Cached.annotate 0 sizeStep t) = t.numNodes := by
  refine ⟨(braun_annotate_iff 0 sizeStep t).2 ht,
    Trees.Cached.annotate_valid 0 sizeStep t, ?_⟩
  exact (Trees.Cached.read_annotate 0 sizeStep t).trans (Trees.fold_numNodes t)

/-- An arbitrary existing cache needs its actual validity proof for the reader. -/
theorem cached_shape_and_size (t : BinaryTree (α × Nat))
    (hcache : Trees.Cached.Valid 0 sizeStep t)
    (hshape : Trees.Braun (Trees.Cached.erase t)) :
    Trees.Braun t ∧ Trees.Cached.read 0 t = t.numNodes :=
  ⟨(braun_erase_iff t).1 hshape, TreeCacheExamples.size_reader t hcache⟩

def sizeBraunFive : BinaryTree (Unit × Nat) :=
  Trees.Cached.annotate 0 sizeStep braunFive

theorem sizeBraunFive_contract :
    Trees.Braun sizeBraunFive ∧ Trees.Cached.Valid 0 sizeStep sizeBraunFive ∧
      Trees.Cached.erase sizeBraunFive = braunFive ∧
      Trees.Cached.read 0 sizeBraunFive = 5 := by
  have h := annotated_size_contract braunFive braunFive_braun
  exact ⟨h.1, h.2.1, Trees.Cached.erase_annotate 0 sizeStep braunFive,
    h.2.2.trans braunFive_shape.1⟩

theorem valid_cache_nonBraun :
    Trees.Cached.Valid 0 sizeStep sizeSample ∧ ¬ Trees.Braun sizeSample := by
  refine ⟨sizeSample_valid, ?_⟩
  intro h
  apply sample_not_braun
  simpa only [sizeSample_erases] using (braun_erase_iff sizeSample).2 h

theorem braun_invalid_cache :
    Trees.Braun corrupt.left ∧ ¬ Trees.Cached.Valid 0 sizeStep corrupt.left := by
  refine ⟨singleton_braun (0, 2), ?_⟩
  change ¬ (True ∧ True ∧ (2 : Nat) = 0 + 0 + 1)
  decide

end BraunShapeExamples
