import Examples.TreeFold

/-! Actual full annotation passes compose measured folds with measured local
cached constructors. Validity and observations concern the returned tree.
They do not execute an erasure or a second recomputation pass. Source and
statement assessment: `docs/research/fdsa-tree-fold-resource.md`.
-/
set_option autoImplicit false
set_option warningAsError true

namespace TreeFoldCacheExamples
open Resources Resources.TreeFold
universe u v
variable {α : Type u} {β : Type v}

/-- One measured fold executes the existing local smart constructor at each node. -/
def annotateRun (entry : Nat) (empty : β)
    (combineRun : β → α → β → Measured β Nat) (t : BinaryTree α) :
    Measured (BinaryTree (α × β)) Nat :=
  run entry .nil (TreeCache.nodeRun empty combineRun) t

/-- A sufficient callback value law identifies the actual returned annotation. -/
theorem annotate_value (entry : Nat) (empty : β)
    (combineRun : β → α → β → Measured β Nat) (combine : β → α → β → β)
    (hvalue : ∀ l a r, (combineRun l a r).1 = combine l a r) (t : BinaryTree α) :
    (annotateRun entry empty combineRun t).1 = Trees.Cached.annotate empty combine t := by
  simpa only [annotateRun, Trees.Cached.annotate] using
    run_value_of entry (BinaryTree.nil : BinaryTree (α × β))
      (TreeCache.nodeRun empty combineRun) (Trees.Cached.smartNode empty combine)
      (fun l a r => TreeCache.nodeRun_value empty combine combineRun l a r
        (hvalue (Trees.Cached.read empty l) a (Trees.Cached.read empty r))) t

theorem annotate_valid (entry : Nat) (empty : β)
    (combineRun : β → α → β → Measured β Nat) (combine : β → α → β → β)
    (hvalue : ∀ l a r, (combineRun l a r).1 = combine l a r) (t : BinaryTree α) :
    Trees.Cached.Valid empty combine (annotateRun entry empty combineRun t).1 := by
  rw [annotate_value entry empty combineRun combine hvalue]
  exact Trees.Cached.annotate_valid empty combine t

theorem annotate_erases (entry : Nat) (empty : β)
    (combineRun : β → α → β → Measured β Nat) (combine : β → α → β → β)
    (hvalue : ∀ l a r, (combineRun l a r).1 = combine l a r) (t : BinaryTree α) :
    Trees.Cached.erase (annotateRun entry empty combineRun t).1 = t := by
  rw [annotate_value entry empty combineRun combine hvalue]
  exact Trees.Cached.erase_annotate empty combine t

theorem annotate_read (entry : Nat) (empty : β)
    (combineRun : β → α → β → Measured β Nat) (combine : β → α → β → β)
    (hvalue : ∀ l a r, (combineRun l a r).1 = combine l a r) (t : BinaryTree α) :
    Trees.Cached.read empty (annotateRun entry empty combineRun t).1 =
      Trees.fold empty combine t := by
  rw [Trees.Cached.read_eq_fold empty combine _
    (annotate_valid entry empty combineRun combine hvalue t),
    annotate_erases entry empty combineRun combine hvalue]

theorem size_cost (entry : Nat) (t : BinaryTree α) :
    (annotateRun entry 0 TreeCacheExamples.sizeRun t).2 =
      entry * (2 * t.numNodes + 1) + 3 * t.numNodes := by
  simpa only [annotateRun] using
    run_cost_const entry (BinaryTree.nil : BinaryTree (α × Nat))
      (TreeCache.nodeRun 0 TreeCacheExamples.sizeRun) 3
      (fun _ a _ => TreeCacheExamples.size_node_cost _ a _) t

theorem height_cost (entry : Nat) (t : BinaryTree α) :
    (annotateRun entry 0 TreeCacheExamples.heightRun t).2 =
      entry * (2 * t.numNodes + 1) + 3 * t.numNodes := by
  simpa only [annotateRun] using
    run_cost_const entry (BinaryTree.nil : BinaryTree (α × Nat))
      (TreeCache.nodeRun 0 TreeCacheExamples.heightRun) 3
      (fun _ a _ => TreeCacheExamples.height_node_cost _ a _) t

theorem size_cost_one (t : BinaryTree α) :
    (annotateRun 1 0 TreeCacheExamples.sizeRun t).2 = 5 * t.numNodes + 1 := by
  rw [size_cost]
  ring

theorem height_cost_one (t : BinaryTree α) :
    (annotateRun 1 0 TreeCacheExamples.heightRun t).2 = 5 * t.numNodes + 1 := by
  rw [height_cost]
  ring

theorem size_read (entry : Nat) (t : BinaryTree α) :
    Trees.Cached.read 0 (annotateRun entry 0 TreeCacheExamples.sizeRun t).1 =
      t.numNodes := by
  rw [annotate_read entry 0 TreeCacheExamples.sizeRun TreeCacheExamples.sizeStep
    (fun _ _ _ => rfl)]
  exact Trees.fold_numNodes t

theorem height_read (entry : Nat) (t : BinaryTree α) :
    Trees.Cached.read 0 (annotateRun entry 0 TreeCacheExamples.heightRun t).1 =
      t.height := by
  rw [annotate_read entry 0 TreeCacheExamples.heightRun TreeCacheExamples.heightStep
    (fun _ _ _ => rfl)]
  exact Trees.fold_height t

theorem size_sample_value (entry : Nat) :
    (annotateRun entry 0 TreeCacheExamples.sizeRun TreeCacheExamples.sample).1 =
      TreeCacheExamples.sizeSample :=
  annotate_value entry 0 TreeCacheExamples.sizeRun TreeCacheExamples.sizeStep
    (fun _ _ _ => rfl) TreeCacheExamples.sample

theorem height_sample_value (entry : Nat) :
    (annotateRun entry 0 TreeCacheExamples.heightRun TreeCacheExamples.sample).1 =
      TreeCacheExamples.heightSample :=
  annotate_value entry 0 TreeCacheExamples.heightRun TreeCacheExamples.heightStep
    (fun _ _ _ => rfl) TreeCacheExamples.sample

theorem size_sample :
    annotateRun 1 0 TreeCacheExamples.sizeRun TreeCacheExamples.sample =
      (TreeCacheExamples.sizeSample, 21) := by
  apply Prod.ext
  · exact size_sample_value 1
  · rw [size_cost_one, TreeCacheExamples.sample_size]

theorem height_sample :
    annotateRun 1 0 TreeCacheExamples.heightRun TreeCacheExamples.sample =
      (TreeCacheExamples.heightSample, 21) := by
  apply Prod.ext
  · exact height_sample_value 1
  · rw [height_cost_one, TreeCacheExamples.sample_size]

theorem list_value (entry : Nat) (t : BinaryTree α) :
    (annotateRun entry [] TreeCacheExamples.appendStepRun t).1 =
      Trees.Cached.annotate [] TreeCacheExamples.listStep t :=
  annotate_value entry [] TreeCacheExamples.appendStepRun TreeCacheExamples.listStep
    TreeFoldExamples.single_step_value t

/-- Recursive validity and erasure connect the actual child read to its input. -/
theorem list_read (entry : Nat) (t : BinaryTree α) :
    Trees.Cached.read [] (annotateRun entry [] TreeCacheExamples.appendStepRun t).1 =
      Trees.inorder t :=
  annotate_read entry [] TreeCacheExamples.appendStepRun TreeCacheExamples.listStep
    TreeFoldExamples.single_step_value t

theorem list_nil_cost (entry : Nat) :
    (annotateRun entry [] TreeCacheExamples.appendStepRun (.nil : BinaryTree α)).2 =
      entry := rfl

/-- The existing local cost already includes its three helper charges. -/
theorem list_node_cost (entry : Nat) (a : α) (l r : BinaryTree α) :
    (annotateRun entry [] TreeCacheExamples.appendStepRun (.node a l r)).2 =
      ((annotateRun entry [] TreeCacheExamples.appendStepRun l).2 +
        ((annotateRun entry [] TreeCacheExamples.appendStepRun r).2 +
          (l.numNodes + 4))) + entry := by
  have hread : Trees.Cached.read []
      (run entry .nil (TreeCache.nodeRun [] TreeCacheExamples.appendStepRun) l).1 =
        Trees.inorder l := list_read entry l
  have h := run_node_cost entry .nil
    (TreeCache.nodeRun [] TreeCacheExamples.appendStepRun) a l r
  rw [TreeCacheExamples.append_node_cost, hread, Trees.inorder_length] at h
  simpa only [annotateRun] using h

theorem list_sample_work :
    (annotateRun 1 [] TreeCacheExamples.appendStepRun TreeCacheExamples.sample).2 =
      27 := by
  simp only [TreeCacheExamples.sample, list_node_cost, list_nil_cost, BinaryTree.numNodes]

theorem list_sample_read :
    Trees.Cached.read []
      (annotateRun 1 [] TreeCacheExamples.appendStepRun TreeCacheExamples.sample).1 =
      [0, 1, 2, 3] := by
  rw [list_read, TreeCacheExamples.sample_inorder]

theorem empty_annotation (entry : Nat) (empty : β)
    (combineRun : β → Empty → β → Measured β Nat) (t : BinaryTree Empty) :
    annotateRun entry empty combineRun t = (.nil, entry) := by
  simpa only [annotateRun] using
    TreeFoldExamples.empty_run entry (BinaryTree.nil : BinaryTree (Empty × β))
      (TreeCache.nodeRun empty combineRun) t

end TreeFoldCacheExamples
