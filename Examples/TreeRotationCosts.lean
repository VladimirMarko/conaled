import Applications.Resources.TreeRotations
import Examples.TreeRotations

/-! Actual local cached-rotation costs. Two zero-cost scalar callbacks give six
helper units. The existing recursive append callback instead gives left work
`2*p+q+9` and right work `p+q+8`, where p and q are the actual fringe cache
lengths. The first returned callback value determines the next left operand.
These counts exclude fringe preparation and an additional wrapper entry.
Source and statement assessment: `docs/research/fdsa-tree-rotations.md`.
-/
set_option autoImplicit false
set_option warningAsError true

namespace TreeRotationCostExamples
universe u
variable {α : Type u}

theorem size_left_cost (A : BinaryTree (α × Nat)) (x : α)
    (B : BinaryTree (α × Nat)) (y : α) (C : BinaryTree (α × Nat)) :
    (Resources.TreeRotations.rebuildLeftRun 0 TreeCacheExamples.sizeRun A x B y C).2 = 6 :=
  Resources.TreeRotations.rebuildLeftRun_cost 0 TreeCacheExamples.sizeRun A x B y C

theorem size_right_cost (A : BinaryTree (α × Nat)) (x : α)
    (B : BinaryTree (α × Nat)) (y : α) (C : BinaryTree (α × Nat)) :
    (Resources.TreeRotations.rebuildRightRun 0 TreeCacheExamples.sizeRun A x B y C).2 = 6 :=
  Resources.TreeRotations.rebuildRightRun_cost 0 TreeCacheExamples.sizeRun A x B y C

theorem height_left_cost (A : BinaryTree (α × Nat)) (x : α)
    (B : BinaryTree (α × Nat)) (y : α) (C : BinaryTree (α × Nat)) :
    (Resources.TreeRotations.rebuildLeftRun 0 TreeCacheExamples.heightRun A x B y C).2 = 6 :=
  Resources.TreeRotations.rebuildLeftRun_cost 0 TreeCacheExamples.heightRun A x B y C

theorem height_right_cost (A : BinaryTree (α × Nat)) (x : α)
    (B : BinaryTree (α × Nat)) (y : α) (C : BinaryTree (α × Nat)) :
    (Resources.TreeRotations.rebuildRightRun 0 TreeCacheExamples.heightRun A x B y C).2 = 6 :=
  Resources.TreeRotations.rebuildRightRun_cost 0 TreeCacheExamples.heightRun A x B y C

/-- The reached bounds are zero for each actual scalar callback invocation. -/
theorem size_left_bound (A : BinaryTree (α × Nat)) (x : α)
    (B : BinaryTree (α × Nat)) (y : α) (C : BinaryTree (α × Nat)) :
    (Resources.TreeRotations.rebuildLeftRun 0 TreeCacheExamples.sizeRun A x B y C).2 ≤ 6 :=
  Resources.TreeRotations.rebuildLeftRun_le 0 TreeCacheExamples.sizeRun A x B y C
    0 0 (Nat.le_refl 0) (Nat.le_refl 0)

theorem size_left_value (A : BinaryTree (α × Nat)) (x : α)
    (B : BinaryTree (α × Nat)) (y : α) (C : BinaryTree (α × Nat)) :
    (Resources.TreeRotations.rebuildLeftRun 0 TreeCacheExamples.sizeRun A x B y C).1 =
      Trees.Cached.rebuildLeft 0 TreeCacheExamples.sizeStep A x B y C :=
  Resources.TreeRotations.rebuildLeftRun_value 0 TreeCacheExamples.sizeStep
    TreeCacheExamples.sizeRun A x B y C rfl rfl

theorem height_left_value (A : BinaryTree (α × Nat)) (x : α)
    (B : BinaryTree (α × Nat)) (y : α) (C : BinaryTree (α × Nat)) :
    (Resources.TreeRotations.rebuildLeftRun 0 TreeCacheExamples.heightRun A x B y C).1 =
      Trees.Cached.rebuildLeft 0 TreeCacheExamples.heightStep A x B y C :=
  Resources.TreeRotations.rebuildLeftRun_value 0 TreeCacheExamples.heightStep
    TreeCacheExamples.heightRun A x B y C rfl rfl

theorem size_left_valid (A : BinaryTree (α × Nat)) (x : α)
    (B : BinaryTree (α × Nat)) (y : α) (C : BinaryTree (α × Nat))
    (hA : Trees.Cached.Valid 0 TreeCacheExamples.sizeStep A)
    (hB : Trees.Cached.Valid 0 TreeCacheExamples.sizeStep B)
    (hC : Trees.Cached.Valid 0 TreeCacheExamples.sizeStep C) :
    Trees.Cached.Valid 0 TreeCacheExamples.sizeStep
      (Resources.TreeRotations.rebuildLeftRun 0 TreeCacheExamples.sizeRun A x B y C).1 :=
  Resources.TreeRotations.rebuildLeftRun_valid 0 TreeCacheExamples.sizeStep
    TreeCacheExamples.sizeRun A x B y C hA hB hC rfl rfl

theorem height_left_valid (A : BinaryTree (α × Nat)) (x : α)
    (B : BinaryTree (α × Nat)) (y : α) (C : BinaryTree (α × Nat))
    (hA : Trees.Cached.Valid 0 TreeCacheExamples.heightStep A)
    (hB : Trees.Cached.Valid 0 TreeCacheExamples.heightStep B)
    (hC : Trees.Cached.Valid 0 TreeCacheExamples.heightStep C) :
    Trees.Cached.Valid 0 TreeCacheExamples.heightStep
      (Resources.TreeRotations.rebuildLeftRun 0 TreeCacheExamples.heightRun A x B y C).1 :=
  Resources.TreeRotations.rebuildLeftRun_valid 0 TreeCacheExamples.heightStep
    TreeCacheExamples.heightRun A x B y C hA hB hC rfl rfl

theorem measured_size_sample :
    let result := Resources.TreeRotations.rebuildLeftRun 0 TreeCacheExamples.sizeRun
      TreeRotationExamples.sizeFringe 1 .nil 1 .nil
    result.2 = 6 ∧ Trees.Cached.Valid 0 TreeCacheExamples.sizeStep result.1 ∧
      Trees.Cached.read 0 result.1 = 3 ∧ Trees.Cached.read 0 result.1 = result.1.numNodes := by
  dsimp only
  have valid := size_left_valid TreeRotationExamples.sizeFringe 1 .nil 1 .nil
    TreeRotationExamples.sizeFringe_valid (Trees.Cached.valid_nil _ _) (Trees.Cached.valid_nil _ _)
  have value := size_left_value TreeRotationExamples.sizeFringe 1 .nil 1 .nil
  exact ⟨size_left_cost _ _ _ _ _, valid,
    (congrArg (Trees.Cached.read 0) value).trans TreeRotationExamples.sizeAfter_read,
    TreeCacheExamples.size_reader _ valid⟩

/-- The local work remains six while the correctly cached height changes from two to three. -/
theorem measured_height_sample :
    let result := Resources.TreeRotations.rebuildLeftRun 0 TreeCacheExamples.heightRun
      TreeRotationExamples.heightFringe 1 .nil 1 .nil
    result.2 = 6 ∧ Trees.Cached.Valid 0 TreeCacheExamples.heightStep result.1 ∧
      Trees.Cached.read 0 TreeRotationExamples.heightBefore = 2 ∧
      Trees.Cached.read 0 result.1 = 3 := by
  dsimp only
  have valid := height_left_valid TreeRotationExamples.heightFringe 1 .nil 1 .nil
    TreeRotationExamples.heightFringe_valid (Trees.Cached.valid_nil _ _) (Trees.Cached.valid_nil _ _)
  have value := height_left_value TreeRotationExamples.heightFringe 1 .nil 1 .nil
  exact ⟨height_left_cost _ _ _ _ _, valid, TreeRotationExamples.original_height_read,
    (congrArg (Trees.Cached.read 0) value).trans TreeRotationExamples.heightAfter_read⟩

private theorem append_callback_value (l : List α) (a : α) (r : List α) :
    (TreeCacheExamples.appendStepRun l a r).1 = TreeCacheExamples.listStep l a r :=
  congrArg Prod.fst (Resources.ListReversal.appendRun_exact l (a :: r))

private theorem append_callback_cost (l : List α) (a : α) (r : List α) :
    (TreeCacheExamples.appendStepRun l a r).2 = l.length + 1 :=
  congrArg Prod.snd (Resources.ListReversal.appendRun_exact l (a :: r))

/-- This is the first executed callback's actual returned list length. -/
private theorem append_callback_length (l : List α) (a : α) (r : List α) :
    (TreeCacheExamples.appendStepRun l a r).1.length = l.length + r.length + 1 := by
  calc
    (TreeCacheExamples.appendStepRun l a r).1.length =
        (TreeCacheExamples.listStep l a r).length :=
      congrArg List.length (append_callback_value l a r)
    _ = l.length + r.length + 1 := by
      change (l ++ (a :: r)).length = l.length + r.length + 1
      simp only [List.length_append, List.length_cons]
      omega

theorem append_left_value (A : BinaryTree (α × List α)) (x : α)
    (B : BinaryTree (α × List α)) (y : α) (C : BinaryTree (α × List α)) :
    (Resources.TreeRotations.rebuildLeftRun [] TreeCacheExamples.appendStepRun A x B y C).1 =
      Trees.Cached.rebuildLeft [] TreeCacheExamples.listStep A x B y C :=
  Resources.TreeRotations.rebuildLeftRun_value [] TreeCacheExamples.listStep
    TreeCacheExamples.appendStepRun A x B y C
    (append_callback_value _ _ _) (append_callback_value _ _ _)

theorem append_right_value (A : BinaryTree (α × List α)) (x : α)
    (B : BinaryTree (α × List α)) (y : α) (C : BinaryTree (α × List α)) :
    (Resources.TreeRotations.rebuildRightRun [] TreeCacheExamples.appendStepRun A x B y C).1 =
      Trees.Cached.rebuildRight [] TreeCacheExamples.listStep A x B y C :=
  Resources.TreeRotations.rebuildRightRun_value [] TreeCacheExamples.listStep
    TreeCacheExamples.appendStepRun A x B y C
    (append_callback_value _ _ _) (append_callback_value _ _ _)

/-- The second append uses the first callback's actual returned list. -/
theorem append_left_cost (A : BinaryTree (α × List α)) (x : α)
    (B : BinaryTree (α × List α)) (y : α) (C : BinaryTree (α × List α)) :
    (Resources.TreeRotations.rebuildLeftRun [] TreeCacheExamples.appendStepRun A x B y C).2 =
      2 * (Trees.Cached.read [] A).length + (Trees.Cached.read [] B).length + 9 := by
  rw [Resources.TreeRotations.rebuildLeftRun_cost,
    append_callback_cost, append_callback_cost, append_callback_length]
  omega

/-- Here the returned inner list is on the right, so the second append traverses A. -/
theorem append_right_cost (A : BinaryTree (α × List α)) (x : α)
    (B : BinaryTree (α × List α)) (y : α) (C : BinaryTree (α × List α)) :
    (Resources.TreeRotations.rebuildRightRun [] TreeCacheExamples.appendStepRun A x B y C).2 =
      (Trees.Cached.read [] A).length + (Trees.Cached.read [] B).length + 8 := by
  rw [Resources.TreeRotations.rebuildRightRun_cost,
    append_callback_cost, append_callback_cost]
  omega

theorem append_left_valid (A : BinaryTree (α × List α)) (x : α)
    (B : BinaryTree (α × List α)) (y : α) (C : BinaryTree (α × List α))
    (hA : Trees.Cached.Valid [] TreeCacheExamples.listStep A)
    (hB : Trees.Cached.Valid [] TreeCacheExamples.listStep B)
    (hC : Trees.Cached.Valid [] TreeCacheExamples.listStep C) :
    Trees.Cached.Valid [] TreeCacheExamples.listStep
      (Resources.TreeRotations.rebuildLeftRun [] TreeCacheExamples.appendStepRun A x B y C).1 :=
  Resources.TreeRotations.rebuildLeftRun_valid [] TreeCacheExamples.listStep
    TreeCacheExamples.appendStepRun A x B y C hA hB hC
    (append_callback_value _ _ _) (append_callback_value _ _ _)

theorem append_right_valid (A : BinaryTree (α × List α)) (x : α)
    (B : BinaryTree (α × List α)) (y : α) (C : BinaryTree (α × List α))
    (hA : Trees.Cached.Valid [] TreeCacheExamples.listStep A)
    (hB : Trees.Cached.Valid [] TreeCacheExamples.listStep B)
    (hC : Trees.Cached.Valid [] TreeCacheExamples.listStep C) :
    Trees.Cached.Valid [] TreeCacheExamples.listStep
      (Resources.TreeRotations.rebuildRightRun [] TreeCacheExamples.appendStepRun A x B y C).1 :=
  Resources.TreeRotations.rebuildRightRun_valid [] TreeCacheExamples.listStep
    TreeCacheExamples.appendStepRun A x B y C hA hB hC
    (append_callback_value _ _ _) (append_callback_value _ _ _)

theorem append_erased_inorder (A : BinaryTree (α × List α)) (x : α)
    (B : BinaryTree (α × List α)) (y : α) (C : BinaryTree (α × List α)) :
    Trees.inorder (Trees.Cached.erase
        (Resources.TreeRotations.rebuildLeftRun [] TreeCacheExamples.appendStepRun A x B y C).1) =
      Trees.inorder (Trees.Cached.erase
        (Resources.TreeRotations.rebuildRightRun [] TreeCacheExamples.appendStepRun A x B y C).1) := by
  rw [append_left_value, append_right_value]
  exact Trees.Cached.inorder_erase_rebuildLeft_eq_rebuildRight
    [] TreeCacheExamples.listStep A x B y C

/-- This agreement concerns reached stored lists; cache validity is a separate premise. -/
theorem append_root_reads_agree (A : BinaryTree (α × List α)) (x : α)
    (B : BinaryTree (α × List α)) (y : α) (C : BinaryTree (α × List α)) :
    Trees.Cached.read []
        (Resources.TreeRotations.rebuildLeftRun [] TreeCacheExamples.appendStepRun A x B y C).1 =
      Trees.Cached.read []
        (Resources.TreeRotations.rebuildRightRun [] TreeCacheExamples.appendStepRun A x B y C).1 := by
  rw [append_left_value, append_right_value]
  apply Trees.Cached.read_rebuildLeft_eq_read_rebuildRight
  simp only [TreeCacheExamples.listStep, List.append_assoc, List.cons_append]

def listFringe (a : α) : BinaryTree (α × List α) :=
  Trees.Cached.annotate [] TreeCacheExamples.listStep (TreeRotationExamples.singletonTree a)

theorem listFringe_valid (a : α) : Trees.Cached.Valid [] TreeCacheExamples.listStep (listFringe a) :=
  Trees.Cached.annotate_valid [] TreeCacheExamples.listStep (TreeRotationExamples.singletonTree a)

theorem listFringe_read (a : α) : Trees.Cached.read [] (listFringe a) = [a] :=
  Trees.Cached.read_annotate [] TreeCacheExamples.listStep (TreeRotationExamples.singletonTree a)

theorem singleton_work (q r s p : α) :
    (Resources.TreeRotations.rebuildLeftRun [] TreeCacheExamples.appendStepRun
        (listFringe q) r (listFringe q) s (listFringe p)).2 = 12 ∧
      (Resources.TreeRotations.rebuildRightRun [] TreeCacheExamples.appendStepRun
        (listFringe q) r (listFringe q) s (listFringe p)).2 = 10 :=
  ⟨append_left_cost _ _ _ _ _, append_right_cost _ _ _ _ _⟩

theorem singleton_left_inorder (q r s p : α) :
    Trees.inorder (Trees.Cached.erase
        (Resources.TreeRotations.rebuildLeftRun [] TreeCacheExamples.appendStepRun
          (listFringe q) r (listFringe q) s (listFringe p)).1) = [q, r, q, s, p] :=
  (congrArg (fun t => Trees.inorder (Trees.Cached.erase t))
    (append_left_value (listFringe q) r (listFringe q) s (listFringe p))).trans
      (Trees.Cached.inorder_erase_rebuildLeft [] TreeCacheExamples.listStep
        (listFringe q) r (listFringe q) s (listFringe p))

theorem singleton_right_inorder (q r s p : α) :
    Trees.inorder (Trees.Cached.erase
        (Resources.TreeRotations.rebuildRightRun [] TreeCacheExamples.appendStepRun
          (listFringe q) r (listFringe q) s (listFringe p)).1) = [q, r, q, s, p] :=
  (append_erased_inorder (listFringe q) r (listFringe q) s (listFringe p)).symm.trans
    (singleton_left_inorder q r s p)

theorem singleton_valid (q r s p : α) :
    Trees.Cached.Valid [] TreeCacheExamples.listStep
        (Resources.TreeRotations.rebuildLeftRun [] TreeCacheExamples.appendStepRun
          (listFringe q) r (listFringe q) s (listFringe p)).1 ∧
      Trees.Cached.Valid [] TreeCacheExamples.listStep
        (Resources.TreeRotations.rebuildRightRun [] TreeCacheExamples.appendStepRun
          (listFringe q) r (listFringe q) s (listFringe p)).1 :=
  ⟨append_left_valid _ _ _ _ _ (listFringe_valid q) (listFringe_valid q) (listFringe_valid p),
    append_right_valid _ _ _ _ _ (listFringe_valid q) (listFringe_valid q) (listFringe_valid p)⟩

theorem chain_left_cost (n : Nat) :
    (Resources.TreeRotations.rebuildLeftRun [] TreeCacheExamples.appendStepRun
      (TreeCacheExamples.chainCache n) () .nil () .nil).2 = 2 * n + 9 := by
  rw [append_left_cost, TreeCacheExamples.chainCache_length]

theorem chain_right_cost (n : Nat) :
    (Resources.TreeRotations.rebuildRightRun [] TreeCacheExamples.appendStepRun
      (TreeCacheExamples.chainCache n) () .nil () .nil).2 = n + 8 := by
  rw [append_right_cost, TreeCacheExamples.chainCache_length]

theorem empty_chain_work :
    (Resources.TreeRotations.rebuildLeftRun [] TreeCacheExamples.appendStepRun
        (TreeCacheExamples.chainCache 0) () .nil () .nil).2 = 9 ∧
      (Resources.TreeRotations.rebuildRightRun [] TreeCacheExamples.appendStepRun
        (TreeCacheExamples.chainCache 0) () .nil () .nil).2 = 8 :=
  ⟨chain_left_cost 0, chain_right_cost 0⟩

theorem chain_valid (n : Nat) :
    Trees.Cached.Valid [] TreeCacheExamples.listStep
        (Resources.TreeRotations.rebuildLeftRun [] TreeCacheExamples.appendStepRun
          (TreeCacheExamples.chainCache n) () .nil () .nil).1 ∧
      Trees.Cached.Valid [] TreeCacheExamples.listStep
        (Resources.TreeRotations.rebuildRightRun [] TreeCacheExamples.appendStepRun
          (TreeCacheExamples.chainCache n) () .nil () .nil).1 :=
  ⟨append_left_valid _ _ _ _ _ (TreeCacheExamples.chainCache_valid n)
      (Trees.Cached.valid_nil _ _) (Trees.Cached.valid_nil _ _),
    append_right_valid _ _ _ _ _ (TreeCacheExamples.chainCache_valid n)
      (Trees.Cached.valid_nil _ _) (Trees.Cached.valid_nil _ _)⟩

theorem chain_erased_values_agree (n : Nat) :
    Trees.inorder (Trees.Cached.erase
        (Resources.TreeRotations.rebuildLeftRun [] TreeCacheExamples.appendStepRun
          (TreeCacheExamples.chainCache n) () .nil () .nil).1) =
      Trees.inorder (Trees.Cached.erase
        (Resources.TreeRotations.rebuildRightRun [] TreeCacheExamples.appendStepRun
          (TreeCacheExamples.chainCache n) () .nil () .nil).1) :=
  append_erased_inorder _ _ _ _ _

/-- The supplied family has valid caches, yet its actual callback work exceeds every constant. -/
theorem chain_work_exceeds (K : Nat) :
    K < (Resources.TreeRotations.rebuildLeftRun [] TreeCacheExamples.appendStepRun
        (TreeCacheExamples.chainCache (K + 1)) () .nil () .nil).2 ∧
      K < (Resources.TreeRotations.rebuildRightRun [] TreeCacheExamples.appendStepRun
        (TreeCacheExamples.chainCache (K + 1)) () .nil () .nil).2 := by
  constructor
  · rw [chain_left_cost]
    omega
  · rw [chain_right_cost]
    omega

end TreeRotationCostExamples
