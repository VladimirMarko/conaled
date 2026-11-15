import Examples.TreeCache

/-! Generic cache-node clients for FDSA C04-073. The callbacks charge two
unit primitive operations (two additions, or max and successor). These are
declared operation tariffs, not machine-time or bit-complexity claims. -/

namespace CTB23Tariff
universe u
variable {α : Type u}

theorem size_value (l : BinaryTree (α × Nat)) (a : α) (r : BinaryTree (α × Nat)) :
    (Resources.TreeCache.nodeRun 0
      (fun x a y => (TreeCacheExamples.sizeStep x a y, 2)) l a r).1 =
      Trees.Cached.smartNode 0 TreeCacheExamples.sizeStep l a r :=
  Resources.TreeCache.nodeRun_value 0 TreeCacheExamples.sizeStep
    (fun x a y => (TreeCacheExamples.sizeStep x a y, 2)) l a r rfl

theorem size_cost (l : BinaryTree (α × Nat)) (a : α) (r : BinaryTree (α × Nat)) :
    (Resources.TreeCache.nodeRun 0
      (fun x a y => (TreeCacheExamples.sizeStep x a y, 2)) l a r).2 = 5 := by
  simpa using (Resources.TreeCache.nodeRun_cost 0
    (fun x a y => (TreeCacheExamples.sizeStep x a y, 2)) l a r)

theorem size_valid (l : BinaryTree (α × Nat)) (a : α) (r : BinaryTree (α × Nat))
    (hl : Trees.Cached.Valid 0 TreeCacheExamples.sizeStep l)
    (hr : Trees.Cached.Valid 0 TreeCacheExamples.sizeStep r) :
    Trees.Cached.Valid 0 TreeCacheExamples.sizeStep
      (Resources.TreeCache.nodeRun 0
        (fun x a y => (TreeCacheExamples.sizeStep x a y, 2)) l a r).1 :=
  Resources.TreeCache.nodeRun_valid 0 TreeCacheExamples.sizeStep
    (fun x a y => (TreeCacheExamples.sizeStep x a y, 2)) l a r hl hr rfl

theorem height_value (l : BinaryTree (α × Nat)) (a : α) (r : BinaryTree (α × Nat)) :
    (Resources.TreeCache.nodeRun 0
      (fun x a y => (TreeCacheExamples.heightStep x a y, 2)) l a r).1 =
      Trees.Cached.smartNode 0 TreeCacheExamples.heightStep l a r :=
  Resources.TreeCache.nodeRun_value 0 TreeCacheExamples.heightStep
    (fun x a y => (TreeCacheExamples.heightStep x a y, 2)) l a r rfl

theorem height_cost (l : BinaryTree (α × Nat)) (a : α) (r : BinaryTree (α × Nat)) :
    (Resources.TreeCache.nodeRun 0
      (fun x a y => (TreeCacheExamples.heightStep x a y, 2)) l a r).2 = 5 := by
  simpa using (Resources.TreeCache.nodeRun_cost 0
    (fun x a y => (TreeCacheExamples.heightStep x a y, 2)) l a r)

theorem height_valid (l : BinaryTree (α × Nat)) (a : α) (r : BinaryTree (α × Nat))
    (hl : Trees.Cached.Valid 0 TreeCacheExamples.heightStep l)
    (hr : Trees.Cached.Valid 0 TreeCacheExamples.heightStep r) :
    Trees.Cached.Valid 0 TreeCacheExamples.heightStep
      (Resources.TreeCache.nodeRun 0
        (fun x a y => (TreeCacheExamples.heightStep x a y, 2)) l a r).1 :=
  Resources.TreeCache.nodeRun_valid 0 TreeCacheExamples.heightStep
    (fun x a y => (TreeCacheExamples.heightStep x a y, 2)) l a r hl hr rfl

end CTB23Tariff
