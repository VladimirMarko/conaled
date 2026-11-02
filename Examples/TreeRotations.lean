import Applications.Trees.CachedRotations
import Examples.TreeCache

/-! Connected ordinary and cached root-rotation cases. The independent word
expectation is `[q,r,q,s,p]`; the existing balanced three-node tree rotates to
the existing left chain, changing height from two to three. Rebuilding cached
nodes changes their annotations while preserving erased payload observations.
Source, scope and statement assessment: `docs/research/fdsa-tree-rotations.md`.
-/
set_option autoImplicit false
set_option warningAsError true

namespace TreeRotationExamples
universe u v
variable {α : Type u}

def singletonTree (a : α) : BinaryTree α := .node a .nil .nil

/-- Every fringe is nonempty and the payload q occurs twice. -/
def fiveBefore (q r s p : α) : BinaryTree α :=
  .node r (singletonTree q) (.node s (singletonTree q) (singletonTree p))

def fiveAfter (q r s p : α) : BinaryTree α :=
  .node s (.node r (singletonTree q) (singletonTree q)) (singletonTree p)

theorem fiveBefore_inorder (q r s p : α) :
    Trees.inorder (fiveBefore q r s p) = [q, r, q, s, p] := rfl

theorem fiveBefore_size (q r s p : α) : (fiveBefore q r s p).numNodes = 5 := rfl

theorem fiveBefore_leaves (q r s p : α) : (fiveBefore q r s p).numLeaves = 6 := rfl

theorem five_left (q r s p : α) :
    Trees.rotateLeft? (fiveBefore q r s p) = some (fiveAfter q r s p) :=
  Trees.rotateLeft?_node_node (singletonTree q) r (singletonTree q) s (singletonTree p)

theorem five_right (q r s p : α) :
    Trees.rotateRight? (fiveAfter q r s p) = some (fiveBefore q r s p) :=
  Trees.rotateRight?_of_rotateLeft? _ _ (five_left q r s p)

theorem fiveAfter_inorder (q r s p : α) :
    Trees.inorder (fiveAfter q r s p) = [q, r, q, s, p] :=
  (Trees.inorder_of_rotateLeft? _ _ (five_left q r s p)).trans
    (fiveBefore_inorder q r s p)

theorem fiveAfter_size (q r s p : α) : (fiveAfter q r s p).numNodes = 5 :=
  (Trees.numNodes_of_rotateLeft? _ _ (five_left q r s p)).trans
    (fiveBefore_size q r s p)

theorem fiveAfter_leaves (q r s p : α) : (fiveAfter q r s p).numLeaves = 6 :=
  (Trees.numLeaves_of_rotateLeft? _ _ (five_left q r s p)).trans
    (fiveBefore_leaves q r s p)

/-- Collapsing all payloads does not change the rotation's shape or domain. -/
theorem five_constant_map (q r s p : α) :
    Trees.rotateLeft? ((fiveBefore q r s p).map (fun _ => ())) =
      some ((fiveAfter q r s p).map (fun _ => ())) := by
  rw [← Trees.map_rotateLeft? (fun _ : α => ()) (fiveBefore q r s p), five_left]

theorem five_constant_inorder (q r s p : α) :
    Trees.inorder ((fiveAfter q r s p).map (fun _ => ())) = [(), (), (), (), ()] :=
  (Trees.inorder_map (fun _ : α => ()) (fiveAfter q r s p)).trans
    (congrArg (List.map (fun _ : α => ())) (fiveAfter_inorder q r s p))

theorem five_constant_size (q r s p : α) :
    ((fiveAfter q r s p).map (fun _ => ())).numNodes = 5 :=
  (Trees.numNodes_map (fun _ : α => ()) (fiveAfter q r s p)).trans
    (fiveAfter_size q r s p)

theorem empty_payload (t : BinaryTree Empty) :
    Trees.rotateLeft? t = none ∧ Trees.rotateRight? t = none := by
  rw [TreeCacheExamples.empty_tree t]
  exact ⟨Trees.rotateLeft?_nil, Trees.rotateRight?_nil⟩

theorem missing_pivots (A : BinaryTree α) (x y : α) (C : BinaryTree α) :
    Trees.rotateLeft? (.node x A .nil) = none ∧
      Trees.rotateRight? (.node y .nil C) = none :=
  ⟨Trees.rotateLeft?_node_nil A x, Trees.rotateRight?_nil_node y C⟩

theorem two_pivot_empty_fringe (x y : α) :
    Trees.rotateLeft? (.node x .nil (.node y .nil .nil)) =
        some (.node y (.node x .nil .nil) .nil) ∧
      Trees.inorder (.node y (.node x .nil .nil) .nil) = [x, y] ∧
      (BinaryTree.node y (.node x .nil .nil) .nil).numNodes = 2 ∧
      (BinaryTree.node y (.node x .nil .nil) .nil).numLeaves = 3 := by
  have rotated := Trees.rotateLeft?_node_node .nil x .nil y .nil
  exact ⟨rotated, (Trees.inorder_of_rotateLeft? _ _ rotated).trans rfl,
    (Trees.numNodes_of_rotateLeft? _ _ rotated).trans rfl,
    (Trees.numLeaves_of_rotateLeft? _ _ rotated).trans rfl⟩

section Ordered
variable {M : Type v} [Monoid M]

/-- Associativity discharges the reached fold law; multiplication order is retained. -/
theorem monoid_fold_left (measure : α → M) (A : BinaryTree α) (x : α)
    (B : BinaryTree α) (y : α) (C : BinaryTree α) :
    Trees.fold 1 (fun l a r => l * measure a * r) (.node y (.node x A B) C) =
      Trees.fold 1 (fun l a r => l * measure a * r) (.node x A (.node y B C)) := by
  apply Trees.fold_rotateLeft 1 (fun l a r => l * measure a * r) A x B y C
  simp only [mul_assoc]

/-- The existing full-inorder/summary bridge composes with the local fold law. -/
theorem monoid_summary_left (measure : α → M) (A : BinaryTree α) (x : α)
    (B : BinaryTree α) (y : α) (C : BinaryTree α) :
    Sequences.OrderedSummary.summary measure (Trees.inorder (.node y (.node x A B) C)) =
      Sequences.OrderedSummary.summary measure (Trees.inorder (.node x A (.node y B C))) := by
  rw [TreeCacheExamples.ordered_summary_fold, TreeCacheExamples.ordered_summary_fold]
  exact monoid_fold_left measure A x B y C

end Ordered

theorem five_word (q r s p : α) :
    Trees.fold (1 : FreeMonoid α) (fun l a r => l * FreeMonoid.of a * r)
      (fiveAfter q r s p) = FreeMonoid.ofList [q, r, q, s, p] := by
  calc
    Trees.fold (1 : FreeMonoid α) (fun l a r => l * FreeMonoid.of a * r)
        (fiveAfter q r s p) =
        Sequences.OrderedSummary.summary FreeMonoid.of (Trees.inorder (fiveAfter q r s p)) :=
      (TreeCacheExamples.ordered_summary_fold FreeMonoid.of (fiveAfter q r s p)).symm
    _ = Sequences.OrderedSummary.summary FreeMonoid.of (Trees.inorder (fiveBefore q r s p)) :=
      monoid_summary_left FreeMonoid.of (singletonTree q) r (singletonTree q) s (singletonTree p)
    _ = Sequences.OrderedSummary.summary FreeMonoid.of [q, r, q, s, p] :=
      congrArg (Sequences.OrderedSummary.summary FreeMonoid.of) (fiveBefore_inorder q r s p)
    _ = FreeMonoid.ofList [q, r, q, s, p] := by
      change Sequences.OrderedSummary.summary FreeMonoid.of
        ([q] ++ ([r] ++ ([q] ++ ([s] ++ [p])))) = _
      simp only [Sequences.OrderedSummary.summary_append,
        Sequences.OrderedSummary.summary_singleton]

theorem balanced_left :
    Trees.rotateLeft? TreeCacheExamples.balancedThree = some TreeCacheExamples.leftThree :=
  Trees.rotateLeft?_node_node (singletonTree 1) 1 .nil 1 .nil

/-- This legal rotation preserves the word but increases height. -/
theorem balanced_rotation_boundary :
    Trees.rotateLeft? TreeCacheExamples.balancedThree = some TreeCacheExamples.leftThree ∧
      Trees.inorder TreeCacheExamples.leftThree = Trees.inorder TreeCacheExamples.balancedThree ∧
      TreeCacheExamples.balancedThree.height = 2 ∧ TreeCacheExamples.leftThree.height = 3 :=
  ⟨balanced_left, Trees.inorder_of_rotateLeft? _ _ balanced_left,
    TreeCacheExamples.same_inorder_different_height.2.1,
    TreeCacheExamples.same_inorder_different_height.2.2⟩

theorem height_fold_not_preserved :
    Trees.fold 0 TreeCacheExamples.heightStep TreeCacheExamples.balancedThree ≠
      Trees.fold 0 TreeCacheExamples.heightStep TreeCacheExamples.leftThree := by
  change Trees.fold 0 (fun l (_ : Nat) r => max l r + 1) TreeCacheExamples.balancedThree ≠
    Trees.fold 0 (fun l (_ : Nat) r => max l r + 1) TreeCacheExamples.leftThree
  rw [Trees.fold_height, Trees.fold_height]
  decide

/-- The original valid size cache, before changing its shape. -/
def sizeBefore : BinaryTree (Nat × Nat) :=
  Trees.Cached.annotate 0 TreeCacheExamples.sizeStep TreeCacheExamples.balancedThree

def sizeFringe : BinaryTree (Nat × Nat) :=
  Trees.Cached.annotate 0 TreeCacheExamples.sizeStep (singletonTree 1)

theorem sizeBefore_valid : Trees.Cached.Valid 0 TreeCacheExamples.sizeStep sizeBefore :=
  Trees.Cached.annotate_valid 0 TreeCacheExamples.sizeStep TreeCacheExamples.balancedThree

theorem sizeFringe_valid : Trees.Cached.Valid 0 TreeCacheExamples.sizeStep sizeFringe :=
  Trees.Cached.annotate_valid 0 TreeCacheExamples.sizeStep (singletonTree 1)

def heightBefore : BinaryTree (Nat × Nat) :=
  Trees.Cached.annotate 0 TreeCacheExamples.heightStep TreeCacheExamples.balancedThree

def heightFringe : BinaryTree (Nat × Nat) :=
  Trees.Cached.annotate 0 TreeCacheExamples.heightStep (singletonTree 1)

theorem heightBefore_valid :
    Trees.Cached.Valid 0 TreeCacheExamples.heightStep heightBefore :=
  Trees.Cached.annotate_valid 0 TreeCacheExamples.heightStep TreeCacheExamples.balancedThree

theorem heightFringe_valid :
    Trees.Cached.Valid 0 TreeCacheExamples.heightStep heightFringe :=
  Trees.Cached.annotate_valid 0 TreeCacheExamples.heightStep (singletonTree 1)

def sizeAfter : BinaryTree (Nat × Nat) :=
  Trees.Cached.rebuildLeft 0 TreeCacheExamples.sizeStep sizeFringe 1 .nil 1 .nil

def heightAfter : BinaryTree (Nat × Nat) :=
  Trees.Cached.rebuildLeft 0 TreeCacheExamples.heightStep heightFringe 1 .nil 1 .nil

theorem sizeAfter_valid : Trees.Cached.Valid 0 TreeCacheExamples.sizeStep sizeAfter :=
  (Trees.Cached.rebuildLeft_valid_iff 0 TreeCacheExamples.sizeStep sizeFringe 1 .nil 1 .nil).2
    ⟨sizeFringe_valid, Trees.Cached.valid_nil _ _, Trees.Cached.valid_nil _ _⟩

theorem heightAfter_valid : Trees.Cached.Valid 0 TreeCacheExamples.heightStep heightAfter :=
  (Trees.Cached.rebuildLeft_valid_iff 0 TreeCacheExamples.heightStep heightFringe 1 .nil 1 .nil).2
    ⟨heightFringe_valid, Trees.Cached.valid_nil _ _, Trees.Cached.valid_nil _ _⟩

theorem sizeAfter_erases : Trees.Cached.erase sizeAfter = TreeCacheExamples.leftThree := by
  rw [sizeAfter, Trees.Cached.erase_rebuildLeft, sizeFringe, Trees.Cached.erase_annotate]

theorem heightAfter_erases : Trees.Cached.erase heightAfter = TreeCacheExamples.leftThree := by
  rw [heightAfter, Trees.Cached.erase_rebuildLeft, heightFringe, Trees.Cached.erase_annotate]

theorem sizeAfter_read : Trees.Cached.read 0 sizeAfter = 3 := by
  calc
    Trees.Cached.read 0 sizeAfter = sizeAfter.numNodes :=
      TreeCacheExamples.size_reader sizeAfter sizeAfter_valid
    _ = (Trees.Cached.erase sizeAfter).numNodes := (Trees.Cached.numNodes_erase sizeAfter).symm
    _ = 3 := congrArg BinaryTree.numNodes sizeAfter_erases

theorem heightAfter_read : Trees.Cached.read 0 heightAfter = 3 := by
  calc
    Trees.Cached.read 0 heightAfter = heightAfter.height :=
      TreeCacheExamples.height_reader heightAfter heightAfter_valid
    _ = (Trees.Cached.erase heightAfter).height := (Trees.Cached.height_erase heightAfter).symm
    _ = 3 := (congrArg BinaryTree.height heightAfter_erases).trans
      TreeCacheExamples.same_inorder_different_height.2.2

theorem repaired_size_tags :
    Trees.Cached.read 0 sizeAfter = 3 ∧ Trees.Cached.read 0 sizeAfter.left = 2 :=
  ⟨sizeAfter_read, rfl⟩

theorem size_payload_inorder :
    Trees.inorder (Trees.Cached.erase sizeAfter) = Trees.inorder (Trees.Cached.erase sizeBefore) :=
  Trees.Cached.inorder_erase_rebuildLeft_eq_rebuildRight
    0 TreeCacheExamples.sizeStep sizeFringe 1 .nil 1 .nil

theorem size_payload_values : Trees.inorder (Trees.Cached.erase sizeAfter) = [1, 1, 1] :=
  size_payload_inorder.trans rfl

/-- The annotated observations change even though the erased payload word agrees. -/
theorem annotation_inorders :
    Trees.inorder sizeBefore = [(1, 1), (1, 3), (1, 1)] ∧
      Trees.inorder sizeAfter = [(1, 1), (1, 2), (1, 3)] := ⟨rfl, rfl⟩

theorem annotation_inorder_changes : Trees.inorder sizeBefore ≠ Trees.inorder sizeAfter := by
  rw [annotation_inorders.1, annotation_inorders.2]
  decide

/-- Merely moving the annotated labels leaves the two pivot tags stale. -/
def staleSizeAfter : BinaryTree (Nat × Nat) :=
  .node (1, 1) (.node (1, 3) (.node (1, 1) .nil .nil) .nil) .nil

theorem raw_size_rotation : Trees.rotateLeft? sizeBefore = some staleSizeAfter :=
  Trees.rotateLeft?_node_node (.node (1, 1) .nil .nil) (1, 3) .nil (1, 1) .nil

theorem stale_tags :
    Trees.Cached.read 0 staleSizeAfter = 1 ∧
    Trees.Cached.read 0 staleSizeAfter.left = 3 ∧
    staleSizeAfter.numNodes = 3 ∧ staleSizeAfter.left.numNodes = 2 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- A valid size cache would read its actual node count; this root does not. -/
theorem stale_not_valid : ¬ Trees.Cached.Valid 0 TreeCacheExamples.sizeStep staleSizeAfter := by
  intro valid
  have root := TreeCacheExamples.size_reader staleSizeAfter valid
  have different : (1 : Nat) ≠ 3 := by decide
  exact different root

theorem original_height_read : Trees.Cached.read 0 heightBefore = 2 := by
  calc
    Trees.Cached.read 0 heightBefore = heightBefore.height :=
      TreeCacheExamples.height_reader heightBefore heightBefore_valid
    _ = (Trees.Cached.erase heightBefore).height :=
      (Trees.Cached.height_erase heightBefore).symm
    _ = 2 := (congrArg BinaryTree.height
      (Trees.Cached.erase_annotate 0 TreeCacheExamples.heightStep
        TreeCacheExamples.balancedThree)).trans
      TreeCacheExamples.same_inorder_different_height.2.1

/-- Repairing either association's roots does not repair a malformed retained fringe. -/
theorem corrupt_fringe_not_repaired :
    ¬ Trees.Cached.Valid 0 TreeCacheExamples.sizeStep
        (Trees.Cached.rebuildLeft 0 TreeCacheExamples.sizeStep
          TreeCacheExamples.corrupt 1 .nil 1 .nil) ∧
      ¬ Trees.Cached.Valid 0 TreeCacheExamples.sizeStep
        (Trees.Cached.rebuildRight 0 TreeCacheExamples.sizeStep
          TreeCacheExamples.corrupt 1 .nil 1 .nil) := by
  constructor
  · intro valid
    exact TreeCacheExamples.corrupt_not_valid
      ((Trees.Cached.rebuildLeft_valid_iff 0 TreeCacheExamples.sizeStep
        TreeCacheExamples.corrupt 1 .nil 1 .nil).1 valid).1
  · intro valid
    exact TreeCacheExamples.corrupt_not_valid
      ((Trees.Cached.rebuildRight_valid_iff 0 TreeCacheExamples.sizeStep
        TreeCacheExamples.corrupt 1 .nil 1 .nil).1 valid).1

end TreeRotationExamples
