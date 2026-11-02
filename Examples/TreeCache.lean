import Applications.Trees.Cached
import Applications.Resources.TreeCache
import Applications.Resources.ListReversal
import Applications.Sequences.OrderedSummary

/-! Connected size, height, ordered-summary and resource uses of cached
node-labelled trees. Independent expectations and statement assessment:
`docs/research/fdsa-tree-cache.md`.
-/
set_option autoImplicit false
set_option warningAsError true

namespace TreeCacheExamples
universe u v w
variable {α : Type u}

def sizeStep (l : Nat) (_ : α) (r : Nat) : Nat := l + r + 1
def heightStep (l : Nat) (_ : α) (r : Nat) : Nat := max l r + 1

theorem size_reader (t : BinaryTree (α × Nat))
    (ht : Trees.Cached.Valid 0 sizeStep t) :
    Trees.Cached.read 0 t = t.numNodes := by
  simpa only [sizeStep, Trees.fold_numNodes, Trees.Cached.numNodes_erase] using
    Trees.Cached.read_eq_fold 0 sizeStep t ht

theorem height_reader (t : BinaryTree (α × Nat))
    (ht : Trees.Cached.Valid 0 heightStep t) :
    Trees.Cached.read 0 t = t.height := by
  simpa only [heightStep, Trees.fold_height, Trees.Cached.height_erase] using
    Trees.Cached.read_eq_fold 0 heightStep t ht

/-- The asymmetric source-independent fixture has four nodes and height three. -/
def sample : BinaryTree Nat :=
  .node 1 (.node 0 .nil .nil) (.node 3 (.node 2 .nil .nil) .nil)

theorem sample_size : sample.numNodes = 4 := rfl
theorem sample_height : sample.height = 3 := rfl
theorem sample_inorder : Trees.inorder sample = [0, 1, 2, 3] := rfl

def sizeSample : BinaryTree (Nat × Nat) := Trees.Cached.annotate 0 sizeStep sample

theorem sizeSample_valid : Trees.Cached.Valid 0 sizeStep sizeSample :=
  Trees.Cached.annotate_valid 0 sizeStep sample

theorem sizeSample_erases : Trees.Cached.erase sizeSample = sample :=
  Trees.Cached.erase_annotate 0 sizeStep sample

theorem sizeSample_read : Trees.Cached.read 0 sizeSample = 4 := by
  calc
    Trees.Cached.read 0 sizeSample = sizeSample.numNodes :=
      size_reader sizeSample sizeSample_valid
    _ = (Trees.Cached.erase sizeSample).numNodes :=
      (Trees.Cached.numNodes_erase sizeSample).symm
    _ = 4 := by rw [sizeSample_erases, sample_size]

def heightSample : BinaryTree (Nat × Nat) := Trees.Cached.annotate 0 heightStep sample

theorem heightSample_valid : Trees.Cached.Valid 0 heightStep heightSample :=
  Trees.Cached.annotate_valid 0 heightStep sample

theorem heightSample_read : Trees.Cached.read 0 heightSample = 3 := by
  calc
    Trees.Cached.read 0 heightSample = heightSample.height :=
      height_reader heightSample heightSample_valid
    _ = (Trees.Cached.erase heightSample).height :=
      (Trees.Cached.height_erase heightSample).symm
    _ = sample.height := congrArg BinaryTree.height
      (Trees.Cached.erase_annotate 0 heightStep sample)
    _ = 3 := sample_height

def pairStep (l : Nat × Nat) (_ : α) (r : Nat × Nat) : Nat × Nat :=
  (l.1 + r.1 + 1, max l.2 r.2 + 1)

theorem pair_fold_size (t : BinaryTree α) :
    (Trees.fold (0, 0) pairStep t).1 = t.numNodes := by
  calc
    (Trees.fold (0, 0) pairStep t).1 = Trees.fold 0 sizeStep t :=
      Trees.fold_fusion (0, 0) pairStep 0 sizeStep Prod.fst rfl
        (fun _ _ _ => rfl) t
    _ = t.numNodes := Trees.fold_numNodes t

theorem pair_fold_height (t : BinaryTree α) :
    (Trees.fold (0, 0) pairStep t).2 = t.height := by
  calc
    (Trees.fold (0, 0) pairStep t).2 = Trees.fold 0 heightStep t :=
      Trees.fold_fusion (0, 0) pairStep 0 heightStep Prod.snd rfl
        (fun _ _ _ => rfl) t
    _ = t.height := Trees.fold_height t

/-- The pair cache is validated once; both observations use projection fusion. -/
theorem pair_reader (t : BinaryTree (α × (Nat × Nat)))
    (ht : Trees.Cached.Valid (0, 0) pairStep t) :
    Trees.Cached.read (0, 0) t = (t.numNodes, t.height) := by
  apply Prod.ext
  · rw [Trees.Cached.read_eq_fold (0, 0) pairStep t ht,
      pair_fold_size, Trees.Cached.numNodes_erase]
  · rw [Trees.Cached.read_eq_fold (0, 0) pairStep t ht,
      pair_fold_height, Trees.Cached.height_erase]

def pairSample : BinaryTree (Nat × (Nat × Nat)) :=
  Trees.Cached.annotate (0, 0) pairStep sample

theorem pairSample_valid : Trees.Cached.Valid (0, 0) pairStep pairSample :=
  Trees.Cached.annotate_valid (0, 0) pairStep sample

theorem pairSample_erases : Trees.Cached.erase pairSample = sample :=
  Trees.Cached.erase_annotate (0, 0) pairStep sample

theorem pairSample_read : Trees.Cached.read (0, 0) pairSample = (4, 3) := by
  rw [pair_reader pairSample pairSample_valid,
    ← Trees.Cached.numNodes_erase pairSample, ← Trees.Cached.height_erase pairSample,
    pairSample_erases, sample_size, sample_height]

section Ordered
variable {M : Type v} [Monoid M]

/-- Compose the full ordered observation with the existing sequence summary.
Multiplication is not assumed commutative. -/
theorem ordered_summary_fold (measure : α → M) (t : BinaryTree α) :
    Sequences.OrderedSummary.summary measure (Trees.inorder t) =
      Trees.fold 1 (fun l a r => l * measure a * r) t := by
  change Sequences.OrderedSummary.summary measure
    (Trees.fold [] (fun l a r => l ++ (a :: r)) t) = _
  refine Trees.fold_fusion [] (fun l a r => l ++ (a :: r)) 1
    (fun l a r => l * measure a * r) (Sequences.OrderedSummary.summary measure)
    (Sequences.OrderedSummary.summary_nil measure) ?_ t
  intro l a r
  change Sequences.OrderedSummary.summary measure (l ++ ([a] ++ r)) = _
  rw [Sequences.OrderedSummary.summary_append,
    Sequences.OrderedSummary.summary_append, Sequences.OrderedSummary.summary_singleton]
  exact (mul_assoc _ _ _).symm

end Ordered

theorem sample_word :
    Trees.fold (1 : FreeMonoid Nat) (fun l a r => l * FreeMonoid.of a * r) sample =
      FreeMonoid.ofList [0, 1, 2, 3] := by
  calc
    Trees.fold (1 : FreeMonoid Nat) (fun l a r => l * FreeMonoid.of a * r) sample =
        Sequences.OrderedSummary.summary FreeMonoid.of (Trees.inorder sample) :=
      (ordered_summary_fold FreeMonoid.of sample).symm
    _ = Sequences.OrderedSummary.summary FreeMonoid.of [0, 1, 2, 3] :=
      congrArg (Sequences.OrderedSummary.summary FreeMonoid.of) sample_inorder
    _ = FreeMonoid.ofList [0, 1, 2, 3] := by
      change Sequences.OrderedSummary.summary FreeMonoid.of
        ([0] ++ ([1] ++ ([2] ++ [3]))) = _
      simp only [Sequences.OrderedSummary.summary_append,
        Sequences.OrderedSummary.summary_singleton]

def balancedThree : BinaryTree Nat := .node 1 (.node 1 .nil .nil) (.node 1 .nil .nil)
def leftThree : BinaryTree Nat := .node 1 (.node 1 (.node 1 .nil .nil) .nil) .nil

/-- Full inorder still forgets shape; its labels cannot determine height. -/
theorem same_inorder_different_height :
    Trees.inorder balancedThree = Trees.inorder leftThree ∧
      balancedThree.height = 2 ∧ leftThree.height = 3 := ⟨rfl, rfl, rfl⟩

/-- A noninjective label map preserves shape and retains every occurrence. -/
theorem repeated_sample :
    (sample.map (fun _ => ())).numNodes = 4 ∧
    (sample.map (fun _ => ())).numLeaves = 5 ∧
    (sample.map (fun _ => ())).height = 3 ∧
    Trees.inorder (sample.map (fun _ => ())) = [(), (), (), ()] := by
  rw [Trees.numNodes_map, Trees.numLeaves_map, Trees.height_map, Trees.inorder_map,
    BinaryTree.numLeaves_eq_numNodes_succ, sample_size, sample_height, sample_inorder]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem empty_tree (t : BinaryTree Empty) : t = .nil := by
  cases t with
  | nil => rfl
  | node a l r => exact Empty.elim a

theorem empty_fold {β : Type v} (empty : β) (combine : β → Empty → β → β)
    (t : BinaryTree Empty) : Trees.fold empty combine t = empty := by
  rw [empty_tree t]

theorem empty_observations (t : BinaryTree Empty) :
    t.numNodes = 0 ∧ t.height = 0 ∧ Trees.inorder t = [] := by
  rw [empty_tree t]
  exact ⟨rfl, rfl, rfl⟩

theorem empty_annotation {β : Type v} (empty : β) (combine : β → Empty → β → β)
    (t : BinaryTree Empty) :
    Trees.Cached.erase (Trees.Cached.annotate empty combine t) = t ∧
      Trees.Cached.Valid empty combine (Trees.Cached.annotate empty combine t) :=
  ⟨Trees.Cached.erase_annotate empty combine t,
    Trees.Cached.annotate_valid empty combine t⟩

/-- The two wrong descendants compensate at the root, hiding the corruption. -/
def corrupt : BinaryTree (Nat × Nat) :=
  .node (1, 4) (.node (0, 2) .nil .nil)
    (.node (3, 1) (.node (2, 1) .nil .nil) .nil)

theorem corrupt_root_checks :
    Trees.Cached.read 0 corrupt = corrupt.numNodes ∧
      Trees.Cached.read 0 corrupt =
        sizeStep (Trees.Cached.read 0 corrupt.left) 1 (Trees.Cached.read 0 corrupt.right) :=
  ⟨rfl, rfl⟩

theorem corrupt_not_valid : ¬ Trees.Cached.Valid 0 sizeStep corrupt := by
  simp [corrupt, Trees.Cached.Valid, Trees.Cached.read, sizeStep]

theorem corrupt_erases : Trees.Cached.erase corrupt = sample := rfl

theorem corrupt_inorder : Trees.inorder (Trees.Cached.erase corrupt) = [0, 1, 2, 3] := by
  rw [corrupt_erases, sample_inorder]

/-- The public constructor-validity equivalence exposes the retained bad child. -/
theorem corrupt_smart_not_valid :
    ¬ Trees.Cached.Valid 0 sizeStep
      (Trees.Cached.smartNode 0 sizeStep corrupt.left 1 corrupt.right) := by
  rw [Trees.Cached.smartNode_valid_iff]
  simp [corrupt, Trees.Cached.Valid, Trees.Cached.read, sizeStep]

theorem corrupt_smart_same_tree :
    Trees.Cached.smartNode 0 sizeStep corrupt.left 1 corrupt.right = corrupt := rfl

/-- This applies label-map transport to arbitrary annotations, including bad ones. -/
theorem erased_fold {β : Type v} {γ : Type w} (empty : β)
    (combine : β → α → β → β) (t : BinaryTree (α × γ)) :
    Trees.fold empty combine (Trees.Cached.erase t) =
      Trees.fold empty (fun l ac r => combine l ac.1 r) t :=
  Trees.fold_map empty combine Prod.fst t

/-- Arithmetic is inlined in this explicitly declared callback observation. -/
def sizeRun (l : Nat) (a : α) (r : Nat) : Resources.Measured Nat Nat :=
  Resources.pure (sizeStep l a r)

def heightRun (l : Nat) (a : α) (r : Nat) : Resources.Measured Nat Nat :=
  Resources.pure (heightStep l a r)

theorem size_node_value (l : BinaryTree (α × Nat)) (a : α)
    (r : BinaryTree (α × Nat)) :
    (Resources.TreeCache.nodeRun 0 sizeRun l a r).1 =
      Trees.Cached.smartNode 0 sizeStep l a r :=
  Resources.TreeCache.nodeRun_value 0 sizeStep sizeRun l a r rfl

theorem height_node_value (l : BinaryTree (α × Nat)) (a : α)
    (r : BinaryTree (α × Nat)) :
    (Resources.TreeCache.nodeRun 0 heightRun l a r).1 =
      Trees.Cached.smartNode 0 heightStep l a r :=
  Resources.TreeCache.nodeRun_value 0 heightStep heightRun l a r rfl

theorem size_node_cost (l : BinaryTree (α × Nat)) (a : α)
    (r : BinaryTree (α × Nat)) :
    (Resources.TreeCache.nodeRun 0 sizeRun l a r).2 = 3 := by
  simpa only [sizeRun, Resources.pure] using
    Resources.TreeCache.nodeRun_cost 0 sizeRun l a r

theorem height_node_cost (l : BinaryTree (α × Nat)) (a : α)
    (r : BinaryTree (α × Nat)) :
    (Resources.TreeCache.nodeRun 0 heightRun l a r).2 = 3 := by
  simpa only [heightRun, Resources.pure] using
    Resources.TreeCache.nodeRun_cost 0 heightRun l a r

theorem size_node_bound (l : BinaryTree (α × Nat)) (a : α)
    (r : BinaryTree (α × Nat)) :
    (Resources.TreeCache.nodeRun 0 sizeRun l a r).2 ≤ 3 :=
  Resources.TreeCache.nodeRun_le 0 sizeRun l a r 0 (Nat.le_refl 0)

theorem size_node_valid (l : BinaryTree (α × Nat)) (a : α)
    (r : BinaryTree (α × Nat))
    (hl : Trees.Cached.Valid 0 sizeStep l) (hr : Trees.Cached.Valid 0 sizeStep r) :
    Trees.Cached.Valid 0 sizeStep (Resources.TreeCache.nodeRun 0 sizeRun l a r).1 :=
  Resources.TreeCache.nodeRun_valid 0 sizeStep sizeRun l a r hl hr rfl

theorem height_node_valid (l : BinaryTree (α × Nat)) (a : α)
    (r : BinaryTree (α × Nat))
    (hl : Trees.Cached.Valid 0 heightStep l) (hr : Trees.Cached.Valid 0 heightStep r) :
    Trees.Cached.Valid 0 heightStep (Resources.TreeCache.nodeRun 0 heightRun l a r).1 :=
  Resources.TreeCache.nodeRun_valid 0 heightStep heightRun l a r hl hr rfl

theorem measured_size_reader (l : BinaryTree (α × Nat)) (a : α)
    (r : BinaryTree (α × Nat))
    (hl : Trees.Cached.Valid 0 sizeStep l) (hr : Trees.Cached.Valid 0 sizeStep r) :
    Trees.Cached.read 0 (Resources.TreeCache.nodeRun 0 sizeRun l a r).1 =
      (Resources.TreeCache.nodeRun 0 sizeRun l a r).1.numNodes :=
  size_reader _ (size_node_valid l a r hl hr)

theorem measured_height_reader (l : BinaryTree (α × Nat)) (a : α)
    (r : BinaryTree (α × Nat))
    (hl : Trees.Cached.Valid 0 heightStep l) (hr : Trees.Cached.Valid 0 heightStep r) :
    Trees.Cached.read 0 (Resources.TreeCache.nodeRun 0 heightRun l a r).1 =
      (Resources.TreeCache.nodeRun 0 heightRun l a r).1.height :=
  height_reader _ (height_node_valid l a r hl hr)

def listStep (l : List α) (a : α) (r : List α) : List α := l ++ (a :: r)

/-- A real existing recursive append, not a synthetic cost annotation. -/
def appendStepRun (l : List α) (a : α) (r : List α) :
    Resources.Measured (List α) Nat := Resources.ListReversal.appendRun l (a :: r)

theorem append_node_value (l : BinaryTree (α × List α)) (a : α)
    (r : BinaryTree (α × List α)) :
    (Resources.TreeCache.nodeRun [] appendStepRun l a r).1 =
      Trees.Cached.smartNode [] listStep l a r := by
  apply Resources.TreeCache.nodeRun_value
  simp [appendStepRun, Resources.ListReversal.appendRun_exact, listStep]

theorem append_node_cost (l : BinaryTree (α × List α)) (a : α)
    (r : BinaryTree (α × List α)) :
    (Resources.TreeCache.nodeRun [] appendStepRun l a r).2 =
      (Trees.Cached.read [] l).length + 4 := by
  simpa [appendStepRun, Resources.ListReversal.appendRun_exact, Nat.add_assoc] using
    Resources.TreeCache.nodeRun_cost [] appendStepRun l a r

theorem append_node_valid (l : BinaryTree (α × List α)) (a : α)
    (r : BinaryTree (α × List α))
    (hl : Trees.Cached.Valid [] listStep l) (hr : Trees.Cached.Valid [] listStep r) :
    Trees.Cached.Valid [] listStep (Resources.TreeCache.nodeRun [] appendStepRun l a r).1 := by
  apply Resources.TreeCache.nodeRun_valid [] listStep appendStepRun l a r hl hr
  simp [appendStepRun, Resources.ListReversal.appendRun_exact, listStep]

/-- Repeated labels are allowed; this family varies actual tree size. -/
def chain : Nat → BinaryTree Unit
  | 0 => .nil
  | n + 1 => .node () (chain n) .nil

theorem chain_numNodes (n : Nat) : (chain n).numNodes = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [chain, ih]

def chainCache (n : Nat) : BinaryTree (Unit × List Unit) :=
  Trees.Cached.annotate [] listStep (chain n)

theorem chainCache_valid (n : Nat) : Trees.Cached.Valid [] listStep (chainCache n) :=
  Trees.Cached.annotate_valid [] listStep (chain n)

theorem chainCache_read (n : Nat) :
    Trees.Cached.read [] (chainCache n) = Trees.inorder (chain n) :=
  Trees.Cached.read_annotate [] listStep (chain n)

theorem chainCache_length (n : Nat) :
    (Trees.Cached.read [] (chainCache n)).length = n := by
  rw [chainCache_read, Trees.inorder_length, chain_numNodes]

/-- Already prepared cached children are the inputs to this local execution.
Their preparation is not silently included in, or equated to, this count. -/
theorem chain_node_cost (n : Nat) :
    (Resources.TreeCache.nodeRun [] appendStepRun (chainCache n) () .nil).2 = n + 4 := by
  rw [append_node_cost, chainCache_length]

theorem chain_node_value (n : Nat) :
    (Resources.TreeCache.nodeRun [] appendStepRun (chainCache n) () .nil).1 =
      chainCache (n + 1) := by
  rw [append_node_value] <;> rfl

theorem chain_node_valid (n : Nat) :
    Trees.Cached.Valid [] listStep
      (Resources.TreeCache.nodeRun [] appendStepRun (chainCache n) () .nil).1 :=
  append_node_valid _ () .nil (chainCache_valid n) (Trees.Cached.valid_nil [] listStep)

/-- Callback work can exceed any fixed constant even with valid child caches. -/
theorem chain_node_exceeds (K : Nat) :
    K < (Resources.TreeCache.nodeRun [] appendStepRun (chainCache (K + 1)) () .nil).2 := by
  rw [chain_node_cost]
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self K) (Nat.le_add_right (K + 1) 4)

theorem empty_read {β : Type v} (empty : β) :
    Resources.TreeCache.readRun empty (.nil : BinaryTree (Empty × β)) = (empty, 1) := rfl

end TreeCacheExamples
