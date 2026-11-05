import Applications.Trees.ShapeLog
import Examples.TreeCache

/-! Connected shape, logarithm and cached-observation uses. Independent case
expectations and statement assessment: `docs/research/fdsa-tree-shape.md`.
-/
set_option autoImplicit false
set_option warningAsError true

namespace TreeShapeExamples
universe u v
variable {α : Type u} {β : Type v}

def single : BinaryTree Unit := .node () .nil .nil

theorem single_complete : Trees.Complete single := by
  simp [single, Trees.complete_node]

theorem single_minHeight : Trees.minHeight single = 1 := by
  calc
    Trees.minHeight single = single.height :=
      (Trees.complete_iff_minHeight_eq_height single).1 single_complete
    _ = 1 := rfl

theorem single_almostComplete : Trees.AlmostComplete single :=
  Trees.complete_almostComplete single single_complete

theorem empty_shapes (t : BinaryTree Empty) :
    Trees.Complete t ∧ Trees.AlmostComplete t ∧
      Trees.minHeight t = 0 ∧ t.height = 0 ∧ t.numLeaves = 1 := by
  rw [TreeCacheExamples.empty_tree t]
  exact ⟨Trees.complete_nil, Trees.almostComplete_nil, rfl, rfl, rfl⟩

def perfectThree : BinaryTree Unit := .node () single single

theorem perfectThree_complete : Trees.Complete perfectThree := by
  exact (Trees.complete_iff_numLeaves_eq_pow_height perfectThree).2 (by decide)

theorem perfectThree_leaves :
    perfectThree.numLeaves = 2 ^ Trees.minHeight perfectThree :=
  Trees.numLeaves_eq_pow_minHeight perfectThree perfectThree_complete

theorem perfectThree_minHeight : Trees.minHeight perfectThree = 2 := by
  calc
    Trees.minHeight perfectThree = perfectThree.height :=
      (Trees.complete_iff_minHeight_eq_height perfectThree).1 perfectThree_complete
    _ = 2 := rfl

def rightTwo : BinaryTree Unit := .node () .nil single

theorem rightTwo_incomplete : ¬ Trees.Complete rightTwo := by
  rw [Trees.complete_iff_minHeight_eq_height]
  decide

theorem rightTwo_almostComplete : Trees.AlmostComplete rightTwo := by
  change 2 ≤ 1 + 1
  decide

theorem rightTwo_strict_capacity :
    2 ^ Trees.minHeight rightTwo < rightTwo.numLeaves ∧
      rightTwo.numLeaves < 2 ^ rightTwo.height :=
  ⟨Trees.pow_minHeight_lt_numLeaves rightTwo rightTwo_incomplete,
    Trees.numLeaves_lt_pow_height rightTwo rightTwo_incomplete⟩

theorem rightTwo_children :
    Trees.AlmostComplete (.nil : BinaryTree Unit) ∧ Trees.AlmostComplete single :=
  Trees.almostComplete_children () .nil single rightTwo_almostComplete

theorem rightTwo_sub : rightTwo.height - Trees.minHeight rightTwo ≤ 1 :=
  (Trees.almostComplete_iff_sub rightTwo).1 rightTwo_almostComplete

theorem chainThree_power_not_complete :
    (TreeCacheExamples.chain 3).numLeaves = 2 ^ (2 : Nat) ∧
      ¬ Trees.Complete (TreeCacheExamples.chain 3) := by
  constructor
  · rfl
  · rw [Trees.complete_iff_numLeaves_eq_pow_minHeight]
    decide

theorem rightTwo_rounded_equalities :
    Trees.minHeight rightTwo = Nat.log 2 rightTwo.numLeaves ∧
      rightTwo.height = Nat.clog 2 rightTwo.numLeaves :=
  ⟨Trees.minHeight_eq_log_numLeaves rightTwo rightTwo_almostComplete,
    Trees.height_eq_clog_numLeaves rightTwo rightTwo_almostComplete⟩

theorem rightTwo_rounded_strictness_fails :
    ¬ Trees.minHeight rightTwo < Nat.log 2 rightTwo.numLeaves ∧
      ¬ Nat.clog 2 rightTwo.numLeaves < rightTwo.height := by
  have hm := rightTwo_rounded_equalities.1
  have hh := rightTwo_rounded_equalities.2
  omega

theorem empty_logarithms (t : BinaryTree Empty) :
    Nat.log 2 t.numLeaves = 0 ∧ Nat.clog 2 t.numLeaves = 0 := by
  have ht := (empty_shapes t).2.1
  have hm := Trees.minHeight_eq_log_numLeaves t ht
  have hh := Trees.height_eq_clog_numLeaves t ht
  have he := TreeCacheExamples.empty_tree t
  rw [he] at hm hh ⊢
  exact ⟨hm.symm, hh.symm⟩

theorem sample_almostComplete : Trees.AlmostComplete TreeCacheExamples.sample := by
  change 3 ≤ 2 + 1
  decide

theorem sample_minHeight : Trees.minHeight TreeCacheExamples.sample = 2 := rfl
theorem sample_leaves : TreeCacheExamples.sample.numLeaves = 5 := rfl

theorem sample_logarithms : Nat.log 2 5 = 2 ∧ Nat.clog 2 5 = 3 := by
  constructor
  · simpa only [sample_leaves, sample_minHeight] using
      (Trees.minHeight_eq_log_numLeaves TreeCacheExamples.sample sample_almostComplete).symm
  · simpa only [sample_leaves, TreeCacheExamples.sample_height] using
      (Trees.height_eq_clog_numLeaves TreeCacheExamples.sample sample_almostComplete).symm

theorem sample_height_nodes : TreeCacheExamples.sample.height =
    Nat.clog 2 (TreeCacheExamples.sample.numNodes + 1) := by
  simpa only [BinaryTree.numLeaves_eq_numNodes_succ] using
    Trees.height_eq_clog_numLeaves TreeCacheExamples.sample sample_almostComplete

theorem sample_wrong_node_offset :
    TreeCacheExamples.sample.height ≠ Nat.clog 2 TreeCacheExamples.sample.numNodes := by
  decide

theorem perfectThree_real_height :
    (perfectThree.height : Real) = Real.logb 2 (perfectThree.numLeaves : Real) :=
  Trees.height_eq_logb_numLeaves perfectThree perfectThree_complete

theorem rightTwo_strict_real :
    (1 : Real) < Real.logb 2 3 ∧ Real.logb 2 3 < (2 : Real) := by
  have hm : Trees.minHeight rightTwo = 1 := rfl
  have hl : rightTwo.numLeaves = 3 := rfl
  have hh : rightTwo.height = 2 := rfl
  constructor
  · simpa only [hm, hl, Nat.cast_one, Nat.cast_ofNat] using
      Trees.minHeight_lt_logb_numLeaves rightTwo rightTwo_incomplete
  · simpa only [hl, hh, Nat.cast_ofNat] using
      Trees.logb_numLeaves_lt_height rightTwo rightTwo_incomplete

theorem sample_real_rounding :
    ⌊Real.logb 2 (5 : Real)⌋₊ = 2 ∧ ⌈Real.logb 2 (5 : Real)⌉₊ = 3 := by
  constructor
  · simpa only [sample_leaves, sample_minHeight, Nat.cast_ofNat] using
      (Trees.minHeight_eq_floor_logb_numLeaves
        TreeCacheExamples.sample sample_almostComplete).symm
  · simpa only [sample_leaves, TreeCacheExamples.sample_height, Nat.cast_ofNat] using
      (Trees.height_eq_ceil_logb_numLeaves
        TreeCacheExamples.sample sample_almostComplete).symm

theorem empty_real_height (t : BinaryTree Empty) :
    (t.height : Real) = Real.logb 2 (t.numLeaves : Real) :=
  Trees.height_eq_logb_numLeaves t (empty_shapes t).1

theorem mapped_sample :
    Trees.minHeight (TreeCacheExamples.sample.map (fun _ => ())) = 2 ∧
      Trees.AlmostComplete (TreeCacheExamples.sample.map (fun _ => ())) :=
  ⟨(Trees.minHeight_map (fun _ => ()) TreeCacheExamples.sample).trans sample_minHeight,
    (Trees.almostComplete_map (fun _ => ()) TreeCacheExamples.sample).2 sample_almostComplete⟩

theorem relabelled_complete :
    Trees.Complete (perfectThree.map (fun _ => false)) :=
  (Trees.complete_map (fun _ => false) perfectThree).2 perfectThree_complete

/-- Erasing any annotations preserves the new shape observation. -/
theorem minHeight_erase (t : BinaryTree (α × β)) :
    Trees.minHeight (Trees.Cached.erase t) = Trees.minHeight t :=
  Trees.minHeight_map Prod.fst t

theorem almostComplete_erase (t : BinaryTree (α × β)) :
    Trees.AlmostComplete (Trees.Cached.erase t) ↔ Trees.AlmostComplete t :=
  Trees.almostComplete_map Prod.fst t

theorem pairSample_shape :
    Trees.minHeight TreeCacheExamples.pairSample = 2 ∧
      Trees.AlmostComplete TreeCacheExamples.pairSample := by
  constructor
  · calc
      Trees.minHeight TreeCacheExamples.pairSample =
          Trees.minHeight (Trees.Cached.erase TreeCacheExamples.pairSample) :=
        (minHeight_erase _).symm
      _ = Trees.minHeight TreeCacheExamples.sample :=
        congrArg Trees.minHeight TreeCacheExamples.pairSample_erases
      _ = 2 := sample_minHeight
  · apply (almostComplete_erase _).1
    rw [TreeCacheExamples.pairSample_erases]
    exact sample_almostComplete

theorem corrupt_shape_without_validity :
    Trees.minHeight TreeCacheExamples.corrupt = 2 ∧
      Trees.AlmostComplete TreeCacheExamples.corrupt ∧
      ¬ Trees.Cached.Valid 0 TreeCacheExamples.sizeStep TreeCacheExamples.corrupt := by
  refine ⟨?_, ?_, TreeCacheExamples.corrupt_not_valid⟩
  · calc
      Trees.minHeight TreeCacheExamples.corrupt =
          Trees.minHeight (Trees.Cached.erase TreeCacheExamples.corrupt) :=
        (minHeight_erase _).symm
      _ = Trees.minHeight TreeCacheExamples.sample :=
        congrArg Trees.minHeight TreeCacheExamples.corrupt_erases
      _ = 2 := sample_minHeight
  · apply (almostComplete_erase _).1
    rw [TreeCacheExamples.corrupt_erases]
    exact sample_almostComplete

def minStep (l : Nat) (_ : α) (r : Nat) : Nat := min l r + 1

/-- Recursive validity makes the cached minimum agree with the structural observation. -/
theorem min_reader (t : BinaryTree (α × Nat))
    (ht : Trees.Cached.Valid 0 minStep t) :
    Trees.Cached.read 0 t = Trees.minHeight t := by
  calc
    Trees.Cached.read 0 t = Trees.fold 0 minStep (Trees.Cached.erase t) :=
      Trees.Cached.read_eq_fold 0 minStep t ht
    _ = Trees.minHeight (Trees.Cached.erase t) := rfl
    _ = Trees.minHeight t := minHeight_erase t

def minSample : BinaryTree (Nat × Nat) :=
  Trees.Cached.annotate 0 minStep TreeCacheExamples.sample

theorem minSample_valid : Trees.Cached.Valid 0 minStep minSample :=
  Trees.Cached.annotate_valid 0 minStep TreeCacheExamples.sample

theorem minSample_erases : Trees.Cached.erase minSample = TreeCacheExamples.sample :=
  Trees.Cached.erase_annotate 0 minStep TreeCacheExamples.sample

theorem minSample_reads : Trees.Cached.read 0 minSample = 2 := by
  calc
    Trees.Cached.read 0 minSample = Trees.minHeight minSample :=
      min_reader minSample minSample_valid
    _ = Trees.minHeight (Trees.Cached.erase minSample) := (minHeight_erase _).symm
    _ = Trees.minHeight TreeCacheExamples.sample := congrArg Trees.minHeight minSample_erases
    _ = 2 := sample_minHeight

/-- Four nodes at optimal maximum height, but external depths differ by two. -/
def heightOptimalCounter : BinaryTree Bool :=
  .node false .nil (perfectThree.map (fun _ => false))

theorem heightOptimalCounter_numNodes : heightOptimalCounter.numNodes = 4 := rfl

theorem heightOptimalCounter_shape :
    heightOptimalCounter.numLeaves = 5 ∧
      Trees.minHeight heightOptimalCounter = 1 ∧ heightOptimalCounter.height = 3 :=
  ⟨rfl, rfl, rfl⟩

theorem optimum_across_labels :
    TreeCacheExamples.sample.height ≤ heightOptimalCounter.height :=
  Trees.height_optimal TreeCacheExamples.sample heightOptimalCounter
    sample_almostComplete (by decide)

theorem counter_not_almostComplete : ¬ Trees.AlmostComplete heightOptimalCounter := by
  change ¬ 3 ≤ 1 + 1
  decide

theorem counter_rounded_height : heightOptimalCounter.height =
    Nat.clog 2 heightOptimalCounter.numLeaves := by
  calc
    heightOptimalCounter.height = TreeCacheExamples.sample.height := rfl
    _ = Nat.clog 2 TreeCacheExamples.sample.numLeaves :=
      Trees.height_eq_clog_numLeaves TreeCacheExamples.sample sample_almostComplete
    _ = Nat.clog 2 heightOptimalCounter.numLeaves := rfl

/-- An actual Boolean-labelled witness attains the optimum even though the
almost-complete predicate fails. The competitor can have any payload type. -/
theorem counter_height_optimal (t : BinaryTree α)
    (ht : heightOptimalCounter.numNodes ≤ t.numNodes) :
    heightOptimalCounter.height ≤ t.height := by
  calc
    heightOptimalCounter.height = TreeCacheExamples.sample.height := rfl
    _ ≤ t.height := Trees.height_optimal TreeCacheExamples.sample t
      sample_almostComplete (by simpa only
        [TreeCacheExamples.sample_size, heightOptimalCounter_numNodes] using ht)

def almostFour : BinaryTree Unit := .node () rightTwo single
def localBalanceCounter : BinaryTree Unit := .node () almostFour rightTwo

/-- A predicate used only to state the all-node premise of this counterexample. -/
private def SiblingHeightBalanced : BinaryTree α → Prop
  | .nil => True
  | .node _ l r => l.height ≤ r.height + 1 ∧ r.height ≤ l.height + 1 ∧
      SiblingHeightBalanced l ∧ SiblingHeightBalanced r

theorem localBalanceCounter_balanced : SiblingHeightBalanced localBalanceCounter := by
  simp [SiblingHeightBalanced, localBalanceCounter, almostFour, rightTwo, single,
    BinaryTree.height]

theorem localBalanceCounter_shape :
    localBalanceCounter.numNodes = 7 ∧ localBalanceCounter.numLeaves = 8 ∧
      Trees.minHeight localBalanceCounter = 2 ∧ localBalanceCounter.height = 4 :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem localBalanceCounter_not_almostComplete :
    ¬ Trees.AlmostComplete localBalanceCounter := by
  change ¬ 4 ≤ 2 + 1
  decide

theorem chain_rounded_bounds (n : Nat) :
    Trees.minHeight (TreeCacheExamples.chain n) ≤
        Nat.log 2 (TreeCacheExamples.chain n).numLeaves ∧
      Nat.clog 2 (TreeCacheExamples.chain n).numLeaves ≤
        (TreeCacheExamples.chain n).height :=
  ⟨Trees.minHeight_le_log_numLeaves (TreeCacheExamples.chain n),
    Trees.clog_numLeaves_le_height (TreeCacheExamples.chain n)⟩

end TreeShapeExamples
