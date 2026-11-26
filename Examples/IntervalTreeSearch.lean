import Applications.Search.IntervalTree.Search
import Applications.Search.IntervalTree.Point
import Applications.Search.IntervalTree.Contract
import Examples.IntervalTreeUpdates

/-! Connected contract, overlap and point-search cases. Expected values and
countermodels come from the independent O10–O18 preparation; existing update
fixtures retain their original definitions and proofs.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.IntervalTreeSearch
open Search IntervalTreeFoundations IntervalTreeUpdates

def fivePoint : IntervalKey Nat := IntervalKey.ofBounds 5 5 (by decide)

theorem empty_search (query : IntervalKey Nat) :
    IntervalTree.search id .nil query = false := IntervalTree.search_nil id query

/-- A malformed cache does not obstruct a hit at the actual root. -/
theorem malformed_root_hit : IntervalTree.search id malformedLeaf fivePoint = true :=
  IntervalTree.search_node_of_overlap id repairKey 99 .nil .nil fivePoint (by decide)

theorem malformed_root_witness :
    ∃ key ∈ Trees.setTree (Trees.Cached.erase malformedLeaf),
      IntervalKey.Overlap key fivePoint :=
  IntervalTree.search_sound id malformed_root_hit

theorem same_reader_different_search :
    IntervalTree.maxHi bottomSingleton = IntervalTree.maxHi (.nil : NTree) ∧
    IntervalTree.search id bottomSingleton zeroPoint = true ∧
    IntervalTree.search id (.nil : NTree) zeroPoint = false := ⟨rfl, rfl, rfl⟩

/-! O12: two different pruning arguments with genuinely satisfied premises. -/
def pruneLeftKey : IntervalKey Nat := IntervalKey.ofBounds 3 4 (by decide)
def pruneRightKey : IntervalKey Nat := IntervalKey.ofBounds 7 9 (by decide)
def pruneLeft : NTree := leaf pruneLeftKey 4

theorem pruneLeft_valid : IntervalTree.CacheValid id pruneLeft := by
  simp only [pruneLeft, leaf, IntervalTree.cacheValid_node, IntervalTree.cacheValid_nil]
  decide

theorem pruneLeft_absent :
    ¬∃ key ∈ Trees.setTree (Trees.Cached.erase pruneLeft), IntervalKey.Overlap key a := by
  simp [pruneLeft, leaf, pruneLeftKey, a, IntervalKey.Overlap,
    IntervalKey.ofBounds, IntervalKey.low, IntervalKey.high]

theorem pruning_cross (rightCache : Nat) :
    ∀ x ∈ Trees.setTree (Trees.Cached.erase pruneLeft),
      ∀ y ∈ Trees.setTree (Trees.Cached.erase (leaf pruneRightKey rightCache)), x.low ≤ y.low := by
  intro x hx y hy
  have hx' : x = pruneLeftKey := by simpa [pruneLeft, leaf] using hx
  have hy' : y = pruneRightKey := by simpa [leaf] using hy
  subst x
  subst y
  decide

theorem invalid_right_lows_excluded :
    ∀ key ∈ Trees.setTree (Trees.Cached.erase (leaf pruneRightKey 999)), a.high < key.low := by
  intro key member
  exact IntervalTree.high_lt_low_of_left_no_overlap id pruneLeft_valid
    (by intro h; cases h) (by decide) pruneLeft_absent (pruning_cross 999) member

theorem invalid_right_overlap_excluded :
    ¬∃ key ∈ Trees.setTree (Trees.Cached.erase (leaf pruneRightKey 999)),
      IntervalKey.Overlap key a :=
  IntervalTree.not_overlap_right_of_left id pruneLeft_valid
    (by intro h; cases h) (by decide) pruneLeft_absent (pruning_cross 999)

theorem pruned_right_is_invalid : ¬IntervalTree.CacheValid id (leaf pruneRightKey 999) := by
  simp only [leaf, IntervalTree.cacheValid_node, IntervalTree.cacheValid_nil]
  decide

def threePoint : IntervalKey Nat := IntervalKey.ofBounds 3 3 (by decide)

theorem unordered_subtree_excluded :
    ¬∃ key ∈ Trees.setTree (Trees.Cached.erase unordered), IntervalKey.Overlap key threePoint :=
  IntervalTree.not_overlap_of_maxHi_lt id unordered_valid (by decide)

theorem empty_subtree_excluded (query : IntervalKey Nat) :
    ¬∃ key ∈ Trees.setTree (Trees.Cached.erase (.nil : NTree)), IntervalKey.Overlap key query :=
  IntervalTree.not_overlap_nil id query

/-! O11: exact paths and semantic answers use the existing seven-node tree. -/
def touchRoot : IntervalKey Nat := IntervalKey.ofBounds 9 10 (by decide)
def touchLeft : IntervalKey Nat := IntervalKey.ofBounds 20 21 (by decide)
def touchRight : IntervalKey Nat := IntervalKey.ofBounds 21 22 (by decide)
def tenPoint : IntervalKey Nat := IntervalKey.ofBounds 10 10 (by decide)
def twentyPoint : IntervalKey Nat := IntervalKey.ofBounds 20 20 (by decide)
def twentyOnePoint : IntervalKey Nat := IntervalKey.ofBounds 21 21 (by decide)
def thirtyOnePoint : IntervalKey Nat := IntervalKey.ofBounds 31 31 (by decide)

theorem main_correct (query : IntervalKey Nat) :
    IntervalTree.search id mainTree query = true ↔
      IntervalSet.HasOverlap (Trees.setTree (Trees.Cached.erase mainTree)) query :=
  IntervalTree.search_correct_book mainTree_valid mainTree_strict query

theorem main_left_choice :
    IntervalTree.search id mainTree touchLeft = IntervalTree.search id mainLeft touchLeft :=
  IntervalTree.search_node_left id d 30 mainLeft mainRight touchLeft
    (by decide) (by intro h; cases h) (by decide)

theorem main_left_then_right :
    IntervalTree.search id mainLeft touchLeft = IntervalTree.search id (leaf c 20) touchLeft :=
  IntervalTree.search_node_right id b 20 (leaf a 2) (leaf c 20) touchLeft (by decide) (by decide)

theorem main_right_choice :
    IntervalTree.search id mainTree touchRight = IntervalTree.search id mainRight touchRight :=
  IntervalTree.search_node_right id d 30 mainLeft mainRight touchRight (by decide) (by decide)

theorem main_literal_answers :
    [touchRoot, touchLeft, touchRight, tenPoint, zeroPoint, thirtyOnePoint, twentyOnePoint].map
      (IntervalTree.search id mainTree) = [true, true, true, true, false, false, false] := rfl

theorem main_semantic_answers :
    IntervalSet.HasOverlap (Trees.setTree (Trees.Cached.erase mainTree)) touchRoot ∧
    IntervalSet.HasOverlap (Trees.setTree (Trees.Cached.erase mainTree)) touchLeft ∧
    IntervalSet.HasOverlap (Trees.setTree (Trees.Cached.erase mainTree)) touchRight ∧
    IntervalSet.HasOverlap (Trees.setTree (Trees.Cached.erase mainTree)) tenPoint ∧
    ¬IntervalSet.HasOverlap (Trees.setTree (Trees.Cached.erase mainTree)) zeroPoint ∧
    ¬IntervalSet.HasOverlap (Trees.setTree (Trees.Cached.erase mainTree)) thirtyOnePoint ∧
    ¬IntervalSet.HasOverlap (Trees.setTree (Trees.Cached.erase mainTree)) twentyOnePoint := by
  refine ⟨(main_correct touchRoot).mp rfl, (main_correct touchLeft).mp rfl,
    (main_correct touchRight).mp rfl, (main_correct tenPoint).mp rfl, ?_, ?_, ?_⟩
  · intro h
    have bad := (main_correct zeroPoint).mpr h
    cases bad
  · intro h
    have bad := (main_correct thirtyOnePoint).mpr h
    cases bad
  · intro h
    have bad := (main_correct twentyOnePoint).mpr h
    cases bad

theorem duplicate_lowOrdered : IntervalTree.LowOrdered id duplicateTree := by
  change [onePoint, onePoint].Pairwise (fun x y => x.low ≤ y.low)
  decide

theorem duplicate_search_correct (query : IntervalKey Nat) :
    IntervalTree.search id duplicateTree query = true ↔
      ∃ key ∈ Trees.setTree (Trees.Cached.erase duplicateTree), IntervalKey.Overlap key query :=
  IntervalTree.search_correct id duplicateTree_valid duplicate_lowOrdered query

theorem weak_search_order_is_not_strict_key_order :
    IntervalTree.LowOrdered id duplicateTree ∧
    ¬OrderedList.Strict (Trees.inorder (Trees.Cached.erase duplicateTree)) :=
  ⟨duplicate_lowOrdered, duplicateTree_not_strict⟩

/-! O13/O18: agreement of raw programs does not imply semantic completeness. -/
theorem malformed_interval_false_negatives :
    (IntervalTree.search id boundOnly twoPoint = false ∧
      IntervalSet.HasOverlap (Trees.setTree (Trees.Cached.erase boundOnly)) twoPoint) ∧
    (IntervalTree.search id attainmentOnly threePoint = false ∧
      IntervalSet.HasOverlap (Trees.setTree (Trees.Cached.erase attainmentOnly)) threePoint) ∧
    (IntervalTree.search id correctRoot twoPoint = false ∧
      IntervalSet.HasOverlap (Trees.setTree (Trees.Cached.erase correctRoot)) twoPoint) := by
  refine ⟨⟨rfl, twoPoint, ?_, IntervalKey.overlap_self twoPoint⟩,
    ⟨rfl, tallZero, ?_, by decide⟩, ⟨rfl, farHigh, ?_, by decide⟩⟩
  · simp [boundOnly]
  · simp [attainmentOnly, attainedLeft]
  · simp [correctRoot]

theorem malformed_singleton_bridges :
    IntervalTree.searchPoint id boundOnly 2 = IntervalTree.search id boundOnly twoPoint ∧
    IntervalTree.searchPoint id attainmentOnly 3 = IntervalTree.search id attainmentOnly threePoint ∧
    IntervalTree.searchPoint id correctRoot 2 = IntervalTree.search id correctRoot twoPoint :=
  ⟨IntervalTree.searchPoint_eq_search id boundOnly 2 (by decide),
    IntervalTree.searchPoint_eq_search id attainmentOnly 3 (by decide),
    IntervalTree.searchPoint_eq_search id correctRoot 2 (by decide)⟩

theorem malformed_point_false_negatives :
    (IntervalTree.searchPoint id boundOnly 2 = false ∧
      ∃ key ∈ Trees.setTree (Trees.Cached.erase boundOnly), IntervalTree.ContainsPoint 2 key) ∧
    (IntervalTree.searchPoint id attainmentOnly 3 = false ∧
      ∃ key ∈ Trees.setTree (Trees.Cached.erase attainmentOnly), IntervalTree.ContainsPoint 3 key) ∧
    (IntervalTree.searchPoint id correctRoot 2 = false ∧
      ∃ key ∈ Trees.setTree (Trees.Cached.erase correctRoot), IntervalTree.ContainsPoint 2 key) := by
  refine ⟨⟨?_, twoPoint, ?_, by decide⟩, ⟨?_, tallZero, ?_, by decide⟩,
    ⟨?_, farHigh, ?_, by decide⟩⟩
  · rw [malformed_singleton_bridges.1]
    exact malformed_interval_false_negatives.1.1
  · simp [boundOnly]
  · rw [malformed_singleton_bridges.2.1]
    exact malformed_interval_false_negatives.2.1.1
  · simp [attainmentOnly, attainedLeft]
  · rw [malformed_singleton_bridges.2.2]
    exact malformed_interval_false_negatives.2.2.1
  · simp [correctRoot]

theorem main_point_correct (point : Nat) :
    IntervalTree.searchPoint id mainTree point = true ↔
      ∃ key ∈ Trees.setTree (Trees.Cached.erase mainTree), IntervalTree.ContainsPoint point key :=
  IntervalTree.searchPoint_correct_book mainTree_valid mainTree_strict point

theorem main_point_literal_answers :
    [20, 22, 21, 0, 31].map (IntervalTree.searchPoint id mainTree) =
      [true, true, false, false, false] := rfl

theorem main_point_contacts_and_gap :
    (∃ key ∈ Trees.setTree (Trees.Cached.erase mainTree), IntervalTree.ContainsPoint 20 key) ∧
    (∃ key ∈ Trees.setTree (Trees.Cached.erase mainTree), IntervalTree.ContainsPoint 22 key) ∧
    ¬∃ key ∈ Trees.setTree (Trees.Cached.erase mainTree), IntervalTree.ContainsPoint 21 key := by
  refine ⟨(main_point_correct 20).mp rfl, (main_point_correct 22).mp rfl, ?_⟩
  intro h
  have bad := (main_point_correct 21).mpr h
  cases bad

theorem overlap_point_and_equality_differ :
    IntervalTree.search id mainTree touchLeft = true ∧
    IntervalTree.searchPoint id mainTree 21 = false ∧
    OrderedMap.containsKey twentyPoint mainTree = false ∧
    IntervalTree.searchPoint id mainTree 20 = true := by
  refine ⟨rfl, rfl, rfl, (main_point_correct 20).mpr ?_⟩
  exact ⟨c, by simp [mainTree, mainLeft, leaf], by decide⟩

def twoThree : IntervalKey Nat := IntervalKey.ofBounds 2 3 (by decide)

theorem leaf_observation_separation :
    IntervalTree.search id (leaf shortZero 2) twoThree = true ∧
    IntervalTree.searchPoint id (leaf shortZero 2) 3 = false ∧
    IntervalTree.searchPoint id (leaf shortZero 2) 1 = true ∧
    OrderedMap.containsKey onePoint (leaf shortZero 2) = false := ⟨rfl, rfl, rfl, rfl⟩

theorem duplicate_point_correct (point : Nat) :
    IntervalTree.searchPoint id duplicateTree point = true ↔
      ∃ key ∈ Trees.setTree (Trees.Cached.erase duplicateTree), IntervalTree.ContainsPoint point key :=
  IntervalTree.searchPoint_correct id duplicateTree_valid duplicate_lowOrdered point

theorem point_empty_and_bottom :
    IntervalTree.searchPoint id (.nil : NTree) 0 = false ∧
    IntervalTree.searchPoint id bottomSingleton 0 = true := ⟨rfl, rfl⟩

/-! O10: a complete mixed word, all seven ordinary laws and every prefix. -/
theorem book_contract :
    IntervalSet.Laws (IntervalTree.deleteOps (id : NKey → NKey))
      (IntervalTree.search id) id (fun t => Trees.setTree (Trees.Cached.erase t))
      (IntervalTree.Valid id) :=
  IntervalTree.intervalSet_laws id (fun _ _ h => IntervalKey.low_le_of_le h.le)

def absentKey : NKey := IntervalKey.ofBounds 42 42 (by decide)
def eighteenPoint : NKey := IntervalKey.ofBounds 18 18 (by decide)
def mixedWord : List (AbstractSet.Update NKey) :=
  [.insert b, .insert a, .insert c, .insert b, .delete a, .insert d, .delete absentKey]
def mixedPrefix (n : Nat) : NTree :=
  AbstractSet.execute (IntervalTree.deleteOps id) (mixedWord.take n) .nil
def mixedResult : NTree := .node (b, 20) .nil (.node (c, 20) .nil (leaf d 9))

theorem mixed_empty_valid : IntervalTree.Valid id (mixedPrefix 0) :=
  book_contract.empty_valid

theorem mixed_empty (key : NKey) :
    key ∉ Trees.setTree (Trees.Cached.erase (mixedPrefix 0)) := book_contract.empty key

theorem mixed_prefix_valid (n : Nat) : IntervalTree.Valid id (mixedPrefix n) :=
  book_contract.toDeleteLaws.prefix_valid mixedWord n book_contract.empty_valid

theorem mixed_insert_valid (n : Nat) (key : NKey) :
    IntervalTree.Valid id (IntervalTree.insert id key (mixedPrefix n)) :=
  book_contract.insert_valid key _ (mixed_prefix_valid n)

theorem mixed_insert_contents (n : Nat) (key other : NKey) :
    other ∈ Trees.setTree (Trees.Cached.erase (IntervalTree.insert id key (mixedPrefix n))) ↔
      other = key ∨ other ∈ Trees.setTree (Trees.Cached.erase (mixedPrefix n)) :=
  book_contract.insert key _ (mixed_prefix_valid n) other

theorem mixed_member (n : Nat) (key : NKey) :
    OrderedMap.containsKey key (mixedPrefix n) = true ↔
      key ∈ Trees.setTree (Trees.Cached.erase (mixedPrefix n)) :=
  book_contract.member key _ (mixed_prefix_valid n)

theorem mixed_delete_valid (n : Nat) (key : NKey) :
    IntervalTree.Valid id (IntervalTree.delete id key (mixedPrefix n)) :=
  book_contract.delete_valid key _ (mixed_prefix_valid n)

theorem mixed_delete_contents (n : Nat) (key other : NKey) :
    other ∈ Trees.setTree (Trees.Cached.erase (IntervalTree.delete id key (mixedPrefix n))) ↔
      other ≠ key ∧ other ∈ Trees.setTree (Trees.Cached.erase (mixedPrefix n)) :=
  book_contract.delete key _ (mixed_prefix_valid n) other

theorem mixed_prefix_contents (n : Nat) :
    Trees.setTree (Trees.Cached.erase (mixedPrefix n)) =
      (mixedWord.take n).foldl AbstractSet.meaningStep (fun _ => False) :=
  book_contract.toDeleteLaws.execute_from_empty (mixedWord.take n)

theorem mixed_prefix_inorder (n : Nat) :
    Trees.inorder (Trees.Cached.erase (mixedPrefix n)) =
      AbstractSet.execute OrderedList.ops (mixedWord.take n) [] :=
  (IntervalTree.inorder_refinement id).execute_from_empty OrderedList.laws (mixedWord.take n)

theorem mixed_member_refines_list (n : Nat) (key : NKey) :
    OrderedMap.containsKey key (mixedPrefix n) =
      OrderedList.ops.member key (AbstractSet.execute OrderedList.ops (mixedWord.take n) []) :=
  (IntervalTree.inorder_refinement id).member_execute OrderedList.laws (mixedWord.take n)
    book_contract.empty_valid key

theorem mixed_member_semantics (n : Nat) (key : NKey) :
    OrderedMap.containsKey key (mixedPrefix n) = true ↔
      ((mixedWord.take n).foldl AbstractSet.meaningStep (fun _ => False)) key :=
  book_contract.toDeleteLaws.member_execute (mixedWord.take n) book_contract.empty_valid key

theorem mixed_from_main_refines_list :
    Trees.inorder (Trees.Cached.erase
      (AbstractSet.execute (IntervalTree.deleteOps id) mixedWord mainTree)) =
      AbstractSet.execute OrderedList.ops mixedWord [a, b, c, d, e, f, g] :=
  (IntervalTree.inorder_refinement id).execute OrderedList.laws mixedWord
    ⟨mainTree_valid, mainTree_strict⟩

theorem mixed_from_main_overlap (query : NKey) :
    IntervalTree.search id (AbstractSet.execute (IntervalTree.deleteOps id) mixedWord mainTree)
      query = true ↔
      IntervalSet.HasOverlap
        (id '' mixedWord.foldl AbstractSet.meaningStep
          (Trees.setTree (Trees.Cached.erase mainTree))) query :=
  book_contract.search_execute mixedWord ⟨mainTree_valid, mainTree_strict⟩ query

theorem mixed_overlap_semantics (n : Nat) (query : NKey) :
    IntervalTree.search id (mixedPrefix n) query = true ↔
      IntervalSet.HasOverlap
        (id '' ((mixedWord.take n).foldl AbstractSet.meaningStep (fun _ => False))) query :=
  book_contract.search_execute (mixedWord.take n) book_contract.empty_valid query

theorem mixed_point_semantics (n point : Nat) :
    IntervalTree.searchPoint id (mixedPrefix n) point = true ↔
      ∃ key ∈ Trees.setTree (Trees.Cached.erase (mixedPrefix n)),
        IntervalTree.ContainsPoint point key :=
  IntervalTree.searchPoint_correct_book (mixed_prefix_valid n).1 (mixed_prefix_valid n).2 point

theorem mixed_prefix_shapes :
    (List.range 8).map mixedPrefix =
      [.nil, leaf b 6, .node (b, 6) (leaf a 2) .nil,
       .node (b, 20) (leaf a 2) (leaf c 20), .node (b, 20) (leaf a 2) (leaf c 20),
       .node (b, 20) .nil (leaf c 20), mixedResult, mixedResult] := rfl

theorem mixed_prefix_inorders :
    (List.range 8).map (fun n => Trees.inorder (Trees.Cached.erase (mixedPrefix n))) =
      [[], [b], [a, b], [a, b, c], [a, b, c], [b, c], [b, c, d], [b, c, d]] := rfl

theorem mixed_prefix_readers :
    (List.range 8).map (fun n => IntervalTree.maxHi (mixedPrefix n)) =
      [0, 6, 6, 20, 20, 20, 20, 20] := rfl

theorem mixed_membership_vectors :
    [a, b, c, d, eighteenPoint].map (fun key =>
      (List.range 8).map (fun n => OrderedMap.containsKey key (mixedPrefix n))) =
      [[false, false, true, true, true, false, false, false],
       [false, true, true, true, true, true, true, true],
       [false, false, false, true, true, true, true, true],
       [false, false, false, false, false, false, true, true],
       [false, false, false, false, false, false, false, false]] := rfl

theorem mixed_overlap_vectors :
    [eighteenPoint, twoPoint].map (fun query =>
      (List.range 8).map (fun n => IntervalTree.search id (mixedPrefix n) query)) =
      [[false, false, false, true, true, true, true, true],
       [false, false, true, true, true, false, false, false]] := rfl

theorem mixed_point_vectors :
    [18, 2].map (fun point =>
      (List.range 8).map (fun n => IntervalTree.searchPoint id (mixedPrefix n) point)) =
      [[false, false, false, true, true, true, true, true],
       [false, false, true, true, true, false, false, false]] := rfl

/-! O12 whole-tree clients retain the literal branch choices. -/
def leftPrunedTree : NTree := .node (fivePoint, 9) pruneLeft (leaf pruneRightKey 9)
def rightPrunedTree : NTree := .node (fivePoint, 9) (leaf a 2) (leaf pruneRightKey 9)
def sevenPoint : NKey := IntervalKey.ofBounds 7 7 (by decide)

theorem leftPrunedTree_valid : IntervalTree.Valid id leftPrunedTree := by
  constructor
  · simp only [leftPrunedTree, pruneLeft, leaf,
      IntervalTree.cacheValid_node, IntervalTree.cacheValid_nil]
    decide
  · change [pruneLeftKey, fivePoint, pruneRightKey].Pairwise (· < ·)
    decide

theorem rightPrunedTree_valid : IntervalTree.Valid id rightPrunedTree := by
  constructor
  · simp only [rightPrunedTree, leaf, IntervalTree.cacheValid_node, IntervalTree.cacheValid_nil]
    decide
  · change [a, fivePoint, pruneRightKey].Pairwise (· < ·)
    decide

theorem left_pruned_choice :
    IntervalTree.search id leftPrunedTree a = IntervalTree.search id pruneLeft a :=
  IntervalTree.search_node_left id fivePoint 9 pruneLeft (leaf pruneRightKey 9) a
    (by decide) (by intro h; cases h) (by decide)

theorem left_pruned_semantics :
    ¬IntervalSet.HasOverlap (Trees.setTree (Trees.Cached.erase leftPrunedTree)) a := by
  intro h
  have bad := (IntervalTree.search_correct_book leftPrunedTree_valid.1 leftPrunedTree_valid.2 a).mpr h
  cases bad

theorem right_pruned_left_absent :
    ¬∃ key ∈ Trees.setTree (Trees.Cached.erase (leaf a 2)), IntervalKey.Overlap key sevenPoint :=
  IntervalTree.not_overlap_of_maxHi_lt id rightPrunedTree_valid.1.1 (by decide)

theorem right_pruned_choice :
    IntervalTree.search id rightPrunedTree sevenPoint =
      IntervalTree.search id (leaf pruneRightKey 9) sevenPoint :=
  IntervalTree.search_node_right id fivePoint 9 (leaf a 2) (leaf pruneRightKey 9) sevenPoint
    (by decide) (by decide)

theorem right_pruned_semantics :
    IntervalSet.HasOverlap (Trees.setTree (Trees.Cached.erase rightPrunedTree)) sevenPoint :=
  (IntervalTree.search_correct_book rightPrunedTree_valid.1 rightPrunedTree_valid.2 sevenPoint).mp rfl

/-! O14: deleting only the nonempty-left guard changes raw behavior. -/
def searchWithoutGuard : NTree → NKey → Bool
  | .nil, _ => false
  | .node (key, _) l r, query =>
      if IntervalKey.Overlap query key then true
      else if query.low ≤ IntervalTree.maxHi l then searchWithoutGuard l query
      else searchWithoutGuard r query

def guardUnordered : NTree := .node (onePoint, 1) .nil (leaf zeroPoint 0)
def guardOrdered : NTree := .node (onePoint, 2) .nil (leaf twoPoint 2)

theorem guardUnordered_valid_cache : IntervalTree.CacheValid id guardUnordered := by
  simp only [guardUnordered, leaf, IntervalTree.cacheValid_node, IntervalTree.cacheValid_nil]
  decide

theorem guardUnordered_bad_lows : ¬IntervalTree.LowOrdered id guardUnordered := by
  change ¬[onePoint, zeroPoint].Pairwise (fun x y => x.low ≤ y.low)
  decide

theorem guard_changes_raw_answer :
    IntervalTree.search id guardUnordered zeroPoint = true ∧
    searchWithoutGuard guardUnordered zeroPoint = false := ⟨rfl, rfl⟩

theorem guardOrdered_valid : IntervalTree.Valid id guardOrdered := by
  constructor
  · simp only [guardOrdered, leaf, IntervalTree.cacheValid_node, IntervalTree.cacheValid_nil]
    decide
  · change [onePoint, twoPoint].Pairwise (· < ·)
    decide

theorem guardOrdered_selects_right :
    IntervalTree.search id guardOrdered zeroPoint =
      IntervalTree.search id (leaf twoPoint 2) zeroPoint :=
  IntervalTree.search_node_empty_left id onePoint 2 (leaf twoPoint 2) zeroPoint (by decide)

/-- This ordered example separates the branch choice, not the final Boolean. -/
theorem guard_ordered_answers_agree :
    IntervalTree.search id guardOrdered zeroPoint = false ∧
    searchWithoutGuard guardOrdered zeroPoint = false := ⟨rfl, rfl⟩

/-! O15: even injectivity, strict complete keys and good caches do not imply low order. -/
def reversedInterval (key : Fin 3) : NKey :=
  if key = 0 then tenPoint else if key = 1 then fivePoint else zeroPoint
def reversedTree : BinaryTree (Fin 3 × Nat) :=
  .node (1, 10) (.node (0, 10) .nil .nil) (.node (2, 0) .nil .nil)

theorem reversed_injective : Function.Injective reversedInterval := by
  change ∀ a b : Fin 3, reversedInterval a = reversedInterval b → a = b
  decide

theorem reversed_valid : IntervalTree.Valid reversedInterval reversedTree := by
  constructor
  · simp only [reversedTree, IntervalTree.cacheValid_node, IntervalTree.cacheValid_nil]
    decide
  · change ([0, 1, 2] : List (Fin 3)).Pairwise (· < ·)
    decide

theorem reversed_incompatible :
    ¬(∀ a b : Fin 3, a < b → (reversedInterval a).low ≤ (reversedInterval b).low) := by
  intro compatible
  exact (by decide : ¬(10 : Nat) ≤ 0) (compatible 0 2 (by decide))

theorem reversed_bad_lows : ¬IntervalTree.LowOrdered reversedInterval reversedTree := by
  change ¬([0, 1, 2] : List (Fin 3)).Pairwise
    (fun x y => (reversedInterval x).low ≤ (reversedInterval y).low)
  decide

theorem reversed_exact_membership : OrderedMap.containsKey 2 reversedTree = true :=
  ((IntervalTree.set_laws reversedInterval).member 2 reversedTree reversed_valid).mpr
    (by change (2 : Fin 3) ∈ Trees.setTree (Trees.Cached.erase reversedTree); simp [reversedTree])

theorem reversed_false_negative :
    IntervalTree.search reversedInterval reversedTree zeroPoint = false ∧
    IntervalSet.HasOverlap (reversedInterval '' Trees.setTree (Trees.Cached.erase reversedTree))
      zeroPoint := by
  refine ⟨rfl, (IntervalSet.hasOverlap_image_iff reversedInterval _ zeroPoint).mpr ?_⟩
  exact ⟨2, by simp [reversedTree], IntervalKey.overlap_self zeroPoint⟩

theorem reversed_raw_point_bridge :
    IntervalTree.searchPoint reversedInterval reversedTree 0 =
      IntervalTree.search reversedInterval reversedTree zeroPoint :=
  IntervalTree.searchPoint_eq_search reversedInterval reversedTree 0 (by decide)

theorem reversed_point_false_negative :
    IntervalTree.searchPoint reversedInterval reversedTree 0 = false ∧
    ∃ key ∈ Trees.setTree (Trees.Cached.erase reversedTree),
      IntervalTree.ContainsPoint 0 (reversedInterval key) := by
  refine ⟨?_, 2, by simp [reversedTree], by decide⟩
  rw [reversed_raw_point_bridge]
  exact reversed_false_negative.1

/-! O16: global compatibility and histories at independent key/endpoint universes. -/
theorem indexed_compatible (a b : IndexedKey) (h : a < b) :
    (indexedInterval a).low ≤ (indexedInterval b).low :=
  IntervalKey.low_le_of_le
    (Prod.Lex.monotone_fst a.down b.down (ULift.down_le.mpr h.le))

theorem indexed_order_allows_equal_lows :
    indexedZero < indexedOne ∧ (indexedInterval indexedZero).low = (indexedInterval indexedOne).low ∧
      ¬Function.Injective indexedInterval :=
  ⟨by decide, rfl, indexed_projection_not_injective⟩

theorem indexed_contract :
    IntervalSet.Laws (IntervalTree.deleteOps indexedInterval)
      (IntervalTree.search indexedInterval) indexedInterval
      (fun t => Trees.setTree (Trees.Cached.erase t)) (IntervalTree.Valid indexedInterval) :=
  IntervalTree.intervalSet_laws indexedInterval indexed_compatible

def indexedWord : List (AbstractSet.Update IndexedKey) :=
  [.insert indexedZero, .insert indexedOne, .insert indexedZero, .delete indexedZero, .delete indexedOne]
def indexedPrefix (n : Nat) : BinaryTree (IndexedKey × Nat) :=
  AbstractSet.execute (IntervalTree.deleteOps indexedInterval) (indexedWord.take n) .nil

theorem indexed_prefix_valid (n : Nat) : IntervalTree.Valid indexedInterval (indexedPrefix n) :=
  indexed_contract.toDeleteLaws.prefix_valid indexedWord n indexed_contract.empty_valid

theorem indexed_prefix_inorder (n : Nat) :
    Trees.inorder (Trees.Cached.erase (indexedPrefix n)) =
      AbstractSet.execute OrderedList.ops (indexedWord.take n) [] :=
  (IntervalTree.inorder_refinement indexedInterval).execute_from_empty OrderedList.laws
    (indexedWord.take n)

theorem indexed_member_semantics (n : Nat) (key : IndexedKey) :
    OrderedMap.containsKey key (indexedPrefix n) = true ↔
      ((indexedWord.take n).foldl AbstractSet.meaningStep (fun _ => False)) key :=
  indexed_contract.toDeleteLaws.member_execute (indexedWord.take n) indexed_contract.empty_valid key

theorem indexed_overlap_semantics (n : Nat) (query : NKey) :
    IntervalTree.search indexedInterval (indexedPrefix n) query = true ↔
      IntervalSet.HasOverlap
        (indexedInterval '' ((indexedWord.take n).foldl AbstractSet.meaningStep (fun _ => False)))
        query :=
  indexed_contract.search_execute (indexedWord.take n) indexed_contract.empty_valid query

theorem indexed_point_semantics (n point : Nat) :
    IntervalTree.searchPoint indexedInterval (indexedPrefix n) point = true ↔
      ∃ key ∈ Trees.setTree (Trees.Cached.erase (indexedPrefix n)),
        IntervalTree.ContainsPoint point (indexedInterval key) :=
  IntervalTree.searchPoint_correct_of_strict indexedInterval indexed_compatible
    (indexed_prefix_valid n).1 (indexed_prefix_valid n).2 point

theorem indexed_prefix_shapes :
    (List.range 6).map indexedPrefix = [.nil, indexedFirst, indexedTree, indexedTree, indexedLast, .nil] :=
  rfl

theorem indexed_prefix_inorders :
    (List.range 6).map (fun n => Trees.inorder (Trees.Cached.erase (indexedPrefix n))) =
      [[], [indexedZero], [indexedZero, indexedOne], [indexedZero, indexedOne], [indexedOne], []] := rfl

theorem indexed_prefix_readers :
    (List.range 6).map (fun n => IntervalTree.maxHi (indexedPrefix n)) = [0, 8, 8, 8, 8, 0] := rfl

theorem indexed_membership_vectors :
    [indexedZero, indexedOne].map (fun key =>
      (List.range 6).map (fun n => OrderedMap.containsKey key (indexedPrefix n))) =
      [[false, true, true, true, false, false], [false, false, true, true, true, false]] := rfl

theorem indexed_overlap_vectors :
    [eightPoint, ninePoint].map (fun query =>
      (List.range 6).map (fun n => IntervalTree.search indexedInterval (indexedPrefix n) query)) =
      [[false, true, true, true, true, false], [false, false, false, false, false, false]] := rfl

theorem indexed_point_vectors :
    [8, 9].map (fun point =>
      (List.range 6).map (fun n => IntervalTree.searchPoint indexedInterval (indexedPrefix n) point)) =
      [[false, true, true, true, true, false], [false, false, false, false, false, false]] := rfl

theorem indexed_delete_retains_coverage :
    OrderedMap.containsKey indexedZero indexedLast = false ∧
    OrderedMap.containsKey indexedOne indexedLast = true ∧
    IntervalTree.search indexedInterval indexedLast eightPoint = true ∧
    IntervalTree.searchPoint indexedInterval indexedLast 8 = true := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · apply (indexed_contract.overlap indexedLast
      ⟨indexedLast_valid, indexed_updates_strict.2.2⟩ eightPoint).mpr
    apply (IntervalSet.hasOverlap_image_iff indexedInterval _ eightPoint).mpr
    exact ⟨indexedOne, by simp [indexedLast], by decide⟩
  · apply (IntervalTree.searchPoint_correct_of_strict indexedInterval indexed_compatible
      indexedLast_valid indexed_updates_strict.2.2 8).mpr
    exact ⟨indexedOne, by simp [indexedLast], by decide⟩

def indexedLater : IndexedKey := ⟨toLex (maxRight, 0)⟩
def indexedSearchTree : BinaryTree (IndexedKey × Nat) :=
  .node (indexedOne, 10) (.node (indexedZero, 8) .nil .nil) (.node (indexedLater, 10) .nil .nil)

theorem indexedSearchTree_valid : IntervalTree.Valid indexedInterval indexedSearchTree := by
  constructor
  · simp only [indexedSearchTree, IntervalTree.cacheValid_node, IntervalTree.cacheValid_nil]
    decide
  · change [indexedZero, indexedOne, indexedLater].Pairwise (· < ·)
    decide

theorem indexedSearchTree_lowOrdered : IntervalTree.LowOrdered indexedInterval indexedSearchTree :=
  IntervalTree.lowOrdered_of_strict indexedInterval indexed_compatible indexedSearchTree_valid.2

theorem indexedSearchTree_semantics (query : NKey) :
    IntervalTree.search indexedInterval indexedSearchTree query = true ↔
      IntervalSet.HasOverlap
        (indexedInterval '' Trees.setTree (Trees.Cached.erase indexedSearchTree)) query :=
  indexed_contract.overlap indexedSearchTree indexedSearchTree_valid query

theorem indexedSearchTree_answers :
    [eightPoint, tenPoint, ninePoint].map (IntervalTree.search indexedInterval indexedSearchTree) =
      [true, true, true] := rfl

/-! The existing opposite-universe fixture has small keys and larger endpoints. -/
theorem lifted_compatible :
    ∀ a b : Fin 2, a < b → (liftedInterval a).low ≤ (liftedInterval b).low := by decide

theorem lifted_valid : IntervalTree.Valid liftedInterval liftedEndpoints := by
  refine ⟨liftedEndpoints_valid, ?_⟩
  rw [liftedEndpoints_inorder]
  change ([0, 1] : List (Fin 2)).Pairwise (· < ·)
  decide

theorem lifted_contract :
    IntervalSet.Laws (IntervalTree.deleteOps liftedInterval)
      (IntervalTree.search liftedInterval) liftedInterval
      (fun t => Trees.setTree (Trees.Cached.erase t)) (IntervalTree.Valid liftedInterval) :=
  IntervalTree.intervalSet_laws liftedInterval lifted_compatible

def liftedQuery (point : Nat) : IntervalKey (ULift.{1} Nat) :=
  IntervalKey.ofBounds ⟨point⟩ ⟨point⟩ le_rfl

theorem lifted_semantics (query : IntervalKey (ULift.{1} Nat)) :
    IntervalTree.search liftedInterval liftedEndpoints query = true ↔
      IntervalSet.HasOverlap (liftedInterval '' Trees.setTree (Trees.Cached.erase liftedEndpoints))
        query :=
  lifted_contract.overlap liftedEndpoints lifted_valid query

theorem lifted_point_semantics (point : ULift.{1} Nat) :
    IntervalTree.searchPoint liftedInterval liftedEndpoints point = true ↔
      ∃ key ∈ Trees.setTree (Trees.Cached.erase liftedEndpoints),
        IntervalTree.ContainsPoint point (liftedInterval key) :=
  IntervalTree.searchPoint_correct_of_strict liftedInterval lifted_compatible
    lifted_valid.1 lifted_valid.2 point

theorem lifted_answers :
    IntervalTree.search liftedInterval liftedEndpoints (liftedQuery 4) = true ∧
    IntervalTree.search liftedInterval liftedEndpoints (liftedQuery 5) = false ∧
    IntervalTree.searchPoint liftedInterval liftedEndpoints ⟨4⟩ = true ∧
    IntervalTree.searchPoint liftedInterval liftedEndpoints ⟨5⟩ = false := ⟨rfl, rfl, rfl, rfl⟩

/-! O17: finite negative maxima, a positive insertion and exact restoration. -/
abbrev ZKey := IntervalKey (WithBot Int)
abbrev ZTree := BinaryTree (ZKey × WithBot Int)
def negativeStates : List ZTree :=
  [negativeMaximum, negativeInserted, IntervalTree.delete id negativeNew negativeInserted]
def negativePoints : List (WithBot Int) :=
  [((-6 : Int) : WithBot Int), ((-2 : Int) : WithBot Int), ((-9 : Int) : WithBot Int),
    ((0 : Int) : WithBot Int), ((2 : Int) : WithBot Int), ⊥]
def negativeQuery (point : WithBot Int) : ZKey := IntervalKey.ofBounds point point le_rfl

theorem negative_state_valid {t : ZTree} (member : t ∈ negativeStates) : IntervalTree.Valid id t := by
  simp only [negativeStates, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact ⟨negativeMaximum_valid, negative_source_strict⟩
  · exact ⟨negative_updates_valid.1, negative_updated_strict⟩
  · exact (IntervalTree.set_laws id).delete_valid negativeNew negativeInserted
      ⟨negative_updates_valid.1, negative_updated_strict⟩

theorem negative_overlap_semantics {t : ZTree} (member : t ∈ negativeStates) (query : ZKey) :
    IntervalTree.search id t query = true ↔
      IntervalSet.HasOverlap (Trees.setTree (Trees.Cached.erase t)) query :=
  IntervalTree.search_correct_book (negative_state_valid member).1 (negative_state_valid member).2 query

theorem negative_point_semantics {t : ZTree} (member : t ∈ negativeStates) (point : WithBot Int) :
    IntervalTree.searchPoint id t point = true ↔
      ∃ key ∈ Trees.setTree (Trees.Cached.erase t), IntervalTree.ContainsPoint point key :=
  IntervalTree.searchPoint_correct_book (negative_state_valid member).1
    (negative_state_valid member).2 point

theorem negative_overlap_table :
    negativeStates.map (fun t => negativePoints.map (fun point =>
      IntervalTree.search id t (negativeQuery point))) =
      [[true, true, false, false, false, false],
       [true, true, false, true, true, false],
       [true, true, false, false, false, false]] := rfl

theorem negative_point_table :
    negativeStates.map (fun t => negativePoints.map (IntervalTree.searchPoint id t)) =
      [[true, true, false, false, false, false],
       [true, true, false, true, true, false],
       [true, true, false, false, false, false]] := rfl

def negativeSpan : ZKey :=
  IntervalKey.ofBounds ((-6 : Int) : WithBot Int) ((-5 : Int) : WithBot Int) (by decide)

theorem negative_span_root_contact : IntervalTree.search id negativeMaximum negativeSpan = true := by
  apply (negative_overlap_semantics (by simp [negativeStates]) negativeSpan).mpr
  exact ⟨negativeRoot, by simp [negativeMaximum], by decide⟩

/-! Deferred O06/O07 observations reuse the accepted update results. -/
theorem whole_key_delete_keeps_coverage :
    OrderedMap.containsKey d (IntervalTree.delete id d mainTree) = false ∧
    IntervalTree.search id (IntervalTree.delete id d mainTree) d = true ∧
    IntervalTree.searchPoint id (IntervalTree.delete id d mainTree) 9 = true := by
  rw [successor_root_recomputed]
  refine ⟨rfl, ?_, ?_⟩
  · apply (IntervalTree.search_correct_book successor_delete_valid successor_delete_strict d).mpr
    exact ⟨c, by simp [rootDeleted, mainLeft, leaf], by decide⟩
  · apply (IntervalTree.searchPoint_correct_book successor_delete_valid successor_delete_strict 9).mpr
    exact ⟨c, by simp [rootDeleted, mainLeft, leaf], by decide⟩

def fallingTrees : List NTree := [mainTree, largestDeleted, twoMaximaDeleted]

theorem falling_valid {t : NTree} (member : t ∈ fallingTrees) : IntervalTree.Valid id t := by
  simp only [fallingTrees, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact ⟨mainTree_valid, mainTree_strict⟩
  · exact ⟨largestDeleted_valid, largestDeleted_strict⟩
  · exact ⟨twoMaximaDeleted_valid, twoMaximaDeleted_strict⟩

theorem falling_overlap_semantics {t : NTree} (member : t ∈ fallingTrees) (query : NKey) :
    IntervalTree.search id t query = true ↔
      IntervalSet.HasOverlap (Trees.setTree (Trees.Cached.erase t)) query :=
  IntervalTree.search_correct_book (falling_valid member).1 (falling_valid member).2 query

theorem falling_point_semantics {t : NTree} (member : t ∈ fallingTrees) (point : Nat) :
    IntervalTree.searchPoint id t point = true ↔
      ∃ key ∈ Trees.setTree (Trees.Cached.erase t), IntervalTree.ContainsPoint point key :=
  IntervalTree.searchPoint_correct_book (falling_valid member).1 (falling_valid member).2 point

theorem falling_point_table :
    fallingTrees.map (fun t => [30, 20, 18].map (IntervalTree.searchPoint id t)) =
      [[true, true, true], [false, true, true], [false, false, true]] := rfl

theorem falling_overlap_table :
    fallingTrees.map (fun t => [30, 20, 18].map (fun point =>
      IntervalTree.search id t (IntervalKey.ofBounds point point le_rfl))) =
      [[true, true, true], [false, true, true], [false, false, true]] := rfl

end Examples.IntervalTreeSearch
