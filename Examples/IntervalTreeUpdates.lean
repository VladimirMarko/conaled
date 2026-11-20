import Applications.Search.IntervalTree.Refinement
import Examples.IntervalTreeFoundations

/-! Connected cases for literal interval-tree updates and their separate raw,
cache and strict-list contracts. See `docs/research/fdsa-interval-updates.md`.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.IntervalTreeUpdates
open Search

abbrev NKey := IntervalKey Nat
abbrev NTree := BinaryTree (NKey × Nat)

def leaf (a : NKey) (m : Nat) : NTree := .node (a, m) .nil .nil

def singletonKey : NKey := IntervalKey.ofBounds 2 5 (by decide)

theorem literal_singleton :
    IntervalTree.insert id singletonKey .nil = leaf singletonKey 5 := rfl

theorem literal_singleton_valid : IntervalTree.CacheValid id (leaf singletonKey 5) := by
  rw [← literal_singleton]
  exact IntervalTree.insert_cacheValid id singletonKey (IntervalTree.cacheValid_nil id)

theorem literal_singleton_observations :
    Trees.inorder (Trees.Cached.erase (leaf singletonKey 5)) = [singletonKey] ∧
    IntervalTree.maxHi (leaf singletonKey 5) = 5 := ⟨rfl, rfl⟩

theorem corrupt_singleton_strict :
    OrderedList.Strict (Trees.inorder (Trees.Cached.erase (leaf singletonKey 99))) :=
  OrderedList.strict_singleton singletonKey

theorem matching_corrupt_leaf_unchanged :
    IntervalTree.insert id singletonKey (leaf singletonKey 99) = leaf singletonKey 99 :=
  IntervalTree.insert_eq_root id singletonKey 99 .nil .nil

theorem matching_corrupt_leaf_still_invalid :
    ¬IntervalTree.CacheValid id (IntervalTree.insert id singletonKey (leaf singletonKey 99)) := by
  rw [matching_corrupt_leaf_unchanged]
  intro valid
  exact (by decide : (99 : Nat) ≠ 5) valid.2.2

theorem empty_operations :
    IntervalTree.delete id singletonKey (.nil : NTree) = .nil ∧
    IntervalTree.splitMin id (.nil : NTree) = none := ⟨rfl, rfl⟩

theorem singleton_extraction :
    IntervalTree.splitMin id (leaf singletonKey 5) = some (singletonKey, .nil) := rfl

theorem singleton_nonempty_extraction :
    IntervalTree.splitMinNonempty id (leaf singletonKey 5) (by intro h; cases h) =
      (singletonKey, .nil) :=
  IntervalTree.splitMinNonempty_eq id (by intro h; cases h) singleton_extraction

theorem absent_delete_repairs_visited_leaf :
    IntervalTree.delete id IntervalTreeFoundations.zeroPoint (leaf singletonKey 99) =
      leaf singletonKey 5 := rfl

theorem absent_delete_repaired_leaf_valid :
    IntervalTree.CacheValid id
      (IntervalTree.delete id IntervalTreeFoundations.zeroPoint (leaf singletonKey 99)) := by
  rw [absent_delete_repairs_visited_leaf]
  exact literal_singleton_valid

theorem absent_delete_preserves_contents :
    Trees.inorder (Trees.Cached.erase
      (IntervalTree.delete id IntervalTreeFoundations.zeroPoint (leaf singletonKey 99))) =
      [singletonKey] :=
  (IntervalTree.inorder_delete id IntervalTreeFoundations.zeroPoint corrupt_singleton_strict).trans rfl

/-! O02, O06, O07: independent complete shapes, contents and falling maxima. -/
def a : NKey := IntervalKey.ofBounds 1 2 (by decide)
def b : NKey := IntervalKey.ofBounds 3 6 (by decide)
def c : NKey := IntervalKey.ofBounds 5 20 (by decide)
def d : NKey := IntervalKey.ofBounds 8 9 (by decide)
def e : NKey := IntervalKey.ofBounds 10 10 (by decide)
def f : NKey := IntervalKey.ofBounds 15 18 (by decide)
def g : NKey := IntervalKey.ofBounds 22 30 (by decide)
def x : NKey := IntervalKey.ofBounds 4 40 (by decide)
def mainLeft : NTree := .node (b, 20) (leaf a 2) (leaf c 20)
def mainRight : NTree := .node (f, 30) (leaf e 10) (leaf g 30)
def mainTree : NTree := .node (d, 30) mainLeft mainRight
def insertedTree : NTree :=
  .node (d, 40) (.node (b, 40) (leaf a 2) (.node (c, 40) (leaf x 40) .nil)) mainRight
def rightResidual : NTree := .node (f, 30) .nil (leaf g 30)
def rootDeleted : NTree := .node (e, 30) mainLeft rightResidual
def rightReduced : NTree := .node (f, 18) (leaf e 10) .nil
def largestDeleted : NTree := .node (d, 20) mainLeft rightReduced
def twoMaximaDeleted : NTree :=
  .node (d, 18) (.node (b, 6) (leaf a 2) .nil) rightReduced

theorem mainTree_valid : IntervalTree.CacheValid id mainTree := by
  simp only [mainTree, mainLeft, mainRight, leaf,
    IntervalTree.cacheValid_node, IntervalTree.cacheValid_nil]
  decide

theorem mainTree_strict : OrderedList.Strict (Trees.inorder (Trees.Cached.erase mainTree)) := by
  change [a, b, c, d, e, f, g].Pairwise (· < ·)
  decide

theorem deep_insert_shape : IntervalTree.insert id x mainTree = insertedTree := rfl

theorem deep_insert_contents :
    Trees.inorder (Trees.Cached.erase (IntervalTree.insert id x mainTree)) =
      [a, b, x, c, d, e, f, g] :=
  (IntervalTree.inorder_insert id x mainTree_strict).trans rfl

theorem deep_insert_valid : IntervalTree.CacheValid id insertedTree := by
  rw [← deep_insert_shape]
  exact IntervalTree.insert_cacheValid id x mainTree_valid

theorem deep_insert_strict : OrderedList.Strict (Trees.inorder (Trees.Cached.erase insertedTree)) := by
  rw [← deep_insert_shape]
  exact IntervalTree.strict_inorder_insert id x mainTree_strict

theorem deep_delete_restores_shape : IntervalTree.delete id x insertedTree = mainTree := rfl

theorem deep_delete_restores_contents :
    Trees.inorder (Trees.Cached.erase (IntervalTree.delete id x insertedTree)) =
      [a, b, c, d, e, f, g] :=
  (IntervalTree.inorder_delete id x deep_insert_strict).trans rfl

theorem deep_delete_preserves_cache :
    IntervalTree.CacheValid id (IntervalTree.delete id x insertedTree) :=
  IntervalTree.delete_cacheValid id x deep_insert_valid

theorem successor_extracted :
    IntervalTree.splitMin id mainRight = some (e, rightResidual) := rfl

theorem successor_residual_valid : IntervalTree.CacheValid id rightResidual :=
  IntervalTree.splitMin_cacheValid id mainTree_valid.2.1 successor_extracted

theorem successor_root_recomputed : IntervalTree.delete id d mainTree = rootDeleted := by
  exact IntervalTree.delete_eq_root_splitMin id d 30 successor_extracted

theorem successor_root_not_own_high :
    IntervalTree.maxHi rootDeleted = 30 ∧ e.high = 10 ∧
      IntervalTree.maxHi rootDeleted ≠ e.high := ⟨rfl, rfl, by decide⟩

theorem successor_delete_valid : IntervalTree.CacheValid id rootDeleted := by
  rw [← successor_root_recomputed]
  exact IntervalTree.delete_cacheValid id d mainTree_valid

theorem successor_delete_contents :
    Trees.inorder (Trees.Cached.erase (IntervalTree.delete id d mainTree)) =
      [a, b, c, e, f, g] :=
  (IntervalTree.inorder_delete id d mainTree_strict).trans rfl

theorem successor_delete_strict : OrderedList.Strict (Trees.inorder (Trees.Cached.erase rootDeleted)) := by
  rw [← successor_root_recomputed]
  exact IntervalTree.strict_inorder_delete id d mainTree_strict

theorem first_maximum_falls : IntervalTree.delete id g mainTree = largestDeleted := rfl
theorem second_maximum_falls :
    IntervalTree.delete id c largestDeleted = twoMaximaDeleted := rfl

theorem largestDeleted_valid : IntervalTree.CacheValid id largestDeleted := by
  rw [← first_maximum_falls]
  exact IntervalTree.delete_cacheValid id g mainTree_valid

theorem largestDeleted_strict :
    OrderedList.Strict (Trees.inorder (Trees.Cached.erase largestDeleted)) := by
  rw [← first_maximum_falls]
  exact IntervalTree.strict_inorder_delete id g mainTree_strict

theorem falling_maxima_contents :
    Trees.inorder (Trees.Cached.erase largestDeleted) = [a, b, c, d, e, f] ∧
    Trees.inorder (Trees.Cached.erase twoMaximaDeleted) = [a, b, d, e, f] := by
  constructor
  · rw [← first_maximum_falls]
    exact (IntervalTree.inorder_delete id g mainTree_strict).trans rfl
  · rw [← second_maximum_falls]
    exact (IntervalTree.inorder_delete id c largestDeleted_strict).trans rfl

theorem twoMaximaDeleted_valid : IntervalTree.CacheValid id twoMaximaDeleted := by
  rw [← second_maximum_falls]
  exact IntervalTree.delete_cacheValid id c largestDeleted_valid

theorem twoMaximaDeleted_strict :
    OrderedList.Strict (Trees.inorder (Trees.Cached.erase twoMaximaDeleted)) := by
  rw [← second_maximum_falls]
  exact IntervalTree.strict_inorder_delete id c largestDeleted_strict

theorem falling_maxima_readers :
    [IntervalTree.maxHi mainTree, IntervalTree.maxHi largestDeleted,
      IntervalTree.maxHi twoMaximaDeleted] = [30, 20, 18] := rfl

/-! O03: only visited ancestors are reconstructed. -/
def pointOne : NKey := IntervalKey.ofBounds 1 1 (by decide)
def pointThree : NKey := IntervalKey.ofBounds 3 3 (by decide)
def pointFive : NKey := IntervalKey.ofBounds 5 5 (by decide)
def pointSix : NKey := IntervalKey.ofBounds 6 6 (by decide)
def wrongAncestor : NTree := .node (pointThree, 100) (leaf pointOne 1) .nil
def corruptSibling : NTree := .node (pointThree, 100) (leaf pointOne 99) (leaf pointFive 5)
def corruptSiblingInserted : NTree :=
  .node (pointThree, 99) (leaf pointOne 99) (.node (pointFive, 6) .nil (leaf pointSix 6))

theorem duplicate_repairs_ancestor :
    IntervalTree.insert id pointOne wrongAncestor =
      .node (pointThree, 3) (leaf pointOne 1) .nil := rfl

theorem duplicate_repaired_ancestor_valid :
    IntervalTree.CacheValid id (IntervalTree.insert id pointOne wrongAncestor) := by
  rw [duplicate_repairs_ancestor]
  simp only [leaf, IntervalTree.cacheValid_node, IntervalTree.cacheValid_nil]
  decide

theorem unvisited_corruption_remains :
    IntervalTree.insert id pointSix corruptSibling = corruptSiblingInserted := rfl

theorem unvisited_corruption_invalid : ¬IntervalTree.CacheValid id corruptSiblingInserted := by
  intro valid
  exact (by decide : (99 : Nat) ≠ 1) valid.1.2.2

theorem corruptSibling_strict :
    OrderedList.Strict (Trees.inorder (Trees.Cached.erase corruptSibling)) := by
  change [pointOne, pointThree, pointFive].Pairwise (· < ·)
  decide

theorem corruptSibling_insert_contents :
    Trees.inorder (Trees.Cached.erase corruptSiblingInserted) =
      [pointOne, pointThree, pointFive, pointSix] := by
  rw [← unvisited_corruption_remains]
  exact (IntervalTree.inorder_insert id pointSix corruptSibling_strict).trans rfl

theorem corruptSibling_insert_strict :
    OrderedList.Strict (Trees.inorder (Trees.Cached.erase corruptSiblingInserted)) := by
  rw [← unvisited_corruption_remains]
  exact IntervalTree.strict_inorder_insert id pointSix corruptSibling_strict

theorem empty_right_returns_corrupt_left :
    IntervalTree.delete id pointThree (.node (pointThree, 100) (leaf pointOne 99) .nil) =
      leaf pointOne 99 := IntervalTree.delete_eq_root_nil id pointThree 100 (leaf pointOne 99)

/-! O04: extracting the unique maximum contributor lowers the residual maximum. -/
def s : NKey := IntervalKey.ofBounds 1 40 (by decide)
def t : NKey := IntervalKey.ofBounds 2 3 (by decide)
def u : NKey := IntervalKey.ofBounds 4 5 (by decide)
def v : NKey := IntervalKey.ofBounds 6 7 (by decide)
def splitInput : NTree := .node (u, 40) (.node (s, 40) .nil (leaf t 3)) (leaf v 7)
def splitResidual : NTree := .node (u, 7) (leaf t 3) (leaf v 7)

theorem splitInput_valid : IntervalTree.CacheValid id splitInput := by
  simp only [splitInput, leaf, IntervalTree.cacheValid_node, IntervalTree.cacheValid_nil]
  decide

theorem split_maximum_falls : IntervalTree.splitMin id splitInput = some (s, splitResidual) := rfl

theorem split_nonempty_pair :
    IntervalTree.splitMinNonempty id splitInput (by intro h; cases h) = (s, splitResidual) :=
  IntervalTree.splitMinNonempty_eq id (by intro h; cases h) split_maximum_falls

theorem split_residual_valid : IntervalTree.CacheValid id splitResidual :=
  IntervalTree.splitMin_cacheValid id splitInput_valid split_maximum_falls

theorem split_raw_contents :
    s :: Trees.inorder (Trees.Cached.erase splitResidual) =
      Trees.inorder (Trees.Cached.erase splitInput) :=
  IntervalTree.splitMin_inorder id split_maximum_falls

theorem split_maximum_readers :
    IntervalTree.maxHi splitInput = 40 ∧ IntervalTree.maxHi splitResidual = 7 := ⟨rfl, rfl⟩

theorem splitInput_strict : OrderedList.Strict (Trees.inorder (Trees.Cached.erase splitInput)) := by
  change [s, t, u, v].Pairwise (· < ·)
  decide

theorem split_residual_maximum_attained :
    ∃ key ∈ Trees.setTree (Trees.Cached.erase splitResidual), key.high = 7 :=
  IntervalTree.maxHi_attained id split_residual_valid (by intro h; cases h)

/-! O05: raw leftmost extraction does not promise leastness or cache repair. -/
def pointTwo : NKey := IntervalKey.ofBounds 2 2 (by decide)
def rawSplitInput : NTree := .node (pointOne, 99) (leaf pointFive 77) (leaf pointTwo 0)
def rawSplitResidual : NTree := .node (pointOne, 1) .nil (leaf pointTwo 0)

theorem malformed_split :
    IntervalTree.splitMin id rawSplitInput = some (pointFive, rawSplitResidual) := rfl

theorem malformed_split_contents :
    pointFive :: Trees.inorder (Trees.Cached.erase rawSplitResidual) =
      Trees.inorder (Trees.Cached.erase rawSplitInput) :=
  IntervalTree.splitMin_inorder id malformed_split

theorem malformed_split_not_least :
    pointOne ∈ Trees.inorder (Trees.Cached.erase rawSplitInput) ∧ pointOne < pointFive := by
  decide

theorem malformed_residual_invalid : ¬IntervalTree.CacheValid id rawSplitResidual := by
  intro valid
  exact (by decide : (0 : Nat) ≠ 2) valid.2.1.2.2

theorem malformed_residual_misses_high :
    pointTwo ∈ Trees.inorder (Trees.Cached.erase rawSplitResidual) ∧
      IntervalTree.maxHi rawSplitResidual < pointTwo.high := by decide

theorem malformed_input_invalid : ¬IntervalTree.CacheValid id rawSplitInput := by
  intro valid
  exact (by decide : (77 : Nat) ≠ 5) valid.1.2.2

theorem malformed_input_unordered :
    ¬OrderedList.Strict (Trees.inorder (Trees.Cached.erase rawSplitInput)) := by
  change ¬[pointFive, pointOne, pointTwo].Pairwise (· < ·)
  decide

theorem successor_join_valid : IntervalTree.CacheValid id (IntervalTree.join id mainLeft mainRight) :=
  IntervalTree.join_cacheValid id mainTree_valid.1 mainTree_valid.2.1

theorem successor_join_contents :
    Trees.inorder (Trees.Cached.erase (IntervalTree.join id mainLeft mainRight)) =
      [a, b, c, e, f, g] := (IntervalTree.inorder_join id mainLeft mainRight).trans rfl

open IntervalTreeFoundations

/-! O08: complete-key order is enough for the list equalities, even with bad caches. -/
def corruptTiesInserted : NTree :=
  .node (lowFive, 99) (.node (lowTwo, 4) .nil (leaf lowFour 4)) (leaf lowEight 99)
def corruptTiesDeleted : NTree := .node (lowFive, 99) (leaf lowTwo 99) .nil

theorem corruptTies_strict :
    OrderedList.Strict (Trees.inorder (Trees.Cached.erase corruptedEqualLows)) := by
  change [lowTwo, lowFive, lowEight].Pairwise (· < ·)
  decide

theorem corrupt_ties_insert_shape :
    IntervalTree.insert id lowFour corruptedEqualLows = corruptTiesInserted := rfl
theorem corrupt_ties_delete_shape :
    IntervalTree.delete id lowEight corruptedEqualLows = corruptTiesDeleted := rfl

theorem corrupt_ties_insert_contents :
    Trees.inorder (Trees.Cached.erase corruptTiesInserted) = [lowTwo, lowFour, lowFive, lowEight] := by
  rw [← corrupt_ties_insert_shape]
  exact (IntervalTree.inorder_insert id lowFour corruptTies_strict).trans rfl

theorem corrupt_ties_delete_contents :
    Trees.inorder (Trees.Cached.erase corruptTiesDeleted) = [lowTwo, lowFive] := by
  rw [← corrupt_ties_delete_shape]
  exact (IntervalTree.inorder_delete id lowEight corruptTies_strict).trans rfl

theorem corrupt_ties_outputs_strict :
    OrderedList.Strict (Trees.inorder (Trees.Cached.erase corruptTiesInserted)) ∧
    OrderedList.Strict (Trees.inorder (Trees.Cached.erase corruptTiesDeleted)) := by
  rw [← corrupt_ties_insert_shape, ← corrupt_ties_delete_shape]
  exact ⟨IntervalTree.strict_inorder_insert id lowFour corruptTies_strict,
    IntervalTree.strict_inorder_delete id lowEight corruptTies_strict⟩

theorem corrupt_ties_outputs_invalid :
    ¬IntervalTree.CacheValid id corruptTiesInserted ∧
    ¬IntervalTree.CacheValid id corruptTiesDeleted := by
  constructor
  · intro valid
    exact (by decide : (99 : Nat) ≠ 8) valid.2.1.2.2
  · intro valid
    exact (by decide : (99 : Nat) ≠ 2) valid.1.2.2

/-! O09: caches do not enforce search ordering or set-deletion semantics. -/
def unorderedInserted : NTree :=
  .node (onePoint, 3) (leaf twoPoint 2) (.node (zeroPoint, 3) .nil (leaf pointThree 3))
def unorderedDeleted : NTree := .node (zeroPoint, 3) (leaf twoPoint 2) (leaf pointThree 3)

theorem unordered_insert_shape : IntervalTree.insert id pointThree unordered = unorderedInserted := rfl
theorem unordered_delete_shape : IntervalTree.delete id onePoint unorderedInserted = unorderedDeleted := rfl

theorem unordered_updates_valid :
    IntervalTree.CacheValid id unorderedInserted ∧ IntervalTree.CacheValid id unorderedDeleted := by
  have hi : IntervalTree.CacheValid id unorderedInserted := by
    rw [← unordered_insert_shape]
    exact IntervalTree.insert_cacheValid id pointThree unordered_valid
  exact ⟨hi, by rw [← unordered_delete_shape]; exact IntervalTree.delete_cacheValid id onePoint hi⟩

theorem unordered_updates_still_unordered :
    ¬OrderedList.Strict (Trees.inorder (Trees.Cached.erase unorderedInserted)) ∧
    ¬OrderedList.Strict (Trees.inorder (Trees.Cached.erase unorderedDeleted)) := by
  change ¬[twoPoint, onePoint, zeroPoint, pointThree].Pairwise (· < ·) ∧
    ¬[twoPoint, zeroPoint, pointThree].Pairwise (· < ·)
  decide

theorem unordered_delete_misses_key : IntervalTree.delete id zeroPoint unordered = unordered := rfl

theorem unordered_raw_update_transport (query : NKey) :
    Trees.Cached.erase (IntervalTree.insert id query unordered) =
      OrderedTree.insert query (Trees.Cached.erase unordered) ∧
    Trees.Cached.erase (IntervalTree.delete id query unordered) =
      OrderedTree.deleteBy id query (Trees.Cached.erase unordered) :=
  ⟨IntervalTree.erase_insert id query unordered, IntervalTree.erase_delete id query unordered⟩

theorem unordered_delete_not_list_delete :
    Trees.inorder (Trees.Cached.erase (IntervalTree.delete id zeroPoint unordered)) ≠
      OrderedList.delete zeroPoint (Trees.inorder (Trees.Cached.erase unordered)) := by decide

theorem unordered_insert_duplicates_key :
    Trees.inorder (Trees.Cached.erase (IntervalTree.insert id twoPoint unordered)) =
      [twoPoint, onePoint, zeroPoint, twoPoint] := rfl

theorem unordered_insert_not_list_insert :
    Trees.inorder (Trees.Cached.erase (IntervalTree.insert id twoPoint unordered)) ≠
      OrderedList.insert twoPoint (Trees.inorder (Trees.Cached.erase unordered)) := by decide

def duplicateTree : NTree := .node (onePoint, 1) .nil (leaf onePoint 1)

theorem duplicateTree_valid : IntervalTree.CacheValid id duplicateTree := by
  simp only [duplicateTree, leaf, IntervalTree.cacheValid_node, IntervalTree.cacheValid_nil]
  decide

theorem duplicateTree_not_strict :
    ¬OrderedList.Strict (Trees.inorder (Trees.Cached.erase duplicateTree)) := by
  change ¬[onePoint, onePoint].Pairwise (· < ·)
  decide

theorem duplicate_delete_retains_key :
    IntervalTree.delete id onePoint duplicateTree = leaf onePoint 1 ∧
    onePoint ∈ Trees.setTree (Trees.Cached.erase (IntervalTree.delete id onePoint duplicateTree)) := by
  constructor
  · rfl
  · change onePoint ∈ Trees.setTree (.node onePoint .nil .nil)
    simp

theorem duplicate_delete_not_set_difference :
    Trees.setTree (Trees.Cached.erase (IntervalTree.delete id onePoint duplicateTree)) ≠
      Trees.setTree (Trees.Cached.erase duplicateTree) \ {onePoint} := by
  intro equal
  have absent := duplicate_delete_retains_key.2
  rw [equal] at absent
  exact absent.2 rfl

/-! O16: keys live in a higher universe and need not project injectively. -/
def indexedFirst : BinaryTree (IndexedKey × Nat) := .node (indexedZero, 8) .nil .nil
def indexedLast : BinaryTree (IndexedKey × Nat) := .node (indexedOne, 8) .nil .nil

theorem indexed_insert_first : IntervalTree.insert indexedInterval indexedZero .nil = indexedFirst := rfl
theorem indexed_insert_second :
    IntervalTree.insert indexedInterval indexedOne indexedFirst = indexedTree := rfl
theorem indexed_insert_duplicate :
    IntervalTree.insert indexedInterval indexedZero indexedTree = indexedTree :=
  IntervalTree.insert_eq_root indexedInterval indexedZero 8 .nil indexedLast
theorem indexed_split :
    IntervalTree.splitMin indexedInterval indexedTree = some (indexedZero, indexedLast) := rfl

theorem indexed_split_nonempty :
    IntervalTree.splitMinNonempty indexedInterval indexedTree (by intro h; cases h) =
      (indexedZero, indexedLast) :=
  IntervalTree.splitMinNonempty_eq indexedInterval (by intro h; cases h) indexed_split
theorem indexed_delete_first :
    IntervalTree.delete indexedInterval indexedZero indexedTree = indexedLast := rfl
theorem indexed_delete_last :
    IntervalTree.delete indexedInterval indexedOne indexedLast = .nil :=
  IntervalTree.delete_eq_root_nil indexedInterval indexedOne 8 .nil

theorem indexedFirst_valid : IntervalTree.CacheValid indexedInterval indexedFirst := by
  rw [← indexed_insert_first]
  exact IntervalTree.insert_cacheValid indexedInterval indexedZero (IntervalTree.cacheValid_nil _)

theorem indexed_updated_valid : IntervalTree.CacheValid indexedInterval indexedTree := by
  rw [← indexed_insert_second]
  exact IntervalTree.insert_cacheValid indexedInterval indexedOne indexedFirst_valid

theorem indexedLast_valid : IntervalTree.CacheValid indexedInterval indexedLast :=
  IntervalTree.splitMin_cacheValid indexedInterval indexed_updated_valid indexed_split

theorem indexed_updates_strict :
    OrderedList.Strict (Trees.inorder (Trees.Cached.erase indexedFirst)) ∧
    OrderedList.Strict (Trees.inorder (Trees.Cached.erase indexedTree)) ∧
    OrderedList.Strict (Trees.inorder (Trees.Cached.erase indexedLast)) := by
  have first : OrderedList.Strict (Trees.inorder (Trees.Cached.erase indexedFirst)) := by
    rw [← indexed_insert_first]
    exact IntervalTree.strict_inorder_insert indexedInterval indexedZero OrderedList.strict_nil
  have second : OrderedList.Strict (Trees.inorder (Trees.Cached.erase indexedTree)) := by
    rw [← indexed_insert_second]
    exact IntervalTree.strict_inorder_insert indexedInterval indexedOne first
  refine ⟨first, second, ?_⟩
  rw [← indexed_delete_first]
  exact IntervalTree.strict_inorder_delete indexedInterval indexedZero second

theorem indexed_update_contents :
    Trees.inorder (Trees.Cached.erase (IntervalTree.insert indexedInterval indexedOne indexedFirst)) =
      [indexedZero, indexedOne] ∧
    Trees.inorder (Trees.Cached.erase (IntervalTree.delete indexedInterval indexedZero indexedTree)) =
      [indexedOne] :=
  ⟨(IntervalTree.inorder_insert indexedInterval indexedOne indexed_updates_strict.1).trans rfl,
    (IntervalTree.inorder_delete indexedInterval indexedZero indexed_updates_strict.2.1).trans rfl⟩

theorem indexed_final_delete_contract :
    IntervalTree.CacheValid indexedInterval
      (IntervalTree.delete indexedInterval indexedOne indexedLast) ∧
    Trees.inorder (Trees.Cached.erase (IntervalTree.delete indexedInterval indexedOne indexedLast)) = [] ∧
    OrderedList.Strict (Trees.inorder (Trees.Cached.erase
      (IntervalTree.delete indexedInterval indexedOne indexedLast))) :=
  ⟨IntervalTree.delete_cacheValid indexedInterval indexedOne indexedLast_valid,
    (IntervalTree.inorder_delete indexedInterval indexedOne indexed_updates_strict.2.2).trans rfl,
    IntervalTree.strict_inorder_delete indexedInterval indexedOne indexed_updates_strict.2.2⟩

theorem indexed_reader_sequence :
    [IntervalTree.maxHi (.nil : BinaryTree (IndexedKey × Nat)), IntervalTree.maxHi indexedFirst,
      IntervalTree.maxHi indexedTree, IntervalTree.maxHi indexedLast,
      IntervalTree.maxHi (IntervalTree.delete indexedInterval indexedOne indexedLast)] =
      [0, 8, 8, 8, 0] := rfl

theorem indexed_remaining_projection :
    (Trees.inorder (Trees.Cached.erase (IntervalTree.delete indexedInterval indexedZero indexedTree))).map
      indexedInterval = [rootEight] := by
  rw [indexed_update_contents.2]
  rfl

theorem indexed_key_delete_not_interval_delete :
    indexedInterval '' Trees.setTree (Trees.Cached.erase
      (IntervalTree.delete indexedInterval indexedZero indexedTree)) ≠
      (indexedInterval '' Trees.setTree (Trees.Cached.erase indexedTree)) \ {rootEight} := by
  intro equal
  have belongs : rootEight ∈ indexedInterval '' Trees.setTree (Trees.Cached.erase
      (IntervalTree.delete indexedInterval indexedZero indexedTree)) := by
    refine ⟨indexedOne, ?_, rfl⟩
    rw [indexed_delete_first]
    simp [indexedLast]
  rw [equal] at belongs
  exact belongs.2 rfl

/-! O17: an inserted positive high can fall back to a negative finite maximum. -/
def negativeNew : IntervalKey (WithBot Int) :=
  IntervalKey.ofBounds ((-7 : Int) : WithBot Int) ((2 : Int) : WithBot Int) (by decide)
def negativeInserted : BinaryTree (IntervalKey (WithBot Int) × WithBot Int) :=
  .node (negativeRoot, ((2 : Int) : WithBot Int))
    (.node (negativeLeft, ((2 : Int) : WithBot Int)) .nil
      (.node (negativeNew, ((2 : Int) : WithBot Int)) .nil .nil))
    (.node (negativeRight, ((-1 : Int) : WithBot Int)) .nil .nil)

theorem negative_insert_shape : IntervalTree.insert id negativeNew negativeMaximum = negativeInserted := rfl
theorem negative_delete_restores_shape :
    IntervalTree.delete id negativeNew negativeInserted = negativeMaximum := rfl

theorem negative_updates_valid :
    IntervalTree.CacheValid id negativeInserted ∧
    IntervalTree.CacheValid id (IntervalTree.delete id negativeNew negativeInserted) := by
  have hi : IntervalTree.CacheValid id negativeInserted := by
    rw [← negative_insert_shape]
    exact IntervalTree.insert_cacheValid id negativeNew negativeMaximum_valid
  exact ⟨hi, IntervalTree.delete_cacheValid id negativeNew hi⟩

theorem negative_source_strict :
    OrderedList.Strict (Trees.inorder (Trees.Cached.erase negativeMaximum)) := by
  change [negativeLeft, negativeRoot, negativeRight].Pairwise (· < ·)
  decide

theorem negative_updated_strict :
    OrderedList.Strict (Trees.inorder (Trees.Cached.erase negativeInserted)) := by
  rw [← negative_insert_shape]
  exact IntervalTree.strict_inorder_insert id negativeNew negative_source_strict

theorem negative_update_contents :
    Trees.inorder (Trees.Cached.erase (IntervalTree.insert id negativeNew negativeMaximum)) =
      [negativeLeft, negativeNew, negativeRoot, negativeRight] ∧
    Trees.inorder (Trees.Cached.erase (IntervalTree.delete id negativeNew negativeInserted)) =
      [negativeLeft, negativeRoot, negativeRight] :=
  ⟨(IntervalTree.inorder_insert id negativeNew negative_source_strict).trans rfl,
    (IntervalTree.inorder_delete id negativeNew negative_updated_strict).trans rfl⟩

theorem negative_maximum_restored :
    IntervalTree.maxHi negativeInserted = ((2 : Int) : WithBot Int) ∧
    IntervalTree.maxHi (IntervalTree.delete id negativeNew negativeInserted) = ((-1 : Int) : WithBot Int) ∧
    IntervalTree.maxHi (.nil : BinaryTree (IntervalKey (WithBot Int) × WithBot Int)) ≠
      ((0 : Int) : WithBot Int) := ⟨rfl, rfl, numeric_zero_is_not_bottom⟩

/-! X01: raw Max data does not supply canonical maximum semantics. -/
section NonlawfulMaximum
local instance constantMax : Max Nat := ⟨fun _ _ => 100⟩

theorem nonlawful_literal_singleton :
    IntervalTree.insert id singletonKey .nil = leaf singletonKey 5 :=
  IntervalTree.insert_nil id singletonKey

theorem nonlawful_smart_singleton :
    IntervalTree.node id .nil singletonKey .nil = leaf singletonKey 100 := by
  rw [IntervalTree.node_eq, IntervalTree.max3_eq]
  rfl

theorem nonlawful_empty_valid : IntervalTree.CacheValid id (.nil : NTree) :=
  IntervalTree.cacheValid_nil id

theorem nonlawful_singletons_same_erasure :
    Trees.Cached.erase (IntervalTree.insert id singletonKey .nil) =
      Trees.Cached.erase (IntervalTree.node id .nil singletonKey .nil) := rfl

theorem nonlawful_singletons_different :
    IntervalTree.insert id singletonKey .nil ≠ IntervalTree.node id .nil singletonKey .nil := by decide

theorem nonlawful_literal_invalid :
    ¬IntervalTree.CacheValid id (IntervalTree.insert id singletonKey .nil) := by
  intro valid
  exact (by decide : (5 : Nat) ≠ 100) valid.2.2

theorem nonlawful_insert_not_preserving :
    ¬∀ t : NTree, IntervalTree.CacheValid id t →
      IntervalTree.CacheValid id (IntervalTree.insert id singletonKey t) := by
  rw [IntervalTree.insert_preserves_cacheValid_iff]
  decide

theorem nonlawful_smart_valid :
    IntervalTree.CacheValid id (IntervalTree.node id .nil singletonKey .nil) :=
  IntervalTree.node_cacheValid id (IntervalTree.cacheValid_nil id) singletonKey
    (IntervalTree.cacheValid_nil id)

theorem nonlawful_smart_unattained :
    ¬∃ key ∈ Trees.setTree (Trees.Cached.erase (IntervalTree.node id .nil singletonKey .nil)),
      key.high = IntervalTree.maxHi (IntervalTree.node id .nil singletonKey .nil) := by
  simp only [IntervalTree.erase_node, Trees.Cached.erase_nil, Trees.setTree_node, Trees.setTree_nil,
    Set.empty_union, Set.union_empty, Set.mem_singleton_iff, exists_eq_left]
  decide

end NonlawfulMaximum

end Examples.IntervalTreeUpdates
