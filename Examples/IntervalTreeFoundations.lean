import Applications.Search.OrderedMap.Membership
import Applications.Search.IntervalTree.Maximum
import Applications.Search.IntervalSet
import Mathlib.Order.Nat
import Mathlib.Order.WithBot

/-! Connected augmented-membership and interval-cache foundation cases.
Independent expectations are described in `docs/research/fdsa-interval-foundations.md`.
These examples keep key identity, geometry, raw readers and validity separate.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.IntervalTreeFoundations
open Search

def functions : BinaryTree (Nat × ULift.{1} (Nat → Nat)) :=
  .node (2, ⟨fun n => n + 20⟩)
    (.node (1, ⟨fun n => n + 10⟩) .nil .nil)
    (.node (3, ⟨fun n => n + 30⟩) .nil .nil)

theorem functions_inorder : Trees.inorder (Trees.Cached.erase functions) = [1, 2, 3] := rfl

theorem functions_ordered : OrderedTree.OrderedBy Prod.fst functions := by
  apply (OrderedTree.orderedBy_iff_map Prod.fst functions).mpr
  apply OrderedTree.ordered_of_inorder_pairwise
  change ([1, 2, 3] : List Nat).Pairwise (· < ·)
  decide

theorem functions_presence_vector :
    [0, 1, 2, 3, 4].map (fun key => OrderedMap.containsKey key functions) =
      [false, true, true, true, false] := rfl

theorem functions_values_vector :
    [0, 1, 2, 3, 4].map (fun key => (OrderedMap.lookup key functions).map
      (fun f => f.down 4)) = [none, some 14, some 24, some 34, none] := rfl

theorem functions_raw_erasure (query : Nat) :
    OrderedMap.containsKey query functions =
      OrderedTree.member query (Trees.Cached.erase functions) :=
  OrderedMap.containsKey_eq_member_erase query functions

theorem functions_semantic_membership (query : Nat) :
    OrderedMap.containsKey query functions = true ↔ query ∈ [1, 2, 3] := by
  simpa only [functions_inorder] using
    OrderedMap.containsKey_eq_true_iff_mem_inorder functions_ordered query

def numericAnnotations : BinaryTree (Nat × Int) :=
  .node (2, 99) (.node (1, -100) .nil .nil) (.node (3, 7) .nil .nil)

/-- Annotation values and their universe can change without changing membership. -/
theorem functions_numeric_presence (query : Nat) :
    OrderedMap.containsKey query functions = OrderedMap.containsKey query numericAnnotations :=
  OrderedMap.containsKey_congr_erase (left := functions) (right := numericAnnotations) rfl query

theorem empty_annotation_carrier (query : Nat) :
    OrderedMap.containsKey query (.nil : BinaryTree (Nat × Empty)) = false :=
  OrderedMap.containsKey_nil query

/-! Empty and a bottom singleton share a reader, but only one has a witness. -/
def zeroPoint : IntervalKey Nat := IntervalKey.ofBounds 0 0 (by decide)

def bottomSingleton : BinaryTree (IntervalKey Nat × Nat) :=
  IntervalTree.node id .nil zeroPoint .nil

theorem empty_valid :
    IntervalTree.CacheValid id (.nil : BinaryTree (IntervalKey Nat × Nat)) :=
  IntervalTree.cacheValid_nil id

theorem bottomSingleton_literal : bottomSingleton = .node (zeroPoint, 0) .nil .nil := rfl

theorem bottomSingleton_valid : IntervalTree.CacheValid id bottomSingleton :=
  IntervalTree.node_cacheValid id (IntervalTree.cacheValid_nil id) zeroPoint
    (IntervalTree.cacheValid_nil id)

theorem empty_bottomSingleton_same_reader :
    IntervalTree.maxHi (.nil : BinaryTree (IntervalKey Nat × Nat)) =
      IntervalTree.maxHi bottomSingleton := rfl

theorem empty_has_no_attainment :
    ¬∃ key ∈ Trees.setTree (Trees.Cached.erase (.nil : BinaryTree (IntervalKey Nat × Nat))),
      key.high = (0 : Nat) := by
  simp

theorem bottomSingleton_attains :
    ∃ key ∈ Trees.setTree (Trees.Cached.erase bottomSingleton), key.high = (0 : Nat) :=
  IntervalTree.maxHi_attained id bottomSingleton_valid (by intro h; cases h)

/-! The greatest key lies right, while the greatest high lies left. -/
def maxLeft : IntervalKey Nat := IntervalKey.ofBounds 1 20 (by decide)
def maxRoot : IntervalKey Nat := IntervalKey.ofBounds 4 5 (by decide)
def maxRight : IntervalKey Nat := IntervalKey.ofBounds 9 10 (by decide)

def highMaximum : BinaryTree (IntervalKey Nat × Nat) :=
  .node (maxRoot, 20) (.node (maxLeft, 20) .nil .nil) (.node (maxRight, 10) .nil .nil)

theorem highMaximum_valid : IntervalTree.CacheValid id highMaximum := by
  change IntervalTree.CacheValid id (IntervalTree.node id
    (IntervalTree.node id .nil maxLeft .nil) maxRoot
    (IntervalTree.node id .nil maxRight .nil))
  exact IntervalTree.node_cacheValid id
    (IntervalTree.node_cacheValid id (IntervalTree.cacheValid_nil id) maxLeft
      (IntervalTree.cacheValid_nil id)) maxRoot
    (IntervalTree.node_cacheValid id (IntervalTree.cacheValid_nil id) maxRight
      (IntervalTree.cacheValid_nil id))

theorem highMaximum_ordered : OrderedTree.OrderedBy Prod.fst highMaximum := by
  apply (OrderedTree.orderedBy_iff_map Prod.fst highMaximum).mpr
  apply OrderedTree.ordered_of_inorder_pairwise
  change [maxLeft, maxRoot, maxRight].Pairwise (· < ·)
  decide

theorem highMaximum_inorder :
    Trees.inorder (Trees.Cached.erase highMaximum) = [maxLeft, maxRoot, maxRight] := rfl

theorem highMaximum_bound (key : IntervalKey Nat)
    (member : key ∈ Trees.setTree (Trees.Cached.erase highMaximum)) : key.high ≤ 20 :=
  IntervalTree.high_le_maxHi id highMaximum_valid member

theorem highMaximum_attains :
    ∃ key ∈ Trees.setTree (Trees.Cached.erase highMaximum), key.high = 20 :=
  IntervalTree.maxHi_attained id highMaximum_valid (by intro h; cases h)

theorem highMaximum_left_witness :
    maxLeft ∈ Trees.setTree (Trees.Cached.erase highMaximum) ∧ maxLeft.high = 20 := by
  constructor
  · apply (Trees.mem_inorder_iff_mem_setTree maxLeft _).mp
    change maxLeft ∈ [maxLeft, maxRoot, maxRight]
    exact List.mem_cons_self
  · rfl

theorem highMaximum_greatest_key_smaller_high :
    maxLeft < maxRight ∧ maxRoot < maxRight ∧ maxRight.high < IntervalTree.maxHi highMaximum := by
  decide

/-! The high tie breaker distinguishes complete keys; caches do not select lookup paths. -/
def lowTwo : IntervalKey Nat := IntervalKey.ofBounds 1 2 (by decide)
def lowFive : IntervalKey Nat := IntervalKey.ofBounds 1 5 (by decide)
def lowEight : IntervalKey Nat := IntervalKey.ofBounds 1 8 (by decide)
def lowFour : IntervalKey Nat := IntervalKey.ofBounds 1 4 (by decide)

def equalLows : BinaryTree (IntervalKey Nat × Nat) :=
  .node (lowFive, 8) (.node (lowTwo, 2) .nil .nil) (.node (lowEight, 8) .nil .nil)

def corruptedEqualLows : BinaryTree (IntervalKey Nat × Nat) :=
  .node (lowFive, 99) (.node (lowTwo, 99) .nil .nil) (.node (lowEight, 99) .nil .nil)

theorem equalLows_ordered : OrderedTree.OrderedBy Prod.fst equalLows := by
  apply (OrderedTree.orderedBy_iff_map Prod.fst equalLows).mpr
  apply OrderedTree.ordered_of_inorder_pairwise
  change [lowTwo, lowFive, lowEight].Pairwise (· < ·)
  decide

theorem equalLows_valid : IntervalTree.CacheValid id equalLows := by
  change IntervalTree.CacheValid id (IntervalTree.node id
    (IntervalTree.node id .nil lowTwo .nil) lowFive (IntervalTree.node id .nil lowEight .nil))
  exact IntervalTree.node_cacheValid id
    (IntervalTree.node_cacheValid id (IntervalTree.cacheValid_nil id) lowTwo
      (IntervalTree.cacheValid_nil id)) lowFive
    (IntervalTree.node_cacheValid id (IntervalTree.cacheValid_nil id) lowEight
      (IntervalTree.cacheValid_nil id))

theorem equalLows_membership (query : IntervalKey Nat) :
    OrderedMap.containsKey query equalLows = true ↔ query ∈ [lowTwo, lowFive, lowEight] :=
  OrderedMap.containsKey_eq_true_iff_mem_inorder equalLows_ordered query

theorem corruptedEqualLows_invalid : ¬IntervalTree.CacheValid id corruptedEqualLows := by
  intro h
  exact (by decide : (99 : Nat) ≠ 2) h.1.2.2

theorem equalLows_corruption_preserves_membership (query : IntervalKey Nat) :
    OrderedMap.containsKey query equalLows = OrderedMap.containsKey query corruptedEqualLows :=
  OrderedMap.containsKey_congr_erase (left := equalLows) (right := corruptedEqualLows) rfl query

theorem overlapping_key_can_be_absent :
    OrderedMap.containsKey lowFour equalLows = false ∧ IntervalKey.Overlap lowFour lowFive := by
  constructor
  · rfl
  · decide

private theorem nat_leaf_valid (key : IntervalKey Nat) :
    IntervalTree.CacheValid id (.node (key, key.high) .nil .nil) := by
  have valid := IntervalTree.node_cacheValid id (IntervalTree.cacheValid_nil id) key
    (IntervalTree.cacheValid_nil id)
  rw [IntervalTree.node_eq, IntervalTree.max3_eq] at valid
  simpa only [IntervalTree.maxHi_nil, Nat.bot_eq_zero, Nat.max_zero, id_eq] using valid

/-! Neither the maximum bound nor its witness needs a BST. Directed lookup does. -/
def onePoint : IntervalKey Nat := IntervalKey.ofBounds 1 1 (by decide)
def twoPoint : IntervalKey Nat := IntervalKey.ofBounds 2 2 (by decide)

def unordered : BinaryTree (IntervalKey Nat × Nat) :=
  .node (onePoint, 2) (.node (twoPoint, 2) .nil .nil) (.node (zeroPoint, 0) .nil .nil)

theorem unordered_valid : IntervalTree.CacheValid id unordered := by
  change IntervalTree.CacheValid id (IntervalTree.node id
    (.node (twoPoint, twoPoint.high) .nil .nil) onePoint
    (.node (zeroPoint, zeroPoint.high) .nil .nil))
  exact IntervalTree.node_cacheValid id (nat_leaf_valid twoPoint) onePoint
    (nat_leaf_valid zeroPoint)

theorem unordered_not_ordered : ¬OrderedTree.OrderedBy Prod.fst unordered := by
  rw [OrderedTree.orderedBy_iff_map, OrderedTree.ordered_iff_inorder_pairwise]
  change ¬[twoPoint, onePoint, zeroPoint].Pairwise (· < ·)
  decide

theorem unordered_bound (key : IntervalKey Nat)
    (member : key ∈ Trees.setTree (Trees.Cached.erase unordered)) : key.high ≤ 2 :=
  IntervalTree.high_le_maxHi id unordered_valid member

theorem unordered_attains :
    ∃ key ∈ Trees.setTree (Trees.Cached.erase unordered), key.high = 2 :=
  IntervalTree.maxHi_attained id unordered_valid (by intro h; cases h)

theorem unordered_lookup_misses_stored_key :
    OrderedMap.containsKey zeroPoint unordered = false ∧
      zeroPoint ∈ Trees.setTree (Trees.Cached.erase unordered) := by
  constructor
  · rfl
  · apply (Trees.mem_inorder_iff_mem_setTree zeroPoint _).mp
    change zeroPoint ∈ [twoPoint, onePoint, zeroPoint]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)

theorem unordered_raw_path (query : IntervalKey Nat) :
    OrderedMap.containsKey query unordered =
      OrderedTree.member query (Trees.Cached.erase unordered) :=
  OrderedMap.containsKey_eq_member_erase query unordered

/-! Independent calculations exercise each argument of max3 and a three-way tie. -/
def rootThree : IntervalKey Nat := IntervalKey.ofBounds 2 3 (by decide)
def leftNine : IntervalKey Nat := IntervalKey.ofBounds 0 9 (by decide)
def rightEight : IntervalKey Nat := IntervalKey.ofBounds 5 8 (by decide)
def rootTen : IntervalKey Nat := IntervalKey.ofBounds 2 10 (by decide)
def leftFour : IntervalKey Nat := IntervalKey.ofBounds 0 4 (by decide)
def rightSeven : IntervalKey Nat := IntervalKey.ofBounds 5 7 (by decide)
def rootEight : IntervalKey Nat := IntervalKey.ofBounds 2 8 (by decide)
def leftEight : IntervalKey Nat := IntervalKey.ofBounds 0 8 (by decide)

theorem max3_branch_calculations :
    IntervalTree.max3 id rootThree .nil .nil = 3 ∧
    IntervalTree.max3 id rootThree (.node (leftNine, 9) .nil .nil) .nil = 9 ∧
    IntervalTree.max3 id rootThree .nil (.node (rightEight, 8) .nil .nil) = 8 ∧
    IntervalTree.max3 id rootTen (.node (leftFour, 4) .nil .nil)
      (.node (rightSeven, 7) .nil .nil) = 10 ∧
    IntervalTree.max3 id rootEight (.node (leftEight, 8) .nil .nil)
      (.node (rightEight, 8) .nil .nil) = 8 :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

def tiedMaximum : BinaryTree (IntervalKey Nat × Nat) :=
  IntervalTree.node id (.node (leftEight, 8) .nil .nil) rootEight
    (.node (rightEight, 8) .nil .nil)

theorem tiedMaximum_valid : IntervalTree.CacheValid id tiedMaximum :=
  IntervalTree.node_cacheValid id (nat_leaf_valid leftEight) rootEight (nat_leaf_valid rightEight)

theorem tiedMaximum_attains :
    ∃ key ∈ Trees.setTree (Trees.Cached.erase tiedMaximum), key.high = 8 :=
  IntervalTree.maxHi_attained id tiedMaximum_valid (by intro h; cases h)

theorem tiedMaximum_witness_not_unique :
    leftEight ≠ rightEight ∧
    leftEight ∈ Trees.setTree (Trees.Cached.erase tiedMaximum) ∧
    rightEight ∈ Trees.setTree (Trees.Cached.erase tiedMaximum) ∧
    leftEight.high = IntervalTree.maxHi tiedMaximum ∧
    rightEight.high = IntervalTree.maxHi tiedMaximum := by
  refine ⟨by decide, ?_, ?_, rfl, rfl⟩
  · apply (Trees.mem_inorder_iff_mem_setTree leftEight _).mp
    change leftEight ∈ [leftEight, rootEight, rightEight]
    exact List.mem_cons_self
  · apply (Trees.mem_inorder_iff_mem_setTree rightEight _).mp
    change rightEight ∈ [leftEight, rootEight, rightEight]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)

/-! Negative finite endpoints use the actual added bottom, never integer zero. -/
def negativeLeft : IntervalKey (WithBot Int) :=
  IntervalKey.ofBounds ((-8 : Int) : WithBot Int) ((-6 : Int) : WithBot Int) (by decide)
def negativeRoot : IntervalKey (WithBot Int) :=
  IntervalKey.ofBounds ((-5 : Int) : WithBot Int) ((-4 : Int) : WithBot Int) (by decide)
def negativeRight : IntervalKey (WithBot Int) :=
  IntervalKey.ofBounds ((-3 : Int) : WithBot Int) ((-1 : Int) : WithBot Int) (by decide)

def negativeMaximum : BinaryTree (IntervalKey (WithBot Int) × WithBot Int) :=
  .node (negativeRoot, ((-1 : Int) : WithBot Int))
    (.node (negativeLeft, ((-6 : Int) : WithBot Int)) .nil .nil)
    (.node (negativeRight, ((-1 : Int) : WithBot Int)) .nil .nil)

theorem negativeMaximum_valid : IntervalTree.CacheValid id negativeMaximum := by
  change IntervalTree.CacheValid id (IntervalTree.node id
    (IntervalTree.node id .nil negativeLeft .nil) negativeRoot
    (IntervalTree.node id .nil negativeRight .nil))
  exact IntervalTree.node_cacheValid id
    (IntervalTree.node_cacheValid id (IntervalTree.cacheValid_nil id) negativeLeft
      (IntervalTree.cacheValid_nil id)) negativeRoot
    (IntervalTree.node_cacheValid id (IntervalTree.cacheValid_nil id) negativeRight
      (IntervalTree.cacheValid_nil id))

theorem negativeMaximum_ordered : OrderedTree.OrderedBy Prod.fst negativeMaximum := by
  apply (OrderedTree.orderedBy_iff_map Prod.fst negativeMaximum).mpr
  apply OrderedTree.ordered_of_inorder_pairwise
  change [negativeLeft, negativeRoot, negativeRight].Pairwise (· < ·)
  decide

theorem negativeMaximum_bound (key : IntervalKey (WithBot Int))
    (member : key ∈ Trees.setTree (Trees.Cached.erase negativeMaximum)) :
    key.high ≤ ((-1 : Int) : WithBot Int) :=
  IntervalTree.high_le_maxHi id negativeMaximum_valid member

theorem negativeMaximum_attains :
    ∃ key ∈ Trees.setTree (Trees.Cached.erase negativeMaximum),
      key.high = ((-1 : Int) : WithBot Int) :=
  IntervalTree.maxHi_attained id negativeMaximum_valid (by intro h; cases h)

theorem negative_singleton_max3 :
    IntervalTree.max3 id negativeLeft .nil .nil = ((-6 : Int) : WithBot Int) := rfl

theorem numeric_zero_is_not_bottom :
    IntervalTree.maxHi (.nil : BinaryTree (IntervalKey (WithBot Int) × WithBot Int)) ≠
      ((0 : Int) : WithBot Int) := WithBot.bot_ne_coe

theorem numeric_zero_gives_unattained_answer :
    max negativeLeft.high (max ((0 : Int) : WithBot Int) ((0 : Int) : WithBot Int)) =
      ((0 : Int) : WithBot Int) ∧ negativeLeft.high ≠ ((0 : Int) : WithBot Int) := by
  decide

/-! All subtree readers can be upper bounds while the root value is unattained. -/
def boundOnlyLeft : BinaryTree (IntervalKey Nat × Nat) :=
  .node (zeroPoint, 100) .nil .nil

def boundOnly : BinaryTree (IntervalKey Nat × Nat) :=
  .node (onePoint, 100) boundOnlyLeft (.node (twoPoint, 2) .nil .nil)

theorem boundOnly_ordered : OrderedTree.OrderedBy Prod.fst boundOnly := by
  apply (OrderedTree.orderedBy_iff_map Prod.fst boundOnly).mpr
  apply OrderedTree.ordered_of_inorder_pairwise
  change [zeroPoint, onePoint, twoPoint].Pairwise (· < ·)
  decide

theorem boundOnly_raw_reader : IntervalTree.maxHi boundOnly = 100 := rfl

theorem boundOnly_root_equation :
    IntervalTree.maxHi boundOnly =
      IntervalTree.max3 id onePoint boundOnlyLeft (.node (twoPoint, 2) .nil .nil) := rfl

theorem boundOnly_every_subtree_bounds :
    ∀ subtree ∈ Trees.subtrees boundOnly,
      ∀ key ∈ Trees.setTree (Trees.Cached.erase subtree), key.high ≤ IntervalTree.maxHi subtree := by
  simp [boundOnly, boundOnlyLeft, Trees.subtrees_node, zeroPoint, onePoint, twoPoint,
    IntervalKey.high, IntervalKey.ofBounds]

theorem boundOnly_no_attainment :
    ¬∃ key ∈ Trees.setTree (Trees.Cached.erase boundOnly),
      key.high = IntervalTree.maxHi boundOnly := by
  simp [boundOnly, boundOnlyLeft, zeroPoint, onePoint, twoPoint,
    IntervalKey.high, IntervalKey.ofBounds]

theorem boundOnly_invalid : ¬IntervalTree.CacheValid id boundOnly := by
  intro valid
  exact (by decide : (100 : Nat) ≠ 0) valid.1.2.2

theorem boundOnly_smart_preserves_bad_child :
    IntervalTree.node id boundOnlyLeft onePoint (.node (twoPoint, 2) .nil .nil) = boundOnly := by
  rw [IntervalTree.node_eq]
  rfl

/-! Conversely, every nonempty subtree can attain its reader without bounding its highs. -/
def shortZero : IntervalKey Nat := IntervalKey.ofBounds 0 2 (by decide)
def tallZero : IntervalKey Nat := IntervalKey.ofBounds 0 5 (by decide)
def fourPoint : IntervalKey Nat := IntervalKey.ofBounds 4 4 (by decide)

def attainedLeft : BinaryTree (IntervalKey Nat × Nat) :=
  .node (tallZero, 2) (.node (shortZero, 2) .nil .nil) .nil

def attainmentOnly : BinaryTree (IntervalKey Nat × Nat) :=
  .node (onePoint, 4) attainedLeft (.node (fourPoint, 4) .nil .nil)

theorem attainmentOnly_ordered : OrderedTree.OrderedBy Prod.fst attainmentOnly := by
  apply (OrderedTree.orderedBy_iff_map Prod.fst attainmentOnly).mpr
  apply OrderedTree.ordered_of_inorder_pairwise
  change [shortZero, tallZero, onePoint, fourPoint].Pairwise (· < ·)
  decide

theorem attainmentOnly_every_nonempty_subtree_attains :
    ∀ subtree ∈ Trees.subtrees attainmentOnly, subtree ≠ .nil →
      ∃ key ∈ Trees.setTree (Trees.Cached.erase subtree),
        key.high = IntervalTree.maxHi subtree := by
  simp [attainmentOnly, attainedLeft, Trees.subtrees_node, shortZero, tallZero, onePoint,
    fourPoint, IntervalKey.high, IntervalKey.ofBounds]

theorem attainmentOnly_fails_bound :
    tallZero ∈ Trees.setTree (Trees.Cached.erase attainmentOnly) ∧
      ¬tallZero.high ≤ IntervalTree.maxHi attainmentOnly := by
  simp [attainmentOnly, attainedLeft, tallZero, IntervalKey.high, IntervalKey.ofBounds]

theorem attainmentOnly_root_equation :
    IntervalTree.maxHi attainmentOnly =
      IntervalTree.max3 id onePoint attainedLeft (.node (fourPoint, 4) .nil .nil) := rfl

theorem attainmentOnly_invalid : ¬IntervalTree.CacheValid id attainmentOnly := by
  intro valid
  exact (by decide : (2 : Nat) ≠ 5) valid.1.2.2

/-! A correct global maximum and a correct root equation still do not repair descendants. -/
def farHigh : IntervalKey Nat := IntervalKey.ofBounds 2 100 (by decide)
def correctRootLeft : BinaryTree (IntervalKey Nat × Nat) := .node (zeroPoint, 50) .nil .nil

def correctRoot : BinaryTree (IntervalKey Nat × Nat) :=
  .node (onePoint, 100) correctRootLeft (.node (farHigh, 100) .nil .nil)

theorem correctRoot_ordered : OrderedTree.OrderedBy Prod.fst correctRoot := by
  apply (OrderedTree.orderedBy_iff_map Prod.fst correctRoot).mpr
  apply OrderedTree.ordered_of_inorder_pairwise
  change [zeroPoint, onePoint, farHigh].Pairwise (· < ·)
  decide

theorem correctRoot_global_maximum :
    (∃ key ∈ Trees.setTree (Trees.Cached.erase correctRoot),
      key.high = IntervalTree.maxHi correctRoot) ∧
    ∀ key ∈ Trees.setTree (Trees.Cached.erase correctRoot),
      key.high ≤ IntervalTree.maxHi correctRoot := by
  simp [correctRoot, correctRootLeft, zeroPoint, onePoint, farHigh,
    IntervalKey.high, IntervalKey.ofBounds]

theorem correctRoot_equation :
    IntervalTree.maxHi correctRoot =
      IntervalTree.max3 id onePoint correctRootLeft (.node (farHigh, 100) .nil .nil) := rfl

theorem correctRoot_invalid : ¬IntervalTree.CacheValid id correctRoot := by
  intro valid
  exact (by decide : (50 : Nat) ≠ 0) valid.1.2.2

theorem correctRoot_smart_preserves_bad_child :
    IntervalTree.node id correctRootLeft onePoint (.node (farHigh, 100) .nil .nil) = correctRoot := by
  rw [IntervalTree.node_eq]
  rfl

/-! Local reconstruction repairs a bad leaf's root, with exactly the same erased contents. -/
def repairKey : IntervalKey Nat := IntervalKey.ofBounds 2 5 (by decide)
def malformedLeaf : BinaryTree (IntervalKey Nat × Nat) := .node (repairKey, 99) .nil .nil
def repairedLeaf : BinaryTree (IntervalKey Nat × Nat) := IntervalTree.node id .nil repairKey .nil

theorem malformedLeaf_invalid : ¬IntervalTree.CacheValid id malformedLeaf := by
  intro valid
  exact (by decide : (99 : Nat) ≠ 5) valid.2.2

theorem repairedLeaf_valid : IntervalTree.CacheValid id repairedLeaf :=
  IntervalTree.node_cacheValid id (IntervalTree.cacheValid_nil id) repairKey
    (IntervalTree.cacheValid_nil id)

theorem repairedLeaf_reader : IntervalTree.maxHi repairedLeaf = 5 :=
  IntervalTree.maxHi_node_smart id .nil repairKey .nil

theorem repairedLeaf_same_erasure :
    Trees.Cached.erase repairedLeaf = Trees.Cached.erase malformedLeaf :=
  IntervalTree.erase_node id .nil repairKey .nil

theorem highMaximum_smart_literal :
    IntervalTree.node id (.node (maxLeft, 20) .nil .nil) maxRoot
      (.node (maxRight, 10) .nil .nil) = highMaximum := by
  rw [IntervalTree.node_eq]
  rfl

theorem bad_child_blocks_smart_validity :
    ¬IntervalTree.CacheValid id
      (IntervalTree.node id boundOnlyLeft onePoint (.node (twoPoint, 2) .nil .nil)) := by
  rw [IntervalTree.node_cacheValid_iff]
  intro valid
  exact (by decide : (100 : Nat) ≠ 0) valid.1.2.2

/-! Distinct higher-universe complete keys can project to one interval. -/
abbrev IndexedKey := ULift.{1} ((IntervalKey Nat) ×ₗ Nat)

def indexedInterval (key : IndexedKey) : IntervalKey Nat := (ofLex key.down).1
def indexedZero : IndexedKey := ⟨toLex (rootEight, 0)⟩
def indexedOne : IndexedKey := ⟨toLex (rootEight, 1)⟩

def indexedTree : BinaryTree (IndexedKey × Nat) :=
  .node (indexedZero, 8) .nil (.node (indexedOne, 8) .nil .nil)

theorem indexed_keys_distinct : indexedZero ≠ indexedOne := by decide

theorem indexed_projection_not_injective : ¬Function.Injective indexedInterval := by
  intro injective
  exact indexed_keys_distinct (injective rfl)

theorem indexedTree_ordered : OrderedTree.OrderedBy Prod.fst indexedTree := by
  apply (OrderedTree.orderedBy_iff_map Prod.fst indexedTree).mpr
  apply OrderedTree.ordered_of_inorder_pairwise
  change [indexedZero, indexedOne].Pairwise (· < ·)
  decide

theorem indexedTree_valid : IntervalTree.CacheValid indexedInterval indexedTree := by
  change IntervalTree.CacheValid indexedInterval (IntervalTree.node indexedInterval .nil indexedZero
    (IntervalTree.node indexedInterval .nil indexedOne .nil))
  exact IntervalTree.node_cacheValid indexedInterval
    (IntervalTree.cacheValid_nil indexedInterval) indexedZero
    (IntervalTree.node_cacheValid indexedInterval (IntervalTree.cacheValid_nil indexedInterval)
      indexedOne (IntervalTree.cacheValid_nil indexedInterval))

theorem indexedTree_membership (query : IndexedKey) :
    OrderedMap.containsKey query indexedTree = true ↔ query ∈ [indexedZero, indexedOne] :=
  OrderedMap.containsKey_eq_true_iff_mem_inorder indexedTree_ordered query

theorem indexedTree_interval_occurrences :
    (Trees.inorder (Trees.Cached.erase indexedTree)).map indexedInterval = [rootEight, rootEight] :=
  rfl

theorem indexedTree_projected_inorder_not_strict :
    ¬((Trees.inorder (Trees.Cached.erase indexedTree)).map indexedInterval).Pairwise (· < ·) := by
  rw [indexedTree_interval_occurrences]
  simp

theorem indexedTree_high_occurrences :
    Trees.inorder (Trees.Cached.erase (IntervalTree.highTree indexedInterval indexedTree)) = [8, 8] :=
  (IntervalTree.inorder_erase_highTree indexedInterval indexedTree).trans rfl

theorem indexedTree_bound (key : IndexedKey)
    (member : key ∈ Trees.setTree (Trees.Cached.erase indexedTree)) :
    (indexedInterval key).high ≤ 8 :=
  IntervalTree.high_le_maxHi indexedInterval indexedTree_valid member

theorem indexedTree_attains :
    ∃ key ∈ Trees.setTree (Trees.Cached.erase indexedTree), (indexedInterval key).high = 8 :=
  IntervalTree.maxHi_attained indexedInterval indexedTree_valid (by intro h; cases h)

def eightPoint : IntervalKey Nat := IntervalKey.ofBounds 8 8 (by decide)
def ninePoint : IntervalKey Nat := IntervalKey.ofBounds 9 9 (by decide)

theorem indexed_image_touches :
    IntervalSet.HasOverlap (indexedInterval '' ({indexedZero, indexedOne} : Set IndexedKey))
      eightPoint := by
  apply (IntervalSet.hasOverlap_image_iff indexedInterval _ eightPoint).mpr
  exact ⟨indexedZero, by simp, by decide⟩

theorem indexed_image_has_gap :
    ¬IntervalSet.HasOverlap (indexedInterval '' ({indexedZero, indexedOne} : Set IndexedKey))
      ninePoint := by
  rw [IntervalSet.hasOverlap_image_iff]
  simp [indexedInterval, indexedZero, indexedOne, IntervalKey.Overlap, rootEight, ninePoint,
    IntervalKey.low, IntervalKey.high, IntervalKey.ofBounds]

theorem indexed_images_agree :
    indexedInterval '' ({indexedZero, indexedOne} : Set IndexedKey) =
      indexedInterval '' ({indexedOne} : Set IndexedKey) := by
  simp [indexedInterval, indexedZero, indexedOne]

theorem indexed_complete_membership_differs :
    indexedZero ∈ ({indexedZero, indexedOne} : Set IndexedKey) ∧
      indexedZero ∉ ({indexedOne} : Set IndexedKey) := by
  simp [indexed_keys_distinct]

/-- Endpoints can instead live in a larger universe than complete keys. -/
def liftedInterval (key : Fin 2) : IntervalKey (ULift.{1} Nat) :=
  if key = 0 then IntervalKey.ofBounds ⟨1⟩ ⟨4⟩ (by decide)
  else IntervalKey.ofBounds ⟨2⟩ ⟨4⟩ (by decide)

def liftedEndpoints : BinaryTree (Fin 2 × ULift.{1} Nat) :=
  .node (0, ⟨4⟩) .nil (.node (1, ⟨4⟩) .nil .nil)

theorem liftedEndpoints_valid : IntervalTree.CacheValid liftedInterval liftedEndpoints := by
  change IntervalTree.CacheValid liftedInterval (IntervalTree.node liftedInterval .nil 0
    (IntervalTree.node liftedInterval .nil 1 .nil))
  exact IntervalTree.node_cacheValid liftedInterval (IntervalTree.cacheValid_nil liftedInterval) 0
    (IntervalTree.node_cacheValid liftedInterval (IntervalTree.cacheValid_nil liftedInterval) 1
      (IntervalTree.cacheValid_nil liftedInterval))

theorem liftedEndpoints_inorder : Trees.inorder (Trees.Cached.erase liftedEndpoints) = [0, 1] := rfl

theorem liftedEndpoints_bound (key : Fin 2)
    (member : key ∈ Trees.setTree (Trees.Cached.erase liftedEndpoints)) :
    (liftedInterval key).high ≤ (⟨4⟩ : ULift.{1} Nat) :=
  IntervalTree.high_le_maxHi liftedInterval liftedEndpoints_valid member

theorem liftedEndpoints_attains :
    ∃ key ∈ Trees.setTree (Trees.Cached.erase liftedEndpoints),
      (liftedInterval key).high = (⟨4⟩ : ULift.{1} Nat) :=
  IntervalTree.maxHi_attained liftedInterval liftedEndpoints_valid (by intro h; cases h)

end Examples.IntervalTreeFoundations
