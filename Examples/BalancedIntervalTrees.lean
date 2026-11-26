import Applications.Search.RectangleSweep.Balanced
import Examples.IntervalTreeSearch
import Examples.RectangleSweep

/-!
# Connected balanced interval-tree cases

The independently fixed expectations in the balanced interval-tree preparation
paper include exact product caches, deletion ties, duplicate images, and weaker
query invariants. These clients connect those expectations to the public
balancing programs, full interval-set laws, and occurrence-sensitive sweep.
They make no measured running-time claim.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.BalancedIntervalTrees
open Trees Search Search.IntervalTree
open Examples.IntervalTreeFoundations
  (IndexedKey indexedInterval indexedZero indexedOne rootEight eightPoint ninePoint)
universe u v
variable {κ : Type u} {σ : Type v}

/- Finite fixture decisions stay local; the public contracts do not require
decidable annotation equality. -/
private def balancedDecidable (d : Nat) :
    (t : BinaryTree κ) → Decidable (HeightBalance.BalancedD d t)
  | .nil => isTrue trivial
  | .node _ l r => by
      letI := balancedDecidable d l
      letI := balancedDecidable d r
      exact inferInstanceAs (Decidable
        (HeightBalance.BalancedD d l ∧ HeightBalance.BalancedD d r ∧
          l.height ≤ r.height + d ∧ r.height ≤ l.height + d))

private def cachedDecidable [DecidableEq σ] (empty : σ) (combine : σ → κ → σ → σ) :
    (t : BinaryTree (κ × σ)) → Decidable (Cached.Valid empty combine t)
  | .nil => isTrue trivial
  | .node (a, s) l r => by
      letI := cachedDecidable empty combine l
      letI := cachedDecidable empty combine r
      exact inferInstanceAs (Decidable
        (Cached.Valid empty combine l ∧ Cached.Valid empty combine r ∧
          s = combine (Cached.read empty l) a (Cached.read empty r)))

local instance (d : Nat) (t : BinaryTree κ) :
    Decidable (HeightBalance.BalancedD d t) := balancedDecidable d t
local instance [DecidableEq σ] (ann : HeightBalance.HeightAnnotation κ σ)
    (t : BinaryTree (κ × σ)) : Decidable (HeightBalance.CacheValid ann t) :=
  cachedDecidable ann.empty ann.combine t
local instance [DecidableEq σ] (ann : HeightBalance.HeightAnnotation κ σ) (d : Nat)
    (t : BinaryTree (κ × σ)) : Decidable (HeightBalance.ValidD ann d t) :=
  inferInstanceAs (Decidable
    (HeightBalance.BalancedD d (Cached.erase t) ∧ HeightBalance.CacheValid ann t))
local instance [LT κ] [DecidableLT κ] [DecidableEq σ]
    (ann : HeightBalance.HeightAnnotation κ σ) (d : Nat) (t : BinaryTree (κ × σ)) :
    Decidable (HeightBalance.SetValid ann d t) :=
  inferInstanceAs (Decidable
    (HeightBalance.ValidD ann d t ∧ (inorder (Cached.erase t)).Pairwise (· < ·)))
local instance (iv : κ → IntervalKey Nat) (t : BinaryTree (κ × Nat)) :
    Decidable (IntervalTree.CacheValid iv t) :=
  cachedDecidable 0 (IntervalTree.combine iv) t

abbrev NKey := IntervalKey Nat
abbrev NTree := BinaryTree (NKey × (Nat × Nat))
def point (n : Nat) : NKey := IntervalKey.ofBounds n n le_rfl
def leaf (iv : κ → NKey) (a : κ) : BinaryTree (κ × (Nat × Nat)) :=
  .node (a, (1, (iv a).high)) .nil .nil
def natAnn : HeightBalance.HeightAnnotation NKey (Nat × Nat) := Balanced.annotation id

theorem nat_contract : IntervalSet.Laws (Balanced.deleteOps (id : NKey → NKey))
    (Balanced.search id) id (fun t => setTree (Cached.erase t)) (Balanced.Valid id) :=
  Balanced.intervalSetLaws id (fun _ _ h => IntervalKey.low_le_of_le h.le)

/-! R1–R4: both single and both double rotations rebuild complete annotations. -/
def rrA : NKey := point 1
def rrB : NKey := point 2
def rrC : NKey := IntervalKey.ofBounds 3 100 (by decide)
def rrRight : NTree := .node (rrB, (2, 100)) .nil (leaf id rrC)
def rrExpected : NTree := .node (rrB, (2, 100)) (leaf id rrA) (leaf id rrC)

theorem rr_rotation : HeightBalance.balR natAnn 1 .nil rrA rrRight = rrExpected :=
  HeightBalance.balR_single natAnn 1 .nil rrA .nil rrB (2, 100) (leaf id rrC)
    (by decide) (by decide)

def llA : NKey := IntervalKey.ofBounds 0 1 (by decide)
def llB : NKey := IntervalKey.ofBounds 2 3 (by decide)
def llC : NKey := IntervalKey.ofBounds 4 100 (by decide)
def llLeft : NTree := .node (llB, (2, 3)) (leaf id llA) .nil
def llExpected : NTree := .node (llB, (2, 100)) (leaf id llA) (leaf id llC)

theorem ll_rotation : HeightBalance.balL natAnn 1 llLeft llC .nil = llExpected :=
  HeightBalance.balL_single natAnn 1 (leaf id llA) llB (2, 3) .nil llC .nil
    (by decide) (by decide)

def lrA : NKey := IntervalKey.ofBounds 1 100 (by decide)
def lrB : NKey := point 2
def lrC : NKey := point 3
def lrLeft : NTree := .node (lrA, (2, 100)) .nil (leaf id lrB)
def lrExpected : NTree := .node (lrB, (2, 100)) (leaf id lrA) (leaf id lrC)

theorem lr_rotation : HeightBalance.balL natAnn 1 lrLeft lrC .nil = lrExpected :=
  HeightBalance.balL_double natAnn 1 .nil lrA (2, 100) .nil lrB (1, 2) .nil lrC .nil
    (by decide) (by decide)

def rlRight : NTree := .node (rrC, (2, 100)) (leaf id rrB) .nil

theorem rl_rotation : HeightBalance.balR natAnn 1 .nil rrA rlRight = rrExpected :=
  HeightBalance.balR_double natAnn 1 .nil rrA .nil rrB (1, 2) .nil rrC (2, 100) .nil
    (by decide) (by decide)

theorem rotation_results_valid :
    Balanced.Valid id rrExpected ∧ Balanced.Valid id llExpected ∧ Balanced.Valid id lrExpected := by
  decide

theorem insertion_reaches_rotations :
    HeightBalance.insert natAnn 1 rrC
        (HeightBalance.insert natAnn 1 rrB (HeightBalance.insert natAnn 1 rrA .nil)) = rrExpected ∧
      HeightBalance.insert natAnn 1 lrB
        (HeightBalance.insert natAnn 1 lrA (HeightBalance.insert natAnn 1 lrC .nil)) = lrExpected :=
  ⟨rfl, rfl⟩

theorem rr_maximum_contract :
    (∃ a ∈ setTree (Cached.erase rrExpected), a.high = 100) ∧
      ∀ a ∈ setTree (Cached.erase rrExpected), a.high ≤ 100 :=
  Balanced.maxHi_spec id (Balanced.cacheValid_maximumTree id rotation_results_valid.1.1.2)
    (by intro h; cases h)

theorem rr_query_hit : Balanced.search id rrExpected (point 3) = true := by
  apply (nat_contract.overlap rrExpected rotation_results_valid.1 (point 3)).mpr
  apply (IntervalSet.hasOverlap_image_iff id _ (point 3)).mpr
  exact ⟨rrC, by simp [rrExpected, leaf], by decide⟩

/-! D1/D2: deleting a leaf exposes the equality branch of the single rotation. -/
def deleteLeftInput : NTree :=
  .node (point 4, (3, 5))
    (.node (point 2, (2, 3)) (leaf id (point 1)) (leaf id (point 3))) (leaf id (point 5))
def deleteLeftExpected : NTree :=
  .node (point 2, (3, 4)) (leaf id (point 1))
    (.node (point 4, (2, 4)) (leaf id (point 3)) .nil)
def deleteRightInput : NTree :=
  .node (point 2, (3, 5)) (leaf id (point 1))
    (.node (point 4, (2, 5)) (leaf id (point 3)) (leaf id (point 5)))
def deleteRightExpected : NTree :=
  .node (point 4, (3, 5)) (.node (point 2, (2, 3)) .nil (leaf id (point 3)))
    (leaf id (point 5))

theorem deletion_tie_inputs_valid :
    Balanced.Valid id deleteLeftInput ∧ Balanced.Valid id deleteRightInput := by decide

theorem delete_left_tie : HeightBalance.delete natAnn 1 (point 5) deleteLeftInput =
    deleteLeftExpected := rfl
theorem delete_right_tie : HeightBalance.delete natAnn 1 (point 1) deleteRightInput =
    deleteRightExpected := rfl

theorem deletion_tie_results_valid :
    Balanced.Valid id deleteLeftExpected ∧ Balanced.Valid id deleteRightExpected := by
  constructor
  · have h := nat_contract.delete_valid (point 5) deleteLeftInput deletion_tie_inputs_valid.1
    change Balanced.Valid id (HeightBalance.delete natAnn 1 (point 5) deleteLeftInput) at h
    rwa [delete_left_tie] at h
  · have h := nat_contract.delete_valid (point 1) deleteRightInput deletion_tie_inputs_valid.2
    change Balanced.Valid id (HeightBalance.delete natAnn 1 (point 1) deleteRightInput) at h
    rwa [delete_right_tie] at h

/-! O1/O2: complete keys live in a higher universe than their shared interval. -/
theorem indexed_contract : IntervalSet.Laws (Balanced.deleteOps indexedInterval)
    (Balanced.search indexedInterval) indexedInterval
    (fun t => setTree (Cached.erase t)) (Balanced.Valid indexedInterval) :=
  Balanced.intervalSetLaws indexedInterval IntervalTreeSearch.indexed_compatible

def indexedPrefix (n : Nat) : BinaryTree (IndexedKey × (Nat × Nat)) :=
  AbstractSet.execute (Balanced.deleteOps indexedInterval)
    (IntervalTreeSearch.indexedWord.take n) .nil
def indexedFirst := leaf indexedInterval indexedZero
def indexedBoth : BinaryTree (IndexedKey × (Nat × Nat)) :=
  .node (indexedZero, (2, 8)) .nil (leaf indexedInterval indexedOne)
def indexedLast := leaf indexedInterval indexedOne

theorem indexed_prefix_valid (n : Nat) : Balanced.Valid indexedInterval (indexedPrefix n) :=
  indexed_contract.toDeleteLaws.prefix_valid IntervalTreeSearch.indexedWord n indexed_contract.empty_valid

theorem indexed_member_semantics (n : Nat) (key : IndexedKey) :
    OrderedMap.containsKey key (indexedPrefix n) = true ↔
      ((IntervalTreeSearch.indexedWord.take n).foldl AbstractSet.meaningStep (fun _ => False)) key :=
  indexed_contract.toDeleteLaws.member_execute
    (IntervalTreeSearch.indexedWord.take n) indexed_contract.empty_valid key

theorem indexed_overlap_semantics (n : Nat) (query : NKey) :
    Balanced.search indexedInterval (indexedPrefix n) query = true ↔
      IntervalSet.HasOverlap (indexedInterval ''
        ((IntervalTreeSearch.indexedWord.take n).foldl AbstractSet.meaningStep (fun _ => False))) query :=
  indexed_contract.search_execute (IntervalTreeSearch.indexedWord.take n) indexed_contract.empty_valid query

theorem indexed_prefix_shapes :
    (List.range 6).map indexedPrefix =
      [.nil, indexedFirst, indexedBoth, indexedBoth, indexedLast, .nil] := rfl

theorem indexed_prefix_readers :
    (List.range 6).map (fun n => Cached.read (0, 0) (indexedPrefix n)) =
      [(0, 0), (1, 8), (2, 8), (2, 8), (1, 8), (0, 0)] := rfl

theorem indexed_overlap_vectors :
    [eightPoint, ninePoint].map (fun query =>
      (List.range 6).map (fun n => Balanced.search indexedInterval (indexedPrefix n) query)) =
      [[false, true, true, true, true, false], [false, false, false, false, false, false]] := rfl

theorem indexed_delete_preserves_other_occurrence :
    OrderedMap.containsKey indexedZero (indexedPrefix 4) = false ∧
      OrderedMap.containsKey indexedOne (indexedPrefix 4) = true ∧
      Balanced.search indexedInterval (indexedPrefix 4) eightPoint = true := by
  refine ⟨rfl, rfl, ?_⟩
  apply (indexed_contract.overlap _ (indexed_prefix_valid 4) eightPoint).mpr
  apply (IntervalSet.hasOverlap_image_iff indexedInterval _ eightPoint).mpr
  exact ⟨indexedOne, by change indexedOne ∈ setTree (Cached.erase indexedLast); simp [indexedLast, leaf],
    by decide⟩

def indexedTwo : IndexedKey := ⟨toLex (rootEight, 2)⟩
def indexedTriple : BinaryTree (IndexedKey × (Nat × Nat)) :=
  .node (indexedOne, (2, 8)) (leaf indexedInterval indexedZero) (leaf indexedInterval indexedTwo)
def indexedAfterRootDelete : BinaryTree (IndexedKey × (Nat × Nat)) :=
  .node (indexedZero, (2, 8)) .nil (leaf indexedInterval indexedTwo)

theorem indexed_rotation_and_predecessor :
    (Balanced.deleteOps indexedInterval).insert indexedTwo indexedBoth = indexedTriple ∧
      HeightBalance.splitMaxOption (Balanced.annotation indexedInterval) 1
        (leaf indexedInterval indexedZero) = some (.nil, indexedZero) ∧
      (Balanced.deleteOps indexedInterval).delete indexedOne indexedTriple = indexedAfterRootDelete :=
  ⟨rfl, rfl, rfl⟩

theorem indexed_rotated_valid : Balanced.Valid indexedInterval indexedTriple ∧
    Balanced.Valid indexedInterval indexedAfterRootDelete := by
  have pairValid : Balanced.Valid indexedInterval indexedBoth := indexed_prefix_valid 2
  have tripleValid := indexed_contract.insert_valid indexedTwo indexedBoth pairValid
  rw [indexed_rotation_and_predecessor.1] at tripleValid
  refine ⟨tripleValid, ?_⟩
  have result := indexed_contract.delete_valid indexedOne indexedTriple tripleValid
  rwa [indexed_rotation_and_predecessor.2.2] at result

/-! M1/M2 and B1: raw updates preserve equal malformed nodes; bottom is not emptiness. -/
def malformed : NTree := .node (rootEight, (99, 77)) .nil .nil

theorem malformed_equal_insert :
    HeightBalance.insert natAnn 1 rootEight malformed = malformed :=
  HeightBalance.insert_of_not_lt_of_not_lt natAnn 1 rootEight rootEight (99, 77) .nil .nil
    (by decide) (by decide)

theorem malformed_boundary : ¬Balanced.Valid id malformed ∧
    Balanced.search id malformed eightPoint = true ∧ Balanced.search id malformed ninePoint = false := by
  decide

theorem malformed_search_sound :
    ∃ a ∈ setTree (Cached.erase malformed), IntervalKey.Overlap a eightPoint :=
  Balanced.search_sound id malformed_boundary.2.1

def staleLeft : NTree := .node (rrA, (1, 100)) .nil .nil
def staleRotated : NTree := .node (rrB, (2, 100)) staleLeft (leaf id rrC)

theorem smart_node_does_not_repair_child :
    HeightBalance.node natAnn staleLeft rrB (leaf id rrC) = staleRotated := rfl

theorem stale_cache_boundary : HeightBalance.BalancedD 1 (Cached.erase staleRotated) ∧
    (inorder (Cached.erase staleRotated)).Pairwise (· < ·) ∧
    Balanced.maxHi staleRotated = 100 ∧
    ¬IntervalTree.CacheValid id (Balanced.maximumTree staleRotated) := by decide

theorem stale_false_negative : Balanced.search id staleRotated (point 3) = false ∧
    ∃ a ∈ setTree (Cached.erase staleRotated), IntervalKey.Overlap a (point 3) :=
  ⟨rfl, rrC, by simp [staleRotated, leaf], by decide⟩

theorem bottom_is_not_empty :
    Balanced.maxHi (.nil : NTree) = Balanced.maxHi (leaf id (point 0)) ∧
      Balanced.Valid id (.nil : NTree) ∧ Balanced.Valid id (leaf id (point 0)) ∧
      Balanced.search id (.nil : NTree) (point 0) = false ∧
      Balanced.search id (leaf id (point 0)) (point 0) = true ∧
      Balanced.search id (leaf id (point 0)) (point 1) = false := by decide

def emptyLeftGuard : NTree := .node (point 1, (2, 1)) .nil (leaf id (point 0))

theorem empty_left_guard : Balanced.search id emptyLeftGuard (point 0) = true ∧
    Balanced.search id emptyLeftGuard (point 0) =
      IntervalTree.search id (Balanced.maximumTree emptyLeftGuard) (point 0) :=
  ⟨rfl, Balanced.search_eq id emptyLeftGuard (point 0)⟩

/-! W1–W3: a query needs neither height validity, balance, nor strict key order. -/
def wrongHeight : NTree := .node (rootEight, (99, 8)) .nil .nil
def unbalanced : NTree :=
  .node (point 1, (3, 3)) .nil (.node (point 2, (2, 3)) .nil (leaf id (point 3)))
def repeatedKey : NTree := .node (rootEight, (2, 8)) (leaf id rootEight) .nil
abbrev LowOrdered (t : NTree) : Prop :=
  (inorder (Cached.erase t)).Pairwise (fun a b => a.low ≤ b.low)

theorem weak_maximum_validity :
    IntervalTree.CacheValid id (Balanced.maximumTree wrongHeight) ∧
      IntervalTree.CacheValid id (Balanced.maximumTree unbalanced) ∧
      IntervalTree.CacheValid id (Balanced.maximumTree repeatedKey) := by decide

theorem weak_low_order : LowOrdered wrongHeight ∧ LowOrdered unbalanced ∧ LowOrdered repeatedKey := by
  decide

theorem weak_examples_not_full_valid :
    ¬Balanced.Valid id wrongHeight ∧ ¬Balanced.Valid id unbalanced ∧ ¬Balanced.Valid id repeatedKey := by
  decide

theorem weak_query_contracts (query : NKey) :
    (Balanced.search id wrongHeight query = true ↔
      ∃ a ∈ setTree (Cached.erase wrongHeight), IntervalKey.Overlap a query) ∧
    (Balanced.search id unbalanced query = true ↔
      ∃ a ∈ setTree (Cached.erase unbalanced), IntervalKey.Overlap a query) ∧
    (Balanced.search id repeatedKey query = true ↔
      ∃ a ∈ setTree (Cached.erase repeatedKey), IntervalKey.Overlap a query) :=
  ⟨Balanced.search_correct id weak_maximum_validity.1 weak_low_order.1 query,
    Balanced.search_correct id weak_maximum_validity.2.1 weak_low_order.2.1 query,
    Balanced.search_correct id weak_maximum_validity.2.2 weak_low_order.2.2 query⟩

theorem weak_expected_queries :
    [eightPoint, ninePoint].map (Balanced.search id wrongHeight) = [true, false] ∧
      [point 3, point 4].map (Balanced.search id unbalanced) = [true, false] ∧
      [eightPoint, ninePoint].map (Balanced.search id repeatedKey) = [true, false] := ⟨rfl, rfl, rfl⟩

/-! W4 reuses the existing reverse 10/5/0 projection; full AVL validity is insufficient. -/
def reverseProduct : BinaryTree (Fin 3 × (Nat × Nat)) :=
  .node (1, (2, 10)) (.node (0, (1, 10)) .nil .nil) (.node (2, (1, 0)) .nil .nil)

theorem reverse_product_valid : Balanced.Valid IntervalTreeSearch.reversedInterval reverseProduct := by
  decide

theorem reverse_projection :
    Balanced.maximumTree reverseProduct = IntervalTreeSearch.reversedTree := rfl

theorem reverse_false_negative :
    Balanced.search IntervalTreeSearch.reversedInterval reverseProduct (point 0) = false ∧
      IntervalSet.HasOverlap (IntervalTreeSearch.reversedInterval ''
        setTree (Cached.erase reverseProduct)) (point 0) := by
  constructor
  · rw [Balanced.search_eq, reverse_projection]
    exact IntervalTreeSearch.reversed_false_negative.1
  · exact IntervalTreeSearch.reversed_false_negative.2

/-! W5: an underestimated maximum can prune a real witness in an ordered tree. -/
def underestimatedKey : NKey := IntervalKey.ofBounds 1 5 (by decide)
def underestimated : NTree :=
  .node (point 10, (2, 10)) (.node (underestimatedKey, (1, 0)) .nil .nil) .nil

theorem underestimated_false_negative :
    LowOrdered underestimated ∧ HeightBalance.BalancedD 1 (Cached.erase underestimated) ∧
      ¬IntervalTree.CacheValid id (Balanced.maximumTree underestimated) ∧
      Balanced.search id underestimated (point 3) = false ∧
      ∃ a ∈ setTree (Cached.erase underestimated), IntervalKey.Overlap a (point 3) := by
  refine ⟨by decide, by decide, by decide, rfl, underestimatedKey, ?_, by decide⟩
  simp [underestimated]

/-! S1–S5: the concrete consumer uses distinct occurrence keys and closed boundaries. -/
theorem balanced_empty_misses :
    RectangleSweep.balancedSweep ([] : List (Rectangle Nat Int)) = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  exact Rectangle.not_hasIntersection_nil
    ((RectangleSweep.balancedSweep_eq_true_iff_hasIntersection _).mp h)

theorem balanced_singleton_misses :
    RectangleSweep.balancedSweep [Examples.RectangleSweep.natSquare] = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  exact Rectangle.not_hasIntersection_singleton _
    ((RectangleSweep.balancedSweep_eq_true_iff_hasIntersection _).mp h)

theorem balanced_duplicate_hit :
    RectangleSweep.balancedSweep
      [Examples.RectangleSweep.natSquare, Examples.RectangleSweep.natSquare] = true :=
  (RectangleSweep.balancedSweep_eq_true_iff_hasIntersection _).mpr
    ((Rectangle.hasIntersection_pair_iff _ _).mpr (Rectangle.intersects_self _))

theorem balanced_boundary_hit :
    RectangleSweep.balancedSweep
      [Examples.RectangleSweep.natSquare, Examples.RectangleSweep.natEdge] = true :=
  (RectangleSweep.balancedSweep_eq_true_iff_hasIntersection _).mpr
    ((Rectangle.hasIntersection_pair_iff _ _).mpr
      ⟨(0, 1), Examples.RectangleSweep.nat_edge_common_point⟩)

def xGap : Rectangle Nat Int :=
  ⟨IntervalKey.ofBounds 2 3 (by decide), IntervalKey.ofBounds 0 1 (by decide)⟩
def yGap : Rectangle Nat Int :=
  ⟨IntervalKey.ofBounds 0 1 (by decide), IntervalKey.ofBounds 2 3 (by decide)⟩

theorem balanced_x_gap :
    RectangleSweep.balancedSweep [Examples.RectangleSweep.natSquare, xGap] = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  have hit := (Rectangle.hasIntersection_pair_iff _ _).mp
    ((RectangleSweep.balancedSweep_eq_true_iff_hasIntersection _).mp h)
  exact (by unfold Rectangle.Overlap IntervalKey.Overlap; decide :
      ¬Rectangle.Overlap Examples.RectangleSweep.natSquare xGap)
    ((Rectangle.overlap_iff_intersects _ _).mpr hit)

theorem balanced_y_gap :
    RectangleSweep.balancedSweep [Examples.RectangleSweep.natSquare, yGap] = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  have hit := (Rectangle.hasIntersection_pair_iff _ _).mp
    ((RectangleSweep.balancedSweep_eq_true_iff_hasIntersection _).mp h)
  exact (by unfold Rectangle.Overlap IntervalKey.Overlap; decide :
      ¬Rectangle.Overlap Examples.RectangleSweep.natSquare yGap)
    ((Rectangle.overlap_iff_intersects _ _).mpr hit)

def sweepKey0 : RectangleSweep.Key Nat := toLex (Examples.RectangleSweep.natSquare.x, 0)
def sweepKey1 : RectangleSweep.Key Nat := toLex (Examples.RectangleSweep.natSquare.x, 1)
def activePair : BinaryTree (RectangleSweep.Key Nat × (Nat × Nat)) :=
  .node (sweepKey0, (2, 1)) .nil (leaf RectangleSweep.keyInterval sweepKey1)

/-- These are full update-prefix states; a successful scan stops before its second insert. -/
theorem sweep_occurrence_updates :
    (Balanced.deleteOps RectangleSweep.keyInterval).insert sweepKey1
        ((Balanced.deleteOps RectangleSweep.keyInterval).insert sweepKey0 .nil) = activePair ∧
      (Balanced.deleteOps RectangleSweep.keyInterval).delete sweepKey0 activePair =
        leaf RectangleSweep.keyInterval sweepKey1 := ⟨rfl, rfl⟩

theorem sweep_surviving_occurrence :
    Balanced.Valid RectangleSweep.keyInterval activePair ∧
      OrderedMap.containsKey sweepKey0 (leaf RectangleSweep.keyInterval sweepKey1) = false ∧
      OrderedMap.containsKey sweepKey1 (leaf RectangleSweep.keyInterval sweepKey1) = true ∧
      Balanced.search RectangleSweep.keyInterval (leaf RectangleSweep.keyInterval sweepKey1) (point 1) = true := by
  refine ⟨by decide, rfl, rfl, ?_⟩
  apply ((Balanced.intervalSetLaws RectangleSweep.keyInterval
    RectangleSweep.keyInterval_low_le_of_lt).overlap _ (by decide) (point 1)).mpr
  apply (IntervalSet.hasOverlap_image_iff RectangleSweep.keyInterval _ (point 1)).mpr
  exact ⟨sweepKey1, by simp [leaf], by decide⟩

end Examples.BalancedIntervalTrees
