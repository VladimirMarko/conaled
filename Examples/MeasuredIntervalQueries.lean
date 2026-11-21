import Applications.Resources.IntervalTree
import Examples.BalancedIntervalTrees

/-!
# Connected measured interval-query cases

The fixed literal paths and tariffs precede the measured implementation; their
correspondence is retained in `docs/research/fdsa-measured-rectangle-scan.md`.
These clients distinguish actual projection/Boolean results, reached comparison
work, empty-left bypass and the absence of sibling retry. Soundness, weak-low-order
completeness and strict-key adapters retain the existing pure hypotheses.
Stored height and balance are not query premises. Costs are declared source
observations, with no bit-complexity, allocation or host-runtime claim.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.MeasuredIntervalQueries
open Trees Resources Resources.IntervalTree Search Search.IntervalTree
open Examples.BalancedIntervalTrees
open Examples.IntervalTreeFoundations
  (IndexedKey indexedInterval rootEight eightPoint ninePoint)
universe u v
variable {α : Type u} {κ : Type v}

/-- A constant observation on the actual returned interval projection. -/
def projectAt [LE α] (iv : κ → IntervalKey α) (p : Nat) (key : κ) :
    Measured (IntervalKey α) Nat := (iv key, p)

/-- Endpoint comparison is independent of the complete-key update comparator. -/
def compareAt [LE α] [DecidableLE α] (e : Nat) (x y : α) : Measured Bool Nat :=
  (decide (x ≤ y), e)

abbrev unitLE := compareAt (α := Nat) 1
abbrev unitQuery := searchRun (projectAt (id : NKey → NKey) 0) unitLE

/-! The helper has no entry charge, and the second test is conditional. -/
theorem overlap_selected_branches :
    overlapRun unitLE (point 0) (point 1) = (false, 1) ∧
      overlapRun unitLE (point 1) (point 1) = (true, 2) ∧
      overlapRun unitLE (point 2) (point 1) = (false, 2) :=
  ⟨overlapRun_of_first_false unitLE (point 0) (point 1) rfl,
    overlapRun_of_first_true unitLE (point 1) (point 1) rfl,
    overlapRun_of_first_true unitLE (point 2) (point 1) rfl⟩

theorem overlap_value_and_bound (query stored : NKey) :
    (overlapRun unitLE query stored).1 = decide (IntervalKey.overlap query stored) ∧
      (overlapRun unitLE query stored).2 ≤ 2 :=
  ⟨overlapRun_value unitLE query stored (fun _ _ => rfl),
    overlapRun_cost_le unitLE query stored 1 (fun _ _ => Nat.le_refl 1)⟩

/-- The actual first callback observation survives; no second-call tariff is added. -/
theorem overlap_first_false_keeps_observation (c : Nat) :
    (overlapRun (fun x y : Nat => (decide (x ≤ y), c + x + y))
      (point 0) (point 1)).2 = c + 1 :=
  overlapRun_cost (fun x y : Nat => (decide (x ≤ y), c + x + y))
    (point 0) (point 1)

/-- A single root read returns the stored maximum and ignores stored height. -/
theorem maximum_reader [Bot α] (t : BinaryTree (κ × (Nat × α))) :
    maxHiRun t = (Balanced.maxHi t, 1) :=
  Prod.ext (maxHiRun_value t) (maxHiRun_cost t)

theorem maximum_zero_does_not_mean_empty :
    maxHiRun (.nil : NTree) = (0, 1) ∧
      maxHiRun (leaf id (point 0)) = (0, 1) ∧
      unitQuery .nil (point 0) = (false, 1) ∧
      unitQuery (leaf id (point 0)) (point 0) = (true, 3) ∧
      unitQuery (leaf id (point 0)) (point 1) = (false, 4) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! All prepared literal unit-tariff query paths. -/
theorem empty_query (query : NKey) : unitQuery .nil query = (false, 1) :=
  searchRun_nil (projectAt id 0) unitLE query

theorem singleton_paths :
    unitQuery (leaf id (point 1)) (point 1) = (true, 3) ∧
      unitQuery (leaf id (point 1)) (point 0) = (false, 3) ∧
      unitQuery (leaf id (point 1)) (point 2) = (false, 4) := ⟨rfl, rfl, rfl⟩

theorem rr_all_paths :
    unitQuery rrExpected (point 2) = (true, 3) ∧
      unitQuery rrExpected (point 1) = (true, 7) ∧
      unitQuery rrExpected (point 3) = (true, 8) ∧
      unitQuery rrExpected (point 101) = (false, 9) ∧
      unitQuery rrExpected (point 0) = (false, 7) := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem stale_and_underestimated_paths :
    unitQuery staleRotated (point 3) = (false, 9) ∧
      unitQuery underestimated (point 3) = (false, 5) := ⟨rfl, rfl⟩

theorem stored_height_is_uninspected :
    maxHiRun wrongHeight = (8, 1) ∧
      wrongHeight.height = 1 ∧
      unitQuery wrongHeight eightPoint = (true, 3) ∧
      unitQuery wrongHeight ninePoint = (false, 4) := ⟨rfl, rfl, rfl, rfl⟩

theorem empty_left_bypass : unitQuery emptyLeftGuard (point 0) = (true, 5) := rfl

theorem nonbalanced_and_repeated_key_paths :
    unitQuery unbalanced (point 3) = (true, 9) ∧
      unitQuery unbalanced (point 4) = (false, 10) ∧
      unitQuery repeatedKey eightPoint = (true, 3) ∧
      unitQuery repeatedKey ninePoint = (false, 6) := ⟨rfl, rfl, rfl, rfl⟩

theorem reverse_projection_path :
    searchRun (projectAt Examples.IntervalTreeSearch.reversedInterval 0) unitLE
      reverseProduct (point 0) = (false, 7) := rfl

/-! False callback values are honest raw clients, outside the usual erasure premises. -/
theorem actual_projected_interval_once :
    searchRun (fun (_ : NKey) => (point 0, 4)) unitLE
      (leaf id (point 1)) (point 0) = (true, 7) := rfl

theorem actual_false_first_comparison :
    searchRun (projectAt (id : NKey → NKey) 0) (fun _ _ => (false, 1))
      (leaf id (point 1)) (point 1) = (false, 3) ∧
      unitQuery (leaf id (point 1)) (point 1) = (true, 3) := ⟨rfl, rfl⟩

def secondFalse (x y : Nat) : Measured Bool Nat :=
  (if x = 4 ∧ y = 8 then false else decide (x ≤ y), 1)

theorem actual_false_second_comparison :
    searchRun (projectAt (id : NKey → NKey) 0) secondFalse
      (leaf id rootEight) (point 4) = (false, 4) ∧
      unitQuery (leaf id rootEight) (point 4) = (true, 3) := ⟨rfl, rfl⟩

/-- Two projections, five reached endpoint tests, one maximum read and two entries. -/
theorem rr_right_hit_constant_tariffs (p e : Nat) :
    searchRun (projectAt (id : NKey → NKey) p) (compareAt e)
      rrExpected (point 3) = (true, 2 * p + 5 * e + 3) := by
  apply Prod.ext
  · rfl
  · change p + ((e + e) + (1 + (e + ((p + ((e + e) + 0)) + 1)))) + 1 =
      2 * p + 5 * e + 3
    omega

/-- The projected low is the declared observation, so no global constant P exists. -/
def projectionLow (key : NKey) : Measured NKey Nat := (key, key.low)
def varyingLE (x y : Nat) : Measured Bool Nat :=
  (decide (x ≤ y), if x ≤ y then 2 else 5)

/-- Projection work 2+3; reached comparison work 2+5+5+2+2; local work 3. -/
theorem varying_callback_observations :
    searchRun projectionLow varyingLE rrExpected (point 3) = (true, 24) := rfl

theorem varying_comparison_global_bound (x y : Nat) : (varyingLE x y).2 ≤ 5 := by
  by_cases h : x ≤ y <;> simp [varyingLE, h]

theorem projection_low_not_globally_bounded :
    ¬ ∃ P, ∀ key, (projectionLow key).2 ≤ P := by
  rintro ⟨P, hP⟩
  have h := hP (point (P + 1))
  change P + 1 ≤ P at h
  omega

/-! Generic erasure and structural work keep endpoint and key universes independent. -/
theorem constant_callbacks_value_and_bound [LE α] [Bot α] [DecidableLE α]
    (iv : κ → IntervalKey α) (p e : Nat)
    (t : BinaryTree (κ × (Nat × α))) (query : IntervalKey α) :
    (searchRun (projectAt iv p) (compareAt e) t query).1 = Balanced.search iv t query ∧
      (searchRun (projectAt iv p) (compareAt e) t query).2 ≤
        (p + 3 * e + 2) * t.height + 1 :=
  ⟨searchRun_value iv (projectAt iv p) (compareAt e) t query
      (fun _ => rfl) (fun _ _ => rfl),
    searchRun_cost_le (projectAt iv p) (compareAt e) t query p e
      (fun _ => Nat.le_refl p) (fun _ _ => Nat.le_refl e)⟩

theorem unit_query_shape_bound (t : NTree) (query : NKey) :
    (unitQuery t query).2 ≤ 5 * t.height + 1 :=
  searchRun_cost_le (projectAt id 0) unitLE t query 0 1
    (fun _ => Nat.le_refl 0) (fun _ _ => Nat.le_refl 1)

/-- A false comparator still satisfies the raw structural bound. -/
theorem false_comparator_shape_bound (t : NTree) (query : NKey) :
    (searchRun (projectAt (id : NKey → NKey) 0) (fun _ _ => (false, 1)) t query).2 ≤
      5 * t.height + 1 :=
  searchRun_cost_le (projectAt id 0) (fun _ _ => (false, 1)) t query 0 1
    (fun _ => Nat.le_refl 0) (fun _ _ => Nat.le_refl 1)

theorem changed_projection_shape_bound (t : NTree) (query : NKey) :
    (searchRun (fun (_ : NKey) => (point 0, 4)) unitLE t query).2 ≤
      9 * t.height + 1 :=
  searchRun_cost_le (fun (_ : NKey) => (point 0, 4)) unitLE t query 4 1
    (fun _ => Nat.le_refl 4) (fun _ _ => Nat.le_refl 1)

/-- Stored 99 does not appear in the height-one bound, which is six. -/
theorem wrong_stored_height_bound (query : NKey) : (unitQuery wrongHeight query).2 ≤ 6 :=
  unit_query_shape_bound wrongHeight query

/-! Meaningful public soundness and the strictly weaker query completeness contract. -/
theorem malformed_success_has_original_witness :
    ∃ a ∈ setTree (Cached.erase malformed), IntervalKey.overlap a eightPoint :=
  searchRun_sound id (projectAt id 0) unitLE malformed eightPoint
    (fun _ => rfl) (fun _ _ => rfl) rfl

theorem weak_query_contracts (query : NKey) :
    ((unitQuery wrongHeight query).1 = true ↔
      ∃ a ∈ setTree (Cached.erase wrongHeight), IntervalKey.overlap a query) ∧
    ((unitQuery unbalanced query).1 = true ↔
      ∃ a ∈ setTree (Cached.erase unbalanced), IntervalKey.overlap a query) ∧
    ((unitQuery repeatedKey query).1 = true ↔
      ∃ a ∈ setTree (Cached.erase repeatedKey), IntervalKey.overlap a query) :=
  ⟨searchRun_correct id (projectAt id 0) unitLE wrongHeight query
      (fun _ => rfl) (fun _ _ => rfl) weak_maximum_validity.1 weak_low_order.1,
    searchRun_correct id (projectAt id 0) unitLE unbalanced query
      (fun _ => rfl) (fun _ _ => rfl) weak_maximum_validity.2.1 weak_low_order.2.1,
    searchRun_correct id (projectAt id 0) unitLE repeatedKey query
      (fun _ => rfl) (fun _ _ => rfl) weak_maximum_validity.2.2 weak_low_order.2.2⟩

theorem weak_inputs_exclude_full_validity :
    ¬Balanced.Valid id wrongHeight ∧ ¬Balanced.Valid id unbalanced ∧
      ¬Balanced.Valid id repeatedKey := weak_examples_not_full_valid

/-- The stale selected child is exhausted; the overlapping sibling is not tried. -/
theorem stale_query_misses_existing_overlap :
    unitQuery staleRotated (point 3) = (false, 9) ∧
      ∃ a ∈ setTree (Cached.erase staleRotated), IntervalKey.overlap a (point 3) :=
  ⟨rfl, stale_false_negative.2⟩

theorem underestimated_query_misses_existing_overlap :
    unitQuery underestimated (point 3) = (false, 5) ∧
      ∃ a ∈ setTree (Cached.erase underestimated), IntervalKey.overlap a (point 3) :=
  ⟨rfl, underestimated_false_negative.2.2.2.2⟩

/-- Full AVL set validity does not supply a missing low-projection compatibility law. -/
theorem reversed_projection_needs_compatibility :
    Balanced.Valid Examples.IntervalTreeSearch.reversedInterval reverseProduct ∧
      searchRun (projectAt Examples.IntervalTreeSearch.reversedInterval 0) unitLE
        reverseProduct (point 0) = (false, 7) ∧
      IntervalSet.hasOverlap (Examples.IntervalTreeSearch.reversedInterval ''
        setTree (Cached.erase reverseProduct)) (point 0) :=
  ⟨reverse_product_valid, rfl, reverse_false_negative.2⟩

/-! Occurrence keys are in a higher universe than their shared Nat interval. -/
theorem indexed_exact_queries :
    searchRun (projectAt indexedInterval 0) unitLE indexedBoth eightPoint = (true, 3) ∧
      searchRun (projectAt indexedInterval 0) unitLE indexedBoth ninePoint = (false, 7) :=
  ⟨rfl, rfl⟩

theorem indexed_strict_query_contract (query : NKey) :
    (searchRun (projectAt indexedInterval 0) unitLE indexedBoth query).1 = true ↔
      ∃ a ∈ setTree (Cached.erase indexedBoth), IntervalKey.overlap (indexedInterval a) query := by
  have valid : Balanced.Valid indexedInterval indexedBoth := indexed_prefix_valid 2
  exact searchRun_correct_of_strict indexedInterval (projectAt indexedInterval 0) unitLE
    indexedBoth query (fun _ => rfl) (fun _ _ => rfl)
    Examples.IntervalTreeSearch.indexed_compatible
    (Balanced.cacheValid_maximumTree indexedInterval valid.1.2) valid.2

/-- The converse universe separation also works: small keys, lifted endpoints. -/
def liftedPoint (n : Nat) : IntervalKey (ULift.{1} Nat) :=
  IntervalKey.ofBounds ⟨n⟩ ⟨n⟩ le_rfl

def liftedEndpointLeaf : BinaryTree (Unit × (Nat × ULift.{1} Nat)) :=
  .node ((), (99, ⟨7⟩)) .nil .nil

theorem lifted_endpoint_query :
    searchRun (projectAt (fun (_ : Unit) => liftedPoint 7) 0) (compareAt 1)
      liftedEndpointLeaf (liftedPoint 7) = (true, 3) := rfl

end Examples.MeasuredIntervalQueries
