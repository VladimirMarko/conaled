import Applications.Resources.HeightBalance.Logarithmic
import Applications.Resources.IntervalTree.Logarithmic
import Applications.Search.RectangleSweep.Complexity
import Examples.MeasuredHeightUpdates
import Examples.MeasuredIntervalQueries
import Examples.MeasuredBalancedRectangleSweep

/-!
# Connected structural logarithms and complete sweep bounds

The independent cases distinguish actual shape from stored summaries, nodes
from distinct keys, and closed admission from a particular event prefix.
All nine previously proved complete executions retain their literal costs.
The logarithmic bounds concern the declared source observations and globally
bounded callbacks; no bit-complexity or machine-time claim follows.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.MeasuredBalancedComplexity
open Trees Search Search.RectangleSweep Resources
open Examples.BalancedIntervalTrees
open Examples.MeasuredHeightUpdates
  (ordinaryHeight ordinaryCombine atomicLt ordinaryInsert ordinarySplit ordinaryDelete
    productHeight productCombine productInsert productDelete)
open Examples.MeasuredIntervalQueries (unitQuery unitLE projectAt)
open Examples.RectangleSweep (natSquare)
universe u v w

/-! Actual integer heights, including zero tolerance and empty carriers. -/

theorem empty_height_bounds {α : Type u} (d : Nat) :
    (.nil : BinaryTree α).height ≤ (d + 1) * Nat.clog 2 (.nil : BinaryTree α).numLeaves ∧
      (.nil : BinaryTree α).height ≤
        (d + 1) * Nat.clog 2 ((.nil : BinaryTree α).numNodes + 1) :=
  ⟨Trees.HeightBalance.height_le_mul_clog_numLeaves d .nil
      (Trees.HeightBalance.balancedD_nil d),
    Trees.HeightBalance.height_le_mul_clog_numNodes_add_one d .nil
      (Trees.HeightBalance.balancedD_nil d)⟩

theorem empty_carrier_and_annotation {σ : Type v} (d : Nat) :
    (.nil : BinaryTree (ULift.{u} PEmpty × σ)).height ≤
      (d + 1) * Nat.clog 2 ((.nil : BinaryTree (ULift.{u} PEmpty × σ)).numNodes + 1) :=
  (empty_height_bounds (α := ULift.{u} PEmpty × σ) d).2

theorem ordinary_perfect_balanced (d : Nat) :
    Trees.HeightBalance.BalancedD d (Cached.erase Examples.HeightUpdates.perfectSeven) := by
  simp [Examples.HeightUpdates.perfectSeven, Examples.HeightUpdates.heightNode,
    Examples.HeightUpdates.heightSingleton, Trees.HeightBalance.BalancedD, BinaryTree.height]

/-- Reuse the existing seven-node shape while making its key observation noninjective. -/
def repeatedSeven : BinaryTree Unit :=
  Examples.HeightUpdates.perfectSeven.map (fun _ => ())

theorem repeated_seven_balanced_zero : Trees.HeightBalance.BalancedD 0 repeatedSeven := by
  apply (Trees.HeightBalance.balancedD_map 0 _ _).mpr
  exact (Trees.HeightBalance.balancedD_map 0 Prod.fst _).mp (ordinary_perfect_balanced 0)

theorem repeated_seven_measures :
    repeatedSeven.height = 3 ∧ repeatedSeven.numNodes = 7 ∧
      repeatedSeven.numLeaves = 8 ∧ (inorder repeatedSeven).toFinset.card = 1 := by
  decide

theorem perfect_zero_tolerance_integer_bound :
    repeatedSeven.height ≤ (0 + 1) * Nat.clog 2 repeatedSeven.numLeaves ∧
      repeatedSeven.height = (0 + 1) * Nat.clog 2 repeatedSeven.numLeaves :=
  ⟨Trees.HeightBalance.height_le_mul_clog_numLeaves 0 repeatedSeven
      repeated_seven_balanced_zero, by decide⟩

theorem distinct_keys_do_not_bound_shape :
    ¬ repeatedSeven.height ≤ 2 * Nat.clog 2 ((inorder repeatedSeven).toFinset.card + 1) := by
  decide

/-- A single explicit separator; no general shape generator is needed. -/
def chainSeven : BinaryTree Unit :=
  .node () (.node () (.node () (.node () (.node () (.node ()
    (.node () .nil .nil) .nil) .nil) .nil) .nil) .nil) .nil

theorem chain_seven_requires_its_tolerance :
    Trees.HeightBalance.BalancedD 6 chainSeven ∧
      ¬ Trees.HeightBalance.BalancedD 1 chainSeven := by
  simp [chainSeven, Trees.HeightBalance.BalancedD, BinaryTree.height]

theorem chain_seven_integer_bounds :
    chainSeven.height ≤ (6 + 1) * Nat.clog 2 (chainSeven.numNodes + 1) ∧
      ¬ chainSeven.height ≤ 2 * Nat.clog 2 (chainSeven.numNodes + 1) :=
  ⟨Trees.HeightBalance.height_le_mul_clog_numNodes_add_one 6 chainSeven
      chain_seven_requires_its_tolerance.1, by decide⟩

theorem wrong_height_shape_balanced :
    Trees.HeightBalance.BalancedD 1 (Cached.erase wrongHeight) := by
  simp [wrongHeight, Trees.HeightBalance.BalancedD, BinaryTree.height]

/-- Neither the stored 99 nor full cache validity is a premise of a shape-cost bound. -/
theorem wrong_height_logarithmic_work (x query : NKey) :
    ¬ IntervalTree.Balanced.Valid id wrongHeight ∧
      wrongHeight.height ≤ 2 * Nat.clog 2 (wrongHeight.numNodes + 1) ∧
      (productInsert x wrongHeight).2 ≤ 66 * Nat.clog 2 (wrongHeight.numNodes + 1) + 8 ∧
      (unitQuery wrongHeight query).2 ≤ 10 * Nat.clog 2 (wrongHeight.numNodes + 1) + 1 := by
  refine ⟨weak_examples_not_full_valid.1, ?_, ?_, ?_⟩
  · simpa only [Cached.height_erase, Cached.numNodes_erase] using
      Trees.HeightBalance.height_le_mul_clog_numNodes_add_one
        1 (Cached.erase wrongHeight) wrong_height_shape_balanced
  · exact Resources.HeightBalance.insertRun_cost_le_clog
      (0, 0) productHeight (productCombine id) atomicLt 1 x wrongHeight 0 4 1
      (fun _ => Nat.le_refl 0) (fun _ _ _ => Nat.le_refl 4)
      (fun _ _ => Nat.le_refl 1) wrong_height_shape_balanced
  · exact Resources.IntervalTree.searchRun_cost_le_clog
      (projectAt id 0) unitLE wrongHeight query 1 0 1
      (fun _ => Nat.le_refl 0) (fun _ _ => Nat.le_refl 1) wrong_height_shape_balanced

/-- Bounded wrong callbacks still meet cost contracts, independently of erasure. -/
theorem wrong_callbacks_logarithmic_work (t : NTree) (x query : NKey)
    (balanced : Trees.HeightBalance.BalancedD 1 (Cached.erase t)) :
    (Resources.HeightBalance.insertRun (0, 0) productHeight (productCombine id)
      (fun _ _ => (false, 1)) 1 x t).2 ≤ 66 * Nat.clog 2 (t.numNodes + 1) + 8 ∧
      (Resources.IntervalTree.searchRun (projectAt (id : NKey → NKey) 0)
        (fun _ _ => (false, 1)) t query).2 ≤ 10 * Nat.clog 2 (t.numNodes + 1) + 1 ∧
      (Resources.IntervalTree.searchRun (fun (_ : NKey) => (point 0, 4))
        unitLE t query).2 ≤ 18 * Nat.clog 2 (t.numNodes + 1) + 1 :=
  ⟨Resources.HeightBalance.insertRun_cost_le_clog
      (0, 0) productHeight (productCombine id) (fun _ _ => (false, 1)) 1 x t 0 4 1
      (fun _ => Nat.le_refl 0) (fun _ _ _ => Nat.le_refl 4)
      (fun _ _ => Nat.le_refl 1) balanced,
    Resources.IntervalTree.searchRun_cost_le_clog
      (projectAt id 0) (fun _ _ => (false, 1)) t query 1 0 1
      (fun _ => Nat.le_refl 0) (fun _ _ => Nat.le_refl 1) balanced,
    Resources.IntervalTree.searchRun_cost_le_clog
      (fun (_ : NKey) => (point 0, 4)) unitLE t query 1 4 1
      (fun _ => Nat.le_refl 4) (fun _ _ => Nat.le_refl 1) balanced⟩

theorem unbounded_callbacks_remain_excluded :
    (¬ ∃ H, ∀ s, (Examples.MeasuredHeightUpdates.heightCharged s).2 ≤ H) ∧
      (¬ ∃ P, ∀ key, (Examples.MeasuredIntervalQueries.projectionLow key).2 ≤ P) :=
  ⟨Examples.MeasuredHeightUpdates.height_callback_unbounded,
    Examples.MeasuredIntervalQueries.projection_low_not_globally_bounded⟩

/-! Ordinary H=0, K=2, C=1 operation work, with all additive terms. -/

theorem ordinary_logarithmic_bounds (x : Nat) (t : Examples.HeightUpdates.HTree)
    (balanced : Trees.HeightBalance.BalancedD 1 (Cached.erase t)) :
    (ordinaryInsert x t).2 ≤ 54 * Nat.clog 2 (t.numNodes + 1) + 6 ∧
      (ordinarySplit t).2 ≤ 50 * Nat.clog 2 (t.numNodes + 1) + 1 ∧
      (ordinaryDelete x t).2 ≤ 54 * Nat.clog 2 (t.numNodes + 1) + 1 :=
  ⟨Resources.HeightBalance.insertRun_cost_le_clog
      0 ordinaryHeight ordinaryCombine atomicLt 1 x t 0 2 1
      (fun _ => Nat.le_refl 0) (fun _ _ _ => Nat.le_refl 2)
      (fun _ _ => Nat.le_refl 1) balanced,
    Resources.HeightBalance.splitMaxRun_cost_le_clog
      0 ordinaryHeight ordinaryCombine 1 t 0 2
      (fun _ => Nat.le_refl 0) (fun _ _ _ => Nat.le_refl 2) balanced,
    Resources.HeightBalance.deleteRun_cost_le_clog
      0 ordinaryHeight ordinaryCombine atomicLt 1 x t 0 2 1
      (fun _ => Nat.le_refl 0) (fun _ _ _ => Nat.le_refl 2)
      (fun _ _ => Nat.le_refl 1) balanced⟩

theorem ordinary_nonempty_extraction (t : Examples.HeightUpdates.HTree)
    (balanced : Trees.HeightBalance.BalancedD 1 (Cached.erase t)) (hne : t ≠ .nil) :
    (ordinarySplit t).2 ≤ 50 * Nat.clog 2 (t.numNodes + 1) :=
  Resources.HeightBalance.splitMaxRun_cost_le_clog_of_ne_nil
    0 ordinaryHeight ordinaryCombine 1 t 0 2
    (fun _ => Nat.le_refl 0) (fun _ _ _ => Nat.le_refl 2) balanced hne

theorem ordinary_empty_additive_terms :
    (ordinaryInsert 2 .nil).2 = 6 ∧ (ordinarySplit (.nil : Examples.HeightUpdates.HTree)).2 = 1 ∧
      (ordinaryDelete 2 .nil).2 = 1 ∧
      (ordinaryInsert 2 .nil).2 ≤ 54 * Nat.clog 2 (0 + 1) + 6 :=
  ⟨congrArg Prod.snd Examples.MeasuredHeightUpdates.ordinary_base_tariffs.1,
    congrArg Prod.snd Examples.MeasuredHeightUpdates.ordinary_base_tariffs.2.1,
    congrArg Prod.snd Examples.MeasuredHeightUpdates.ordinary_base_tariffs.2.2.2,
    (ordinary_logarithmic_bounds 2 .nil (Trees.HeightBalance.balancedD_nil 1)).1⟩

theorem ordinary_perfect_envelopes :
    (ordinaryInsert 8 Examples.HeightUpdates.perfectSeven).2 ≤ 168 ∧
      (ordinarySplit Examples.HeightUpdates.perfectSeven).2 ≤ 151 ∧
      (ordinaryDelete 4 Examples.HeightUpdates.perfectSeven).2 ≤ 163 ∧
      ordinaryDelete 4 Examples.HeightUpdates.perfectSeven =
        (Examples.HeightUpdates.deletePredecessorOutput, 27) :=
  ⟨(ordinary_logarithmic_bounds 8 _ (ordinary_perfect_balanced 1)).1,
    (ordinary_logarithmic_bounds 4 _ (ordinary_perfect_balanced 1)).2.1,
    (ordinary_logarithmic_bounds 4 _ (ordinary_perfect_balanced 1)).2.2,
    Examples.MeasuredHeightUpdates.ordinary_predecessor_tariff⟩

/-! Family consequences use log(n+1), not the larger n log n growth class. -/

theorem zero_affine_log_family :
    Asymptotics.IsBigO Filter.atTop (fun _ : Nat => (0 : ℝ))
      (fun n => Real.logb 2 (n + 1 : Nat)) := by
  simpa only [Nat.cast_zero] using
    Resources.isBigO_logb_succ_of_clog_bound (fun _ => 0) 0 0 7 (by
      intro n _
      simp)

/-- Arbitrary returned values and independent payload/summary universes remain admissible. -/
theorem update_families_logarithmic {α : Type u} {σ : Type v}
    (empty : σ) (heightRun : σ → Measured Nat Nat)
    (combineRun : σ → α → σ → Measured σ Nat)
    (ltRun : α → α → Measured Bool Nat) (d : Nat)
    (keys : Nat → α) (family : Nat → BinaryTree (α × σ)) (H K C : Nat)
    (hH : ∀ s, (heightRun s).2 ≤ H)
    (hK : ∀ l a r, (combineRun l a r).2 ≤ K)
    (hC : ∀ a b, (ltRun a b).2 ≤ C)
    (sizes : ∀ n, (family n).numNodes = n)
    (balanced : ∀ n, Trees.HeightBalance.BalancedD d (Cached.erase (family n))) :
    Asymptotics.IsBigO Filter.atTop
        (fun n => ((Resources.HeightBalance.insertRun empty heightRun combineRun ltRun
          d (keys n) (family n)).2 : ℝ))
        (fun n => Real.logb 2 (n + 1 : Nat)) ∧
      Asymptotics.IsBigO Filter.atTop
        (fun n => ((Resources.HeightBalance.splitMaxRun empty heightRun combineRun
          d (family n)).2 : ℝ))
        (fun n => Real.logb 2 (n + 1 : Nat)) ∧
      Asymptotics.IsBigO Filter.atTop
        (fun n => ((Resources.HeightBalance.deleteRun empty heightRun combineRun ltRun
          d (keys n) (family n)).2 : ℝ))
        (fun n => Real.logb 2 (n + 1 : Nat)) :=
  ⟨Resources.HeightBalance.insertRun_isBigO empty heightRun combineRun ltRun
      d keys family H K C hH hK hC sizes balanced,
    Resources.HeightBalance.splitMaxRun_isBigO empty heightRun combineRun
      d family H K hH hK sizes balanced,
    Resources.HeightBalance.deleteRun_isBigO empty heightRun combineRun ltRun
      d keys family H K C hH hK hC sizes balanced⟩

theorem ordinary_families_logarithmic (keys : Nat → Nat)
    (family : Nat → Examples.HeightUpdates.HTree)
    (sizes : ∀ n, (family n).numNodes = n)
    (balanced : ∀ n, Trees.HeightBalance.BalancedD 1 (Cached.erase (family n))) :
    Asymptotics.IsBigO Filter.atTop (fun n => ((ordinaryInsert (keys n) (family n)).2 : ℝ))
        (fun n => Real.logb 2 (n + 1 : Nat)) ∧
      Asymptotics.IsBigO Filter.atTop (fun n => ((ordinarySplit (family n)).2 : ℝ))
        (fun n => Real.logb 2 (n + 1 : Nat)) ∧
      Asymptotics.IsBigO Filter.atTop (fun n => ((ordinaryDelete (keys n) (family n)).2 : ℝ))
        (fun n => Real.logb 2 (n + 1 : Nat)) :=
  update_families_logarithmic 0 ordinaryHeight ordinaryCombine atomicLt 1 keys family 0 2 1
    (fun _ => Nat.le_refl 0) (fun _ _ _ => Nat.le_refl 2)
    (fun _ _ => Nat.le_refl 1) sizes balanced

/-- Endpoint and key universes remain separate; no semantic callback equation is needed. -/
theorem query_family_logarithmic {α : Type u} {κ : Type w} [LE α] [Bot α]
    (ivRun : κ → Measured (IntervalKey α) Nat) (leRun : α → α → Measured Bool Nat)
    (d : Nat) (queries : Nat → IntervalKey α)
    (family : Nat → BinaryTree (κ × (Nat × α))) (P E : Nat)
    (hP : ∀ a, (ivRun a).2 ≤ P) (hE : ∀ a b, (leRun a b).2 ≤ E)
    (sizes : ∀ n, (family n).numNodes = n)
    (balanced : ∀ n, Trees.HeightBalance.BalancedD d (Cached.erase (family n))) :
    Asymptotics.IsBigO Filter.atTop
      (fun n => ((Resources.IntervalTree.searchRun ivRun leRun (family n) (queries n)).2 : ℝ))
      (fun n => Real.logb 2 (n + 1 : Nat)) :=
  Resources.IntervalTree.searchRun_isBigO ivRun leRun d queries family P E hP hE sizes balanced

/-! Finite support uses complete occurrence keys, even for equal rectangles. -/

theorem support_cardinalities :
    (MeasuredBalanced.inputKeys ([] : List (Rectangle Nat Int))).ncard = 0 ∧
      (MeasuredBalanced.inputKeys [natSquare]).ncard = 1 ∧
      (MeasuredBalanced.inputKeys [natSquare, natSquare]).ncard = 2 :=
  ⟨MeasuredBalanced.inputKeys_ncard [], MeasuredBalanced.inputKeys_ncard [natSquare],
    MeasuredBalanced.inputKeys_ncard [natSquare, natSquare]⟩

theorem square_key_allowed : sweepKey0 ∈ MeasuredBalanced.inputKeys [natSquare] :=
  MeasuredBalanced.occurrenceKey_mem_inputKeys [natSquare] ⟨0, by decide⟩

theorem duplicate_keys_allowed :
    sweepKey0 ∈ MeasuredBalanced.inputKeys [natSquare, natSquare] ∧
      sweepKey1 ∈ MeasuredBalanced.inputKeys [natSquare, natSquare] ∧ sweepKey0 ≠ sweepKey1 :=
  ⟨MeasuredBalanced.occurrenceKey_mem_inputKeys [natSquare, natSquare] ⟨0, by decide⟩,
    MeasuredBalanced.occurrenceKey_mem_inputKeys [natSquare, natSquare] ⟨1, by decide⟩,
    by decide⟩

theorem singleton_leaf_admitted :
    MeasuredBalanced.Admitted [natSquare] (leaf keyInterval sweepKey0) := by
  simpa only [Examples.MeasuredBalancedRectangleSweep.indexed_update_history.1] using
    MeasuredBalanced.insertRun_admitted [natSquare] sweepKey0 .nil square_key_allowed
      (MeasuredBalanced.admitted_nil [natSquare])

theorem singleton_delete_admitted :
    MeasuredBalanced.Admitted [natSquare]
      (MeasuredBalanced.deleteRun sweepKey0 (leaf keyInterval sweepKey0)).1 ∧
      MeasuredBalanced.deleteRun sweepKey0 (leaf keyInterval sweepKey0) = (.nil, 14) :=
  ⟨MeasuredBalanced.deleteRun_admitted [natSquare] sweepKey0 _ singleton_leaf_admitted, rfl⟩

theorem duplicate_pair_admitted :
    MeasuredBalanced.Admitted [natSquare, natSquare] activePair := by
  have first : MeasuredBalanced.Admitted [natSquare, natSquare] (leaf keyInterval sweepKey0) := by
    simpa only [Examples.MeasuredBalancedRectangleSweep.indexed_update_history.1] using
      MeasuredBalanced.insertRun_admitted [natSquare, natSquare] sweepKey0 .nil
        duplicate_keys_allowed.1 (MeasuredBalanced.admitted_nil [natSquare, natSquare])
  simpa only [Examples.MeasuredBalancedRectangleSweep.indexed_update_history.2.1] using
    MeasuredBalanced.insertRun_admitted [natSquare, natSquare] sweepKey1
      (leaf keyInterval sweepKey0) duplicate_keys_allowed.2.1 first

theorem surviving_id_admitted :
    MeasuredBalanced.Admitted [natSquare, natSquare] (leaf keyInterval sweepKey1) := by
  simpa only [Examples.MeasuredBalancedRectangleSweep.indexed_update_history.2.2.2.1] using
    MeasuredBalanced.deleteRun_admitted [natSquare, natSquare] sweepKey0 activePair
      duplicate_pair_admitted

theorem singleton_excludes_id_one : sweepKey1 ∉ MeasuredBalanced.inputKeys [natSquare] := by
  rintro ⟨i, hi⟩
  have range := i.isLt
  have ids := congrArg (fun key : Key Nat => (ofLex key).2) hi
  change i.val = 1 at ids
  change i.val < 1 at range
  omega

/-- Deletion needs no allowed-key premise, even on a nonempty admitted state. -/
theorem unsupported_deletion_stays_admitted :
    sweepKey1 ∉ MeasuredBalanced.inputKeys [natSquare] ∧
      MeasuredBalanced.Admitted [natSquare]
        (MeasuredBalanced.deleteRun sweepKey1 (leaf keyInterval sweepKey0)).1 :=
  ⟨singleton_excludes_id_one,
    MeasuredBalanced.deleteRun_admitted [natSquare] sweepKey1 _ singleton_leaf_admitted⟩

theorem unsupported_insertion_is_not_admitted :
    ¬ MeasuredBalanced.Admitted [natSquare] (MeasuredBalanced.insertRun sweepKey1 .nil).1 := by
  intro admitted
  apply singleton_excludes_id_one
  apply admitted.2
  change sweepKey1 ∈ setTree (Cached.erase (leaf keyInterval sweepKey1))
  simp [leaf]

theorem pair_exceeds_singleton_support : ¬ MeasuredBalanced.Admitted [natSquare] activePair := by
  intro admitted
  have nodes := MeasuredBalanced.admitted_numNodes_le [natSquare] activePair admitted
  change 2 ≤ 1 at nodes
  omega

theorem empty_support_forces_nil {α : Type u} {β : Type v}
    [LinearOrder α] [OrderBot α] [LinearOrder β] (t : MeasuredBalanced.Tree α)
    (admitted : MeasuredBalanced.Admitted ([] : List (Rectangle α β)) t) : t = .nil := by
  have nodes := MeasuredBalanced.admitted_numNodes_le ([] : List (Rectangle α β)) t admitted
  cases t with
  | nil => rfl
  | node a l r => simp only [BinaryTree.numNodes, List.length_nil] at nodes; omega

/-- Primitive cost bounds do not require the proposed insertion key to be supported. -/
theorem empty_support_primitive_bounds (key : Key Nat) (query : IntervalKey Nat) :
    (MeasuredBalanced.insertRun key .nil).2 ≤ 8 ∧
      (MeasuredBalanced.splitMaxRun (.nil : MeasuredBalanced.Tree Nat)).2 ≤ 1 ∧
      (MeasuredBalanced.deleteRun key .nil).2 ≤ 1 ∧
      (MeasuredBalanced.queryRun .nil query).2 ≤ 1 :=
  ⟨MeasuredBalanced.insertRun_admitted_cost_le ([] : List (Rectangle Nat Int)) key .nil
      (MeasuredBalanced.admitted_nil []),
    MeasuredBalanced.splitMaxRun_admitted_cost_le ([] : List (Rectangle Nat Int)) .nil
      (MeasuredBalanced.admitted_nil []),
    MeasuredBalanced.deleteRun_admitted_cost_le ([] : List (Rectangle Nat Int)) key .nil
      (MeasuredBalanced.admitted_nil []),
    MeasuredBalanced.queryRun_admitted_cost_le ([] : List (Rectangle Nat Int)) .nil query
      (MeasuredBalanced.admitted_nil [])⟩

/-- This admitted start was obtained by deleting ID0; it is not the first inserted leaf. -/
theorem noninitial_admitted_scan :
    leaf keyInterval sweepKey1 ≠ leaf keyInterval sweepKey0 ∧
      (MeasuredBalanced.scanRun (leaf keyInterval sweepKey1)
        (events [natSquare, natSquare])).2 ≤ 753 :=
  ⟨by decide, MeasuredBalanced.scanRun_events_cost_le_admitted
    [natSquare, natSquare] (leaf keyInterval sweepKey1) surviving_id_admitted⟩

theorem duplicate_primitive_envelopes (key : Key Nat) (query : IntervalKey Nat) :
    activePair.numNodes = 2 ∧ activePair.height = 2 ∧
      (MeasuredBalanced.insertRun key activePair).2 ≤ 180 ∧
      (MeasuredBalanced.splitMaxRun activePair).2 ≤ 125 ∧
      (MeasuredBalanced.deleteRun key activePair).2 ≤ 173 ∧
      (MeasuredBalanced.queryRun activePair query).2 ≤ 21 :=
  ⟨rfl, rfl,
    MeasuredBalanced.insertRun_admitted_cost_le [natSquare, natSquare] key activePair duplicate_pair_admitted,
    MeasuredBalanced.splitMaxRun_admitted_cost_le [natSquare, natSquare] activePair duplicate_pair_admitted,
    MeasuredBalanced.deleteRun_admitted_cost_le [natSquare, natSquare] key activePair duplicate_pair_admitted,
    MeasuredBalanced.queryRun_admitted_cost_le [natSquare, natSquare] activePair query duplicate_pair_admitted⟩

/-- Arbitrary admitted states and arbitrary queries retain independent x/y universes. -/
theorem admitted_state_bounds {α : Type u} {β : Type v}
    [LinearOrder α] [OrderBot α] [LinearOrder β]
    (rs : List (Rectangle α β)) (t : MeasuredBalanced.Tree α) (query : IntervalKey α)
    (admitted : MeasuredBalanced.Admitted rs t) :
    (MeasuredBalanced.inputKeys rs).Finite ∧ t.numNodes ≤ rs.length ∧
      t.height ≤ 2 * Nat.clog 2 (rs.length + 1) ∧
      (MeasuredBalanced.queryRun t query).2 ≤ 10 * Nat.clog 2 (rs.length + 1) + 1 ∧
      (MeasuredBalanced.scanRun t (events rs)).2 ≤
        182 * rs.length * Nat.clog 2 (rs.length + 1) + 12 * rs.length + 1 :=
  ⟨MeasuredBalanced.inputKeys_finite rs,
    MeasuredBalanced.admitted_numNodes_le rs t admitted,
    MeasuredBalanced.admitted_height_le rs t admitted,
    MeasuredBalanced.queryRun_admitted_cost_le rs t query admitted,
    MeasuredBalanced.scanRun_events_cost_le_admitted rs t admitted⟩

theorem every_scheduled_occurrence_is_supported {α : Type u} {β : Type v}
    [LinearOrder α] [OrderBot α] [LinearOrder β]
    (rs : List (Rectangle α β)) (e : Event α β) (mem : e ∈ events rs) :
    e.completeKey ∈ MeasuredBalanced.inputKeys rs :=
  MeasuredBalanced.event_key_mem_inputKeys rs e mem

theorem small_scan_envelopes :
    (MeasuredBalanced.scanRun .nil (events ([] : List (Rectangle Nat Int)))).2 ≤ 1 ∧
      (MeasuredBalanced.scanRun .nil (events [natSquare])).2 ≤ 195 ∧
      (MeasuredBalanced.scanRun .nil (events [natSquare, natSquare])).2 ≤ 753 ∧
      (MeasuredBalanced.scanRun .nil (events [natSquare, natSquare, natSquare])).2 ≤ 1129 :=
  ⟨MeasuredBalanced.scanRun_events_cost_le_admitted [] .nil (MeasuredBalanced.admitted_nil []),
    MeasuredBalanced.scanRun_events_cost_le_admitted [natSquare] .nil
      (MeasuredBalanced.admitted_nil [natSquare]),
    MeasuredBalanced.scanRun_events_cost_le_admitted [natSquare, natSquare] .nil
      (MeasuredBalanced.admitted_nil [natSquare, natSquare]),
    MeasuredBalanced.scanRun_events_cost_le_admitted [natSquare, natSquare, natSquare] .nil
      (MeasuredBalanced.admitted_nil [natSquare, natSquare, natSquare])⟩

/-! Existing exact whole executions connect to the new all-input envelope. -/

def fullEnvelope (n : Nat) : Nat :=
  24 * n * Nat.clog 2 (2 * n) + 182 * n * Nat.clog 2 (n + 1) + 40 * n + 8

theorem small_full_envelopes :
    fullEnvelope 0 = 8 ∧ fullEnvelope 1 = 254 ∧
      fullEnvelope 2 = 912 ∧ fullEnvelope 3 = 1436 := by decide

theorem pipeline_and_bound (rs : List (Rectangle Nat Int)) (answer : Bool) (work bound : Nat)
    (executed : MeasuredBalanced.sweepRun rs = (answer, work))
    (envelope : fullEnvelope rs.length = bound) :
    MeasuredBalanced.sweepRun rs = (answer, work) ∧ (MeasuredBalanced.sweepRun rs).2 ≤ bound := by
  refine ⟨executed, ?_⟩
  have h := MeasuredBalanced.sweepRun_cost_le rs
  change (MeasuredBalanced.sweepRun rs).2 ≤ fullEnvelope rs.length at h
  exact envelope ▸ h

theorem empty_pipeline_envelope :
    MeasuredBalanced.sweepRun ([] : List (Rectangle Nat Int)) = (false, 8) ∧
      (MeasuredBalanced.sweepRun ([] : List (Rectangle Nat Int))).2 ≤ 8 :=
  pipeline_and_bound [] false 8 8
    Examples.MeasuredBalancedRectangleSweep.empty_pipeline.2.2.2 (by decide)

theorem square_pipeline_envelope :
    MeasuredBalanced.sweepRun [natSquare] = (false, 64) ∧
      (MeasuredBalanced.sweepRun [natSquare]).2 ≤ 254 :=
  pipeline_and_bound [natSquare] false 64 254
    Examples.MeasuredBalancedRectangleSweep.singleton_pipeline.2.2.2 (by decide)

theorem point_pipeline_envelope :
    MeasuredBalanced.sweepRun [Examples.MeasuredBalancedRectangleSweep.natPoint] = (false, 66) ∧
      (MeasuredBalanced.sweepRun [Examples.MeasuredBalancedRectangleSweep.natPoint]).2 ≤ 254 :=
  pipeline_and_bound [Examples.MeasuredBalancedRectangleSweep.natPoint] false 66 254
    Examples.MeasuredBalancedRectangleSweep.point_pipeline.2.2.2 (by decide)

theorem duplicate_pipeline_envelope :
    MeasuredBalanced.sweepRun [natSquare, natSquare] = (true, 126) ∧
      (MeasuredBalanced.sweepRun [natSquare, natSquare]).2 ≤ 912 :=
  pipeline_and_bound [natSquare, natSquare] true 126 912
    Examples.MeasuredBalancedRectangleSweep.duplicate_pipeline.2.2.2 (by decide)

theorem triple_pipeline_envelope :
    MeasuredBalanced.sweepRun [natSquare, natSquare, natSquare] = (true, 221) ∧
      (MeasuredBalanced.sweepRun [natSquare, natSquare, natSquare]).2 ≤ 1436 :=
  pipeline_and_bound [natSquare, natSquare, natSquare] true 221 1436
    Examples.MeasuredBalancedRectangleSweep.triple_pipeline.2.2.2 (by decide)

theorem x_gap_pipeline_envelope :
    MeasuredBalanced.sweepRun [natSquare, xGap] = (false, 185) ∧
      (MeasuredBalanced.sweepRun [natSquare, xGap]).2 ≤ 912 :=
  pipeline_and_bound [natSquare, xGap] false 185 912
    Examples.MeasuredBalancedRectangleSweep.x_gap_pipeline.2.2.2 (by decide)

theorem y_gap_pipeline_envelope :
    MeasuredBalanced.sweepRun [natSquare, yGap] = (false, 150) ∧
      (MeasuredBalanced.sweepRun [natSquare, yGap]).2 ≤ 912 :=
  pipeline_and_bound [natSquare, yGap] false 150 912
    Examples.MeasuredBalancedRectangleSweep.y_gap_pipeline.2.2.2 (by decide)

theorem reversed_gap_pipeline_envelope :
    MeasuredBalanced.sweepRun [yGap, natSquare] = (false, 152) ∧
      (MeasuredBalanced.sweepRun [yGap, natSquare]).2 ≤ 912 :=
  pipeline_and_bound [yGap, natSquare] false 152 912
    Examples.MeasuredBalancedRectangleSweep.reversed_y_gap_pipeline.2.2.2 (by decide)

theorem post_deletion_pipeline_envelope :
    MeasuredBalanced.sweepRun [natSquare, yGap, yGap] = (true, 228) ∧
      (MeasuredBalanced.sweepRun [natSquare, yGap, yGap]).2 ≤ 1436 :=
  pipeline_and_bound [natSquare, yGap, yGap] true 228 1436
    Examples.MeasuredBalancedRectangleSweep.hit_after_deletion_pipeline.2.2.2 (by decide)

theorem zero_vanishing_envelope_fails (C : Nat) :
    ¬ (MeasuredBalanced.sweepRun ([] : List (Rectangle Nat Int))).2 ≤ C * 0 * Nat.clog 2 0 := by
  rw [Examples.MeasuredBalancedRectangleSweep.empty_pipeline.2.2.2]
  simp

theorem duplicate_eventual_envelope :
    (MeasuredBalanced.sweepRun [natSquare, natSquare]).2 ≤ 456 * 2 * Nat.clog 2 2 :=
  MeasuredBalanced.sweepRun_cost_le_clog [natSquare, natSquare] (by decide)

theorem singleton_shifted_envelope :
    (MeasuredBalanced.sweepRun [natSquare]).2 ≤ 278 * Nat.clog 2 2 :=
  MeasuredBalanced.sweepRun_cost_le_clog_succ [natSquare] (by decide)

/-- A genuine all-size input family, with every duplicate retaining its occurrence ID. -/
theorem repeated_rectangle_family {α : Type u} {β : Type v}
    [LinearOrder α] [OrderBot α] [LinearOrder β] (r : Rectangle α β) :
    Asymptotics.IsBigO Filter.atTop
      (fun n => ((MeasuredBalanced.sweepRun (List.replicate n r)).2 : ℝ))
      (fun n => (n : ℝ) * Real.logb 2 n) :=
  MeasuredBalanced.sweepRun_isBigO (fun n => List.replicate n r)
    (fun _ => by simp)

theorem repeated_square_all_input_bound (n : Nat) :
    (MeasuredBalanced.sweepRun (List.replicate n natSquare)).2 ≤ fullEnvelope n := by
  simpa only [List.length_replicate, fullEnvelope] using
    MeasuredBalanced.sweepRun_cost_le (List.replicate n natSquare)

theorem repeated_square_eventual_bound (n : Nat) (hn : 2 ≤ n) :
    (MeasuredBalanced.sweepRun (List.replicate n natSquare)).2 ≤ 456 * n * Nat.clog 2 n := by
  simpa only [List.length_replicate] using
    MeasuredBalanced.sweepRun_cost_le_clog (List.replicate n natSquare)
      (by simpa only [List.length_replicate] using hn)

theorem repeated_square_logarithmic_sweep :
    Asymptotics.IsBigO Filter.atTop
      (fun n => ((MeasuredBalanced.sweepRun (List.replicate n natSquare)).2 : ℝ))
      (fun n => (n : ℝ) * Real.logb 2 n) :=
  repeated_rectangle_family natSquare

end Examples.MeasuredBalancedComplexity
