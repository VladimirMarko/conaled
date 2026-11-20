import Applications.Resources.ListPriorityQueue

/-!
# Executed source priority-queue costs

The expected values distinguish comparison-first selection, duplicate occurrences
and operand order. Counts use the public measured results; they concern explicit
source observations, not native timing, sharing or allocation.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.ListPriorityQueueWork

open Resources.ListPriorityQueue

universe u v

abbrev maxUnit : Nat → Nat → Resources.Measured Bool Nat :=
  unitComparator (fun candidate head => head ≤ candidate)

/-- Price source calls, comparisons and cons, leaving comparator work separate. -/
def unitPrices : Cost := cost 1 1 0 1

/-- The unary model instead prices the actual comparator work once. -/
def unaryPrices : Cost := cost 1 0 1 1

theorem source_delete_unit_exact (queue : List Nat) :
    deleteMaxRun maxUnit queue =
      (Search.ListMaximumQueue.deleteMax queue,
        cost (queue.length + 1) (queue.length - 1) (queue.length - 1) (queue.length - 1)) := by
  apply Prod.ext (deleteMaxRun_source maxUnit (fun _ _ => rfl) queue)
  rw [deleteMaxRun_cost, deleteMaxRun_unit_work]

theorem select_empty : selectRun maxUnit 7 [] = ((7, []), cost 1 0 0 0) :=
  selectRun_nil maxUnit 7

theorem both_candidate_branches :
    selectRun maxUnit 2 [1, 3] = ((3, [1, 2]), cost 3 2 2 2) :=
  selectRun_unit_exact (fun a b : Nat => b ≤ a) 2 [1, 3]

theorem tie_retains_seed :
    selectRun maxUnit 7 [7] = ((7, [7]), cost 2 1 1 1) :=
  selectRun_unit_exact (fun a b : Nat => b ≤ a) 7 [7]

theorem known_maximum_still_scans :
    selectRun maxUnit 7 [1, 2, 0] = ((7, [1, 2, 0]), cost 4 3 3 3) :=
  selectRun_unit_exact (fun a b : Nat => b ≤ a) 7 [1, 2, 0]

theorem tied_selection_family (n : Nat) :
    selectRun maxUnit 7 (List.replicate n 7) =
      ((7, List.replicate n 7), cost (n + 1) n n n) := by
  rw [selectRun_unit_exact, List.length_replicate]
  have selected := Applications.Sorting.SourceSelection.select_of_lower
    (fun a b : Nat => b ≤ a) 7 (List.replicate n 7)
    (fun _ member => Nat.le_of_eq (List.mem_replicate.mp member).2)
  rw [selected]

theorem empty_delete : deleteMaxRun maxUnit [] = (none, cost 1 0 0 0) :=
  deleteMaxRun_nil maxUnit

theorem zero_is_a_key :
    deleteMaxRun maxUnit [0] = (some (0, []), cost 2 0 0 0) := by
  rw [deleteMaxRun_cons, selectRun_nil]
  apply Prod.ext
  · rfl
  · funext metric
    cases metric <;> rfl

theorem exact_source_remainder :
    deleteMaxRun maxUnit [3, 1, 2] = (some (3, [1, 2]), cost 4 2 2 2) :=
  source_delete_unit_exact [3, 1, 2]

theorem first_repeated_maximum :
    deleteMaxRun maxUnit [2, 7, 7, 4] = (some (7, [2, 7, 4]), cost 5 3 3 3) :=
  source_delete_unit_exact [2, 7, 7, 4]

theorem second_repeated_maximum :
    deleteMaxRun maxUnit [2, 7, 4] = (some (7, [2, 4]), cost 4 2 2 2) :=
  source_delete_unit_exact [2, 7, 4]

theorem first_removes_one_occurrence :
    ([2, 7, 7, 4] : List Nat).count 7 = 1 + ([2, 7, 4] : List Nat).count 7 := by
  simpa only [beq_self_eq_true, ↓reduceIte] using
    deleteMaxRun_count maxUnit [2, 7, 7, 4] 7 [2, 7, 4]
      (congrArg Prod.fst first_repeated_maximum) 7

theorem second_removes_one_occurrence :
    ([2, 7, 4] : List Nat).count 7 = 1 + ([2, 4] : List Nat).count 7 := by
  simpa only [beq_self_eq_true, ↓reduceIte] using
    deleteMaxRun_count maxUnit [2, 7, 4] 7 [2, 4]
      (congrArg Prod.fst second_repeated_maximum) 7

theorem successful_residual_size : ([2, 7, 4] : List Nat).length + 1 = [2, 7, 7, 4].length :=
  deleteMaxRun_length maxUnit [2, 7, 7, 4] 7 [2, 7, 4]
    (congrArg Prod.fst first_repeated_maximum)

/-- The second deletion receives the first run's actual residual list. -/
def twoDeletes (cmp : Nat → Nat → Resources.Measured Bool Nat) (queue : List Nat) :
    Resources.Measured (Option (Nat × Nat × List Nat)) Cost :=
  Resources.bind (deleteMaxRun cmp queue) fun
    | none => Resources.pure none
    | some (first, rest) => Resources.bind (deleteMaxRun cmp rest) fun
        | none => Resources.pure none
        | some (second, final) => Resources.pure (some (first, second, final))

theorem repeated_maxima_client :
    twoDeletes maxUnit [2, 7, 7, 4] = (some (7, 7, [2, 4]), cost 9 5 5 5) := by
  unfold twoDeletes
  rw [first_repeated_maximum]
  dsimp only [Resources.bind]
  rw [second_repeated_maximum]
  apply Prod.ext
  · rfl
  · funext metric
    cases metric <;> rfl

theorem two_deletes_empty : twoDeletes maxUnit [] = (none, cost 1 0 0 0) := by
  unfold twoDeletes
  rw [deleteMaxRun_nil]
  apply Prod.ext
  · rfl
  · funext metric
    cases metric <;> rfl

theorem two_deletes_singleton : twoDeletes maxUnit [0] = (none, cost 3 0 0 0) := by
  unfold twoDeletes
  rw [zero_is_a_key]
  dsimp only [Resources.bind]
  rw [deleteMaxRun_nil]
  apply Prod.ext
  · rfl
  · funext metric
    cases metric <;> rfl

theorem insertion_does_not_scan (key : Nat) (queue : List Nat) :
    insertRun key queue = (key :: queue, cost 1 0 0 1) := insertRun_exact key queue

theorem empty_has_constant_price :
    price unitPrices (emptyRun : Resources.Measured (List Nat) Cost).2 = 1 := emptyRun_price unitPrices

theorem insert_has_constant_price (key : Nat) (queue : List Nat) :
    price unitPrices (insertRun key queue).2 = 2 := insertRun_price unitPrices key queue

theorem empty_left_merge (queue : List Nat) :
    mergeRun [] queue = (queue, cost 1 0 0 0) := mergeRun_exact [] queue

theorem merge_copies_only_left :
    mergeRun [7, 2, 7] [7, 0] = ([7, 2, 7, 7, 0], cost 4 0 0 3) :=
  mergeRun_exact [7, 2, 7] [7, 0]

def mergeThenDelete (cmp : Nat → Nat → Resources.Measured Bool Nat) (left right : List Nat) :
    Resources.Measured (Option (Nat × List Nat)) Cost :=
  Resources.bind (mergeRun left right) (deleteMaxRun cmp)

theorem duplicate_rich_merge_client :
    mergeThenDelete maxUnit [7, 2, 7] [7, 0] =
      (some (7, [2, 7, 7, 0]), cost 10 4 4 7) := by
  unfold mergeThenDelete
  rw [merge_copies_only_left]
  dsimp only [Resources.bind]
  rw [source_delete_unit_exact]
  apply Prod.ext
  · rfl
  · funext metric
    cases metric <;> rfl

theorem merged_delete_retains_two_sevens :
    ((mergeRun [7, 2, 7] [7, 0]).1).count 7 =
      1 + ([2, 7, 7, 0] : List Nat).count 7 := by
  rw [mergeRun_value]
  have removed : (deleteMaxRun maxUnit ([7, 2, 7] ++ [7, 0])).1 = some (7, [2, 7, 7, 0]) :=
    congrArg Prod.fst (source_delete_unit_exact _)
  simpa only [beq_self_eq_true, ↓reduceIte] using
    deleteMaxRun_count maxUnit _ 7 [2, 7, 7, 0] removed 7

theorem merge_cost_changes_under_swap :
    (mergeRun [1, 1] [2]).2 .cons = 2 ∧
      (mergeRun [2] [1, 1]).2 .cons = 1 :=
  ⟨mergeRun_copies [1, 1] [2], mergeRun_copies [2] [1, 1]⟩

theorem merge_observation_commutes :
    ((mergeRun [1, 1] [2]).1).Perm ((mergeRun [2] [1, 1]).1) := by
  rw [mergeRun_value, mergeRun_value]
  exact List.perm_append_comm

theorem merge_raw_values_differ :
    (mergeRun [1, 1] [2]).1 ≠ (mergeRun [2] [1, 1]).1 := by
  rw [mergeRun_value, mergeRun_value]
  decide

theorem merge_left_family (n : Nat) :
    (mergeRun (List.replicate n 7) [0]).2 .cons = n := mergeRun_growing_left 7 [0] n

theorem total_size_does_not_lower_bound_calls (K threshold : Nat) :
    ∃ left right : List Nat, threshold ≤ left.length + right.length ∧
      K * (mergeRun left right).2 .calls < left.length + right.length :=
  merge_no_total_lower 7 K threshold

/-- The carrier and observed key have independent universes and no payload order. -/
theorem keyed_unit_projection {α : Type u} {κ : Type v} [LE κ] [DecidableLE κ]
    (key : α → κ) (seed : α) (tail : List α) :
    ((selectRun (unitComparator (fun a b => key b ≤ key a)) seed tail).1,
      (selectRun (unitComparator (fun a b => key b ≤ key a)) seed tail).2 .comparisons) =
      Resources.SelectionSort.selectRun (fun a b => key b ≤ key a) seed tail :=
  selectRun_unit_projection _ seed tail

theorem tied_payload_keeps_actual_seed :
    selectRun (unitComparator (fun a b : Nat × String => b.1 ≤ a.1)) (7, "seed") [(7, "head")] =
      (((7, "seed"), [(7, "head")]), cost 2 1 1 1) :=
  selectRun_unit_exact _ (7, "seed") [(7, "head")]

def replaceComparator (_candidate _head : Nat) : Resources.Measured Bool Nat := (false, 0)

theorem arbitrary_comparator_result :
    selectRun replaceComparator 7 [2, 1] = ((1, [7, 2]), cost 3 2 0 2) := by
  apply Prod.ext
  · rw [selectRun_value]
    rfl
  · rw [selectRun_cost]
    funext metric
    cases metric <;> rfl

theorem arbitrary_comparator_preserves_occurrences :
    ([7, 2, 1] : List Nat).Perm
      ((selectRun replaceComparator 7 [2, 1]).1.1 :: (selectRun replaceComparator 7 [2, 1]).1.2) :=
  selectRun_perm replaceComparator 7 [2, 1]

theorem arbitrary_comparator_is_not_a_maximum :
    ¬ ∀ a ∈ ([7, 2, 1] : List Nat), a ≤ (selectRun replaceComparator 7 [2, 1]).1.1 := by
  rw [arbitrary_comparator_result]
  intro maximum
  have impossible := maximum 7 (by decide)
  change (7 : Nat) ≤ 1 at impossible
  omega

theorem unary_candidate_changes :
    selectRun unaryMaxComparator 2 [1, 3] = ((3, [1, 2]), cost 3 2 5 2) := by
  apply Prod.ext (selectRun_unary_value 2 [1, 3])
  have work : (selectRun unaryMaxComparator 2 [1, 3]).2 .comparisonWork = 5 := by
    simp [selectRun_work_step, selectRun_work_nil, unaryMaxComparator,
      Resources.UnaryComparison.unaryLERun_spec]
  rw [selectRun_cost, work]
  rfl

theorem unary_duplicate_queue :
    deleteMaxRun unaryMaxComparator [2, 7, 7, 4] =
      (some (7, [2, 7, 4]), cost 5 3 16 3) := by
  apply Prod.ext (deleteMaxRun_unary_value [2, 7, 7, 4])
  have work : (deleteMaxRun unaryMaxComparator [2, 7, 7, 4]).2 .comparisonWork = 16 := by
    rw [deleteMaxRun_work_cons]
    simp [selectRun_work_step, selectRun_work_nil, unaryMaxComparator,
      Resources.UnaryComparison.unaryLERun_spec]
  rw [deleteMaxRun_cost, work]
  rfl

theorem equal_value_and_calls_different_comparator_work :
    (deleteMaxRun maxUnit [2, 7, 7, 4]).1 = (deleteMaxRun unaryMaxComparator [2, 7, 7, 4]).1 ∧
    (deleteMaxRun maxUnit [2, 7, 7, 4]).2 .comparisons =
      (deleteMaxRun unaryMaxComparator [2, 7, 7, 4]).2 .comparisons ∧
    (deleteMaxRun maxUnit [2, 7, 7, 4]).2 .comparisonWork ≠
      (deleteMaxRun unaryMaxComparator [2, 7, 7, 4]).2 .comparisonWork := by
  rw [first_repeated_maximum, unary_duplicate_queue]
  decide

theorem unary_price_is_explicit :
    price unaryPrices (deleteMaxRun unaryMaxComparator [2, 7, 7, 4]).2 = 24 := by
  rw [unary_duplicate_queue]
  rfl

theorem equal_large_keys_have_unbounded_work (budget : Nat) :
    ∃ queue : List Nat, queue.length = 2 ∧
      budget < (deleteMaxRun unaryMaxComparator queue).2 .comparisonWork :=
  unary_fixed_length_unbounded budget

theorem bounded_keys_pay_per_actual_comparison :
    (deleteMaxRun unaryMaxComparator [2, 7, 7, 4]).2 .comparisonWork ≤ 8 * (4 - 1) :=
  deleteMaxRun_unary_work_le [2, 7, 7, 4] 7 (by decide)

theorem unit_delete_family_linear :
    Asymptotics.IsBigO Filter.atTop
      (fun n => (price unitPrices (deleteMaxRun maxUnit (List.replicate n 7)).2 : ℝ))
      (fun n => ((n + 1 : Nat) : ℝ)) := by
  apply deleteMaxRun_price_isBigO unitPrices maxUnit _ 1
  · intro n
    simp
  · intro _ _ _ _ _
    exact Nat.le_refl 1

theorem unit_selection_family_linear :
    Asymptotics.IsBigO Filter.atTop
      (fun n => (price unitPrices (selectRun maxUnit 7 (List.replicate n 7)).2 : ℝ))
      (fun n => ((n + 1 : Nat) : ℝ)) := by
  apply selectRun_price_isBigO unitPrices maxUnit (fun _ => 7) (fun n => List.replicate n 7) 1
  · intro n
    simp
  · intro _ _ _ _ _
    exact Nat.le_refl 1

theorem unary_bounded_family_linear (M : Nat) :
    Asymptotics.IsBigO Filter.atTop
      (fun n => (price unaryPrices (deleteMaxRun unaryMaxComparator (List.replicate n M)).2 : ℝ))
      (fun n => ((n + 1 : Nat) : ℝ)) := by
  apply deleteMaxRun_price_isBigO unaryPrices unaryMaxComparator _ (M + 1)
  · intro n
    simp
  · intro n candidate _candidate_mem head head_mem
    have equal : head = M := (List.mem_replicate.mp head_mem).2
    rw [unaryMaxComparator_work, equal]
    exact Nat.add_le_add_right (Nat.min_le_left M candidate) 1

theorem merge_family_linear_despite_large_right :
    Asymptotics.IsBigO Filter.atTop
      (fun n => (price unitPrices (mergeRun (List.replicate n 1) (List.replicate (n * n) 7)).2 : ℝ))
      (fun n => ((n + 1 : Nat) : ℝ)) :=
  mergeRun_price_isBigO unitPrices (fun n => List.replicate n 1)
    (fun n => List.replicate (n * n) 7) (fun _ => by simp)

end Examples.ListPriorityQueueWork
