import Applications.Search.ListMaximumQueue

/-!
Source-connected list maximum queue cases. Exact outputs distinguish the
comparison-first source recurrence from other occurrence-correct selectors.
Identity abstraction remains stronger than permutation of the observed entries.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.ListMaximumQueues

universe u

open Search.ListMaximumQueue
open Applications.Sorting

theorem empty_and_zero : deleteMax [] = none ∧ deleteMax [0] = some (0, []) :=
  ⟨deleteMax_nil, rfl⟩

theorem both_comparison_branches :
    selectMax 5 [2, 4] = (5, [2, 4]) ∧ selectMax 2 [5, 4] = (5, [2, 4]) := by
  constructor <;> rw [selectMax_cons] <;> rfl

theorem equal_keys_take_keep_branch : selectMax 7 [7, 4] = (7, [7, 4]) := by
  rw [selectMax_cons]
  rfl

/-- Distinct payloads make the same generic selector's tie choice observable. -/
theorem tagged_tie_retains_seed :
    SourceSelection.select (fun candidate head : Nat × Bool => head.1 ≤ candidate.1)
      (7, false) [(7, true)] = ((7, false), [(7, true)]) := rfl

theorem exact_remainder : selectMax 2 [1, 3] = (3, [1, 2]) := rfl

theorem delete_exact_remainder : deleteMax [3, 1, 2] = some (3, [1, 2]) := rfl

theorem source_exercise_connection :
    ([2, 1, 3] : List Nat).Perm [3, 1, 2] ∧
      List.Forall (fun key => key ≤ 3) [1, 2] ∧ 2 ≤ 3 := by
  have upper := select_biggest 2 [1, 3] 3 [1, 2] exact_remainder
  refine ⟨?_, upper, select_biggest_aux 2 [1, 3] 3 [1, 2] upper exact_remainder⟩
  simpa only [exact_remainder] using select_perm 2 [1, 3]

theorem selected_original_membership_and_bound :
    3 ∈ ([2, 1, 3] : List Nat) ∧ ∀ key ∈ ([2, 1, 3] : List Nat), key ≤ 3 := by
  constructor
  · simpa only [exact_remainder] using select_mem 2 [1, 3]
  · simpa only [exact_remainder] using select_maximum 2 [1, 3]

theorem dual_order_same_recursion :
    selectMax 2 [1, 3] =
        SourceSelection.select (α := OrderDual Nat) (· ≤ ·) (2 : Nat) ([1, 3] : List Nat) ∧
      selectMax 2 [1, 3] = (3, [1, 2]) :=
  ⟨selectMax_eq_dual 2 [1, 3], exact_remainder⟩

theorem repeated_maxima_twice :
    deleteMax [2, 7, 7, 4] = some (7, [2, 7, 4]) ∧
      deleteMax [2, 7, 4] = some (7, [2, 4]) := ⟨rfl, rfl⟩

theorem duplicate_delete_source_law :
    ([2, 7, 7, 4] : List Nat).Perm [7, 2, 7, 4] ∧
      ∀ key ∈ ([2, 7, 4] : List Nat), key ≤ 7 :=
  deleteMax_relate [2, 7, 7, 4] [2, 7, 4] 7 [2, 7, 7, 4] [2, 7, 4]
    (valid _) (abs_intro _) repeated_maxima_twice.1 (abs_intro _)

theorem duplicate_merge_and_delete :
    merge [7, 2, 7] [7, 0] = [7, 2, 7, 7, 0] ∧
      (merge [7, 2, 7] [7, 0]).count 7 = 3 ∧
      deleteMax (merge [7, 2, 7] [7, 0]) = some (7, [2, 7, 7, 0]) :=
  ⟨rfl, rfl, rfl⟩

theorem duplicate_merge_source_law :
    ([7, 2, 7, 7, 0] : List Nat).Perm ([7, 2, 7] ++ [7, 0]) :=
  merge_relate [7, 2, 7] [7, 0] [7, 2, 7] [7, 0] [7, 2, 7, 7, 0]
    (valid _) (valid _) (abs_intro _) (abs_intro _) (abs_intro _)

theorem identity_is_stronger_than_permutation :
    ([1, 2] : List Nat).Perm [2, 1] ∧ ¬ Abs [1, 2] [2, 1] ∧
      Sequences.Multiplicity.contents ([1, 2] : List Nat) =
        Sequences.Multiplicity.contents [2, 1] := by
  have reordered : ([1, 2] : List Nat).Perm [2, 1] := by decide
  exact ⟨reordered, by change ([1, 2] : List Nat) ≠ [2, 1]; decide,
    Sequences.Multiplicity.perm_contents reordered⟩

theorem native_merge_order_and_occurrences :
    merge [1, 1] [2] ≠ merge [2] [1, 1] ∧
      (merge [1, 1] [2]).Perm (merge [2] [1, 1]) :=
  ⟨by decide, List.perm_append_comm⟩

theorem absent_iff_empty (queue : Queue) : deleteMax queue = none ↔ queue = [] :=
  (deleteMax_none queue (valid queue)).symm

theorem every_raw_list_has_its_identity_witness (queue : Queue) :
    Valid queue ∧ Abs queue queue ∧ ∃ meaning, Abs queue meaning :=
  ⟨valid queue, abs_intro queue, can_relate queue (valid queue)⟩

/-- The occurrence result is reusable even when the relation is not an order. -/
theorem arbitrary_relation_preserves_occurrences {α : Type u} (r : α → α → Prop)
    [DecidableRel r] (seed : α) (tail : List α) :
    (seed :: tail).Perm ((SourceSelection.select r seed tail).1 ::
      (SourceSelection.select r seed tail).2) :=
  (SourceSelection.select_perm r seed tail).symm

theorem equality_relation_has_no_extremum_conclusion :
    ([1, 2] : List Nat).Perm
        ((SourceSelection.select (· = ·) 1 [2]).1 ::
          (SourceSelection.select (· = ·) 1 [2]).2) ∧
      ¬ (∀ key ∈ ([1, 2] : List Nat),
        (SourceSelection.select (· = ·) 1 [2]).1 = key) :=
  ⟨arbitrary_relation_preserves_occurrences (· = ·) 1 [2], by decide⟩

theorem already_maximal_seed_retains_exact_tail (seed : Nat) (tail : List Nat)
    (bounded : ∀ key ∈ tail, key ≤ seed) : selectMax seed tail = (seed, tail) :=
  SourceSelection.select_of_lower (fun candidate head : Nat => head ≤ candidate)
    seed tail bounded

theorem successful_delete_is_an_original_maximum :
    7 ∈ ([2, 7, 7, 4] : List Nat) ∧ ∀ key ∈ ([2, 7, 7, 4] : List Nat), key ≤ 7 :=
  ⟨laws.deleteMax_mem [2, 7, 7, 4] [2, 7, 4] 7 [2, 7, 7, 4]
      (valid _) (abs_intro _) repeated_maxima_twice.1,
    laws.deleteMax_maximum [2, 7, 7, 4] [2, 7, 4] 7 [2, 7, 7, 4]
      (valid _) (abs_intro _) repeated_maxima_twice.1⟩

theorem one_duplicate_and_one_list_entry_removed :
    ([2, 7, 7, 4] : List Nat).count 7 = ([2, 7, 4] : List Nat).count 7 + 1 ∧
      ([2, 7, 4] : List Nat).length + 1 = ([2, 7, 7, 4] : List Nat).length := by
  constructor
  · simpa only [↓reduceIte] using
      laws.deleteMax_count [2, 7, 7, 4] [2, 7, 4] 7 7 [2, 7, 7, 4] [2, 7, 4]
        (valid _) (abs_intro _) repeated_maxima_twice.1 (abs_intro _)
  · exact laws.deleteMax_length [2, 7, 7, 4] [2, 7, 4] 7 [2, 7, 7, 4] [2, 7, 4]
      (valid _) (abs_intro _) repeated_maxima_twice.1 (abs_intro _)

theorem unselected_occurrence_survives :
    ([2, 7, 7, 4] : List Nat).count 2 = ([2, 7, 4] : List Nat).count 2 := by
  exact laws.deleteMax_count [2, 7, 7, 4] [2, 7, 4] 7 2 [2, 7, 7, 4] [2, 7, 4]
    (valid _) (abs_intro _) repeated_maxima_twice.1 (abs_intro _)

theorem merged_every_query_count (query : Nat) :
    (merge [7, 2, 7] [7, 0]).count query =
      ([7, 2, 7] : List Nat).count query + ([7, 0] : List Nat).count query :=
  laws.merge_count [7, 2, 7] [7, 0] [7, 2, 7] [7, 0] (merge [7, 2, 7] [7, 0]) query
    (valid _) (valid _) (abs_intro _) (abs_intro _) (abs_intro _)

theorem literal_successful_delete_Forall :
    ([2, 7, 7, 4] : List Nat).Perm [7, 2, 7, 4] ∧
      List.Forall (fun key => key ≤ 7) [2, 7, 4] :=
  deleteMax_relate_forall [2, 7, 7, 4] [2, 7, 4] 7 [2, 7, 7, 4] [2, 7, 4]
    (valid _) (abs_intro _) repeated_maxima_twice.1 (abs_intro _)

theorem dual_queue_repeated_removals :
    exactQueue.remove [2, 7, 7, 4] = some (Search.MaximumQueue.encode 7, [2, 7, 4]) ∧
      exactQueue.remove [2, 7, 4] = some (Search.MaximumQueue.encode 7, [2, 4]) := by
  constructor
  · rw [exactQueue_remove, repeated_maxima_twice.1]
    rfl
  · rw [exactQueue_remove, repeated_maxima_twice.2]
    rfl

theorem dual_queue_observation_law :
    (([2, 7, 7, 4] : List Nat).map Search.MaximumQueue.encode).Perm
        (Search.MaximumQueue.encode 7 :: ([2, 7, 4] : List Nat).map Search.MaximumQueue.encode) ∧
      ∀ entry ∈ ([2, 7, 7, 4] : List Nat).map Search.MaximumQueue.encode,
        (Search.MaximumQueue.encode 7).2 ≤ entry.2 := by
  have result := exactQueue.remove_spec [2, 7, 7, 4] (Search.MaximumQueue.encode 7)
    [2, 7, 4] (valid [2, 7, 7, 4]) dual_queue_repeated_removals.1
  exact ⟨result.2.1, result.2.2⟩

theorem dual_queue_law_returns_Nat_maximum :
    ∀ key ∈ ([2, 7, 7, 4] : List Nat), key ≤ 7 := by
  intro key member
  exact dual_queue_observation_law.2 (Search.MaximumQueue.encode key)
    (List.mem_map.mpr ⟨key, member, rfl⟩)

theorem dual_queue_source_insertion :
    exactQueue.add [Search.MaximumQueue.encode 7] [2, 7, 4] = [7, 2, 7, 4] ∧
      exactQueue.add (([7, 2, 7] : List Nat).map Search.MaximumQueue.encode) [7, 0] =
        merge [7, 2, 7] [7, 0] :=
  ⟨exactQueue_add_singleton 7 [2, 7, 4], exactQueue_add_keys [7, 2, 7] [7, 0]⟩

theorem native_merge_observation_separate_from_adapter :
    exactQueue.entries (merge [7, 2, 7] [7, 0]) =
      exactQueue.entries [7, 2, 7] ++ exactQueue.entries [7, 0] :=
  exactQueue_native_merge [7, 2, 7] [7, 0]

end Examples.ListMaximumQueues
