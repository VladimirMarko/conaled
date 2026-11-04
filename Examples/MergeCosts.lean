import Applications.Resources.ListMerge
import Applications.Resources.CallComparison
import Applications.Search.LeftistQueue
import Examples.StableSorting
import Mathlib.Data.Multiset.AddSub

/-!
# Connected ordinary merge observations

The independent examples distinguish comparisons from invocations, preserve
ordered duplicate occurrences, and sequence a second merge on the first actual
returned list. Source/key order assumptions belong only to their semantic
claims. The raw queue client counts one merge in the existing node body, not
the child enumerations or a whole tree traversal.
Source, scope and statement assessment: docs/research/fdsa-list-merge.md.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.MergeCosts
open Applications.Sorting
open _root_.Resources.ListMerge

universe u v
variable {α : Type u} {κ : Type v}

def natCompare (a b : Nat) : Bool := decide (a ≤ b)

def byKey [LE κ] [DecidableLE κ] (key : α → κ) (a b : α) : Bool :=
  decide (key a ≤ key b)

/-- Ordinary occurrence preservation is transported through actual value erasure. -/
theorem result_perm (cmp : α → α → Bool) (xs ys : List α) :
    (run cmp xs ys).1.Perm (xs ++ ys) := by
  rw [run_value]
  exact List.merge_perm_append cmp

theorem result_length (cmp : α → α → Bool) (xs ys : List α) :
    (run cmp xs ys).1.length = xs.length + ys.length :=
  (congrArg List.length (run_value cmp xs ys)).trans (List.length_merge cmp xs ys)

theorem result_multiset (cmp : α → α → Bool) (xs ys : List α) :
    ((run cmp xs ys).1 : Multiset α) = (xs : Multiset α) + (ys : Multiset α) := by
  calc
    ((run cmp xs ys).1 : Multiset α) = ((xs ++ ys : List α) : Multiset α) :=
      Multiset.coe_eq_coe.mpr (result_perm cmp xs ys)
    _ = _ := (Multiset.coe_add xs ys).symm

theorem result_mem (cmp : α → α → Bool) (xs ys : List α) (a : α) :
    a ∈ (run cmp xs ys).1 ↔ a ∈ xs ∨ a ∈ ys := by
  rw [run_value]
  exact List.mem_merge

theorem empty_sides (cmp : α → α → Bool) (xs ys : List α) :
    run cmp [] ys = (ys, (0, 1)) ∧ run cmp xs [] = (xs, (0, 1)) :=
  ⟨run_nil_left cmp ys, run_nil_right cmp xs⟩

theorem empty_payload (cmp : Empty → Empty → Bool) (xs ys : List Empty) :
    run cmp xs ys = ([], (0, 1)) := by
  cases xs with
  | nil =>
      cases ys with
      | nil => exact run_nil_left cmp []
      | cons y _ => exact Empty.elim y
  | cons x _ => exact Empty.elim x

theorem low_singleton : run natCompare [0] [1, 2] = ([0, 1, 2], (1, 2)) := by
  simp [natCompare, run_cons_cons, run_nil_left, Resources.bind]

theorem high_singleton : run natCompare [2] [0, 1] = ([0, 1, 2], (2, 3)) := by
  simp [natCompare, run_cons_cons, run_nil_right, Resources.bind]

/-- The scalar projection uses the existing entry tick on the actual child. -/
theorem low_singleton_entry_model :
    Resources.reweight Prod.snd (run natCompare [0] [1, 2]) = ([0, 1, 2], 2) := by
  rw [run_entries_cons_cons]
  simp [natCompare, run_nil_left, Resources.reweight, Resources.bind,
    Resources.pure, Resources.CallCount.tick]

theorem interleaving :
    run natCompare [0, 2, 2] [1, 2, 3] = ([0, 1, 2, 2, 2, 3], (4, 5)) := by
  simp [natCompare, run_cons_cons, run_nil_left, Resources.bind]

/-- All three copies of 2 remain, alongside the general multiset and support laws. -/
theorem interleaving_observations :
    let output := (run natCompare [0, 2, 2] [1, 2, 3]).1
    output.length = 6 ∧
      (output : Multiset Nat) = (([0, 2, 2] : List Nat) : Multiset Nat) +
        (([1, 2, 3] : List Nat) : Multiset Nat) ∧
      (2 ∈ output ↔ 2 ∈ ([0, 2, 2] : List Nat) ∨ 2 ∈ ([1, 2, 3] : List Nat)) ∧
      output.count 2 = 3 := by
  dsimp only
  refine ⟨result_length natCompare _ _, result_multiset natCompare _ _,
    result_mem natCompare _ _ 2, ?_⟩
  exact (congrArg (fun r : List Nat × (Nat × Nat) => r.1.count 2) interleaving).trans
    (by decide)

theorem always_true (a b c : α) :
    run (fun _ _ => true) [a, b] [c] = ([a, b, c], (2, 3)) := by
  simp [run_cons_cons, run_nil_left, Resources.bind]

theorem always_false (a b c : α) :
    run (fun _ _ => false) [a, b] [c] = ([c, a, b], (1, 2)) := by
  simp [run_cons_cons, run_nil_right, Resources.bind]

theorem tied_runs :
    run natCompare [1, 1] [1] = ([1, 1, 1], (2, 3)) ∧
      run natCompare [1] [1, 1] = ([1, 1, 1], (1, 2)) := by
  constructor <;> simp [natCompare, run_cons_cons, run_nil_left, Resources.bind]

/-- Equal values, lengths and contents do not identify either observation. -/
theorem ties_do_not_determine_cost :
    (run natCompare [1, 1] [1]).1 = (run natCompare [1] [1, 1]).1 ∧
      (run natCompare [1, 1] [1]).1.length = (run natCompare [1] [1, 1]).1.length ∧
      (run natCompare [1, 1] [1]).1.Perm (run natCompare [1] [1, 1]).1 ∧
      (run natCompare [1, 1] [1]).2.1 ≠ (run natCompare [1] [1, 1]).2.1 ∧
      (run natCompare [1, 1] [1]).2.2 ≠ (run natCompare [1] [1, 1]).2.2 := by
  rw [tied_runs.1, tied_runs.2]
  exact ⟨rfl, rfl, List.Perm.refl _, by decide, by decide⟩

theorem unsorted_run :
    run natCompare [3, 1] [2, 1] = ([2, 1, 3, 1], (2, 3)) := by
  simp [natCompare, run_cons_cons, run_nil_right, Resources.bind]

theorem unsorted_cost_bounds :
    comparisons natCompare [3, 1] [2, 1] ≤ 4 ∧ entries natCompare [3, 1] [2, 1] ≤ 5 :=
  ⟨comparisons_le natCompare _ _, entries_le natCompare _ _⟩

theorem unsorted_inputs_retained (cmp : Nat → Nat → Bool) :
    List.Sublist [3, 1] (run cmp [3, 1] [2, 1]).1 ∧
      List.Sublist [2, 1] (run cmp [3, 1] [2, 1]).1 := by
  constructor
  · rw [run_value]
    exact sublist_merge_left cmp _ _
  · rw [run_value]
    exact sublist_merge_right cmp _ _

/-- No comparator can remove the out-of-order pair retained from the left input. -/
theorem unsorted_for_every_comparator (cmp : Nat → Nat → Bool) :
    ¬ (run cmp [3, 1] [2, 1]).1.Pairwise (fun a b => a ≤ b) := by
  intro sorted
  rw [run_value] at sorted
  have left := (pairwise_of_merge cmp [3, 1] [2, 1] sorted).1
  exact (by decide : ¬ ([3, 1] : List Nat).Pairwise (fun a b => a ≤ b)) left

theorem source_value [LE α] [DecidableLE α] (xs ys : List α) :
    (run (fun a b => decide (a ≤ b)) xs ys).1 = sourceMerge xs ys :=
  (run_value _ xs ys).trans (sourceMerge_eq_merge xs ys).symm

theorem key_value [LE κ] [DecidableLE κ] (key : α → κ) (xs ys : List α) :
    (run (byKey key) xs ys).1 = mergeBy key xs ys := run_value _ xs ys

/-- The source adapter pulls back key order without ordering payload records globally. -/
theorem key_source_value [LE κ] [DecidableLE κ] (key : α → κ) (xs ys : List α) :
    letI : LE α := ⟨fun a b => key a ≤ key b⟩
    letI : DecidableLE α := fun a b => inferInstanceAs (Decidable (key a ≤ key b))
    (run (byKey key) xs ys).1 = sourceMerge xs ys := by
  let : LE α := ⟨fun a b => key a ≤ key b⟩
  let : DecidableLE α := fun a b => inferInstanceAs (Decidable (key a ≤ key b))
  exact (key_value key xs ys).trans (mergeBy_source key xs ys).symm

theorem key_sorted_iff [LE κ] [DecidableLE κ] [Std.IsLinearPreorder κ]
    (key : α → κ) (xs ys : List α) :
    KeySorted key (run (byKey key) xs ys).1 ↔ KeySorted key xs ∧ KeySorted key ys := by
  rw [run_value]
  apply merge_sorted_compatible_on_iff key (byKey key) xs ys
  intro a _ b _
  exact ⟨of_decide_eq_true, fun h =>
    (Std.le_total (a := key a) (b := key b)).resolve_left (of_decide_eq_false h)⟩

theorem source_key_sorted_iff [LE κ] [DecidableLE κ] [Std.IsLinearPreorder κ]
    (key : α → κ) (xs ys : List α) :
    letI : LE α := ⟨fun a b => key a ≤ key b⟩
    letI : DecidableLE α := fun a b => inferInstanceAs (Decidable (key a ≤ key b))
    KeySorted key (sourceMerge xs ys) ↔ KeySorted key xs ∧ KeySorted key ys := by
  let : LE α := ⟨fun a b => key a ≤ key b⟩
  let : DecidableLE α := fun a b => inferInstanceAs (Decidable (key a ≤ key b))
  rw [← key_source_value key xs ys]
  exact key_sorted_iff key xs ys

theorem measured_key_spec [LE κ] [DecidableLE κ] [Std.IsLinearPreorder κ] [DecidableEq κ]
    (key : α → κ) (xs ys : List α) (hx : KeySorted key xs) (hy : KeySorted key ys) :
    StableSort key (xs ++ ys) (run (byKey key) xs ys).1 := by
  rw [key_value]
  exact mergeBy_spec key xs ys hx hy

def recordsLeft : List Examples.StableSorting.Record := [(2, "first")]
def recordsRight : List Examples.StableSorting.Record := [(-1, "negative"), (2, "last")]

theorem records_value :
    (run (byKey Prod.fst) recordsLeft recordsRight).1 = Examples.StableSorting.expected :=
  (measured_key_spec Prod.fst recordsLeft recordsRight (by decide) (by decide)).unique
    Examples.StableSorting.expected_spec

/-- The public comparison recurrence counts the negative step and the subsequent left tie. -/
theorem records_counts : (run (byKey Prod.fst) recordsLeft recordsRight).2 = (2, 3) := by
  have counted : comparisons (byKey Prod.fst) recordsLeft recordsRight = 2 := by
    simp [recordsLeft, recordsRight, byKey, comparisons_cons_cons, comparisons_nil_left]
  exact Prod.ext counted
    ((entries_eq_comparisons_add_one _ recordsLeft recordsRight).trans
      (congrArg (fun n : Nat => n + 1) counted))

theorem records_exact :
    run (byKey Prod.fst) recordsLeft recordsRight = (Examples.StableSorting.expected, (2, 3)) :=
  Prod.ext records_value records_counts

def taggedLeft (a b : α) : List (Nat × α) := [(1, a), (1, b)]
def taggedRight (c : α) : List (Nat × α) := [(1, c)]

/-- Key erasure is noninjective, yet the actual branch observations are preserved. -/
theorem tagged_key_transport (a b c : α) :
    run natCompare [1, 1] [1] =
        ((run (byKey Prod.fst) (taggedLeft a b) (taggedRight c)).1.map Prod.fst,
          (run (byKey Prod.fst) (taggedLeft a b) (taggedRight c)).2) ∧
      run natCompare [1] [1, 1] =
        ((run (byKey Prod.fst) (taggedRight c) (taggedLeft a b)).1.map Prod.fst,
          (run (byKey Prod.fst) (taggedRight c) (taggedLeft a b)).2) :=
  ⟨run_map (byKey Prod.fst) natCompare Prod.fst (taggedLeft a b) (taggedRight c)
      (fun _ _ _ _ => rfl),
    run_map (byKey Prod.fst) natCompare Prod.fst (taggedRight c) (taggedLeft a b)
      (fun _ _ _ _ => rfl)⟩

theorem tagged_counts (a b c : α) :
    (run (byKey Prod.fst) (taggedLeft a b) (taggedRight c)).2 = (2, 3) ∧
      (run (byKey Prod.fst) (taggedRight c) (taggedLeft a b)).2 = (1, 2) :=
  ⟨(congrArg Prod.snd (tagged_key_transport a b c).1).symm.trans
      (congrArg Prod.snd tied_runs.1),
    (congrArg Prod.snd (tagged_key_transport a b c).2).symm.trans
      (congrArg Prod.snd tied_runs.2)⟩

theorem tagged_values (a b c : α) :
    (run (byKey Prod.fst) (taggedLeft a b) (taggedRight c)).1 = [(1, a), (1, b), (1, c)] ∧
      (run (byKey Prod.fst) (taggedRight c) (taggedLeft a b)).1 = [(1, c), (1, a), (1, b)] := by
  constructor <;> rw [key_value] <;> simp [mergeBy, taggedLeft, taggedRight]

theorem tagged_exact (a b c : α) :
    run (byKey Prod.fst) (taggedLeft a b) (taggedRight c) =
        ([(1, a), (1, b), (1, c)], (2, 3)) ∧
      run (byKey Prod.fst) (taggedRight c) (taggedLeft a b) =
        ([(1, c), (1, a), (1, b)], (1, 2)) :=
  ⟨Prod.ext (tagged_values a b c).1 (tagged_counts a b c).1,
    Prod.ext (tagged_values a b c).2 (tagged_counts a b c).2⟩

theorem tagged_stable (a b c : α) :
    StableSort Prod.fst (taggedLeft a b ++ taggedRight c)
      (run (byKey Prod.fst) (taggedLeft a b) (taggedRight c)).1 :=
  measured_key_spec Prod.fst _ _
    (by simp [KeySorted, taggedLeft]) (by simp [KeySorted, taggedRight])

def falseLeft : List (Nat × String) := [(1, "A"), (1, "B")]
def falseRight : List (Nat × String) := [(1, "C")]

theorem false_compare_compatible :
    ∀ a ∈ falseLeft, ∀ b ∈ falseRight,
      (false = true → a.1 ≤ b.1) ∧ (false = false → b.1 ≤ a.1) := by
  intro a ha b hb
  simp only [falseLeft, falseRight, List.mem_cons, List.not_mem_nil, or_false] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl <;> decide

theorem false_record_run :
    run (fun _ _ => false) falseLeft falseRight =
      ([(1, "C"), (1, "A"), (1, "B")], (1, 2)) :=
  always_false (1, "A") (1, "B") (1, "C")

/-- Actual compatible sorted output and permutation still do not imply stable tags. -/
theorem compatible_not_stable :
    KeySorted Prod.fst (run (fun _ _ => false) falseLeft falseRight).1 ∧
      (run (fun _ _ => false) falseLeft falseRight).1.Perm (falseLeft ++ falseRight) ∧
      ¬ Stable Prod.fst (falseLeft ++ falseRight)
        (run (fun _ _ => false) falseLeft falseRight).1 := by
  refine ⟨?_, result_perm _ _ _, ?_⟩
  · rw [run_value]
    exact merge_sorted_compatible_on Prod.fst _ falseLeft falseRight
      false_compare_compatible (by decide) (by decide)
  · intro stable
    have wrong := stable 1
    rw [false_record_run] at wrong
    simp [falseLeft, falseRight] at wrong

def unsortedRecordsLeft : List (Nat × String) := [(3, "A"), (1, "B")]
def unsortedRecordsRight : List (Nat × String) := [(2, "C"), (1, "D")]

theorem unsorted_records_run :
    run (byKey Prod.fst) unsortedRecordsLeft unsortedRecordsRight =
      ([(2, "C"), (1, "D"), (3, "A"), (1, "B")], (2, 3)) := by
  simp [unsortedRecordsLeft, unsortedRecordsRight, byKey,
    run_cons_cons, run_nil_right, Resources.bind]

/-- Sorted blocks are a genuine premise even for the left-on-equality comparator. -/
theorem unsorted_record_filters :
    (run (byKey Prod.fst) unsortedRecordsLeft unsortedRecordsRight).1.filter
        (fun a => decide (a.1 = 1)) = [(1, "D"), (1, "B")] ∧
      (unsortedRecordsLeft ++ unsortedRecordsRight).filter (fun a => decide (a.1 = 1)) =
        [(1, "B"), (1, "D")] ∧
      ¬ Stable Prod.fst (unsortedRecordsLeft ++ unsortedRecordsRight)
        (run (byKey Prod.fst) unsortedRecordsLeft unsortedRecordsRight).1 := by
  refine ⟨?_, by decide, ?_⟩
  · rw [unsorted_records_run]
    decide
  · intro stable
    have wrong := stable 1
    rw [unsorted_records_run] at wrong
    simp [unsortedRecordsLeft, unsortedRecordsRight] at wrong

/-- The second merge receives the actual list produced by the first execution. -/
def twoStage (cmp : α → α → Bool) (xs ys zs : List α) :
    Resources.Measured (List α) (Nat × Nat) :=
  Resources.bind (run cmp xs ys) (fun first => run cmp zs first)

theorem twoStage_value (cmp : α → α → Bool) (xs ys zs : List α) :
    (twoStage cmp xs ys zs).1 = List.merge zs (List.merge xs ys cmp) cmp := by
  unfold twoStage
  rw [Resources.bind_value, run_value, run_value]

theorem twoStage_observation (cmp : α → α → Bool) (xs ys zs : List α) :
    (twoStage cmp xs ys zs).2 =
      (comparisons cmp xs ys + comparisons cmp zs (run cmp xs ys).1,
        entries cmp xs ys + entries cmp zs (run cmp xs ys).1) :=
  congrArg Prod.snd
    (Resources.CallCount.let_rule (run cmp xs ys) (fun first => run cmp zs first))

/-- Each of the two actual executions contributes its own terminal invocation. -/
theorem twoStage_entries (cmp : α → α → Bool) (xs ys zs : List α) :
    (twoStage cmp xs ys zs).2.2 = (twoStage cmp xs ys zs).2.1 + 2 := by
  simp only [twoStage_observation, entries_eq_comparisons_add_one]
  omega

theorem twoStage_bounds (cmp : α → α → Bool) (xs ys zs : List α) :
    (twoStage cmp xs ys zs).2.1 ≤ 2 * (xs.length + ys.length) + zs.length ∧
      (twoStage cmp xs ys zs).2.2 ≤ 2 * (xs.length + ys.length) + zs.length + 2 := by
  have first := comparisons_le cmp xs ys
  have second := comparisons_le cmp zs (run cmp xs ys).1
  have actualLength := result_length cmp xs ys
  rw [actualLength] at second
  have upper : (twoStage cmp xs ys zs).2.1 ≤ 2 * (xs.length + ys.length) + zs.length := by
    rw [twoStage_observation]
    omega
  have entryRelation := twoStage_entries cmp xs ys zs
  exact ⟨upper, by omega⟩

/-- Existing additive projection commutes with this actual value-dependent bind. -/
theorem twoStage_comparisons_projection (cmp : α → α → Bool) (xs ys zs : List α) :
    Resources.reweight (AddMonoidHom.fst Nat Nat) (twoStage cmp xs ys zs) =
      Resources.bind (Resources.reweight (AddMonoidHom.fst Nat Nat) (run cmp xs ys))
        (fun first => Resources.reweight (AddMonoidHom.fst Nat Nat) (run cmp zs first)) :=
  Resources.reweight_bind (AddMonoidHom.fst Nat Nat)
    (run cmp xs ys) (fun first => run cmp zs first)

theorem twoStage_entries_projection (cmp : α → α → Bool) (xs ys zs : List α) :
    Resources.reweight (AddMonoidHom.snd Nat Nat) (twoStage cmp xs ys zs) =
      Resources.bind (Resources.reweight (AddMonoidHom.snd Nat Nat) (run cmp xs ys))
        (fun first => Resources.reweight (AddMonoidHom.snd Nat Nat) (run cmp zs first)) :=
  Resources.reweight_bind (AddMonoidHom.snd Nat Nat)
    (run cmp xs ys) (fun first => run cmp zs first)

theorem first_stage : run natCompare [2] [0] = ([0, 2], (1, 2)) := by
  simp [natCompare, run_cons_cons, run_nil_right, Resources.bind]

theorem second_stage : run natCompare [1] [0, 2] = ([0, 1, 2], (2, 3)) := by
  simp [natCompare, run_cons_cons, run_nil_left, Resources.bind]

theorem twoStage_example : twoStage natCompare [2] [0] [1] = ([0, 1, 2], (3, 5)) := by
  rw [twoStage, Resources.CallCount.let_rule, first_stage, second_stage]
  rfl

/-- Substituting the original concatenation changes both value and subsequent work. -/
theorem substituted_input_example :
    Resources.bind (run natCompare [2] [0]) (fun _ => run natCompare [1] [2, 0]) =
      ([1, 2, 0], (2, 4)) := by
  have second : run natCompare [1] [2, 0] = ([1, 2, 0], (1, 2)) := by
    simp [natCompare, run_cons_cons, run_nil_left, Resources.bind]
  rw [Resources.CallCount.let_rule, first_stage, second]
  rfl

theorem actual_input_matters :
    (twoStage natCompare [2] [0] [1]).1 ≠
        (Resources.bind (run natCompare [2] [0]) (fun _ => run natCompare [1] [2, 0])).1 ∧
      (twoStage natCompare [2] [0] [1]).2 ≠
        (Resources.bind (run natCompare [2] [0]) (fun _ => run natCompare [1] [2, 0])).2 := by
  rw [twoStage_example, substituted_input_example]
  decide

/-- Only the merge of the already obtained child enumerations is observed here. -/
def queueBody [LE κ] [DecidableLE κ] (x : α) (p : κ)
    (l r : Search.LeftistQueue.PQ α κ) : Resources.Measured (List (α × κ)) (Nat × Nat) :=
  Resources.bind
    (run (byKey Prod.snd) (Search.LeftistQueue.toListQ l) (Search.LeftistQueue.toListQ r))
    (fun zs => Resources.pure ((x, p) :: zs))

theorem queueBody_value [LE κ] [DecidableLE κ] (k : Nat) (x : α) (p : κ)
    (l r : Search.LeftistQueue.PQ α κ) :
    (queueBody x p l r).1 = Search.LeftistQueue.toListQ (.fork k x p l r) := by
  calc
    (queueBody x p l r).1 =
        (x, p) :: (run (byKey Prod.snd)
          (Search.LeftistQueue.toListQ l) (Search.LeftistQueue.toListQ r)).1 :=
      congrArg Prod.fst (Resources.CallCount.primitive_rule (fun zs => (x, p) :: zs)
        (run (byKey Prod.snd) (Search.LeftistQueue.toListQ l) (Search.LeftistQueue.toListQ r)))
    _ = (x, p) :: List.merge (Search.LeftistQueue.toListQ l)
        (Search.LeftistQueue.toListQ r) (byKey Prod.snd) :=
      congrArg (List.cons (x, p)) (run_value _ _ _)
    _ = Search.LeftistQueue.toListQ (.fork k x p l r) := rfl

theorem queueBody_observation [LE κ] [DecidableLE κ] (x : α) (p : κ)
    (l r : Search.LeftistQueue.PQ α κ) :
    (queueBody x p l r).2 =
      (comparisons (byKey Prod.snd) (Search.LeftistQueue.toListQ l) (Search.LeftistQueue.toListQ r),
        entries (byKey Prod.snd) (Search.LeftistQueue.toListQ l) (Search.LeftistQueue.toListQ r)) := by
  have h := Resources.CallCount.primitive_rule (fun zs => (x, p) :: zs)
    (run (byKey Prod.snd) (Search.LeftistQueue.toListQ l) (Search.LeftistQueue.toListQ r))
  simpa only [queueBody, comparisons, entries] using congrArg Prod.snd h

/-- Raw content preservation supplies child lengths without heap or rank invariants. -/
theorem queueBody_bounds [LE κ] [DecidableLE κ] (x : α) (p : κ)
    (l r : Search.LeftistQueue.PQ α κ) :
    (queueBody x p l r).2.1 ≤ Search.LeftistQueue.size l + Search.LeftistQueue.size r ∧
      (queueBody x p l r).2.2 ≤ Search.LeftistQueue.size l + Search.LeftistQueue.size r + 1 := by
  have leftLength : (Search.LeftistQueue.toListQ l).length = Search.LeftistQueue.size l :=
    (Search.LeftistQueue.toListQ_perm l).length_eq.trans (Search.LeftistQueue.entries_length l)
  have rightLength : (Search.LeftistQueue.toListQ r).length = Search.LeftistQueue.size r :=
    (Search.LeftistQueue.toListQ_perm r).length_eq.trans (Search.LeftistQueue.entries_length r)
  constructor
  · calc
      (queueBody x p l r).2.1 = comparisons (byKey Prod.snd)
          (Search.LeftistQueue.toListQ l) (Search.LeftistQueue.toListQ r) :=
        congrArg Prod.fst (queueBody_observation x p l r)
      _ ≤ (Search.LeftistQueue.toListQ l).length + (Search.LeftistQueue.toListQ r).length :=
        comparisons_le _ _ _
      _ = Search.LeftistQueue.size l + Search.LeftistQueue.size r :=
        congrArg₂ Nat.add leftLength rightLength
  · calc
      (queueBody x p l r).2.2 = entries (byKey Prod.snd)
          (Search.LeftistQueue.toListQ l) (Search.LeftistQueue.toListQ r) :=
        congrArg Prod.snd (queueBody_observation x p l r)
      _ ≤ (Search.LeftistQueue.toListQ l).length + (Search.LeftistQueue.toListQ r).length + 1 :=
        entries_le _ _ _
      _ = Search.LeftistQueue.size l + Search.LeftistQueue.size r + 1 :=
        congrArg (fun n : Nat => n + 1) (congrArg₂ Nat.add leftLength rightLength)

def rawLeft : Search.LeftistQueue.PQ Unit Nat := .fork 0 () 1 .null .null
def rawRight : Search.LeftistQueue.PQ Unit Nat := .fork 0 () 2 .null .null
def rawRoot : Search.LeftistQueue.PQ Unit Nat := .fork 99 () 9 rawLeft rawRight

theorem raw_queue_body :
    queueBody () 9 rawLeft rawRight = ([((), 9), ((), 1), ((), 2)], (1, 2)) := by
  simp [queueBody, rawLeft, rawRight, Search.LeftistQueue.toListQ,
    Search.LeftistQueue.mergeOn, byKey, run_cons_cons, run_nil_left,
    Resources.bind, Resources.pure]

theorem raw_queue_erasure_and_order :
    (queueBody () 9 rawLeft rawRight).1 = Search.LeftistQueue.toListQ rawRoot ∧
      ¬ (queueBody () 9 rawLeft rawRight).1.Pairwise (fun a b => a.2 ≤ b.2) := by
  refine ⟨queueBody_value 99 () 9 rawLeft rawRight, ?_⟩
  rw [raw_queue_body]
  decide

/-- The existing C1 comparison applies because both nonempty inputs force a comparison. -/
theorem nonempty_tariffs (cmp : α → α → Bool) (x y : α) (xs ys : List α) :
    comparisons cmp (x :: xs) (y :: ys) ≤ entries cmp (x :: xs) (y :: ys) ∧
      entries cmp (x :: xs) (y :: ys) ≤ 2 * comparisons cmp (x :: xs) (y :: ys) := by
  rw [entries_eq_comparisons_add_one]
  exact ⟨Resources.CallCount.cost_le_add_entry _,
    Resources.CallCount.add_entry_le _ (comparisons_cons_pos cmp x y xs ys)⟩

theorem empty_tariff_not_multiplicative (cmp : α → α → Bool) (ys : List α) (K : Nat) :
    ¬ entries cmp [] ys ≤ K * comparisons cmp [] ys := by
  rw [entries_nil_left, comparisons_nil_left]
  exact Resources.CallCount.zero_cost_entry_matters K

theorem low_singleton_attains_factor_two :
    (run natCompare [0] [1, 2]).2.1 = 1 ∧ (run natCompare [0] [1, 2]).2.2 = 2 ∧
      (run natCompare [0] [1, 2]).2.2 = 2 * (run natCompare [0] [1, 2]).2.1 := by
  rw [low_singleton]
  decide

end Examples.MergeCosts
