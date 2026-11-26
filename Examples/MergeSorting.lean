import Applications.Sorting.SourceMergeSort
import Applications.Sorting.Alternating
import Applications.Resources.SourceMergeSort
import Examples.SelectionSorting

/-!
VFA 2.1 Merge: all source statements, the actual alternating split and
well-founded whole-sort recurrence, and checked semantic and measured clients.
The source's nested local merge adapts to the existing length-founded primitive.
Its value bridge does not identify execution costs or physical storage.

The key generalization preserves ordering and occurrences but need not preserve
equal-key order, fix key-sorted inputs, or be idempotent. The three-record cycle
below distinguishes these observations from Nat sorting correctness.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.MergeSorting

open Applications.Sorting
universe u v

abbrev split {α : Type u} := SourceMergeSort.split (α := α)
abbrev merge := sourceMerge (α := Nat)
abbrev mergesort := SourceMergeSort.sortOn (α := Nat) id
abbrev Sorted := InsertionSorting.Sorted
abbrev IsSortingAlgorithm := InsertionSorting.IsSortingAlgorithm

/-- The exact source schema, independently of a particular list predicate. -/
def TwoStepListInduction : Prop :=
  ∀ (α : Type u) (P : List α → Prop), P [] → (∀ a, P [a]) →
    (∀ a b xs, P xs → P (a :: b :: xs)) → ∀ xs, P xs

/-- This conditional proof consumes its supplied two-step induction principle. -/
theorem split_len' (IP : TwoStepListInduction.{u}) {α : Type u}
    (l l1 l2 : List α) (h : split l = (l1, l2)) :
    l1.length ≤ l.length ∧ l2.length ≤ l.length := by
  refine IP α (fun xs => ∀ ys zs, split xs = (ys, zs) →
    ys.length ≤ xs.length ∧ zs.length ≤ xs.length) ?_ ?_ ?_ l l1 l2 h
  · intro ys zs he
    have he' : ([], []) = (ys, zs) := he
    rcases Prod.mk.inj he' with ⟨rfl, rfl⟩
    simp
  · intro x ys zs he
    have he' : ([x], []) = (ys, zs) := he
    rcases Prod.mk.inj he' with ⟨rfl, rfl⟩
    simp
  · intro x y xs ih ys zs he
    have he' : (x :: (split xs).1, y :: (split xs).2) = (ys, zs) := he
    rcases Prod.mk.inj he' with ⟨rfl, rfl⟩
    have hb := ih (split xs).1 (split xs).2 rfl
    simp only [List.length_cons]
    omega

/-- The source's explicit recursive proof term is constructive in Lean too. -/
theorem list_ind2 : TwoStepListInduction.{u} := by
  intro α P h0 h1 hs xs
  exact SourceMergeSort.list_induction_two P h0 h1 hs xs

/-- This also covers the true statement of the source's aborted first attempt. -/
theorem split_len {α : Type u} (l l1 l2 : List α) (h : split l = (l1, l2)) :
    l1.length ≤ l.length ∧ l2.length ≤ l.length :=
  split_len' list_ind2 l l1 l2 h

theorem split_perm {α : Type u} (l l1 l2 : List α) (h : split l = (l1, l2)) :
    l.Perm (l1 ++ l2) := by
  have hp := SourceMergeSort.split_perm l
  change l.Perm ((split l).1 ++ (split l).2) at hp
  simpa only [h] using hp

/-- The shared primitive has the source's exact left-tie merge equations. -/
theorem merge_equation (xs ys : List Nat) :
    merge xs ys = List.merge xs ys (fun a b => decide (a ≤ b)) :=
  sourceMerge_eq_merge xs ys

theorem merge2 (x1 x2 : Nat) (r1 r2 : List Nat) (h : x1 ≤ x2) :
    merge (x1 :: r1) (x2 :: r2) = x1 :: merge r1 (x2 :: r2) := by
  simp only [merge, sourceMerge, ite_eq_left h]

theorem merge_right_branch (x1 x2 : Nat) (r1 r2 : List Nat) (h : ¬ x1 ≤ x2) :
    merge (x1 :: r1) (x2 :: r2) = x2 :: merge (x1 :: r1) r2 := by
  simp only [merge, sourceMerge, ite_eq_right h]

theorem merge_nil_l (l : List Nat) : merge [] l = l := by
  rw [merge_equation, List.nil_merge]

theorem merge_nil_r (l : List Nat) : merge l [] = l := by
  rw [merge_equation, List.merge_right]

/-- Public one-level equation for the exact whole source algorithm. -/
theorem mergesort_equation (l : List Nat) :
    mergesort l = match l with
      | [] => []
      | [x] => [x]
      | _ :: _ :: _ => merge (mergesort (split l).1) (mergesort (split l).2) := by
  cases l with
  | nil => exact SourceMergeSort.sortBy_nil _
  | cons x xs =>
      cases xs with
      | nil => exact SourceMergeSort.sortBy_singleton _ x
      | cons y ys =>
          simpa only [mergesort, SourceMergeSort.sortOn, split, merge,
            sourceMerge_eq_merge, id_eq] using
            SourceMergeSort.sortBy_step (fun a b : Nat => decide (a ≤ b))
              (x :: y :: ys) (by simp)

/-- The generated source interface, including its equality and shape premises,
is recovered from the shared input/output induction theorem. -/
theorem mergesort_ind (P : List Nat → List Nat → Prop)
    (h0 : ∀ l : List Nat, l = [] → P [] [])
    (h1 : ∀ (l : List Nat) (x : Nat), l = [x] → P [x] [x])
    (hs : ∀ l xs : List Nat, l = xs →
      (match xs with | _ :: _ :: _ => True | _ => False) →
      ∀ l1 l2 : List Nat, split l = (l1, l2) →
      P l1 (mergesort l1) → P l2 (mergesort l2) →
      P xs (merge (mergesort l1) (mergesort l2)))
    (l : List Nat) : P l (mergesort l) := by
  refine SourceMergeSort.sortBy_induction _ P (h0 [] rfl)
    (fun x => h1 [x] x rfl) ?_ l
  intro xs hlen ih1 ih2
  suffices hout : P xs (merge (mergesort (split xs).1) (mergesort (split xs).2)) by
    simpa only [merge, sourceMerge_eq_merge, mergesort, SourceMergeSort.sortOn,
      split, id_eq] using hout
  apply hs xs xs rfl ?_ (split xs).1 (split xs).2 rfl ih1 ih2
  cases xs with
  | nil => simp at hlen
  | cons x xs =>
      cases xs with
      | nil => simp at hlen
      | cons y ys => trivial

/-- No sortedness of either input is assumed by this source exercise. -/
theorem sorted_merge1 (x x1 : Nat) (l1 : List Nat) (x2 : Nat) (l2 : List Nat)
    (hx1 : x ≤ x1) (hx2 : x ≤ x2)
    (hs : Sorted (merge (x1 :: l1) (x2 :: l2))) :
    Sorted (x :: merge (x1 :: l1) (x2 :: l2)) := by
  by_cases h : x1 ≤ x2
  · rw [merge2 x1 x2 l1 l2 h] at hs ⊢
    exact InsertionSorting.sorted_cons x x1 _ hx1 hs
  · rw [merge_right_branch x1 x2 l1 l2 h] at hs ⊢
    exact InsertionSorting.sorted_cons x x2 _ hx2 hs

theorem sorted_merge (l1 : List Nat) (h1 : Sorted l1)
    (l2 : List Nat) (h2 : Sorted l2) : Sorted (merge l1 l2) := by
  apply List.isChain_iff_pairwise.mpr
  rw [merge_equation]
  exact mergeBy_sorted id l1 l2 (List.isChain_iff_pairwise.mp h1)
    (List.isChain_iff_pairwise.mp h2)

/-- A checked consumer of the source input/output induction interface. -/
theorem mergesort_sorts (l : List Nat) : Sorted (mergesort l) := by
  refine mergesort_ind (fun _ ys => Sorted ys) ?_ ?_ ?_ l
  · intro _ _; exact InsertionSorting.sorted_nil
  · intro _ x _; exact InsertionSorting.sorted_1 x
  · intro _ _ _ _ l1 l2 _ ih1 ih2
    exact sorted_merge (mergesort l1) ih1 (mergesort l2) ih2

theorem merge_perm (l1 l2 : List Nat) : (l1 ++ l2).Perm (merge l1 l2) := by
  rw [merge_equation]
  exact (mergeBy_perm id l1 l2).symm

/-- Both actual split branches preserve multiplicity in the source direction. -/
theorem mergesort_perm (l : List Nat) : l.Perm (mergesort l) := by
  refine mergesort_ind (fun xs ys => xs.Perm ys) ?_ ?_ ?_ l
  · intro _ _; exact List.Perm.refl []
  · intro _ x _; exact List.Perm.refl [x]
  · intro xs ys he _ l1 l2 hsplit ih1 ih2
    subst ys
    exact (split_perm xs l1 l2 hsplit).trans
      ((ih1.append ih2).trans (merge_perm (mergesort l1) (mergesort l2)))

theorem mergesort_correct : IsSortingAlgorithm mergesort :=
  fun l => ⟨mergesort_perm l, mergesort_sorts l⟩

/-! Split distinctions and public-equation clients. -/

theorem split_empty : split ([] : List Nat) = ([], []) := rfl
theorem split_singleton (x : Nat) : split [x] = ([x], []) := rfl
theorem split_even : split [0, 1, 2, 3] = ([0, 2], [1, 3]) := rfl
theorem split_odd : split [0, 1, 2, 3, 4] = ([0, 2, 4], [1, 3]) := rfl

theorem split_odd_contract :
    ([0, 1, 2, 3, 4] : List Nat).Perm ([0, 2, 4] ++ [1, 3]) ∧
      ([0, 2, 4] : List Nat).length = 3 ∧ ([1, 3] : List Nat).length = 2 := by
  refine ⟨split_perm _ _ _ split_odd, ?_⟩
  exact SourceMergeSort.split_lengths ([0, 1, 2, 3, 4] : List Nat)

theorem split_not_reversed_piles :
    split [0, 1, 2, 3, 4] ≠ halve [0, 1, 2, 3, 4] ([], []) := by decide

theorem split_not_contiguous :
    split [0, 1, 2, 3, 4] ≠
      (([0, 1, 2, 3, 4] : List Nat).take 3, ([0, 1, 2, 3, 4] : List Nat).drop 3) := by decide

/-- The reverse-and-append bridge retains both nonempty supplied piles. -/
theorem split_accumulator_bridge :
    halve [0, 1, 2, 3, 4] ([8], [9]) = ([4, 2, 0, 8], [3, 1, 9]) := by
  simpa [SourceMergeSort.split] using
    SourceMergeSort.halve_eq_reverse_split [0, 1, 2, 3, 4] [8] [9]

theorem split_base_not_smaller (x : Nat) :
    ¬ (split ([] : List Nat)).1.length < ([] : List Nat).length ∧
      ¬ (split [x]).1.length < ([x] : List Nat).length := by simp [split]

theorem source_pair {α : Type u} (cmp : α → α → Bool) (x y : α) :
    SourceMergeSort.sortBy cmp [x, y] = List.merge [x] [y] cmp := by
  rw [SourceMergeSort.sortBy_step cmp [x, y] (by simp)]
  simp only [SourceMergeSort.split, SourceMergeSort.sortBy_singleton]

theorem source_three {α : Type u} (cmp : α → α → Bool) (x y z : α) :
    SourceMergeSort.sortBy cmp [x, y, z] = List.merge (List.merge [x] [z] cmp) [y] cmp := by
  rw [SourceMergeSort.sortBy_step cmp [x, y, z] (by simp)]
  simp only [SourceMergeSort.split, source_pair, SourceMergeSort.sortBy_singleton]

theorem mergesort_three : mergesort [3, 1, 2] = [1, 2, 3] := by
  change SourceMergeSort.sortBy (fun a b : Nat => decide (a ≤ b)) [3, 1, 2] = _
  rw [source_three]
  simp

theorem merge_tie (x : Nat) (xs ys : List Nat) :
    merge (x :: xs) (x :: ys) = x :: merge xs (x :: ys) := merge2 x x xs ys le_rfl

theorem comparator_laws_matter :
    ¬ Sorted (SourceMergeSort.sortBy (fun _ _ : Nat => false) [1, 2]) := by
  rw [source_pair]
  simp [Sorted, InsertionSorting.Sorted]

/-! Output uniqueness uses antisymmetry of values, or only of observed keys. -/

theorem agrees_with_insertion (xs : List Nat) : mergesort xs = InsertionSorting.sort xs :=
  sorters_eq_at (· ≤ ·) mergesort InsertionSorting.sort xs
    ⟨List.isChain_iff_pairwise.mp (mergesort_sorts xs), (mergesort_perm xs).symm⟩
    ⟨List.isChain_iff_pairwise.mp (InsertionSorting.sort_sorted xs),
      (InsertionSorting.sort_perm xs).symm⟩

theorem agrees_with_stable_sort (xs : List Nat) : mergesort xs = sortOn id xs :=
  sorters_eq_at (· ≤ ·) mergesort (sortOn id) xs
    ⟨List.isChain_iff_pairwise.mp (mergesort_sorts xs), (mergesort_perm xs).symm⟩
    (sortOn_correct id xs)

theorem agrees_with_selection (xs : List Nat) :
    mergesort xs = SelectionSorting.selectionSort xs :=
  (agrees_with_insertion xs).trans (SelectionSorting.agrees_with_insertion xs).symm

theorem sorted_fixed (xs : List Nat) (h : Sorted xs) : mergesort xs = xs :=
  (agrees_with_insertion xs).trans (InsertionSorting.sorted_fixed xs h)

theorem mergesort_idempotent (xs : List Nat) : mergesort (mergesort xs) = mergesort xs :=
  sorted_fixed (mergesort xs) (mergesort_sorts xs)

theorem sort_pi : mergesort [3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5] =
    [1, 1, 2, 3, 3, 4, 5, 5, 5, 6, 9] :=
  (agrees_with_insertion _).trans InsertionSorting.sort_pi

theorem pi_contract :
    ([3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5] : List Nat).Perm
      [1, 1, 2, 3, 3, 4, 5, 5, 5, 6, 9] ∧ Sorted [1, 1, 2, 3, 3, 4, 5, 5, 5, 6, 9] := by
  simpa only [sort_pi] using mergesort_correct [3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5]

theorem keyed_correct {α : Type u} {κ : Type v} [LE κ] [DecidableLE κ]
    [Std.IsLinearPreorder κ] (key : α → κ) (xs : List α) :
    KeySorted key (SourceMergeSort.sortOn key xs) ∧
      (SourceMergeSort.sortOn key xs).Perm xs := SourceMergeSort.sortOn_correct key xs

theorem key_lists_agree {α : Type u} {κ : Type v} [LinearOrder κ]
    (key : α → κ) (xs : List α) :
    (SourceMergeSort.sortOn key xs).map key = sortOn id (xs.map key) := by
  have hs := keyed_correct key xs
  have ht := sortOn_correct id (xs.map key)
  apply List.Perm.eq_of_pairwise' (r := (· ≤ ·))
  · simpa only [List.pairwise_map, Function.comp_def] using hs.1
  · exact ht.1
  · exact (hs.2.map key).trans ht.2.symm

/-! The alternating source sort has a tagged equal-key two-cycle. -/

abbrev Record := Nat × String
def records : List Record := [(0, "a"), (0, "b"), (0, "c")]
def afterOne : List Record := [(0, "a"), (0, "c"), (0, "b")]

theorem records_split : split records = ([(0, "a"), (0, "c")], [(0, "b")]) := rfl

theorem record_output : SourceMergeSort.sortOn Prod.fst records = afterOne := by
  change SourceMergeSort.sortBy (fun a b : Record => decide (a.1 ≤ b.1))
    [(0, "a"), (0, "b"), (0, "c")] = _
  rw [source_three]
  simp [afterOne]

theorem record_second_output : SourceMergeSort.sortOn Prod.fst afterOne = records := by
  change SourceMergeSort.sortBy (fun a b : Record => decide (a.1 ≤ b.1))
    [(0, "a"), (0, "c"), (0, "b")] = _
  rw [source_three]
  simp [records]

theorem records_sorted : KeySorted Prod.fst records := by decide

theorem record_contract : KeySorted Prod.fst (SourceMergeSort.sortOn Prod.fst records) ∧
    (SourceMergeSort.sortOn Prod.fst records).Perm records := keyed_correct Prod.fst records

theorem records_not_fixed : SourceMergeSort.sortOn Prod.fst records ≠ records := by
  rw [record_output]
  decide

theorem record_two_cycle :
    SourceMergeSort.sortOn Prod.fst (SourceMergeSort.sortOn Prod.fst records) = records := by
  rw [record_output, record_second_output]

theorem records_not_idempotent :
    SourceMergeSort.sortOn Prod.fst (SourceMergeSort.sortOn Prod.fst records) ≠
      SourceMergeSort.sortOn Prod.fst records := by
  rw [record_two_cycle, record_output]
  decide

theorem records_not_stable : ¬ Stable Prod.fst records (SourceMergeSort.sortOn Prod.fst records) := by
  intro hs
  have h := hs 0
  rw [record_output] at h
  have bad : afterOne = records := h
  exact (by decide : afterOne ≠ records) bad

/-- Shared merge is stable for the actual block concatenation, which is different
from the source sort's original equal-key order. -/
theorem blocks_stable :
    Stable Prod.fst ([(0, "a"), (0, "c")] ++ [(0, "b")] : List Record)
      (mergeBy Prod.fst [(0, "a"), (0, "c")] [(0, "b")]) :=
  mergeBy_stable Prod.fst _ _ (by decide) (by decide)

theorem records_differ_from_stable_sort :
    SourceMergeSort.sortOn Prod.fst records ≠ sortOn Prod.fst records := by
  intro h
  apply records_not_stable
  rw [h]
  exact (sortOn_spec Prod.fst records).stable

/-! Measured execution consumes actual returned halves and merged outputs. -/

abbrev natCmp (a b : Nat) := decide (a ≤ b)

/-- The shared measured merge erases to the actual source merge primitive. -/
theorem measured_merge_source (xs ys : List Nat) :
    (Resources.ListMerge.run natCmp xs ys).1 = merge xs ys :=
  (Resources.ListMerge.run_value natCmp xs ys).trans (merge_equation xs ys).symm

theorem measured_merge_bound (xs ys : List Nat) :
    Resources.ListMerge.comparisons natCmp xs ys ≤ xs.length + ys.length - 1 :=
  Resources.ListMerge.comparisons_le_pred natCmp xs ys

theorem measured_split_three :
    Resources.SourceMergeSort.splitRun [3, 1, 2] = (([3, 2], [1]), 3) := by
  rw [Resources.SourceMergeSort.splitRun_exact]
  rfl

theorem measured_pair {α : Type u} (cmp : α → α → Bool) (x y : α) :
    Resources.SourceMergeSort.run cmp [x, y] = (List.merge [x] [y] cmp, (2, 1)) := by
  rw [Resources.SourceMergeSort.run_step cmp [x, y] (by simp)]
  cases h : cmp x y <;>
    simp [Resources.SourceMergeSort.splitRun, Resources.bind, Resources.reweight,
      Resources.SourceMergeSort.run_singleton, Resources.ListMerge.run, h]

theorem measured_three : Resources.SourceMergeSort.run natCmp [3, 1, 2] =
    ([1, 2, 3], (5, 2)) := by
  have hp : Resources.SourceMergeSort.run natCmp [3, 2] = ([2, 3], (2, 1)) := by
    simpa [List.cons_merge_cons, natCmp] using measured_pair natCmp 3 2
  rw [Resources.SourceMergeSort.run_step natCmp [3, 1, 2] (by decide)]
  simp [Resources.SourceMergeSort.splitRun, Resources.bind, Resources.reweight, hp,
    Resources.SourceMergeSort.run_singleton, Resources.ListMerge.run, natCmp]

theorem measured_three_other : Resources.SourceMergeSort.run natCmp [3, 2, 1] =
    ([1, 2, 3], (5, 3)) := by
  have hp : Resources.SourceMergeSort.run natCmp [3, 1] = ([1, 3], (2, 1)) := by
    simpa [List.cons_merge_cons, natCmp] using measured_pair natCmp 3 1
  rw [Resources.SourceMergeSort.run_step natCmp [3, 2, 1] (by decide)]
  simp [Resources.SourceMergeSort.splitRun, Resources.bind, Resources.reweight, hp,
    Resources.SourceMergeSort.run_singleton, Resources.ListMerge.run, natCmp]

theorem measured_boundaries :
    Resources.SourceMergeSort.run natCmp [] = ([], (0, 0)) ∧
      Resources.SourceMergeSort.run natCmp [7] = ([7], (0, 0)) ∧
      Resources.SourceMergeSort.splitRun [7] = (([7], []), 1) :=
  ⟨Resources.SourceMergeSort.run_nil natCmp,
    Resources.SourceMergeSort.run_singleton natCmp 7, rfl⟩

theorem measured_merge_interleaved :
    Resources.ListMerge.run natCmp [1, 3] [2, 4] = ([1, 2, 3, 4], (3, 4)) := by
  simp [Resources.ListMerge.run, Resources.bind, natCmp]

theorem measured_merge_early_exhaustion :
    Resources.ListMerge.run natCmp [1, 2] [3, 4] = ([1, 2, 3, 4], (2, 3)) := by
  simp [Resources.ListMerge.run, Resources.bind, natCmp]

theorem same_value_different_comparisons :
    (Resources.SourceMergeSort.run natCmp [3, 1, 2]).1 =
      (Resources.SourceMergeSort.run natCmp [3, 2, 1]).1 ∧
      (Resources.SourceMergeSort.run natCmp [3, 1, 2]).2.2 ≠
        (Resources.SourceMergeSort.run natCmp [3, 2, 1]).2.2 := by
  rw [measured_three, measured_three_other]
  decide

def measuredSquare :
    Squares.Square ⟨List Nat, List Nat, id⟩
      ⟨Resources.Measured (List Nat) (Nat × Nat), List Nat, Prod.fst⟩ :=
  Resources.erasureSquare (Resources.SourceMergeSort.run natCmp) mergesort
    (Resources.SourceMergeSort.run_value natCmp)

theorem measured_pi_via_square :
    (measuredSquare.impl [3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5]).1 =
      [1, 1, 2, 3, 3, 4, 5, 5, 5, 6, 9] :=
  (measuredSquare.commutes _).trans sort_pi

theorem measured_sorting_contract (xs : List Nat) :
    xs.Perm (Resources.SourceMergeSort.run natCmp xs).1 ∧
      Sorted (Resources.SourceMergeSort.run natCmp xs).1 := by
  simpa only [Resources.SourceMergeSort.run_value, mergesort, SourceMergeSort.sortOn,
    natCmp, id_eq] using mergesort_correct xs

theorem range_work_bound (n : Nat) :
    Resources.SourceMergeSort.work natCmp (List.range n) ≤ 2 * (n * Nat.clog 2 n) := by
  simpa only [List.length_range] using
    Resources.SourceMergeSort.work_le_clog natCmp (List.range n)

/-- This family theorem counts the declared split visits and merge comparisons. -/
theorem range_work_isBigO :
    Asymptotics.IsBigO Filter.atTop
      (fun n => (Resources.SourceMergeSort.work natCmp (List.range n) : ℝ))
      (fun n => (n : ℝ) * Real.logb 2 n) :=
  Resources.SourceMergeSort.work_isBigO natCmp List.range (fun _ => List.length_range)

end Examples.MergeSorting
