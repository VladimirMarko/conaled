import Applications.Resources.QuickSort
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Order.Interval.Finset.Nat

/-! Fresh uniform occurrence-pivot quicksort with two observations of its actual
recursive execution. Every nonempty call selects an index, removes that occurrence,
executes both measured filters, binds the actual recursive results, and performs
the two right-associated source appends. The observations are the Exercise 2.4
tariff and the additional append calls. Pivot selection, lookup/removal and random
bits are not charged by these observations. This PMF is a probability denotation,
not a random-bit sampler. Support bounds here do not assert an expected bound.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.RandomQuickSort
open Applications.Sorting
open scoped BigOperators ENNReal
universe u v w
variable {α : Type u} {κ : Type v}

noncomputable section

private theorem uniformIndex_normalization (m : Nat) :
    (∑ _i : Fin (m + 1), (((m + 1 : Nat) : ℝ≥0∞)⁻¹)) = 1 := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact ENNReal.mul_inv_cancel (by simp) (ENNReal.natCast_ne_top _)

/-- A uniform valid occurrence index for a nonempty list. No Fin 0 case or
inhabited payload is used. -/
def uniformIndex (m : Nat) : PMF (Fin (m + 1)) :=
  PMF.ofFintype (fun _ => (((m + 1 : Nat) : ℝ≥0∞)⁻¹)) (uniformIndex_normalization m)

@[simp] theorem uniformIndex_apply (m : Nat) (i : Fin (m + 1)) :
    uniformIndex m i = (((m + 1 : Nat) : ℝ≥0∞)⁻¹) := rfl

@[simp] theorem mem_support_uniformIndex (m : Nat) (i : Fin (m + 1)) :
    i ∈ (uniformIndex m).support := by
  rw [PMF.mem_support_iff, uniformIndex_apply]
  exact ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _)

@[simp] theorem uniformIndex_zero : uniformIndex 0 = PMF.pure (0 : Fin 1) := by
  apply PMF.ext
  intro i
  have hi : i = 0 := by
    apply Fin.ext
    have hlt := i.isLt
    omega
  subst i
  simp [PMF.pure_apply]

/-- An event counts occurrences, including repeated payload values. -/
theorem uniformIndex_event (m : Nat) (event : Fin (m + 1) → Bool) :
    PMF.map event (uniformIndex m) true =
      ((Finset.univ.filter (fun i => event i = true)).card : ℝ≥0∞) /
        ((m + 1 : Nat) : ℝ≥0∞) := by
  classical
  calc
    _ = ∑ i ∈ Finset.univ.filter (fun i => event i = true),
        (((m + 1 : Nat) : ℝ≥0∞)⁻¹) := by
      rw [PMF.map_apply, tsum_fintype]
      simp only [Finset.sum_filter, uniformIndex_apply]
      apply Finset.sum_congr rfl
      intro i _
      cases event i <;> simp
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]

private theorem eraseIdx_length_lt (xs : List α) (i : Nat) (hi : i < xs.length) :
    (xs.eraseIdx i).length < xs.length := by
  have h := List.length_eraseIdx_add_one hi
  omega

private theorem filter_eraseIdx_length_lt (p : α → Bool) (xs : List α)
    (i : Nat) (hi : i < xs.length) :
    ((xs.eraseIdx i).filter p).length < xs.length :=
  lt_of_le_of_lt (List.length_filter_le _ _) (eraseIdx_length_lt xs i hi)

private theorem unit_filter_exact (p : α → Bool) (xs : List α) :
    ListCalls.filterRun (fun x => (p x, 1)) xs = (xs.filter p, 2 * xs.length + 1) := by
  apply Prod.ext
  · exact ListCalls.filterRun_value _ _
  · exact ListCalls.filterRun_cost_of_constant _ xs 1 (fun _ _ => rfl)

/-- Fresh index sampling occurs again in each actual recursive child. The second
filter and both appends consume the values produced by the source operations. -/
def run (lt : α → α → Bool) : List α → PMF (Measured (List α) (Nat × Nat))
  | [] => PMF.pure ([], (1, 0))
  | head :: tail =>
      PMF.bind (uniformIndex tail.length) fun i =>
        let pivot := (head :: tail)[i.val]'i.isLt
        let rest := (head :: tail).eraseIdx i.val
        let leftInput := ListCalls.filterRun (fun x => (lt x pivot, 1)) rest
        PMF.bind (run lt leftInput.1) fun left =>
          let rightInput := ListCalls.filterRun (fun x => (!(lt x pivot), 1)) rest
          PMF.bind (run lt rightInput.1) fun right =>
            let assembled := QuickSort.appendPivotRun left.1 pivot right.1
            PMF.pure (assembled.1,
              (leftInput.2 + left.2.1 + rightInput.2 + right.2.1 + 1,
                left.2.2 + right.2.2 + assembled.2))
termination_by xs => xs.length
decreasing_by
  all_goals simp only [ListCalls.filterRun_value]
  all_goals exact filter_eraseIdx_length_lt _ _ _ i.isLt

@[simp] theorem run_nil (lt : α → α → Bool) :
    run lt [] = PMF.pure ([], (1, 0)) := by rw [run]

/-- Derived from both measured filters and both measured appends. The input of
each child is the indexed remainder's actual returned partition. -/
theorem run_cons (lt : α → α → Bool) (head : α) (tail : List α) :
    run lt (head :: tail) =
      PMF.bind (uniformIndex tail.length) fun i =>
        let pivot := (head :: tail)[i.val]'i.isLt
        let rest := (head :: tail).eraseIdx i.val
        PMF.bind (run lt (rest.filter (fun x => lt x pivot))) fun left =>
          PMF.bind (run lt (rest.filter (fun x => !(lt x pivot)))) fun right =>
            PMF.pure (left.1 ++ ([pivot] ++ right.1),
              (left.2.1 + right.2.1 + 4 * rest.length + 3,
                left.2.2 + right.2.2 + left.1.length + 3)) := by
  rw [run]
  simp only [unit_filter_exact, QuickSort.appendPivotRun_exact]
  apply congrArg (PMF.bind _)
  funext i
  apply congrArg (PMF.bind _)
  funext left
  apply congrArg (PMF.bind _)
  funext right
  apply congrArg PMF.pure
  apply Prod.ext
  · rfl
  · apply Prod.ext <;> dsimp only <;> omega

@[simp] theorem run_singleton (lt : α → α → Bool) (x : α) :
    run lt [x] = PMF.pure ([x], (5, 3)) := by
  simp [run_cons]

/-- Only keys need comparisons; payloads carry no additional instances. -/
abbrev runOn [LT κ] [DecidableLT κ] (key : α → κ) (xs : List α) :=
  run (fun a b => decide (key a < key b)) xs

private theorem right_filter_eq [LinearOrder κ] (key : α → κ)
    (pivot : α) (xs : List α) :
    xs.filter (fun x => !(decide (key x < key pivot))) =
      xs.filter (fun x => decide (key pivot ≤ key x)) := by
  apply List.filter_congr
  intro x _
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq, not_lt]

/-- The key instance retains the source's strict-left/nonstrict-right split. -/
theorem runOn_cons [LinearOrder κ] (key : α → κ) (head : α) (tail : List α) :
    runOn key (head :: tail) =
      PMF.bind (uniformIndex tail.length) fun i =>
        let pivot := (head :: tail)[i.val]'i.isLt
        let rest := (head :: tail).eraseIdx i.val
        PMF.bind (runOn key (rest.filter (fun x => decide (key x < key pivot)))) fun left =>
          PMF.bind (runOn key (rest.filter (fun x => decide (key pivot ≤ key x)))) fun right =>
            PMF.pure (left.1 ++ ([pivot] ++ right.1),
              (left.2.1 + right.2.1 + 4 * rest.length + 3,
                left.2.2 + right.2.2 + left.1.length + 3)) := by
  simp only [runOn, run_cons, right_filter_eq]

/-- Every actual supported branch is witnessed by a valid sampled occurrence
and the two supported recursive results. No externally supplied sampler occurs. -/
theorem mem_support_run_cons_iff (lt : α → α → Bool) (head : α) (tail : List α)
    (result : Measured (List α) (Nat × Nat)) :
    result ∈ (run lt (head :: tail)).support ↔
      ∃ i : Fin (tail.length + 1),
        let pivot := (head :: tail)[i.val]'i.isLt
        let rest := (head :: tail).eraseIdx i.val
        ∃ left ∈ (run lt (rest.filter (fun x => lt x pivot))).support,
          ∃ right ∈ (run lt (rest.filter (fun x => !(lt x pivot)))).support,
            result = (left.1 ++ ([pivot] ++ right.1),
              (left.2.1 + right.2.1 + 4 * rest.length + 3,
                left.2.2 + right.2.2 + left.1.length + 3)) := by
  rw [run_cons]
  simp only [PMF.mem_support_bind_iff, mem_support_uniformIndex,
    PMF.mem_support_pure_iff, true_and]

/-- Raw occurrence preservation requires no comparison law or payload equality. -/
theorem run_perm (lt : α → α → Bool) (xs : List α)
    (result : Measured (List α) (Nat × Nat)) (hr : result ∈ (run lt xs).support) :
    result.1.Perm xs := by
  match xs with
  | [] =>
      have he : result = ([], (1, 0)) := by
        simpa only [run_nil, PMF.mem_support_pure_iff] using hr
      subst result
      exact List.Perm.refl []
  | head :: tail =>
      obtain ⟨i, left, hl, right, hright, he⟩ :=
        (mem_support_run_cons_iff lt head tail result).mp hr
      let pivot := (head :: tail)[i.val]'i.isLt
      let rest := (head :: tail).eraseIdx i.val
      have hleft := run_perm lt (rest.filter (fun x => lt x pivot)) left hl
      have hright' := run_perm lt (rest.filter (fun x => !(lt x pivot))) right hright
      rw [he]
      exact ((hleft.append (hright'.cons pivot)).trans
        (List.perm_middle.trans ((List.filter_append_perm _ rest).cons pivot))).trans
          (List.getElem_cons_eraseIdx_perm i.isLt)
termination_by xs.length
decreasing_by
  all_goals exact filter_eraseIdx_length_lt _ _ _ i.isLt

theorem run_length (lt : α → α → Bool) (xs : List α)
    (result : Measured (List α) (Nat × Nat)) (hr : result ∈ (run lt xs).support) :
    result.1.length = xs.length := (run_perm lt xs result hr).length_eq

/-- Comparator compatibility is local to this input, and the observed key
relation needs only transitivity. This is not a stability statement. -/
theorem run_sorted_compatible_on [LE κ] [IsTrans κ (· ≤ ·)]
    (key : α → κ) (lt : α → α → Bool) (xs : List α)
    (hc : ∀ a ∈ xs, ∀ b ∈ xs, (lt a b = true → key a ≤ key b) ∧
      (lt a b = false → key b ≤ key a))
    (result : Measured (List α) (Nat × Nat)) (hr : result ∈ (run lt xs).support) :
    KeySorted key result.1 := by
  match xs with
  | [] =>
      have he : result = ([], (1, 0)) := by
        simpa only [run_nil, PMF.mem_support_pure_iff] using hr
      simp [he, KeySorted]
  | head :: tail =>
      obtain ⟨i, left, hl, right, hright, he⟩ :=
        (mem_support_run_cons_iff lt head tail result).mp hr
      let pivot := (head :: tail)[i.val]'i.isLt
      let rest := (head :: tail).eraseIdx i.val
      have hp : pivot ∈ head :: tail := List.getElem_mem i.isLt
      have hleft := run_sorted_compatible_on key lt (rest.filter (fun x => lt x pivot))
        (fun a ha b hb => hc a (List.mem_of_mem_eraseIdx (List.mem_filter.mp ha).1)
          b (List.mem_of_mem_eraseIdx (List.mem_filter.mp hb).1)) left hl
      have hright' := run_sorted_compatible_on key lt (rest.filter (fun x => !(lt x pivot)))
        (fun a ha b hb => hc a (List.mem_of_mem_eraseIdx (List.mem_filter.mp ha).1)
          b (List.mem_of_mem_eraseIdx (List.mem_filter.mp hb).1)) right hright
      have hlow : ∀ a ∈ left.1, key a ≤ key pivot := by
        intro a ha
        have hf := List.mem_filter.mp ((run_perm lt _ left hl).mem_iff.mp ha)
        exact (hc a (List.mem_of_mem_eraseIdx hf.1) pivot hp).1 hf.2
      have hhigh : ∀ b ∈ right.1, key pivot ≤ key b := by
        intro b hb
        have hf := List.mem_filter.mp ((run_perm lt _ right hright).mem_iff.mp hb)
        have hf' : lt b pivot = false := by simpa using hf.2
        exact (hc b (List.mem_of_mem_eraseIdx hf.1) pivot hp).2 hf'
      rw [he]
      apply List.pairwise_append.mpr
      refine ⟨hleft, List.pairwise_cons.mpr ⟨hhigh, hright'⟩, ?_⟩
      intro a ha b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact hlow a ha
      · exact Std.le_trans (hlow a ha) (hhigh b hb)
termination_by xs.length
decreasing_by
  all_goals exact filter_eraseIdx_length_lt _ _ _ i.isLt

theorem runOn_correct [LinearOrder κ] (key : α → κ) (xs : List α)
    (result : Measured (List α) (Nat × Nat)) (hr : result ∈ (runOn key xs).support) :
    KeySorted key result.1 ∧ result.1.Perm xs := by
  refine ⟨?_, run_perm _ xs result hr⟩
  apply run_sorted_compatible_on key _ xs _ result hr
  intro a _ b _
  exact ⟨fun h => le_of_lt (of_decide_eq_true h),
    fun h => le_of_not_gt (of_decide_eq_false h)⟩

private theorem support_cost_bounds (lt : α → α → Bool) (xs : List α)
    (result : Measured (List α) (Nat × Nat)) (hr : result ∈ (run lt xs).support) :
    result.2.1 ≤ 2 * xs.length ^ 2 + 2 * xs.length + 1 ∧
      3 * xs.length ≤ result.2.2 ∧
      2 * result.2.2 ≤ xs.length ^ 2 + 5 * xs.length ∧
      result.2.2 ≤ result.2.1 := by
  match xs with
  | [] =>
      have he : result = ([], (1, 0)) := by
        simpa only [run_nil, PMF.mem_support_pure_iff] using hr
      subst result
      simp
  | head :: tail =>
      obtain ⟨i, left, hl, right, hright, he⟩ :=
        (mem_support_run_cons_iff lt head tail result).mp hr
      let pivot := (head :: tail)[i.val]'i.isLt
      let rest := (head :: tail).eraseIdx i.val
      obtain ⟨htl, hal, haul, hatl⟩ :=
        support_cost_bounds lt (rest.filter (fun x => lt x pivot)) left hl
      obtain ⟨htr, har, haur, hatr⟩ :=
        support_cost_bounds lt (rest.filter (fun x => !(lt x pivot))) right hright
      have hlength := run_length lt (rest.filter (fun x => lt x pivot)) left hl
      have hpart := QuickSort.partition_lengths (fun x => lt x pivot) rest
      have hrest : rest.length + 1 = (head :: tail).length :=
        List.length_eraseIdx_add_one i.isLt
      have hprod := Nat.zero_le
        ((rest.filter (fun x => lt x pivot)).length *
          (rest.filter (fun x => !(lt x pivot))).length)
      rw [he]
      dsimp only
      rw [hlength]
      rw [← hrest, ← hpart]
      refine ⟨?_, ?_, ?_, ?_⟩
      · nlinarith
      · omega
      · nlinarith
      · omega
termination_by xs.length
decreasing_by
  all_goals exact filter_eraseIdx_length_lt _ _ _ i.isLt

/-- The exercise bound holds on every actual random branch, with duplicates. -/
theorem exercise_cost_le (lt : α → α → Bool) (xs : List α)
    (result : Measured (List α) (Nat × Nat)) (hr : result ∈ (run lt xs).support) :
    result.2.1 ≤ 2 * xs.length ^ 2 + 2 * xs.length + 1 :=
  (support_cost_bounds lt xs result hr).1

theorem three_mul_length_le_append_cost (lt : α → α → Bool) (xs : List α)
    (result : Measured (List α) (Nat × Nat)) (hr : result ∈ (run lt xs).support) :
    3 * xs.length ≤ result.2.2 := (support_cost_bounds lt xs result hr).2.1

theorem two_mul_append_cost_le (lt : α → α → Bool) (xs : List α)
    (result : Measured (List α) (Nat × Nat)) (hr : result ∈ (run lt xs).support) :
    2 * result.2.2 ≤ xs.length ^ 2 + 5 * xs.length :=
  (support_cost_bounds lt xs result hr).2.2.1

theorem append_cost_le_exercise_cost (lt : α → α → Bool) (xs : List α)
    (result : Measured (List α) (Nat × Nat)) (hr : result ∈ (run lt xs).support) :
    result.2.2 ≤ result.2.1 := (support_cost_bounds lt xs result hr).2.2.2

/-- Append-inclusive source-body observation. Selection, lookup/removal and
random bits are still outside this tariff. -/
theorem append_inclusive_cost_bounds (lt : α → α → Bool) (xs : List α)
    (result : Measured (List α) (Nat × Nat)) (hr : result ∈ (run lt xs).support) :
    result.2.1 ≤ result.2.1 + result.2.2 ∧
      result.2.1 + result.2.2 ≤ 2 * result.2.1 := by
  have ha := append_cost_le_exercise_cost lt xs result hr
  omega

theorem two_mul_append_inclusive_cost_le (lt : α → α → Bool) (xs : List α)
    (result : Measured (List α) (Nat × Nat)) (hr : result ∈ (run lt xs).support) :
    2 * (result.2.1 + result.2.2) ≤ 5 * xs.length ^ 2 + 9 * xs.length + 2 := by
  have ht := exercise_cost_le lt xs result hr
  have ha := two_mul_append_cost_le lt xs result hr
  omega

theorem append_inclusive_cost_le (lt : α → α → Bool) (xs : List α)
    (result : Measured (List α) (Nat × Nat)) (hr : result ∈ (run lt xs).support) :
    result.2.1 + result.2.2 ≤ (5 * xs.length ^ 2 + 9 * xs.length + 2) / 2 := by
  have h := two_mul_append_inclusive_cost_le lt xs result hr
  omega

/-- Project the actual observation to a countable carrier before introducing
any measurable space. Payloads remain unrestricted. -/
def exerciseLaw (lt : α → α → Bool) (xs : List α) : PMF Nat :=
  PMF.map (fun result => result.2.1) (run lt xs)

/-- The append-inclusive source-body count, without pivot implementation costs. -/
def literalLaw (lt : α → α → Bool) (xs : List α) : PMF Nat :=
  PMF.map (fun result => result.2.1 + result.2.2) (run lt xs)

/-- The cost law is obtained by mapping the actual returned observation. This
distributional recursion does not assert an expectation or integrability. -/
theorem exerciseLaw_cons (lt : α → α → Bool) (head : α) (tail : List α) :
    exerciseLaw lt (head :: tail) =
      PMF.bind (uniformIndex tail.length) fun i =>
        let pivot := (head :: tail)[i.val]'i.isLt
        let rest := (head :: tail).eraseIdx i.val
        PMF.bind (exerciseLaw lt (rest.filter (fun x => lt x pivot))) fun left =>
          PMF.bind (exerciseLaw lt (rest.filter (fun x => !(lt x pivot)))) fun right =>
            PMF.pure (left + right + 4 * rest.length + 3) := by
  simp only [exerciseLaw, run_cons, PMF.map_bind, PMF.pure_map,
    PMF.bind_map, Function.comp_def]

@[simp] theorem exerciseLaw_nil (lt : α → α → Bool) :
    exerciseLaw lt [] = PMF.pure 1 := by simp [exerciseLaw, PMF.pure_map]

@[simp] theorem literalLaw_nil (lt : α → α → Bool) :
    literalLaw lt [] = PMF.pure 1 := by simp [literalLaw, PMF.pure_map]

@[simp] theorem exerciseLaw_singleton (lt : α → α → Bool) (x : α) :
    exerciseLaw lt [x] = PMF.pure 5 := by simp [exerciseLaw, PMF.pure_map]

@[simp] theorem literalLaw_singleton (lt : α → α → Bool) (x : α) :
    literalLaw lt [x] = PMF.pure 8 := by simp [literalLaw, PMF.pure_map]

theorem exerciseLaw_support (lt : α → α → Bool) (xs : List α) :
    (exerciseLaw lt xs).support ⊆ Set.Iic (2 * xs.length ^ 2 + 2 * xs.length + 1) := by
  intro cost hc
  obtain ⟨result, hr, he⟩ := (PMF.mem_support_map_iff _ _ _).mp hc
  rw [← he]
  exact exercise_cost_le lt xs result hr

theorem exerciseLaw_support_finite (lt : α → α → Bool) (xs : List α) :
    (exerciseLaw lt xs).support.Finite :=
  (Set.finite_Iic _).subset (exerciseLaw_support lt xs)

theorem literalLaw_support (lt : α → α → Bool) (xs : List α) :
    (literalLaw lt xs).support ⊆ Set.Iic ((5 * xs.length ^ 2 + 9 * xs.length + 2) / 2) := by
  intro cost hc
  obtain ⟨result, hr, he⟩ := (PMF.mem_support_map_iff _ _ _).mp hc
  rw [← he]
  exact append_inclusive_cost_le lt xs result hr

theorem literalLaw_support_finite (lt : α → α → Bool) (xs : List α) :
    (literalLaw lt xs).support.Finite :=
  (Set.finite_Iic _).subset (literalLaw_support lt xs)

private theorem eq_pure_of_support {β : Type w} (p : PMF β) (x : β)
    (h : ∀ y ∈ p.support, y = x) : p = PMF.pure x := by
  classical
  have hs : p.support = {x} := by
    apply Set.Subset.antisymm
    · intro y hy
      exact h y hy
    · intro y hy
      have hy' : y = x := hy
      subst y
      obtain ⟨z, hz⟩ := p.support_nonempty
      rw [← h z hz]
      exact hz
  have hx : p x = 1 := (p.apply_eq_one_iff x).mpr hs
  apply PMF.ext
  intro y
  rw [PMF.pure_apply]
  split_ifs with hy
  · simpa only [hy] using hx
  · exact (p.apply_eq_zero_iff y).mpr (fun hy' => hy (h y hy'))

/-- If every observed comparison is false, every random pivot leaves the whole
remainder on the right. This is a pathwise fact for arbitrary tagged values. -/
theorem costs_of_all_false (lt : α → α → Bool) (xs : List α)
    (hf : ∀ a ∈ xs, ∀ b ∈ xs, lt a b = false)
    (result : Measured (List α) (Nat × Nat)) (hr : result ∈ (run lt xs).support) :
    result.2 = (2 * xs.length ^ 2 + 2 * xs.length + 1, 3 * xs.length) := by
  match xs with
  | [] =>
      have he : result = ([], (1, 0)) := by
        simpa only [run_nil, PMF.mem_support_pure_iff] using hr
      simp [he]
  | head :: tail =>
      obtain ⟨i, left, hl, right, hright, he⟩ :=
        (mem_support_run_cons_iff lt head tail result).mp hr
      let pivot := (head :: tail)[i.val]'i.isLt
      let rest := (head :: tail).eraseIdx i.val
      have hp : pivot ∈ head :: tail := List.getElem_mem i.isLt
      have hleft : rest.filter (fun x => lt x pivot) = [] :=
        List.filter_eq_nil_iff.mpr (fun x hx => by
          simp [hf x (List.mem_of_mem_eraseIdx hx) pivot hp])
      have hrightInput : rest.filter (fun x => !(lt x pivot)) = rest :=
        List.filter_eq_self.mpr (fun x hx => by
          simp [hf x (List.mem_of_mem_eraseIdx hx) pivot hp])
      have hleftResult : left = ([], (1, 0)) := by
        change left ∈ (run lt (rest.filter (fun x => lt x pivot))).support at hl
        simpa only [hleft, run_nil, PMF.mem_support_pure_iff] using hl
      have hrightSupport : right ∈ (run lt rest).support := by
        change right ∈ (run lt (rest.filter (fun x => !(lt x pivot)))).support at hright
        simpa only [hrightInput] using hright
      have hc := costs_of_all_false lt rest
        (fun a ha b hb => hf a (List.mem_of_mem_eraseIdx ha)
          b (List.mem_of_mem_eraseIdx hb)) right hrightSupport
      have hrest : rest.length + 1 = (head :: tail).length :=
        List.length_eraseIdx_add_one i.isLt
      rw [he, hleftResult]
      dsimp only
      rw [hc]
      rw [← hrest]
      simp only [List.length_nil]
      apply Prod.ext <;> dsimp only <;> nlinarith
termination_by xs.length
decreasing_by
  exact eraseIdx_length_lt _ _ i.isLt

/-- The joint cost law can be deterministic even when the value order is not. -/
theorem joint_cost_law_of_all_false (lt : α → α → Bool) (xs : List α)
    (hf : ∀ a ∈ xs, ∀ b ∈ xs, lt a b = false) :
    PMF.map Prod.snd (run lt xs) =
      PMF.pure (2 * xs.length ^ 2 + 2 * xs.length + 1, 3 * xs.length) := by
  apply eq_pure_of_support
  intro cost hc
  obtain ⟨result, hr, he⟩ := (PMF.mem_support_map_iff _ _ _).mp hc
  rw [← he]
  exact costs_of_all_false lt xs hf result hr

theorem costs_of_constant_key [LinearOrder κ] (key : α → κ) (xs : List α) (c : κ)
    (hk : ∀ x ∈ xs, key x = c)
    (result : Measured (List α) (Nat × Nat)) (hr : result ∈ (runOn key xs).support) :
    result.2 = (2 * xs.length ^ 2 + 2 * xs.length + 1, 3 * xs.length) := by
  apply costs_of_all_false _ xs _ result hr
  intro a ha b hb
  simp [hk a ha, hk b hb]

/-- Equal keys remain quadratic for every pivot choice, even with distinct tags. -/
theorem joint_cost_law_of_constant_key [LinearOrder κ] (key : α → κ) (xs : List α) (c : κ)
    (hk : ∀ x ∈ xs, key x = c) :
    PMF.map Prod.snd (runOn key xs) =
      PMF.pure (2 * xs.length ^ 2 + 2 * xs.length + 1, 3 * xs.length) := by
  apply joint_cost_law_of_all_false
  intro a ha b hb
  simp [hk a ha, hk b hb]

/-- An all-size duplicate family of actual executions, with no payload equality
instance. Random occurrence choice cannot improve this source partition. -/
theorem runOn_replicate [LinearOrder κ] (key : α → κ) (x : α) (n : Nat) :
    runOn key (List.replicate n x) =
      PMF.pure (List.replicate n x, (2 * n ^ 2 + 2 * n + 1, 3 * n)) := by
  apply eq_pure_of_support
  intro result hr
  apply Prod.ext
  · exact List.perm_replicate.mp (run_perm _ _ result hr)
  · simpa only [List.length_replicate] using
      costs_of_constant_key key (List.replicate n x) (key x)
        (fun a ha => congrArg key (List.eq_of_mem_replicate ha)) result hr

end
end Resources.RandomQuickSort
