import Applications.Selection.FixedRank
import Applications.Selection.MedianOfMedians

/-!
Reduction of selection to a lower median, FDSA Exercise 3.5.

For input length `n` and zero-based rank `k`, add `n-1-2*k` copies of an input
minimum and `2*k+1-n` copies of an input maximum. Natural subtraction makes
one padding count zero. The output has odd length, and the original selected
occurrence moves to its central rank. Equal values and repeated extrema are
allowed. No global bottom, top or inhabited instance is required. The actual
extrema, length, replication and append costs are instrumented separately in
`Applications.Resources.MedianReduction`.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Applications.Selection.MedianReduction
open Applications.Selection.FixedRank
universe u
variable {α : Type u}

/-- The association also specifies which two append calls the source pays for. -/
def padExtrema (low high : Nat) (lo hi : α) (xs : List α) : List α :=
  List.replicate low lo ++ (xs ++ List.replicate high hi)

theorem padExtrema_length (low high : Nat) (lo hi : α) (xs : List α) :
    (padExtrema low high lo hi xs).length = low + xs.length + high := by
  simp only [padExtrema, List.length_append, List.length_replicate]
  omega

/-- The identity is arithmetic; validity is needed separately for a linear
output-size bound and for the existence of the requested occurrence. -/
theorem padding_length_identity (k n : Nat) :
    (n - 1 - 2 * k) + n + (2 * k + 1 - n) =
      2 * (k + (n - 1 - 2 * k)) + 1 := by
  omega

theorem padding_total_le (k n : Nat) (hk : k < n) :
    (n - 1 - 2 * k) + (2 * k + 1 - n) ≤ n - 1 := by
  omega

variable [LinearOrder α]

/-- Two actual minimum traversals, the second in the order dual, find input
extrema. The input head supplies both initial candidates. -/
def extrema (x : α) (xs : List α) : α × α :=
  (minimumLoop x xs, minimumLoop (α := OrderDual α) x xs)

theorem extrema_spec (x : α) (xs : List α) :
    ((extrema x xs).1 ∈ x :: xs ∧ ∀ y ∈ x :: xs, (extrema x xs).1 ≤ y) ∧
      ((extrema x xs).2 ∈ x :: xs ∧ ∀ y ∈ x :: xs, y ≤ (extrema x xs).2) :=
  ⟨minimumLoop_spec x xs, minimumLoop_spec (α := OrderDual α) x xs⟩

theorem extrema_eq_of_bounds (x : α) (xs : List α) (lo hi : α)
    (hlo_mem : lo ∈ x :: xs) (hhi_mem : hi ∈ x :: xs)
    (hlo : ∀ y ∈ x :: xs, lo ≤ y) (hhi : ∀ y ∈ x :: xs, y ≤ hi) :
    extrema x xs = (lo, hi) := by
  have he := extrema_spec x xs
  apply Prod.ext
  · exact le_antisymm (he.1.2 lo hlo_mem) (hlo _ he.1.1)
  · exact le_antisymm (hhi _ he.2.1) (he.2.2 hi hhi_mem)

/-- Padding can tie the selected value. Strict counts therefore contribute
at most the padding count, not an assumed exact number of smaller values. -/
theorem ranked_padExtrema (low high : Nat) (lo hi : α) (xs : List α) (k : Nat)
    (a : α) (ha : RankedAt xs k a) (hlo : lo ≤ a) (hhi : a ≤ hi) :
    RankedAt (padExtrema low high lo hi xs) (k + low) a := by
  have hlow_gt : (List.replicate low lo).countP (fun x => decide (a < x)) = 0 := by
    simp [List.countP_replicate, not_lt_of_ge hlo]
  have hhigh_lt : (List.replicate high hi).countP (fun x => decide (x < a)) = 0 := by
    simp [List.countP_replicate, not_lt_of_ge hhi]
  have hlow_lt : (List.replicate low lo).countP (fun x => decide (x < a)) ≤ low := by
    have h : (List.replicate low lo).countP (fun x => decide (x < a)) ≤
        (List.replicate low lo).length := List.countP_le_length
    simpa only [List.length_replicate] using h
  have hhigh_gt : (List.replicate high hi).countP (fun x => decide (a < x)) ≤ high := by
    have h : (List.replicate high hi).countP (fun x => decide (a < x)) ≤
        (List.replicate high hi).length := List.countP_le_length
    simpa only [List.length_replicate] using h
  have hc := ha.count_bounds
  have hk := ha.lt_length
  apply ranked_iff_count_bounds.mpr
  simp only [padExtrema, List.countP_append, List.length_append, List.length_replicate,
    hlow_gt, hhigh_lt]
  constructor <;> omega

/-- Empty input is extended to empty output. Every nonempty input executes
length, extrema search and both padding/append operations. -/
def reduceToMedian (k : Nat) : List α → List α
  | [] => []
  | x :: xs =>
      let n := (x :: xs).length
      let bounds := extrema x xs
      padExtrema (n - 1 - 2 * k) (2 * k + 1 - n) bounds.1 bounds.2 (x :: xs)

theorem reduceToMedian_nil (k : Nat) : reduceToMedian k ([] : List α) = [] := rfl

theorem reduceToMedian_length (k : Nat) (xs : List α) (hx : xs ≠ []) :
    (reduceToMedian k xs).length =
      (xs.length - 1 - 2 * k) + xs.length + (2 * k + 1 - xs.length) := by
  cases xs with
  | nil => exact (hx rfl).elim
  | cons x xs => simp only [reduceToMedian, padExtrema_length]

theorem reduceToMedian_nonempty (k : Nat) (xs : List α) (hx : xs ≠ []) :
    reduceToMedian k xs ≠ [] := by
  apply List.ne_nil_of_length_pos
  rw [reduceToMedian_length k xs hx]
  have hn : 0 < xs.length := List.length_pos_iff.mpr hx
  omega

theorem reduceToMedian_length_eq (k : Nat) (xs : List α) (hx : xs ≠ []) :
    (reduceToMedian k xs).length = 2 * (k + (xs.length - 1 - 2 * k)) + 1 := by
  rw [reduceToMedian_length k xs hx]
  exact padding_length_identity k xs.length

/-- The central occurrence index is exactly the original index plus the
number of minimum copies, even when that minimum equals the selected value. -/
theorem reduceToMedian_center (k : Nat) (xs : List α) (hx : xs ≠ []) :
    ((reduceToMedian k xs).length - 1) / 2 = k + (xs.length - 1 - 2 * k) := by
  rw [reduceToMedian_length_eq k xs hx]
  omega

theorem reduceToMedian_odd (k : Nat) (xs : List α) (hx : xs ≠ []) :
    (reduceToMedian k xs).length % 2 = 1 := by
  rw [reduceToMedian_length_eq k xs hx]
  omega

theorem reduceToMedian_length_le (k : Nat) (xs : List α) (hk : k < xs.length) :
    (reduceToMedian k xs).length ≤ 2 * xs.length - 1 := by
  have hx : xs ≠ [] := List.ne_nil_of_length_pos (by omega)
  rw [reduceToMedian_length k xs hx]
  have h := padding_total_le k xs.length hk
  omega

theorem reduceToMedian_rank_shift (k : Nat) (xs : List α) (a : α)
    (ha : RankedAt xs k a) :
    RankedAt (reduceToMedian k xs) (k + (xs.length - 1 - 2 * k)) a := by
  cases xs with
  | nil =>
      have h := ha.lt_length
      simp at h
  | cons x xs =>
      have he := extrema_spec x xs
      exact ranked_padExtrema _ _ _ _ (x :: xs) k a ha
        (he.1.2 a ha.mem) (he.2.2 a ha.mem)

theorem reduceToMedian_ranked (k : Nat) (xs : List α) (a : α)
    (ha : RankedAt xs k a) :
    RankedAt (reduceToMedian k xs) (((reduceToMedian k xs).length - 1) / 2) a := by
  have hn := ha.lt_length
  have hx : xs ≠ [] := List.ne_nil_of_length_pos (by omega)
  rw [reduceToMedian_center k xs hx]
  exact reduceToMedian_rank_shift k xs a ha

/-- Calling any valid lower-median policy on the constructed list solves the
original zero-based selection problem. The reduction itself never calls it. -/
theorem reduceToMedian_value (choose : List α → Option α) (hv : PivotValid choose)
    (k : Nat) (xs : List α) (hk : k < xs.length) :
    lowerMedianWith choose (reduceToMedian k xs) = selectFixed k xs := by
  obtain ⟨a, ha, hr⟩ := selectFixed_spec k xs hk
  rw [lowerMedianWith_value choose hv]
  exact (ranked_iff_index.mp (reduceToMedian_ranked k xs a hr)).trans ha.symm

theorem reduceToMedian_payload_value (k : Nat) (xs : List α)
    (hx : xs ≠ []) (hk : k < xs.length) :
    some (lowerMedianValue (reduceToMedian k xs) (reduceToMedian_nonempty k xs hx)) =
      selectFixed k xs := by
  rw [← lowerMedianWith_eq_some_value List.head? head_pivot_valid]
  exact reduceToMedian_value List.head? head_pivot_valid k xs hk

/-- The original public selector keeps its one-based rank interface. -/
theorem reduceToMedian_spec (choose : List α → Option α) (hv : PivotValid choose)
    (k : Nat) (xs : List α) (hx : xs ≠ []) (hk : k < xs.length) :
    reduceToMedian k xs ≠ [] ∧
      lowerMedianWith choose (reduceToMedian k xs) = selectWith choose (k + 1) xs := by
  refine ⟨reduceToMedian_nonempty k xs hx, ?_⟩
  rw [reduceToMedian_value choose hv k xs hk, selectFixed_eq_selectWith choose hv]

end Applications.Selection.MedianReduction
