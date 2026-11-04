import Applications.Resources.SelectionMedians
import Examples.SelectionAuxiliary
import Examples.MedianOfMedians

/-! Connected payload-map cases for the measured median preparation.
Expected values retain duplicates and short final chunks. Exact costs come
from the source chopping and callback executions, not a specification tariff.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.SelectionMedians
open Resources.SelectionMedians Resources.SelectionAuxiliary
open Applications.Selection Applications.Sequences.Chunks
universe u

theorem lower_even_payload :
    slowMedianValueRun ([7, 2] : List Nat) (by decide) = (2, 10) :=
  slowMedianValueRun_of_run _ _ _ _ Examples.SelectionAuxiliary.lower_even_median

theorem duplicate_payload :
    slowMedianValueRun ([4, 4] : List Nat) (by decide) = (4, 9) :=
  slowMedianValueRun_of_run _ _ _ _ Examples.SelectionAuxiliary.repeated_central_values

theorem payload_rank_and_budget {α : Type u} [LinearOrder α]
    (xs : List α) (hx : xs ≠ []) (hn : xs.length ≤ 5) :
    RankedAt xs ((xs.length - 1) / 2) (slowMedianValueRun xs hx).1 ∧
      (slowMedianValueRun xs hx).1 ∈ xs ∧ (slowMedianValueRun xs hx).2 ≤ 47 :=
  ⟨slowMedianValueRun_ranked xs hx, slowMedianValueRun_mem xs hx,
    slowMedianValueRun_small_bound xs hx hn⟩

theorem empty_payload_map :
    mapSlowMedianRun ([] : List (List (Fin 0))) (by simp) = ([], 1) := by
  apply Prod.ext
  · rw [mapSlowMedianRun_value]
    rfl
  · rw [mapSlowMedianRun_cost]
    rfl

/-- Each of the two occurrences pays its own callback, then the map pays
two nonempty entries and its empty call: 10 + 9 + 3 = 22. -/
theorem two_chunk_map :
    mapSlowMedianRun ([[7, 2], [4, 4]] : List (List Nat))
      (by
        intro ys hy
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with rfl | rfl <;> decide) = ([2, 4], 22) := by
  apply Prod.ext
  · apply (List.map_inj_right
      (fun (a b : Nat) (h : some a = some b) => Option.some.inj h)).mp
    rw [mapSlowMedianRun_some_values]
    simp only [List.map_cons, List.map_nil,
      Examples.SelectionAuxiliary.lower_even_median,
      Examples.SelectionAuxiliary.repeated_central_values]
  · rw [mapSlowMedianRun_cost]
    norm_num [Examples.SelectionAuxiliary.lower_even_median,
      Examples.SelectionAuxiliary.repeated_central_values]

theorem empty_chunk_preparation :
    chunkMediansRun 5 ([] : List (Fin 0)) = ([], 2) := by
  apply Prod.ext
  · exact (chunkMediansRun_eq_nil_iff 5 _).mpr (Or.inr rfl)
  · rw [chunkMediansRun_cost, Resources.Chunks.chopRun_nil, chop_nil]
    decide +kernel

theorem zero_size_preparation :
    chunkMediansRun 0 ([7, 2, 4] : List Nat) = ([], 2) := by
  apply Prod.ext
  · exact (chunkMediansRun_eq_nil_iff 0 _).mpr (Or.inl rfl)
  · rw [chunkMediansRun_cost, Resources.Chunks.chopRun_zero, chop_zero]
    decide +kernel

theorem two_full_chunks : chunkMediansRun 5 (List.range 10) = ([2, 7], 70) := by
  apply Prod.ext
  · rw [chunkMediansRun_value, Examples.MedianOfMedians.two_full_chunk_medians]
  · rw [chunkMediansRun_cost_positive 5 _ (by decide)]
    decide +kernel

theorem short_final_chunk : chunkMediansRun 5 (List.range 7) = ([2, 5], 53) := by
  apply Prod.ext
  · rw [chunkMediansRun_value, Examples.MedianOfMedians.short_final_chunk_medians]
  · rw [chunkMediansRun_cost_positive 5 _ (by decide)]
    decide +kernel

theorem duplicate_occurrences :
    chunkMediansRun 5 (List.replicate 6 4) = ([4, 4], 48) := by
  apply Prod.ext
  · rw [chunkMediansRun_value, Examples.MedianOfMedians.duplicate_chunk_medians]
  · rw [chunkMediansRun_cost_positive 5 _ (by decide)]
    decide +kernel

theorem first_recursive_size :
    chunkMediansRun 5 (List.range 21) = ([2, 7, 12, 17, 20], 150) := by
  apply Prod.ext
  · apply (List.map_inj_right
      (fun (a b : Nat) (h : some a = some b) => Option.some.inj h)).mp
    rw [chunkMediansRun_some_values]
    decide +kernel
  · rw [chunkMediansRun_cost_positive 5 _ (by decide)]
    decide +kernel

theorem first_recursive_map_count :
    (mapSlowMedianRun (chop 5 (List.range 21))
      (chop_mem_ne_nil 5 (List.range 21))).2 = 92 := by
  rw [mapSlowMedianRun_cost]
  decide +kernel

theorem prepared_pivot_membership {α : Type u} [LinearOrder α]
    (d : Nat) (xs : List α) (a : α) (ha : a ∈ (chunkMediansRun d xs).1) : a ∈ xs :=
  chunkMediansRun_mem d xs a ha

theorem general_group_preparation {α : Type u} [LinearOrder α]
    (d : Nat) (xs : List α) :
    (chunkMediansRun d xs).1.length = xs.length ⌈/⌉ d ∧
      (chunkMediansRun d xs).2 ≤
        5 * xs.length + (d ^ 2 + 4 * d + 3) * (xs.length ⌈/⌉ d) + 2 :=
  ⟨chunkMediansRun_length d xs, chunkMediansRun_bound d xs⟩

theorem book_map_budget {α : Type u} [LinearOrder α] (xs : List α) :
    (mapSlowMedianRun (chop 5 xs) (chop_mem_ne_nil 5 xs)).2 ≤ 10 * xs.length + 48 :=
  mapSlowMedianRun_chop_five_bound xs

theorem book_preparation_budget {α : Type u} [LinearOrder α] (xs : List α) :
    (chunkMediansRun 5 xs).2 ≤ 15 * xs.length + 49 := chunkMediansRun_five_bound xs

end Examples.SelectionMedians
