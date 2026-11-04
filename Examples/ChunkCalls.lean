import Applications.Resources.Chunks

/-! Connected cases for the source chopping recursion. The expected counts
include both list traversals, every chopping entry, and its terminal call.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.ChunkCalls
open Resources.Chunks Applications.Sequences.Chunks
universe u

theorem empty_payload (d : Nat) : chopRun d ([] : List (Fin 0)) = ([], 1) :=
  chopRun_nil d

theorem zero_size : chopRun 0 ([7, 2, 4] : List Nat) = ([], 1) :=
  chopRun_zero _

theorem singleton_chunks :
    chopRun 1 ([7, 2, 4] : List Nat) = ([[7], [2], [4]], 16) := by
  apply Prod.ext
  · rw [chopRun_value, chop_one]
    rfl
  · rw [chopRun_one_cost]
    rfl

theorem short_final_chunk :
    chopRun 2 ([7, 2, 4] : List Nat) = ([[7, 2], [4]], 13) := by
  rw [chopRun_exact 2 _ (by decide)]
  decide +kernel

theorem oversized_group :
    chopRun 10 ([7, 2, 4] : List Nat) = ([[7, 2, 4]], 10) := by
  rw [chopRun_exact 10 _ (by decide)]
  decide +kernel

theorem first_recursive_size :
    chopRun 5 (List.range 21) =
      ([[0, 1, 2, 3, 4], [5, 6, 7, 8, 9], [10, 11, 12, 13, 14],
        [15, 16, 17, 18, 19], [20]], 58) := by
  rw [chopRun_exact 5 _ (by decide)]
  decide +kernel

/-- The first step really contains both calls; a fused traversal has a
different source tariff even when it returns the same two list values. -/
theorem both_traversals_are_charged :
    (Resources.ListCalls.takeRun 2 ([7, 2, 4] : List Nat)).2 = 3 ∧
      (Resources.ListCalls.dropRun 2 ([7, 2, 4] : List Nat)).2 = 3 ∧
      (chopRun 2 ([7, 2, 4] : List Nat)).2 = 13 := by
  rw [Resources.ListCalls.takeRun_exact, Resources.ListCalls.dropRun_exact,
    short_final_chunk]
  decide

/-- Replacing only the first take/drop pair by one split would cost ten;
the unchanged source execution costs thirteen. -/
theorem fused_first_step_is_not_source_count :
    (Resources.SymmetricCosts.splitRun 2 ([7, 2, 4] : List Nat)).2 +
        (chopRun 2 ([4] : List Nat)).2 + 1 = 10 ∧
      (chopRun 2 ([7, 2, 4] : List Nat)).2 ≠ 10 := by
  rw [short_final_chunk, Resources.SymmetricCosts.splitRun_work,
    chopRun_cost 2 ([4] : List Nat) (by decide)]
  decide +kernel

theorem no_occurrence_is_lost {α : Type u} (d : Nat) (xs : List α) (hd : 0 < d) :
    (chopRun d xs).1.flatten = xs := chopRun_flatten d xs hd

theorem reached_chunks_are_valid {α : Type u} (d : Nat) (xs ys : List α)
    (hy : ys ∈ (chopRun d xs).1) : ys ≠ [] ∧ ys.length ≤ d :=
  ⟨chopRun_mem_ne_nil d xs ys hy, chopRun_mem_length d xs ys hy⟩

theorem arbitrary_group_budget {α : Type u} (d : Nat) (xs : List α) :
    (chopRun d xs).2 ≤ 5 * xs.length + 1 := chopRun_cost_bound d xs

end Examples.ChunkCalls
