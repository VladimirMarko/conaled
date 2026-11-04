import Applications.Sequences.Chunks

/-! Chopping preserves occurrences and retains short final groups. -/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.ListChunks
open Applications.Sequences.Chunks

theorem zero_size_source_convention : chop 0 ([1, 2, 3] : List Nat) = [] :=
  chop_zero _

theorem singleton_chunks : chop 1 ([4, 4, 1] : List Nat) = [[4], [4], [1]] := by
  rw [chop_one]
  rfl

theorem partial_final_chunk :
    chop 5 ([0, 1, 2, 3, 4, 5, 6] : List Nat) = [[0, 1, 2, 3, 4], [5, 6]] := by
  calc
    chop 5 ([0, 1, 2, 3, 4, 5, 6] : List Nat) =
        [0, 1, 2, 3, 4] :: chop 5 [5, 6] :=
      chop_eq_cons _ _ (by decide) (by decide)
    _ = [[0, 1, 2, 3, 4], [5, 6]] := by
      rw [chop_eq_singleton 5 [5, 6] (by decide) (by decide) (by decide)]

theorem partial_chunk_count :
    (chop 5 ([0, 1, 2, 3, 4, 5, 6] : List Nat)).length = 2 := by
  rw [length_chop_eq_add_pred_div]
  rfl

theorem partial_chunks_flatten :
    (chop 5 ([0, 1, 2, 3, 4, 5, 6] : List Nat)).flatten = [0, 1, 2, 3, 4, 5, 6] :=
  flatten_chop _ _ (by decide)

theorem boolean_chunks : chop 2 [true, false, true] = [[true, false], [true]] := by
  calc
    chop 2 [true, false, true] = [true, false] :: chop 2 [true] :=
      chop_eq_cons _ _ (by decide) (by decide)
    _ = [[true, false], [true]] := by
      rw [chop_eq_singleton 2 [true] (by decide) (by decide) (by decide)]

theorem duplicate_counts :
    ((chop 2 ([1, 1, 2, 1, 3] : List Nat)).map
      (List.countP (fun x => decide (x = 1)))).sum = 3 := by
  rw [countP_chop 2 _ (by decide)]
  rfl

theorem duplicate_multiset :
    ((chop 2 ([1, 1, 2, 1, 3] : List Nat)).map
      (fun ys : List Nat => (ys : Multiset Nat))).sum = ([1, 1, 2, 1, 3] : Multiset Nat) :=
  sum_multiset_chop _ _ (by decide)

theorem short_group_nonempty (ys : List Nat)
    (hy : ys ∈ chop 5 [0, 1, 2, 3, 4, 5, 6]) : ys ≠ [] ∧ ys.length ≤ 5 :=
  ⟨chop_mem_ne_nil _ _ _ hy, length_mem_chop _ _ _ hy⟩

theorem aligned_append :
    chop 5 ([0, 0, 0, 1, 1] ++ [0, 1] : List Nat) =
      chop 5 [0, 0, 0, 1, 1] ++ chop 5 [0, 1] :=
  chop_append _ _ _ (by decide) (by decide)

/-- This symbolic family is consumed later by the strict seventy-percent
counterexample; it uses every natural number of complete blocks. -/
theorem repeated_five_blocks (n : Nat) :
    chop 5 (List.replicate n ([0, 0, 0, 1, 1] : List Nat)).flatten =
      List.replicate n [0, 0, 0, 1, 1] :=
  chop_replicate_blocks _ _ _ (by decide) rfl

theorem repeated_occurrences (n : Nat) :
    chop 5 (List.replicate (n * 5) true) = List.replicate n [true, true, true, true, true] :=
  chop_replicate 5 n true (by decide)

end Examples.ListChunks
