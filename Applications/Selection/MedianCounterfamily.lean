import Applications.Selection.MedianOfMedians

/-!
An infinite counterfamily for the exact seventy-percent claim, FDSA Exercise 3.7.

The final singleton zero is part of the actual chopped input. It gives the
list of chunk medians equally many zero and unit occurrences, whose lower
median is zero. Every input has positive length; the strict comparison is
expressed with integer counts, without rounding a percentage or dividing by
an input length. No distinctness assumption is made.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Applications.Selection.MedianCounterfamily
open Applications.Sequences.Chunks

def lowBlock : List Nat := [0, 0, 0, 1, 1]

def highBlock : List Nat := [1, 1, 1, 1, 1]

def fullBlocks (i : Nat) : List (List Nat) :=
  List.replicate i lowBlock ++ List.replicate (i + 1) highBlock

/-- The short final chunk contributes a zero median and no greater entry. -/
def family (i : Nat) : List Nat := (fullBlocks i).flatten ++ [0]

theorem fullBlocks_length (i : Nat) : (fullBlocks i).length = 2 * i + 1 := by
  simp only [fullBlocks, List.length_append, List.length_replicate]
  omega

theorem mem_fullBlocks_length (i : Nat) (ys : List Nat) (hy : ys ∈ fullBlocks i) :
    ys.length = 5 := by
  rcases List.mem_append.mp hy with hy | hy
  · rw [List.eq_of_mem_replicate hy]
    rfl
  · rw [List.eq_of_mem_replicate hy]
    rfl

theorem flatten_fullBlocks_length (i : Nat) :
    (fullBlocks i).flatten.length = 5 * (2 * i + 1) := by
  simp only [fullBlocks, List.length_flatten, List.map_append, List.map_replicate,
    List.sum_append, List.sum_replicate_nat]
  change i * 5 + (i + 1) * 5 = 5 * (2 * i + 1)
  omega

theorem family_length (i : Nat) : (family i).length = 10 * i + 6 := by
  simp only [family, List.length_append, flatten_fullBlocks_length,
    List.length_cons, List.length_nil]
  omega

theorem family_positive (i : Nat) : 0 < (family i).length := by
  rw [family_length]
  omega

theorem family_ne_nil (i : Nat) : family i ≠ [] :=
  List.ne_nil_of_length_pos (family_positive i)

theorem family_lengths_strictMono : StrictMono (fun i => (family i).length) := by
  intro i j hij
  change (family i).length < (family j).length
  rw [family_length, family_length]
  omega

/-- Both full-block alignment and the final singleton are preserved by chop. -/
theorem chop_family (i : Nat) : chop 5 (family i) = fullBlocks i ++ [[0]] := by
  have ha : 5 ∣ (fullBlocks i).flatten.length := by
    rw [flatten_fullBlocks_length]
    exact ⟨2 * i + 1, rfl⟩
  rw [family, chop_append 5 _ _ (by decide) ha,
    chop_flatten 5 (fullBlocks i) (by decide) (mem_fullBlocks_length i),
    chop_eq_singleton 5 ([0] : List Nat) (by decide) (by decide) (by decide)]

theorem lowBlock_median (h : lowBlock ≠ []) : lowerMedianValue lowBlock h = 0 :=
  (lowerMedianValue_ranked _ h).unique (ranked_iff_count_bounds.mpr (by decide))

theorem highBlock_median (h : highBlock ≠ []) : lowerMedianValue highBlock h = 1 :=
  (lowerMedianValue_ranked _ h).unique (ranked_iff_count_bounds.mpr (by decide))

theorem singleton_zero_median (h : ([0] : List Nat) ≠ []) :
    lowerMedianValue [0] h = 0 :=
  (lowerMedianValue_ranked _ h).unique (ranked_iff_count_bounds.mpr (by decide))

/-- The head equals the median only for these three nonempty block shapes.
The proof erases the attached membership certificates after establishing that
equality for every actual chunk; it does not replace the pivot policy by head. -/
theorem chunkMedians_family (i : Nat) :
    chunkMedians 5 (family i) =
      List.replicate i 0 ++ List.replicate (i + 1) 1 ++ [0] := by
  have hm (ys : List Nat) (hy : ys ∈ chop 5 (family i)) :
      lowerMedianValue ys (chop_mem_ne_nil 5 (family i) ys hy) = ys.headD 0 := by
    have hy' := hy
    rw [chop_family] at hy'
    rcases List.mem_append.mp hy' with hy' | hy'
    · rcases List.mem_append.mp hy' with hy' | hy'
      · have he : ys = lowBlock := List.eq_of_mem_replicate hy'
        subst ys
        exact lowBlock_median _
      · have he : ys = highBlock := List.eq_of_mem_replicate hy'
        subst ys
        exact highBlock_median _
    · have he : ys = [0] := List.mem_singleton.mp hy'
      subst ys
      exact singleton_zero_median _
  calc
    chunkMedians 5 (family i) =
        (chop 5 (family i)).attach.map (fun ys => ys.val.headD 0) := by
      unfold chunkMedians
      apply List.map_congr_left
      intro ys _
      exact hm ys.val ys.property
    _ = (chop 5 (family i)).map (fun ys : List Nat => ys.headD 0) :=
      List.attach_map_val (l := chop 5 (family i)) (f := fun ys : List Nat => ys.headD 0)
    _ = List.replicate i 0 ++ List.replicate (i + 1) 1 ++ [0] := by
      rw [chop_family]
      simp [fullBlocks, lowBlock, highBlock]

theorem chunkMedians_family_length (i : Nat) :
    (chunkMedians 5 (family i)).length = 2 * i + 2 := by
  rw [chunkMedians_family]
  simp only [List.length_append, List.length_replicate, List.length_cons, List.length_nil]
  omega

theorem chunkMedians_family_count_lt (i : Nat) :
    (chunkMedians 5 (family i)).countP (fun x => decide (x < 0)) = 0 := by
  simp

theorem chunkMedians_family_count_gt (i : Nat) :
    (chunkMedians 5 (family i)).countP (fun x => decide (0 < x)) = i + 1 := by
  rw [chunkMedians_family]
  simp [List.countP_replicate]

/-- The even median list selects its lower central zero occurrence. -/
theorem family_pivot (i : Nat) : medianOfMedians 5 (family i) = some 0 := by
  apply (medianOfMedians_some_iff_ranked 5 (family i) 0).mpr
  apply ranked_iff_count_bounds.mpr
  rw [chunkMedians_family_count_lt, chunkMedians_family_count_gt,
    chunkMedians_family_length]
  omega

theorem family_count_gt (i : Nat) :
    (family i).countP (fun x => decide (0 < x)) = 7 * i + 5 := by
  simp only [family, List.countP_append, List.countP_flatten, fullBlocks,
    List.map_append, List.map_replicate, List.sum_append, List.sum_replicate_nat]
  change i * 2 + (i + 1) * 5 + 0 = 7 * i + 5
  omega

/-- The integer comparison exceeds seventy percent by a fixed numerator of eight. -/
theorem family_excess (i : Nat) :
    10 * (family i).countP (fun x => decide (0 < x)) = 7 * (family i).length + 8 := by
  rw [family_count_gt, family_length]
  omega

theorem family_strict_seventy (i : Nat) :
    7 * (family i).length < 10 * (family i).countP (fun x => decide (0 < x)) := by
  have h := family_excess i
  omega

/-- Any successful pivot of this deterministic operation is the zero already
identified above, so the strict comparison is against its actual result. -/
theorem family_pivot_strict_seventy (i p : Nat)
    (hp : medianOfMedians 5 (family i) = some p) :
    7 * (family i).length < 10 * (family i).countP (fun x => decide (p < x)) := by
  have he : p = 0 := Option.some.inj (hp.symm.trans (family_pivot i))
  subst p
  exact family_strict_seventy i

/-- A single explicit function witnesses every index of the exercise. Positive
lengths make the integer inequality equivalent to the strict proportion claim. -/
theorem infinite_family :
    ∃ f : Nat → List Nat, StrictMono (fun i => (f i).length) ∧
      ∀ i, 0 < (f i).length ∧ ∃ p : Nat, medianOfMedians 5 (f i) = some p ∧
        7 * (f i).length < 10 * (f i).countP (fun x => decide (p < x)) :=
  ⟨family, family_lengths_strictMono, fun i =>
    ⟨family_positive i, 0, family_pivot i, family_strict_seventy i⟩⟩

end Applications.Selection.MedianCounterfamily
