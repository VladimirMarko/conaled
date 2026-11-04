import Applications.Resources.Partition
import Applications.Selection.ThreeWay

/-! Connected cases for shared partition values and the actual source execution.
Buckets retain order and duplicate occurrences. Pivot membership is needed only
for the strict-size implication, and the source count includes the empty call.
Source and statement assessment: `docs/research/fdsa-three-way-partition.md`.
-/
set_option autoImplicit false
set_option warningAsError true

namespace ThreeWayPartitionExamples
universe u
variable {α : Type u} [LinearOrder α]

/-- Every copy of the supplied pivot stays in the equal bucket, including n = 0. -/
theorem replicate_partition (p : α) (n : Nat) :
    Sequences.Partition.partition3 p (List.replicate n p) =
      ([], List.replicate n p, []) := by
  induction n with
  | zero => exact Sequences.Partition.partition3_nil p
  | succ n ih =>
      rw [List.replicate_succ, Sequences.Partition.partition3_cons, ih]
      simp

/-- The old Selection operation remains the same public value interface. -/
theorem selection_partition (p : α) (xs : List α) :
    Applications.Selection.partition3 p xs = Sequences.Partition.partition3 p xs := rfl

/-- Both strict buckets display input order instead of sorted order. -/
def mixed : List Nat := [4, 1, 2, 0, 3, 2, 1, 4]

theorem mixed_partition :
    Sequences.Partition.partition3 2 mixed = ([1, 0, 1], [2, 2], [4, 3, 4]) :=
  Sequences.Partition.partition3_eq_filters 2 mixed

theorem outside_partition :
    Sequences.Partition.partition3 4 [3, 1, 3] = ([3, 1, 3], [], []) :=
  Sequences.Partition.partition3_eq_filters 4 [3, 1, 3]

theorem interior_partition :
    Sequences.Partition.partition3 2 [3, 1, 3, 1] = ([1, 1], [], [3, 3]) :=
  Sequences.Partition.partition3_eq_filters 2 [3, 1, 3, 1]

theorem lower_partition :
    Sequences.Partition.partition3 1 [1, 0, 1] = ([0], [1, 1], []) :=
  Sequences.Partition.partition3_eq_filters 1 [1, 0, 1]

/-- The final empty invocation is charged even when there are no input cells. -/
theorem empty_run (p : α) :
    Resources.Partition.partitionRun p [] = (([], [], []), 1) :=
  Resources.Partition.partitionRun_nil p

theorem replicate_run (p : α) (n : Nat) :
    Resources.Partition.partitionRun p (List.replicate n p) =
      (([], List.replicate n p, []), n + 1) := by
  apply Prod.ext
  · exact (Resources.Partition.partitionRun_value p (List.replicate n p)).trans
      (replicate_partition p n)
  · simpa only [List.length_replicate] using
      Resources.Partition.partitionRun_cost p (List.replicate n p)

theorem singleton_run (p : α) :
    Resources.Partition.partitionRun p [p] = (([], [p], []), 2) :=
  replicate_run p 1

/-- Only the positive-length instance supplies pivot membership for strict shrinking. -/
theorem replicate_strict (p : α) (n : Nat) (hn : 0 < n) :
    (Resources.Partition.partitionRun p (List.replicate n p)).1.1.length < n ∧
      (Resources.Partition.partitionRun p (List.replicate n p)).1.2.2.length < n := by
  have hp : p ∈ List.replicate n p := List.mem_replicate.mpr ⟨Nat.ne_of_gt hn, rfl⟩
  rw [Resources.Partition.partitionRun_value]
  simpa only [List.length_replicate] using
    Sequences.Partition.partition_strict_sizes p (List.replicate n p) hp

/-- The measured value also meets the preserved Selection-name interface. -/
theorem measured_selection_value (p : α) (xs : List α) :
    (Resources.Partition.partitionRun p xs).1 = Applications.Selection.partition3 p xs :=
  (Resources.Partition.partitionRun_value p xs).trans (selection_partition p xs).symm

theorem mixed_run :
    Resources.Partition.partitionRun 2 mixed = (([1, 0, 1], [2, 2], [4, 3, 4]), 9) :=
  Prod.ext ((Resources.Partition.partitionRun_value 2 mixed).trans mixed_partition)
    (Resources.Partition.partitionRun_cost 2 mixed)

theorem mixed_value :
    (Resources.Partition.partitionRun 2 mixed).1 = ([1, 0, 1], [2, 2], [4, 3, 4]) :=
  congrArg Prod.fst mixed_run

theorem mixed_cost : (Resources.Partition.partitionRun 2 mixed).2 = 9 :=
  congrArg Prod.snd mixed_run

/-- Grouping the buckets preserves occurrences, without preserving the original sequence. -/
theorem mixed_perm :
    let t := (Resources.Partition.partitionRun 2 mixed).1
    (t.1 ++ t.2.1 ++ t.2.2).Perm mixed := by
  dsimp only
  rw [Resources.Partition.partitionRun_value]
  exact Sequences.Partition.partition3_perm 2 mixed

theorem mixed_lengths :
    let t := (Resources.Partition.partitionRun 2 mixed).1
    t.1.length = 3 ∧ t.2.1.length = 2 ∧ t.2.2.length = 3 ∧
      t.1.length + t.2.1.length + t.2.2.length = 8 := by
  dsimp only
  refine ⟨congrArg (fun t : List Nat × List Nat × List Nat => t.1.length) mixed_value,
    congrArg (fun t : List Nat × List Nat × List Nat => t.2.1.length) mixed_value,
    congrArg (fun t : List Nat × List Nat × List Nat => t.2.2.length) mixed_value, ?_⟩
  calc
    _ = (Sequences.Partition.partition3 2 mixed).1.length +
        (Sequences.Partition.partition3 2 mixed).2.1.length +
        (Sequences.Partition.partition3 2 mixed).2.2.length :=
      congrArg (fun t : List Nat × List Nat × List Nat =>
        t.1.length + t.2.1.length + t.2.2.length)
        (Resources.Partition.partitionRun_value 2 mixed)
    _ = 8 := Sequences.Partition.partition_lengths 2 mixed

theorem mixed_strict :
    (Resources.Partition.partitionRun 2 mixed).1.1.length < 8 ∧
      (Resources.Partition.partitionRun 2 mixed).1.2.2.length < 8 := by
  rw [Resources.Partition.partitionRun_value]
  exact Sequences.Partition.partition_strict_sizes 2 mixed (by decide)

/-- An outside pivot is still a valid input to the partition operation. -/
theorem outside_run :
    Resources.Partition.partitionRun 4 [3, 1, 3] = (([3, 1, 3], [], []), 4) :=
  Prod.ext ((Resources.Partition.partitionRun_value 4 [3, 1, 3]).trans outside_partition)
    (Resources.Partition.partitionRun_cost 4 [3, 1, 3])

/-- The unchanged lower side refutes strict shrinking without a suitable premise. -/
theorem outside_boundary :
    4 ∉ ([3, 1, 3] : List Nat) ∧
      (Resources.Partition.partitionRun 4 [3, 1, 3]).1.1.length = 3 ∧
      ¬ (Resources.Partition.partitionRun 4 [3, 1, 3]).1.1.length < 3 := by
  rw [outside_run]
  decide

theorem interior_run :
    Resources.Partition.partitionRun 2 [3, 1, 3, 1] = (([1, 1], [], [3, 3]), 5) :=
  Prod.ext ((Resources.Partition.partitionRun_value 2 [3, 1, 3, 1]).trans interior_partition)
    (Resources.Partition.partitionRun_cost 2 [3, 1, 3, 1])

/-- Pivot membership is sufficient, not necessary, for both strict sides to shrink. -/
theorem interior_boundary :
    2 ∉ ([3, 1, 3, 1] : List Nat) ∧
      (Resources.Partition.partitionRun 2 [3, 1, 3, 1]).1.2.1 = [] ∧
      (Resources.Partition.partitionRun 2 [3, 1, 3, 1]).1.1.length < 4 ∧
      (Resources.Partition.partitionRun 2 [3, 1, 3, 1]).1.2.2.length < 4 := by
  rw [interior_run]
  decide

/-- The second invocation receives the actual lower bucket of the first result.
Ordinary bind adds nine and four, with no additional wrapper entry. -/
theorem bind_returned_lower :
    Resources.bind (Resources.Partition.partitionRun 2 mixed)
      (fun t => Resources.Partition.partitionRun 1 t.1) = (([0], [1, 1], []), 13) := by
  have next : Resources.Partition.partitionRun 1 [1, 0, 1] = (([0], [1, 1], []), 4) :=
    Prod.ext ((Resources.Partition.partitionRun_value 1 [1, 0, 1]).trans lower_partition)
      (Resources.Partition.partitionRun_cost 1 [1, 0, 1])
  calc
    Resources.bind (Resources.Partition.partitionRun 2 mixed)
        (fun t => Resources.Partition.partitionRun 1 t.1) =
        Resources.bind ((([1, 0, 1], [2, 2], [4, 3, 4]), 9) :
          Resources.Measured (List Nat × List Nat × List Nat) Nat)
          (fun t => Resources.Partition.partitionRun 1 t.1) :=
      congrArg (fun r : Resources.Measured (List Nat × List Nat × List Nat) Nat =>
        Resources.bind r (fun t => Resources.Partition.partitionRun 1 t.1)) mixed_run
    _ = (([0], [1, 1], []), 13) :=
      congrArg (fun r : Resources.Measured (List Nat × List Nat × List Nat) Nat =>
        (r.1, 9 + r.2)) next

end ThreeWayPartitionExamples
