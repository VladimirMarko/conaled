import Mathlib.Data.List.Perm.Basic
import Mathlib.Order.Defs.LinearOrder

/-! Ordered three-way partition values shared by sorting and selection.
The existing two-stage operation is kept separate from any measured source
realization. Each bucket retains input order and every repeated occurrence.
Source and statement assessment: `docs/research/fdsa-three-way-partition.md`.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Sequences.Partition
universe u
variable {α : Type u} [LinearOrder α]

/-- Standard stable partitions retain every equal occurrence in input order. -/
def partition3 (p : α) (xs : List α) : List α × List α × List α :=
  let sides := xs.partition (fun x => decide (x < p))
  let upper := sides.2.partition (fun x => decide (x = p))
  (sides.1, upper.1, upper.2)

theorem partition3_eq_filters (p : α) (xs : List α) :
    partition3 p xs = (xs.filter (fun x => decide (x < p)),
      xs.filter (fun x => decide (x = p)), xs.filter (fun x => decide (p < x))) := by
  simp only [partition3, List.partition_eq_filter_filter, List.filter_filter]
  congr 2 <;> apply List.filter_congr <;> intro x hx <;>
    apply Bool.eq_iff_iff.mpr <;>
    simp only [Function.comp_def, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
      decide_eq_true_eq] <;> constructor <;> intro h
  · exact h.1
  · subst x; simp
  · exact lt_of_le_of_ne (le_of_not_gt h.2) (Ne.symm h.1)
  · exact ⟨ne_of_gt h, not_lt_of_gt h⟩

theorem partition3_perm (p : α) (xs : List α) :
    ((partition3 p xs).1 ++ (partition3 p xs).2.1 ++ (partition3 p xs).2.2).Perm xs := by
  simp only [partition3, List.partition_eq_filter_filter]
  rw [List.append_assoc]
  exact (List.Perm.append_left _ (List.filter_append_perm _ _)).trans
    (List.filter_append_perm _ _)

theorem partition_left_mem (p : α) (xs : List α) (x : α) :
    x∈(partition3 p xs).1 ↔ x∈xs ∧ x<p := by
  simp [partition3_eq_filters]

theorem partition_equal_mem (p : α) (xs : List α) (x : α) :
    x∈(partition3 p xs).2.1 ↔ x∈xs ∧ x=p := by
  simp [partition3_eq_filters]

theorem partition_right_mem (p : α) (xs : List α) (x : α) :
    x∈(partition3 p xs).2.2 ↔ x∈xs ∧ p<x := by
  simp [partition3_eq_filters]

theorem partition_lengths (p : α) (xs : List α) :
    (partition3 p xs).1.length+(partition3 p xs).2.1.length+
      (partition3 p xs).2.2.length=xs.length := by
  simpa [Nat.add_assoc] using (partition3_perm p xs).length_eq

theorem partition_strict_sizes (p : α) (xs : List α) (hp : p∈xs) :
    (partition3 p xs).1.length<xs.length ∧
      (partition3 p xs).2.2.length<xs.length := by
  have he : p∈(partition3 p xs).2.1 := (partition_equal_mem p xs p).mpr ⟨hp,rfl⟩
  have hn : 0<(partition3 p xs).2.1.length := List.length_pos_iff.mpr (List.ne_nil_of_mem he)
  have hl:=partition_lengths p xs
  omega

/-- The existing value operation returns three empty buckets on an empty input. -/
@[simp] theorem partition3_nil (p : α) : partition3 p [] = ([], [], []) :=
  partition3_eq_filters p []

/-- The source head step, proved about the existing two-stage value operation.
It does not assign a one-pass resource observation to that operation. -/
theorem partition3_cons (p y : α) (ys : List α) :
    partition3 p (y :: ys) =
      let t := partition3 p ys
      if y < p then (y :: t.1, t.2.1, t.2.2)
      else if p = y then (t.1, y :: t.2.1, t.2.2)
      else (t.1, t.2.1, y :: t.2.2) := by
  by_cases hlt : y < p
  · simp [partition3_eq_filters, List.filter_cons, hlt, ne_of_lt hlt, not_lt_of_gt hlt]
  · by_cases heq : p = y
    · subst y
      simp [partition3_eq_filters, List.filter_cons]
    · have hgt : p < y := lt_of_le_of_ne (le_of_not_gt hlt) heq
      simp [partition3_eq_filters, List.filter_cons, hlt, heq, Ne.symm heq, hgt]

end Sequences.Partition
