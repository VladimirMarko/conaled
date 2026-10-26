import Applications.Resources.Measured
import Applications.Optimization.KnapsackThinning

/-! Source 0/1-knapsack row instrumentation. The first three observations are
weight tests, value comparisons and update calls. The fourth is the conservative
unit-scalar tariff of KnapsackWork, including an explicit immutable bulk copy.
Every candidate reads the same old row; writes cannot reuse the current item.
No allocation, mutable-runtime or full optimum theorem is asserted here. -/
namespace Resources.Knapsack
open Optimization.KnapsackThinning
variable {α : Type}
abbrev Work := Nat × Nat × Nat × Nat

def better (s t : Selection α) : Selection α := if t.value ≤ s.value then s else t

def read (old : Array (Selection α)) (j : Nat) : Selection α := old[j]?.getD emptySelection

def next (i : Item α) (old : Array (Selection α)) (j : Nat) : Selection α :=
  if j < i.weight then read old j else better (read old j) (add i (read old (j-i.weight)))

def nextMeasured (i : Item α) (old : Array (Selection α)) (j : Nat) : Measured (Selection α) Work :=
  if j < i.weight then (read old j, (1,0,0,7))
  else (better (read old j) (add i (read old (j-i.weight))), (1,1,0,30))

def fits (weight : Nat) (indices : List Nat) : Nat :=
  (indices.map (fun j => if j < weight then 0 else 1)).sum

def entries (i : Item α) (old : Array (Selection α)) : List Nat → Measured (List (Nat × Selection α)) Work
  | [] => ([], (0,0,0,1))
  | j :: js => bind (nextMeasured i old j) fun s =>
      bind (entries i old js) fun rest => ((j,s)::rest, (0,0,0,3))

/-- Source association-pair construction costs one and source map cons/case
costs two; its terminal case costs one. -/
theorem entries_exact (i : Item α) (old : Array (Selection α)) (indices : List Nat) :
    entries i old indices =
      (indices.map (fun j => (j, next i old j)),
       (indices.length, fits i.weight indices, 0,
        10 * indices.length + 23 * fits i.weight indices + 1)) := by
  induction indices with
  | nil => rfl
  | cons j js ih =>
    by_cases hj : j < i.weight
    · simp [entries, nextMeasured, next, bind, ih, fits, hj, Nat.mul_add]
      omega
    · simp [entries, nextMeasured, next, bind, ih, fits, hj, Nat.mul_add]
      omega

def assign (old : Array (Selection α)) (updates : List (Nat × Selection α)) : Array (Selection α) :=
  updates.foldl (fun a p => a.setIfInBounds p.1 p.2) old

def writes (old : Array (Selection α)) : List (Nat × Selection α) → Measured (Array (Selection α)) Work
  | [] => (old, (0,0,0,1))
  | p :: ps => bind (old.setIfInBounds p.1 p.2, (0,0,1,8)) fun updated => writes updated ps

theorem writes_exact (old : Array (Selection α)) (updates : List (Nat × Selection α)) :
    writes old updates = (assign old updates, (0,0,updates.length,8*updates.length+1)) := by
  induction updates generalizing old with
  | nil => rfl
  | cons p ps ih => simp [writes, bind, ih, assign, Nat.mul_add, Nat.add_comm, Nat.add_left_comm]

def copy (old : Array (Selection α)) : Measured (Array (Selection α)) Work :=
  (old.toList.toArray, (0,0,0,2*old.size+1))

def step (capacity : Nat) (i : Item α) (old : Array (Selection α)) : Array (Selection α) :=
  assign old ((List.range (capacity+1)).map (fun j => (j, next i old j)))

def stepMeasured (capacity : Nat) (i : Item α) (old : Array (Selection α)) : Measured (Array (Selection α)) Work :=
  bind (entries i old (List.range (capacity+1))) fun updates =>
    bind (copy old) fun fresh =>
      bind (writes fresh updates) fun out => (out, (0,0,0,3*(capacity+1)+6))

theorem fits_range (weight count : Nat) : fits weight (List.range count) = count-weight := by
  induction count with
  | zero => simp [fits]
  | succ count ih =>
    simp only [List.range_succ, fits, List.map_append, List.sum_append,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] at ih ⊢
    rw [ih]
    split <;> omega

/-- Exact source multi-counter row plus the conservative full scalar tariff.
The copy contribution is 2*old.size+1 even when few capacities fit. -/
theorem stepMeasured_exact (capacity : Nat) (i : Item α) (old : Array (Selection α)) :
    stepMeasured capacity i old =
      (step capacity i old,
       (capacity+1, capacity+1-i.weight, capacity+1,
        21*(capacity+1)+23*(capacity+1-i.weight)+2*old.size+9)) := by
  simp [stepMeasured, entries_exact, writes_exact, bind, copy, step, fits_range,
    Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  omega

theorem stepMeasured_value (capacity : Nat) (i : Item α) (old : Array (Selection α)) :
    (stepMeasured capacity i old).1 = step capacity i old := by rw [stepMeasured_exact]

theorem stepMeasured_bound (capacity : Nat) (i : Item α) (old : Array (Selection α))
    (hs : old.size = capacity+1) :
    (stepMeasured capacity i old).2.2.2.2 ≤ 50*(capacity+1)+10 := by
  rw [stepMeasured_exact]
  simp only
  rw [hs]
  omega

end Resources.Knapsack
