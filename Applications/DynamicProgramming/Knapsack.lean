import Applications.DynamicProgramming.Batch

/-! The 0/1 knapsack value recurrence. Each item consumes one immutable row;
ascending writes cannot reuse that item. Selection witnesses are separate work. -/
namespace DynamicProgramming.Knapsack

structure Item where
  weight : Nat
  value : Nat
  deriving DecidableEq, Repr

def next (item : Item) (old : Nat → Nat) (capacity : Nat) : Nat :=
  if capacity < item.weight then old capacity
  else max (old capacity) (item.value + old (capacity - item.weight))

def value : List Item → Nat → Nat
  | [], _ => 0
  | item :: items, capacity => next item (value items) capacity

def associations (item : Item) (old : Array Nat) : List (Nat × Nat) :=
  (List.range old.size).map (fun j => (j, next item (fun k => old[k]?.getD 0) j))

def step (item : Item) (old : Array Nat) : Array Nat :=
  arrayAssign old (associations item old)

theorem step_batch (item : Item) (old : Array Nat) :
    ArrayBatch old (step item old) (associations item old) := by
  apply arrayAssign_batch
  · simpa [associations, List.map_map, Function.comp_def] using List.nodup_range (n := old.size)
  · intro p hp
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hp
    exact List.mem_range.mp hj

theorem step_entry (item : Item) (old : Array Nat) (j : Nat) (hj : j < old.size) :
    (step item old)[j]? = some (next item (fun k => old[k]?.getD 0) j) :=
  (step_batch item old).2.1 _ _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)

def table (capacity : Nat) : List Item → Array Nat
  | [] => (List.replicate (capacity + 1) 0).toArray
  | item :: items => step item (table capacity items)

theorem table_size (capacity : Nat) (items : List Item) :
    (table capacity items).size = capacity + 1 := by
  induction items with
  | nil => simp [table]
  | cons item items ih => exact (step_batch item _).1.trans ih

theorem table_entry (capacity : Nat) (items : List Item) (j : Nat) (hj : j ≤ capacity) :
    (table capacity items)[j]? = some (value items j) := by
  induction items generalizing j with
  | nil =>
    simp only [table, value, List.getElem?_toArray,
      List.getElem?_replicate_of_lt (by omega : j < capacity + 1)]
  | cons item items ih =>
    rw [table, step_entry item _ j (by rw [table_size]; omega)]
    simp only [value, next]
    rw [ih j hj]
    simp only [Option.getD_some]
    split
    · rfl
    · rw [ih (j - item.weight) (by omega)]
      rfl

/-- A weight-one item is usable once even though the capacity is two. -/
theorem one_item_once : (table 2 [⟨1, 7⟩])[2]? = some 7 := by
  rw [table_entry 2 _ 2 (by omega)]
  rfl

end DynamicProgramming.Knapsack
