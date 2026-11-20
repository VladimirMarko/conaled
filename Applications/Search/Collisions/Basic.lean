import Applications.Search.OrderedMap.TotalTable
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Dedup

/-!
# Counting repeated occurrences through total tables

The executable client queries before writing: an already-seen key increments
the counter without changing the table; a fresh key writes `true` without
incrementing. Operations do not carry validity or finite-support assumptions.
The independent answer counts occurrences after the first, not equal pairs.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Search.Collisions

universe u v w z
variable {κ : Type u} {ι : Type v} {T : Type w} {U : Type z}

/-- Independent finite-list specification. Deduplication order is immaterial. -/
def count [DecidableEq κ] (xs : List κ) : Nat := xs.length - xs.dedup.length

/-- One source query, followed by exactly one of increment or write. -/
def step (ops : TotalTable.Ops κ Bool T) (state : Nat × T) (key : κ) : Nat × T :=
  if ops.get key state.2 then (state.1 + 1, state.2)
  else (state.1, ops.set key true state.2)

/-- Keep the actual final table as well as the collision counter. -/
def run (ops : TotalTable.Ops κ Bool T) (xs : List κ) (state : Nat × T) : Nat × T :=
  xs.foldl (step ops) state

/-- The source result discards only the final table. -/
def loop (ops : TotalTable.Ops κ Bool T) (xs : List κ) (c : Nat) (table : T) : Nat :=
  (run ops xs (c, table)).1

def collisions (ops : TotalTable.Ops κ Bool T) (xs : List κ) : Nat :=
  loop ops xs 0 ops.empty

@[simp] theorem run_nil (ops : TotalTable.Ops κ Bool T) (state : Nat × T) :
    run ops [] state = state := rfl

theorem run_cons (ops : TotalTable.Ops κ Bool T) (key : κ) (xs : List κ)
    (state : Nat × T) :
    run ops (key :: xs) state = run ops xs (step ops state key) := rfl

@[simp] theorem loop_nil (ops : TotalTable.Ops κ Bool T) (c : Nat) (table : T) :
    loop ops [] c table = c := rfl

theorem loop_cons (ops : TotalTable.Ops κ Bool T) (key : κ) (xs : List κ)
    (c : Nat) (table : T) :
    loop ops (key :: xs) c table =
      if ops.get key table then loop ops xs (c + 1) table
      else loop ops xs c (ops.set key true table) := by
  cases h : ops.get key table <;> simp [loop, run, List.foldl, step, h]

/-- Chronological composition uses the ordinary list fold. -/
theorem run_append (ops : TotalTable.Ops κ Bool T) (xs ys : List κ)
    (state : Nat × T) :
    run ops (xs ++ ys) state = run ops ys (run ops xs state) := by
  exact List.foldl_append

/-- An arbitrary starting counter is an offset; no table laws are needed. -/
theorem loop_add (ops : TotalTable.Ops κ Bool T) (xs : List κ) (c n : Nat)
    (table : T) : loop ops xs (c + n) table = c + loop ops xs n table := by
  induction xs generalizing n table with
  | nil => rfl
  | cons key xs ih =>
      rw [loop_cons, loop_cons]
      split
      · simpa only [Nat.add_assoc] using ih (n + 1) table
      · exact ih n (ops.set key true table)

/-- Each list element contributes either zero or one, even for an arbitrary
initial Boolean function with infinite support. -/
theorem loop_bounds (ops : TotalTable.Ops κ Bool T) (xs : List κ) (c : Nat)
    (table : T) : c ≤ loop ops xs c table ∧ loop ops xs c table ≤ c + xs.length := by
  induction xs generalizing c table with
  | nil => simp
  | cons key xs ih =>
      rw [loop_cons]
      split
      · have h := ih (c + 1) table
        simp only [List.length_cons]
        omega
      · have h := ih c (ops.set key true table)
        simp only [List.length_cons]
        omega

theorem run_valid {ops : TotalTable.Ops κ Bool T} {default : Bool} {Valid : T → Prop}
    (laws : TotalTable.Laws ops default Valid) (xs : List κ) (c : Nat)
    {table : T} (valid : Valid table) : Valid (run ops xs (c, table)).2 := by
  induction xs generalizing c table with
  | nil => exact valid
  | cons key xs ih =>
      rw [run_cons]
      cases h : ops.get key table <;> simp only [step, h, Bool.false_eq_true, ↓reduceIte]
      · exact ih c (laws.set_valid key true table valid)
      · exact ih (c + 1) valid

/-- Corresponding arbitrary initial tables remain observationally equal and
produce the same counter. No finite witness or key equality decision is needed. -/
theorem run_agrees {a : TotalTable.Ops κ Bool T} {b : TotalTable.Ops κ Bool U}
    {d e : Bool} {P : T → Prop} {Q : U → Prop}
    (ha : TotalTable.Laws a d P) (hb : TotalTable.Laws b e Q)
    (xs : List κ) (c : Nat) {table : T} {other : U}
    (ht : P table) (hs : Q other)
    (same : TotalTable.observe a table = TotalTable.observe b other) :
    (run a xs (c, table)).1 = (run b xs (c, other)).1 ∧
      TotalTable.observe a (run a xs (c, table)).2 =
        TotalTable.observe b (run b xs (c, other)).2 := by
  induction xs generalizing c table other with
  | nil => exact ⟨rfl, same⟩
  | cons key xs ih =>
      have get_same : a.get key table = b.get key other := congrFun same key
      rw [run_cons, run_cons]
      cases h : a.get key table
      · have other_get : b.get key other = false := get_same.symm.trans h
        simp only [step, h, other_get, Bool.false_eq_true, ↓reduceIte]
        apply ih c (ha.set_valid key true table ht) (hb.set_valid key true other hs)
        simpa only [TotalTable.setAll] using
          ha.setAll_agrees hb [(key, true)] ht hs same
      · have other_get : b.get key other = true := get_same.symm.trans h
        simp only [step, h, other_get, ↓reduceIte]
        exact ih (c + 1) ht hs same

theorem loop_agrees {a : TotalTable.Ops κ Bool T} {b : TotalTable.Ops κ Bool U}
    {d e : Bool} {P : T → Prop} {Q : U → Prop}
    (ha : TotalTable.Laws a d P) (hb : TotalTable.Laws b e Q)
    (xs : List κ) (c : Nat) {table : T} {other : U}
    (ht : P table) (hs : Q other)
    (same : TotalTable.observe a table = TotalTable.observe b other) :
    loop a xs c table = loop b xs c other :=
  (run_agrees ha hb xs c ht hs same).1

/-- Injective key transport preserves the loop for corresponding arbitrary
initial tables. Values at target keys outside the image are unrestricted. -/
theorem loop_reindex {a : TotalTable.Ops κ Bool T} {b : TotalTable.Ops ι Bool U}
    {d e : Bool} {P : T → Prop} {Q : U → Prop}
    (ha : TotalTable.Laws a d P) (hb : TotalTable.Laws b e Q)
    (f : κ → ι) (injective : Function.Injective f) (xs : List κ) (c : Nat)
    {table : T} {other : U} (ht : P table) (hs : Q other)
    (same : ∀ key, a.get key table = b.get (f key) other) :
    loop a xs c table = loop b (xs.map f) c other := by
  induction xs generalizing c table other with
  | nil => rfl
  | cons key xs ih =>
      rw [List.map_cons, loop_cons, loop_cons, ← same key]
      split
      · exact ih (c + 1) ht hs same
      · apply ih c (ha.set_valid key true table ht) (hb.set_valid (f key) true other hs)
        intro query
        by_cases h : key = query
        · subst query
          rw [ha.get_set_same key true table ht, hb.get_set_same (f key) true other hs]
        · rw [ha.get_set_other key query true table h ht,
            hb.get_set_other (f key) (f query) true other (fun eq => h (injective eq)) hs]
          exact same query

/-- A finite seen-key witness is a proof invariant, not part of the operations
or an assertion that every total Boolean function has finite support. -/
def Seen [DecidableEq κ] (ops : TotalTable.Ops κ Bool T) (keys : Finset κ)
    (table : T) : Prop := ∀ key, ops.get key table = decide (key ∈ keys)

theorem seen_empty [DecidableEq κ] {ops : TotalTable.Ops κ Bool T} {Valid : T → Prop}
    (laws : TotalTable.Laws ops false Valid) : Seen ops ∅ ops.empty := by
  intro key
  simpa using laws.get_empty key

theorem seen_set [DecidableEq κ] {ops : TotalTable.Ops κ Bool T} {Valid : T → Prop}
    (laws : TotalTable.Laws ops false Valid) {keys : Finset κ} {table : T}
    (valid : Valid table) (seen : Seen ops keys table) (key : κ) :
    Seen ops (insert key keys) (ops.set key true table) := by
  intro query
  by_cases h : query = key
  · subst query
    simpa using laws.get_set_same key true table valid
  · rw [laws.get_set_other key query true table (Ne.symm h) valid, seen query]
    simp [h]

/-- Finite-prefix conservation: every occurrence either increases the counter
or increases the number of seen keys by one. The initial counter is arbitrary. -/
theorem run_spec [DecidableEq κ] {ops : TotalTable.Ops κ Bool T} {Valid : T → Prop}
    (laws : TotalTable.Laws ops false Valid) (xs : List κ) (c : Nat)
    {table : T} {keys : Finset κ} (valid : Valid table) (seen : Seen ops keys table) :
    Valid (run ops xs (c, table)).2 ∧
      Seen ops (keys ∪ xs.toFinset) (run ops xs (c, table)).2 ∧
      (run ops xs (c, table)).1 + (keys ∪ xs.toFinset).card =
        c + xs.length + keys.card := by
  induction xs generalizing c table keys with
  | nil => simpa using And.intro valid (And.intro seen (rfl : c + keys.card = c + keys.card))
  | cons key xs ih =>
      by_cases hk : key ∈ keys
      · have get_true : ops.get key table = true := by simpa [hk] using seen key
        have union_eq : keys ∪ (key :: xs).toFinset = keys ∪ xs.toFinset := by
          rw [List.toFinset_cons, Finset.union_insert,
            Finset.insert_eq_of_mem (Finset.mem_union_left _ hk)]
        rw [run_cons, union_eq]
        simp only [step, get_true, ↓reduceIte]
        obtain ⟨hv, hs, hc⟩ := ih (c + 1) valid seen
        refine ⟨hv, hs, ?_⟩
        simp only [List.length_cons]
        omega
      · have get_false : ops.get key table = false := by simpa [hk] using seen key
        rw [run_cons]
        simp only [step, get_false, Bool.false_eq_true, ↓reduceIte,
          List.toFinset_cons, Finset.union_insert, ← Finset.insert_union]
        obtain ⟨hv, hs, hc⟩ := ih c (laws.set_valid key true table valid)
          (seen_set laws valid seen key)
        refine ⟨hv, hs, ?_⟩
        rw [Finset.card_insert_of_notMem hk] at hc
        simp only [List.length_cons]
        omega

/-- Every processed prefix has exactly its own finite seen set and independent
repetition count. No property of later input is required. -/
theorem run_from_empty [DecidableEq κ] {ops : TotalTable.Ops κ Bool T} {Valid : T → Prop}
    (laws : TotalTable.Laws ops false Valid) (xs : List κ) (c : Nat) :
    Valid (run ops xs (c, ops.empty)).2 ∧
      Seen ops xs.toFinset (run ops xs (c, ops.empty)).2 ∧
      (run ops xs (c, ops.empty)).1 = c + count xs := by
  obtain ⟨hv, hs, hc⟩ := run_spec laws xs c laws.empty_valid (seen_empty laws)
  simp only [Finset.empty_union, Finset.card_empty, Nat.add_zero] at hs hc
  refine ⟨hv, hs, ?_⟩
  rw [List.card_toFinset] at hc
  have hle := (List.dedup_sublist xs).length_le
  unfold count
  omega

theorem collisions_correct [DecidableEq κ] {ops : TotalTable.Ops κ Bool T}
    {Valid : T → Prop} (laws : TotalTable.Laws ops false Valid) (xs : List κ) :
    collisions ops xs = count xs := by
  simpa only [collisions, loop, Nat.zero_add] using (run_from_empty laws xs 0).2.2

theorem prefix_seen [DecidableEq κ] {ops : TotalTable.Ops κ Bool T} {Valid : T → Prop}
    (laws : TotalTable.Laws ops false Valid) (xs : List κ) (c : Nat) (key : κ) :
    ops.get key (run ops xs (c, ops.empty)).2 = true ↔ key ∈ xs := by
  rw [(run_from_empty laws xs c).2.1 key]
  simp

/-- Relabeling may change every numeric label while preserving repetitions. -/
theorem count_map [DecidableEq κ] [DecidableEq ι] (f : κ → ι)
    (injective : Function.Injective f) (xs : List κ) : count (xs.map f) = count xs := by
  simp only [count, List.length_map, List.dedup_map_of_injective injective]

theorem count_nodup [DecidableEq κ] {xs : List κ} (nodup : xs.Nodup) : count xs = 0 := by
  simp [count, nodup.dedup]

theorem count_replicate [DecidableEq κ] (key : κ) (n : Nat) :
    count (List.replicate n key) = n - 1 := by
  cases n with
  | zero => simp [count]
  | succ n => simp [count, List.replicate_dedup (Nat.succ_ne_zero n)]

end Search.Collisions
