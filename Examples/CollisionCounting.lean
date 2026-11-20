import Applications.Search.Collisions.Representations

/-!
# Connected collision-counting cases

Each expected value comes from occurrences minus distinct keys. Three equal
occurrences have two repeats, not three equal pairs. Source numeral lists retain
their own Nat, signed-binary, and positive-binary labels. The shifted encoding
is exhibited separately. No statement here asserts native execution costs.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Examples.CollisionCounting

open Search
open Search.Collisions

universe u v

/-- This was the first worked obligation for the generic correctness theorem. -/
theorem three_repeats {κ : Type u} {T : Type v} (ops : TotalTable.Ops κ Bool T)
    (Valid : T → Prop) (laws : TotalTable.Laws ops false Valid) (key : κ) :
    Collisions.collisions ops [key, key, key] = 2 := by
  classical
  rw [Collisions.collisions_correct laws]
  change count (List.replicate 3 key) = 2
  exact count_replicate key 3

theorem empty_input {κ : Type u} {T : Type v} (ops : TotalTable.Ops κ Bool T)
    (Valid : T → Prop) (laws : TotalTable.Laws ops false Valid) :
    Collisions.collisions ops [] = 0 := by
  classical
  rw [Collisions.collisions_correct laws]
  rfl

theorem distinct_input {κ : Type u} {T : Type v} [DecidableEq κ]
    (ops : TotalTable.Ops κ Bool T) (Valid : T → Prop)
    (laws : TotalTable.Laws ops false Valid) (xs : List κ) (distinct : xs.Nodup) :
    Collisions.collisions ops xs = 0 := by
  rw [Collisions.collisions_correct laws]
  exact count_nodup distinct

/-- Two further reads of a previously marked key both increment the counter. -/
theorem initial_seen_twice {κ : Type u} {T : Type v} (ops : TotalTable.Ops κ Bool T)
    (Valid : T → Prop) (laws : TotalTable.Laws ops false Valid) (key : κ) (c : Nat) :
    Collisions.loop ops [key, key] c (ops.set key true ops.empty) = c + 2 := by
  classical
  have h := (run_spec laws [key, key] c (laws.set_valid key true ops.empty laws.empty_valid)
    (seen_set laws laws.empty_valid (seen_empty laws) key)).2.2
  simp at h
  change (run ops [key, key] (c, ops.set key true ops.empty)).1 = c + 2
  omega

/-- A true marker takes the increment branch without a further write. -/
theorem duplicate_keeps_table {κ : Type u} {T : Type v} (ops : TotalTable.Ops κ Bool T)
    (Valid : T → Prop) (laws : TotalTable.Laws ops false Valid) (key : κ) (c : Nat)
    (table : T) (valid : Valid table) :
    step ops (c, ops.set key true table) key = (c + 1, ops.set key true table) := by
  simp only [step, laws.get_set_same key true table valid, ↓reduceIte]

/-- A false overwrite is fresh for this Boolean-marker algorithm, even though
there was an explicit write. Optional binding presence is not its observation. -/
theorem overwritten_false_is_fresh {κ : Type u} {T : Type v}
    (ops : TotalTable.Ops κ Bool T) (Valid : T → Prop)
    (laws : TotalTable.Laws ops false Valid) (key : κ) (c : Nat)
    (table : T) (valid : Valid table) :
    step ops (c, ops.set key false table) key =
      (c, ops.set key true (ops.set key false table)) := by
  simp only [step, laws.get_set_same key false table valid, Bool.false_eq_true, ↓reduceIte]

/-- Eight occurrences and seven distinct natural keys. -/
theorem verySlow_pi : VerySlow.collisions [3, 1, 4, 1, 5, 9, 2, 6] = 1 := by
  rw [VerySlow.collisions_correct]
  decide

/-- The same source numerals in the signed-binary carrier. -/
theorem ratherSlow_pi : RatherSlow.collisions [3, 1, 4, 1, 5, 9, 2, 6] = 1 := by
  apply ZNum.to_int_inj.mp
  rw [RatherSlow.collisions_correct]
  decide

/-- These are literal positive numerals, not encodings of the Nat pi list. -/
theorem fastEnough_pi : FastEnough.collisions [3, 1, 4, 1, 5, 9, 2, 6] = 1 := by
  rw [FastEnough.collisions_correct]
  decide

theorem signed_negative_keys : RatherSlow.collisions [-2, 0, 4, -2, 4] = 2 := by
  apply ZNum.to_int_inj.mp
  rw [RatherSlow.collisions_correct]
  decide

/-- A negative initial counter is allowed; two duplicate increments take
minus five to minus three. -/
theorem signed_initial_offset :
    RatherSlow.loop [-2, -2, -2] (-5) (RatherSlow.empty false) = -3 := by
  apply ZNum.to_int_inj.mp
  rw [RatherSlow.loop_common]
  change (-5 : Int) +
    (Collisions.collisions (TotalTable.functions false) ([-2, -2, -2] : List ZNum) : Int) = -3
  rw [Collisions.collisions_correct (TotalTable.functions_laws false)]
  decide

/-- An unrestricted constant-true starting function has infinite support.
The arbitrary-table theorem still applies and all three reads increment. -/
theorem all_true_initial_function :
    RatherSlow.loop [-8, 5, -8] (-5) (fun _ => true) = -2 := by
  apply ZNum.to_int_inj.mp
  rw [RatherSlow.loop_common]
  change (-5 : Int) +
    (Collisions.loop (TotalTable.functions false) ([-8, 5, -8] : List ZNum) 0 (fun _ => true) : Int) = -2
  simp only [Collisions.loop_cons, Collisions.loop_nil, TotalTable.functions, ↓reduceIte]
  decide

theorem signed_prefix_nonnegative (xs : List ZNum) :
    0 ≤ (RatherSlow.loop xs 0 (RatherSlow.empty false) : Int) :=
  RatherSlow.zero_start_nonnegative xs (RatherSlow.empty false)

/-- Erasing key distinctions can create repetitions. -/
theorem noninjective_relabeling_changes_result :
    VerySlow.collisions (([0, 1] : List Nat).map (fun _ => 0)) = 1 ∧
      VerySlow.collisions [0, 1] = 0 := by
  simp only [VerySlow.collisions_correct]
  decide

theorem numeric_distinct_trie (xs : List PosNum)
    (distinct : (xs.map Numerals.PositiveKeys.numeric).Nodup) :
    FastEnough.collisions xs = 0 := by
  rw [FastEnough.collisions_numeric, VerySlow.collisions_correct]
  exact count_nodup distinct

theorem encoded_nat_client (xs : List Nat) :
    FastEnough.collisions (xs.map Numerals.PositiveKeys.encode) = count xs := by
  rw [FastEnough.collisions_encode, VerySlow.collisions_correct]

theorem encoded_pi_numeric_labels :
    ((([3, 1, 4, 1, 5, 9, 2, 6] : List Nat).map Numerals.PositiveKeys.encode).map
      Numerals.PositiveKeys.numeric) = [4, 2, 5, 2, 6, 10, 3, 7] := by
  simp only [List.map_cons, List.map_nil, Numerals.PositiveKeys.numeric_encode]

/-- With positive3 and10 initially marked, the queries3,10,3 increment three
times and4 is fresh. The shifted function proof uses Nat2 and9 for the marks. -/
theorem seeded_trie_abstraction :
    FastEnough.loop [3, 10, 3, 4] 5
      (PositiveTrie.insert 3 true (PositiveTrie.insert 10 true (PositiveTrie.empty false))) = 8 := by
  rw [FastEnough.loop_abstract, PositiveTrie.abstract_insert,
    PositiveTrie.abstract_insert, PositiveTrie.abstract_empty]
  decide

end Examples.CollisionCounting
