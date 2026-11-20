import Applications.Search.BinomialQueue.Contract
import Applications.Representations.DecodedBinomialQueue
import Examples.MaximumQueueClients
import Examples.BinomialQueues

/-!
The accepted build/native-merge/two-removals client runs through both the source
list queue and the dense binomial queue. Separate machine clients connect the
literal source branches to signed integers and to checked textbook Nat inputs.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.BinomialQueueClients

open Search.BinomialQueue
open Search.MaximumQueue (encode)
open MaximumQueueClients
open Representations.DecodedBinomialQueue

abbrev binomial : Search.PriorityInterface.ExactQueue Unit (OrderDual Nat) := exactQueue

theorem native_merge_observation (p q : binomial.Carrier) :
    (binomial.entries (mergeValid p q)).Perm (binomial.entries p ++ binomial.entries q) :=
  mergeValid_entries p q

theorem binomial_build_occurrences (keys : List Nat) :
    (binomial.entries (build binomial keys)).Perm (keys.map encode) :=
  build_entries binomial keys

/-- Both native merges retain every input occurrence for arbitrary input lists. -/
theorem list_binomial_merge_occurrences (left right : List Nat) :
    (sourceList.entries (mergeBuilt sourceList Search.ListMaximumQueue.merge left right)).Perm
      (binomial.entries (mergeBuilt binomial mergeValid left right)) := by
  have listEntries := mergeBuilt_entries sourceList Search.ListMaximumQueue.merge
    (fun p q _ _ => sourceList_merge_entries p q) left right
  have heapEntries := mergeBuilt_entries binomial mergeValid
    (fun p q _ _ => native_merge_observation p q) left right
  exact listEntries.trans heapEntries.symm

theorem binomial_two_maxima :
    ∃ first second,
      binomial.remove (mergeBuilt binomial mergeValid [7, 2, 7] [7, 0]) =
        some (encode 7, first) ∧
      binomial.remove first = some (encode 7, second) ∧
      binomial.Valid first ∧ binomial.Valid second ∧
      (binomial.entries first).count (encode 7) = 2 ∧
      (binomial.entries second).Perm ([2, 7, 0].map encode) ∧
      (binomial.entries second).count (encode 7) = 1 :=
  two_maxima_client binomial mergeValid (fun p q _ _ => mergeValid_valid p q)
    (fun p q _ _ => native_merge_observation p q)

/-- The same client obtains two actual successes and identical residual
occurrences from the two different carriers. -/
theorem list_binomial_two_removals :
    ∃ listFirst listSecond heapFirst heapSecond,
      sourceList.remove (mergeBuilt sourceList Search.ListMaximumQueue.merge [7, 2, 7] [7, 0]) =
        some (encode 7, listFirst) ∧
      sourceList.remove listFirst = some (encode 7, listSecond) ∧
      binomial.remove (mergeBuilt binomial mergeValid [7, 2, 7] [7, 0]) =
        some (encode 7, heapFirst) ∧
      binomial.remove heapFirst = some (encode 7, heapSecond) ∧
      (sourceList.entries listSecond).Perm (binomial.entries heapSecond) ∧
      (sourceList.entries listSecond).count (encode 7) = 1 ∧
      (binomial.entries heapSecond).count (encode 7) = 1 := by
  obtain ⟨listFirst, listSecond, listRemove, listAgain, _, _, _, listObservation, listCount⟩ :=
    sourceList_two_maxima
  obtain ⟨heapFirst, heapSecond, heapRemove, heapAgain, _, _, _, heapObservation, heapCount⟩ :=
    binomial_two_maxima
  exact ⟨listFirst, listSecond, heapFirst, heapSecond, listRemove, listAgain, heapRemove, heapAgain,
    listObservation.trans heapObservation.symm, listCount, heapCount⟩

def leftVersion : binomial.Carrier := build binomial [7, 2, 7]
def rightVersion : binomial.Carrier := build binomial [7, 0]
def mergedVersion : binomial.Carrier := mergeValid leftVersion rightVersion

theorem old_left_version : (binomial.entries leftVersion).Perm ([7, 2, 7].map encode) :=
  build_entries binomial [7, 2, 7]

theorem old_right_version : (binomial.entries rightVersion).Perm ([7, 0].map encode) :=
  build_entries binomial [7, 0]

/-- The saved source values remain available alongside both returned residuals. -/
theorem persistent_versions_and_removals :
    (binomial.entries leftVersion).Perm ([7, 2, 7].map encode) ∧
    (binomial.entries rightVersion).Perm ([7, 0].map encode) ∧
    ∃ first second, binomial.remove mergedVersion = some (encode 7, first) ∧
      binomial.remove first = some (encode 7, second) ∧
      (binomial.entries second).count (encode 7) = 1 := by
  obtain ⟨first, second, hfirst, hsecond, _, _, _, _, hcount⟩ := binomial_two_maxima
  exact ⟨old_left_version, old_right_version, first, second, hfirst, hsecond, hcount⟩

theorem textbook_input_bounded : NatBounded BinomialQueues.sourceForest := by
  intro key hk
  have hperm := (queue_elems_iff _ _).mp BinomialQueues.source_fold_occurrences
  have hinput := hperm.mem_iff.mpr hk
  simp only [BinomialQueues.sourceInput, List.mem_cons, List.not_mem_nil, or_false] at hinput
  omega

theorem textbook_machine_deletion :
    (deleteMax int64Greater
      (mapQueue (fun n : Nat => Int64.ofInt n) BinomialQueues.sourceForest)).map
        (fun result => (result.1.toInt, mapQueue Int64.toInt result.2)) =
      (deleteMax natGreater BinomialQueues.sourceForest).map
        (fun result => ((result.1 : Int), mapQueue (fun n : Nat => (n : Int)) result.2)) :=
  nat_deleteMax_transport _ textbook_input_bounded

theorem textbook_machine_maximum :
    (findMax int64Greater
      (mapQueue (fun n : Nat => Int64.ofInt n) BinomialQueues.sourceForest)).map Int64.toInt =
      some 9 := by
  rw [nat_findMax_transport _ textbook_input_bounded, BinomialQueues.source_fold_maximum]
  rfl

def signedInputs : List Int := [-(2 : Int) ^ 63, -1, (2 : Int) ^ 63 - 1, 0, -1]

def signedQueue : Queue Int64 :=
  (signedInputs.map Int64.ofInt).foldl (fun q key => insert int64Greater key q) []

theorem signed_endpoint_maximum :
    (findMax int64Greater signedQueue).map Int64.toInt = some ((2 : Int) ^ 63 - 1) := by decide

theorem signed_endpoint_decode :
    (findMax int64Greater signedQueue).map Int64.toInt =
      findMax Representations.SignedComparison.intGtb (mapQueue Int64.toInt signedQueue) :=
  decode_findMax signedQueue

theorem negative_before_zero : int64Greater (Int64.ofInt (-1)) (Int64.ofInt 0) = false ∧
    int64Greater (Int64.ofInt 0) (Int64.ofInt (-1)) = true := by decide

theorem equal_machine_keys : int64Greater (Int64.ofInt 7) (Int64.ofInt 7) = false := by decide

theorem signed_lower_endpoint_checked :
    (checkedInt64 (-(2 : Int) ^ 63)).map Int64.toInt = some (-(2 : Int) ^ 63) := by
  rw [checkedInt64_decode]
  decide

theorem signed_upper_endpoint_checked :
    (checkedInt64 ((2 : Int) ^ 63 - 1)).map Int64.toInt = some ((2 : Int) ^ 63 - 1) := by
  rw [checkedInt64_decode]
  decide

theorem signed_overflow_rejected : checkedInt64 ((2 : Int) ^ 63) = none ∧
    checkedInt64 (-(2 : Int) ^ 63 - 1) = none := by
  constructor <;> rw [checkedInt64_none] <;> omega

theorem nat_boundary_rejected : checkedNat64 (2 ^ 63) = none :=
  (checkedNat64_none _).mpr le_rfl

theorem nat_largest_checked :
    (checkedNat64 (2 ^ 63 - 1)).map Int64.toInt = some ((2 ^ 63 - 1 : Nat) : Int) := by
  rw [checkedNat64_decode]
  decide

theorem machine_list_duplicates :
    (listDeleteMax Representations.SignedComparison.int64Leb
      [Int64.ofInt 7, Int64.ofInt 1, Int64.ofInt 7]).map
        (fun result => (result.1.toInt, result.2.map Int64.toInt)) = some (7, [1, 7]) := by decide

theorem machine_list_correspondence :
    (listDeleteMax Representations.SignedComparison.int64Leb
      [Int64.ofInt 7, Int64.ofInt 1, Int64.ofInt 7]).map
        (fun result => (result.1.toInt, result.2.map Int64.toInt)) =
      (Search.ListMaximumQueue.deleteMax [7, 1, 7]).map
        (fun result => ((result.1 : Int), result.2.map (fun n : Nat => (n : Int)))) := by
  apply nat_list_delete_transport [7, 1, 7]
  intro key hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  omega

end Examples.BinomialQueueClients
