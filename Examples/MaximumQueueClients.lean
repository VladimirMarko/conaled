import Applications.Search.MaximumQueue
import Applications.Search.ListMaximumQueue
import Mathlib.Data.List.Count

/-!
# One occurrence client for maximum queues

The existing minimum-queue interface is viewed through `OrderDual Nat`. A native
merge remains a supplied operation with its own proved observation and validity
laws. The client retains repeated priorities and consumes the interface's bound
on all original entries. Different realizations need not return the same shape.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.MaximumQueueClients

universe u

open Search.PriorityInterface
open Search.MaximumQueue (encode decode)

private theorem encode_injective : Function.Injective encode := by
  intro a b h
  simpa only [Search.MaximumQueue.decode_encode] using congrArg decode h

/-- Every input occurrence is inserted through the existing batch interface. -/
def build (Q : ExactQueue.{0,0,u} Unit (OrderDual Nat)) (keys : List Nat) : Q.Carrier :=
  Q.add (keys.map encode) Q.empty

theorem build_valid (Q : ExactQueue.{0,0,u} Unit (OrderDual Nat)) (keys : List Nat) :
    Q.Valid (build Q keys) := Q.add_valid _ _ Q.empty_valid

theorem build_entries (Q : ExactQueue.{0,0,u} Unit (OrderDual Nat)) (keys : List Nat) :
    (Q.entries (build Q keys)).Perm (keys.map encode) := by
  simpa only [build, Q.empty_entries, List.append_nil] using Q.add_exact (keys.map encode) Q.empty

/-- Use the implementation's native merge, with no decoding or reinsertion. -/
def mergeBuilt (Q : ExactQueue.{0,0,u} Unit (OrderDual Nat))
    (merge : Q.Carrier → Q.Carrier → Q.Carrier) (left right : List Nat) : Q.Carrier :=
  merge (build Q left) (build Q right)

theorem mergeBuilt_valid (Q : ExactQueue.{0,0,u} Unit (OrderDual Nat))
    (merge : Q.Carrier → Q.Carrier → Q.Carrier)
    (merge_valid : ∀ p q, Q.Valid p → Q.Valid q → Q.Valid (merge p q))
    (left right : List Nat) : Q.Valid (mergeBuilt Q merge left right) :=
  merge_valid _ _ (build_valid Q left) (build_valid Q right)

theorem mergeBuilt_entries (Q : ExactQueue.{0,0,u} Unit (OrderDual Nat))
    (merge : Q.Carrier → Q.Carrier → Q.Carrier)
    (merge_entries : ∀ p q, Q.Valid p → Q.Valid q →
      (Q.entries (merge p q)).Perm (Q.entries p ++ Q.entries q))
    (left right : List Nat) :
    (Q.entries (mergeBuilt Q merge left right)).Perm ((left ++ right).map encode) := by
  have h := (merge_entries (build Q left) (build Q right)
    (build_valid Q left) (build_valid Q right)).trans
    ((build_entries Q left).append (build_entries Q right))
  simpa only [mergeBuilt, List.map_append] using h

/-- The maximum is an actual stored occurrence, and exactly one copy is removed. -/
theorem remove_occurrence (Q : ExactQueue.{0,0,u} Unit (OrderDual Nat))
    (queue : Q.Carrier) (keys : List Nat) (key : Nat) (rest : Q.Carrier)
    (valid : Q.Valid queue) (entries : (Q.entries queue).Perm (keys.map encode))
    (removed : Q.remove queue = some (encode key, rest)) :
    Q.Valid rest ∧ key ∈ keys ∧ (∀ a ∈ keys, a ≤ key) ∧
      (Q.entries rest).length + 1 = keys.length ∧
      ∀ a, keys.count a = (Q.entries rest).count (encode a) + if a = key then 1 else 0 := by
  have h := Q.remove_spec queue (encode key) rest valid removed
  have permutation := entries.symm.trans h.2.1
  refine ⟨h.1, ?_, ?_, ?_, ?_⟩
  · have member : encode key ∈ keys.map encode :=
      permutation.mem_iff.mpr List.mem_cons_self
    rcases List.mem_map.mp member with ⟨a, ha, he⟩
    exact (encode_injective he) ▸ ha
  · intro a ha
    have original : encode a ∈ Q.entries queue :=
      entries.mem_iff.mpr (List.mem_map.mpr ⟨a, ha, rfl⟩)
    exact (Search.MaximumQueue.encode_priority_le key a).mp (h.2.2 _ original)
  · simpa only [List.length_cons, List.length_map] using permutation.length_eq.symm
  · intro a
    have count := permutation.count_eq (encode a)
    rw [List.count_map_of_injective keys encode encode_injective a] at count
    by_cases same : a = key
    · subst a
      simpa using count
    · have different : encode key ≠ encode a := fun he => same (encode_injective he.symm)
      simpa [different, same] using count

/-- A nonempty observed queue really has a removable result; the contract is not
used only under an assumed successful execution. -/
theorem exists_remove (Q : ExactQueue.{0,0,u} Unit (OrderDual Nat))
    (queue : Q.Carrier) (keys : List Nat) (entries : (Q.entries queue).Perm (keys.map encode))
    (nonempty : keys ≠ []) : ∃ key rest, Q.remove queue = some (encode key, rest) := by
  cases removed_result : Q.remove queue with
  | none =>
      have empty := (Q.remove_none queue).mp removed_result
      have length := entries.length_eq
      simp only [empty, List.length_nil, List.length_map] at length
      exact False.elim (nonempty (List.length_eq_zero_iff.mp length.symm))
  | some output =>
      refine ⟨decode output.1, output.2, ?_⟩
      simp only [Search.MaximumQueue.encode_decode, Prod.mk.eta]

/-- Cancelling the returned occurrence determines the entire residual multiset.
The displayed head is an observation witness, not the queue's stored shape. -/
theorem remove_head_entries (Q : ExactQueue.{0,0,u} Unit (OrderDual Nat))
    (queue rest : Q.Carrier) (key : Nat) (keys : List Nat)
    (valid : Q.Valid queue)
    (entries : (Q.entries queue).Perm ((key :: keys).map encode))
    (removed : Q.remove queue = some (encode key, rest)) :
    (Q.entries rest).Perm (keys.map encode) := by
  have permutation := entries.symm.trans (Q.remove_spec queue (encode key) rest valid removed).2.1
  exact permutation.cons_inv.symm

/-- The three copies of7 in the input force a real maximum result and two copies
in the residual. This is independent of the queue's concrete representation. -/
theorem three_maxima_client (Q : ExactQueue.{0,0,u} Unit (OrderDual Nat))
    (merge : Q.Carrier → Q.Carrier → Q.Carrier)
    (merge_valid : ∀ p q, Q.Valid p → Q.Valid q → Q.Valid (merge p q))
    (merge_entries : ∀ p q, Q.Valid p → Q.Valid q →
      (Q.entries (merge p q)).Perm (Q.entries p ++ Q.entries q)) :
    ∃ rest, Q.remove (mergeBuilt Q merge [7,2,7] [7,0]) = some (encode 7, rest) ∧
      Q.Valid rest ∧ (Q.entries rest).length = 4 ∧ (Q.entries rest).count (encode 7) = 2 := by
  have valid := mergeBuilt_valid Q merge merge_valid [7,2,7] [7,0]
  have entries := mergeBuilt_entries Q merge merge_entries [7,2,7] [7,0]
  obtain ⟨key, rest, removed⟩ := exists_remove Q _ _ entries (by decide)
  obtain ⟨rest_valid, member, upper, length, count⟩ :=
    remove_occurrence Q _ _ key rest valid entries removed
  have lower : 7 ≤ key := upper 7 (by decide)
  have key_le : key ≤ 7 := by
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
    omega
  have equal : key = 7 := Nat.le_antisymm key_le lower
  subst key
  refine ⟨rest, removed, rest_valid, ?_, ?_⟩
  · change (Q.entries rest).length + 1 = 5 at length
    omega
  · have hc := count 7
    change 3 = (Q.entries rest).count (encode 7) + 1 at hc
    omega

/-- The next removal still returns7. Both successful calls are proved to exist,
and their final residual retains exactly one of the original three copies. -/
theorem two_maxima_client (Q : ExactQueue.{0,0,u} Unit (OrderDual Nat))
    (merge : Q.Carrier → Q.Carrier → Q.Carrier)
    (merge_valid : ∀ p q, Q.Valid p → Q.Valid q → Q.Valid (merge p q))
    (merge_entries : ∀ p q, Q.Valid p → Q.Valid q →
      (Q.entries (merge p q)).Perm (Q.entries p ++ Q.entries q)) :
    ∃ first second,
      Q.remove (mergeBuilt Q merge [7,2,7] [7,0]) = some (encode 7, first) ∧
      Q.remove first = some (encode 7, second) ∧ Q.Valid first ∧ Q.Valid second ∧
      (Q.entries first).count (encode 7) = 2 ∧
      (Q.entries second).Perm ([2,7,0].map encode) ∧
      (Q.entries second).count (encode 7) = 1 := by
  obtain ⟨first, removed_first, valid_first, _length_first, count_first⟩ :=
    three_maxima_client Q merge merge_valid merge_entries
  have original_valid := mergeBuilt_valid Q merge merge_valid [7,2,7] [7,0]
  have original_entries := mergeBuilt_entries Q merge merge_entries [7,2,7] [7,0]
  have residual := remove_head_entries Q _ first 7 [2,7,7,0]
    original_valid original_entries removed_first
  have first_entries : (Q.entries first).Perm ([7,2,7,0].map encode) :=
    residual.trans ((List.Perm.swap 7 2 [7,0]).map encode)
  obtain ⟨key, second, removed_second⟩ := exists_remove Q first [7,2,7,0] first_entries (by decide)
  obtain ⟨valid_second, member, upper, _length_second, count_second⟩ :=
    remove_occurrence Q first [7,2,7,0] key second valid_first first_entries removed_second
  have lower : 7 ≤ key := upper 7 (by decide)
  have key_le : key ≤ 7 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    omega
  have equal : key = 7 := Nat.le_antisymm key_le lower
  subst key
  refine ⟨first, second, removed_first, removed_second, valid_first, valid_second,
    count_first, remove_head_entries Q first second 7 [2,7,0] valid_first first_entries removed_second,
    ?_⟩
  have count := count_second 7
  change 2 = (Q.entries second).count (encode 7) + 1 at count
  omega

/-- An existing minimum leftist queue supplies a maximum occurrence queue under
order duality, including its own native meld. -/
abbrev leftist : ExactQueue Unit (OrderDual Nat) := exactLeftist

theorem leftist_three_maxima :
    ∃ rest, leftist.remove (mergeBuilt leftist Search.LeftistQueue.combineQ [7,2,7] [7,0]) =
      some (encode 7, rest) ∧ leftist.Valid rest ∧ (leftist.entries rest).length = 4 ∧
      (leftist.entries rest).count (encode 7) = 2 :=
  three_maxima_client leftist Search.LeftistQueue.combineQ
    Search.LeftistQueue.combineQ_valid (fun p q _ _ => Search.LeftistQueue.combineQ_entries p q)

theorem leftist_two_maxima :
    ∃ first second,
      leftist.remove (mergeBuilt leftist Search.LeftistQueue.combineQ [7,2,7] [7,0]) =
        some (encode 7, first) ∧
      leftist.remove first = some (encode 7, second) ∧ leftist.Valid first ∧ leftist.Valid second ∧
      (leftist.entries first).count (encode 7) = 2 ∧
      (leftist.entries second).Perm ([2,7,0].map encode) ∧
      (leftist.entries second).count (encode 7) = 1 :=
  two_maxima_client leftist Search.LeftistQueue.combineQ
    Search.LeftistQueue.combineQ_valid (fun p q _ _ => Search.LeftistQueue.combineQ_entries p q)

/-- The source list realization uses the same occurrence client and its own
append merge, with its ordinary raw list carrier. -/
abbrev sourceList : ExactQueue Unit (OrderDual Nat) := Search.ListMaximumQueue.exactQueue

theorem build_sourceList (keys : List Nat) : build sourceList keys = keys := by
  change Search.ListMaximumQueue.exactQueue.add (keys.map encode)
    Search.ListMaximumQueue.empty = keys
  rw [Search.ListMaximumQueue.exactQueue_add_keys, Search.ListMaximumQueue.empty_eq,
    List.append_nil]

theorem sourceList_merge_entries (p q : List Nat) :
    (sourceList.entries (Search.ListMaximumQueue.merge p q)).Perm
      (sourceList.entries p ++ sourceList.entries q) := by
  change (Search.ListMaximumQueue.exactQueue.entries (Search.ListMaximumQueue.merge p q)).Perm
    (Search.ListMaximumQueue.exactQueue.entries p ++ Search.ListMaximumQueue.exactQueue.entries q)
  rw [Search.ListMaximumQueue.exactQueue_native_merge]

theorem sourceList_three_maxima :
    ∃ rest, sourceList.remove (mergeBuilt sourceList Search.ListMaximumQueue.merge [7,2,7] [7,0]) =
      some (encode 7, rest) ∧ sourceList.Valid rest ∧ (sourceList.entries rest).length = 4 ∧
      (sourceList.entries rest).count (encode 7) = 2 :=
  three_maxima_client sourceList Search.ListMaximumQueue.merge
    Search.ListMaximumQueue.merge_valid (fun p q _ _ => sourceList_merge_entries p q)

theorem sourceList_two_maxima :
    ∃ first second,
      sourceList.remove (mergeBuilt sourceList Search.ListMaximumQueue.merge [7,2,7] [7,0]) =
        some (encode 7, first) ∧
      sourceList.remove first = some (encode 7, second) ∧
      sourceList.Valid first ∧ sourceList.Valid second ∧
      (sourceList.entries first).count (encode 7) = 2 ∧
      (sourceList.entries second).Perm ([2,7,0].map encode) ∧
      (sourceList.entries second).count (encode 7) = 1 :=
  two_maxima_client sourceList Search.ListMaximumQueue.merge
    Search.ListMaximumQueue.merge_valid (fun p q _ _ => sourceList_merge_entries p q)

/-- Both realizations actually support the same two maximum removals. Their
final observations agree by occurrences, without equating their carrier states. -/
theorem interchangeable_two_removal_client :
    ∃ listFirst listSecond heapFirst heapSecond,
      sourceList.remove (mergeBuilt sourceList Search.ListMaximumQueue.merge [7,2,7] [7,0]) =
        some (encode 7, listFirst) ∧
      sourceList.remove listFirst = some (encode 7, listSecond) ∧
      leftist.remove (mergeBuilt leftist Search.LeftistQueue.combineQ [7,2,7] [7,0]) =
        some (encode 7, heapFirst) ∧
      leftist.remove heapFirst = some (encode 7, heapSecond) ∧
      (sourceList.entries listSecond).Perm (leftist.entries heapSecond) ∧
      (sourceList.entries listSecond).count (encode 7) = 1 ∧
      (leftist.entries heapSecond).count (encode 7) = 1 := by
  obtain ⟨listFirst, listSecond, listRemove, listRemoveAgain, _listFirstValid, _listSecondValid,
    _listFirstCount, listObservation, listCount⟩ := sourceList_two_maxima
  obtain ⟨heapFirst, heapSecond, heapRemove, heapRemoveAgain, _heapFirstValid, _heapSecondValid,
    _heapFirstCount, heapObservation, heapCount⟩ := leftist_two_maxima
  exact ⟨listFirst, listSecond, heapFirst, heapSecond, listRemove, listRemoveAgain,
    heapRemove, heapRemoveAgain, listObservation.trans heapObservation.symm, listCount, heapCount⟩

end Examples.MaximumQueueClients
