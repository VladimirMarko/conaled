import Applications.Search.MaximumQueue
import Applications.Search.ListMaximumQueue

/-!
The guarded contract admits an implementation with an invalid raw state. Its
valid states execute the actual source list queue, while its invalid state
deliberately violates an unguarded empty-observation law. The valid-state adapter
still supports exact insertion and removal, including repeated maxima.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.MaximumQueueContract

open Search.MaximumQueue

/-- `none` represents a malformed state, not an empty queue. -/
def Valid : Option (List Nat) → Prop
  | none => False
  | some _ => True

def Abs (state : Option (List Nat)) (meaning : List Nat) : Prop := state = some meaning

def observe (state : Option (List Nat)) : List Nat := state.getD []

/-- Each valid operation directly uses the source queue; only the behavior on
the invalid state is unconstrained. -/
def ops : Operations (Option (List Nat)) where
  empty := some Search.ListMaximumQueue.empty
  insert := fun key state => state.map (Search.ListMaximumQueue.insert key)
  deleteMax := fun state => match state with
    | none => some (0, none)
    | some queue => (Search.ListMaximumQueue.deleteMax queue).map
        (fun (key, rest) => (key, some rest))
  merge := fun left right => left.bind (fun p => right.map (Search.ListMaximumQueue.merge p))

theorem delete_some (queue rest : List Nat) (key : Nat) :
    ops.deleteMax (some queue) = some (key, some rest) ↔
      Search.ListMaximumQueue.deleteMax queue = some (key, rest) := by
  cases h : Search.ListMaximumQueue.deleteMax queue with
  | none => simp [ops, h]
  | some result => rcases result with ⟨selected, residual⟩; simp [ops, h]

theorem laws : Laws ops Valid Abs where
  can_relate := by
    intro state hv
    cases state with
    | none => exact False.elim hv
    | some queue => exact ⟨queue, rfl⟩
  abs_perm := by
    intro state left right _ hl hr
    have h : left = right := Option.some.inj (hl.symm.trans hr)
    subst right
    exact List.Perm.refl _
  empty_valid := trivial
  empty_relate := rfl
  insert_valid := by
    intro key state hv
    cases state with
    | none => exact False.elim hv
    | some _ => trivial
  insert_relate := by
    intro state meaning key _ related
    subst state
    rfl
  deleteMax_none := by
    intro state hv
    cases state with
    | none => exact False.elim hv
    | some queue =>
      cases queue with
      | nil => simp [Abs, ops, Search.ListMaximumQueue.deleteMax]
      | cons seed tail => simp [Abs, ops, Search.ListMaximumQueue.deleteMax]
  deleteMax_valid := by
    intro state rest key hv hd
    cases state with
    | none => exact False.elim hv
    | some queue =>
      cases h : Search.ListMaximumQueue.deleteMax queue with
      | none => simp [ops, h] at hd
      | some result =>
        rcases result with ⟨selected, residual⟩
        simp only [ops, h, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hd
        rcases hd with ⟨rfl, rfl⟩
        trivial
  deleteMax_relate := by
    intro state rest key meaning residual _ related hd rest_related
    subst state
    subst rest
    exact Search.ListMaximumQueue.deleteMax_relate meaning residual key meaning residual
      trivial rfl ((delete_some meaning residual key).mp hd) rfl
  merge_valid := by
    intro left right hl hr
    cases left with
    | none => exact False.elim hl
    | some _ =>
      cases right with
      | none => exact False.elim hr
      | some _ => trivial
  merge_relate := by
    intro left right pl ql al _ _ hl hr ha
    subst left
    subst right
    exact Search.ListMaximumQueue.merge_relate pl ql pl ql al trivial trivial rfl rfl
      (Option.some.inj ha)

theorem observe_spec (state : Option (List Nat)) (hv : Valid state) :
    Abs state (observe state) := by
  cases state with
  | none => exact False.elim hv
  | some _ => rfl

def wrap (queue : List Nat) : {state : Option (List Nat) // Valid state} :=
  ⟨some queue, trivial⟩

def exactQueue : Search.PriorityInterface.ExactQueue Unit (OrderDual Nat) :=
  exactQueueOnValid ops laws observe observe_spec

/-- The intended raw invalid state really exists, so all-valid transport would
require a false extra premise for this implementation. -/
theorem not_all_valid : ¬ ∀ state, Valid state := fun h => h none

theorem invalid_has_no_witness : ¬ ∃ meaning, Abs none meaning := by
  rintro ⟨meaning, h⟩
  change none = some meaning at h
  cases h

theorem invalid_empty_law_fails :
    ¬ (ops.deleteMax none = none ↔ observe none = []) := by
  decide

theorem invalid_cannot_enter_adapter :
    ¬ ∃ state : {q : Option (List Nat) // Valid q}, state.val = none := by
  rintro ⟨state, h⟩
  have hv := state.property
  rw [h] at hv
  exact hv

theorem valid_empty_witness : ∃ meaning, Abs ops.empty meaning :=
  laws.can_relate ops.empty laws.empty_valid

theorem empty_witness_unique (meaning : List Nat) (h : Abs ops.empty meaning) :
    meaning = [] := laws.empty_abstract meaning h

theorem abstraction_does_not_permute :
    ([1, 2] : List Nat).Perm [2, 1] ∧ Abs (some [1, 2]) [1, 2] ∧
      ¬ Abs (some [1, 2]) [2, 1] :=
  ⟨List.Perm.swap _ _ _, rfl, by
    change ¬ ((some [1, 2] : Option (List Nat)) = some [2, 1])
    decide⟩

theorem abstract_multiset_unique (meaning : List Nat)
    (h : Abs (some [7, 2, 7]) meaning) :
    (meaning : Multiset Nat) = ([7, 2, 7] : List Nat) :=
  laws.abs_multiset (some [7, 2, 7]) meaning [7, 2, 7] trivial h rfl

theorem insert_duplicate_count : ([7, 7, 2] : List Nat).count 7 = 2 :=
  laws.insert_count (some [7, 2]) [7, 2] [7, 7, 2] 7 7 trivial rfl rfl

theorem encoded_order : (encode 7).2 ≤ (encode 2).2 ∧ decode (encode 7) = 7 :=
  ⟨(encode_priority_le 7 2).mpr (by decide), decode_encode 7⟩

theorem valid_empty_projection :
    (validOperations ops laws).empty.val = some [] := validOperations_empty_val ops laws

theorem valid_insert_projection :
    ((validOperations ops laws).insert 7 (wrap [7, 2])).val = some [7, 7, 2] :=
  validOperations_insert_val ops laws 7 (wrap [7, 2])

theorem valid_merge_projection :
    ((validOperations ops laws).merge (wrap [7, 2, 7]) (wrap [7, 0])).val =
      some [7, 2, 7, 7, 0] :=
  validOperations_merge_val ops laws (wrap [7, 2, 7]) (wrap [7, 0])

theorem source_remove_repeated :
    ops.deleteMax (some [2, 7, 7, 4]) = some (7, some [2, 7, 4]) :=
  (delete_some _ _ _).mpr (by decide)

theorem valid_delete_projection :
    ((validOperations ops laws).deleteMax (wrap [2, 7, 7, 4])).map
      (fun (key, rest) => (key, rest.val)) = some (7, some [2, 7, 4]) :=
  (validOperations_deleteMax_val ops laws (wrap [2, 7, 7, 4])).trans source_remove_repeated

theorem successful_witness :
    Valid (some [2, 7, 4]) ∧ ∃ residual, Abs (some [2, 7, 4]) residual ∧
      ([2, 7, 7, 4] : List Nat).Perm (7 :: residual) ∧ ∀ x ∈ residual, x ≤ 7 :=
  laws.deleteMax_exists (some [2, 7, 7, 4]) (some [2, 7, 4]) 7 _
    trivial rfl source_remove_repeated

theorem selected_original_maximum :
    7 ∈ ([2, 7, 7, 4] : List Nat) ∧ ∀ x ∈ ([2, 7, 7, 4] : List Nat), x ≤ 7 :=
  ⟨laws.deleteMax_mem (some [2, 7, 7, 4]) (some [2, 7, 4]) 7 _
      trivial rfl source_remove_repeated,
    laws.deleteMax_maximum (some [2, 7, 7, 4]) (some [2, 7, 4]) 7 _
      trivial rfl source_remove_repeated⟩

theorem exactly_one_copy_removed :
    ([2, 7, 7, 4] : List Nat).count 7 = ([2, 7, 4] : List Nat).count 7 + 1 :=
  laws.deleteMax_count (some [2, 7, 7, 4]) (some [2, 7, 4]) 7 7 _ _
    trivial rfl source_remove_repeated rfl

theorem other_count_preserved :
    ([2, 7, 7, 4] : List Nat).count 2 = ([2, 7, 4] : List Nat).count 2 :=
  laws.deleteMax_count (some [2, 7, 7, 4]) (some [2, 7, 4]) 7 2 _ _
    trivial rfl source_remove_repeated rfl

theorem residual_size : ([2, 7, 4] : List Nat).length + 1 = ([2, 7, 7, 4] : List Nat).length :=
  laws.deleteMax_length (some [2, 7, 7, 4]) (some [2, 7, 4]) 7 _ _
    trivial rfl source_remove_repeated rfl

theorem merged_witness :
    Valid (ops.merge (some [7, 2, 7]) (some [7, 0])) ∧
      ∃ meaning, Abs (ops.merge (some [7, 2, 7]) (some [7, 0])) meaning ∧
        meaning.Perm ([7, 2, 7] ++ [7, 0]) :=
  laws.merge_exists _ _ _ _ trivial trivial rfl rfl

theorem merge_keeps_three_copies :
    ([7, 2, 7, 7, 0] : List Nat).count 7 = 3 := by
  have h := laws.merge_count (some [7, 2, 7]) (some [7, 0])
    [7, 2, 7] [7, 0] [7, 2, 7, 7, 0] 7 trivial trivial rfl rfl rfl
  exact h

theorem merge_multiset_addition :
    ([7, 2, 7, 7, 0] : Multiset Nat) =
      ([7, 2, 7] : Multiset Nat) + ([7, 0] : Multiset Nat) :=
  laws.merge_multiset (some [7, 2, 7]) (some [7, 0])
    [7, 2, 7] [7, 0] [7, 2, 7, 7, 0] trivial trivial rfl rfl rfl

theorem merged_size : ([7, 2, 7, 7, 0] : List Nat).length = 5 :=
  laws.merge_length (some [7, 2, 7]) (some [7, 0])
    [7, 2, 7] [7, 0] [7, 2, 7, 7, 0] trivial trivial rfl rfl rfl

theorem adapted_empty : exactQueue.remove (wrap []) = none :=
  (exactQueue.remove_none (wrap [])).mpr rfl

theorem adapted_zero : exactQueue.remove (wrap [0]) = some (encode 0, wrap []) :=
  (exactQueueOnValid_remove_some ops laws observe observe_spec (wrap [0]) (wrap [])
    (encode 0)).mpr ((delete_some [0] [] 0).mpr (by decide))

theorem adapted_repeated :
    exactQueue.remove (wrap [2, 7, 7, 4]) = some (encode 7, wrap [2, 7, 4]) :=
  (exactQueueOnValid_remove_some ops laws observe observe_spec _ _ (encode 7)).mpr
    source_remove_repeated

theorem adapted_second_maximum :
    exactQueue.remove (wrap [2, 7, 4]) = some (encode 7, wrap [2, 4]) :=
  (exactQueueOnValid_remove_some ops laws observe observe_spec _ _ (encode 7)).mpr
    ((delete_some _ _ _).mpr (by decide))

theorem adapted_entries :
    exactQueue.entries (wrap [2, 7, 7, 4]) = [encode 2, encode 7, encode 7, encode 4] :=
  exactQueueOnValid_entries ops laws observe observe_spec (wrap [2, 7, 7, 4])

theorem adapted_add_occurrences :
    (exactQueue.entries (exactQueue.add [encode 7, encode 7] (wrap [2]))).Perm
      [encode 7, encode 7, encode 2] :=
  exactQueue.add_exact [encode 7, encode 7] (wrap [2])

theorem adapted_native_merge :
    ((observe (ops.merge (some [7, 2, 7]) (some [7, 0]))).map encode).Perm
      [encode 7, encode 2, encode 7, encode 7, encode 0] :=
  encoded_merge_entries laws observe observe_spec (some [7, 2, 7]) (some [7, 0])
    trivial trivial

end Examples.MaximumQueueContract
