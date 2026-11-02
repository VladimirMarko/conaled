import Applications.Search.PriorityMerge
import Applications.Search.PrioritySearchQueue

/-!
# Exact priority observations on existing queue realizations

The closed calculations distinguish one-occurrence deletion, overlapping merge,
payload ties, and invalid cached ranks. Public observation and client laws are
applied to the same actual states. No operation-count statement is intended.
-/
set_option autoImplicit false
set_option warningAsError true

namespace PriorityModelExamples

open Search.PriorityInterface Search.LeftistQueue
universe u v z

namespace SourceUnit

variable {σ : Type v} [LinearOrder σ] (Q : ExactQueue.{0,v,z} Unit σ)

/-- Figure 14.1: empty content. -/
theorem empty_content : Q.priorityMultiset Q.empty = 0 := Q.priorityMultiset_empty

/-- Figure 14.1: validity of the actual designated empty state. -/
theorem empty_valid : Q.Valid Q.empty := Q.empty_valid

/-- The source validity premise is retained; the existing content law is stronger. -/
theorem insert_content (x : σ) (q : Q.Carrier) (_hq : Q.Valid q) :
    Q.priorityMultiset (Q.add [((),x)] q) = Q.priorityMultiset q + {x} :=
  Q.priorityMultiset_insertOne_add ((),x) q

theorem insert_valid (x : σ) (q : Q.Carrier) (hq : Q.Valid q) :
    Q.Valid (Q.add [((),x)] q) := Q.insertOne_valid ((),x) q hq

/-- Actual deletion subtracts one source minimum on the stated nonempty domain. -/
theorem delete_content (q : Q.Carrier) (hq : Q.Valid q) (hne : Q.priorityMultiset q ≠ 0) :
    Q.priorityMultiset (Q.toOperations.deleteMin q) =
      Q.priorityMultiset q - {(Q.priorityMultiset q).toFinset.min'
        (Multiset.toFinset_nonempty.mpr hne)} :=
  Q.priorityMultiset_deleteMin_sub_min q hq hne

theorem delete_valid (q : Q.Carrier) (hq : Q.Valid q) (_hne : Q.priorityMultiset q ≠ 0) :
    Q.Valid (Q.toOperations.deleteMin q) := Q.deleteMin_valid q hq

/-- The seventh source law uses Option instead of an empty-type default. -/
theorem get_minimum (q : Q.Carrier) (hq : Q.Valid q) (hne : Q.priorityMultiset q ≠ 0) :
    Q.toOperations.peekPriority? q = some ((Q.priorityMultiset q).toFinset.min'
      (Multiset.toFinset_nonempty.mpr hne)) := Q.peekPriority?_eq_min q hq hne

/-- The companion theory's additional eighth law is a separate Boolean reflection. -/
theorem isEmpty_reflection (q : Q.Carrier) (_hq : Q.Valid q) :
    Q.toOperations.isEmpty q = true ↔ Q.priorityMultiset q = 0 := Q.isEmpty_eq_true_iff q

end SourceUnit

abbrev unitQueue : ExactQueue Unit Nat := exactLeftist
abbrev unitListQueue : ExactQueue Unit Nat := exactList
abbrev boolQueue : ExactQueue Bool Nat := exactLeftist

def leaf (p : Nat) : PQ Unit Nat := .fork 1 () p .null .null

def duplicates : PQ Unit Nat := makeQ [((),1),((),1),((),3)]
def duplicatesRest : PQ Unit Nat := .fork 1 () 1 (leaf 3) .null

theorem duplicates_shape :
    duplicates = .fork 1 () 1 duplicatesRest .null := by decide +kernel

theorem duplicates_valid : unitQueue.Valid duplicates :=
  (makeQ_spec [((),1),((),1),((),3)]).1

theorem duplicates_entries :
    entries duplicates = [((),1),((),1),((),3)] := by decide +kernel

theorem duplicates_remove :
    unitQueue.remove duplicates = some (((),1), duplicatesRest) := by decide +kernel

def firstInput : PQ Unit Nat := makeQ [((),1),((),3)]
def secondInput : PQ Unit Nat := makeQ [((),1),((),2)]
def merged : PQ Unit Nat := combineQ firstInput secondInput
def inserted : PQ Unit Nat := unitQueue.add [((),2)] merged
def remainder : PQ Unit Nat := .fork 2 () 1 (leaf 2) (.fork 1 () 2 (leaf 3) .null)

theorem first_valid : unitQueue.Valid firstInput :=
  (makeQ_spec [((),1),((),3)]).1

theorem second_valid : unitQueue.Valid secondInput :=
  (makeQ_spec [((),1),((),2)]).1

theorem first_entries : entries firstInput = [((),1),((),3)] := by decide +kernel
theorem second_entries : entries secondInput = [((),1),((),2)] := by decide +kernel

theorem merged_entries :
    entries merged = [((),1),((),3),((),1),((),2)] := by decide +kernel

theorem inserted_entries :
    entries inserted = [((),1),((),1),((),2),((),2),((),3)] := by decide +kernel

theorem remainder_entries :
    entries remainder = [((),1),((),2),((),2),((),3)] := rfl

theorem inserted_remove :
    unitQueue.remove inserted = some (((),1), remainder) := by decide +kernel

def listFirst : unitListQueue.Carrier := unitListQueue.add [((),1),((),3)] unitListQueue.empty
def listSecond : unitListQueue.Carrier := unitListQueue.add [((),1),((),2)] unitListQueue.empty
def listMerged : unitListQueue.Carrier := listFirst ++ listSecond
def listInserted : unitListQueue.Carrier := unitListQueue.add [((),2)] listMerged

theorem list_inserted_entries :
    listInserted = [((),1),((),3),((),1),((),2),((),2)] := rfl

theorem list_first_valid : unitListQueue.Valid listFirst :=
  unitListQueue.add_valid _ _ unitListQueue.empty_valid

theorem list_second_valid : unitListQueue.Valid listSecond :=
  unitListQueue.add_valid _ _ unitListQueue.empty_valid

def falseLeaf : PQ Bool Nat := .fork 1 false 1 .null .null
def trueLeaf : PQ Bool Nat := .fork 1 true 1 .null .null
def falseFirst : PQ Bool Nat := combineQ falseLeaf trueLeaf
def trueFirst : PQ Bool Nat := combineQ trueLeaf falseLeaf

theorem false_leaf_valid : boolQueue.Valid falseLeaf := by
  simp [boolQueue, exactLeftist, Valid, Ranked, Heap, All, rank, falseLeaf]

theorem true_leaf_valid : boolQueue.Valid trueLeaf := by
  simp [boolQueue, exactLeftist, Valid, Ranked, Heap, All, rank, trueLeaf]

theorem false_first_remove :
    boolQueue.remove falseFirst = some ((false,1), trueLeaf) := by decide +kernel

theorem true_first_remove :
    boolQueue.remove trueFirst = some ((true,1), falseLeaf) := by decide +kernel

/-- The root rank is wrong, but the singleton's heap order is correct. -/
def corrupt : PQ Unit Nat := .fork 9 () 1 .null .null

/-- Correct cached ranks do not prevent a parent from exceeding a child. -/
def wrongOrder : PQ Unit Nat := .fork 1 () 3 (leaf 1) .null

/-- Removal exposes the malformed child instead of repairing it. -/
def corruptBelow : PQ Unit Nat := .fork 1 () 0 corrupt .null

theorem corrupt_heap : Heap corrupt := by simp [corrupt, Heap, All]
theorem corrupt_not_ranked : ¬ Ranked corrupt := by simp [corrupt, Ranked, rank]

theorem corrupt_invalid : ¬ unitQueue.Valid corrupt := by
  intro h
  exact corrupt_not_ranked h.1

theorem wrong_order_ranked : Ranked wrongOrder := by
  simp [wrongOrder, leaf, Ranked, rank]

theorem wrong_order_not_heap : ¬ Heap wrongOrder := by
  simp [wrongOrder, leaf, Heap, All]

theorem wrong_order_invalid : ¬ unitQueue.Valid wrongOrder := by
  intro h
  exact wrong_order_not_heap h.2

theorem corrupt_below_heap : Heap corruptBelow := by
  simp [corruptBelow, corrupt, Heap, All]

theorem corrupt_below_invalid : ¬ unitQueue.Valid corruptBelow := by
  intro h
  exact corrupt_not_ranked h.1.1

theorem corrupt_remove : unitQueue.remove corrupt = some (((),1), .null) := by
  decide +kernel

theorem wrong_order_remove : unitQueue.remove wrongOrder = some (((),3), leaf 1) := by
  decide +kernel

theorem corrupt_below_remove :
    unitQueue.remove corruptBelow = some (((),0), corrupt) := by decide +kernel

theorem insert_corrupt : insertQ () 0 corrupt = corruptBelow := by decide +kernel

theorem duplicates_priorities :
    unitQueue.priorityMultiset duplicates = ([1,1,3] : List Nat) := by
  change (entries duplicates : Multiset (Unit × Nat)).map Prod.snd = _
  rw [duplicates_entries] <;> rfl

theorem duplicates_rest_priorities :
    unitQueue.priorityMultiset duplicatesRest = ([1,3] : List Nat) := rfl

theorem first_priorities : unitQueue.priorityMultiset firstInput = ([1,3] : List Nat) := by
  change (entries firstInput : Multiset (Unit × Nat)).map Prod.snd = _
  rw [first_entries] <;> rfl

theorem second_priorities : unitQueue.priorityMultiset secondInput = ([1,2] : List Nat) := by
  change (entries secondInput : Multiset (Unit × Nat)).map Prod.snd = _
  rw [second_entries] <;> rfl

theorem merged_priorities :
    unitQueue.priorityMultiset merged = ([1,3,1,2] : List Nat) := by
  change (entries merged : Multiset (Unit × Nat)).map Prod.snd = _
  rw [merged_entries] <;> rfl

theorem inserted_priorities :
    unitQueue.priorityMultiset inserted = ([1,1,2,2,3] : List Nat) := by
  change (entries inserted : Multiset (Unit × Nat)).map Prod.snd = _
  rw [inserted_entries] <;> rfl

theorem remainder_priorities :
    unitQueue.priorityMultiset remainder = ([1,2,2,3] : List Nat) := rfl

/-- Both count bridges meet the independently calculated two-entry inputs. -/
theorem input_cardinalities :
    (unitQueue.entryMultiset firstInput).card = 2 ∧
      (unitQueue.entryMultiset secondInput).card = 2 ∧
      (unitQueue.priorityMultiset firstInput).card = 2 ∧
      (unitQueue.priorityMultiset secondInput).card = 2 := by
  have heA := unitQueue.entryMultiset_card firstInput
  have heB := unitQueue.entryMultiset_card secondInput
  have hpA := unitQueue.priorityMultiset_card firstInput
  have hpB := unitQueue.priorityMultiset_card secondInput
  change (unitQueue.entryMultiset firstInput).card = (entries firstInput).length at heA
  change (unitQueue.entryMultiset secondInput).card = (entries secondInput).length at heB
  change (unitQueue.priorityMultiset firstInput).card = (entries firstInput).length at hpA
  change (unitQueue.priorityMultiset secondInput).card = (entries secondInput).length at hpB
  rw [first_entries] at heA hpA
  rw [second_entries] at heB hpB
  exact ⟨heA, heB, hpA, hpB⟩

/-- The public removal certificate is specialized at the actual repeated minimum. -/
theorem duplicates_certificate :
    unitQueue.Valid duplicatesRest ∧ ((),1) ∈ unitQueue.entryMultiset duplicates ∧
      unitQueue.entryMultiset duplicates = ((),1) ::ₘ unitQueue.entryMultiset duplicatesRest ∧
      IsLeast {p | p ∈ unitQueue.priorityMultiset duplicates} 1 ∧
      unitQueue.priorityMultiset duplicates = 1 ::ₘ unitQueue.priorityMultiset duplicatesRest :=
  unitQueue.remove_spec_multiset duplicates ((),1) duplicatesRest
    duplicates_valid duplicates_remove

theorem duplicates_residual_card : (unitQueue.priorityMultiset duplicatesRest).card = 2 := by
  have h := unitQueue.remove_priority_card duplicates ((),1) duplicatesRest
    duplicates_valid duplicates_remove
  have hin : (unitQueue.priorityMultiset duplicates).card = 3 := by
    rw [duplicates_priorities] <;> rfl
  omega

theorem duplicates_pop :
    unitQueue.popObs duplicates = some (1, ([1,3] : Multiset Nat)) := by
  rw [unitQueue.popObs_of_remove duplicates ((),1) duplicatesRest duplicates_remove,
    duplicates_rest_priorities]

theorem duplicates_nonempty : unitQueue.priorityMultiset duplicates ≠ 0 := by
  rw [duplicates_priorities] <;> decide +kernel

theorem duplicates_minimum :
    (unitQueue.priorityMultiset duplicates).toFinset.min'
      (Multiset.toFinset_nonempty.mpr duplicates_nonempty) = 1 := by
  have hmin := unitQueue.peekPriority?_eq_min duplicates duplicates_valid duplicates_nonempty
  have hpeek := (Operations.views_of_some unitQueue.toOperations duplicates ((),1)
    duplicatesRest duplicates_remove).2.1
  exact Option.some.inj (hmin.symm.trans hpeek)

theorem duplicates_source_subtraction :
    unitQueue.priorityMultiset (unitQueue.toOperations.deleteMin duplicates) =
      unitQueue.priorityMultiset duplicates - {1} := by
  simpa only [duplicates_minimum] using
    unitQueue.priorityMultiset_deleteMin_sub_min duplicates duplicates_valid duplicates_nonempty

example :
    unitQueue.priorityMultiset (unitQueue.toOperations.deleteMin duplicates) =
        ([1,3] : List Nat) ∧
      unitQueue.Valid (unitQueue.toOperations.deleteMin duplicates) := by
  refine ⟨?_, unitQueue.deleteMin_valid duplicates duplicates_valid⟩
  rw [duplicates_source_subtraction, duplicates_priorities] <;> decide +kernel

example : unitQueue.toOperations.peekPriority? duplicates = some 1 := by
  simpa only [duplicates_minimum] using
    unitQueue.peekPriority?_eq_min duplicates duplicates_valid duplicates_nonempty

example : unitQueue.priorityMultiset duplicatesRest = unitQueue.priorityMultiset duplicates - {1} :=
  unitQueue.priorityMultiset_remove_sub duplicates ((),1) duplicatesRest
    duplicates_valid duplicates_remove

/-- The concrete representative is built by the existing batch insertion into empty. -/
theorem duplicates_from_empty :
    duplicates = unitQueue.add [((),1),((),1),((),3)] unitQueue.empty := rfl

theorem duplicates_entry_realization :
    unitQueue.entryMultiset duplicates = ([((),1),((),1),((),3)] : List (Unit × Nat)) := by
  rw [duplicates_from_empty, unitQueue.entryMultiset_add,
    unitQueue.entryMultiset_empty, Multiset.add_zero]

example : ∃ q, unitQueue.Valid q ∧
    unitQueue.entryMultiset q = ([((),1),((),1),((),3)] : List (Unit × Nat)) ∧
    unitQueue.popObs q = some (1, ([1,3] : Multiset Nat)) := by
  obtain ⟨q, hq, he⟩ := unitQueue.exists_entryMultiset
    ([((),1),((),1),((),3)] : List (Unit × Nat))
  have hobs : unitQueue.priorityMultiset q = unitQueue.priorityMultiset duplicates := by
    change (unitQueue.entryMultiset q).map Prod.snd =
      (unitQueue.entryMultiset duplicates).map Prod.snd
    rw [he, duplicates_entry_realization]
  have hagree := unitQueue.popObs_eq unitQueue (fun _ _ => Nat.le_antisymm)
    q duplicates hq duplicates_valid hobs
  exact ⟨q, hq, he, hagree.trans duplicates_pop⟩

example : ∃ q, unitQueue.Valid q ∧
    unitQueue.priorityMultiset q = ([1,1,3] : List Nat) ∧
    unitQueue.popObs q = some (1, ([1,3] : Multiset Nat)) := by
  obtain ⟨q, hq, hp⟩ := unitQueue.exists_priorityMultiset () ([1,1,3] : List Nat)
  have hagree := unitQueue.popObs_eq unitQueue (fun _ _ => Nat.le_antisymm)
    q duplicates hq duplicates_valid (hp.trans duplicates_priorities.symm)
  exact ⟨q, hq, hp, hagree.trans duplicates_pop⟩

abbrev liftedListQueue : ExactQueue (ULift.{1} Unit) Nat := exactList
def liftedDuplicates : liftedListQueue.Carrier :=
  liftedListQueue.add [(ULift.up (),1),(ULift.up (),1),(ULift.up (),3)] liftedListQueue.empty

theorem lifted_duplicates_valid : liftedListQueue.Valid liftedDuplicates :=
  liftedListQueue.add_valid _ _ liftedListQueue.empty_valid

theorem lifted_duplicates_priorities :
    liftedListQueue.priorityMultiset liftedDuplicates = ([1,1,3] : List Nat) := by
  rw [liftedDuplicates, liftedListQueue.priorityMultiset_add,
    liftedListQueue.priorityMultiset_empty, Multiset.add_zero] <;> rfl

/-- Payload and carrier universes differ; the common observation stays at Nat priorities. -/
example : unitQueue.popObs duplicates = liftedListQueue.popObs liftedDuplicates ∧
    liftedListQueue.popObs liftedDuplicates = some (1, ([1,3] : Multiset Nat)) := by
  have h := unitQueue.popObs_eq liftedListQueue (fun _ _ => Nat.le_antisymm)
    duplicates liftedDuplicates duplicates_valid lifted_duplicates_valid
    (duplicates_priorities.trans lifted_duplicates_priorities.symm)
  exact ⟨h, h.symm.trans duplicates_pop⟩

theorem main_client_result :
    mergeInsertRemove unitQueue.toOperations combineQ ((),2) firstInput secondInput =
      some (((),1), remainder) := inserted_remove

/-- The common client theorem carries both input proofs through both actual intermediate states. -/
theorem main_client_certificate :
    unitQueue.Valid merged ∧ unitQueue.Valid inserted ∧
      unitQueue.priorityMultiset inserted ≠ 0 ∧ unitQueue.Valid remainder ∧
      ((),2) ::ₘ (unitQueue.entryMultiset firstInput + unitQueue.entryMultiset secondInput) =
        ((),1) ::ₘ unitQueue.entryMultiset remainder ∧
      2 ::ₘ (unitQueue.priorityMultiset firstInput + unitQueue.priorityMultiset secondInput) =
        1 ::ₘ unitQueue.priorityMultiset remainder ∧
      IsLeast {p | p ∈ 2 ::ₘ
        (unitQueue.priorityMultiset firstInput + unitQueue.priorityMultiset secondInput)} 1 ∧
      (unitQueue.entryMultiset remainder).card =
        (unitQueue.entryMultiset firstInput).card + (unitQueue.entryMultiset secondInput).card ∧
      (unitQueue.priorityMultiset remainder).card =
        (unitQueue.priorityMultiset firstInput).card + (unitQueue.priorityMultiset secondInput).card :=
  unitQueue.mergeInsertRemove_spec combineQ leftistMergeLaws ((),2) firstInput secondInput
    first_valid second_valid ((),1) remainder main_client_result

theorem merged_valid : unitQueue.Valid merged := main_client_certificate.1
theorem inserted_valid : unitQueue.Valid inserted := main_client_certificate.2.1
theorem remainder_valid : unitQueue.Valid remainder := main_client_certificate.2.2.2.1

theorem main_residual_card : (unitQueue.priorityMultiset remainder).card = 4 := by
  rcases main_client_certificate with ⟨_, _, _, _, _, _, _, _, h⟩
  rw [first_priorities, second_priorities] at h
  exact h

/-- Full-entry counts retain the same actual merge, insertion, and removal stages. -/
theorem entry_stage_cardinalities :
    (unitQueue.entryMultiset merged).card = 4 ∧
      (unitQueue.entryMultiset inserted).card = 5 ∧
      (unitQueue.entryMultiset remainder).card = 4 := by
  have hA := input_cardinalities.1
  have hB := input_cardinalities.2.1
  have hm := unitQueue.entryMultiset_merge_card combineQ leftistMergeLaws
    firstInput secondInput first_valid second_valid
  rw [hA, hB] at hm
  have hm' : (unitQueue.entryMultiset merged).card = 4 := hm
  have hi := unitQueue.entryMultiset_add_card [((),2)] merged
  rw [hm'] at hi
  rcases main_client_certificate with ⟨_, _, _, _, _, _, _, hr, _⟩
  rw [hA, hB] at hr
  exact ⟨hm', hi, hr⟩

example : (unitQueue.priorityMultiset merged).card = 4 ∧
    (unitQueue.priorityMultiset inserted).card = 5 := by
  have hm := unitQueue.priorityMultiset_merge_card combineQ leftistMergeLaws
    firstInput secondInput first_valid second_valid
  rw [first_priorities, second_priorities] at hm
  have hm' : (unitQueue.priorityMultiset merged).card = 4 := hm
  have hi := unitQueue.priorityMultiset_add_card [((),2)] merged
  rw [hm'] at hi
  exact ⟨hm', hi⟩

example : unitQueue.priorityMultiset inserted = unitQueue.priorityMultiset merged + {2} ∧
    unitQueue.Valid inserted :=
  ⟨unitQueue.priorityMultiset_insertOne_add ((),2) merged,
    unitQueue.insertOne_valid ((),2) merged merged_valid⟩

theorem main_pop : unitQueue.popObs inserted = some (1, ([1,2,2,3] : Multiset Nat)) := by
  rw [unitQueue.popObs_of_remove inserted ((),1) remainder inserted_remove, remainder_priorities]

theorem list_first_priorities :
    unitListQueue.priorityMultiset listFirst = ([1,3] : List Nat) := rfl

theorem list_second_priorities :
    unitListQueue.priorityMultiset listSecond = ([1,2] : List Nat) := rfl

theorem list_client_stages :
    unitListQueue.Valid listMerged ∧ unitListQueue.Valid listInserted ∧
      ∃ a s, mergeInsertRemove unitListQueue.toOperations List.append ((),2) listFirst listSecond =
        some (a,s) ∧ unitListQueue.Valid s ∧ (unitListQueue.priorityMultiset s).card = 4 := by
  obtain ⟨a, s, hremove⟩ := unitListQueue.mergeInsertRemove_exists List.append
    ((),2) listFirst listSecond
  have h := unitListQueue.mergeInsertRemove_spec List.append appendMergeLaws
    ((),2) listFirst listSecond list_first_valid list_second_valid a s hremove
  rcases h with ⟨hm, hi, _, hs, _, _, _, _, hc⟩
  refine ⟨hm, hi, a, s, hremove, hs, ?_⟩
  rw [list_first_priorities, list_second_priorities] at hc
  exact hc

theorem client_input_agreement :
    unitQueue.priorityMultiset inserted = unitListQueue.priorityMultiset listInserted := by
  calc
    unitQueue.priorityMultiset inserted =
        2 ::ₘ (unitQueue.priorityMultiset firstInput + unitQueue.priorityMultiset secondInput) :=
      unitQueue.priorityMultiset_mergeInsert combineQ leftistMergeLaws
        ((),2) firstInput secondInput first_valid second_valid
    _ = 2 ::ₘ (unitListQueue.priorityMultiset listFirst + unitListQueue.priorityMultiset listSecond) := by
      rw [first_priorities, second_priorities, list_first_priorities, list_second_priorities]
    _ = unitListQueue.priorityMultiset listInserted :=
      (unitListQueue.priorityMultiset_mergeInsert List.append appendMergeLaws
        ((),2) listFirst listSecond list_first_valid list_second_valid).symm

/-- Both actual clients consume the common atomic theorem; no list tie policy is assumed. -/
example :
    (mergeInsertRemove unitQueue.toOperations combineQ ((),2) firstInput secondInput).map
        (fun (e,r) => (e.2, unitQueue.priorityMultiset r)) =
      some (1, ([1,2,2,3] : Multiset Nat)) ∧
    (mergeInsertRemove unitListQueue.toOperations List.append ((),2) listFirst listSecond).map
        (fun (e,r) => (e.2, unitListQueue.priorityMultiset r)) =
      some (1, ([1,2,2,3] : Multiset Nat)) := by
  change unitQueue.popObs inserted = _ ∧ unitListQueue.popObs listInserted = _
  have h := unitQueue.popObs_eq unitListQueue (fun _ _ => Nat.le_antisymm)
    inserted listInserted inserted_valid list_client_stages.2.1 client_input_agreement
  exact ⟨main_pop, h.symm.trans main_pop⟩

theorem self_merge_priorities :
    unitQueue.priorityMultiset (combineQ firstInput firstInput) = ([1,1,3,3] : List Nat) := by
  rw [unitQueue.priorityMultiset_merge combineQ leftistMergeLaws
    firstInput firstInput first_valid first_valid]
  simp only [first_priorities]
  decide +kernel

example : unitQueue.priorityMultiset (combineQ firstInput firstInput) ≠
    unitQueue.priorityMultiset firstInput := by
  rw [self_merge_priorities, first_priorities]
  decide +kernel

example : unitQueue.entryMultiset (combineQ firstInput secondInput) =
    unitQueue.entryMultiset (combineQ secondInput firstInput) :=
  unitQueue.entryMultiset_merge_comm combineQ leftistMergeLaws
    firstInput secondInput first_valid second_valid

example : unitQueue.priorityMultiset (combineQ (combineQ firstInput secondInput) duplicates) =
    unitQueue.priorityMultiset (combineQ firstInput (combineQ secondInput duplicates)) :=
  unitQueue.priorityMultiset_merge_assoc combineQ leftistMergeLaws
    firstInput secondInput duplicates first_valid second_valid duplicates_valid

example :
    unitQueue.entryMultiset (combineQ unitQueue.empty firstInput) = unitQueue.entryMultiset firstInput ∧
      unitQueue.entryMultiset (combineQ firstInput unitQueue.empty) = unitQueue.entryMultiset firstInput ∧
      unitQueue.priorityMultiset (combineQ unitQueue.empty firstInput) = unitQueue.priorityMultiset firstInput ∧
      unitQueue.priorityMultiset (combineQ firstInput unitQueue.empty) = unitQueue.priorityMultiset firstInput :=
  ⟨unitQueue.entryMultiset_empty_merge combineQ leftistMergeLaws firstInput first_valid,
    unitQueue.entryMultiset_merge_empty combineQ leftistMergeLaws firstInput first_valid,
    unitQueue.priorityMultiset_empty_merge combineQ leftistMergeLaws firstInput first_valid,
    unitQueue.priorityMultiset_merge_empty combineQ leftistMergeLaws firstInput first_valid⟩

theorem false_first_valid : boolQueue.Valid falseFirst :=
  leftistMergeLaws.valid falseLeaf trueLeaf false_leaf_valid true_leaf_valid

theorem true_first_valid : boolQueue.Valid trueFirst :=
  leftistMergeLaws.valid trueLeaf falseLeaf true_leaf_valid false_leaf_valid

theorem tied_priority_agreement : boolQueue.priorityMultiset falseFirst = boolQueue.priorityMultiset trueFirst :=
  boolQueue.priorityMultiset_merge_comm combineQ leftistMergeLaws
    falseLeaf trueLeaf false_leaf_valid true_leaf_valid

example : boolQueue.popObs falseFirst = boolQueue.popObs trueFirst ∧
    boolQueue.popObs trueFirst = some (1, ({1} : Multiset Nat)) := by
  have h := boolQueue.popObs_eq boolQueue (fun _ _ => Nat.le_antisymm)
    falseFirst trueFirst false_first_valid true_first_valid tied_priority_agreement
  have hfalse : boolQueue.popObs falseFirst = some (1, ({1} : Multiset Nat)) := by
    rw [boolQueue.popObs_of_remove falseFirst (false,1) trueLeaf false_first_remove] <;> rfl
  exact ⟨h, h.symm.trans hfalse⟩

example : boolQueue.toOperations.peekEntry? falseFirst ≠ boolQueue.toOperations.peekEntry? trueFirst := by
  rw [(Operations.views_of_some boolQueue.toOperations falseFirst (false,1)
      trueLeaf false_first_remove).1,
    (Operations.views_of_some boolQueue.toOperations trueFirst (true,1)
      falseLeaf true_first_remove).1]
  decide +kernel

example : boolQueue.entryMultiset trueLeaf ≠ boolQueue.entryMultiset falseLeaf := by decide +kernel

example : (boolQueue.toOperations.peekEntry? falseFirst).map Prod.fst ≠
    (boolQueue.toOperations.peekEntry? trueFirst).map Prod.fst := by
  rw [(Operations.views_of_some boolQueue.toOperations falseFirst (false,1)
      trueLeaf false_first_remove).1,
    (Operations.views_of_some boolQueue.toOperations trueFirst (true,1)
      falseLeaf true_first_remove).1]
  decide +kernel

example : falseFirst ≠ trueFirst := by
  intro h
  have hd := congrArg boolQueue.remove h
  rw [false_first_remove, true_first_remove] at hd
  have he : false = true := congrArg (fun z : (Bool × Nat) × PQ Bool Nat => z.1.1)
    (Option.some.inj hd)
  cases he

theorem leftist_empty_views :
    unitQueue.toOperations.peekEntry? unitQueue.empty = none ∧
      unitQueue.toOperations.peekPriority? unitQueue.empty = none ∧
      unitQueue.toOperations.deleteMin unitQueue.empty = unitQueue.empty ∧
      unitQueue.toOperations.isEmpty unitQueue.empty = true :=
  Operations.views_of_none unitQueue.toOperations unitQueue.empty
    ((unitQueue.remove_none_iff_entryMultiset unitQueue.empty).mpr unitQueue.entryMultiset_empty)

theorem list_empty_views :
    unitListQueue.toOperations.peekEntry? unitListQueue.empty = none ∧
      unitListQueue.toOperations.peekPriority? unitListQueue.empty = none ∧
      unitListQueue.toOperations.deleteMin unitListQueue.empty = unitListQueue.empty ∧
      unitListQueue.toOperations.isEmpty unitListQueue.empty = true :=
  Operations.views_of_none unitListQueue.toOperations unitListQueue.empty
    ((unitListQueue.remove_none_iff_priorityMultiset unitListQueue.empty).mpr
      unitListQueue.priorityMultiset_empty)

example : unitQueue.toOperations.isEmpty unitQueue.empty = true ↔
    unitQueue.priorityMultiset unitQueue.empty = 0 :=
  unitQueue.isEmpty_eq_true_iff unitQueue.empty

example : nullQ (unitQueue.empty) = true :=
  (nullQ_iff_priorityMultiset unitQueue.empty).mpr unitQueue.priorityMultiset_empty

theorem leaf_seven_valid : unitQueue.Valid (leaf 7) := by
  simp [unitQueue, exactLeftist, leaf, Valid, Ranked, Heap, All, rank]

theorem leaf_seven_remove : unitQueue.remove (leaf 7) = some (((),7), unitQueue.empty) := by
  decide +kernel

example : unitQueue.popObs (leaf 7) = some (7,0) ∧ unitQueue.Valid unitQueue.empty := by
  refine ⟨?_, (unitQueue.remove_spec_multiset (leaf 7) ((),7) unitQueue.empty
    leaf_seven_valid leaf_seven_remove).1⟩
  simpa only [unitQueue.priorityMultiset_empty] using
    unitQueue.popObs_of_remove (leaf 7) ((),7) unitQueue.empty leaf_seven_remove

/-- The concrete content proof needs no heap or rank hypothesis. -/
private theorem raw_remove_entries (q : PQ Unit Nat) (e : Unit × Nat) (r : PQ Unit Nat)
    (h : unitQueue.remove q = some (e,r)) : (entries q).Perm (e :: entries r) := by
  cases q with
  | null => simp [unitQueue, exactLeftist, deleteQ] at h
  | fork _ x p l s =>
    change some ((x,p), combineQ l s) = some (e,r) at h
    rcases Prod.mk.inj (Option.some.inj h) with ⟨rfl, rfl⟩
    exact List.Perm.cons _ (combineQ_entries l s).symm

example :
    (entries corrupt).Perm (((),1) :: entries (.null : PQ Unit Nat)) ∧
      (entries wrongOrder).Perm (((),3) :: entries (leaf 1)) ∧
      (entries corruptBelow).Perm (((),0) :: entries corrupt) :=
  ⟨raw_remove_entries corrupt ((),1) .null corrupt_remove,
    raw_remove_entries wrongOrder ((),3) (leaf 1) wrong_order_remove,
    raw_remove_entries corruptBelow ((),0) corrupt corrupt_below_remove⟩

theorem corrupt_minimum : IsLeast {p | p ∈ unitQueue.priorityMultiset corrupt} 1 :=
  peekQ?_isLeast corrupt ((),1) corrupt_heap rfl

theorem corrupt_below_minimum : IsLeast {p | p ∈ unitQueue.priorityMultiset corruptBelow} 0 :=
  peekQ?_isLeast corruptBelow ((),0) corrupt_below_heap rfl

theorem wrong_order_not_minimum : ¬ IsLeast {p | p ∈ unitQueue.priorityMultiset wrongOrder} 3 := by
  intro h
  have hmem : (1 : Nat) ∈ unitQueue.priorityMultiset wrongOrder := by decide +kernel
  have hbad : 3 ≤ 1 := h.2 hmem
  omega

example : unitQueue.Valid (leaf 1) ∧ ¬ unitQueue.Valid corrupt := by
  refine ⟨?_, corrupt_invalid⟩
  simp [unitQueue, exactLeftist, leaf, Valid, Ranked, Heap, All, rank]

example : ¬ unitQueue.Valid corrupt ∧
    IsLeast {p | p ∈ unitQueue.priorityMultiset corrupt} 1 ∧
    unitQueue.Valid (unitQueue.toOperations.deleteMin corrupt) := by
  refine ⟨corrupt_invalid, corrupt_minimum, ?_⟩
  rw [(Operations.views_of_some unitQueue.toOperations corrupt ((),1) .null corrupt_remove).2.2.1]
  exact unitQueue.empty_valid

example : ¬ IsLeast {p | p ∈ unitQueue.priorityMultiset wrongOrder} 3 ∧
    unitQueue.Valid (unitQueue.toOperations.deleteMin wrongOrder) := by
  refine ⟨wrong_order_not_minimum, ?_⟩
  rw [(Operations.views_of_some unitQueue.toOperations wrongOrder ((),3)
    (leaf 1) wrong_order_remove).2.2.1]
  simp [unitQueue, exactLeftist, leaf, Valid, Ranked, Heap, All, rank]

example : IsLeast {p | p ∈ unitQueue.priorityMultiset corruptBelow} 0 ∧
    ¬ unitQueue.Valid (unitQueue.toOperations.deleteMin corruptBelow) := by
  refine ⟨corrupt_below_minimum, ?_⟩
  rw [(Operations.views_of_some unitQueue.toOperations corruptBelow ((),0)
    corrupt corrupt_below_remove).2.2.1]
  exact corrupt_invalid

example :
    unitQueue.toOperations.peekEntry? corrupt = peekQ? corrupt ∧
      unitQueue.toOperations.peekEntry? wrongOrder = peekQ? wrongOrder ∧
      unitQueue.toOperations.peekEntry? corruptBelow = peekQ? corruptBelow :=
  ⟨deleteQ_fst corrupt, deleteQ_fst wrongOrder, deleteQ_fst corruptBelow⟩

example :
    (nullQ corrupt = true ↔ unitQueue.entryMultiset corrupt = 0) ∧
      (nullQ wrongOrder = true ↔ unitQueue.priorityMultiset wrongOrder = 0) ∧
      (peekQ? corruptBelow = none ↔ nullQ corruptBelow = true) :=
  ⟨nullQ_iff_entryMultiset corrupt, nullQ_iff_priorityMultiset wrongOrder,
    peekQ?_eq_none_iff corruptBelow⟩

example : (unitQueue.entries (unitQueue.add [((),0)] corrupt)).Perm
    (((),0) :: unitQueue.entries corrupt) := unitQueue.add_exact [((),0)] corrupt

example : unitQueue.priorityMultiset (unitQueue.toOperations.insertOne ((),0) corrupt) =
        ([0,1] : List Nat) ∧
      ¬ unitQueue.Valid (unitQueue.toOperations.insertOne ((),0) corrupt) := by
  refine ⟨?_, ?_⟩
  · rw [unitQueue.priorityMultiset_insertOne] <;> rfl
  · change ¬ unitQueue.Valid (insertQ () 0 corrupt)
    rw [insert_corrupt]
    exact corrupt_below_invalid

def pairKey (x : Nat × Nat) : Nat := x.1
abbrev keyedQueue : Queue (Nat × Nat) Nat Nat pairKey :=
  Search.PrioritySearchQueue.keyed pairKey

def keyedBatch : List ((Nat × Nat) × Nat) := [((3,10),7),((3,20),7)]

theorem keyed_replacement :
    keyedQueue.add keyedBatch keyedQueue.empty = [((3,10),7)] :=
  Search.PrioritySearchQueue.exact_same_key_tie

theorem keyed_covers_replaced :
    ∃ e ∈ keyedQueue.entries (keyedQueue.add keyedBatch keyedQueue.empty),
      pairKey e.1 = 3 ∧ e.2 ≤ 7 :=
  keyedQueue.add_covers keyedBatch keyedQueue.empty ((3,20),7)
    (by simp [keyedBatch])

theorem keyed_length_bound :
    (keyedQueue.entries (keyedQueue.add keyedBatch keyedQueue.empty)).length ≤ 2 := by
  have h := keyedQueue.add_length keyedBatch keyedQueue.empty
  simpa only [keyedQueue.empty_entries, keyedBatch, List.length_cons,
    List.length_nil, Nat.add_zero] using h

/-- Only these fixed operations and the selected identity observation are excluded. -/
theorem fixed_keyed_not_exact :
    ¬ ExactLaws keyedQueue.toOperations keyedQueue.entries keyedQueue.Valid := by
  intro h
  have hlength := (h.add_exact keyedBatch keyedQueue.empty).length_eq
  have hone :
      (keyedQueue.entries (keyedQueue.add keyedBatch keyedQueue.empty)).length = 1 := by
    rw [keyed_replacement] <;> rfl
  have htwo : (keyedBatch ++ keyedQueue.entries keyedQueue.empty).length = 2 := rfl
  change (keyedQueue.entries (keyedQueue.add keyedBatch keyedQueue.empty)).length =
    (keyedBatch ++ keyedQueue.entries keyedQueue.empty).length at hlength
  omega

/-- The existing weakening preserves coverage without promising a converse. -/
example {α : Type u} {κ : Type v} (Q : ExactQueue.{u,0,z} α Nat)
    (key : α → κ) (xs : List (α × Nat)) (q : Q.Carrier) (e : α × Nat)
    (he : e ∈ xs ++ Q.entries q) :
    ∃ e' ∈ Q.entries (Q.add xs q), key e'.1 = key e.1 ∧ e'.2 ≤ e.2 :=
  (Q.keyed key).add_covers xs q e he

theorem empty_item_entries (Q : ExactQueue.{0,0,z} Empty Nat) (q : Q.Carrier) :
    Q.entries q = [] := by
  cases Q.entries q with
  | nil => rfl
  | cons e _ => exact e.1.elim

theorem empty_item_observation (Q : ExactQueue.{0,0,z} Empty Nat) (q : Q.Carrier) :
    Q.entryMultiset q = 0 ∧ Q.priorityMultiset q = 0 ∧ Q.remove q = none ∧
      Q.toOperations.peekPriority? q = none ∧ Q.toOperations.isEmpty q = true := by
  have he := Q.entryMultiset_eq_zero_of_isEmpty_payload q
  have hp := (Q.priorityMultiset_eq_zero_iff q).mpr he
  have hn := (Q.remove_none q).mpr (empty_item_entries Q q)
  have hv := Operations.views_of_none Q.toOperations q hn
  exact ⟨he, hp, hn, hv.2.1, hv.2.2.2⟩

example (q : PQ Empty Nat) :
    (exactLeftist : ExactQueue Empty Nat).toOperations.peekPriority? q = none :=
  (empty_item_observation exactLeftist q).2.2.2.1

example (q : List (Empty × Nat)) :
    (exactList : ExactQueue Empty Nat).toOperations.isEmpty q = true :=
  (empty_item_observation exactList q).2.2.2.2

theorem empty_payload_cannot_realize_one (Q : ExactQueue.{0,0,z} Empty Nat) :
    ¬ ∃ q, Q.Valid q ∧ Q.priorityMultiset q = {1} := by
  rintro ⟨q, _, hq⟩
  have hz := (empty_item_observation Q q).2.1
  rw [hq] at hz
  exact Multiset.singleton_ne_zero 1 hz

example {α : Type u} {π : Type v} (ops : Operations.{u,v,z} α π)
    (h : IsEmpty ops.Carrier) : False := h.false ops.empty

namespace Indiscrete

local instance : LE Bool := ⟨fun _ _ => True⟩
local instance : DecidableLE Bool := fun _ _ => isTrue trivial
local instance : Std.IsLinearPreorder Bool where
  le_refl := by intros; trivial
  le_trans := by intros; trivial
  le_total := by intros; exact Or.inl trivial

abbrev queue : ExactQueue Unit Bool := exactLeftist
def falsePriority : PQ Unit Bool := .fork 1 () false .null .null
def truePriority : PQ Unit Bool := .fork 1 () true .null .null
def falseRoot : PQ Unit Bool := combineQ falsePriority truePriority
def trueRoot : PQ Unit Bool := combineQ truePriority falsePriority

theorem false_priority_valid : queue.Valid falsePriority := by
  simp [queue, exactLeftist, falsePriority, Valid, Ranked, Heap, All, rank]

theorem true_priority_valid : queue.Valid truePriority := by
  simp [queue, exactLeftist, truePriority, Valid, Ranked, Heap, All, rank]

theorem false_root_valid : queue.Valid falseRoot :=
  combineQ_valid _ _ false_priority_valid true_priority_valid

theorem true_root_valid : queue.Valid trueRoot :=
  combineQ_valid _ _ true_priority_valid false_priority_valid

theorem false_root_remove :
    queue.remove falseRoot = some (((),false), truePriority) := by decide +kernel

theorem true_root_remove :
    queue.remove trueRoot = some (((),true), falsePriority) := by decide +kernel

theorem antisymmetry_fails : ¬ (∀ p q : Bool, p ≤ q → q ≤ p → p = q) := by
  intro h
  have he := h false true trivial trivial
  cases he

theorem equal_priority_contents : queue.priorityMultiset falseRoot = queue.priorityMultiset trueRoot := by
  decide +kernel

example : IsLeast {p | p ∈ queue.priorityMultiset falseRoot} false ∧
    IsLeast {p | p ∈ queue.priorityMultiset trueRoot} true :=
  ⟨(queue.remove_spec_multiset falseRoot ((),false) truePriority
      false_root_valid false_root_remove).2.2.2.1,
    (queue.remove_spec_multiset trueRoot ((),true) falsePriority
      true_root_valid true_root_remove).2.2.2.1⟩

theorem different_popObs : queue.popObs falseRoot ≠ queue.popObs trueRoot := by
  rw [queue.popObs_of_remove falseRoot ((),false) truePriority false_root_remove,
    queue.popObs_of_remove trueRoot ((),true) falsePriority true_root_remove]
  intro h
  have he : false = true := congrArg Prod.fst (Option.some.inj h)
  cases he

end Indiscrete

namespace EmptyPriority

local instance : LE Empty := ⟨fun _ _ => True⟩
local instance : DecidableLE Empty := fun _ _ => isTrue trivial
local instance : Std.IsLinearPreorder Empty where
  le_refl := by intros; trivial
  le_trans := by intros; trivial
  le_total := by intros; exact Or.inl trivial

abbrev queue : ExactQueue Unit Empty := exactLeftist
abbrev listQueue : ExactQueue Unit Empty := exactList

theorem raw_empty (q : PQ Unit Empty) : q = .null := by
  cases q with
  | null => rfl
  | fork _ _ p _ _ => exact p.elim

theorem list_raw_empty (q : List (Unit × Empty)) : q = [] := by
  cases q with
  | nil => rfl
  | cons e _ => exact e.2.elim

theorem no_priority_observation (Q : ExactQueue.{0,0,z} Unit Empty) (q : Q.Carrier) :
    Q.priorityMultiset q = 0 ∧ Q.remove q = none ∧ Q.toOperations.peekPriority? q = none := by
  have he := Q.entryMultiset_eq_zero_of_isEmpty_priority q
  have hp := (Q.priorityMultiset_eq_zero_iff q).mpr he
  have hn := (Q.remove_none_iff_priorityMultiset q).mpr hp
  exact ⟨hp, hn, (Operations.views_of_none Q.toOperations q hn).2.1⟩

example (q : PQ Unit Empty) :
    peekQ? q = none ∧ queue.toOperations.peekEntry? q = none ∧
      queue.toOperations.peekPriority? q = none := by
  have hd : peekQ? q = none := by rw [raw_empty q] <;> rfl
  refine ⟨hd, ?_, (no_priority_observation queue q).2.2⟩
  exact (deleteQ_fst q).trans hd

example (q : List (Unit × Empty)) : listQueue.toOperations.peekPriority? q = none ∧
    listQueue.toOperations.deleteMin q = q := by
  have hn := (listQueue.remove_none q).mpr (list_raw_empty q)
  exact ⟨(no_priority_observation listQueue q).2.2,
    (Operations.views_of_none listQueue.toOperations q hn).2.2.1⟩

end EmptyPriority

end PriorityModelExamples
