import Applications.Search.BinomialQueue.Maximum
import Applications.Search.MaximumQueue

/-!
The complete Nat source contract and its explicit occurrence observation enter
the established maximum-to-minimum queue adapter on the valid-state subtype.
Native meld remains the source merge operation.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Search.BinomialQueue

/-- The four original source operations on Nat keys. -/
def natOperations : MaximumQueue.Operations (Queue Nat) where
  empty := empty
  insert := insert natGreater
  deleteMax := deleteMax natGreater
  merge := merge natGreater

@[simp] theorem natOperations_empty : natOperations.empty = empty := rfl
@[simp] theorem natOperations_insert (key : Nat) (q : Queue Nat) :
    natOperations.insert key q = insert natGreater key q := rfl
@[simp] theorem natOperations_deleteMax (q : Queue Nat) :
    natOperations.deleteMax q = deleteMax natGreater q := rfl
@[simp] theorem natOperations_merge (p q : Queue Nat) :
    natOperations.merge p q = merge natGreater p q := rfl

/-- Every one of the eleven relational source fields is proved with its guards. -/
theorem nat_laws : MaximumQueue.Laws natOperations Valid Abs where
  can_relate := can_relate
  abs_perm := abs_perm
  empty_valid := empty_valid
  empty_relate := empty_relate
  insert_valid := insert_valid natGreater natGreater_eq
  insert_relate := insert_relate natGreater
  deleteMax_none := deleteMax_none_relate natGreater
  deleteMax_valid := deleteMax_some_valid natGreater_eq
  deleteMax_relate := deleteMax_some_relate natGreater_eq
  merge_valid := merge_valid natGreater natGreater_eq
  merge_relate := merge_relate natGreater

/-- The existing interface counts all occurrences, with Nat maximum interpreted
as minimum under OrderDual. Validity is carried by the actual source state. -/
def exactQueue : PriorityInterface.ExactQueue Unit (OrderDual Nat) :=
  MaximumQueue.exactQueueOnValid natOperations nat_laws contents
    (fun q _ => queue_elems_contents q)

@[simp] theorem exactQueue_entries (q : {q : Queue Nat // Valid q}) :
    exactQueue.entries q = (contents q.val).map MaximumQueue.encode := rfl

@[simp] theorem exactQueue_valid (q : {q : Queue Nat // Valid q}) : exactQueue.Valid q := trivial

@[simp] theorem exactQueue_empty_val : exactQueue.empty.val = empty := rfl

@[simp] theorem exactQueue_add_singleton_val (key : Nat)
    (q : {q : Queue Nat // Valid q}) :
    (exactQueue.add [MaximumQueue.encode key] q).val = insert natGreater key q.val := rfl

/-- Batch insertion retains the existing interface's fold order and calls the
actual source insertion for each decoded entry. -/
theorem exactQueue_add_val (entries : List (Unit × OrderDual Nat))
    (q : {q : Queue Nat // Valid q}) :
    (exactQueue.add entries q).val =
      entries.foldr (fun entry rest => insert natGreater (MaximumQueue.decode entry) rest) q.val := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
      change insert natGreater (MaximumQueue.decode entry) (exactQueue.add entries q).val = _
      rw [ih]
      rfl

theorem exactQueue_remove_some (p q : {q : Queue Nat // Valid q})
    (entry : Unit × OrderDual Nat) :
    exactQueue.remove p = some (entry, q) ↔
      deleteMax natGreater p.val = some (MaximumQueue.decode entry, q.val) :=
  MaximumQueue.exactQueueOnValid_remove_some natOperations nat_laws contents
    (fun r _ => queue_elems_contents r) p q entry

theorem exactQueue_remove_val (q : {q : Queue Nat // Valid q}) :
    (exactQueue.remove q).map (fun (entry, rest) => (MaximumQueue.decode entry, rest.val)) =
      deleteMax natGreater q.val := by
  change (((MaximumQueue.validOperations natOperations nat_laws).deleteMax q).map
    (fun (key, rest) => (MaximumQueue.encode key, rest))).map
      (fun (entry, rest) => (MaximumQueue.decode entry, rest.val)) = _
  rw [Option.map_map]
  exact MaximumQueue.validOperations_deleteMax_val natOperations nat_laws q

/-- Native meld on the valid subtype is supplied by the existing source adapter. -/
def mergeValid (p q : {q : Queue Nat // Valid q}) : {q : Queue Nat // Valid q} :=
  (MaximumQueue.validOperations natOperations nat_laws).merge p q

@[simp] theorem mergeValid_val (p q : {q : Queue Nat // Valid q}) :
    (mergeValid p q).val = merge natGreater p.val q.val := rfl

theorem mergeValid_entries (p q : {q : Queue Nat // Valid q}) :
    (exactQueue.entries (mergeValid p q)).Perm (exactQueue.entries p ++ exactQueue.entries q) :=
  MaximumQueue.encoded_merge_entries nat_laws contents (fun r _ => queue_elems_contents r)
    p.val q.val p.property q.property

@[simp] theorem mergeValid_valid (p q : {q : Queue Nat // Valid q}) :
    exactQueue.Valid (mergeValid p q) := trivial

end Search.BinomialQueue
