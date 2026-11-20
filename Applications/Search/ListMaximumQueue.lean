import Applications.Search.MaximumQueue
import Applications.Sorting.SourceSelection

/-!
# The source list maximum queue

The VFA Priqueue selector is the accepted comparison-before-recursion selector
at the reversed natural order. It retains the candidate on ties and reconstructs
the exact source remainder. The queue stores its list directly: insertion is
cons, deletion exposes that selector, and native merge is append. Concrete
abstraction is identity, independently of the occurrence equivalence used by
the public queue contract.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Search.ListMaximumQueue

open Applications.Sorting

abbrev Key := Nat
abbrev Queue := List Key

/-- Reversing the comparison changes minimum selection into source maximum
selection without preprocessing or replacing its recursion. -/
def selectMax (seed : Nat) (tail : List Nat) : Nat × List Nat :=
  SourceSelection.select (fun candidate head : Nat => head ≤ candidate) seed tail

theorem selectMax_eq_source (seed : Nat) (tail : List Nat) :
    selectMax seed tail =
      SourceSelection.select (fun candidate head : Nat => head ≤ candidate) seed tail := rfl

/-- Order duality changes the relation, not the stored list or its traversal. -/
theorem selectMax_eq_dual (seed : Nat) (tail : List Nat) :
    selectMax seed tail =
      SourceSelection.select (α := OrderDual Nat) (· ≤ ·) seed tail := rfl

theorem selectMax_nil (seed : Nat) : selectMax seed [] = (seed, []) := rfl

/-- The Boolean source branch is tested before the actual recursive call. -/
theorem selectMax_cons (seed head : Nat) (tail : List Nat) :
    selectMax seed (head :: tail) = if decide (head ≤ seed) then
      ((selectMax seed tail).1, head :: (selectMax seed tail).2)
    else ((selectMax head tail).1, seed :: (selectMax head tail).2) := by
  by_cases keep : head ≤ seed <;>
    simp [selectMax, SourceSelection.select_cons, keep]

/-- Source orientation: the input is permuted to the selected entry and remainder.
The underlying occurrence theorem requires no order laws. -/
theorem select_perm (seed : Nat) (tail : List Nat) :
    let (chosen, rest) := selectMax seed tail
    (seed :: tail).Perm (chosen :: rest) :=
  (SourceSelection.select_perm (fun candidate head : Nat => head ≤ candidate) seed tail).symm

theorem select_length (seed : Nat) (tail : List Nat) :
    (selectMax seed tail).2.length = tail.length :=
  SourceSelection.select_length (fun candidate head : Nat => head ≤ candidate) seed tail

theorem select_mem (seed : Nat) (tail : List Nat) :
    (selectMax seed tail).1 ∈ seed :: tail :=
  SourceSelection.select_mem (fun candidate head : Nat => head ≤ candidate) seed tail

theorem select_seed_le (seed : Nat) (tail : List Nat) :
    seed ≤ (selectMax seed tail).1 :=
  SourceSelection.select_le_seed (α := OrderDual Nat) (· ≤ ·) seed tail

theorem select_maximum (seed : Nat) (tail : List Nat) :
    ∀ key ∈ seed :: tail, key ≤ (selectMax seed tail).1 :=
  SourceSelection.select_lower (α := OrderDual Nat) (· ≤ ·) seed tail

/-- The source auxiliary exercise retains its redundant remainder-bound premise.
The stronger accepted seed theorem discharges its conclusion directly. -/
theorem select_biggest_aux (seed : Nat) (tail : List Nat) (chosen : Nat)
    (rest : List Nat) (_upper : List.Forall (fun key => key ≤ chosen) rest)
    (selected : selectMax seed tail = (chosen, rest)) : seed ≤ chosen := by
  simpa only [selected] using select_seed_le seed tail

/-- The source Forall bound on the exact reconstructed remainder. -/
theorem select_biggest (seed : Nat) (tail : List Nat) (chosen : Nat)
    (rest : List Nat) (selected : selectMax seed tail = (chosen, rest)) :
    List.Forall (fun key => key ≤ chosen) rest := by
  apply List.forall_iff_forall_mem.mpr
  have bound : ∀ key ∈ (selectMax seed tail).2, key ≤ (selectMax seed tail).1 :=
    SourceSelection.select_smallest (α := OrderDual Nat) (· ≤ ·) seed tail
  simpa only [selected] using bound

def empty : Queue := []

def insert (key : Key) (queue : Queue) : Queue := key :: queue

def deleteMax : Queue → Option (Key × Queue)
  | [] => none
  | seed :: tail => some (selectMax seed tail)

def merge (left right : Queue) : Queue := left ++ right

/-- Every raw source list is a valid queue. -/
def Valid (_queue : Queue) : Prop := True

/-- The source one-constructor abstraction is precisely list identity. -/
def Abs (queue : Queue) (meaning : List Nat) : Prop := queue = meaning

theorem abs_intro (queue : Queue) : Abs queue queue := rfl

theorem abs_eq {queue : Queue} {meaning : List Nat} (related : Abs queue meaning) :
    queue = meaning := related

theorem abs_iff (queue : Queue) (meaning : List Nat) :
    Abs queue meaning ↔ queue = meaning := Iff.rfl

theorem valid (queue : Queue) : Valid queue := trivial

theorem empty_eq : empty = [] := rfl

theorem insert_eq (key : Key) (queue : Queue) : insert key queue = key :: queue := rfl

theorem deleteMax_nil : deleteMax [] = none := rfl

theorem deleteMax_cons (seed : Nat) (tail : List Nat) :
    deleteMax (seed :: tail) = some (selectMax seed tail) := rfl

theorem merge_eq (left right : Queue) : merge left right = left ++ right := rfl

theorem can_relate (queue : Queue) (_valid : Valid queue) :
    ∃ meaning, Abs queue meaning := ⟨queue, abs_intro queue⟩

theorem abs_perm (queue : Queue) (left right : List Nat) (_valid : Valid queue)
    (left_related : Abs queue left) (right_related : Abs queue right) : left.Perm right := by
  rw [← abs_eq left_related, ← abs_eq right_related]

theorem empty_valid : Valid empty := trivial

theorem empty_relate : Abs empty [] := rfl

theorem insert_valid (key : Nat) (queue : Queue) (_valid : Valid queue) :
    Valid (insert key queue) := trivial

theorem insert_relate (queue : Queue) (meaning : List Nat) (key : Nat)
    (_valid : Valid queue) (related : Abs queue meaning) :
    Abs (insert key queue) (key :: meaning) := by
  change key :: queue = key :: meaning
  rw [abs_eq related]

theorem deleteMax_none (queue : Queue) (_valid : Valid queue) :
    Abs queue [] ↔ deleteMax queue = none := by
  cases queue <;> simp [Abs, deleteMax]

theorem deleteMax_valid (queue rest : Queue) (key : Nat) (_valid : Valid queue)
    (_deleted : deleteMax queue = some (key, rest)) : Valid rest := trivial

theorem deleteMax_relate (queue rest : Queue) (key : Nat) (meaning residual : List Nat)
    (_valid : Valid queue) (related : Abs queue meaning)
    (deleted : deleteMax queue = some (key, rest)) (rest_related : Abs rest residual) :
    meaning.Perm (key :: residual) ∧ ∀ entry ∈ residual, entry ≤ key := by
  subst meaning
  subst residual
  cases queue with
  | nil => simp [deleteMax] at deleted
  | cons seed tail =>
      have selected : selectMax seed tail = (key, rest) := Option.some.inj deleted
      refine ⟨?_, List.forall_iff_forall_mem.mp (select_biggest seed tail key rest selected)⟩
      simpa only [selected] using select_perm seed tail

theorem merge_valid (left right : Queue) (_left_valid : Valid left)
    (_right_valid : Valid right) : Valid (merge left right) := trivial

theorem merge_relate (left right : Queue) (left_meaning right_meaning output : List Nat)
    (_left_valid : Valid left) (_right_valid : Valid right)
    (left_related : Abs left left_meaning) (right_related : Abs right right_meaning)
    (output_related : Abs (merge left right) output) :
    output.Perm (left_meaning ++ right_meaning) := by
  rw [← abs_eq output_related, ← abs_eq left_related, ← abs_eq right_related]
  exact List.Perm.refl _


/-- The complete source operations record keeps the ordinary list carrier. -/
def ops : MaximumQueue.Operations Queue where
  empty := empty
  insert := insert
  deleteMax := deleteMax
  merge := merge

/-- Every field is discharged by the concrete source proof above. -/
theorem laws : MaximumQueue.Laws ops Valid Abs where
  can_relate := can_relate
  abs_perm := abs_perm
  empty_valid := empty_valid
  empty_relate := empty_relate
  insert_valid := insert_valid
  insert_relate := insert_relate
  deleteMax_none := deleteMax_none
  deleteMax_valid := deleteMax_valid
  deleteMax_relate := deleteMax_relate
  merge_valid := merge_valid
  merge_relate := merge_relate

/-- Literal Forall presentation of the successful-deletion source exercise. -/
theorem deleteMax_relate_forall (queue rest : Queue) (key : Nat)
    (meaning residual : List Nat) (queue_valid : Valid queue) (related : Abs queue meaning)
    (deleted : deleteMax queue = some (key, rest)) (rest_related : Abs rest residual) :
    meaning.Perm (key :: residual) ∧ List.Forall (fun entry => entry ≤ key) residual := by
  have related_result := deleteMax_relate queue rest key meaning residual
    queue_valid related deleted rest_related
  exact ⟨related_result.1, List.forall_iff_forall_mem.mpr related_result.2⟩

/-- Identity observation supplies a concrete witness, without changing Abs. -/
def observe (queue : Queue) : List Nat := queue

theorem observe_spec (queue : Queue) (_valid : Valid queue) : Abs queue (observe queue) := rfl

/-- The shared all-valid adapter retains List Nat as its raw carrier. The map
belongs to the observation; operations execute the supplied source functions. -/
def exactQueue : PriorityInterface.ExactQueue Unit (OrderDual Nat) :=
  MaximumQueue.exactQueueOfAllValid ops laws observe observe_spec valid

theorem exactQueue_empty : exactQueue.empty = empty := rfl

theorem exactQueue_entries (queue : Queue) :
    exactQueue.entries queue = queue.map MaximumQueue.encode := rfl

theorem exactQueue_add_singleton (key : Nat) (queue : Queue) :
    exactQueue.add [MaximumQueue.encode key] queue = insert key queue := rfl

/-- A mathematical description of the direct insertion fold. No preprocessing
map is inserted into the executable adapter. -/
theorem exactQueue_add_keys (keys : List Nat) (queue : Queue) :
    exactQueue.add (keys.map MaximumQueue.encode) queue = keys ++ queue := by
  induction keys with
  | nil => rfl
  | cons key keys ih =>
      change insert key (exactQueue.add (keys.map MaximumQueue.encode) queue) =
        (key :: keys) ++ queue
      rw [ih]
      rfl

theorem exactQueue_remove (queue : Queue) :
    exactQueue.remove queue =
      (deleteMax queue).map (fun (key, rest) => (MaximumQueue.encode key, rest)) := rfl

/-- Native source merge is observed separately; ExactQueue has no meld field. -/
theorem exactQueue_native_merge (left right : Queue) :
    exactQueue.entries (merge left right) = exactQueue.entries left ++ exactQueue.entries right := by
  simp only [exactQueue_entries, merge_eq, List.map_append]

end Search.ListMaximumQueue
