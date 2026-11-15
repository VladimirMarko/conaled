import Applications.Search.OrderedMap.TotalTable
import Applications.Search.OrderedMap.AssociationList
import Applications.Search.OrderedMap.Basic

/-! One total-table client reused by native functions and partial shadowing
lists. Expected results specify chronological writes independently. No runtime
or representation-equality comparison follows from these observations. -/
set_option autoImplicit false
set_option warningAsError true

namespace TotalTableExamples
open Search
universe u v w

/-- The executable client takes operations, not their proof or a decoder. -/
def queryAfter {κ : Type u} {ν : Type v} {T : Type w}
    (ops : TotalTable.Ops κ ν T) (writes : List (κ × ν)) (start : T) (q : κ) : ν :=
  ops.get q (TotalTable.setAll ops writes start)

/-- Any valid corresponding starting tables can replace each other. -/
theorem list_function_client {κ : Type u} {ν : Type v} [DecidableEq κ]
    (d : ν) (writes entries : List (κ × ν)) (q : κ) :
    queryAfter (TotalTable.ofPartial (OrderedMap.lists κ ν) d) writes entries q =
      queryAfter (TotalTable.functions d) writes
        (OrderedMap.withDefault d (OrderedMap.listObserve entries)) q := by
  exact congrFun
    ((TotalTable.ofPartial_unrestricted OrderedMap.lists_laws d).setAll_agrees
      (TotalTable.functions_laws d) writes trivial trivial rfl) q

/-- The reused partial client also agrees with the integrated observation
square's existing specification. -/
theorem list_spec {κ : Type u} {ν : Type v} [DecidableEq κ]
    (d : ν) (writes entries : List (κ × ν)) :
    TotalTable.observe (TotalTable.ofPartial (OrderedMap.lists κ ν) d)
        (TotalTable.setAll (TotalTable.ofPartial (OrderedMap.lists κ ν) d) writes entries) =
      OrderedMap.withDefault d (OrderedMap.writeAll writes (OrderedMap.listObserve entries)) :=
  TotalTable.observe_partial_setAll OrderedMap.lists_laws d writes entries

/-- No ordered-key structure is used by this contract. -/
theorem repeated_bool_keys (q : Bool) :
    queryAfter (TotalTable.ofPartial (OrderedMap.lists Bool String) "default")
      [(false, "old"), (true, "other"), (false, "new")] [] q =
        (if q then "other" else "new") := by
  rw [list_function_client]
  cases q <;> rfl

/-- Empty updates preserve an arbitrary starting function. -/
example {κ : Type u} {ν : Type v} [DecidableEq κ] (d : ν) (f : κ → ν) (q : κ) :
    queryAfter (TotalTable.functions d) [] f q = f q := rfl

/-- The third key keeps its supplied initial value. -/
example : queryAfter (TotalTable.ofPartial (OrderedMap.lists Nat String) "default")
    [(0, "old"), (1, "other"), (0, "new")] [(2, "retained")] 2 = "retained" := by
  rw [list_function_client]
  rfl

/-- Default lookup forgets a real difference in presence, through the current
partial-map theorem rather than an invented total-table presence operation. -/
example : ∃ m n : OrderedMap.Meaning Bool String,
    m ≠ n ∧ OrderedMap.withDefault "default" m = OrderedMap.withDefault "default" n :=
  OrderedMap.forget_default_not_injective false "default"

example :
    queryAfter (TotalTable.ofPartial (OrderedMap.lists Bool String) "default")
      [(false, "default")] [] false = "default" ∧
    OrderedMap.hasBinding (OrderedMap.listObserve [(false, "default")]) false = true ∧
    OrderedMap.hasBinding (OrderedMap.listObserve ([] : List (Bool × String))) false = false := by
  refine ⟨?_, rfl, rfl⟩
  rw [list_function_client]
  rfl

/-- Raw states carry a validity tag. Invalid states deliberately disobey the
same-key law, demonstrating why the contract retains its input premise. -/
def tagged : TotalTable.Ops Bool Nat ((Bool → Nat) × Bool) where
  empty := (fun _ => 0, true)
  get k t := if t.2 then t.1 k else 0
  set k v t := (Function.update t.1 k v, t.2)

def Valid (t : (Bool → Nat) × Bool) : Prop := t.2 = true

theorem tagged_laws : TotalTable.Laws tagged 0 Valid where
  empty_valid := rfl
  set_valid _ _ _ ht := ht
  get_empty _ := rfl
  get_set_same k v t ht := by simp [tagged, Valid] at ht ⊢; simp [ht]
  get_set_other k q v t hne ht := by
    simp only [Valid] at ht
    simp [tagged, ht, Ne.symm hne]

/-- The public arbitrary-list law preserves the actual final validity. -/
example (writes : List (Bool × Nat)) :
    Valid (TotalTable.setAll tagged writes tagged.empty) :=
  tagged_laws.setAll_valid writes tagged_laws.empty_valid

example : tagged.get false (tagged.set false 7 (fun _ => 0, false)) ≠ 7 := by decide

/-- A valid raw client can be compared to native functions without hiding the
validity precondition or requiring a partial-map decoder. -/
theorem tagged_function_client (writes : List (Bool × Nat))
    (t : (Bool → Nat) × Bool) (ht : Valid t) (q : Bool) :
    queryAfter tagged writes t q =
      queryAfter (TotalTable.functions 0) writes t.1 q := by
  apply congrFun (tagged_laws.setAll_agrees (TotalTable.functions_laws 0)
    writes ht trivial ?_) q
  funext k
  simp only [Valid] at ht
  simp [TotalTable.observe, tagged, TotalTable.functions, ht]

/-- The existing ordered-tree validity proof supplies the raw total-table
contract. This instantiates the raw adapter, not only its True specialization. -/
theorem rawTree_laws {κ ν : Type u} [LinearOrder κ] (d : ν) :
    TotalTable.Laws (TotalTable.ofPartial (OrderedMap.rawTrees κ ν) d) d
      (Search.OrderedTree.OrderedBy Prod.fst) :=
  TotalTable.ofPartial_laws (OrderedMap.rawTrees κ ν) OrderedMap.observe
    (Search.OrderedTree.OrderedBy Prod.fst) d trivial
    (fun k v _ ht => OrderedMap.ordered_bind ht k v) OrderedMap.trees_laws

theorem rawTree_client {κ ν : Type u} [LinearOrder κ] (d : ν)
    (writes : List (κ × ν)) (t : BinaryTree (κ × ν))
    (ht : Search.OrderedTree.OrderedBy Prod.fst t) (q : κ) :
    queryAfter (TotalTable.ofPartial (OrderedMap.rawTrees κ ν) d) writes t q =
      queryAfter (TotalTable.functions d) writes
        (OrderedMap.withDefault d (OrderedMap.observe t)) q := by
  apply congrFun ((rawTree_laws d).setAll_agrees (TotalTable.functions_laws d)
    writes ht trivial ?_) q
  funext k
  change (OrderedMap.lookup k t).getD d = (OrderedMap.observe t k).getD d
  rw [OrderedMap.lookup_correct ht k]

end TotalTableExamples
