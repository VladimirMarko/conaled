import Applications.Search.OrderedMap.Basic
import Applications.Search.OrderedMap.AssociationList
import Applications.Search.OrderedMap.Observations
import SquareKit.Combinators

/-!
# Shared map clients across the textbook developments

PFDS ordered trees, the FDSA-XA01 AList realization and VFA shadowing lists use
one partial-map contract. Existing synchronization connects full binding-list
clients; vertical pasting supplies default-valued lookup. Full partial meaning
retains both absence and explicitly stored optional/default values.

These are value-level relationships. Equality of lookup observations transfers
no allocation, physical sharing, callback count or runtime cost. The preserved
generic total-table, deletion and modification capabilities require their own
subsequent integration; this slice does not accept an entire book chapter.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.TextbookMaps
open Search.OrderedMap
open Squares

universe u v

section GeneralClients
variable {κ : Type u} {ν : Type v} [DecidableEq κ]

/-- Arbitrary matching initial states and every binding list are covered,
including repeated keys; equality concerns complete partial observations. -/
theorem alist_list_agrees (bindings : List (κ × ν))
    (m : AList (fun _ : κ => ν)) (entries : List (κ × ν))
    (same : alistObserve m = listObserve entries) :
    alistObserve (bindAll (alists κ ν) bindings m) =
      listObserve (bindAll (lists κ ν) bindings entries) :=
  alists_laws.bindAll_observation_agrees lists_laws bindings same

/-- The function realization can start from any actual AList observation.
No finite-support or representation-isomorphism premise enters the shared law. -/
theorem alist_function_agrees (bindings : List (κ × ν))
    (m : AList (fun _ : κ => ν)) :
    alistObserve (bindAll (alists κ ν) bindings m) =
      bindAll (functions κ ν) bindings (alistObserve m) :=
  alists_laws.bindAll_observation_agrees functions_laws bindings rfl

end GeneralClients

section SynchronizedClients
variable {κ ν : Type u} [LinearOrder κ]

/-- The existing agreement construction retains both the raw-list execution
and the independently implemented ordered tree on matching initial meanings. -/
def jointWrites (bindings : List (κ × ν)) :
    Square
      (synchronized (listObserve : List (κ × ν) → Meaning κ ν)
        (decode : Tree κ ν → Meaning κ ν))
      (synchronized (listObserve : List (κ × ν) → Meaning κ ν)
        (decode : Tree κ ν → Meaning κ ν)) :=
  synchronize (lists_laws.bindAllSquare bindings)
    (trees_laws.bindAllSquare bindings) (fun _ => rfl)

theorem paired_outputs (bindings : List (κ × ν)) (entries : List (κ × ν))
    (t : Tree κ ν) (same : listObserve entries = decode t) :
    listObserve (bindAll (lists κ ν) bindings entries) =
      decode (bindAll (trees κ ν) bindings t) :=
  synchronize_agrees (lists_laws.bindAllSquare bindings)
    (trees_laws.bindAllSquare bindings) (fun _ => rfl) ⟨(entries, t), same⟩

/-- A standard AList and an ordered tree execute the same chronological client.
The intermediate raw list is a proved bridge, not equality of concrete states. -/
theorem alist_tree_from_empty (bindings : List (κ × ν)) :
    alistObserve (bindAll (alists κ ν) bindings (alists κ ν).empty) =
      decode (bindAll (trees κ ν) bindings (trees κ ν).empty) := by
  apply (alist_list_agrees bindings (alists κ ν).empty []
    ((alists_laws (κ := κ) (ν := ν)).empty.trans
      (lists_laws (κ := κ) (ν := ν)).empty.symm)).trans
  exact paired_outputs bindings [] (trees κ ν).empty
    ((lists_laws (κ := κ) (ν := ν)).empty.trans
      (trees_laws (κ := κ) (ν := ν)).empty.symm)

end SynchronizedClients

private def changes : List (Nat × Option Nat) :=
  [(2, some 7), (1, none), (2, some 9)]

private def written : AList (fun _ : Nat => Option Nat) :=
  bindAll (alists Nat (Option Nat)) changes (alists Nat (Option Nat)).empty

/-- Independent expectations: key two keeps the last value, key one contains
an optional payload `none`, and key three is absent. -/
theorem stored_none_and_absent :
    (alists Nat (Option Nat)).lookup 1 written = some none ∧
    (alists Nat (Option Nat)).lookup 3 written = none ∧
    (alists Nat (Option Nat)).lookup 2 written = some (some 9) := by
  have laws := alists_laws (κ := Nat) (ν := Option Nat)
  have atKey (query : Nat) :
      (alists Nat (Option Nat)).lookup query written =
        writeAll changes (fun _ => none) query := by
    simpa only [written, laws.empty] using
      laws.lookup_bindAll changes (alists Nat (Option Nat)).empty query
  exact ⟨(atKey 1).trans (by rfl), (atKey 3).trans (by rfl),
    (atKey 2).trans (by rfl)⟩

/-- Defaulting both queries to `none` loses their distinct presence bits. -/
theorem defaulted_optional_boundary :
    withDefault none (alistObserve written) 1 = none ∧
    withDefault none (alistObserve written) 3 = none ∧
    hasBinding (alistObserve written) 1 = true ∧
    hasBinding (alistObserve written) 3 = false := by
  have found : alistObserve written 1 = some none := stored_none_and_absent.1
  have absent : alistObserve written 3 = none := stored_none_and_absent.2.1
  simp [withDefault, hasBinding, found, absent]

/-- The actual list client uses the vertically pasted default observation.
The expected total table is false at zero, one and two, and true at three. -/
theorem default_client (query : Nat) :
    withDefault false
        (listObserve (bindAll (lists Nat Bool) [(1, false), (3, true)] [])) query =
      if query = 3 then true else false := by
  have h := congrFun
    (((lists_laws (κ := Nat) (ν := Bool)).defaultBindAllSquare false
      [(1, false), (3, true)]).commutes []) query
  change withDefault false
      (listObserve (bindAll (lists Nat Bool) [(1, false), (3, true)] [])) query =
    (Function.update (Function.update (fun _ : Nat => false) 1 false) 3 true) query at h
  simpa [Function.update_apply] using h

/-- Raw first-match lists and chronological writes require the proved reversal.
Without it this repeated-key input gives two different observed values. -/
theorem precedence_boundary :
    listLookup 0 ([(0, "new"), (0, "old")] : List (Nat × String)) = some "new" ∧
    listObserve
      (bindAll (lists Nat String) [(0, "new"), (0, "old")] []) 0 = some "old" := by
  refine ⟨rfl, ?_⟩
  rw [bindAll_lists]
  rfl

/-- A shadowed raw entry is not the observed binding at its key. -/
theorem shadowed_entry :
    (0, "old") ∈ ([(0, "new"), (0, "old")] : List (Nat × String)) ∧
    listLookup 0 ([(0, "new"), (0, "old")] : List (Nat × String)) ≠ some "old" := by
  decide

/-- The partial-map core needs no default inhabitant of its payload type. -/
theorem empty_payload (query : Nat) :
    (functions Nat Empty).lookup query (functions Nat Empty).empty = none :=
  congrFun (functions_laws (κ := Nat) (ν := Empty)).empty query

/-- Bool keys and type-valued payloads live in different universes. Values need
no equality or ordering decision; this uses the ordinary public map laws. -/
theorem type_valued_payload :
    (functions Bool Type).lookup true
      ((functions Bool Type).bind true Nat (functions Bool Type).empty) = some Nat := by
  have laws := functions_laws (κ := Bool) (ν := Type)
  rw [laws.lookup, laws.bind]
  rfl

private def malformed : BinaryTree (Nat × String) :=
  .node (0, "root") (.node (1, "hidden") .nil .nil) .nil

/-- The valid-state restriction matters: directed lookup can miss a binding
seen by the independent whole-tree observation on an invalid raw tree. -/
theorem invalid_tree_boundary :
    lookup 1 malformed = none ∧ observe malformed 1 = some "hidden" ∧
      ¬ Search.OrderedTree.OrderedBy Prod.fst malformed := by
  decide

end Examples.TextbookMaps
