import Applications.Search.RectangleSweep.Measured
import Applications.Resources.ListIndex
import Applications.Resources.ListCalls
import Applications.Resources.ListReversal
import Mathlib.Tactic.Ring

/-!
# Measured rectangle event generation and pipeline composition

The indexed input is computed once and its returned list feeds both event maps.
Their actual returned lists feed measured append. Constructor callbacks may carry
input-dependent costs. Value erasure is a separate premise, not a replacement of
the actual returned values. Generation costs are paid before sorting and scanning,
including when the later scan returns early.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Search.RectangleSweep
open Resources
universe u v w
variable {α : Type u} {β : Type v} {S : Type w} [LE α]

section Generation
variable [LE β]

def rawEventsRun (pairCost succCost : Nat)
    (makeRun : Kind → Rectangle α β → Nat → Measured (Event α β) Nat)
    (rs : List (Rectangle α β)) : Measured (List (Event α β)) Nat :=
  Resources.bind (ListIndex.run pairCost succCost rs 0) fun indexed =>
    Resources.bind (ListCalls.mapRun (fun p => makeRun .insert p.1 p.2) indexed) fun insertions =>
      Resources.bind (ListCalls.mapRun (fun p => makeRun .delete p.1 p.2) indexed) fun deletions =>
        ListReversal.appendRun insertions deletions

theorem rawEventsRun_value (pairCost succCost : Nat)
    (makeRun : Kind → Rectangle α β → Nat → Measured (Event α β) Nat)
    (make_value : ∀ kind r id, (makeRun kind r id).1 = eventFor r kind id)
    (rs : List (Rectangle α β)) :
    (rawEventsRun pairCost succCost makeRun rs).1 = rawEvents rs := by
  simp [rawEventsRun, Resources.bind, ListIndex.run_value, ListCalls.mapRun_value,
    ListReversal.appendRun_exact, make_value, rawEvents]

/-- Both maps preserve length even when callbacks return noncanonical events. -/
theorem rawEventsRun_length (pairCost succCost : Nat)
    (makeRun : Kind → Rectangle α β → Nat → Measured (Event α β) Nat)
    (rs : List (Rectangle α β)) :
    (rawEventsRun pairCost succCost makeRun rs).1.length = 2 * rs.length := by
  simp [rawEventsRun, Resources.bind, ListIndex.run_value, ListCalls.mapRun_value,
    ListReversal.appendRun_exact, Nat.two_mul]

/-- Input-dependent constructor observations are summed at their actual IDs. -/
theorem rawEventsRun_cost (pairCost succCost : Nat)
    (makeRun : Kind → Rectangle α β → Nat → Measured (Event α β) Nat)
    (rs : List (Rectangle α β)) :
    (rawEventsRun pairCost succCost makeRun rs).2 =
      (rs.zipIdx.map (fun p => (makeRun .insert p.1 p.2).2)).sum +
      (rs.zipIdx.map (fun p => (makeRun .delete p.1 p.2).2)).sum +
      (pairCost + succCost + 4) * rs.length + 4 := by
  simp only [rawEventsRun, Resources.bind, ListIndex.run_value, ListIndex.run_cost,
    ListCalls.mapRun_value, ListCalls.mapRun_cost, ListReversal.appendRun_exact,
    List.length_map, List.length_zipIdx]
  ring

theorem rawEventsRun_cost_of_constant (pairCost succCost insertion deletion : Nat)
    (makeRun : Kind → Rectangle α β → Nat → Measured (Event α β) Nat)
    (rs : List (Rectangle α β))
    (insert_cost : ∀ p ∈ rs.zipIdx, (makeRun .insert p.1 p.2).2 = insertion)
    (delete_cost : ∀ p ∈ rs.zipIdx, (makeRun .delete p.1 p.2).2 = deletion) :
    (rawEventsRun pairCost succCost makeRun rs).2 =
      (pairCost + succCost + insertion + deletion + 4) * rs.length + 4 := by
  have hi := ListCalls.mapRun_cost_of_constant
    (fun p : Rectangle α β × Nat => makeRun .insert p.1 p.2) rs.zipIdx insertion insert_cost
  have hd := ListCalls.mapRun_cost_of_constant
    (fun p : Rectangle α β × Nat => makeRun .delete p.1 p.2) rs.zipIdx deletion delete_cost
  simp only [List.length_zipIdx] at hi hd
  simp only [rawEventsRun, Resources.bind, ListIndex.run_value, ListIndex.run_cost,
    ListReversal.appendRun_exact, ListCalls.mapRun_value, List.length_map,
    List.length_zipIdx, hi, hd]
  ring

def rawEventsRunConst (pairCost succCost insertion deletion : Nat)
    (rs : List (Rectangle α β)) : Measured (List (Event α β)) Nat :=
  rawEventsRun pairCost succCost
    (fun kind r id => (eventFor r kind id, match kind with
      | .insert => insertion
      | .delete => deletion)) rs

theorem rawEventsRunConst_exact (pairCost succCost insertion deletion : Nat)
    (rs : List (Rectangle α β)) :
    rawEventsRunConst pairCost succCost insertion deletion rs =
      (rawEvents rs, (pairCost + succCost + insertion + deletion + 4) * rs.length + 4) := by
  apply Prod.ext
  · exact rawEventsRun_value pairCost succCost _ (by intros; rfl) rs
  · exact rawEventsRun_cost_of_constant pairCost succCost insertion deletion _ rs
      (by intros; rfl) (by intros; rfl)

/-- One generation and one sorter invocation supply the events actually scanned. -/
def sweepRun (pairCost succCost : Nat)
    (makeRun : Kind → Rectangle α β → Nat → Measured (Event α β) Nat)
    (sortRun : List (Event α β) → Measured (List (Event α β)) Nat)
    (insertRun deleteRun : Key α → S → Measured S Nat)
    (queryRun : S → IntervalKey α → Measured Bool Nat)
    (entry terminal : Nat) (empty : S) (rs : List (Rectangle α β)) : Measured Bool Nat :=
  Resources.bind (rawEventsRun pairCost succCost makeRun rs) fun generated =>
    Resources.bind (sortRun generated) fun sorted =>
      scanRun insertRun deleteRun queryRun entry terminal empty sorted

theorem sweepRun_cost (pairCost succCost : Nat)
    (makeRun : Kind → Rectangle α β → Nat → Measured (Event α β) Nat)
    (sortRun : List (Event α β) → Measured (List (Event α β)) Nat)
    (insertRun deleteRun : Key α → S → Measured S Nat)
    (queryRun : S → IntervalKey α → Measured Bool Nat)
    (entry terminal : Nat) (empty : S) (rs : List (Rectangle α β)) :
    (sweepRun pairCost succCost makeRun sortRun insertRun deleteRun queryRun
      entry terminal empty rs).2 =
      (rawEventsRun pairCost succCost makeRun rs).2 +
      (sortRun (rawEventsRun pairCost succCost makeRun rs).1).2 +
      (scanRun insertRun deleteRun queryRun entry terminal empty
        (sortRun (rawEventsRun pairCost succCost makeRun rs).1).1).2 := by
  simp [sweepRun, Resources.bind, Nat.add_assoc]

end Generation

section Canonical
variable [LinearOrder β]

/-- Erasure identifies the actual stage inputs, while retaining each observation. -/
theorem sweepRun_cost_of_values (pairCost succCost : Nat)
    (makeRun : Kind → Rectangle α β → Nat → Measured (Event α β) Nat)
    (sortRun : List (Event α β) → Measured (List (Event α β)) Nat)
    (insertRun deleteRun : Key α → S → Measured S Nat)
    (queryRun : S → IntervalKey α → Measured Bool Nat)
    (entry terminal : Nat) (empty : S)
    (make_value : ∀ kind r id, (makeRun kind r id).1 = eventFor r kind id)
    (sort_value : ∀ es, (sortRun es).1 = sortEvents es)
    (rs : List (Rectangle α β)) :
    (sweepRun pairCost succCost makeRun sortRun insertRun deleteRun queryRun
      entry terminal empty rs).2 =
      (rawEventsRun pairCost succCost makeRun rs).2 + (sortRun (rawEvents rs)).2 +
      (scanRun insertRun deleteRun queryRun entry terminal empty (events rs)).2 := by
  rw [sweepRun_cost, rawEventsRun_value _ _ _ make_value, sort_value]
  rfl

theorem sweepRun_value (pairCost succCost : Nat)
    (ops : AbstractSet.DeleteOps (Key α) S) (query : S → IntervalKey α → Bool)
    (makeRun : Kind → Rectangle α β → Nat → Measured (Event α β) Nat)
    (sortRun : List (Event α β) → Measured (List (Event α β)) Nat)
    (insertRun deleteRun : Key α → S → Measured S Nat)
    (queryRun : S → IntervalKey α → Measured Bool Nat) (entry terminal : Nat)
    (make_value : ∀ kind r id, (makeRun kind r id).1 = eventFor r kind id)
    (sort_value : ∀ es, (sortRun es).1 = sortEvents es)
    (insert_value : ∀ key state, (insertRun key state).1 = ops.insert key state)
    (delete_value : ∀ key state, (deleteRun key state).1 = ops.delete key state)
    (query_value : ∀ state interval, (queryRun state interval).1 = query state interval)
    (rs : List (Rectangle α β)) :
    (sweepRun pairCost succCost makeRun sortRun insertRun deleteRun queryRun
      entry terminal ops.empty rs).1 = sweep ops query rs := by
  simp only [sweepRun, bind_value, rawEventsRun_value _ _ _ make_value, sort_value]
  exact scanRun_value ops query insertRun deleteRun queryRun entry terminal
    insert_value delete_value query_value ops.empty (events rs)

end Canonical
end Search.RectangleSweep
