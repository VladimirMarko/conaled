import Applications.Sequences.AbstractStack
import Applications.Sequences.OrderedSummary
import Examples.DifferenceListCosts

/-!
# Full sequence agreement before ordered summarization

The PFDS stack append and the FDSA difference-list materializer preserve the
same full list, including order and repeated occurrences. The stack contract
uses a relation, so this agreement needs neither a total decoder nor a new
container interface. An actual summary client then uses the existing decoder
of the custom stack and the shared ordered-summary laws.

Charges remain separate: stack primitive invocations cost `4 * n + 1`, whereas
the materializer records `4 * n + 2` closure-creation/application events. These
different observations establish no machine-time comparison. Explicit fuel and
`Option` distinguish successful empty output from failed stack execution.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.TextbookSequences

open Sequences.AbstractStack Sequences.OrderedSummary Examples.DifferenceListCosts

universe u v
variable {α S : Type u} {M : Type v} [Monoid M]

/-- The original representation relation covers the entire materialized list.
Only sufficient-fuel inputs are claimed to succeed; each execution retains its
own public cost observation. -/
theorem append_materialize_correct {ops : Ops α S} {rel : S → List α → Prop}
    (laws : Laws ops rel) {s t : S} {xs ys : List α}
    (hs : rel s xs) (ht : rel t ys) {fuel : Nat} (enough : xs.length ≤ fuel) :
    ∃ r, appendRun ops fuel s t = (some r, 4 * xs.length + 1) ∧
      rel r (materialize xs ys).1 ∧
      (materialize xs ys).2 = 4 * xs.length + 2 := by
  obtain ⟨r, run, rep⟩ := appendRun_correct laws hs ht enough
  refine ⟨r, run, ?_, ?_⟩
  · rw [materialize_eq]
    exact rep
  · exact congrArg Prod.snd (materialize_eq xs ys)

/-- This concrete realization already has a full list observation. Its actual
optional summary result agrees with summarizing the other implementation's
output, for every monoid and every payload measure. -/
theorem custom_summary_materialize (measure : α → M) (s t : Stack α)
    {fuel : Nat} (enough : s.toList.length ≤ fuel) :
    ((appendRun (custom α) fuel s t).1.map fun r => summary measure r.toList) =
      some (summary measure (materialize s.toList t.toList).1) := by
  obtain ⟨r, run, rep, _⟩ := append_materialize_correct (custom_laws α)
    (s := s) (t := t) (xs := s.toList) (ys := t.toList) rfl rfl enough
  change r.toList = (materialize s.toList t.toList).1 at rep
  rw [run]
  change some (summary measure r.toList) = _
  rw [rep]

/-- The common client preserves multiplication order. No commutativity or
injectivity of the summary is assumed; full sequence agreement was proved first. -/
theorem custom_summary_append (measure : α → M) (s t : Stack α)
    {fuel : Nat} (enough : s.toList.length ≤ fuel) :
    ((appendRun (custom α) fuel s t).1.map fun r => summary measure r.toList) =
      some (summary measure s.toList * summary measure t.toList) := by
  rw [custom_summary_materialize measure s t enough, materialize_eq]
  rw [summary_append]

/-- A second observable client uses the existing composed append/head square;
empty head observations are kept as `Option`. -/
theorem append_head_materialize {ops : Ops α S} {rel : S → List α → Prop}
    (laws : Laws ops rel) {s t : S} {xs ys : List α}
    (hs : rel s xs) (ht : rel t ys) {fuel : Nat} (enough : xs.length ≤ fuel) :
    ((appendRun ops fuel s t).1.bind ops.head) = (materialize xs ys).1.head? := by
  rw [materialize_eq]
  exact appendHead_correct laws hs ht enough

private def taggedLeft : Stack (Nat × Bool) := .cons (3, true) (.cons (3, true) .nil)
private def taggedRight : Stack (Nat × Bool) := .cons (5, false) .nil

/-- Independent expected output: two repeated left entries followed by the
right entry. Processing two left entries requires nine stack calls; constructing
and applying the two-element difference list records ten closure events. -/
theorem tagged_full_sequence :
    ∃ r, appendRun (custom (Nat × Bool)) 2 taggedLeft taggedRight = (some r, 9) ∧
      r.toList = [(3, true), (3, true), (5, false)] ∧
      materialize [(3, true), (3, true)] [(5, false)] =
        ([(3, true), (3, true), (5, false)], 10) := by
  obtain ⟨r, run, rep, _⟩ := append_materialize_correct (custom_laws (Nat × Bool))
    (s := taggedLeft) (t := taggedRight)
    (xs := [(3, true), (3, true)]) (ys := [(5, false)]) rfl rfl (by decide : 2 ≤ 2)
  refine ⟨r, run, ?_, materialize_eq _ _⟩
  change r.toList = (materialize [(3, true), (3, true)] [(5, false)]).1 at rep
  simpa only [materialize_eq, List.cons_append, List.nil_append] using rep

/-- The diagnostic's word records the repeated labels in their original order,
alongside the independently expected length three. -/
theorem tagged_summary :
    ((appendRun (custom (Nat × Bool)) 2 taggedLeft taggedRight).1.map fun r =>
      diagnostic r.toList) =
      some (Multiplicative.ofAdd 3, FreeMonoid.ofList [true, true, false]) := by
  have agrees := custom_summary_materialize diagnosticMeasure taggedLeft taggedRight
    (by decide : taggedLeft.toList.length ≤ 2)
  calc
    _ = some (diagnostic (materialize taggedLeft.toList taggedRight.toList).1) := by
      simpa only [diagnostic] using agrees
    _ = some (Multiplicative.ofAdd 3, FreeMonoid.ofList [true, true, false]) := by
      rw [materialize_eq, diagnostic_value]
      rfl

/-- Empty success requires no inhabitants of the payload type and no recursive
fuel. The result is `some 1`, not the failure result `none`. -/
theorem empty_summary_success :
    ((appendRun (custom Empty) 0 .nil .nil).1.map fun r =>
      summary (lengthMeasure : Empty → Multiplicative Nat) r.toList) =
      some 1 := by
  simpa only [Stack.toList, summary_nil, one_mul] using
    custom_summary_append (lengthMeasure : Empty → Multiplicative Nat) .nil .nil
      (by decide : (Stack.nil : Stack Empty).toList.length ≤ 0)

/-- Dropping the fuel hypothesis would confuse failure with a valid sequence.
The difference-list execution still produces the nonempty ordered output. -/
theorem insufficient_fuel_boundary :
    ((appendRun (custom Bool) 0 (.cons true .nil) .nil).1.map fun r =>
      summary (FreeMonoid.of : Bool → FreeMonoid Bool) r.toList) = none ∧
      materialize [true] [] = ([true], 6) := by
  exact ⟨rfl, materialize_eq _ _⟩

end Examples.TextbookSequences
