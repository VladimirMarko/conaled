import Applications.Suspensions.Rules

/-!
# A failed pattern followed by a successful cached match

The inherited body fragment increments a reference and returns a captured
natural number. Literal matching has no additional effects. The expectation,
derived from Appendix A before the proof, is that matching the returned one
against zero fails but retains both the increment and cache. A second match
against one succeeds without another body execution.
-/
set_option warningAsError true

namespace Examples.SuspensionRules
open Suspensions Suspensions.Source

abbrev Memory := State Unit Nat Nat

def initial : Memory :=
  ⟨fun address => if address = 0 then some (.value 0)
    else if address = 1 then some (.thunk () 1) else none, 2, {11}⟩

def evaluateBody : Evaluation Unit Nat Nat Unit :=
  fun s captured _ answer t => ∃ counter,
    s.memory 0 = some (.value counter) ∧ answer = .ok captured ∧
      t = replace s 0 (.value (counter + 1))

def matchLiteral : Matching Unit Nat Nat Nat Unit Unit :=
  fun s _ literal value answer t =>
    answer = .ok (if value = literal then some () else none) ∧ t = s

def afterBody : Memory := replace initial 0 (.value 1)
def afterFailure : Memory := memoize afterBody 1 1

theorem body_deterministic {s env code a t b u}
    (first : evaluateBody s env code a t) (second : evaluateBody s env code b u) :
    a = b ∧ t = u := by
  rcases first with ⟨counter, lookup, rfl, rfl⟩
  rcases second with ⟨other, lookup', rfl, rfl⟩
  have same := lookup.symm.trans lookup'
  cases same
  exact ⟨rfl, rfl⟩

theorem literal_deterministic {s env pattern value a t b u}
    (first : matchLiteral s env pattern value a t)
    (second : matchLiteral s env pattern value b u) : a = b ∧ t = u := by
  rcases first with ⟨rfl, rfl⟩
  rcases second with ⟨rfl, rfl⟩
  exact ⟨rfl, rfl⟩

theorem failed_match :
    SuspensionMatch evaluateBody matchLiteral initial 99 1 0 (.ok none) afterFailure := by
  apply SuspensionMatch.evaluated (code := ()) (captured := 1) (value := 1)
    (afterBody := afterBody)
  · rfl
  · exact ⟨0, rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

theorem failed_match_state :
    afterFailure.memory 0 = some (.value 1) ∧
      afterFailure.memory 1 = some (.value 1) ∧
      afterFailure.next = 2 ∧ afterFailure.exceptionNames = {11} := by
  refine ⟨?_, memoize_lookup afterBody 1 1, rfl, rfl⟩
  exact (memoize_other afterBody 1 1 (by decide : 0 ≠ 1)).trans
    (replace_lookup initial 0 (.value 1))

/-- Any derivation in this explicit body/matcher realization has the expected
failed outcome and reached state, not just the selected derivation above. -/
theorem failed_match_unique {answer final}
    (run : SuspensionMatch evaluateBody matchLiteral initial 99 1 0 answer final) :
    answer = .ok none ∧ final = afterFailure :=
  suspension_deterministic body_deterministic literal_deterministic run failed_match

theorem next_match_cached :
    SuspensionMatch evaluateBody matchLiteral afterFailure 99 1 1
      (.ok (some ())) afterFailure := by
  apply (suspension_cached_iff (memoize_lookup afterBody 1 1)).mpr
  exact ⟨rfl, rfl⟩

/-- Both requests use the same address; the counter is still one after the
successful second match, despite the first request having failed. -/
theorem failure_then_success :
    ∃ middle final,
      SuspensionMatch evaluateBody matchLiteral initial 99 1 0 (.ok none) middle ∧
      SuspensionMatch evaluateBody matchLiteral middle 99 1 1 (.ok (some ())) final ∧
      final.memory 0 = some (.value 1) ∧ final.memory 1 = some (.value 1) := by
  exact ⟨afterFailure, afterFailure, failed_match, next_match_cached,
    failed_match_state.1, failed_match_state.2.1⟩

end Examples.SuspensionRules
