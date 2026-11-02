import Applications.Suspensions.Continuation

/-!
# Finite continuation decomposition, including faults

A finite run with appended caller frames either faults in the isolated body,
retaining that same answer and transition count, or first delivers a boundary
and then executes the caller. The caller itself may fault. This distinction is
needed when interpreting raw executions without a type-safety assumption.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Suspensions.Core.Machine
variable {Primitive : Type}

/-- Caller frames cannot recover an isolated machine fault. Source exceptions
remain a separate delivered boundary and may be handled by those frames. -/
theorem evaluates_stuck_append {parameters : Parameters Primitive} {config : Config Primitive}
    {answer : Answer Primitive} {steps : Nat}
    (body : Progress.Evaluates (step parameters) config answer steps)
    (stuck : boundaryControl answer.result = none) (tail : List (Frame Primitive)) :
    Progress.Evaluates (step parameters) (appendFrames config tail) answer steps := by
  induction body with
  | done finished => exact .done (step_stuck_append finished stuck tail)
  | next moved _ ih => exact .next (step_append moved tail) (ih stuck)

/-- Every finite plugged execution decomposes, without a restriction on its
final answer. An isolated fault and a later caller fault are different cases. -/
theorem evaluates_split_all {parameters : Parameters Primitive} {config : Config Primitive}
    {tail : List (Frame Primitive)} {answer : Answer Primitive} {steps : Nat}
    (whole : Progress.Evaluates (step parameters) (appendFrames config tail) answer steps) :
    (Progress.Evaluates (step parameters) config answer steps ∧
      boundaryControl answer.result = none) ∨
    ∃ bodyAnswer control n m,
      Progress.Evaluates (step parameters) config bodyAnswer n ∧
      boundaryControl bodyAnswer.result = some control ∧
      Progress.Evaluates (step parameters) ⟨bodyAnswer.memory, control, tail⟩ answer m ∧
      steps = (n - 1) + m := by
  induction steps using Nat.strong_induction_on generalizing config with
  | h steps ih =>
      cases first : step parameters config with
      | inl bodyAnswer =>
          cases boundary : boundaryControl bodyAnswer.result with
          | some control =>
              have shape := step_boundary first boundary
              refine .inr ⟨bodyAnswer, control, 1, steps, .done first, boundary, ?_, by simp⟩
              simpa only [shape, appendFrames, List.nil_append] using whole
          | none =>
              have finished := step_stuck_append first boundary tail
              have same := (Progress.Evaluates.done finished).unique whole
              refine .inl ⟨?_, ?_⟩
              · rw [← same.1, ← same.2]
                exact .done first
              · simpa only [← same.1] using boundary
      | inr next =>
          have moved := step_append first tail
          cases whole with
          | done finished => simp [moved] at finished
          | @next _ actual _ remaining actualMoved rest =>
              have same : appendFrames next tail = actual :=
                Sum.inr.inj (moved.symm.trans actualMoved)
              subst actual
              rcases ih remaining (by omega) rest with ⟨body, stuck⟩ |
                ⟨bodyAnswer, control, n, m, body, boundary, residual, count⟩
              · exact .inl ⟨.next first body, stuck⟩
              · refine .inr ⟨bodyAnswer, control, n + 1, m, .next first body,
                  boundary, residual, ?_⟩
                have positive : 0 < n := by cases body <;> omega
                omega

end Suspensions.Core.Machine
