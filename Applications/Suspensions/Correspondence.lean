import Applications.Suspensions.Rules
import Applications.Suspensions.Continuation

/-!
# Realizing the suspension rules through finite execution

The source rule schemata are instantiated with the existing finite-evaluation
judgment for the explicit core machine. Outcomes, environments and reached
states remain visible. Continuation composition supplies the important bridge:
a body is not evaluated by an opaque, assumed-terminating host operation.
-/
set_option warningAsError true

namespace Suspensions.Core.Correspondence
open Machine

variable {Primitive : Type}

def evaluationResult : Except (Value Primitive) (Value Primitive) → Result Primitive
  | .ok value => .value value
  | .error packet => .raised packet

def matchingResult : Except (Value Primitive) (Option (Env Primitive)) → Result Primitive
  | .ok (some bindings) => .matched bindings
  | .ok none => .mismatch
  | .error packet => .raised packet

def evaluation (parameters : Parameters Primitive) :
    Source.Evaluation (Expr Primitive) (Env Primitive) (Value Primitive) (Value Primitive) :=
  fun s env expression answer t =>
    ∃ steps, Progress.Evaluates (step parameters) (start s env expression)
      ⟨t, evaluationResult answer⟩ steps

def matching (parameters : Parameters Primitive) :
    Source.Matching (Expr Primitive) (Env Primitive) (Value Primitive) Pattern
      (Env Primitive) (Value Primitive) :=
  fun s env pattern value answer t =>
    ∃ steps, Progress.Evaluates (step parameters) (startPattern s env pattern value)
      ⟨t, matchingResult answer⟩ steps

theorem after_step_iff {parameters : Parameters Primitive} {before after : Config Primitive}
    {answer : Answer Primitive} (edge : step parameters before = .inr after) :
    (∃ steps, Progress.Evaluates (step parameters) before answer steps) ↔
      ∃ steps, Progress.Evaluates (step parameters) after answer steps := by
  constructor
  · rintro ⟨_, run⟩
    cases run with
    | done finished => simp [edge] at finished
    | next moved rest =>
      rw [edge] at moved
      cases moved
      exact ⟨_, rest⟩
  · rintro ⟨_, rest⟩
    exact ⟨_, .next edge rest⟩

theorem matching_cached_iff {parameters : Parameters Primitive} {s : Memory Primitive}
    {env : Env Primitive} {inner : Pattern} {address : Nat} {value : Value Primitive}
    {answer : Except (Value Primitive) (Option (Env Primitive))} {t : Memory Primitive}
    (found : s.memory address = some (.value value)) :
    matching parameters s env (.suspended inner) (.address address) answer t ↔
      matching parameters s env inner value answer t := by
  apply after_step_iff
  simpa [step, startPattern, continue] using
    congrArg Prod.fst (hit_transition parameters s env inner address value [] found)

/-- Every derivation of the independent forcing rules is realized by finite
machine execution, including exception propagation and failed inner matching. -/
theorem suspension_match_sound {parameters : Parameters Primitive}
    {s : Memory Primitive} {caller : Env Primitive} {address : Nat} {inner : Pattern}
    {answer : Except (Value Primitive) (Option (Env Primitive))} {t : Memory Primitive}
    (run : Source.SuspensionMatch (evaluation parameters) (matching parameters)
      s caller address inner answer t) :
    matching parameters s caller (.suspended inner) (.address address) answer t := by
  cases run with
  | cached found matched => exact (matching_cached_iff found).mpr matched
  | @evaluated s caller address inner code captured value afterBody answer afterMatch
      found body matched =>
    rcases body with ⟨bodySteps, bodyRun⟩
    rcases matched with ⟨matchSteps, matchRun⟩
    have continuation : Progress.Evaluates (step parameters)
        ⟨afterBody, .value value, [.memoize address caller inner]⟩
        ⟨afterMatch, matchingResult answer⟩ (matchSteps + 1) := by
      apply Progress.Evaluates.next
      · simpa [step, continue] using congrArg Prod.fst
          (memoize_before_match parameters afterBody caller inner address value [])
      · exact matchRun
    have resumed := evaluates_append bodyRun (by rfl) [.memoize address caller inner] continuation
    apply (after_step_iff (before := startPattern s caller (.suspended inner) (.address address))
      (after := ⟨s, .eval captured code, [.memoize address caller inner]⟩) ?_).mpr
    · exact ⟨_, by simpa [appendFrames, start] using resumed⟩
    · simpa [step, startPattern, continue] using congrArg Prod.fst
        (body_transition parameters s caller captured inner address code [] found)
  | @raised s caller address inner code captured packet afterBody found body =>
    rcases body with ⟨bodySteps, bodyRun⟩
    have continuation : Progress.Evaluates (step parameters)
        ⟨afterBody, .raised packet, [.memoize address caller inner]⟩
        ⟨afterBody, .raised packet⟩ 2 :=
      .next (by rfl) (.done (by rfl))
    have resumed := evaluates_append bodyRun (by rfl) [.memoize address caller inner] continuation
    apply (after_step_iff (before := startPattern s caller (.suspended inner) (.address address))
      (after := ⟨s, .eval captured code, [.memoize address caller inner]⟩) ?_).mpr
    · exact ⟨_, by simpa [appendFrames, start, matchingResult] using resumed⟩
    · simpa [step, startPattern, continue] using congrArg Prod.fst
        (body_transition parameters s caller captured inner address code [] found)

end Suspensions.Core.Correspondence
