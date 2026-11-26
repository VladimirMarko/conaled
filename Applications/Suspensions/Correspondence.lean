import Applications.Suspensions.Rules
import Applications.Suspensions.Continuation
import Applications.Suspensions.Return

/-!
# Realizing the suspension rules through finite execution

The source rule schemata are instantiated with the existing finite-evaluation
judgment for the explicit core machine. Outcomes, environments and reached
states remain visible. Continuation composition supplies the important bridge:
a body is not evaluated by an opaque, assumed-terminating host operation.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Suspensions.Core.Correspondence
open Machine

variable {Primitive : Type}

def evaluationResult : Except (Value Primitive) (Value Primitive) → Result Primitive
  | .ok value => .value value
  | .error packet => .raised packet

def evaluationControl : Except (Value Primitive) (Value Primitive) → Control Primitive
  | .ok value => .value value
  | .error packet => .raised packet

theorem evaluation_boundary (answer : Except (Value Primitive) (Value Primitive)) :
    boundaryControl (evaluationResult answer) = some (evaluationControl answer) := by
  cases answer <;> rfl

def matchingResult : Except (Value Primitive) (Option (Env Primitive)) → Result Primitive
  | .ok (some bindings) => .matched bindings
  | .ok none => .mismatch
  | .error packet => .raised packet

theorem evaluationResult_injective : Function.Injective (@evaluationResult Primitive) := by
  intro first second same
  cases first <;> cases second <;> cases same <;> rfl

theorem matchingResult_injective : Function.Injective (@matchingResult Primitive) := by
  intro first second same
  cases first with
  | error packet =>
      cases second with
      | error other => cases same; rfl
      | ok result => cases result <;> cases same
  | ok result =>
      cases second with
      | error packet => cases result <;> cases same
      | ok other => cases result <;> cases other <;> cases same <;> rfl

def matchingControl : Except (Value Primitive) (Option (Env Primitive)) → Control Primitive
  | .ok (some bindings) => .matched bindings
  | .ok none => .mismatch
  | .error packet => .raised packet

theorem matching_boundary (answer : Except (Value Primitive) (Option (Env Primitive))) :
    boundaryControl (matchingResult answer) = some (matchingControl answer) := by
  cases answer with
  | ok result => cases result <;> rfl
  | error packet => rfl

theorem matching_not_stuck (answer : Except (Value Primitive) (Option (Env Primitive)))
    (fault : Fault) : matchingResult answer ≠ .stuck fault := by
  intro same
  have boundary := matching_boundary answer
  rw [same] at boundary
  cases boundary

theorem matching_raised {answer : Except (Value Primitive) (Option (Env Primitive))}
    {packet : Value Primitive} (same : matchingResult answer = .raised packet) :
    answer = .error packet := by
  cases answer with
  | ok result => cases result <;> cases same
  | error exception => cases same; rfl

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

theorem evaluation_deterministic {parameters : Parameters Primitive}
    {s : Memory Primitive} {env : Env Primitive} {expression : Expr Primitive}
    {first second : Except (Value Primitive) (Value Primitive)} {t u : Memory Primitive}
    (left : evaluation parameters s env expression first t)
    (right : evaluation parameters s env expression second u) : first = second ∧ t = u := by
  obtain ⟨_, left⟩ := left
  obtain ⟨_, right⟩ := right
  have same := (left.unique right).1
  exact ⟨evaluationResult_injective (congrArg Answer.result same), congrArg Answer.memory same⟩

theorem matching_deterministic {parameters : Parameters Primitive}
    {s : Memory Primitive} {env : Env Primitive} {pattern : Pattern} {value : Value Primitive}
    {first second : Except (Value Primitive) (Option (Env Primitive))} {t u : Memory Primitive}
    (left : matching parameters s env pattern value first t)
    (right : matching parameters s env pattern value second u) : first = second ∧ t = u := by
  obtain ⟨_, left⟩ := left
  obtain ⟨_, right⟩ := right
  have same := (left.unique right).1
  exact ⟨matchingResult_injective (congrArg Answer.result same), congrArg Answer.memory same⟩

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
  simpa [step, startPattern, proceed] using
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
  | @evaluated code captured value afterBody answer _ found body matched =>
    rcases body with ⟨bodySteps, bodyRun⟩
    rcases matched with ⟨matchSteps, matchRun⟩
    have continuation : Progress.Evaluates (step parameters)
        ⟨afterBody, .value value, [.memoize address caller inner]⟩
        ⟨t, matchingResult answer⟩ (matchSteps + 1) := by
      apply Progress.Evaluates.next
      · simpa [step, proceed] using congrArg Prod.fst
          (memoize_before_match parameters afterBody caller inner address value [])
      · exact matchRun
    have resumed := evaluates_append bodyRun (by rfl) [.memoize address caller inner] continuation
    apply (after_step_iff (before := startPattern s caller (.suspended inner) (.address address))
      (after := ⟨s, .eval captured code, [.memoize address caller inner]⟩) ?_).mpr
    · exact ⟨_, by simpa [appendFrames, start] using resumed⟩
    · simpa [step, startPattern, proceed] using congrArg Prod.fst
        (body_transition parameters s caller captured inner address code [] found)
  | @raised code captured packet _ found body =>
    rcases body with ⟨bodySteps, bodyRun⟩
    have continuation : Progress.Evaluates (step parameters)
        ⟨t, .raised packet, [.memoize address caller inner]⟩
        ⟨t, .raised packet⟩ 2 :=
      .next (by rfl) (.done (by rfl))
    have resumed := evaluates_append bodyRun (by rfl) [.memoize address caller inner] continuation
    apply (after_step_iff (before := startPattern s caller (.suspended inner) (.address address))
      (after := ⟨s, .eval captured code, [.memoize address caller inner]⟩) ?_).mpr
    · exact ⟨_, by simpa [appendFrames, start, matchingResult] using resumed⟩
    · simpa [step, startPattern, proceed] using congrArg Prod.fst
        (body_transition parameters s caller captured inner address code [] found)

/-- Finite non-stuck execution has one of the independent source derivations.
The body is split from its actual continuation. A matched environment or an
ordinary mismatch cannot masquerade as an expression result: such a boundary
would immediately fault at the memoization frame. -/
theorem suspension_match_complete {parameters : Parameters Primitive}
    {s : Memory Primitive} {caller : Env Primitive} {address : Nat} {inner : Pattern}
    {answer : Except (Value Primitive) (Option (Env Primitive))} {t : Memory Primitive}
    (run : matching parameters s caller (.suspended inner) (.address address) answer t) :
    Source.SuspensionMatch (evaluation parameters) (matching parameters)
      s caller address inner answer t := by
  cases found : s.memory address with
  | none =>
      rcases run with ⟨steps, run⟩
      have fault : step parameters (startPattern s caller (.suspended inner) (.address address)) =
          .inl ⟨s, .stuck (.missingAddress address)⟩ := by
        simp [step, transition, startPattern, found, finish]
      have same := (Progress.Evaluates.done fault).unique run
      exact False.elim (matching_not_stuck answer _ (congrArg Answer.result same.1).symm)
  | some cell =>
      cases cell with
      | value value => exact .cached found ((matching_cached_iff found).mp run)
      | thunk code captured =>
          have moved : step parameters
              (startPattern s caller (.suspended inner) (.address address)) =
              .inr ⟨s, .eval captured code, [.memoize address caller inner]⟩ := by
            simpa [step, startPattern, proceed] using congrArg Prod.fst
              (body_transition parameters s caller captured inner address code [] found)
          obtain ⟨steps, plugged⟩ := (after_step_iff moved).mp run
          have full : Progress.Evaluates (step parameters)
              (appendFrames (start s captured code) [.memoize address caller inner])
              ⟨t, matchingResult answer⟩ steps := by
            simpa [appendFrames, start] using plugged
          obtain ⟨bodyAnswer, control, n, m, body, boundary, residual, _⟩ :=
            evaluates_split full (matching_boundary answer)
          rcases bodyAnswer with ⟨afterBody, result⟩
          cases result with
          | value value =>
              simp only [boundaryControl, Option.some.injEq] at boundary
              subst control
              have write : step parameters
                  ⟨afterBody, .value value, [.memoize address caller inner]⟩ =
                  .inr (startPattern (Suspensions.memoize afterBody address value)
                    caller inner value) := rfl
              exact .evaluated found ⟨n, body⟩ ((after_step_iff write).mp ⟨m, residual⟩)
          | raised packet =>
              simp only [boundaryControl, Option.some.injEq] at boundary
              subst control
              have unwind : Progress.Evaluates (step parameters)
                  ⟨afterBody, .raised packet, [.memoize address caller inner]⟩
                  ⟨afterBody, .raised packet⟩ 2 := .next rfl (.done rfl)
              have same := (unwind.unique residual).1
              have stateEq : afterBody = t := congrArg Answer.memory same
              have answerEq := matching_raised (congrArg Answer.result same).symm
              subst t
              subst answer
              exact .raised found ⟨n, body⟩
          | matched bindings =>
              simp only [boundaryControl, Option.some.injEq] at boundary
              subst control
              have fault : step parameters
                  ⟨afterBody, .matched bindings, [.memoize address caller inner]⟩ =
                  .inl ⟨afterBody, .stuck .invalidContinuation⟩ := rfl
              have same := (Progress.Evaluates.done fault).unique residual
              exact False.elim (matching_not_stuck answer _ (congrArg Answer.result same.1).symm)
          | mismatch =>
              simp only [boundaryControl, Option.some.injEq] at boundary
              subst control
              have fault : step parameters
                  ⟨afterBody, .mismatch, [.memoize address caller inner]⟩ =
                  .inl ⟨afterBody, .stuck .invalidContinuation⟩ := rfl
              have same := (Progress.Evaluates.done fault).unique residual
              exact False.elim (matching_not_stuck answer _ (congrArg Answer.result same.1).symm)
          | stuck fault => cases boundary

theorem suspension_match_iff {parameters : Parameters Primitive}
    {s : Memory Primitive} {caller : Env Primitive} {address : Nat} {inner : Pattern}
    {answer : Except (Value Primitive) (Option (Env Primitive))} {t : Memory Primitive} :
    Source.SuspensionMatch (evaluation parameters) (matching parameters)
        s caller address inner answer t ↔
      matching parameters s caller (.suspended inner) (.address address) answer t :=
  ⟨suspension_match_sound, suspension_match_complete⟩

/-- Reference-pattern Rule158 reads the current value cell and then runs the
inner pattern from that same state. In particular, the reached state is not
reset when the inner pattern fails or raises. -/
theorem reference_match_iff {parameters : Parameters Primitive}
    {s : Memory Primitive} {caller : Env Primitive} {address : Nat} {inner : Pattern}
    {answer : Except (Value Primitive) (Option (Env Primitive))} {t : Memory Primitive} :
    Source.ReferenceMatch (matching parameters) s caller address inner answer t ↔
      matching parameters s caller (.reference inner) (.address address) answer t := by
  constructor
  · intro source
    cases source with
    | @read value answer t found matched =>
        apply (after_step_iff (before := startPattern s caller (.reference inner) (.address address))
          (after := startPattern s caller inner value) ?_).mpr matched
        simp [step, transition, startPattern, proceed, found]
  · intro run
    cases found : s.memory address with
    | none =>
        rcases run with ⟨steps, run⟩
        have fault : step parameters (startPattern s caller (.reference inner) (.address address)) =
            .inl ⟨s, .stuck (.missingAddress address)⟩ := by
          simp [step, transition, startPattern, found, finish]
        have same := (Progress.Evaluates.done fault).unique run
        exact False.elim (matching_not_stuck answer _ (congrArg Answer.result same.1).symm)
    | some cell =>
        cases cell with
        | value value =>
            apply Source.ReferenceMatch.read found
            apply (after_step_iff (before := startPattern s caller (.reference inner) (.address address))
              (after := startPattern s caller inner value) ?_).mp run
            simp [step, transition, startPattern, proceed, found]
        | thunk code captured =>
            rcases run with ⟨steps, run⟩
            have fault : step parameters (startPattern s caller (.reference inner) (.address address)) =
                .inl ⟨s, .stuck .expectedReferenceValue⟩ := by
              simp [step, transition, startPattern, found, finish]
            have same := (Progress.Evaluates.done fault).unique run
            exact False.elim (matching_not_stuck answer _ (congrArg Answer.result same.1).symm)

def clauseResult : Except (Value Primitive) (Option (Value Primitive)) → Result Primitive
  | .ok (some value) => .value value
  | .ok none => .mismatch
  | .error packet => .raised packet

def clauseControl : Except (Value Primitive) (Option (Value Primitive)) → Control Primitive
  | .ok (some value) => .value value
  | .ok none => .mismatch
  | .error packet => .raised packet

theorem clause_boundary (answer : Except (Value Primitive) (Option (Value Primitive))) :
    boundaryControl (clauseResult answer) = some (clauseControl answer) := by
  cases answer with
  | ok result => cases result <;> rfl
  | error packet => rfl

theorem clauseResult_injective : Function.Injective (@clauseResult Primitive) := by
  intro first second same
  cases first with
  | error packet =>
      cases second with
      | error other => cases same; rfl
      | ok result => cases result <;> cases same
  | ok result =>
      cases second with
      | error packet => cases result <;> cases same
      | ok other => cases result <;> cases other <;> cases same <;> rfl

def Clauses (parameters : Parameters Primitive) (s : Memory Primitive) (env : Env Primitive)
    (value : Value Primitive) (alternatives : List (Pattern × Expr Primitive))
    (answer : Except (Value Primitive) (Option (Value Primitive))) (t : Memory Primitive) : Prop :=
  ∃ steps, Progress.Evaluates (step parameters) ⟨s, .clauses env alternatives value, []⟩
    ⟨t, clauseResult answer⟩ steps

/-- A successful or exceptional head returns directly. Only ordinary failure
enters the remaining clauses, using the memory reached by the failed pattern. -/
def clauseBoundary (s : Memory Primitive) (env : Env Primitive) (value : Value Primitive)
    (remaining : List (Pattern × Expr Primitive)) :
    Except (Value Primitive) (Option (Value Primitive)) → Config Primitive
  | .ok (some result) => ⟨s, .value result, []⟩
  | .ok none => ⟨s, .clauses env remaining value, []⟩
  | .error packet => ⟨s, .raised packet, []⟩

/-- Realize one independent source clause before its actual residual run.
The expression and pattern premises are finite machine runs, composed through
their explicit frames; no body is hidden inside an atomic transition. -/
theorem clause_resumes {parameters : Parameters Primitive}
    {s : Memory Primitive} {env : Env Primitive} {value : Value Primitive}
    {head : Pattern × Expr Primitive} {remaining : List (Pattern × Expr Primitive)}
    {answer : Except (Value Primitive) (Option (Value Primitive))} {t : Memory Primitive}
    (source : Source.ClauseMatch (evaluation parameters) (matching parameters) Env.extend
      s env value head answer t)
    {final : Answer Primitive} {residualSteps : Nat}
    (residual : Progress.Evaluates (step parameters)
      (clauseBoundary t env value remaining answer) final residualSteps) :
    ∃ steps, Progress.Evaluates (step parameters)
      ⟨s, .clauses env (head :: remaining) value, []⟩ final steps := by
  cases source with
  | @success pattern code bindings afterPattern result t matched evaluated =>
      obtain ⟨patternSteps, patternRun⟩ := matched
      obtain ⟨bodySteps, bodyRun⟩ := evaluated
      have bodyResidual : Progress.Evaluates (step parameters)
          ⟨t, evaluationControl result, []⟩ final residualSteps := by
        cases result <;> exact residual
      have bodyResumed := evaluates_append bodyRun (evaluation_boundary result) [] bodyResidual
      have patternResidual : Progress.Evaluates (step parameters)
          ⟨afterPattern, .matched bindings, [.clause env code remaining value]⟩
          final (((bodySteps - 1) + residualSteps) + 1) := by
        apply Progress.Evaluates.next (by rfl)
        simpa only [appendFrames_nil, start] using bodyResumed
      have resumed := evaluates_append patternRun rfl [.clause env code remaining value]
        patternResidual
      exact ⟨_, .next rfl (by simpa [appendFrames, startPattern] using resumed)⟩
  | @failure pattern code t matched =>
      obtain ⟨patternSteps, patternRun⟩ := matched
      have patternResidual : Progress.Evaluates (step parameters)
          ⟨t, .mismatch, [.clause env code remaining value]⟩ final (residualSteps + 1) :=
        .next rfl residual
      have resumed := evaluates_append patternRun rfl [.clause env code remaining value]
        patternResidual
      exact ⟨_, .next rfl (by simpa [appendFrames, startPattern] using resumed)⟩
  | @raised pattern code packet t matched =>
      obtain ⟨patternSteps, patternRun⟩ := matched
      have patternResidual : Progress.Evaluates (step parameters)
          ⟨t, .raised packet, [.clause env code remaining value]⟩ final (residualSteps + 1) :=
        .next rfl residual
      have resumed := evaluates_append patternRun rfl [.clause env code remaining value]
        patternResidual
      exact ⟨_, .next rfl (by simpa [appendFrames, startPattern] using resumed)⟩

/-- Source Rules124–128 are realized by the ordered-clause machine. Every
failed-pattern state is passed to the next source clause and its execution. -/
theorem alternatives_sound {parameters : Parameters Primitive}
    {s : Memory Primitive} {env : Env Primitive} {value : Value Primitive}
    {alternatives : List (Pattern × Expr Primitive)}
    {answer : Except (Value Primitive) (Option (Value Primitive))} {t : Memory Primitive}
    (source : Source.Alternatives
      (Source.ClauseMatch (evaluation parameters) (matching parameters) Env.extend)
      s env value alternatives answer t) :
    Clauses parameters s env value alternatives answer t := by
  induction source with
  | empty => exact ⟨2, .next rfl (.done rfl)⟩
  | success clause => exact clause_resumes clause (.done rfl)
  | failure clause _ rest =>
      obtain ⟨steps, run⟩ := rest
      exact clause_resumes clause run
  | raised clause => exact clause_resumes clause (.done rfl)

/-- Ordered-clause execution also yields an independent source derivation.
The return-class invariant rules out raw expression mismatch and raw pattern
values; this is weaker than, and independent of, value-type preservation. -/
theorem alternatives_complete {parameters : Parameters Primitive}
    {s : Memory Primitive} {env : Env Primitive} {value : Value Primitive}
    {alternatives : List (Pattern × Expr Primitive)}
    {answer : Except (Value Primitive) (Option (Value Primitive))} {t : Memory Primitive}
    (run : Clauses parameters s env value alternatives answer t) :
    Source.Alternatives
      (Source.ClauseMatch (evaluation parameters) (matching parameters) Env.extend)
      s env value alternatives answer t := by
  induction alternatives generalizing s t answer with
  | nil =>
      obtain ⟨steps, run⟩ := run
      have empty : Progress.Evaluates (step parameters)
          ⟨s, .clauses env [] value, []⟩ ⟨s, clauseResult (.ok none)⟩ 2 :=
        .next rfl (.done rfl)
      have same := (empty.unique run).1
      have stateEq : s = t := congrArg Answer.memory same
      have resultEq : clauseResult (.ok none) = clauseResult answer :=
        congrArg Answer.result same
      have answerEq := clauseResult_injective (Primitive := Primitive) resultEq
      subst t
      subst answer
      exact .empty
  | cons head rest ih =>
      rcases head with ⟨pattern, code⟩
      have moved : step parameters ⟨s, .clauses env ((pattern, code) :: rest) value, []⟩ =
          .inr ⟨s, .pattern env pattern value, [.clause env code rest value]⟩ := rfl
      obtain ⟨steps, plugged⟩ := (after_step_iff moved).mp run
      have full : Progress.Evaluates (step parameters)
          (appendFrames (startPattern s env pattern value) [.clause env code rest value])
          ⟨t, clauseResult answer⟩ steps := by
        simpa [appendFrames, startPattern] using plugged
      obtain ⟨patternAnswer, control, n, m, patternRun, boundary, residual, _⟩ :=
        evaluates_split full (clause_boundary answer)
      rcases patternAnswer with ⟨afterPattern, result⟩
      cases result with
      | value result => exact False.elim (Return.pattern_result patternRun)
      | matched bindings =>
          simp only [boundaryControl, Option.some.injEq] at boundary
          subst control
          have selected : step parameters
              ⟨afterPattern, .matched bindings, [.clause env code rest value]⟩ =
              .inr (start afterPattern (Env.extend env bindings) code) := rfl
          obtain ⟨bodySteps, bodyRun⟩ := (after_step_iff selected).mp ⟨m, residual⟩
          cases answer with
          | ok result =>
              cases result with
              | none => exact False.elim (Return.expression_result bodyRun)
              | some result =>
                  have selectedClause : Source.ClauseMatch (evaluation parameters)
                      (matching parameters) Env.extend s env value (pattern, code)
                      (.ok (some result)) t :=
                    .success (result := .ok result) ⟨n, patternRun⟩ ⟨bodySteps, bodyRun⟩
                  exact .success selectedClause
          | error packet =>
              have selectedClause : Source.ClauseMatch (evaluation parameters)
                  (matching parameters) Env.extend s env value (pattern, code)
                  (.error packet) t :=
                .success (result := .error packet) ⟨n, patternRun⟩ ⟨bodySteps, bodyRun⟩
              exact .raised selectedClause
      | mismatch =>
          simp only [boundaryControl, Option.some.injEq] at boundary
          subst control
          have failed : step parameters
              ⟨afterPattern, .mismatch, [.clause env code rest value]⟩ =
              .inr ⟨afterPattern, .clauses env rest value, []⟩ := rfl
          have tail := (after_step_iff failed).mp ⟨m, residual⟩
          exact .failure (.failure ⟨n, patternRun⟩) (ih tail)
      | raised packet =>
          simp only [boundaryControl, Option.some.injEq] at boundary
          subst control
          have unwind : Progress.Evaluates (step parameters)
              ⟨afterPattern, .raised packet, [.clause env code rest value]⟩
              ⟨afterPattern, clauseResult (.error packet)⟩ 2 := .next rfl (.done rfl)
          have same := (unwind.unique residual).1
          have stateEq : afterPattern = t := congrArg Answer.memory same
          have resultEq : clauseResult (.error packet) = clauseResult answer :=
            congrArg Answer.result same
          have answerEq := clauseResult_injective (Primitive := Primitive) resultEq
          subst t
          subst answer
          exact .raised (.raised ⟨n, patternRun⟩)
      | stuck fault => cases boundary

theorem alternatives_iff {parameters : Parameters Primitive}
    {s : Memory Primitive} {env : Env Primitive} {value : Value Primitive}
    {alternatives : List (Pattern × Expr Primitive)}
    {answer : Except (Value Primitive) (Option (Value Primitive))} {t : Memory Primitive} :
    Source.Alternatives
        (Source.ClauseMatch (evaluation parameters) (matching parameters) Env.extend)
        s env value alternatives answer t ↔
      Clauses parameters s env value alternatives answer t :=
  ⟨alternatives_sound, alternatives_complete⟩

end Suspensions.Core.Correspondence
