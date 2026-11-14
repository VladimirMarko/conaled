import Applications.Suspensions.Store

/-!
# The suspension and effectful-matching rules

These are the Appendix A rule schemata, parameterized by the inherited core's
expression and pattern judgments. They are independent of the concrete
continuation machine. A realization must supply those judgments and establish
their connection to execution; these definitions do not assume that arbitrary
expressions terminate or that an exception restores memory.

`Except X (Option B)` distinguishes a successful binding environment, ordinary
pattern failure, and an exception. Every outcome retains the reached state.
-/
set_option warningAsError true

namespace Suspensions.Source

variable {Code Env Value Pattern Bindings Exception : Type}

abbrev Evaluation (Code Env Value Exception : Type) :=
  State Code Env Value → Env → Code → Except Exception Value → State Code Env Value → Prop

abbrev Matching (Code Env Value Pattern Bindings Exception : Type) :=
  State Code Env Value → Env → Pattern → Value →
    Except Exception (Option Bindings) → State Code Env Value → Prop

/-- The two displayed forcing rules and the inherited body-exception rule.
The normal-body rule installs the value before its last premise. -/
inductive SuspensionMatch
    (evaluate : Evaluation Code Env Value Exception)
    (matchPattern : Matching Code Env Value Pattern Bindings Exception) :
    State Code Env Value → Env → Nat → Pattern →
      Except Exception (Option Bindings) → State Code Env Value → Prop
  | cached {s caller address pattern value answer t} :
      s.memory address = some (.value value) →
      matchPattern s caller pattern value answer t →
      SuspensionMatch evaluate matchPattern s caller address pattern answer t
  | evaluated {s caller address pattern code captured value afterBody answer afterMatch} :
      s.memory address = some (.thunk code captured) →
      evaluate s captured code (.ok value) afterBody →
      matchPattern (memoize afterBody address value) caller pattern value answer afterMatch →
      SuspensionMatch evaluate matchPattern s caller address pattern answer afterMatch
  | raised {s caller address pattern code captured exception afterBody} :
      s.memory address = some (.thunk code captured) →
      evaluate s captured code (.error exception) afterBody →
      SuspensionMatch evaluate matchPattern s caller address pattern (.error exception) afterBody

theorem suspension_cached_iff
    {evaluate : Evaluation Code Env Value Exception}
    {matchPattern : Matching Code Env Value Pattern Bindings Exception}
    {s caller address pattern value answer t}
    (found : s.memory address = some (.value value)) :
    SuspensionMatch evaluate matchPattern s caller address pattern answer t ↔
      matchPattern s caller pattern value answer t := by
  constructor
  · intro run
    cases run with
    | cached lookup matched =>
      have same := lookup.symm.trans found
      cases same
      exact matched
    | evaluated lookup _ _ => simp [found] at lookup
    | raised lookup _ => simp [found] at lookup
  · exact SuspensionMatch.cached found

/-- The successful body's intermediate state is retained even when the inner
match fails or raises. The match may itself further change the cached cell. -/
theorem suspension_thunk_iff
    {evaluate : Evaluation Code Env Value Exception}
    {matchPattern : Matching Code Env Value Pattern Bindings Exception}
    {s caller address pattern code captured answer t}
    (found : s.memory address = some (.thunk code captured)) :
    SuspensionMatch evaluate matchPattern s caller address pattern answer t ↔
      (∃ value afterBody,
        evaluate s captured code (.ok value) afterBody ∧
        matchPattern (memoize afterBody address value) caller pattern value answer t) ∨
      (∃ exception, answer = .error exception ∧
        evaluate s captured code (.error exception) t) := by
  constructor
  · intro run
    cases run with
    | cached lookup _ => simp [found] at lookup
    | evaluated lookup body matched =>
      have same := lookup.symm.trans found
      cases same
      exact Or.inl ⟨_, _, body, matched⟩
    | raised lookup body =>
      have same := lookup.symm.trans found
      cases same
      exact Or.inr ⟨_, rfl, body⟩
  · rintro (⟨value, afterBody, body, matched⟩ | ⟨exception, rfl, body⟩)
    · exact .evaluated found body matched
    · exact .raised found body

/-- Determinism is inherited from the two core judgments, not postulated for
an arbitrary suspension body. It includes equality of reached states. -/
theorem suspension_deterministic
    {evaluate : Evaluation Code Env Value Exception}
    {matchPattern : Matching Code Env Value Pattern Bindings Exception}
    (evalUnique : ∀ {s env code a t b u}, evaluate s env code a t →
      evaluate s env code b u → a = b ∧ t = u)
    (matchUnique : ∀ {s env pattern value a t b u},
      matchPattern s env pattern value a t →
      matchPattern s env pattern value b u → a = b ∧ t = u)
    {s caller address pattern a t b u}
    (left : SuspensionMatch evaluate matchPattern s caller address pattern a t)
    (right : SuspensionMatch evaluate matchPattern s caller address pattern b u) :
    a = b ∧ t = u := by
  cases left with
  | cached found matched =>
    exact matchUnique matched ((suspension_cached_iff found).mp right)
  | evaluated found body matched =>
    rcases (suspension_thunk_iff found).mp right with
      ⟨value, afterBody, body', matched'⟩ | ⟨exception, _, body'⟩
    · obtain ⟨same, rfl⟩ := evalUnique body body'
      cases same
      exact matchUnique matched matched'
    · have same := (evalUnique body body').1
      cases same
  | raised found body =>
    rcases (suspension_thunk_iff found).mp right with
      ⟨value, afterBody, body', _⟩ | ⟨exception, rfl, body'⟩
    · have same := (evalUnique body body').1
      cases same
    · obtain ⟨same, states⟩ := evalUnique body body'
      cases same
      exact ⟨rfl, states⟩

/-- Appendix A's state-threaded replacement of reference-pattern Rule158. -/
inductive ReferenceMatch
    (matchPattern : Matching Code Env Value Pattern Bindings Exception) :
    State Code Env Value → Env → Nat → Pattern →
      Except Exception (Option Bindings) → State Code Env Value → Prop
  | read {s caller address pattern value answer t} :
      s.memory address = some (.value value) →
      matchPattern s caller pattern value answer t →
      ReferenceMatch matchPattern s caller address pattern answer t

theorem reference_match_iff
    {matchPattern : Matching Code Env Value Pattern Bindings Exception}
    {s caller address pattern value answer t}
    (found : s.memory address = some (.value value)) :
    ReferenceMatch matchPattern s caller address pattern answer t ↔
      matchPattern s caller pattern value answer t := by
  constructor
  · intro run
    cases run with
    | read lookup matched =>
      have same := lookup.symm.trans found
      cases same
      exact matched
  · exact ReferenceMatch.read found

/-- One source match rule: evaluate its body only after successful matching.
Failure and exceptions are separate, and neither discards the pattern's state. -/
inductive ClauseMatch
    (evaluate : Evaluation Code Env Value Exception)
    (matchPattern : Matching Code Env Value Pattern Bindings Exception)
    (extend : Env → Bindings → Env) :
    State Code Env Value → Env → Value → (Pattern × Code) →
      Except Exception (Option Value) → State Code Env Value → Prop
  | success {s env value pattern code bindings afterPattern result t} :
      matchPattern s env pattern value (.ok (some bindings)) afterPattern →
      evaluate afterPattern (extend env bindings) code result t →
      ClauseMatch evaluate matchPattern extend s env value (pattern, code)
        (result.map some) t
  | failure {s env value pattern code t} :
      matchPattern s env pattern value (.ok none) t →
      ClauseMatch evaluate matchPattern extend s env value (pattern, code) (.ok none) t
  | raised {s env value pattern code exception t} :
      matchPattern s env pattern value (.error exception) t →
      ClauseMatch evaluate matchPattern extend s env value (pattern, code) (.error exception) t

/-- Source Rules124–126 with the state convention made explicit. -/
inductive Alternatives
    (clause : State Code Env Value → Env → Value → (Pattern × Code) →
      Except Exception (Option Value) → State Code Env Value → Prop) :
    State Code Env Value → Env → Value → List (Pattern × Code) →
      Except Exception (Option Value) → State Code Env Value → Prop
  | empty {s env value} : Alternatives clause s env value [] (.ok none) s
  | success {s env value head rest result t} :
      clause s env value head (.ok (some result)) t →
      Alternatives clause s env value (head :: rest) (.ok (some result)) t
  | failure {s env value head rest afterFailure result t} :
      clause s env value head (.ok none) afterFailure →
      Alternatives clause afterFailure env value rest result t →
      Alternatives clause s env value (head :: rest) result t
  | raised {s env value head rest exception t} :
      clause s env value head (.error exception) t →
      Alternatives clause s env value (head :: rest) (.error exception) t

/-- A failed head really feeds its changed state into the remaining clauses. -/
theorem alternatives_after_failure
    {clause : State Code Env Value → Env → Value → (Pattern × Code) →
      Except Exception (Option Value) → State Code Env Value → Prop}
    {s env value head rest afterFailure result t}
    (headFailure : clause s env value head (.ok none) afterFailure)
    (tailResult : Alternatives clause afterFailure env value rest result t) :
    Alternatives clause s env value (head :: rest) result t :=
  .failure headFailure tailResult

end Suspensions.Source
