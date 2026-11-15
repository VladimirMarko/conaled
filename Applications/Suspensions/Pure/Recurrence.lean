import Applications.Suspensions.Pure.Continuation
import Mathlib.Logic.Function.Iterate

/-!
# A recurrence obstruction to finite pure evaluation

`Reaches` is a finite observation of the existing machine, using a thin
finished-absorbing iterator. It is not another evaluation judgment. Ending at
an unfinished configuration means that all transitions in that prefix occurred.

A positive prefix that returns to its initial configuration with caller frames
appended precludes every finite result. Otherwise the residual caller run would
contain an isolated completion of the same input with a strictly smaller count,
contradicting `Progress.Evaluates.unique`. This covers normal results, source
exceptions, matching results and faults alike.

The conclusion concerns this unshared interpretation. Applying it to raw heap
body reentry still requires the separate interpretation and containment bridge.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Suspensions.Pure.Recurrence
open Machine
variable {Primitive : Type}

def advance (parameters : Parameters Primitive) :
    Result Primitive ⊕ Config Primitive → Result Primitive ⊕ Config Primitive
  | .inl answer => .inl answer
  | .inr config => step parameters config

def Reaches (parameters : Parameters Primitive) (steps : Nat)
    (config next : Config Primitive) : Prop :=
  (advance parameters)^[steps] (.inr config) = .inr next

@[simp] theorem iterate_answer (parameters : Parameters Primitive) (steps : Nat)
    (answer : Result Primitive) :
    (advance parameters)^[steps] (.inl answer) = .inl answer := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      rw [Function.iterate_succ_apply]
      exact ih

theorem reaches_zero_iff (parameters : Parameters Primitive) (config next : Config Primitive) :
    Reaches parameters 0 config next ↔ config = next := by
  simp [Reaches]

theorem reaches_succ_iff (parameters : Parameters Primitive) (steps : Nat)
    (config last : Config Primitive) :
    Reaches parameters (steps + 1) config last ↔
      ∃ next, step parameters config = .inr next ∧ Reaches parameters steps next last := by
  unfold Reaches
  rw [Function.iterate_succ_apply]
  change (advance parameters)^[steps] (step parameters config) = .inr last ↔
    ∃ next, step parameters config = .inr next ∧
      (advance parameters)^[steps] (.inr next) = .inr last
  cases first : step parameters config <;> simp

theorem Reaches.one {parameters : Parameters Primitive} {config next : Config Primitive}
    (moved : step parameters config = .inr next) : Reaches parameters 1 config next := moved

theorem Reaches.trans {parameters : Parameters Primitive} {n m : Nat}
    {config middle last : Config Primitive} (first : Reaches parameters n config middle)
    (second : Reaches parameters m middle last) : Reaches parameters (n + m) config last := by
  unfold Reaches at first second ⊢
  rw [Nat.add_comm n m, Function.iterate_add_apply, first, second]

theorem Reaches.evaluates {parameters : Parameters Primitive} {steps : Nat}
    {config next : Config Primitive} (reached : Reaches parameters steps config next)
    {answer : Result Primitive} {n : Nat}
    (residual : Progress.Evaluates (step parameters) next answer n) :
    Progress.Evaluates (step parameters) config answer (steps + n) := by
  induction steps generalizing config with
  | zero =>
      have same := (reaches_zero_iff parameters config next).mp reached
      subst config
      simpa only [Nat.zero_add] using residual
  | succ steps ih =>
      obtain ⟨first, moved, remaining⟩ := (reaches_succ_iff parameters steps config next).mp reached
      have composed := Progress.Evaluates.next moved (ih remaining)
      have count : (steps + n) + 1 = (steps + 1) + n := by omega
      simpa only [count] using composed

/-- Splitting at a known unfinished prefix retains the actual remaining count. -/
theorem Reaches.remaining {parameters : Parameters Primitive} {steps : Nat}
    {config next : Config Primitive} (reached : Reaches parameters steps config next)
    {answer : Result Primitive} {n : Nat}
    (whole : Progress.Evaluates (step parameters) config answer n) :
    ∃ m, Progress.Evaluates (step parameters) next answer m ∧ n = steps + m := by
  induction steps generalizing config n with
  | zero =>
      have same := (reaches_zero_iff parameters config next).mp reached
      subst config
      exact ⟨n, whole, by simp⟩
  | succ steps ih =>
      obtain ⟨first, moved, remaining⟩ := (reaches_succ_iff parameters steps config next).mp reached
      cases whole with
      | done finished => simp [moved] at finished
      | @next _ actual _ count actualMoved rest =>
          have same : first = actual := Sum.inr.inj (moved.symm.trans actualMoved)
          subst actual
          obtain ⟨m, residual, equation⟩ := ih remaining rest
          exact ⟨m, residual, by omega⟩

theorem Reaches.append {parameters : Parameters Primitive} {steps : Nat}
    {config next : Config Primitive} (reached : Reaches parameters steps config next)
    (tail : List (Frame Primitive)) :
    Reaches parameters steps (appendFrames config tail) (appendFrames next tail) := by
  induction steps generalizing config with
  | zero =>
      have same := (reaches_zero_iff parameters config next).mp reached
      subst config
      rfl
  | succ steps ih =>
      obtain ⟨first, moved, remaining⟩ := (reaches_succ_iff parameters steps config next).mp reached
      apply (reaches_succ_iff parameters steps _ _).mpr
      exact ⟨appendFrames first tail, step_append moved tail, ih remaining⟩

/-- A finite nonfault evaluation reaches its delivery control after exactly
one fewer transition. This is an actual unfinished prefix, not padded fuel. -/
theorem evaluates_boundary_reaches {parameters : Parameters Primitive}
    {config : Config Primitive} {answer : Result Primitive} {control : Control Primitive} {n : Nat}
    (evaluation : Progress.Evaluates (step parameters) config answer n)
    (boundary : boundaryControl answer = some control) :
    Reaches parameters (n - 1) config ⟨control, []⟩ := by
  induction evaluation with
  | done finished =>
      rw [step_boundary finished boundary]
      rfl
  | @next input next output steps moved evaluation ih =>
      have reached := (Reaches.one moved).trans (ih boundary)
      have positive := evaluates_positive evaluation
      have count : 1 + (steps - 1) = (steps + 1) - 1 := by omega
      simpa only [count] using reached

/-- Replaying a normal body certificate reaches the caller's inner pattern in
n+1 transitions: entry, all but isolated delivery, then return-to-pattern.
The inner pattern has not run. Caller frames are arbitrary and unchanged.
This is the pure replay used for a justified raw cache hit; it asserts no heap
relation or constant-cost force operation on its own. -/
theorem force_prefix_of_certificate {parameters : Parameters Primitive}
    {body : Core.Expr Primitive} {captured : Env Primitive}
    {recursive : Option (Suspensions.Pure.Group Primitive)} {value : Value Primitive} {n : Nat}
    (evaluation : Progress.Evaluates (step parameters)
      (start (bodyEnvironment captured recursive) body) (.value value) n)
    (environment : Env Primitive) (inner : Core.Pattern) (tail : List (Frame Primitive)) :
    Reaches parameters (n + 1)
      (appendFrames (startPattern environment (.suspended inner)
        (.suspension body captured recursive)) tail)
      (appendFrames (startPattern environment inner value) tail) := by
  have entered : Reaches parameters 1
      (startPattern environment (.suspended inner) (.suspension body captured recursive))
      (appendFrames (start (bodyEnvironment captured recursive) body) [.force environment inner]) :=
    Reaches.one (congrArg Prod.fst
      (body_transition parameters environment captured recursive inner body []))
  have evaluated := (evaluates_boundary_reaches evaluation rfl).append [.force environment inner]
  have returned : Reaches parameters 1
      (appendFrames ⟨.value value, []⟩ [.force environment inner])
      (startPattern environment inner value) :=
    Reaches.one (congrArg Prod.fst (body_return parameters environment inner value []))
  have replayed := (entered.trans (evaluated.trans returned)).append tail
  have positive := evaluates_positive evaluation
  have count : 1 + ((n - 1) + 1) = n + 1 := by omega
  simpa only [count] using replayed

theorem Reaches.not_terminates {parameters : Parameters Primitive} {steps : Nat}
    {config next : Config Primitive} (reached : Reaches parameters steps config next)
    (unfinished : ¬ Progress.Terminates (step parameters) next) :
    ¬ Progress.Terminates (step parameters) config := by
  rintro ⟨answer, n, whole⟩
  obtain ⟨m, residual, _⟩ := reached.remaining whole
  exact unfinished ⟨answer, m, residual⟩

/-- A concrete positive recurrence is an obstruction, not a nonreentrancy
assumption. Any hypothesized finite result yields a smaller completion of the
identical isolated input, including when either completion is a fault. -/
theorem recurring_prefix_not_terminates {parameters : Parameters Primitive}
    {config : Config Primitive} {tail : List (Frame Primitive)} {steps : Nat}
    (positive : 0 < steps)
    (repeated : Reaches parameters steps config (appendFrames config tail)) :
    ¬ Progress.Terminates (step parameters) config := by
  rintro ⟨answer, n, whole⟩
  obtain ⟨m, residual, count⟩ := repeated.remaining whole
  obtain ⟨bodyAnswer, bodyCount, body, bound⟩ := evaluates_isolated_le residual
  have sameCount := (whole.unique body).2
  omega

/-- Universal search failure follows from the finite-evaluation theorem. One
failed bounded search, by itself, is never used to infer this conclusion. -/
theorem search_none_of_not_terminates {parameters : Parameters Primitive}
    {config : Config Primitive} (unfinished : ¬ Progress.Terminates (step parameters) config)
    (fuel : Nat) : Progress.search (step parameters) fuel config = none := by
  cases found : Progress.search (step parameters) fuel config with
  | none => rfl
  | some result =>
      exact False.elim (unfinished ⟨result.1, result.2, Progress.search_sound found⟩)

end Suspensions.Pure.Recurrence
