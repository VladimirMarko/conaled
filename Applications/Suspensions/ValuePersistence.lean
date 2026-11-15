import Applications.Suspensions.BodyEvent
import Applications.Suspensions.Invariant

/-!
# Value cells persist through raw execution

Once an address contains a value, actual bounded execution retains a value
cell there. Fresh allocation cannot replace an occupied address; recursive
closing preserves value cells; assignment and memoization write values.

The payload may change. In particular, an older pending memoize frame may
overwrite an inner successful result, and reference assignment remains
effectful. This law gives neither payload equality nor a single-write bound.
It applies only after a value exists: a body that raises without a successful
write remains a thunk and can be entered again.

One-step preservation needs bounded input memory. Finite runs and observations
reuse the existing configuration invariant so that all later inputs remain
bounded. Fresh starts discharge its frame premise with an empty stack. No
purity, typing, termination or nonreentrancy assumption is introduced.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Suspensions.Core.Machine
variable {Primitive : Type}

def HasValue (memory : Memory Primitive) (address : Nat) : Prop :=
  ∃ value, memory.memory address = some (.value value)

def OutcomeHasValue (address : Nat) : Answer Primitive ⊕ Config Primitive → Prop
  | .inl answer => HasValue answer.memory address
  | .inr config => HasValue config.memory address

theorem HasValue.allocate {memory : Memory Primitive} {address : Nat}
    (present : HasValue memory address) (bounded : Suspensions.Bounded memory)
    (cell : Cell (Expr Primitive) (Env Primitive) (Value Primitive)) :
    HasValue (Suspensions.allocate memory cell).1 address := by
  obtain ⟨value, found⟩ := present
  exact ⟨value, Suspensions.allocate_retains bounded found cell⟩

theorem HasValue.memoize {memory : Memory Primitive} {address : Nat}
    (present : HasValue memory address) (written : Nat) (value : Value Primitive) :
    HasValue (Suspensions.memoize memory written value) address := by
  by_cases same : address = written
  · subst address
    exact ⟨value, Suspensions.memoize_lookup memory written value⟩
  · obtain ⟨old, found⟩ := present
    exact ⟨old, (Suspensions.memoize_other memory written value same).trans found⟩

theorem HasValue.srec {memory : Memory Primitive} {address : Nat}
    (present : HasValue memory address) (targets : Finset Nat) (extend : Env Primitive → Env Primitive) :
    HasValue (Suspensions.srec memory targets extend) address := by
  obtain ⟨value, found⟩ := present
  exact ⟨value, Suspensions.srec_value targets extend found⟩

private theorem eval_hasValue (parameters : Parameters Primitive) (memory : Memory Primitive)
    (environment : Env Primitive) (expression : Expr Primitive) (stack : List (Frame Primitive))
    {address : Nat} (bounded : Suspensions.Bounded memory) (present : HasValue memory address) :
    OutcomeHasValue address (step parameters ⟨memory, .eval environment expression, stack⟩) := by
  cases expression <;> simp only [step, transition, proceed, finish, OutcomeHasValue]
  all_goals
    repeat' first
      | (fail_if_no_progress subst_vars)
      | (fail_if_no_progress simp_all)
      | exact present
      | exact present.allocate bounded _
      | split at *

private theorem value_hasValue (parameters : Parameters Primitive) (memory : Memory Primitive)
    (value : Value Primitive) (stack : List (Frame Primitive)) {address : Nat}
    (bounded : Suspensions.Bounded memory) (present : HasValue memory address) :
    OutcomeHasValue address (step parameters ⟨memory, .value value, stack⟩) := by
  cases stack with
  | nil => exact present
  | cons frame rest =>
      cases frame <;> simp only [step, transition, proceed, finish, OutcomeHasValue]
      all_goals
        repeat' first
          | (fail_if_no_progress subst_vars)
          | (fail_if_no_progress simp_all)
          | exact present.allocate bounded _
          | exact present.memoize _ _
          | split at *

private theorem raised_hasValue (parameters : Parameters Primitive) (memory : Memory Primitive)
    (packet : Value Primitive) (stack : List (Frame Primitive)) {address : Nat}
    (present : HasValue memory address) :
    OutcomeHasValue address (step parameters ⟨memory, .raised packet, stack⟩) := by
  cases stack with
  | nil => exact present
  | cons frame rest => cases frame <;> exact present

private theorem pattern_hasValue (parameters : Parameters Primitive) (memory : Memory Primitive)
    (environment : Env Primitive) (pattern : Pattern) (value : Value Primitive)
    (stack : List (Frame Primitive)) {address : Nat} (present : HasValue memory address) :
    OutcomeHasValue address (step parameters ⟨memory, .pattern environment pattern value, stack⟩) := by
  cases pattern <;> simp only [step, transition, proceed, finish, OutcomeHasValue]
  all_goals repeat' first | (fail_if_no_progress subst_vars) | (fail_if_no_progress simp_all) | split at *

private theorem matched_hasValue (parameters : Parameters Primitive) (memory : Memory Primitive)
    (bindings : Env Primitive) (stack : List (Frame Primitive)) {address : Nat}
    (present : HasValue memory address) :
    OutcomeHasValue address (step parameters ⟨memory, .matched bindings, stack⟩) := by
  cases stack with
  | nil => exact present
  | cons frame rest => cases frame <;> exact present

private theorem mismatch_hasValue (parameters : Parameters Primitive) (memory : Memory Primitive)
    (stack : List (Frame Primitive)) {address : Nat} (present : HasValue memory address) :
    OutcomeHasValue address (step parameters ⟨memory, .mismatch, stack⟩) := by
  cases stack with
  | nil => exact present
  | cons frame rest => cases frame <;> exact present

private theorem clauses_hasValue (parameters : Parameters Primitive) (memory : Memory Primitive)
    (environment : Env Primitive) (clauses : List (Pattern × Expr Primitive)) (value : Value Primitive)
    (stack : List (Frame Primitive)) {address : Nat} (present : HasValue memory address) :
    OutcomeHasValue address (step parameters ⟨memory, .clauses environment clauses value, stack⟩) := by
  cases clauses with
  | nil => exact present
  | cons clause rest => cases clause; exact present

private theorem rows_hasValue (parameters : Parameters Primitive) (memory : Memory Primitive)
    (environment : Env Primitive) (patterns : List (Nat × Pattern)) (fields bindings : Env Primitive)
    (stack : List (Frame Primitive)) {address : Nat} (present : HasValue memory address) :
    OutcomeHasValue address (step parameters ⟨memory, .rows environment patterns fields bindings, stack⟩) := by
  cases patterns with
  | nil => exact present
  | cons row rest =>
      rcases row with ⟨label, pattern⟩
      simp only [step, transition, proceed, finish, OutcomeHasValue]
      repeat' first | (fail_if_no_progress subst_vars) | (fail_if_no_progress simp_all) | split at *

private theorem recursive_hasValue (parameters : Parameters Primitive) (memory : Memory Primitive)
    (environment : Env Primitive) (bindings : List (Nat × Expr Primitive)) (created : Env Primitive)
    (body : Expr Primitive) (stack : List (Frame Primitive)) {address : Nat}
    (present : HasValue memory address) :
    OutcomeHasValue address (step parameters ⟨memory, .recursive environment bindings created body, stack⟩) := by
  cases bindings with
  | nil => exact present.srec _ _
  | cons binding rest =>
      rcases binding with ⟨name, expression⟩
      simp only [step, transition, proceed, finish, OutcomeHasValue]
      repeat' first | (fail_if_no_progress subst_vars) | (fail_if_no_progress simp_all) | split at *

/-- Every actual transition preserves the value-cell constructor. The
bounded-memory premise is used only for the freshness of new allocation. -/
theorem step_hasValue {parameters : Parameters Primitive} {config : Config Primitive} {address : Nat}
    (bounded : Suspensions.Bounded config.memory) (present : HasValue config.memory address) :
    OutcomeHasValue address (step parameters config) := by
  rcases config with ⟨memory, control, stack⟩
  cases control with
  | eval environment expression => exact eval_hasValue parameters memory environment expression stack bounded present
  | value value => exact value_hasValue parameters memory value stack bounded present
  | raised packet => exact raised_hasValue parameters memory packet stack present
  | pattern environment pattern value => exact pattern_hasValue parameters memory environment pattern value stack present
  | matched bindings => exact matched_hasValue parameters memory bindings stack present
  | mismatch => exact mismatch_hasValue parameters memory stack present
  | clauses environment clauses value => exact clauses_hasValue parameters memory environment clauses value stack present
  | rows environment patterns fields bindings =>
      exact rows_hasValue parameters memory environment patterns fields bindings stack present
  | recursive environment bindings created body =>
      exact recursive_hasValue parameters memory environment bindings created body stack present

/-- The finite run may return a source exception or fault. No equality with
the original payload is concluded. -/
theorem evaluates_hasValue {parameters : Parameters Primitive} {config : Config Primitive}
    {answer : Answer Primitive} {steps address : Nat} (valid : ConfigBounded config)
    (present : HasValue config.memory address)
    (evaluation : Progress.Evaluates (step parameters) config answer steps) :
    HasValue answer.memory address := by
  revert valid present
  induction evaluation with
  | done finished =>
      intro valid present
      have kept := step_hasValue (parameters := parameters) valid.1 present
      rw [finished] at kept
      exact kept
  | next moved _ ih =>
      intro valid present
      have bounded := step_bounded (parameters := parameters) valid
      have kept := step_hasValue (parameters := parameters) valid.1 present
      rw [moved] at bounded kept
      exact ih bounded kept

theorem start_evaluates_hasValue {parameters : Parameters Primitive} {memory : Memory Primitive}
    {environment : Env Primitive} {expression : Expr Primitive} {answer : Answer Primitive}
    {steps address : Nat} (bounded : Suspensions.Bounded memory) (present : HasValue memory address)
    (evaluation : Progress.Evaluates (step parameters) (start memory environment expression) answer steps) :
    HasValue answer.memory address :=
  evaluates_hasValue (start_bounded bounded environment expression) present evaluation

theorem startPattern_evaluates_hasValue {parameters : Parameters Primitive} {memory : Memory Primitive}
    {environment : Env Primitive} {pattern : Pattern} {value : Value Primitive}
    {answer : Answer Primitive} {steps address : Nat} (bounded : Suspensions.Bounded memory)
    (present : HasValue memory address)
    (evaluation : Progress.Evaluates (step parameters)
      (startPattern memory environment pattern value) answer steps) : HasValue answer.memory address :=
  evaluates_hasValue (startPattern_bounded bounded environment pattern value) present evaluation

/-- Bounded observation retains the value cell both at unfinished states and
at delivered answers. Absorbing observations add no transition-count claim. -/
theorem observe_hasValue {parameters : Parameters Primitive} {config : Config Primitive} {address : Nat}
    (valid : ConfigBounded config) (present : HasValue config.memory address) (budget : Nat) :
    OutcomeHasValue address (Prefix.observe parameters budget config) := by
  have iterates : ∀ n (state : Answer Primitive ⊕ Config Primitive), OutcomeBounded state →
      OutcomeHasValue address state → OutcomeHasValue address ((Prefix.advance parameters)^[n] state) := by
    intro n
    induction n with
    | zero => intro state _ kept; exact kept
    | succ n ih =>
        intro state bounded kept
        rw [Function.iterate_succ_apply]
        cases state with
        | inl answer => exact ih (.inl answer) bounded kept
        | inr next =>
            exact ih _ (step_bounded (parameters := parameters) bounded)
              (step_hasValue (parameters := parameters) bounded.1 kept)
  exact iterates budget (.inr config) valid present

theorem observe_unfinished_hasValue {parameters : Parameters Primitive} {config next : Config Primitive}
    {budget address : Nat} (valid : ConfigBounded config) (present : HasValue config.memory address)
    (observed : Prefix.observe parameters budget config = .inr next) : HasValue next.memory address := by
  have kept := observe_hasValue (parameters := parameters) valid present budget
  rw [observed] at kept
  exact kept

theorem observe_finished_hasValue {parameters : Parameters Primitive} {config : Config Primitive}
    {answer : Answer Primitive} {budget address : Nat} (valid : ConfigBounded config)
    (present : HasValue config.memory address)
    (observed : Prefix.observe parameters budget config = .inl answer) : HasValue answer.memory address := by
  have kept := observe_hasValue (parameters := parameters) valid present budget
  rw [observed] at kept
  exact kept

theorem start_observe_hasValue {parameters : Parameters Primitive} {memory : Memory Primitive}
    (bounded : Suspensions.Bounded memory) {address : Nat} (present : HasValue memory address)
    (environment : Env Primitive) (expression : Expr Primitive) (budget : Nat) :
    OutcomeHasValue address (Prefix.observe parameters budget (start memory environment expression)) :=
  observe_hasValue (start_bounded bounded environment expression) present budget

/-- The unrestricted body-event characterization rules out entry at an
address that currently contains any value, regardless of its payload. -/
theorem hasValue_no_body {parameters : Parameters Primitive} {config : Config Primitive} {address : Nat}
    (present : HasValue config.memory address) : (transition parameters config).2 ≠ .body address := by
  intro event
  obtain ⟨_, _, _, _, _, thunk⟩ := (body_event_iff parameters config address).mp event
  obtain ⟨value, found⟩ := present
  rw [found] at thunk
  cases thunk

/-- A suspended-address match uses the current cached payload. The theorem
does not equate it with an earlier payload at the same address. -/
theorem hasValue_hit (parameters : Parameters Primitive) {memory : Memory Primitive} {address : Nat}
    (present : HasValue memory address) (caller : Env Primitive) (inner : Pattern)
    (stack : List (Frame Primitive)) :
    ∃ value, memory.memory address = some (.value value) ∧
      transition parameters ⟨memory, .pattern caller (.suspended inner) (.address address), stack⟩ =
        proceed memory (.pattern caller inner value) stack (.hit address) := by
  obtain ⟨value, found⟩ := present
  exact ⟨value, found, hit_transition parameters memory caller inner address value stack found⟩

/-- At every later live observation, this same physical address cannot be
entered as a body, even if other cells still contain thunks. -/
theorem observe_no_body {parameters : Parameters Primitive} {config next : Config Primitive}
    {budget address : Nat} (valid : ConfigBounded config) (present : HasValue config.memory address)
    (observed : Prefix.observe parameters budget config = .inr next) :
    (transition parameters next).2 ≠ .body address :=
  hasValue_no_body (observe_unfinished_hasValue valid present observed)

/-- A later suspended match at the retained address takes the actual hit
transition, with the payload found at that later state. -/
theorem observe_force_hit {parameters : Parameters Primitive} {config next : Config Primitive}
    {budget address : Nat} {caller : Env Primitive} {inner : Pattern}
    (valid : ConfigBounded config) (present : HasValue config.memory address)
    (observed : Prefix.observe parameters budget config = .inr next)
    (matching : next.control = .pattern caller (.suspended inner) (.address address)) :
    ∃ value, next.memory.memory address = some (.value value) ∧
      transition parameters next =
        proceed next.memory (.pattern caller inner value) next.stack (.hit address) := by
  have kept := observe_unfinished_hasValue valid present observed
  rcases next with ⟨memory, control, stack⟩
  cases matching
  exact hasValue_hit parameters kept caller inner stack

end Suspensions.Core.Machine
