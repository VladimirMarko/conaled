import Applications.Suspensions.Prefix
import Mathlib.Tactic.FailIfNoProgress

/-!
# Finite memory throughout suspension execution

Bounded initial memory remains bounded through the actual machine transitions.
A pending memoize frame additionally needs its write address below the current
frontier. Fresh starts have no such frames; every frame the machine pushes is
justified by an actual occupied thunk lookup. Allocation can only increase the
frontier. Repeated frames for one address and cycles in captured environments
are both allowed.

The invariant is lifted to complete finite evaluations and to the existing
bounded prefix observer. An unfinished observation retains its reached memory
and valid pending frames. No termination or source type-safety premise occurs.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Suspensions.Core.Machine
variable {Primitive : Type}

/-- Only pending cache-write addresses are constrained. The equality form
keeps arbitrary frame-list tails opaque during transition proofs. -/
def FrameBounded (frontier : Nat) (frame : Frame Primitive) : Prop :=
  ∀ address environment inner,
    frame = .memoize address environment inner → address < frontier

def ConfigBounded (config : Config Primitive) : Prop :=
  Suspensions.Bounded config.memory ∧
    List.Forall (FrameBounded config.memory.next) config.stack

def OutcomeBounded : Answer Primitive ⊕ Config Primitive → Prop
  | .inl answer => Suspensions.Bounded answer.memory
  | .inr config => ConfigBounded config

theorem frameBounded_mono {first second : Nat} {frame : Frame Primitive}
    (growth : first ≤ second) (valid : FrameBounded first frame) :
    FrameBounded second frame :=
  fun address environment inner equal =>
    Nat.lt_of_lt_of_le (valid address environment inner equal) growth

private theorem frames_mono {first second : Nat} {stack : List (Frame Primitive)}
    (growth : first ≤ second) (valid : List.Forall (FrameBounded first) stack) :
    List.Forall (FrameBounded second) stack :=
  List.Forall.imp (fun _ h => frameBounded_mono growth h) valid

theorem start_bounded {memory : Memory Primitive} (bounded : Suspensions.Bounded memory)
    (environment : Env Primitive) (expression : Expr Primitive) :
    ConfigBounded (start memory environment expression) := ⟨bounded, trivial⟩

theorem startPattern_bounded {memory : Memory Primitive} (bounded : Suspensions.Bounded memory)
    (environment : Env Primitive) (pattern : Pattern) (value : Value Primitive) :
    ConfigBounded (startPattern memory environment pattern value) := ⟨bounded, trivial⟩

private theorem memoize_bounded_of_lt {memory : Memory Primitive}
    (bounded : Suspensions.Bounded memory) {address : Nat}
    (inside : address < memory.next) (value : Value Primitive) :
    Suspensions.Bounded (Suspensions.memoize memory address value) :=
  Suspensions.replace_bounded bounded inside (.value value)

private theorem eval_bounded (parameters : Parameters Primitive) (memory : Memory Primitive)
    (environment : Env Primitive) (expression : Expr Primitive) (stack : List (Frame Primitive))
    (bounded : Suspensions.Bounded memory)
    (frames : List.Forall (FrameBounded memory.next) stack) :
    OutcomeBounded (step parameters ⟨memory, .eval environment expression, stack⟩) := by
  have larger := frames_mono (Nat.le_succ memory.next) frames
  cases expression <;>
    simp only [step, transition, proceed, finish, OutcomeBounded, ConfigBounded,
      FrameBounded, List.forall_cons] at *
  all_goals
    repeat' first
      | (fail_if_no_progress subst_vars)
      | (fail_if_no_progress simp_all)
      | exact bounded
      | exact Suspensions.delay_bounded bounded _ _
      | apply And.intro
      | split at *

private theorem value_bounded (parameters : Parameters Primitive) (memory : Memory Primitive)
    (value : Value Primitive) (stack : List (Frame Primitive))
    (bounded : Suspensions.Bounded memory)
    (frames : List.Forall (FrameBounded memory.next) stack) :
    OutcomeBounded (step parameters ⟨memory, .value value, stack⟩) := by
  have larger := frames_mono (Nat.le_succ memory.next) frames
  cases stack with
  | nil => exact bounded
  | cons frame rest =>
      cases frame <;>
        simp only [step, transition, proceed, finish, OutcomeBounded, ConfigBounded,
          FrameBounded, List.forall_cons] at *
      all_goals
        repeat' first
          | (fail_if_no_progress subst_vars)
          | (fail_if_no_progress simp_all)
          | exact bounded
          | exact Suspensions.allocate_bounded bounded _
          | exact Suspensions.memoize_bounded bounded (by assumption) _
          | exact memoize_bounded_of_lt bounded (by assumption) _
          | apply And.intro
          | split at *

private theorem raised_bounded (parameters : Parameters Primitive) (memory : Memory Primitive)
    (packet : Value Primitive) (stack : List (Frame Primitive))
    (bounded : Suspensions.Bounded memory)
    (frames : List.Forall (FrameBounded memory.next) stack) :
    OutcomeBounded (step parameters ⟨memory, .raised packet, stack⟩) := by
  cases stack with
  | nil => exact bounded
  | cons frame rest =>
      cases frame <;>
        simp_all [step, transition, proceed, OutcomeBounded, ConfigBounded, FrameBounded]

private theorem pattern_bounded (parameters : Parameters Primitive) (memory : Memory Primitive)
    (environment : Env Primitive) (pattern : Pattern) (value : Value Primitive)
    (stack : List (Frame Primitive)) (bounded : Suspensions.Bounded memory)
    (frames : List.Forall (FrameBounded memory.next) stack) :
    OutcomeBounded (step parameters ⟨memory, .pattern environment pattern value, stack⟩) := by
  cases pattern <;>
    simp only [step, transition, proceed, finish, OutcomeBounded, ConfigBounded,
      FrameBounded, List.forall_cons] at *
  all_goals
    repeat' first
      | (fail_if_no_progress subst_vars)
      | (fail_if_no_progress simp_all)
      | exact bounded.occupied_lt (by assumption)
      | apply And.intro
      | split at *

private theorem matched_bounded (parameters : Parameters Primitive) (memory : Memory Primitive)
    (bindings : Env Primitive) (stack : List (Frame Primitive))
    (bounded : Suspensions.Bounded memory)
    (frames : List.Forall (FrameBounded memory.next) stack) :
    OutcomeBounded (step parameters ⟨memory, .matched bindings, stack⟩) := by
  cases stack with
  | nil => exact bounded
  | cons frame rest =>
      cases frame <;>
        simp_all [step, transition, proceed, finish, OutcomeBounded, ConfigBounded, FrameBounded]

private theorem mismatch_bounded (parameters : Parameters Primitive) (memory : Memory Primitive)
    (stack : List (Frame Primitive)) (bounded : Suspensions.Bounded memory)
    (frames : List.Forall (FrameBounded memory.next) stack) :
    OutcomeBounded (step parameters ⟨memory, .mismatch, stack⟩) := by
  cases stack with
  | nil => exact bounded
  | cons frame rest =>
      cases frame <;>
        simp_all [step, transition, proceed, finish, OutcomeBounded, ConfigBounded, FrameBounded]

private theorem clauses_bounded (parameters : Parameters Primitive) (memory : Memory Primitive)
    (environment : Env Primitive) (clauses : List (Pattern × Expr Primitive))
    (value : Value Primitive) (stack : List (Frame Primitive))
    (bounded : Suspensions.Bounded memory)
    (frames : List.Forall (FrameBounded memory.next) stack) :
    OutcomeBounded (step parameters ⟨memory, .clauses environment clauses value, stack⟩) := by
  cases clauses with
  | nil => exact ⟨bounded, frames⟩
  | cons clause rest =>
      rcases clause with ⟨pattern, body⟩
      simp_all [step, transition, proceed, OutcomeBounded, ConfigBounded, FrameBounded]

private theorem rows_bounded (parameters : Parameters Primitive) (memory : Memory Primitive)
    (environment : Env Primitive) (patterns : List (Nat × Pattern))
    (fields : List (Nat × Value Primitive)) (bindings : Env Primitive)
    (stack : List (Frame Primitive)) (bounded : Suspensions.Bounded memory)
    (frames : List.Forall (FrameBounded memory.next) stack) :
    OutcomeBounded (step parameters ⟨memory, .rows environment patterns fields bindings, stack⟩) := by
  cases patterns with
  | nil => exact ⟨bounded, frames⟩
  | cons row rest =>
      rcases row with ⟨label, pattern⟩
      simp only [step, transition, proceed, finish, OutcomeBounded, ConfigBounded,
        FrameBounded, List.forall_cons] at *
      repeat' first
        | (fail_if_no_progress subst_vars)
        | (fail_if_no_progress simp_all)
        | apply And.intro
        | split at *

private theorem recursive_bounded (parameters : Parameters Primitive) (memory : Memory Primitive)
    (environment : Env Primitive) (bindings : List (Nat × Expr Primitive))
    (created : Env Primitive) (body : Expr Primitive) (stack : List (Frame Primitive))
    (bounded : Suspensions.Bounded memory)
    (frames : List.Forall (FrameBounded memory.next) stack) :
    OutcomeBounded (step parameters ⟨memory, .recursive environment bindings created body, stack⟩) := by
  cases bindings with
  | nil => exact ⟨Suspensions.srec_bounded bounded _ _, frames⟩
  | cons binding rest =>
      rcases binding with ⟨name, expression⟩
      cases accepted : recursiveRhs expression <;>
        simp_all [step, transition, proceed, finish, OutcomeBounded, ConfigBounded, FrameBounded]

/-- Every actual step preserves finite memory and all pending write bounds.
The final branch covers normal, exceptional, match and stuck answers alike. -/
theorem step_bounded {parameters : Parameters Primitive} {config : Config Primitive}
    (valid : ConfigBounded config) : OutcomeBounded (step parameters config) := by
  rcases config with ⟨memory, control, stack⟩
  rcases valid with ⟨bounded, frames⟩
  cases control with
  | eval environment expression =>
      exact eval_bounded parameters memory environment expression stack bounded frames
  | value value => exact value_bounded parameters memory value stack bounded frames
  | raised packet => exact raised_bounded parameters memory packet stack bounded frames
  | pattern environment pattern value =>
      exact pattern_bounded parameters memory environment pattern value stack bounded frames
  | matched bindings => exact matched_bounded parameters memory bindings stack bounded frames
  | mismatch => exact mismatch_bounded parameters memory stack bounded frames
  | clauses environment clauses value =>
      exact clauses_bounded parameters memory environment clauses value stack bounded frames
  | rows environment patterns fields bindings =>
      exact rows_bounded parameters memory environment patterns fields bindings stack bounded frames
  | recursive environment bindings created body =>
      exact recursive_bounded parameters memory environment bindings created body stack bounded frames

theorem evaluates_bounded {parameters : Parameters Primitive} {config : Config Primitive}
    {answer : Answer Primitive} {steps : Nat} (valid : ConfigBounded config)
    (evaluation : Progress.Evaluates (step parameters) config answer steps) :
    Suspensions.Bounded answer.memory := by
  revert valid
  induction evaluation with
  | done finished =>
      intro valid
      have preserved := step_bounded (parameters := parameters) valid
      rw [finished] at preserved
      exact preserved
  | next moved _ ih =>
      intro valid
      have preserved := step_bounded (parameters := parameters) valid
      rw [moved] at preserved
      exact ih preserved

theorem start_evaluates_bounded {parameters : Parameters Primitive} {memory : Memory Primitive}
    {environment : Env Primitive} {expression : Expr Primitive} {answer : Answer Primitive}
    {steps : Nat} (bounded : Suspensions.Bounded memory)
    (evaluation : Progress.Evaluates (step parameters)
      (start memory environment expression) answer steps) : Suspensions.Bounded answer.memory :=
  evaluates_bounded (start_bounded bounded environment expression) evaluation

theorem startPattern_evaluates_bounded {parameters : Parameters Primitive} {memory : Memory Primitive}
    {environment : Env Primitive} {pattern : Pattern} {value : Value Primitive}
    {answer : Answer Primitive} {steps : Nat} (bounded : Suspensions.Bounded memory)
    (evaluation : Progress.Evaluates (step parameters)
      (startPattern memory environment pattern value) answer steps) : Suspensions.Bounded answer.memory :=
  evaluates_bounded (startPattern_bounded bounded environment pattern value) evaluation

/-- The finite domain contains every occupied cell of the reached memory. -/
theorem evaluates_domain {parameters : Parameters Primitive} {config : Config Primitive}
    {answer : Answer Primitive} {steps : Nat} (valid : ConfigBounded config)
    (evaluation : Progress.Evaluates (step parameters) config answer steps) (address : Nat) :
    address ∈ Suspensions.domain answer.memory ↔
      ∃ cell, answer.memory.memory address = some cell :=
  Suspensions.mem_domain (evaluates_bounded valid evaluation) address

private theorem advance_bounded {parameters : Parameters Primitive}
    {state : Answer Primitive ⊕ Config Primitive} (valid : OutcomeBounded state) :
    OutcomeBounded (Prefix.advance parameters state) := by
  cases state with
  | inl answer => exact valid
  | inr config => exact step_bounded (parameters := parameters) valid

/-- Finite observation preserves the reached state, including unfinished
configurations. Absorbing a delivered answer introduces no body-work claim. -/
theorem observe_bounded {parameters : Parameters Primitive} {config : Config Primitive}
    (valid : ConfigBounded config) (budget : Nat) :
    OutcomeBounded (Prefix.observe parameters budget config) := by
  have iterates : ∀ n (state : Answer Primitive ⊕ Config Primitive), OutcomeBounded state →
      OutcomeBounded ((Prefix.advance parameters)^[n] state) := by
    intro n
    induction n with
    | zero => intro state valid; exact valid
    | succ n ih =>
        intro state valid
        rw [Function.iterate_succ_apply]
        exact ih _ (advance_bounded (parameters := parameters) valid)
  exact iterates budget (.inr config) valid

theorem observe_unfinished_bounded {parameters : Parameters Primitive} {config next : Config Primitive}
    {budget : Nat} (valid : ConfigBounded config)
    (observed : Prefix.observe parameters budget config = .inr next) : ConfigBounded next := by
  have preserved := observe_bounded (parameters := parameters) valid budget
  rw [observed] at preserved
  exact preserved

theorem observe_finished_bounded {parameters : Parameters Primitive} {config : Config Primitive}
    {answer : Answer Primitive} {budget : Nat} (valid : ConfigBounded config)
    (observed : Prefix.observe parameters budget config = .inl answer) :
    Suspensions.Bounded answer.memory := by
  have preserved := observe_bounded (parameters := parameters) valid budget
  rw [observed] at preserved
  exact preserved

end Suspensions.Core.Machine
