import Applications.Suspensions.Pending
import Applications.Suspensions.ValuePersistence

/-!
# Successful cache writes and settled continuations

A cache-write event comes from returning through the corresponding memoize
frame. After that frame is removed, a retained value cell and absence of any
older pending frame for the same address prevent every later cache write to
that address. The payload may still change by reference assignment.

These raw laws state their stack premises explicitly. The pure finite source
application derives those premises from actual nonreentry; this module does
not assume purity or change the transition system.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Suspensions.Core.Machine
variable {Primitive : Type}

private theorem eval_no_cacheWrite (parameters : Parameters Primitive) (memory : Memory Primitive)
    (environment : Env Primitive) (expression : Expr Primitive)
    (stack : List (Frame Primitive)) (address : Nat) :
    (transition parameters ⟨memory, .eval environment expression, stack⟩).2 ≠ .cacheWrite address := by
  intro event
  cases expression <;> simp only [transition, proceed, finish] at event
  all_goals repeat' first | (solve | simp_all) | split at event


private theorem raised_no_cacheWrite (parameters : Parameters Primitive) (memory : Memory Primitive)
    (packet : Value Primitive) (stack : List (Frame Primitive)) (address : Nat) :
    (transition parameters ⟨memory, .raised packet, stack⟩).2 ≠ .cacheWrite address := by
  intro event
  cases stack with
  | nil => cases event
  | cons frame rest => cases frame <;> cases event


private theorem matched_no_cacheWrite (parameters : Parameters Primitive) (memory : Memory Primitive)
    (bindings : Env Primitive) (stack : List (Frame Primitive)) (address : Nat) :
    (transition parameters ⟨memory, .matched bindings, stack⟩).2 ≠ .cacheWrite address := by
  intro event
  cases stack with
  | nil => cases event
  | cons frame rest => cases frame <;> cases event


private theorem mismatch_no_cacheWrite (parameters : Parameters Primitive) (memory : Memory Primitive)
    (stack : List (Frame Primitive)) (address : Nat) :
    (transition parameters ⟨memory, .mismatch, stack⟩).2 ≠ .cacheWrite address := by
  intro event
  cases stack with
  | nil => cases event
  | cons frame rest => cases frame <;> cases event


private theorem clauses_no_cacheWrite (parameters : Parameters Primitive) (memory : Memory Primitive)
    (environment : Env Primitive) (clauses : List (Pattern × Expr Primitive)) (value : Value Primitive)
    (stack : List (Frame Primitive)) (address : Nat) :
    (transition parameters ⟨memory, .clauses environment clauses value, stack⟩).2 ≠ .cacheWrite address := by
  intro event
  cases clauses with
  | nil => cases event
  | cons clause rest => cases clause; cases event


private theorem rows_no_cacheWrite (parameters : Parameters Primitive) (memory : Memory Primitive)
    (environment : Env Primitive) (patterns : List (Nat × Pattern)) (fields bindings : Env Primitive)
    (stack : List (Frame Primitive)) (address : Nat) :
    (transition parameters ⟨memory, .rows environment patterns fields bindings, stack⟩).2 ≠
      .cacheWrite address := by
  intro event
  cases patterns with
  | nil => cases event
  | cons row rest =>
      rcases row with ⟨label, pattern⟩
      simp only [transition, proceed, finish] at event
      repeat' first | (solve | simp_all) | split at event


private theorem recursive_no_cacheWrite (parameters : Parameters Primitive) (memory : Memory Primitive)
    (environment : Env Primitive) (bindings : List (Nat × Expr Primitive)) (created : Env Primitive)
    (body : Expr Primitive) (stack : List (Frame Primitive)) (address : Nat) :
    (transition parameters ⟨memory, .recursive environment bindings created body, stack⟩).2 ≠
      .cacheWrite address := by
  intro event
  cases bindings with
  | nil => cases event
  | cons binding rest =>
      rcases binding with ⟨name, expression⟩
      simp only [transition, proceed, finish] at event
      repeat' first | (solve | simp_all) | split at event


private theorem value_cacheWrite_origin (parameters : Parameters Primitive) (memory : Memory Primitive)
    (value : Value Primitive) (stack : List (Frame Primitive)) (address : Nat)
    (event : (transition parameters ⟨memory, .value value, stack⟩).2 = .cacheWrite address) :
    ∃ environment inner rest, stack = .memoize address environment inner :: rest := by
  cases stack with
  | nil => cases event
  | cons frame rest =>
      cases frame with
      | memoize actual environment inner =>
          have same : actual = address := by
            simpa only [transition, proceed, Event.cacheWrite.injEq] using event
          subst actual
          exact ⟨environment, inner, rest, rfl⟩
      | constructor _ | record _ _ _ _ | function _ _ | argument _
      | bindValue _ _ _ | bindMatch _ _ | branch _ _ _ | reference | read
      | assignReference _ _ | assignValue _ | raise | handler _ _ | handlerResult _
      | applicationResult | clause _ _ _ _ | row _ _ _ _ | layered _ _ | recursive _ _ _ _ _ =>
          simp only [transition, proceed, finish] at event
          repeat' first | (solve | simp_all) | split at event

private theorem pattern_no_cacheWrite (parameters : Parameters Primitive) (memory : Memory Primitive)
    (environment : Env Primitive) (pattern : Pattern) (value : Value Primitive)
    (stack : List (Frame Primitive)) (address : Nat) :
    (transition parameters ⟨memory, .pattern environment pattern value, stack⟩).2 ≠ .cacheWrite address := by
  intro event
  cases pattern <;> simp only [transition, proceed, finish] at event
  all_goals repeat' first | (solve | simp_all) | split at event

/-- The successful write event identifies the current return and the exact
pending frame removed by that transition. The raw machine does not require
the overwritten cell to remain a thunk. -/
theorem cacheWrite_event_iff (parameters : Parameters Primitive) (config : Config Primitive) (address : Nat) :
    (transition parameters config).2 = .cacheWrite address ↔
      ∃ value environment inner rest, config.control = .value value ∧
        config.stack = .memoize address environment inner :: rest := by
  rcases config with ⟨memory, control, stack⟩
  constructor
  · intro event
    cases control with
    | eval environment expression =>
        exact False.elim (eval_no_cacheWrite parameters memory environment expression stack address event)
    | value value =>
        obtain ⟨environment, inner, rest, same⟩ :=
          value_cacheWrite_origin parameters memory value stack address event
        exact ⟨value, environment, inner, rest, rfl, same⟩
    | raised packet => exact False.elim (raised_no_cacheWrite parameters memory packet stack address event)
    | pattern environment pattern value =>
        exact False.elim (pattern_no_cacheWrite parameters memory environment pattern value stack address event)
    | matched bindings => exact False.elim (matched_no_cacheWrite parameters memory bindings stack address event)
    | mismatch => exact False.elim (mismatch_no_cacheWrite parameters memory stack address event)
    | clauses environment clauses value =>
        exact False.elim (clauses_no_cacheWrite parameters memory environment clauses value stack address event)
    | rows environment patterns fields bindings =>
        exact False.elim (rows_no_cacheWrite parameters memory environment patterns fields bindings stack address event)
    | recursive environment bindings created body =>
        exact False.elim (recursive_no_cacheWrite parameters memory environment bindings created body stack address event)
  · rintro ⟨value, environment, inner, rest, sameControl, sameStack⟩
    cases sameControl
    cases sameStack
    rfl

/-- A value cell together with absence of any older pending write to its
address. Other addresses and reference assignments remain unrestricted. -/
def Settled (address : Nat) (config : Config Primitive) : Prop :=
  HasValue config.memory address ∧ address ∉ pendingAddresses config.stack

def OutcomeSettled (address : Nat) : Answer Primitive ⊕ Config Primitive → Prop
  | .inl answer => HasValue answer.memory address
  | .inr config => Settled address config

theorem Settled.no_cacheWrite {parameters : Parameters Primitive} {config : Config Primitive}
    {address : Nat} (settled : Settled address config) :
    (transition parameters config).2 ≠ .cacheWrite address := by
  intro event
  obtain ⟨value, environment, inner, rest, _, sameStack⟩ :=
    (cacheWrite_event_iff parameters config address).mp event
  apply settled.2
  simp [sameStack]

/-- No new pending write can be created for a retained value cell: it would
require a body event whose lookup is a thunk instead. -/
theorem step_settled {parameters : Parameters Primitive} {config : Config Primitive} {address : Nat}
    (bounded : Suspensions.Bounded config.memory) (settled : Settled address config) :
    OutcomeSettled address (step parameters config) := by
  have value := step_hasValue (parameters := parameters) bounded settled.1
  have pending := pending_transition parameters config
  cases moved : step parameters config with
  | inl answer =>
      rw [moved] at value
      exact value
  | inr next =>
      rw [moved] at value pending
      refine ⟨value, ?_⟩
      rcases pending with smaller | ⟨fresh, event, added⟩
      · exact fun present => settled.2 (smaller.subset present)
      · rw [added]
        apply List.not_mem_cons.mpr
        refine ⟨?_, settled.2⟩
        intro same
        subst fresh
        exact hasValue_no_body settled.1 event

/-- A successful write with no duplicate pending address removes the unique
frame for that address and leaves a settled continuation. Boundedness for
later execution is a separate premise of the preservation laws. -/
theorem cacheWrite_settles {parameters : Parameters Primitive} {config : Config Primitive}
    {address : Nat} (distinct : (pendingAddresses config.stack).Nodup)
    (event : (transition parameters config).2 = .cacheWrite address) :
    ∃ next, step parameters config = .inr next ∧ Settled address next := by
  obtain ⟨value, environment, inner, rest, sameControl, sameStack⟩ :=
    (cacheWrite_event_iff parameters config address).mp event
  rw [sameStack, pendingAddresses_memoize] at distinct
  refine ⟨⟨Suspensions.memoize config.memory address value, .pattern environment inner value, rest⟩,
    ?_, ⟨⟨value, Suspensions.memoize_lookup config.memory address value⟩,
      (List.nodup_cons.mp distinct).1⟩⟩
  rcases config with ⟨memory, control, stack⟩
  cases sameControl
  cases sameStack
  rfl

/-- The existing bounded observer preserves the settled property. Its
absorbing finished states retain only the value-cell fact, with no stack. -/
theorem observe_settled {parameters : Parameters Primitive} {config : Config Primitive} {address : Nat}
    (valid : ConfigBounded config) (settled : Settled address config) (budget : Nat) :
    OutcomeSettled address (Prefix.observe parameters budget config) := by
  have iterates : ∀ n (state : Answer Primitive ⊕ Config Primitive), OutcomeBounded state →
      OutcomeSettled address state → OutcomeSettled address ((Prefix.advance parameters)^[n] state) := by
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
              (step_settled (parameters := parameters) bounded.1 kept)
  exact iterates budget (.inr config) valid settled

theorem observe_unfinished_settled {parameters : Parameters Primitive} {config next : Config Primitive}
    {budget address : Nat} (valid : ConfigBounded config) (settled : Settled address config)
    (reached : Prefix.observe parameters budget config = .inr next) : Settled address next := by
  have kept := observe_settled (parameters := parameters) valid settled budget
  rw [reached] at kept
  exact kept

theorem observe_no_cacheWrite {parameters : Parameters Primitive} {config next : Config Primitive}
    {budget address : Nat} (valid : ConfigBounded config) (settled : Settled address config)
    (reached : Prefix.observe parameters budget config = .inr next) :
    (transition parameters next).2 ≠ .cacheWrite address :=
  (observe_unfinished_settled valid settled reached).no_cacheWrite

end Suspensions.Core.Machine
