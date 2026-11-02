import Applications.Suspensions.Machine

/-!
# Exact origins of raw suspension-body events

A body-entry event is emitted precisely when a suspended pattern inspects an
address whose current cell is an unforced thunk. The address in the event is
the actual inspected address, even when several cells have identical code
and captures. Cached values instead emit hit events; missing addresses fault.

This characterization is unrestricted: it assumes neither a valid heap nor
typing, purity, representation, termination or absence of reentry. It inspects
the existing transition, without introducing another event generator or run.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Suspensions.Core.Machine
variable {Primitive : Type}

private theorem eval_no_body (parameters : Parameters Primitive) (memory : Memory Primitive)
    (environment : Env Primitive) (expression : Expr Primitive)
    (stack : List (Frame Primitive)) (address : Nat) :
    (transition parameters ⟨memory, .eval environment expression, stack⟩).2 ≠ .body address := by
  intro event
  cases expression <;> simp only [transition, proceed, finish] at event
  all_goals repeat' first | (solve | simp_all) | split at event

private theorem value_no_body (parameters : Parameters Primitive) (memory : Memory Primitive)
    (value : Value Primitive) (stack : List (Frame Primitive)) (address : Nat) :
    (transition parameters ⟨memory, .value value, stack⟩).2 ≠ .body address := by
  intro event
  cases stack with
  | nil => cases event
  | cons frame rest =>
      cases frame <;> simp only [transition, proceed, finish] at event
      all_goals repeat' first | (solve | simp_all) | split at event

private theorem raised_no_body (parameters : Parameters Primitive) (memory : Memory Primitive)
    (packet : Value Primitive) (stack : List (Frame Primitive)) (address : Nat) :
    (transition parameters ⟨memory, .raised packet, stack⟩).2 ≠ .body address := by
  intro event
  cases stack with
  | nil => cases event
  | cons frame rest => cases frame <;> cases event

private theorem suspended_body_origin (parameters : Parameters Primitive) (memory : Memory Primitive)
    (caller : Env Primitive) (inner : Pattern) (value : Value Primitive)
    (stack : List (Frame Primitive)) (address : Nat)
    (event : (transition parameters ⟨memory, .pattern caller (.suspended inner) value, stack⟩).2 =
      .body address) :
    ∃ body captured, value = .address address ∧ memory.memory address = some (.thunk body captured) := by
  cases value with
  | address actual =>
      cases found : memory.memory actual with
      | none => simp only [transition, found, finish] at event; cases event
      | some cell =>
          cases cell with
          | value value => simp only [transition, found, proceed] at event; cases event
          | thunk body captured =>
              have same : actual = address := by
                simpa only [transition, found, proceed, Event.body.injEq] using event
              subst actual
              exact ⟨body, captured, rfl, found⟩
  | atom _ | constructor _ _ | record _ | closure _ _ _ | primitive _ | exception _ _ => cases event

private theorem pattern_body_origin (parameters : Parameters Primitive) (memory : Memory Primitive)
    (caller : Env Primitive) (pattern : Pattern) (value : Value Primitive)
    (stack : List (Frame Primitive)) (address : Nat)
    (event : (transition parameters ⟨memory, .pattern caller pattern value, stack⟩).2 = .body address) :
    ∃ inner body captured, pattern = .suspended inner ∧ value = .address address ∧
      memory.memory address = some (.thunk body captured) := by
  cases pattern with
  | suspended inner =>
      obtain ⟨body, captured, inspected, found⟩ :=
        suspended_body_origin parameters memory caller inner value stack address event
      exact ⟨inner, body, captured, rfl, inspected, found⟩
  | wildcard | «variable» _ | atom _ | constructor _ _ | exception _ _ | record _
  | reference _ | layered _ _ =>
      simp only [transition, proceed, finish] at event
      repeat' first | (solve | simp_all) | split at event

private theorem matched_no_body (parameters : Parameters Primitive) (memory : Memory Primitive)
    (bindings : Env Primitive) (stack : List (Frame Primitive)) (address : Nat) :
    (transition parameters ⟨memory, .matched bindings, stack⟩).2 ≠ .body address := by
  intro event
  cases stack with
  | nil => cases event
  | cons frame rest => cases frame <;> cases event

private theorem mismatch_no_body (parameters : Parameters Primitive) (memory : Memory Primitive)
    (stack : List (Frame Primitive)) (address : Nat) :
    (transition parameters ⟨memory, .mismatch, stack⟩).2 ≠ .body address := by
  intro event
  cases stack with
  | nil => cases event
  | cons frame rest => cases frame <;> cases event

private theorem clauses_no_body (parameters : Parameters Primitive) (memory : Memory Primitive)
    (environment : Env Primitive) (clauses : List (Pattern × Expr Primitive)) (value : Value Primitive)
    (stack : List (Frame Primitive)) (address : Nat) :
    (transition parameters ⟨memory, .clauses environment clauses value, stack⟩).2 ≠ .body address := by
  intro event
  cases clauses with
  | nil => cases event
  | cons clause rest => cases clause; cases event

private theorem rows_no_body (parameters : Parameters Primitive) (memory : Memory Primitive)
    (environment : Env Primitive) (patterns : List (Nat × Pattern)) (fields bindings : Env Primitive)
    (stack : List (Frame Primitive)) (address : Nat) :
    (transition parameters ⟨memory, .rows environment patterns fields bindings, stack⟩).2 ≠
      .body address := by
  intro event
  cases patterns with
  | nil => cases event
  | cons row rest =>
      rcases row with ⟨label, pattern⟩
      simp only [transition, proceed, finish] at event
      repeat' first | (solve | simp_all) | split at event

private theorem recursive_no_body (parameters : Parameters Primitive) (memory : Memory Primitive)
    (environment : Env Primitive) (bindings : List (Nat × Expr Primitive)) (created : Env Primitive)
    (body : Expr Primitive) (stack : List (Frame Primitive)) (address : Nat) :
    (transition parameters ⟨memory, .recursive environment bindings created body, stack⟩).2 ≠
      .body address := by
  intro event
  cases bindings with
  | nil => cases event
  | cons binding rest =>
      rcases binding with ⟨name, expression⟩
      simp only [transition, proceed, finish] at event
      repeat' first | (solve | simp_all) | split at event

/-- Exact source of every actual raw body-entry event. Both the inspected
address and the current thunk lookup are retained, without validity premises. -/
theorem body_event_iff (parameters : Parameters Primitive) (config : Config Primitive) (address : Nat) :
    (transition parameters config).2 = .body address ↔
      ∃ caller inner body captured,
        config.control = .pattern caller (.suspended inner) (.address address) ∧
          config.memory.memory address = some (.thunk body captured) := by
  rcases config with ⟨memory, control, stack⟩
  constructor
  · intro event
    cases control with
    | eval environment expression =>
        exact False.elim (eval_no_body parameters memory environment expression stack address event)
    | value value => exact False.elim (value_no_body parameters memory value stack address event)
    | raised packet => exact False.elim (raised_no_body parameters memory packet stack address event)
    | pattern caller pattern value =>
        obtain ⟨inner, body, captured, rfl, rfl, found⟩ :=
          pattern_body_origin parameters memory caller pattern value stack address event
        exact ⟨caller, inner, body, captured, rfl, found⟩
    | matched bindings => exact False.elim (matched_no_body parameters memory bindings stack address event)
    | mismatch => exact False.elim (mismatch_no_body parameters memory stack address event)
    | clauses environment clauses value =>
        exact False.elim (clauses_no_body parameters memory environment clauses value stack address event)
    | rows environment patterns fields bindings =>
        exact False.elim (rows_no_body parameters memory environment patterns fields bindings stack address event)
    | recursive environment bindings created body =>
        exact False.elim (recursive_no_body parameters memory environment bindings created body stack address event)
  · rintro ⟨caller, inner, body, captured, matching, found⟩
    cases matching
    exact congrArg Prod.snd (body_transition parameters memory caller captured inner address body stack found)

/-- A single transition cannot identify two different body addresses. Equal
code or captures at distinct cells do not collapse their event identities. -/
theorem body_event_address_unique {parameters : Parameters Primitive} {config : Config Primitive}
    {first second : Nat} (left : (transition parameters config).2 = .body first)
    (right : (transition parameters config).2 = .body second) : first = second :=
  Event.body.inj (left.symm.trans right)

end Suspensions.Core.Machine
