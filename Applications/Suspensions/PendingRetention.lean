import Applications.Suspensions.CacheWrite
import Applications.Suspensions.Continuation

/-!
# How a pending memoization address can disappear

An actual continuing transition retains a pending address, writes that address,
or exceptionally unwinds its exposed memoize frame. The proof splits at the
existing frame and reuses the ordinary continuation laws; it does not duplicate
the evaluator's transition cases.

In the absence of that particular unwind, a pending frame or a value cell keeps
the address protected from a fresh body entry. Value-cell preservation needs
bounded memory, while the raw stack classification needs neither boundedness
nor distinct pending addresses. Finished outcomes carry no residual stack claim.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Suspensions.Core.Machine
variable {Primitive : Type}

/-- The actual exposed memoize frame is being discarded by raised control.
Exceptions handled above this frame do not satisfy this predicate. -/
def UnwindsMemoize (address : Nat) (config : Config Primitive) : Prop :=
  ∃ packet environment inner rest,
    config.control = .raised packet ∧
      config.stack = .memoize address environment inner :: rest

/-- Continuing past an existing pending frame either retains its address,
successfully writes it, or exceptionally unwinds that very exposed frame.
Duplicate occurrences and unrelated raw effects are unrestricted. -/
theorem pending_mem_after_step {parameters : Parameters Primitive}
    {config next : Config Primitive} {address : Nat}
    (pending : address ∈ pendingAddresses config.stack)
    (moved : step parameters config = .inr next) :
    address ∈ pendingAddresses next.stack ∨
      (transition parameters config).2 = .cacheWrite address ∨
      UnwindsMemoize address config := by
  rcases config with ⟨memory, control, stack⟩
  obtain ⟨environment, inner, member⟩ :=
    (pendingAddresses_mem_iff address stack).mp pending
  obtain ⟨earlier, tail, rfl⟩ := List.mem_iff_append.mp member
  cases first : step parameters ⟨memory, control, earlier⟩ with
  | inr residual =>
      have advanced := step_append first (.memoize address environment inner :: tail)
      have same : next = appendFrames residual (.memoize address environment inner :: tail) :=
        Sum.inr.inj (moved.symm.trans advanced)
      refine Or.inl ?_
      rw [same]
      apply (pendingAddresses_mem_iff address _).mpr
      exact ⟨environment, inner, by simp [appendFrames]⟩
  | inl answer =>
      rcases answer with ⟨lastMemory, result⟩
      cases result with
      | value value =>
          have shape := step_boundary first (control := .value value) rfl
          have emptyPrefix : earlier = [] := congrArg Config.stack shape
          have returned : control = .value value := congrArg Config.control shape
          subst earlier
          subst control
          exact Or.inr (Or.inl rfl)
      | raised packet =>
          have shape := step_boundary first (control := .raised packet) rfl
          have emptyPrefix : earlier = [] := congrArg Config.stack shape
          have returned : control = .raised packet := congrArg Config.control shape
          subst earlier
          subst control
          exact Or.inr (Or.inr ⟨packet, environment, inner, tail, rfl, rfl⟩)
      | matched bindings =>
          have shape := step_boundary first (control := .matched bindings) rfl
          have emptyPrefix : earlier = [] := congrArg Config.stack shape
          have returned : control = .matched bindings := congrArg Config.control shape
          subst earlier
          subst control
          cases moved
      | mismatch =>
          have shape := step_boundary first (control := .mismatch) rfl
          have emptyPrefix : earlier = [] := congrArg Config.stack shape
          have returned : control = .mismatch := congrArg Config.control shape
          subst earlier
          subst control
          cases moved
      | stuck fault =>
          have finished := step_stuck_append first rfl
            (.memoize address environment inner :: tail)
          have impossible : (Sum.inr next : Answer Primitive ⊕ Config Primitive) =
              Sum.inl ⟨lastMemory, .stuck fault⟩ :=
            moved.symm.trans finished
          cases impossible

/-- A value cell need not retain its payload; a pending address need not occur
only once. These are the two ways the selected address can remain protected. -/
def PendingOrValue (address : Nat) (config : Config Primitive) : Prop :=
  HasValue config.memory address ∨ address ∈ pendingAddresses config.stack

/-- Finished answers have no future body events in the absorbing observer.
No value-cell or residual-stack assertion is made about such answers. -/
def OutcomePendingOrValue (address : Nat) : Answer Primitive ⊕ Config Primitive → Prop
  | .inl _ => True
  | .inr config => PendingOrValue address config

/-- Except for the selected exceptional unwind, an existing pending frame or
value cell remains one of those two alternatives after a continuing step. -/
theorem step_pending_or_value {parameters : Parameters Primitive}
    {config : Config Primitive} {address : Nat}
    (bounded : Suspensions.Bounded config.memory) (present : PendingOrValue address config)
    (noUnwind : ¬ UnwindsMemoize address config) :
    OutcomePendingOrValue address (step parameters config) := by
  cases moved : step parameters config with
  | inl answer => trivial
  | inr next =>
      change PendingOrValue address next
      rcases present with value | pending
      · have kept := step_hasValue (parameters := parameters) bounded value
        rw [moved] at kept
        exact Or.inl kept
      · rcases pending_mem_after_step pending moved with retained | written | unwound
        · exact Or.inr retained
        · obtain ⟨value, environment, inner, rest, sameControl, sameStack⟩ :=
            (cacheWrite_event_iff parameters config address).mp written
          rcases config with ⟨memory, control, stack⟩
          cases sameControl
          cases sameStack
          have same :
              (⟨Suspensions.memoize memory address value,
                .pattern environment inner value, rest⟩ : Config Primitive) = next :=
            Sum.inr.inj moved
          cases same
          exact Or.inl ⟨value, Suspensions.memoize_lookup memory address value⟩
        · exact False.elim (noUnwind unwound)

/-- The actual body-entry address is pending in its actual immediate successor.
This statement permits an older pending occurrence at the same address. -/
theorem body_entry_pending {parameters : Parameters Primitive}
    {config : Config Primitive} {address : Nat}
    (event : (transition parameters config).2 = .body address) :
    ∃ next, step parameters config = .inr next ∧ address ∈ pendingAddresses next.stack := by
  obtain ⟨caller, inner, body, captured, sameControl, found⟩ :=
    (body_event_iff parameters config address).mp event
  refine ⟨⟨config.memory, .eval captured body,
    .memoize address caller inner :: config.stack⟩, ?_, ?_⟩
  · rcases config with ⟨memory, control, stack⟩
    cases sameControl
    exact congrArg Prod.fst
      (body_transition parameters memory caller captured inner address body stack found)
  · change address ∈ address :: pendingAddresses config.stack
    exact List.mem_cons_self

end Suspensions.Core.Machine
