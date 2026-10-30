import Applications.Durability.RetentionMachine

namespace Durability.Retention

/-- Proof-side capability identities. They are absent from `Machine`, whose
only ownership storage is the pinned flag. A driver may realize the premise
with an affine type discipline rather than runtime counters or tombstones. -/
structure Handle where
  connection : Nat
  scope : Nat
  deriving DecidableEq, Repr

structure Ownership where
  connection : Nat
  owner : Option Nat
  consumed : Set Nat

def Ownership.admits (d : Ownership) (h : Handle) : Prop :=
  h.connection = d.connection ∧ d.owner = some h.scope ∧ h.scope ∉ d.consumed

inductive OwnershipStep : Ownership → Ownership → Prop
  | acquire {d name} : d.owner = none → name ∉ d.consumed →
      OwnershipStep d { d with owner := some name }
  | release {d h} : d.admits h →
      OwnershipStep d { d with owner := none, consumed := insert h.scope d.consumed }
  | use {d h} : d.admits h → OwnershipStep d d
  | restart {d} : OwnershipStep d ⟨d.connection + 1, none, ∅⟩

/-- Release consumes ownership even when no append changes the stored position. -/
theorem released_not_admitted (d : Ownership) (h : Handle) :
    ¬({ d with owner := none, consumed := insert h.scope d.consumed } : Ownership).admits h := by
  simp [Ownership.admits]

/-- Reacquisition uses a fresh scoped resource. An alias of the consumed owner
cannot release the new pin, even if its numeric position is unchanged. -/
theorem reacquired_excludes_old (d : Ownership) (h : Handle) (name : Nat) :
    ¬({ d with owner := some name, consumed := insert h.scope d.consumed } : Ownership).admits h := by
  simp [Ownership.admits]

theorem restarted_excludes_old (d : Ownership) (h : Handle) :
    ¬(⟨d.connection + 1, none, ∅⟩ : Ownership).admits h := by
  simp [Ownership.admits]

/-- The fencing adapter must derive this flag from connection validity. It is
not a client assertion trusted by the service. -/
def currentConnection (d : Ownership) (h : Handle) : Bool := h.connection == d.connection

theorem restart_flag (d : Ownership) (h : Handle) (old : h.connection = d.connection) :
    currentConnection ⟨d.connection + 1, none, ∅⟩ h = false := by
  simp [currentConnection, old]

theorem fenced_release {c : Config} (ops : Operations α) (s : Service α)
    (d : Ownership) (h : Handle) (old : h.connection = d.connection) :
    command c ops s (.release (currentConnection ⟨d.connection + 1, none, ∅⟩ h)) =
      (.invalidHandle, s) := by rw [restart_flag d h old]; rfl

/-- A successful public pin and the driver's acquired capability must agree.
This predicate does not claim Lean values are intrinsically linear. -/
def Owns (d : Ownership) (ctl : Control) : Prop := d.owner.isSome = ctl.pinned

theorem acquire_owns {d : Ownership} {ctl : Control} (name : Nat) :
    Owns { d with owner := some name } { ctl with pinned := true } := rfl

theorem release_owns {d : Ownership} {ctl : Control} (h : Handle) :
    Owns { d with owner := none, consumed := insert h.scope d.consumed }
      { ctl with pinned := false } := rfl

inductive HandleOperation where
  | release | scan | stream
  deriving DecidableEq

def handleCommand (d : Ownership) (h : Handle) : HandleOperation → Command
  | .release => .release (currentConnection d h)
  | .scan => .scan (currentConnection d h)
  | .stream => .stream (currentConnection d h)

/-- Stale connections may ask and receive InvalidHandle. A call in the current
connection is admitted only with the unique unconsumed scoped capability. -/
def AdmittedHandle (d : Ownership) (h : Handle) : Prop :=
  h.connection ≠ d.connection ∨ d.admits h

theorem replay_not_admitted (d : Ownership) (h : Handle) (name : Nat)
    (connection : h.connection = d.connection) :
    ¬AdmittedHandle { d with owner := some name, consumed := insert h.scope d.consumed } h := by
  simp [AdmittedHandle, connection, Ownership.admits]

/-- This is the connection between the affine premise and the actual service
release transition. It does not make a raw Boolean flag into a capability. -/
theorem owned_release {c : Config} (ops : Operations α) (s : Service α)
    (d : Ownership) (h : Handle) (admitted : d.admits h)
    (owns : Owns d s.control) (online : s.control.online = true) :
    (command c ops s (handleCommand d h .release)).1 = .released ∧
    Owns { d with owner := none, consumed := insert h.scope d.consumed }
      (command c ops s (handleCommand d h .release)).2.control ∧
    ¬AdmittedHandle { d with owner := none, consumed := insert h.scope d.consumed } h := by
  have pin : s.control.pinned = true := by
    rw [← owns, admitted.2.1]
    rfl
  simp [command, handleCommand, currentConnection, admitted.1, online, pin,
    Owns, AdmittedHandle, Ownership.admits]

def Exclusive (ctl : Control) : Prop := ctl.pinned = true → ctl.pending = none

theorem command_exclusive {c : Config} {ops : Operations α} {s : Service α}
    (h : Exclusive s.control) (cmd : Command) :
    Exclusive (command c ops s cmd).2.control := by
  cases cmd
  case release b =>
    cases b <;> simp only [command]
    all_goals repeat' split
    all_goals simp_all [Exclusive]
  case scan b =>
    cases b <;> simp only [command]
    all_goals repeat' split
    all_goals simp_all [Exclusive]
  case stream b =>
    cases b <;> simp only [command]
    all_goals repeat' split
    all_goals simp_all [Exclusive]
  all_goals simp only [command]
  all_goals repeat' split
  all_goals simp_all [Exclusive]

theorem pinned_append_busy {c : Config} {ops : Operations α} {s : Service α}
    (online : s.control.online = true) (pin : s.control.pinned = true)
    (e i : Nat) (p : Bool) : command c ops s (.append e i p) = (.busy, s) := by
  simp [command, online, pin]

theorem second_pin_busy {c : Config} {ops : Operations α} {s : Service α}
    (online : s.control.online = true) (pin : s.control.pinned = true) :
    command c ops s .pin = (.busy, s) := by simp [command, online, pin]

theorem exclusive_publish_unpinned {c : Config} {s : Service Banks} {p : Bool}
    (exclusive : Exclusive s.control) (allowed : CanPublish c s p) :
    s.control.pinned = false := by
  cases eq : s.control.pinned
  · rfl
  · have := exclusive eq
    rw [allowed.2.1] at this
    contradiction

/-- All reachable machine steps preserve the exclusion needed for safe reuse. -/
theorem machine_exclusive {c : Config} {m n : Machine} {event : Label}
    (step : MachineStep c event m n) (h : Exclusive m.control) : Exclusive n.control := by
  cases step with
  | command _ => exact command_exclusive h _
  | begin _ => exact h
  | copy _ _ => exact h
  | publish _ => exact h
  | crash => simp [Machine.control, crashed, Exclusive]
  | busy _ _ => exact h
  | fenced _ => exact h
  | view _ => exact h

/-- Connection fencing and within-connection affine ownership are separate:
`release true` is intentionally unable to recognize a replayed old scope. -/
theorem raw_release_clears_new_pin {c : Config} {ops : Operations α} {s : Service α}
    (online : s.control.online = true) (pin : s.control.pinned = true) :
    (command c ops s (.release true)).2.control.pinned = false := by
  simp [command, online, pin]

end Durability.Retention
