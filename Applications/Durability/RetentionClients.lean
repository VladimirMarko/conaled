import Applications.Durability.RetentionResources
import Applications.Durability.RetentionOwnership

namespace Durability.Retention

theorem command_history_prefix (c : Config) (s : Service (List Bool)) (cmd : Command) :
    s.store <+: (command c (ghostOps c) s cmd).2.store := by
  cases cmd
  case release b =>
    cases b <;> simp only [command]
    all_goals repeat' split
    all_goals exact List.prefix_refl _
  case scan b =>
    cases b <;> simp only [command]
    all_goals repeat' split
    all_goals exact List.prefix_refl _
  case stream b =>
    cases b <;> simp only [command]
    all_goals repeat' split
    all_goals exact List.prefix_refl _
  all_goals simp only [command]
  all_goals repeat' split
  all_goals first | exact List.prefix_refl _ | exact ⟨[_], rfl⟩

theorem ghost_history_prefix {c : Config} {a b : Service (List Bool)} {event : Label}
    (step : GhostStep c event a b) : a.store <+: b.store := by
  cases step with
  | internal => exact List.prefix_refl _
  | command => exact command_history_prefix _ _ _
  | pendingBusy _ _ _ => exact List.prefix_refl _

theorem execution_history_prefix {c : Config} {a b : Service (List Bool)} {events : List Label}
    (steps : Execution (GhostStep c) events a b) : a.store <+: b.store := by
  induction steps with
  | nil => exact List.prefix_refl _
  | cons step _ ih => exact (ghost_history_prefix step).trans ih

/-- The ghost committed effect at an original index survives. This theorem
makes no promise that the retained service still admits payload retrieval. -/
theorem committed_effect_survives {c : Config} {a b : Service (List Bool)} {events : List Label}
    (steps : Execution (GhostStep c) events a b) {i : Nat} {p : Bool}
    (committed : a.store[i]? = some p) : b.store[i]? = some p := by
  obtain ⟨tail, heq⟩ := execution_history_prefix steps
  obtain ⟨bound, eq⟩ := List.getElem?_eq_some_iff.mp committed
  rw [← heq]
  simpa [List.getElem?_append, bound] using committed

/-- An already-published pending request cannot publish twice. -/
theorem duplicate_publish_busy (c : Config) (ops : Operations α) (s : Service α)
    (online : s.control.online = true) (done : s.control.committed = true) :
    command c ops s .publish = (.busy, s) := by
  simp [command, online, done]
  cases s.control.pending <;> rfl

theorem retained_retry_safe {c : Config} {s : Snapshot} {h : List Bool}
    (r : Represents c s h) {e i : Nat} {p : Bool}
    (ack : classify c s e i p = .acknowledged e i) : i < h.length ∧ h[i]? = some p := by
  rw [classify_refines r] at ack
  unfold specClassify at ack
  split_ifs at ack; simp_all

theorem expired_never_fresh {c : Config} {s : Snapshot} {e i : Nat} {p : Bool}
    (same : e = c.incarnation) (domain : i ≤ c.limit) (expired : i < s.lower) :
    classify c s e i p = .expired s.lower := by
  simp [classify, same, expired, Nat.not_lt.mpr domain]

theorem newest_retained_ack {c : Config} {s : Snapshot} {h : List Bool}
    (r : Represents c s h) (room : s.position < c.limit) (p : Bool) :
    classify c (append c s p) c.incarnation s.position p = .acknowledged c.incarnation s.position := by
  rw [classify_refines (append_represents r room p), r.1]
  have positive := c.positive
  have limit : h.length ≤ c.limit := by rw [← r.1]; omega
  have lower : ¬h.length < (h ++ [p]).length - c.window := by simp only [List.length_append, List.length_singleton]; omega
  simp [specClassify, Nat.not_lt.mpr limit]
  omega

theorem publication_ack {c : Config} {s : Service Banks} {p : Bool}
    (allowed : CanPublish c s p) :
    (command c (bankOps c) (published c s p) .acknowledge).1 =
      .acknowledged c.incarnation s.store.root.position := by
  simp [command, published, allowed.1, allowed.2.1, bankOps, replacement_root, append]

/-- Old delayed views retain their own position; a minimum beyond that position
never returns a tuple assembled from a new count and old parity. -/
theorem delayed_minimum {c : Config} {ops : Operations α} {s : Service α} {n minimum : Nat} {b : Bool}
    (online : s.control.online = true) (view : s.control.delayed = some (n,b))
    (later : n < minimum) : command c ops s (.view minimum) = (.notReady, s) := by
  simp [command, viewReply, online, view, Nat.not_le.mpr later]

/-- One scan step reads one frozen record. Its accumulator law is independent
of the service kernel and preserves the entire prefix contribution. -/
theorem scan_accumulator (past : Bool) (xs : List Bool) {i : Nat} {p : Bool}
    (read : xs[i]? = some p) :
    xor (xor past (parity (xs.take i))) p = xor past (parity (xs.take (i + 1))) := by
  rw [List.take_add_one, read]
  simp only [Option.toList_some, parity_append, parity]
  cases past <;> cases (parity (xs.take i)) <;> cases p <;> rfl

theorem scan_complete (s : Snapshot) {i : Nat} (done : s.items[i]? = none) :
    xor s.pastParity (parity (s.items.take i)) = s.total := by
  have bound := List.getElem?_eq_none_iff.mp done
  simp [List.take_of_length_le bound, Snapshot.total]

def ScanValid (s : Service Banks) : Prop := s.control.pinned = true →
  s.control.scanIndex ≤ s.store.root.items.length ∧
  s.control.scanParity = xor s.store.root.pastParity
    (parity (s.store.root.items.take s.control.scanIndex))

theorem command_scan_valid {c : Config} {s : Service Banks}
    (valid : ScanValid s) (exclusive : Exclusive s.control) (cmd : Command) :
    ScanValid (command c (bankOps c) s cmd).2 := by
  have one : ∀ i p, s.store.root.items[i]? = some p →
      i + 1 ≤ s.store.root.items.length ∧
      xor (xor s.store.root.pastParity (parity (s.store.root.items.take i))) p =
        xor s.store.root.pastParity (parity (s.store.root.items.take (i + 1))) := by
    intro i p eq
    exact ⟨by have := (List.getElem?_eq_some_iff.mp eq).choose; omega, scan_accumulator _ _ eq⟩
  cases cmd
  case release b =>
    cases b <;> simp only [command]
    all_goals repeat' split
    all_goals simp_all [ScanValid]
  case scan b =>
    cases b <;> simp only [command]
    all_goals repeat' split
    all_goals simp_all only [ScanValid, bankOps]
    all_goals try have nextBound := (List.getElem?_eq_some_iff.mp ‹s.store.root.items[s.control.scanIndex]? = some _›).choose
    all_goals aesop
  case stream b =>
    cases b <;> simp only [command]
    all_goals repeat' split
    all_goals simp_all only [ScanValid, bankOps]
    all_goals try have nextBound := (List.getElem?_eq_some_iff.mp ‹s.store.root.items[s.control.scanIndex]? = some _›).choose
    all_goals aesop
  all_goals simp only [command]
  all_goals repeat' split
  all_goals simp_all [ScanValid, Exclusive, bankOps, parity]

theorem rebuild_publishes_snapshot {c : Config} {s : Service Banks} {h : List Bool}
    (r : Represents c s.store.root h) (valid : ScanValid s)
    (online : s.control.online = true) (pinned : s.control.pinned = true)
    (done : s.store.root.items[s.control.scanIndex]? = none) :
    command c (bankOps c) s (.scan true) =
      (.summary c.incarnation h.length (parity h),
       { s with control := { s.control with pinned := false, scanIndex := 0, scanParity := false, delayed := some (h.length, parity h) } }) := by
  have parityEq : s.control.scanParity = parity h :=
    (valid pinned).2.trans ((scan_complete s.store.root done).trans r.total)
  simp [command, online, pinned, bankOps, done, parityEq, r.1]

/-- Later commits preserve the meaning of a completed delayed tuple at its old
position. They do not turn it into the current summary. -/
theorem delayed_snapshot_survives {c : Config} {a b : Service (List Bool)} {events : List Label}
    (steps : Execution (GhostStep c) events a b) :
    parity (b.store.take a.store.length) = parity a.store := by
  obtain ⟨tail, eq⟩ := execution_history_prefix steps
  rw [← eq]
  simp

/-- The slot-borrowing invariant needed by the concrete bank writer follows
from mutual exclusion, offline recovery, and the pending copy mode. -/
theorem reachable_exclusive {c : Config} {m : Machine} {events : List Label}
    (run : Execution (MachineStep c) events initialMachine m) : Exclusive m.control := by
  have general : ∀ {start stop : Machine} {es : List Label},
      Execution (MachineStep c) es start stop → Exclusive start.control → Exclusive stop.control := by
    intro start stop es steps
    induction steps with
    | nil => exact id
    | cons step tail ih => exact fun h => ih (machine_exclusive step h)
  exact general run (by simp [Exclusive, initialMachine, Machine.control])

def Machine.service (m : Machine) : Service Banks := ⟨m.disk, m.control⟩

theorem machine_scan_valid {c : Config} {m n : Machine} {event : Label}
    (step : MachineStep c event m n) (valid : ScanValid m.service)
    (exclusive : Exclusive m.control) : ScanValid n.service := by
  cases step with
  | command _ => exact command_scan_valid valid exclusive _
  | begin allowed =>
    simpa only [ScanValid, Machine.service, copyingAt_control, idle_disk, idle_control, copyingAt_root _ _ _ 0 (Nat.zero_le _)] using valid
  | @copy s p count allowed bound =>
    have before := copyingAt_root c s p count (by omega)
    have after := copyingAt_root c s p (count + 1) (by omega)
    simpa only [ScanValid, Machine.service, copyingAt_control, before, after] using valid
  | @publish s p allowed =>
    have pin := exclusive_publish_unpinned exclusive allowed
    simp [ScanValid, Machine.service, Machine.control, published, pin]
  | crash => simp [ScanValid, Machine.service, Machine.control, crashed]
  | busy _ _ => exact valid
  | fenced _ => exact valid
  | view _ => exact valid

theorem reachable_scan_valid {c : Config} {m : Machine} {events : List Label}
    (run : Execution (MachineStep c) events initialMachine m) : ScanValid m.service := by
  have general : ∀ {start stop : Machine} {es : List Label},
      Execution (MachineStep c) es start stop → ScanValid start.service →
      Exclusive start.control → ScanValid stop.service := by
    intro start stop es steps
    induction steps with
    | nil => intro h _; exact h
    | cons step tail ih =>
      intro h ex
      exact ih (machine_scan_valid step h ex) (machine_exclusive step ex)
  exact general run (by simp [ScanValid, Machine.service, initialMachine, Machine.control])
    (by simp [Exclusive, initialMachine, Machine.control])

/-- A copying process has no admitted reader and no recovery cursor. -/
def CopyReady : Machine → Prop
  | .idle _ => True
  | .copying _ _ ctl _ => ctl.online = true ∧ ctl.pinned = false

theorem copy_ready_preserved {c : Config} {m n : Machine} {event : Label}
    (step : MachineStep c event m n) (ready : CopyReady m) (exclusive : Exclusive m.control) :
    CopyReady n := by
  cases step with
  | command _ => trivial
  | begin allowed => exact ⟨allowed.1, exclusive_publish_unpinned exclusive allowed⟩
  | copy _ _ => exact ready
  | publish _ => trivial
  | crash => trivial
  | busy _ _ => exact ready
  | fenced _ => exact ready
  | view _ => exact ready

theorem reachable_copy_ready {c : Config} {m : Machine} {events : List Label}
    (run : Execution (MachineStep c) events initialMachine m) : CopyReady m := by
  have general : ∀ {start stop : Machine} {es : List Label},
      Execution (MachineStep c) es start stop → CopyReady start →
      Exclusive start.control → CopyReady stop := by
    intro start stop es steps
    induction steps with
    | nil => intro h _; exact h
    | cons step tail ih =>
      intro h ex
      exact ih (copy_ready_preserved step h ex) (machine_exclusive step ex)
  exact general run trivial (by simp [Exclusive, initialMachine, Machine.control])

/-- The copy plan reads its owned target suffix, never an old bank address.
The plan's writer address is the inactive bank; `Access.plan` describes only
borrowed read addresses that could be invalidated by overwriting. -/
def borrowedAccess (m : Machine) : Access :=
  ⟨if m.control.pinned then some m.disk.selected else none,
   if m.control.online then none else some m.disk.selected, none⟩

theorem reachable_reuse_safe {c : Config} {cells : CopyState} {target : Snapshot} {ctl : Control}
    {pc : CopyPC} {events : List Label}
    (run : Execution (MachineStep c) events initialMachine (.copying cells target ctl pc)) :
    borrowedAccess (.copying cells target ctl pc) = Access.afterPublication ∧
    (borrowedAccess (.copying cells target ctl pc)).safeOverwrite (!cells.disk.selected) ∧
    cells.disk.selected ≠ !cells.disk.selected := by
  have ready := reachable_copy_ready run
  have eq : borrowedAccess (.copying cells target ctl pc) = Access.afterPublication := by
    simp [borrowedAccess, Machine.control, ready.1, ready.2, Access.afterPublication]
  refine ⟨eq, ?_, ?_⟩
  · rw [eq]; exact retired_safe _
  · cases cells.disk.selected <;> decide

end Durability.Retention
