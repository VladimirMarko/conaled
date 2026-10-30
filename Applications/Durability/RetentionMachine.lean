import Applications.Durability.RetentionService

namespace Durability.Retention

/-- The runtime program counter is a record index plus a finite phase. The
unbounded cut number used in proofs is not an implementation field. -/
inductive CopyPC where
  | record (index : Nat) (persist : Bool)
  | descriptorWrite | descriptorPersist | selector
  deriving DecidableEq, Repr

def pcAt (length count : Nat) : CopyPC :=
  if count < 2 * length then .record (count / 2) (count % 2 = 1)
  else if count = 2 * length then .descriptorWrite
  else if count = 2 * length + 1 then .descriptorPersist else .selector

inductive Machine where
  | idle (service : Service Banks)
  | copying (cells : CopyState) (target : Snapshot) (control : Control) (pc : CopyPC)

def Machine.disk : Machine → Banks
  | .idle s => s.store
  | .copying cells _ _ _ => cells.disk

def Machine.control : Machine → Control
  | .idle s => s.control
  | .copying _ _ ctl _ => ctl

def copyingAt (c : Config) (s : Service Banks) (p : Bool) (count : Nat) : Machine :=
  let target := append c s.store.root p
  .copying (cut s.store target count) target s.control (pcAt target.items.length count)

@[simp] theorem copyingAt_control (c : Config) (s : Service Banks) (p : Bool) (count : Nat) :
    (copyingAt c s p count).control = s.control := rfl

@[simp] theorem idle_disk (s : Service Banks) : (Machine.idle s).disk = s.store := rfl
@[simp] theorem idle_control (s : Service Banks) : (Machine.idle s).control = s.control := rfl

/-- Only a pending unpublished request may acquire the inactive bank. -/
def CanPublish (c : Config) (s : Service Banks) (p : Bool) : Prop :=
  s.control.online = true ∧ s.control.pending = some p ∧
  s.control.committed = false ∧ s.store.root.position < c.limit

def published (c : Config) (s : Service Banks) (p : Bool) : Service Banks :=
  ⟨(bankOps c).append s.store p, { s.control with committed := true }⟩

def crashed (disk : Banks) : Service Banks := ⟨disk, { online := false }⟩

inductive Label where
  | internal
  | response (command : Command) (reply : Reply)
  deriving DecidableEq, Repr

def BusyRequest : Command → Prop
  | .append _ _ _ | .read _ _ | .summary | .pin | .publish | .acknowledge | .recover => True
  | _ => False

def StaleRequest : Command → Prop
  | .release false | .scan false | .stream false => True
  | _ => False

theorem command_stale (c : Config) (ops : Operations α) (s : Service α) (cmd : Command)
    (stale : StaleRequest cmd) : command c ops s cmd = (.invalidHandle, s) := by
  cases cmd <;> simp_all [StaleRequest]
  all_goals rename_i b
  all_goals cases b <;> simp_all [command]

/-- `start` and cut indices in these rules are mathematical witnesses, not
machine fields. The runtime has two banks, a staging bank, the target suffix,
control flags and the finite-phase/index program counter. Crash destroys the
copying constructor, so an old plan cannot continue after restart. -/
inductive MachineStep (c : Config) : Label → Machine → Machine → Prop
  | command {s cmd} : cmd ≠ .publish →
      MachineStep c (.response cmd (command c (bankOps c) s cmd).1)
        (.idle s) (.idle (command c (bankOps c) s cmd).2)
  | begin {s p} : CanPublish c s p →
      MachineStep c .internal (.idle s) (copyingAt c s p 0)
  | copy {s p count} : CanPublish c s p →
      count < (beforePublish (append c s.store.root p)).length →
      MachineStep c .internal (copyingAt c s p count) (copyingAt c s p (count + 1))
  | publish {s p} : CanPublish c s p →
      MachineStep c (.response .publish .reserved)
        (copyingAt c s p (beforePublish (append c s.store.root p)).length)
        (.idle (published c s p))
  | crash {cells target ctl pc} :
      MachineStep c (.response .crash .unavailable) (.copying cells target ctl pc)
        (.idle (crashed cells.disk))
  | busy {cells target ctl pc cmd} : BusyRequest cmd → ctl.committed = false →
      MachineStep c (.response cmd .busy) (.copying cells target ctl pc)
        (.copying cells target ctl pc)

  | fenced {cells target ctl pc cmd} : StaleRequest cmd →
      MachineStep c (.response cmd .invalidHandle) (.copying cells target ctl pc)
        (.copying cells target ctl pc)
  | view {cells target ctl pc minimum} : ctl.online = true →
      MachineStep c (.response (.view minimum) (viewReply c ctl minimum))
        (.copying cells target ctl pc) (.copying cells target ctl pc)

/-- Source internal scheduling can refuse a request while publication is in
progress. This permits backpressure; it does not alter committed history. -/
inductive GhostStep (c : Config) : Label → Service (List Bool) → Service (List Bool) → Prop
  | internal {s} : GhostStep c .internal s s
  | command {s cmd} : GhostStep c (.response cmd (command c (ghostOps c) s cmd).1)
      s (command c (ghostOps c) s cmd).2
  | pendingBusy {s cmd} : s.control.pending.isSome = true → s.control.committed = false → BusyRequest cmd →
      GhostStep c (.response cmd .busy) s s

def MachineRelated (c : Config) (m : Machine) (a : Service (List Bool)) : Prop :=
  Represents c m.disk.root a.store ∧ m.control = a.control ∧
  (∀ cells target ctl pc, m = .copying cells target ctl pc → ctl.pending.isSome = true)

theorem copyingAt_root (c : Config) (s : Service Banks) (p : Bool) (count : Nat)
    (h : count ≤ (beforePublish (append c s.store.root p)).length) :
    (copyingAt c s p count).disk.root = s.store.root := by
  dsimp [copyingAt, Machine.disk, cut]
  have eq : replacement (append c s.store.root p) =
      beforePublish (append c s.store.root p) ++ [.publish] := by
    simp [replacement, beforePublish, List.append_assoc]
  rw [eq, List.take_append_of_le_length h]
  exact before_cut_root _ _ _

theorem copyingAt_related {c : Config} {s : Service Banks} {p : Bool} {count : Nat}
    {a : Service (List Bool)} (r : RelatedService (fun d h => Represents c d.root h) s a)
    (pending : s.control.pending = some p)
    (h : count ≤ (beforePublish (append c s.store.root p)).length) :
    MachineRelated c (copyingAt c s p count) a := by
  refine ⟨by rw [copyingAt_root _ _ _ _ h]; exact r.1, r.2, ?_⟩
  intro cells target ctl pc eq
  have hc : ctl = s.control := by cases eq; rfl
  simp [hc, pending]

theorem idle_related {c : Config} {s : Service Banks} {a : Service (List Bool)}
    (r : RelatedService (fun d h => Represents c d.root h) s a) :
    MachineRelated c (.idle s) a := by
  exact ⟨r.1, r.2, by intro cells target ctl pc eq; cases eq⟩

theorem machine_step_refines {c : Config} {m n : Machine} {event : Label}
    (step : MachineStep c event m n) {a : Service (List Bool)}
    (rel : MachineRelated c m a) :
    ∃ b, GhostStep c event a b ∧ MachineRelated c n b := by
  cases step with
  | command notPublish =>
    obtain ⟨he, hr⟩ := command_refines (bank_simulates c) ⟨rel.1, rel.2.1⟩ _
    refine ⟨_, ?_, idle_related hr⟩
    rw [he]
    exact GhostStep.command
  | begin allowed =>
    exact ⟨a, .internal, copyingAt_related ⟨rel.1, rel.2.1⟩ allowed.2.1 (by omega)⟩
  | @copy s p count allowed bound =>
    have r : RelatedService (fun (d : Banks) h => Represents c d.root h) _ a :=
      ⟨by simpa only [copyingAt_root c s p count (by omega)] using rel.1, rel.2.1⟩
    exact ⟨a, .internal, copyingAt_related r allowed.2.1 (by omega)⟩
  | @publish s p allowed =>
    have r : RelatedService (fun d h => Represents c d.root h) s a :=
      ⟨by simpa only [copyingAt_root _ _ _ _ (le_refl _)] using rel.1, rel.2.1⟩
    have commandEq : command c (bankOps c) s .publish = (.reserved, published c s p) := by
      simp [command, allowed.1, allowed.2.1, allowed.2.2.1, bankOps,
        allowed.2.2.2, published]
    obtain ⟨he, hr⟩ := command_refines (bank_simulates c) r .publish
    rw [commandEq] at he hr
    dsimp only at he hr
    refine ⟨_, ?_, idle_related hr⟩
    rw [he]
    exact GhostStep.command
  | crash =>
    refine ⟨⟨a.store, { online := false }⟩, ?_, ?_⟩
    · exact GhostStep.command (cmd := .crash)
    · exact idle_related ⟨rel.1, rfl⟩
  | busy request unpublished =>
    exact ⟨a, .pendingBusy (by rw [← rel.2.1]; exact rel.2.2 _ _ _ _ rfl)
      (by rw [← rel.2.1]; exact unpublished) request, rel⟩
  | @fenced cells target ctl pc cmd stale =>
    refine ⟨a, ?_, rel⟩
    have eq := command_stale c (ghostOps c) a cmd stale
    simpa only [eq] using (GhostStep.command (c := c) (s := a) (cmd := cmd))
  | @view cells target ctl pc minimum online =>
    refine ⟨a, ?_, rel⟩
    have ctl := rel.2.1
    have onlineA : a.control.online = true := by rw [← ctl]; exact online
    simpa [command, ← rel.2.1, Machine.control, online] using (GhostStep.command (c := c) (s := a) (cmd := .view minimum))

inductive Execution {S : Type} (step : Label → S → S → Prop) : List Label → S → S → Prop
  | nil {s} : Execution step [] s s
  | cons {s t u e es} : step e s t → Execution step es t u → Execution step (e :: es) s u

theorem machine_execution_refines {c : Config} {m n : Machine} {events : List Label}
    (run : Execution (MachineStep c) events m n) {a : Service (List Bool)}
    (rel : MachineRelated c m a) :
    ∃ b, Execution (GhostStep c) events a b ∧ MachineRelated c n b := by
  induction run generalizing a with
  | nil => exact ⟨a, .nil, rel⟩
  | cons step rest ih =>
    obtain ⟨b, first, rb⟩ := machine_step_refines step rel
    obtain ⟨z, tail, rz⟩ := ih rb
    exact ⟨z, .cons first tail, rz⟩

theorem Execution.append {S : Type} {step : Label → S → S → Prop}
    {xs ys : List Label} {a b d : S} (first : Execution step xs a b)
    (last : Execution step ys b d) : Execution step (xs ++ ys) a d := by
  induction first with
  | nil => exact last
  | cons h _ ih => exact .cons h (ih last)

/-- Progress is an available finite schedule, conditional on an admitted
pending request and an interval without crashes. No fairness is assumed. -/
theorem copy_schedule {c : Config} {s : Service Banks} {p : Bool}
    (allowed : CanPublish c s p) (count : Nat)
    (bound : count ≤ (beforePublish (append c s.store.root p)).length) :
    Execution (MachineStep c) (List.replicate count .internal)
      (copyingAt c s p 0) (copyingAt c s p count) := by
  induction count with
  | zero => exact .nil
  | succ n ih =>
    have first := ih (by omega)
    have last : Execution (MachineStep c) [.internal] (copyingAt c s p n) (copyingAt c s p (n + 1)) :=
      .cons (.copy allowed (by omega)) .nil
    simpa only [List.replicate_succ'] using first.append last

theorem scheduled_publication {c : Config} {s : Service Banks} {p : Bool}
    (allowed : CanPublish c s p) :
    Execution (MachineStep c)
      (.internal :: List.replicate (beforePublish (append c s.store.root p)).length .internal ++
        [.response .publish .reserved]) (.idle s) (.idle (published c s p)) := by
  exact .cons (.begin allowed) ((copy_schedule allowed _ (le_refl _)).append
    (.cons (.publish allowed) .nil))

/-- These are counts of actual modeled write/persist/selector transitions.
A request additionally has invocation, begin and acknowledgment transitions. -/
theorem publication_work {c : Config} {s : Snapshot} {h : List Bool}
    (r : Represents c s h) (room : s.position < c.limit) (p : Bool) :
    (replacement (append c s p)).length ≤ 2 * c.window + 3 := by
  rw [replacement_work]
  have bound := (append_represents r room p).2.2.1
  omega

/-- The existing conditional preservation interface transports only properties
of the admitted source observations. Full-history membership is not an admitted
window query after expiry. -/
theorem machine_behaviors_refine {c : Config} {m : Machine} {a : Service (List Bool)}
    (rel : MachineRelated c m a) :
    Interaction.Refines (fun source target => source.1 = target.1 ∧ MachineRelated c target.2 source.2)
      { b : List Label × Service (List Bool) | Execution (GhostStep c) b.1 a b.2 }
      { b : List Label × Machine | Execution (MachineStep c) b.1 m b.2 } := by
  intro t ht
  obtain ⟨b, run, related⟩ := machine_execution_refines ht rel
  exact ⟨(t.1, b), run, rfl, related⟩

end Durability.Retention
