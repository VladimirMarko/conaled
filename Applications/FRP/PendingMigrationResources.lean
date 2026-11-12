import Applications.FRP.PendingMigrationSafety

/-! Logical retained storage and transition costs for both protocol participants.
These are scalar-cell/model-operation counts, not Lean heap benchmarks. -/
set_option autoImplicit false
set_option warningAsError true
namespace FRPSpec.PendingMigration
open Migration

/-- Admission checks the bound before allocating a slot. -/
def Bounded (s : Session) : Prop := s.order.length ≤ 2

theorem step_bounded (s : Session) (c : Command) (h : Bounded s) :
    Bounded (step s c).session := by
  cases c <;> simp only [step]
  all_goals repeat' first
    | simp_all [Bounded, reject, update, enqueue, dispatch, List.length_tail]
    | split
    | omega

theorem execute_bounded (s : Session) (cs : List Command) (h : Bounded s) :
    Bounded (execute s cs).1 := by
  induction cs generalizing s with
  | nil => exact h
  | cons c cs ih => exact ih _ (step_bounded s c h)

theorem state_slots_bound (s : Session) (h : Bounded s) : stateSlots s ≤ 138 := by
  have ha := Migration.backend_cells s.active
  have hq := s.queue.bounded
  have hp : (s.prepared.map (fun p => p.target.cells)).getD 0 ≤ 2 := by
    cases s.prepared with
    | none => simp
    | some p => exact Migration.backend_cells p.target
  unfold stateSlots Bounded at *
  omega

theorem preparation_slots_bound (s : Session) (h : Bounded s) (k : Kind) :
    preparationSlots s k ≤ 142 := by
  have hs := state_slots_bound s h
  have hk := Migration.backend_cells (realize k s.active.logical)
  unfold preparationSlots
  omega

/-- The largest transient branch is evaluation (46 arena cells plus eight
result/request cells). Later command-specific witnesses include queue copies. -/
def peakSlots (s : Session) : Nat := stateSlots s + 54

theorem peak_slots_bound (s : Session) (h : Bounded s) : peakSlots s ≤ 192 := by
  have hs := state_slots_bound s h
  unfold peakSlots
  omega

/-- Charge the executed branch: denied evaluation has no Circuit work;
queue admission/response construction charges its bounded scan/copy; release
charges the full retirement scan even when refused. A unit includes tag/control
observation; the framing reservation is in stateSlots. -/
def commandWork (s : Session) (c : Command) : Nat :=
  let status := (step s c).status
  1 + match c with
  | .accept _ => s.order.length + (if status == .accepted then s.order.length + 3 else 0)
  | .evaluate => if status == .evaluated then Migration.tickWork s.active + 2 else 1
  | .publish | .retry _ | .queryPeer => s.queue.messages.length * 2 + 2
  | .dispatch _ => if s.queue.messages.isEmpty then 0 else 5 + s.queue.messages.length * 2
  | .release => s.queue.messages.length + 4
  | .prepare k _ _ _ =>
      if status == .prepared || status == .validationFailure then 5 + conversionWork k
      else if status == .allocationFailure then 2 else if status == .resourceFailure then 1 else 0
  | .tickCommit => if status == .committed then 2 + conversionWork s.active.kind else 1
  | .cancelWork _ => 3
  | .ownershipCommit => 2
  | .cancelMigration => if s.prepared.isSome then 1 else 0
  | .close | .inspect => 1

theorem conversion_bound (k : Kind) : conversionWork k ≤ 2 := by cases k <;> decide

theorem command_work_bound (s : Session) (c : Command) (h : Bounded s) :
    commandWork s c ≤ 14 := by
  have hq := s.queue.bounded
  have ht := (Migration.tick_bounds s.active).1
  have hk := conversion_bound s.active.kind
  unfold Bounded at h
  cases c <;> simp only [commandWork]
  all_goals repeat' first | split | omega
  all_goals have := conversion_bound ‹Kind›; omega

/-- Cost follows actual state transitions and includes refused commands. No
lifetime counter is added to the executable state. -/
def scheduleWork : Session → List Command → Nat
  | _,[] => 0
  | s,c::cs => commandWork s c + scheduleWork (step s c).session cs

theorem schedule_work_bound (s : Session) (cs : List Command) (h : Bounded s) :
    scheduleWork s cs ≤ 14 * cs.length := by
  induction cs generalizing s with
  | nil => simp [scheduleWork]
  | cons c cs ih =>
    have one := command_work_bound s c h
    have rest := ih _ (step_bounded s c h)
    simp only [scheduleWork, List.length_cons]
    omega

/-- Persistent queue append can coexist with the old list. Count the complete
new queue (at most four five-cell entries), new request/ledger records, and
admission-order copy separately from retained state. Fixed storage includes the
six-entry transfer-event observation buffer (18 cells), command and reply frames. -/
def temporarySlots (s : Session) (c : Command) : Nat :=
  match c with
  | .evaluate => if (step s c).status == .evaluated then Migration.tickArena s.active + 8 else 0
  | .dispatch _ => 5 * s.queue.messages.length + 8
  | .publish | .retry _ | .queryPeer => 5 * (min 4 (s.queue.messages.length + 1))
  | .accept _ => if (step s c).status == .accepted then s.order.length + 9 else 0
  | .prepare k _ _ _ => (realize k s.active.logical).cells + 2
  | .tickCommit => 7
  | .cancelWork _ | .close | .release => 8
  | _ => 0

def commandPeak (s : Session) (c : Command) : Nat := stateSlots s + temporarySlots s c

theorem temporary_slots_bound (s : Session) (c : Command) (h : Bounded s) :
    temporarySlots s c ≤ 54 := by
  have hq := s.queue.bounded
  have ht := (Migration.tick_bounds s.active).2
  unfold Bounded at h
  cases c <;> simp only [temporarySlots]
  all_goals repeat' first | split | omega
  all_goals have := Migration.backend_cells (realize ‹Kind› s.active.logical); omega

theorem command_peak_bound (s : Session) (c : Command) (h : Bounded s) :
    commandPeak s c ≤ 192 := by
  have := state_slots_bound s h
  have := temporary_slots_bound s c h
  unfold commandPeak
  omega

/-- Both variable-width numeric fields are bounded by admission. Framing never
retains a growing identifier or input line. -/
theorem query_frame_bound (s : Session) (h : Bounded s) : (queryText s).length ≤ 12 := by
  have ho : s.order.length ≤ 2 := h
  have hq := s.queue.bounded
  generalize hn : s.order.length = n at *
  generalize hm : s.queue.messages.length = m at *
  unfold queryText
  rw [hn,hm]
  interval_cases n <;> interval_cases m <;>
    cases s.active.kind <;> cases s.active.logical <;> decide

theorem status_frame_bound (status : Status) : ("C:" ++ statusText status ++ "\n").length ≤ 21 := by
  cases status <;> decide

theorem business_frame_bound (value : Bool) : ("B:" ++ Migration.bitText value ++ "\n").length = 4 := by
  cases value <;> decide

/-- Live-cell execution of the actual transfer trace. Release admissibility is
proved separately, so truncated subtraction cannot disguise an over-release. -/
def liveAfter : Nat → List TransferEvent → Nat
  | live,[] => live
  | live,.allocate cells :: rest => liveAfter (live + cells) rest
  | live,.release cells :: rest => liveAfter (live - cells) rest
  | live,_ :: rest => liveAfter live rest

def ReleasesSafe : Nat → List TransferEvent → Prop
  | _,[] => True
  | live,.allocate cells :: rest => ReleasesSafe (live + cells) rest
  | live,.release cells :: rest => cells ≤ live ∧ ReleasesSafe (live - cells) rest
  | live,_ :: rest => ReleasesSafe live rest

def transferPeak : Nat → List TransferEvent → Nat
  | live,[] => live
  | live,.allocate cells :: rest => max live (transferPeak (live + cells) rest)
  | live,.release cells :: rest => max live (transferPeak (live - cells) rest)
  | live,_ :: rest => transferPeak live rest

/-- Preparation events are emitted by the executed branch. Allocation refusal
has no successful allocation; validation failure has an allocation and release. -/
theorem prepare_success_trace (s : Session) (k : Kind) (budget : Nat)
    (hp : s.prepared = none) (hb : preparationSlots s k ≤ budget) :
    (step s (.prepare k budget true true)).transfer =
      [.budget,.attempt ((realize k s.active.logical).cells + 2),
       .allocate ((realize k s.active.logical).cells + 2),
       .copy (realize k s.active.logical).cells,.validate,.release 2] := by
  simp [step, hp, Nat.not_lt.mpr hb, Migration.backend_validates]

theorem prepare_failure_trace (s : Session) (k : Kind) (budget : Nat)
    (hp : s.prepared = none) (hb : preparationSlots s k ≤ budget) :
    (step s (.prepare k budget true false)).transfer =
      [.budget,.attempt ((realize k s.active.logical).cells + 2),
       .allocate ((realize k s.active.logical).cells + 2),
       .copy (realize k s.active.logical).cells,.validate,
       .release ((realize k s.active.logical).cells + 2)] := by
  simp [step, hp, Nat.not_lt.mpr hb, Migration.backend_validates]

theorem successful_preparation_lifetime (s : Session) (k : Kind) (budget : Nat)
    (hp : s.prepared = none) (hb : preparationSlots s k ≤ budget) :
    let trace := (step s (.prepare k budget true true)).transfer
    ReleasesSafe (stateSlots s) trace ∧
      liveAfter (stateSlots s) trace = stateSlots s + (realize k s.active.logical).cells ∧
      transferPeak (stateSlots s) trace = preparationSlots s k := by
  rw [prepare_success_trace s k budget hp hb]
  dsimp only
  simp only [ReleasesSafe, liveAfter, transferPeak, preparationSlots, and_true]
  omega

/-- The interpreted allocation trace ends at the storage actually retained by
the next session, including the still-authoritative old backend. -/
theorem preparation_retained (s : Session) (k : Kind) (budget : Nat)
    (hp : s.prepared = none) (hb : preparationSlots s k ≤ budget) :
    let o := step s (.prepare k budget true true)
    liveAfter (stateSlots s) o.transfer = stateSlots o.session := by
  let p : Prepared s.active := ⟨realize k s.active.logical,realize_logical _ _⟩
  have ho : step s (.prepare k budget true true) =
      ⟨{s with prepared := some p},.prepared,none,none,none,
        [.budget,.attempt (p.target.cells+2),.allocate (p.target.cells+2),
         .copy p.target.cells,.validate,.release 2]⟩ := by
    simp [step,hp,Nat.not_lt.mpr hb,p,Migration.backend_validates]
  rw [ho]
  simp [liveAfter,stateSlots,hp,p]
  omega

theorem failed_preparation_lifetime (s : Session) (k : Kind) (budget : Nat)
    (hp : s.prepared = none) (hb : preparationSlots s k ≤ budget) :
    let trace := (step s (.prepare k budget true false)).transfer
    ReleasesSafe (stateSlots s) trace ∧ liveAfter (stateSlots s) trace = stateSlots s ∧
      transferPeak (stateSlots s) trace = preparationSlots s k := by
  rw [prepare_failure_trace s k budget hp hb]
  dsimp only
  simp only [ReleasesSafe, liveAfter, transferPeak, preparationSlots, and_true]
  omega

theorem ownership_cut_lifetime (s : Session) (p : Prepared s.active)
    (hp : s.prepared = some p) :
    let o := step s .ownershipCommit
    ReleasesSafe (stateSlots s) o.transfer ∧
      liveAfter (stateSlots s) o.transfer = stateSlots o.session := by
  have cut : step s .ownershipCommit =
      ⟨⟨p.target,s.requests,s.peer,s.order,s.queue,none⟩,.migrated,none,none,none,
        [.ownershipCut,.release s.active.cells]⟩ := by
    unfold step
    rw [hp]
  rw [cut]
  simp only [ReleasesSafe, liveAfter, stateSlots, hp, Option.map_some, Option.getD_some,
    Option.map_none, Option.getD_none, and_true]
  omega

theorem migration_cancel_lifetime (s : Session) (p : Prepared s.active)
    (hp : s.prepared = some p) :
    let o := step s .cancelMigration
    ReleasesSafe (stateSlots s) o.transfer ∧
      liveAfter (stateSlots s) o.transfer = stateSlots o.session := by
  simp only [step, hp, Option.map_some, Option.getD_some]
  simp only [ReleasesSafe, liveAfter, stateSlots, hp, Option.map_some, Option.getD_some,
    Option.map_none, Option.getD_none, and_true]
  omega

/-- Explicit environmental waits are supplied by callers, never inferred from
atomic local transitions. This permits unbounded waits when no bound is given. -/
def pause (admission scheduler publication confirmation retirement : Nat)
    (s : Session) (cs : List Command) : Nat :=
  admission + scheduler + publication + confirmation + retirement + scheduleWork s cs

theorem pause_schedule (a w p c r : Nat) (s : Session) (cs : List Command) :
    pause a w p c r s cs = a + w + p + c + r + scheduleWork s cs := rfl

theorem pause_bound (a w p c r : Nat) (s : Session) (cs : List Command) (hs : Bounded s) :
    pause a w p c r s cs ≤ a + w + p + c + r + 14 * cs.length := by
  have := schedule_work_bound s cs hs
  unfold pause
  omega

end FRPSpec.PendingMigration
