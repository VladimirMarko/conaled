import Applications.FRP.MigrationIO

/-! Logical protocol storage and costs; host allocation and scheduling are separate. -/
set_option autoImplicit false
set_option warningAsError true
namespace FRPSpec.Migration

def flightSlots {b : Backend} : Flight b → Nat
  | .idle => 0
  | .accepted _ => 1
  | .pending _ r | .published _ r => 1 + r.candidate.cells + 1

def preparedSlots {b : Backend} : Option (Prepared b) → Nat
  | none => 0
  | some p => p.target.cells

/-- The last-value slot is reserved even before first publication. Fixed slots
cover control, a one-byte input frame and bounded response/workspace buffers. -/
def stateSlots (s : Session) : Nat :=
  fixedSlots + s.active.cells + 1 + flightSlots s.flight + preparedSlots s.prepared

theorem backend_cells (b : Backend) : b.cells ≤ 2 := by cases b <;> simp [Backend.cells]

theorem flight_slots {b : Backend} (f : Flight b) : flightSlots f ≤ 4 := by
  cases f <;> simp only [flightSlots]
  · omega
  · omega
  · have := backend_cells ‹TickResult b _›.candidate; omega
  · have := backend_cells ‹TickResult b _›.candidate; omega

theorem prepared_slots {b : Backend} (p : Option (Prepared b)) : preparedSlots p ≤ 2 := by
  cases p with
  | none => simp [preparedSlots]
  | some p => exact backend_cells p.target

/-- Even manually constructed combinations fit this bound; reachable phases do
not simultaneously retain a tick candidate and a migration preparation. -/
theorem state_slots_bound (s : Session) : stateSlots s ≤ 89 := by
  have := backend_cells s.active
  have := flight_slots s.flight
  have := prepared_slots s.prepared
  unfold stateSlots fixedSlots
  omega

theorem preparation_slots_bound (s : Session) (k : Kind) : preparationSlots s k ≤ 87 := by
  have := backend_cells s.active
  have := backend_cells (realize k s.active.logical)
  unfold preparationSlots fixedSlots
  omega

/-- Allocation refusal models releasing a reserved target; it does not catch
arbitrary host allocation exceptions. Budget checking includes that transient. -/
theorem admitted_preparation_fits (s : Session) (budget : Nat) (a v : Bool)
    (h : (step s (.prepare budget a v)).status = .prepared) :
    stateSlots (step s (.prepare budget a v)).session + 2 ≤ budget := by
  rcases s with ⟨active,flight,last,request,prepared⟩
  cases flight <;> cases request <;> cases prepared <;> simp only [step, reject] at h ⊢
  all_goals try split_ifs at h ⊢
  all_goals simp_all [stateSlots, flightSlots, preparedSlots, preparationSlots]

/-- Body counts are taken from the actual selected Circuit syntax. -/
def tickWork (b : Backend) : Nat := match b with
  | .delay _ => Indefinite.delay.body.work
  | .redundant _ => MigrationPair.redundant.body.work

def tickArena (b : Backend) : Nat := match b with
  | .delay _ => Indefinite.delay.body.arena
  | .redundant _ => MigrationPair.redundant.body.arena

theorem tick_bounds (b : Backend) : tickWork b ≤ 9 ∧ tickArena b ≤ 46 := by
  cases b with
  | delay _ => change 3 ≤ 9 ∧ 13 ≤ 46; decide
  | redundant _ => change 9 ≤ 9 ∧ 46 ≤ 46; decide

/-- Conservative simultaneous protocol state, actual evaluation arena, and a
conversion temporary. No physical-heap or allocator accounting is implied. -/
def peakSlots (s : Session) : Nat := stateSlots s + tickArena s.active + 2

theorem peak_slots_bound (s : Session) : peakSlots s ≤ 137 := by
  have := state_slots_bound s
  have := (tick_bounds s.active).2
  unfold peakSlots
  omega

/-- Protocol operation units: one dispatch/control observation; validation one;
conversion complement+pair two or projection one; reserve/release/commit one.
The Circuit cost is independently included for an evaluation command. -/
def commandWork (s : Session) : Command → Nat
  | .evaluate _ => 1 + tickWork s.active
  | .prepare _ _ _ => 1 + 1 + 1 + (s.request.map conversionWork).getD 0 + 1
  | _ => 1

theorem command_work_bound (s : Session) (c : Command) : commandWork s c ≤ 10 := by
  cases c <;> simp only [commandWork]
  all_goals try omega
  · have := (tick_bounds s.active).1; omega
  · cases s.request with
    | none => decide
    | some k => cases k <;> decide

/-- Finite waiting assumptions are explicit. There is no deadline without them.
This bounds the chosen drain/prepare/commit schedule, not an arbitrary scheduler. -/
def pause (admissionWait schedulerWait sinkWait : Nat) (s : Session) (target : Kind) : Nat :=
  admissionWait + schedulerWait + tickWork s.active + sinkWait + 2 +
    (4 + conversionWork target) + 1

theorem pause_bound (s : Session) (target : Kind) (a w sink A W S : Nat)
    (ha : a ≤ A) (hw : w ≤ W) (hs : sink ≤ S) :
    pause a w sink s target ≤ A + W + S + 18 := by
  have := (tick_bounds s.active).1
  cases target <;> simp only [pause, conversionWork] <;> omega

theorem status_frame_bound (s : Status) : ("C:" ++ statusText s ++ "\n").length ≤ 32 := by
  cases s <;> decide

theorem bit_text_length (b : Bool) : (bitText b).length = 1 := by cases b <;> rfl
theorem kind_text_length (k : Kind) : (kindText k).length = 1 := by cases k <;> rfl

theorem query_frame_bound (s : Session) : (queryText s).length ≤ 32 := by
  rcases s with ⟨active,flight,last,request,prepared⟩
  cases flight <;> cases last <;> cases request <;> cases prepared <;>
    simp [queryText, phaseText, bit_text_length, kind_text_length] <;> decide

end FRPSpec.Migration
