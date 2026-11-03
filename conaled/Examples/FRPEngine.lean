import Applications.FRP.Engine
import Examples.FRPDemand
import Examples.TemporalFRP

/-! Concrete packet scripts for the incremental one-shot engine. Expected answers
come from ordered fragments and closed windows, independently of the runner. -/
namespace Examples.FRPEngine
open FRPSpec.Frontier FRPSpec.Frontier.Trace
open FRPSpec.Frontier.Engine
open Examples.FRPTrace

abbrev C := Command ℚ Nat

def leftPacket : Message ℚ Nat := ⟨3, [(2, [3,4]), (2, [3])]⟩
def rightPacket : Message ℚ Nat := ⟨3, []⟩
def rejected : Message ℚ Nat := ⟨4, [(2, [9])]⟩

/-- Every command supplies its own payload; no future stream is an input. -/
def script : List C :=
  [.register 2, .process, .source .left leftPacket, .source .right rightPacket, .process]

theorem script_events : (Engine.run (init start) script).2 =
    [none, none, none, none, some (2, [3,4,3])] := by decide

#eval (Engine.run (init start) script).2

def packetsFirst : List C :=
  [.source .right rightPacket, .source .left leftPacket, .register 2, .process]

example : (Engine.run (init start) packetsFirst).2 =
    [none, none, none, some (2, [3,4,3])] := by decide

/-- Strict crossing, not equality, is needed on the silent source too. -/
example : (Engine.run (init start)
    [.register 2, .source .left leftPacket, .source .right ⟨2, []⟩,
      .process, .source .right rightPacket, .process]).2 =
    [none, none, none, none, none, some (2, [3,4,3])] := by decide

example : (Engine.run (init start)
    [.register 1, .process, .process, .register 2, .process]).2 =
    [none, some (1, []), none, none, none] := by decide

/-- Both duplicate registrations leave the original one-shot protocol intact. -/
example : (Engine.run (init start)
    [.register 2, .register 1, .source .left leftPacket, .source .right rightPacket,
      .process, .register 1, .process]).2 =
    [none, none, none, none, some (2, [3,4,3]), none, none] := by decide

/-- A rejected late packet cannot clear pending work or manufacture a response. -/
example : (Engine.run (init start)
    [.register 2, .source .left leftPacket, .source .left rejected]).1.request = .pending 2 := by
  decide
example : (Engine.run (init start)
    [.register 2, .source .left leftPacket, .source .left rejected,
      .source .right rightPacket, .process, .source .left rejected, .process]).2 =
    [none, none, none, none, some (2, [3,4,3]), none, none] := by decide

example : (step (init start) (.idle : C)).2 = none := rfl

example : (step (Engine.run (init start)
    [.register 2, .source .left leftPacket]).1 (.source .left rejected)).1 =
    (Engine.run (init start) [.register 2, .source .left leftPacket]).1 := by decide

example : (step (Engine.run (init start) script).1 (.source .left rejected)).1 =
    (Engine.run (init start) script).1 := by decide

/-- This literal script consumes the rejected second left packet at position 6. -/
def referenceScript : List C :=
  [.register 2, .source .left leftPacket, .process, .register 3,
    .source .right rightPacket, .process, .source .left rejected, .process]

theorem referenceScript_corresponds : Corresponds packets FRPDemand.early 0 referenceScript := by
  unfold referenceScript
  simp only [Corresponds]
  decide

/-- All eight event positions agree, not just the nonempty response list. -/
example : Engine.run (init start) referenceScript =
    (reference start packets FRPDemand.early 8,
      referenceEvents start packets FRPDemand.early 0 8) :=
  run_refines start packets FRPDemand.early referenceScript 0 referenceScript_corresponds

example : (Engine.run (init start) referenceScript).2 =
    [none, none, none, none, none, some (2, [3,4,3]), none, none] := by decide

/-- A second literal command order, with processing continuing indefinitely. -/
def lateCommands : Nat → C
  | 0 => .source .right rightPacket
  | 1 => .source .left leftPacket
  | 2 => .register 2
  | _ => .process

theorem late_aligned : Aligned packets FRPDemand.late lateCommands := by
  intro n
  cases n with
  | zero => rfl
  | succ n =>
    cases n with
    | zero => rfl
    | succ n => cases n <;> rfl

theorem late_answer : emission (init start) lateCommands 3 = some (2, [3,4,3]) := by decide

theorem late_fair : Engine.ProcessingFair (init start) lateCommands := by
  intro n t _ _
  refine ⟨max n 3, Nat.le_max_left _ _, ?_⟩
  have h := Nat.le_max_right n 3
  match he : max n 3 with
  | 0 | 1 | 2 => omega
  | k + 3 => rfl

/-- Actual commands, legal source availability and enabled processing discharge
all assumptions of the transferred eventual-delivery theorem. -/
example : ∃ n out, 3 ≤ n ∧ emission (init start) lateCommands n = some (2, out) := by
  apply Engine.eventual_response start packets FRPDemand.late lateCommands late_aligned
    FRPDemand.available FRPDemand.available_fair late_fair 2 3
  · decide
  · intro source
    refine ⟨1, 0, le_rfl, ?_⟩
    cases source <;> decide

/-- Arbitrary legal source interleavings and different registration positions
inherit the same answer through the public agreement theorem. -/
example {x y : List Nat}
    (hx : emission (init start) (commandAt packets FRPDemand.early) 5 = some (2, x))
    (hy : emission (init start) lateCommands 3 = some (2, y)) : x = y :=
  Engine.registration_order_agrees start packets FRPDemand.early _ (fun _ => rfl)
    FRPDemand.late lateCommands late_aligned 5 3 hx hy

example (left right : ℚ → List Nat)
    (hl : ((state (init start) lateCommands 3).sources .left).Completes left)
    (hr : ((state (init start) lateCommands 3).sources .right).Completes right) :
    [3,4,3] = left 2 ++ right 2 :=
  Engine.response_sound start packets FRPDemand.late lateCommands late_aligned 3 late_answer
    left right hl hr

example : [3,4,3] = truth .left 2 ++ truth .right 2 :=
  Engine.response_honest start packets FRPDemand.late lateCommands late_aligned truth
    Examples.TemporalFRP.honest 3 late_answer

example (n : Nat) (hn : 3 < n) : emission (init start) lateCommands n = none :=
  Engine.at_most_once start packets FRPDemand.late lateCommands late_aligned hn late_answer

example (n : Nat) {t : ℚ} {out : List Nat}
    (h : emission (init start) lateCommands n = some (t, out)) :
    ∃ k, k < n ∧ lateCommands k = .register t :=
  response_registered start packets FRPDemand.late lateCommands late_aligned n h

example (n : Nat) (hn : 3 ≤ n) :
    (state (init start) lateCommands n).request = .pending 2 ∨
      ∃ k out, 3 ≤ k ∧ k < n ∧ emission (init start) lateCommands k = some (2, out) :=
  Engine.pending_or_emitted start packets FRPDemand.late lateCommands late_aligned hn (by decide)

example : (Engine.run (init start) script).1.Valid :=
  Engine.run_valid (init_valid (by intro r; simp [start, initial, State.Valid])) script

example : (initial (2 : ℚ) : State ℚ Nat).Completes (fun _ => []) :=
  initial_completes 2 _ (by intros; rfl)

/-- Validation does not certify an arbitrary external truth before initialization. -/
example : ¬ (initial (2 : ℚ) : State ℚ Nat).Completes (fun _ => [9]) := by
  intro h
  have := h 1 (by decide)
  simp [initial, batch] at this

/-- Even closing source packets do not compensate for an unscheduled consumer. -/
example : ¬ Engine.ProcessingFair (init start) (commandAt packets FRPDemand.starved) := by
  intro h
  have hp := processing_fair_refines start packets FRPDemand.starved _ (fun _ => rfl) h
  obtain ⟨m, _, hm⟩ := hp 3 2 (by decide) ⟨[3,4,3], by decide⟩
  exact FRPDemand.starved_no_process m hm

example (n : Nat) : emission (init start) (commandAt packets FRPDemand.starved) n = none := by
  rw [emission_refines start packets FRPDemand.starved _ (fun _ => rfl)]
  unfold Demand.response Demand.emit
  split <;> try rfl
  exact (FRPDemand.starved_no_process n (by assumption)).elim

/-- Fair processing cannot make a stalled source cross the requested frontier. -/
example : ¬ (∀ source, ∃ k n, k ≤ FRPDemand.available.available source n ∧
    (2 : ℚ) < (sourcePrefix (start source) (stalled source) k).frontier) := by
  intro h
  obtain ⟨k, _, _, hk⟩ := h .left
  simp [stalled_prefix, initial] at hk

def stalledCommands : Nat → C
  | 0 => .source .right ⟨2, []⟩
  | 1 => .source .left ⟨2, []⟩
  | 2 => .register 2
  | _ => .process

theorem stalled_aligned : Aligned stalled FRPDemand.late stalledCommands := by
  intro n
  cases n with
  | zero => rfl
  | succ n =>
    cases n with
    | zero => rfl
    | succ n => cases n <;> rfl

example : Engine.ProcessingFair (init start) stalledCommands := by
  intro n t _ _
  refine ⟨max n 3, Nat.le_max_left _ _, ?_⟩
  have h := Nat.le_max_right n 3
  match he : max n 3 with
  | 0 | 1 | 2 => omega
  | k + 3 => rfl

example (n : Nat) : emission (init start) stalledCommands n = none := by
  rw [emission_refines start stalled FRPDemand.late stalledCommands stalled_aligned]
  unfold Demand.response Demand.emit
  split <;> try rfl
  rename_i t ha hq
  have ht : t = 2 := by
    obtain ⟨k, _, hk⟩ := Demand.pending_registered start stalled FRPDemand.late hq
    cases k with
    | zero => simp [FRPDemand.late] at hk
    | succ k =>
      cases k with
      | zero => simp [FRPDemand.late] at hk
      | succ k => cases k <;> simp_all [FRPDemand.late]
  subst t
  simp [observe, Trace.run, stalled_prefix, observeMerge, initial]

end Examples.FRPEngine
