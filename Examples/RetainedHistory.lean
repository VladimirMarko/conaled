import Applications.Durability.RetentionClients
import Applications.Durability.RetentionSummary
import Applications.Durability.DiagnosticGraph

/-! Checked retained-history cases. Expected lists and parity bits are computed
from the stated Boolean histories, independently of the bank layout. -/
namespace RetainedHistoryExamples
open Durability.Retention

def config : Config := ⟨7, 2, 3, by decide, by decide⟩
def wide : Config := ⟨7, 3, 3, by decide, by decide⟩
def start : Service Banks := ⟨initialBanks, {}⟩

def commit (id : Nat) (p : Bool) : List Command := [.append 7 id p, .publish, .acknowledge]
def historyCommands : List Command := commit 0 true ++ commit 1 false ++ commit 2 true

def run (commands : List Command) : List Reply × Service Banks :=
  execute config (bankOps config) start commands

def full : Service Banks := (run historyCommands).2

theorem full_refinement : RelatedService (fun d h => Represents config d.root h)
    full (execute config (ghostOps config) ⟨[], {}⟩ historyCommands).2 :=
  (execute_refines (bank_simulates config) (t := start) (a := ⟨[], {}⟩) ⟨represents_empty config, rfl⟩ historyCommands).2

theorem full_represents : Represents config full.store.root [true, false, true] := by
  exact full_refinement.1

example : full.store.root.lower = 1 ∧ full.store.root.items = [false, true] := by decide
example : read full.store.root 1 3 = .records [false, true] := by
  rw [read_refines full_represents]; decide
example : read full.store.root 0 1 = .expired 1 := by decide
example : read full.store.root 0 0 = .expired 1 := by decide
example : read full.store.root 2 1 = .invalidRange := by decide
example : full.store.root.total = false := full_represents.total
example : parity full.store.root.items = true := by decide
example : classify config full.store.root 7 0 true = .expired 1 ∧
    classify config full.store.root 7 0 false = .expired 1 := by decide
example : classify config full.store.root 7 1 false = .acknowledged 7 1 ∧
    classify config full.store.root 7 1 true = .conflict := by decide
example : classify config full.store.root 7 3 false = .exhausted ∧
    classify config full.store.root 7 2 true = .acknowledged 7 2 := by decide
example : classify config full.store.root 9 100 false = .wrongIncarnation ∧
    classify config full.store.root 7 4 false = .invalidID := by decide
example : classify config empty 7 1 true = .outOfOrder 0 := by decide

/-- The theorem preserves multiplicity and order, not merely length/parity. -/
def duplicates := append wide (append wide (append wide empty true) true) false
example : range duplicates 0 3 = [true, true, false] := by decide
example : parity [true,false] = parity [false,true] ∧ [true,false] ≠ [false,true] := by decide

/-- Two retained retry contracts disagree despite identical summary-only state. -/
def summaryA : SummaryStore := ((⟨0,false,none⟩ : SummaryStore).append true |>.append false).append true
def summaryB : SummaryStore := ((⟨0,false,none⟩ : SummaryStore).append false |>.append true).append true
example : summaryA = summaryB := by decide
example : classify config (append config (append config (append config empty false) true) true) 7 1 true =
    .acknowledged 7 1 ∧ classify config full.store.root 7 1 true = .conflict := by decide

example (commands : List SummaryCommand) :
    (summaryExecute config ⟨⟨0,false,none⟩, {}⟩ commands).1 =
    (execute (singleWindow config) (bankOps (singleWindow config)) start
      (commands.map SummaryCommand.command)).1 := by
  apply summary_window_trace config _ _ ⟨[], {}⟩
  · exact ⟨represents_empty _, rfl⟩
  · exact ⟨represents_empty _, rfl⟩

/-- Pinning the boundary prevents the append that would expire it. -/
def two : Service Banks := (run (commit 0 true ++ commit 1 false)).2
def pinned : Service Banks := (command config (bankOps config) two .pin).2
example : command config (bankOps config) pinned (.append 7 2 true) = (.busy, pinned) :=
  pinned_append_busy rfl rfl 7 2 true
example : command config (bankOps config) pinned .pin = (.busy, pinned) := second_pin_busy rfl rfl
example : (command config (bankOps config) pinned (.stream true)).1 = .records [true] := by decide
example : (execute config (bankOps config) pinned [.stream true, .stream true]).1 =
    [.records [true], .busy] := by decide
example : (execute config (bankOps config) pinned
    [.stream true, .consume, .stream true, .consume, .stream true]).1 =
    [.records [true], .released, .records [false], .released, .released] := by decide

/-- Reacquisition at the same position is permitted; alias replay is not. -/
def reacquired : Service Banks :=
  (execute config (bankOps config) two [.pin, .release true, .pin]).2
example : reacquired.store.root.position = 2 ∧ reacquired.control.pinned = true := by decide
example : (command config (bankOps config) reacquired (.release true)).2.control.pinned = false :=
  raw_release_clears_new_pin rfl rfl

def oldHandle : Handle := ⟨5, 10⟩
def owner : Ownership := ⟨5, some 10, ∅⟩
example : ¬({ owner with owner := some 11, consumed := insert 10 owner.consumed } : Ownership).admits oldHandle :=
  reacquired_excludes_old owner oldHandle 11
example : ({ owner with owner := some 11, consumed := insert 10 owner.consumed } : Ownership).admits ⟨5,11⟩ := by
  simp [Ownership.admits, owner]
example : command config (bankOps config) reacquired
    (.release (currentConnection ⟨6, some 11, ∅⟩ oldHandle)) = (.invalidHandle, reacquired) := rfl

/-- A completed delayed view keeps its old position after another commit. -/
def delayed : Service Banks :=
  (run (commit 0 true ++ [.pin, .scan true, .scan true] ++ commit 1 false)).2
example : delayed.control.delayed = some (1,true) ∧ delayed.store.root.position = 2 := by decide
example : command config (bankOps config) delayed (.view 2) = (.notReady, delayed) :=
  delayed_minimum rfl rfl (by decide)
example : (command config (bankOps config) delayed (.view 1)).1 = .summary 7 1 true := by decide
example : (command config (bankOps config) delayed .summary).1 = .summary 7 2 true := by decide

/-- Every cut in the final replacement is checked against the full-history
relation, not only the cuts shown concretely below. -/
theorem all_crash_cuts (n : Nat) :
    Represents config (cut two.store (append config two.store.root true) n).disk.root [true,false] ∨
    Represents config (cut two.store (append config two.store.root true) n).disk.root [true,false,true] := by
  apply crash_cut_refines
  · exact (execute_refines (bank_simulates config) (t := start) (a := ⟨[], {}⟩) ⟨represents_empty config, rfl⟩
      (commit 0 true ++ commit 1 false)).2.1
  · decide

def crashBefore : Service Banks := crashed (cut two.store (append config two.store.root true) 6).disk
def crashAfter : Service Banks := crashed (cut two.store (append config two.store.root true) 7).disk
def recover : List Command := [.recover, .recover, .recover]
example : (execute config (bankOps config) crashBefore (recover ++ [.append 7 2 true])).1 =
    [.unavailable, .unavailable, .summary 7 2 true, .reserved] := by decide
example : (execute config (bankOps config) crashAfter (recover ++ [.append 7 2 true])).1 =
    [.unavailable, .unavailable, .summary 7 3 false, .acknowledged 7 2] := by decide
example : (execute config (bankOps config) crashAfter
    ([.recover, .crash] ++ recover ++ [.append 7 2 true])).1 =
    [.unavailable, .unavailable, .unavailable, .unavailable, .summary 7 3 false,
      .acknowledged 7 2] := by decide
example : (execute config (bankOps config) pinned [.scan true, .crash]).2.control.delayed = none := by decide
example : (command config (bankOps config) crashAfter (.release false)).1 = .invalidHandle := by decide

/-- Logical deletion cannot preserve cumulative graph admission. This reuses
its existing concrete closure implementation, rather than changing its API. -/
def forward : Durability.Record (Durability.Diagnostic.Edge 2) := ⟨7,0,(0,1)⟩
def reverse : Durability.Record (Durability.Diagnostic.Edge 2) := ⟨7,1,(1,0)⟩
example : Durability.Diagnostic.allows [forward] reverse = false ∧
    Durability.Diagnostic.allows [] reverse = true := by decide

example (commands : List SummaryCommand) :
    (summaryDiskExecute config ⟨⟨fun _ => ⟨0,false,none⟩, false⟩, {}⟩ commands).1 =
    (execute (singleWindow config) (bankOps (singleWindow config)) start
      (commands.map SummaryCommand.command)).1 := by
  apply summary_disk_window_trace config _ _ ⟨[], {}⟩
  · exact ⟨represents_empty _, rfl⟩
  · exact ⟨represents_empty _, rfl⟩

/-- The physical address type has exactly two banks, each reserving W slots.
The general theorem covers all reachable interrupted executions. -/
example {m : Machine} {events : List Label} (steps : Execution (MachineStep config) events initialMachine m) :
    (m.disk.cells false).items.length + (m.disk.cells true).items.length ≤ 4 ∧
    volatileRecords m ≤ 7 := reachable_bounds steps
example : (replacement full.store.root).length = 7 := replacement_work _

end RetainedHistoryExamples
