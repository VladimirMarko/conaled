import Applications.FRP.PendingRetention.Invariant
import Applications.FRP.PendingRetention.Staging

namespace FRPSpec.PendingRetention
open PendingCrash PendingMigration
set_option autoImplicit false

/-- The retained controller stores only authentic messages and a checked
retirement prefix. These obligations concern the actual executor state. -/
def ControlSafe (s : System) (history : Peer) : Prop :=
  PendingMessagesSafe s history ∧ ScanSafe s ∧ RetirementSafe s

theorem LocalCommand.authentic (history : Peer) (command : LocalCommand) :
    CommandAuthentic history command.frameCommand := by
  cases command <;> trivial

set_option maxHeartbeats 1600000 in
theorem control_nonprogress (cfg : Config) (s : System) (command : Command)
    (history : Peer) (ordinary : command ≠ .progress)
    (relation : RetainedRelation s.localBank.selected s.peer.selected history)
    (queues : QueuesSafe s history) (safe : ControlSafe s history) :
    ControlSafe (step cfg s command).system history := by
  have publicSafe := LocalCommand.authentic history
  have initialLive := relation.live
  have initialCounter := relation.counter
  have inputSafe := queues.peerIn
  have replySafe := queues.localIn
  rcases safe with ⟨⟨localSafe,peerSafe⟩,scanSafe,⟨localRetire,peerRetire⟩⟩
  cases command <;>
    simp only [step,localStep,startRetirement,requestStep,replyStep,beginLocal,beginPeer,
      pushRequest,pushReply,duplicateQueue,reject] at *
  all_goals repeat' first
    | contradiction
    | assumption
    | omega
    | simp_all [ControlSafe,PendingMessagesSafe,ScanSafe,RetirementSafe,
        controllerIdle,ReplySafe,RequestSafe,CommandAuthentic]
    | intro introduced
    | split
  rename_i queue index next t eq
  cases queue <;> dsimp only at eq
  all_goals obtain ⟨items,_,rfl⟩ := Option.map_eq_some_iff.mp eq
  all_goals simpa [ControlSafe,PendingMessagesSafe,ScanSafe,RetirementSafe,CommandAuthentic] using
    (show ControlSafe s history from ⟨⟨localSafe,peerSafe⟩,scanSafe,localRetire,peerRetire⟩)

set_option maxHeartbeats 400000 in
theorem control_scan {s : System} {history : Peer} {target cursor : Nat}
    (relation : RetainedRelation s.localBank.selected s.peer.selected history)
    (safe : ControlSafe s history) (owners : Serialized s)
    (scan : s.retirementScan = some (target,cursor)) :
    ControlSafe (scanRetirement s target cursor).system history := by
  have localNone : s.localCause = none := owners.2.1.resolve_right (by simp [scan])
  have peerNone : s.peerCause = none := owners.2.2.resolve_right (by simp [scan])
  obtain ⟨floorCursor,cursorTarget,targetCounter,live⟩ := safe.2.1 target cursor scan
  unfold scanRetirement
  split
  · rename_i below
    dsimp only
    split
    · simp [reject,ControlSafe,PendingMessagesSafe,ScanSafe,RetirementSafe,localNone,peerNone]
    · rename_i record found
      split
      · rename_i released
        have released' : record.released = true := by
          have pair : record.released = true ∧ record.answer.any terminalAnswer = true := by simpa using released
          exact pair.1
        have nextLive := scan_cursor_live relation.pool live found released'
        simp only [ControlSafe,PendingMessagesSafe,ScanSafe,RetirementSafe]
        simp [localNone,peerNone]
        exact ⟨by omega,by omega,targetCounter,nextLive⟩
      · simp [reject,ControlSafe,PendingMessagesSafe,ScanSafe,RetirementSafe,localNone,peerNone]
  · have equal : cursor = target := by omega
    subst cursor
    simp [beginLocal,ControlSafe,PendingMessagesSafe,ScanSafe,RetirementSafe,peerNone,floorCursor,targetCounter]
    exact live

set_option maxHeartbeats 600000 in
theorem control_progress {cfg : Config} {s : System} {history : Peer}
    (relation : RetainedRelation s.localBank.selected s.peer.selected history)
    (safe : ControlSafe s history) (owners : Serialized s) :
    ControlSafe (progress cfg s).system (historyAfter s .progress history) := by
  have scanResult := fun target cursor eq => control_scan relation safe owners (target := target) (cursor := cursor) eq
  have localStutter := s.localBank.progress_stutters
  have peerStutter := s.peer.progress_stutters
  rcases safe with ⟨⟨localSafe,peerSafe⟩,scanSafe,⟨localRetire,peerRetire⟩⟩
  unfold progress
  repeat' first
    | assumption
    | simp_all [ControlSafe,PendingMessagesSafe,ScanSafe,RetirementSafe,Serialized,
        historyAfter,peerAction,reject,localPublished,peerPublished,pushReply]
    | split

/-- Every actual command preserves the authentic pending causes and the live
retirement boundary, including every intermediate bank-copy cut. -/
theorem control_step {cfg : Config} {s : System} {history : Peer}
    (relation : RetainedRelation s.localBank.selected s.peer.selected history)
    (queues : QueuesSafe s history) (pending : PendingMessagesSafe s history)
    (scan : ScanSafe s) (retirement : RetirementSafe s)
    (_staged : Staging cfg s) (owners : Serialized s) (command : Command) :
    PendingMessagesSafe (step cfg s command).system (historyAfter s command history) ∧
    ScanSafe (step cfg s command).system ∧ RetirementSafe (step cfg s command).system := by
  by_cases advancing : command = .progress
  · subst command
    exact control_progress relation ⟨pending,scan,retirement⟩ owners
  · have unchanged : historyAfter s command history = history := by
      cases command <;> simp_all [historyAfter,peerAction]
    rw [unchanged]
    exact control_nonprogress cfg s command history advancing relation queues ⟨pending,scan,retirement⟩

/-- Checked initialization and specialization to every first command, including
refused retirement and crash commands. Reachable iteration is supplied by the
combined source/transport invariant. -/
theorem control_initial : ControlSafe initial [] := by
  simp [ControlSafe,PendingMessagesSafe,ScanSafe,RetirementSafe,initial]

example (cfg : Config) (command : Command) :
    ControlSafe (step cfg initial command).system (historyAfter initial command []) :=
  control_step (by exact RetainedRelation.initial) QueuesSafe.initial
    control_initial.1 control_initial.2.1 control_initial.2.2
    (staging_initial cfg) serialized_initial command

end FRPSpec.PendingRetention
