import Applications.FRP.PendingRetention.Invariant
import Applications.FRP.PendingRetention.Staging

/-! Queue provenance through ordinary controller commands. Publication steps
are handled with their source and lifetime-ledger transition. -/
namespace FRPSpec.PendingRetention
open PendingCrash

theorem QueuesSafe.localStep {cfg : Config} {s : System} {history : Peer}
    (safe : QueuesSafe s history) (command : LocalCommand) :
    QueuesSafe (FRPSpec.PendingRetention.localStep cfg s command).system history := by
  unfold FRPSpec.PendingRetention.localStep
  dsimp only
  split
  · exact safe.congr rfl rfl rfl rfl rfl rfl
  · split
    · exact safe.congr rfl rfl rfl rfl rfl rfl
    · split
      · split
        · exact safe.congr rfl rfl rfl rfl rfl rfl
        · split
          · exact safe.congr rfl rfl rfl rfl rfl rfl
          · apply QueuesSafe.beginLocal; exact safe.congr rfl rfl rfl rfl rfl rfl
      · apply QueuesSafe.beginLocal; exact safe.congr rfl rfl rfl rfl rfl rfl

theorem QueuesSafe.nonprogress_step {cfg : Config} {s : System} {history : Peer}
    (safe : QueuesSafe s history)
    (related : RetainedRelation s.localBank.selected s.peer.selected history)
    (command : Command) (ordinary : command ≠ .progress) :
    QueuesSafe (step cfg s command).system history := by
  cases command with
  | «local» c => exact safe.localStep c
  | send i operation => exact safe.send cfg related.pool related.valid i operation
  | transferRequest => exact safe.transferRequest cfg
  | transferReply => exact safe.transferReply cfg
  | deliverRequest => exact safe.requestStep cfg related.extension
  | deliverReply => exact safe.replyStep cfg
  | duplicate q i => exact safe.duplicateQueue cfg q i
  | drop q => exact safe.drop cfg q
  | crashLocal => exact safe.crashLocal cfg
  | crashPeer => exact safe.crashPeer cfg
  | progress => exact False.elim (ordinary rfl)
  | relinquishBefore target =>
    simp only [step,startRetirement]
    repeat' split
    all_goals exact safe.congr rfl rfl rfl rfl rfl rfl
  | retryRetirement =>
    simp only [step]
    split
    · exact safe.congr rfl rfl rfl rfl rfl rfl
    · split
      · exact safe.congr rfl rfl rfl rfl rfl rfl
      · rename_i target pending
        apply QueuesSafe.pushRequest cfg safe
        exact Nat.le_of_eq (related.local_pending target (by simp [pending]))
  | resumeDeletion =>
    simp only [step]
    split
    · exact safe.congr rfl rfl rfl rfl rfl rfl
    · split
      · exact safe.congr rfl rfl rfl rfl rfl rfl
      · exact safe.beginPeer _ _
  | recoverLocal | recoverPeer | inspect | query =>
    simp only [step]
    split <;> exact safe.congr rfl rfl rfl rfl rfl rfl
  | cleanup | malformed => exact safe.congr rfl rfl rfl rfl rfl rfl

end FRPSpec.PendingRetention
