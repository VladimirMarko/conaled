import Applications.FRP.PendingRetention.Observations
import Applications.FRP.PendingRetention.Safety

namespace FRPSpec.PendingRetention
open PendingCrash
set_option autoImplicit false

def Observed (s : System) : Prop :=
  PoolObserved s.localBank.selected.frame s.localBank.selected.floor s.localBank.selected.outcomes

theorem LocalEdit.observed {cfg : Config} {before after : LocalSnapshot}
    {peer : PeerSnapshot} {history : Peer} {cause : LocalCause}
    (edit : LocalEdit cfg before after cause)
    (safe : RetainedRelation before peer history)
    (observed : PoolObserved before.frame before.floor before.outcomes)
    (authorized : ∀ target, cause = .relinquish target → before.floor ≤ target) :
    PoolObserved after.frame after.floor after.outcomes := by
  cases edit with
  | frame changed => exact observed.localChange safe.pool safe.valid safe.coupled _ changed
  | relinquish target => exact observed.raise_local (authorized target rfl)
  | finish changed => exact observed.finishRetirement safe.local_pending changed

theorem Observed.scan {s : System} (h : Observed s) (target cursor : Nat) :
    Observed (scanRetirement s target cursor).system := by
  unfold scanRetirement
  repeat' first | exact h | dsimp only | split

theorem Observed.localPublished {s : System} (h : Observed s) (cause : LocalCause) :
    Observed (localPublished s cause).system := by
  cases cause with
  | frame command => cases command <;> exact h
  | relinquish => exact h
  | finish => exact h

theorem Observed.peerPublished {cfg : Config} {s : System} (h : Observed s) (cause : PeerCause) :
    Observed (peerPublished cfg s cause).system := by
  cases cause <;> simp only [FRPSpec.PendingRetention.peerPublished,pushReply]
  all_goals repeat' first | exact h | split

theorem Observed.progress {cfg : Config} {s : System} {history : Peer}
    (h : Observed s) (safe : Safe cfg s history) :
    Observed (progress cfg s).system := by
  unfold FRPSpec.PendingRetention.progress
  split
  · exact h
  · cases scan : s.retirementScan with
    | some pair =>
      rcases pair with ⟨target,cursor⟩
      dsimp only
      split
      · exact h
      · exact h.scan target cursor
    | none =>
      dsimp only
      cases localCause : s.localCause with
      | some cause =>
        dsimp only
        split
        · exact h
        · split
          · rename_i published
            apply Observed.localPublished
            exact ((localCause ▸ safe.staging.1).publication published).observed
              safe.semantic.relation h (fun target equal =>
                (safe.retirement.1 target (by simpa [equal] using localCause)).1)
          · rename_i silent
            have same := s.localBank.progress_stutters (Bool.eq_false_iff.mpr silent)
            simpa only [Observed,same] using h
      | none =>
        dsimp only
        cases peerCause : s.peerCause with
        | none => exact h
        | some cause =>
          dsimp only
          split
          · exact h
          · split
            · apply Observed.peerPublished; exact h
            · exact h

theorem Observed.step {cfg : Config} {s : System} {history : Peer}
    (h : Observed s) (safe : Safe cfg s history) (command : Command) :
    Observed (FRPSpec.PendingRetention.step cfg s command).system := by
  by_cases advancing : command = .progress
  · subst command; exact h.progress safe
  · have same := (step_nonprogress_selected cfg s command advancing).1
    simpa only [Observed,same] using h

theorem Observed.execute {cfg : Config} {s : System} {history : Peer}
    (h : Observed s) (safe : Safe cfg s history) (commands : List Command) :
    Observed (FRPSpec.PendingRetention.execute cfg s commands).system := by
  have paired := execute_induction cfg (fun s history => Safe cfg s history ∧ Observed s)
    (fun _ _ command h => ⟨h.1.step command,h.2.step h.1 command⟩)
    s history commands ⟨safe,h⟩
  exact paired.2

/-- Observation coverage is preserved by every finite execution of the same
bounded executor, including copies, crashes, retirement and recovery. -/
theorem initial_execution_observed (cfg : Config) (commands : List Command) :
    Observed (execute cfg initial commands).system :=
  (show Observed initial from PoolObserved.initial .delay).execute (Safe.initial cfg) commands

theorem initial_execution_query_known (cfg : Config) (commands : List Command) (identity : Nat)
    (lower : (execute cfg initial commands).system.localBank.selected.floor ≤ identity)
    (upper : identity < (execute cfg initial commands).system.localBank.selected.frame.nextIdentity) :
    query (execute cfg initial commands).system.localBank.selected identity ≠ .unknown :=
  (initial_execution_observed cfg commands).query_known identity lower upper

/-- Once a retained allocated request leaves the live frame, its actual query
returns a terminal answer authenticated by the execution's lifetime ledger. -/
theorem initial_execution_query_completed (cfg : Config) (commands : List Command) (identity : Nat)
    (lower : (execute cfg initial commands).system.localBank.selected.floor ≤ identity)
    (upper : identity < (execute cfg initial commands).system.localBank.selected.frame.nextIdentity)
    (notLive : ∀ slot request,
      request ∈ (execute cfg initial commands).system.localBank.selected.frame.requests.get slot →
      request.identity ≠ identity) :
    ∃ answer,
      query (execute cfg initial commands).system.localBank.selected identity = .terminal answer ∧
      terminalAnswer answer = true ∧
      ReceiptAuthentic (peerExecute [] (peerActions cfg initial commands)).peer ⟨identity,answer⟩ := by
  have observed := initial_execution_observed cfg commands
  have safe := initial_execution_safe cfg commands
  obtain ⟨answer,result,terminal⟩ := PoolObserved.query_completed observed identity lower upper (by
    intro record member equal live
    obtain ⟨slot,request,present,requestId,_⟩ := live
    exact notLive slot request (by simp [present]) (requestId.trans equal))
  exact ⟨answer,result,terminal,safe.semantic.relation.pool.query_authentic lower result⟩

end FRPSpec.PendingRetention
