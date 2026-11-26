import Applications.FRP.PendingRetention.Invariant
import Applications.FRP.PendingRetention.Staging
import Applications.FRP.PendingRetention.ControlInvariant
import Applications.FRP.PendingRetention.QueueSteps

/-! Semantic preservation at the actual controller's publication boundaries. -/
set_option autoImplicit false
namespace FRPSpec.PendingRetention
open PendingCrash PendingMigration

theorem LocalEdit.related {cfg : Config} {before after : LocalSnapshot}
    {peer : PeerSnapshot} {history : Peer} {cause : LocalCause}
    (edit : LocalEdit cfg before after cause)
    (related : RetainedRelation before peer history)
    (authentic : ∀ c, cause = .frame c → CommandAuthentic history c)
    (authorized : ∀ t, cause = .relinquish t → before.floor ≤ t ∧
      t ≤ before.frame.nextIdentity ∧ LiveAbove before.frame t) :
    RetainedRelation after peer history := by
  cases edit with
  | frame changed => exact related.localChange _ (authentic _ rfl) changed
  | relinquish target =>
    obtain ⟨monotone,counter,live⟩ := authorized target rfl
    exact related.raise_local target monotone counter live
  | finish changed => exact related.finish_local _ changed

theorem LocalEdit.extension {cfg : Config} {before after : LocalSnapshot}
    {history : Peer} {cause : LocalCause}
    (edit : LocalEdit cfg before after cause) (coupled : FramePeer before.frame history)
    (authentic : ∀ c, cause = .frame c → CommandAuthentic history c)
    (authorized : ∀ t, cause = .relinquish t → before.floor ≤ t) :
    LiveFrameExtension before.frame after.frame history ∧ before.floor ≤ after.floor := by
  have reflExtension (f : Frame) : LiveFrameExtension f f history := by
    constructor
    · intro slot r present _; exact ⟨r,present,rfl,rfl⟩
    · intro slot r present phase _; exact ⟨r,present,rfl,rfl,rfl,phase,rfl⟩
  cases edit with
  | frame changed =>
    exact ⟨propose_liveExtension _ _ _ _ coupled (authentic _ rfl)
      (localChange_proposed changed), by rw [(localChange_metadata changed).1]⟩
  | relinquish target => exact ⟨reflExtension _,authorized _ rfl⟩
  | finish changed =>
    unfold finishRetirement at changed
    split at changed <;> try contradiction
    cases changed
    exact ⟨reflExtension _,Nat.le_refl _⟩

def causeHistory (history : Peer) : PeerCause → Peer
  | .business identity command _ _ _ => (peerStep history identity command).peer
  | _ => history

def causeLabel : PeerCause → SourceLabel
  | .business identity _ _ effect prevented => match effect,prevented with
    | some y,_ => .output identity y
    | none,some x => .prevent identity x
    | none,none => .internal
  | _ => .internal

theorem PeerEdit.business_above {cfg : Config} {before after : PeerSnapshot}
    {identity : Nat} {command : PeerCommand} {reply : ReplyPacket} {effect prevented : Option Bool}
    (edit : PeerEdit cfg before after (.business identity command reply effect prevented)) :
    before.floor ≤ identity := by
  cases edit with
  | business changed different =>
    rcases peerDecision_cases changed with expired | performed
    · exact False.elim (different expired.2.1)
    · exact performed.1

theorem PeerEdit.related {cfg : Config} {localState : LocalSnapshot} {before after : PeerSnapshot}
    {history : Peer} {cause : PeerCause} (edit : PeerEdit cfg before after cause)
    (related : RetainedRelation localState before history)
    (traffic : ∀ i c r e p, cause = .business i c r e p →
      MessageSafe localState.frame history (.request i c))
    (authorized : ∀ t, cause = .floor t → t ≤ localState.floor) :
    RetainedRelation localState after (causeHistory history cause) := by
  cases edit with
  | business changed different =>
    exact related.peerDecision (traffic _ _ _ _ _ rfl)
      (PeerEdit.business_above (.business changed different)) changed
  | floor target increasing =>
    exact related.raise_peer target (Nat.le_of_lt increasing) (authorized _ rfl)
  | deletion target pending => exact related.delete_peer target pending

theorem PeerEdit.reply {cfg : Config} {before after : PeerSnapshot} {history : Peer}
    {identity : Nat} {command : PeerCommand} {reply : ReplyPacket} {effect prevented : Option Bool}
    (edit : PeerEdit cfg before after (.business identity command reply effect prevented))
    (extension : PeerExtension before.floor before.entries history) :
    ReplySafe (peerStep history identity command).peer reply := by
  have above := edit.business_above
  cases edit with
  | business changed different =>
    rcases peerDecision_cases changed with expired | performed
    · omega
    · rw [performed.2.2.1,extension.receipt identity command above]
      exact peerStep_receipt_authentic _ _ _

theorem PeerEdit.source {cfg : Config} {localState : LocalSnapshot} {before after : PeerSnapshot}
    {history : Peer} {cause : PeerCause} (edit : PeerEdit cfg before after cause)
    (related : RetainedRelation localState before history)
    (traffic : ∀ i c r e p, cause = .business i c r e p →
      MessageSafe localState.frame history (.request i c)) :
    DelayStep (causeLabel cause) (sourceView localState.frame history)
      (sourceView localState.frame (causeHistory history cause)) := by
  cases edit with
  | business changed different =>
    have above := PeerEdit.business_above (.business changed different)
    rcases peerDecision_cases changed with expired | performed
    · omega
    · rw [performed.2.2.2.1,performed.2.2.2.2]
      rw [related.extension.effect _ _ above,related.extension.prevented _ _ above]
      have source := (peerStep_source_coupled _ _ _ _ related.valid related.coupled
          (traffic _ _ _ _ _ rfl)).2
      cases he : (peerStep history _ _).effect <;> cases hp : (peerStep history _ _).prevented <;>
        simpa only [causeLabel,causeHistory,peerSourceLabel,he,hp] using source
  | floor => exact .internal _
  | deletion => exact .internal _

structure Semantic (s : System) (history : Peer) : Prop where
  relation : RetainedRelation s.localBank.selected s.peer.selected history
  queues : QueuesSafe s history

theorem Semantic.congr {s t : System} {history : Peer} (safe : Semantic s history)
    (localSame : t.localBank.selected = s.localBank.selected)
    (peerSame : t.peer.selected = s.peer.selected)
    (lo : t.localOut = s.localOut) (pi : t.peerIn = s.peerIn)
    (po : t.peerOut = s.peerOut) (li : t.localIn = s.localIn) : Semantic t history := by
  constructor
  · simpa only [localSame,peerSame] using safe.relation
  · exact safe.queues.congr (congrArg LocalSnapshot.frame localSame)
      (congrArg LocalSnapshot.floor localSame) lo pi po li

theorem Semantic.localPublished {cfg : Config} {s : System} {history : Peer}
    (safe : Semantic s history) (bank : LocalBanks) (cause : LocalCause)
    (edit : LocalEdit cfg s.localBank.selected bank.selected cause)
    (authentic : ∀ c, cause = .frame c → CommandAuthentic history c)
    (authorized : ∀ t, cause = .relinquish t → s.localBank.selected.floor ≤ t ∧
      t ≤ s.localBank.selected.frame.nextIdentity ∧ LiveAbove s.localBank.selected.frame t) :
    let result := localPublished {s with localBank := bank} cause
    Semantic result.system history ∧
    DelayStep result.label (sourceView s.localBank.selected.frame history)
      (sourceView result.system.localBank.selected.frame history) := by
  have relation := edit.related safe.relation authentic authorized
  have extension := edit.extension safe.relation.coupled authentic
    (fun t ht => (authorized t ht).1)
  have queues : QueuesSafe {s with localBank := bank} history :=
    safe.queues.extension relation.valid extension.1 extension.2 rfl rfl rfl rfl
  have source := edit.source history safe.relation.valid safe.relation.coupled safe.relation.names.fresh
  have label := edit.publication_label {s with localBank := bank} cause
  dsimp only
  refine ⟨?_,?_⟩
  · cases cause with
    | frame c => cases c <;> exact ⟨relation,queues.congr rfl rfl rfl rfl rfl rfl⟩
    | relinquish => exact ⟨relation,queues.congr rfl rfl rfl rfl rfl rfl⟩
    | finish => exact ⟨relation,queues.congr rfl rfl rfl rfl rfl rfl⟩
  · rw [label]
    cases cause with
    | frame c => cases c <;> exact source
    | relinquish => exact source
    | finish => exact source

theorem Semantic.pushReply {cfg : Config} {s : System} {history : Peer}
    (safe : Semantic s history) (reply : ReplyPacket) (authentic : ReplySafe history reply) :
    Semantic (FRPSpec.PendingRetention.pushReply cfg s reply).system history := by
  refine ⟨?_,safe.queues.pushReply cfg reply authentic⟩
  unfold FRPSpec.PendingRetention.pushReply
  split <;> exact safe.relation

theorem Semantic.peerPublished {cfg : Config} {s : System} {history : Peer}
    (safe : Semantic s history) (bank : PeerBanks) (cause : PeerCause)
    (edit : PeerEdit cfg s.peer.selected bank.selected cause)
    (traffic : ∀ i c r e p, cause = .business i c r e p →
      MessageSafe s.localBank.selected.frame history (.request i c))
    (authorized : ∀ t, cause = .floor t → t ≤ s.localBank.selected.floor) :
    let result := peerPublished cfg {s with peer := bank} cause
    Semantic result.system (causeHistory history cause) ∧
    DelayStep result.label (sourceView s.localBank.selected.frame history)
      (sourceView result.system.localBank.selected.frame (causeHistory history cause)) := by
  have relation := edit.related safe.relation traffic authorized
  have source := edit.source safe.relation traffic
  cases cause with
  | business i c r e p =>
    have base : Semantic {s with peer := bank,peerCause := none} (peerStep history i c).peer :=
      ⟨relation,(safe.queues.peerStep i c).congr rfl rfl rfl rfl rfl rfl⟩
    have sent := base.pushReply (cfg := cfg) r (edit.reply safe.relation.extension)
    refine ⟨sent,?_⟩
    simp only [FRPSpec.PendingRetention.peerPublished]
    have frame : (FRPSpec.PendingRetention.pushReply cfg {s with peer := bank,peerCause := none} r).system.localBank = s.localBank := by
      unfold FRPSpec.PendingRetention.pushReply; split <;> rfl
    rw [frame]
    cases e <;> cases p <;> exact source
  | floor target =>
    exact ⟨⟨relation,safe.queues.congr rfl rfl rfl rfl rfl rfl⟩,source⟩
  | deletion target =>
    have base : Semantic {s with peer := bank,peerCause := none} history :=
      ⟨relation,safe.queues.congr rfl rfl rfl rfl rfl rfl⟩
    have sent := base.pushReply (cfg := cfg) (.deleted target) trivial
    refine ⟨sent,?_⟩
    simp only [FRPSpec.PendingRetention.peerPublished]
    have frame : (FRPSpec.PendingRetention.pushReply cfg {s with peer := bank,peerCause := none} (.deleted target)).system.localBank = s.localBank := by
      unfold FRPSpec.PendingRetention.pushReply; split <;> rfl
    rw [frame]
    unfold FRPSpec.PendingRetention.pushReply
    split <;> exact source

theorem Semantic.scan {s : System} {history : Peer} (safe : Semantic s history)
    (target cursor : Nat) : Semantic (scanRetirement s target cursor).system history ∧
    DelayStep (scanRetirement s target cursor).label (sourceView s.localBank.selected.frame history)
      (sourceView (scanRetirement s target cursor).system.localBank.selected.frame history) := by
  unfold scanRetirement
  repeat' first
    | exact ⟨safe.congr rfl rfl rfl rfl rfl rfl,.internal _⟩
    | dsimp only
    | split

set_option maxHeartbeats 800000 in
theorem Semantic.progress {cfg : Config} {s : System} {history : Peer}
    (safe : Semantic s history) (pending : PendingMessagesSafe s history)
    (retirement : RetirementSafe s) (staged : Staging cfg s) :
    Semantic (FRPSpec.PendingRetention.progress cfg s).system (historyAfter s .progress history) ∧
    DelayStep (FRPSpec.PendingRetention.progress cfg s).label (sourceView s.localBank.selected.frame history)
      (sourceView (FRPSpec.PendingRetention.progress cfg s).system.localBank.selected.frame (historyAfter s .progress history)) := by
  unfold FRPSpec.PendingRetention.progress
  split
  · rename_i down
    have ghost : historyAfter s .progress history = history := by
      have peerDown : s.peerDown = true := (Bool.and_eq_true_iff.mp down).2
      simp [historyAfter,peerAction,peerDown]
    rw [ghost]
    exact ⟨safe,.internal _⟩
  · cases scan : s.retirementScan with
    | some pair =>
      rcases pair with ⟨target,cursor⟩
      have ghost : historyAfter s .progress history = history := by
        simp [historyAfter,peerAction,scan]
      rw [ghost]
      dsimp only
      split
      · exact ⟨safe,.internal _⟩
      · exact safe.scan target cursor
    | none =>
      dsimp only
      cases localCause : s.localCause with
      | some cause =>
        have ghost : historyAfter s .progress history = history := by
          simp [historyAfter,peerAction,localCause]
        rw [ghost]
        dsimp only
        split
        · exact ⟨safe,.internal _⟩
        · split
          · rename_i published
            simpa only [scan,localCause] using safe.localPublished _ cause ((localCause ▸ staged.1).publication published)
              (fun c hc => pending.1 c (by simpa [hc] using localCause))
              (fun t ht => retirement.1 t (by simpa [ht] using localCause))
          · rename_i silent
            have stutter := s.localBank.progress_stutters (Bool.eq_false_iff.mpr silent)
            refine ⟨safe.congr stutter rfl rfl rfl rfl rfl,?_⟩
            simp only [stutter]; exact .internal _
      | none =>
        dsimp only
        cases peerCause : s.peerCause with
        | none =>
          have ghost : historyAfter s .progress history = history := by
            simp [historyAfter,peerAction,peerCause,localCause,scan]
          rw [ghost]
          exact ⟨safe,.internal _⟩
        | some cause =>
          try dsimp only
          split
          · rename_i down
            have ghost : historyAfter s .progress history = history := by
              simp [historyAfter,peerAction,down]
            rw [ghost]
            exact ⟨safe,.internal _⟩
          · rename_i awake
            split
            · rename_i published
              have ghost : historyAfter s .progress history = causeHistory history cause := by
                cases cause <;> simp [historyAfter,peerAction,peerCause,localCause,scan,
                  Bool.eq_false_iff.mpr awake,published,causeHistory]
              rw [ghost]
              simpa only [scan,localCause,peerCause] using safe.peerPublished _ cause ((peerCause ▸ staged.2).publication published)
                (fun i c r e p hc => pending.2 i c r e p (by simpa [hc] using peerCause))
                (fun t ht => retirement.2 t (by simpa [ht] using peerCause))
            · rename_i silent
              have ghost : historyAfter s .progress history = history := by
                cases cause <;> simp [historyAfter,peerAction,peerCause,localCause,scan,
                  Bool.eq_false_iff.mpr awake,silent]
              rw [ghost]
              exact ⟨safe.congr rfl (s.peer.progress_stutters (Bool.eq_false_iff.mpr silent))
                rfl rfl rfl rfl,.internal _⟩

structure Safe (cfg : Config) (s : System) (history : Peer) : Prop where
  semantic : Semantic s history
  pending : PendingMessagesSafe s history
  scan : ScanSafe s
  retirement : RetirementSafe s
  staging : Staging cfg s
  serialized : Serialized s

theorem Safe.initial (cfg : Config) : Safe cfg initial [] :=
  ⟨⟨RetainedRelation.initial,QueuesSafe.initial⟩,
   control_initial.1,control_initial.2.1,control_initial.2.2,
   staging_initial cfg,serialized_initial⟩

theorem Semantic.step {cfg : Config} {s : System} {history : Peer}
    (safe : Safe cfg s history) (command : Command) :
    Semantic (FRPSpec.PendingRetention.step cfg s command).system (historyAfter s command history) ∧
    DelayStep (FRPSpec.PendingRetention.step cfg s command).label
      (sourceView s.localBank.selected.frame history)
      (sourceView (FRPSpec.PendingRetention.step cfg s command).system.localBank.selected.frame
        (historyAfter s command history)) := by
  by_cases advancing : command = .progress
  · subst command
    exact safe.semantic.progress safe.pending safe.retirement safe.staging
  · obtain ⟨localSame,peerSame,label⟩ := step_nonprogress_selected cfg s command advancing
    have ghost : historyAfter s command history = history := by
      cases command <;> simp_all [historyAfter,peerAction]
    rw [ghost]
    refine ⟨⟨?_,safe.semantic.queues.nonprogress_step safe.semantic.relation command advancing⟩,?_⟩
    · simpa only [localSame,peerSame] using safe.semantic.relation
    · rw [label,localSame]; exact .internal _

theorem Safe.step {cfg : Config} {s : System} {history : Peer}
    (safe : Safe cfg s history) (command : Command) :
    Safe cfg (FRPSpec.PendingRetention.step cfg s command).system (historyAfter s command history) := by
  obtain ⟨pending,scan,retirement⟩ := control_step safe.semantic.relation safe.semantic.queues
    safe.pending safe.scan safe.retirement safe.staging safe.serialized command
  exact ⟨(Semantic.step safe command).1,pending,scan,retirement,
    staging_step safe.staging command,serialized_step safe.serialized command⟩

/-- The same executor used by the storage and work bounds preserves the complete
transport/source relation through arbitrary finite commands and failures. -/
theorem Safe.execute {cfg : Config} {s : System} {history : Peer}
    (safe : Safe cfg s history) (commands : List Command) :
    Safe cfg (FRPSpec.PendingRetention.execute cfg s commands).system
      (peerExecute history (peerActions cfg s commands)).peer :=
  execute_induction cfg (Safe cfg) (fun _ _ c h => h.step c) s history commands safe

/-- Every actual emitted label implements the independent delay source. -/
theorem Safe.sourceRun {cfg : Config} {s : System} {history : Peer}
    (safe : Safe cfg s history) (commands : List Command) :
    SourceRun (sourceView s.localBank.selected.frame history)
      (FRPSpec.PendingRetention.execute cfg s commands).labels
      (sourceView (FRPSpec.PendingRetention.execute cfg s commands).system.localBank.selected.frame
        (peerExecute history (peerActions cfg s commands)).peer) := by
  induction commands generalizing s history with
  | nil => exact .nil _
  | cons command commands ih =>
    have head := (Semantic.step safe command).2
    have tail := ih (safe.step command)
    have combined := SourceRun.cons head tail
    cases action : peerAction s command with
    | none => simpa [FRPSpec.PendingRetention.execute,peerActions,action,historyAfter,peerExecute] using combined
    | some pair =>
      rcases pair with ⟨identity,operation⟩
      simpa [FRPSpec.PendingRetention.execute,peerActions,action,historyAfter,peerExecute] using combined

theorem initial_execution_safe (cfg : Config) (commands : List Command) :
    Safe cfg (execute cfg initial commands).system (peerExecute [] (peerActions cfg initial commands)).peer :=
  (Safe.initial cfg).execute commands

theorem initial_execution_source (cfg : Config) (commands : List Command) :
    SourceRun (sourceView initialFrame []) (execute cfg initial commands).labels
      (sourceView (execute cfg initial commands).system.localBank.selected.frame
        (peerExecute [] (peerActions cfg initial commands)).peer) :=
  (Safe.initial cfg).sourceRun commands

end FRPSpec.PendingRetention
