import Applications.FRP.PendingRetention.Runtime
import Applications.FRP.PendingRetention.Refinement

/-! Staged updates retain their originating edit through every persistent-copy
microstep. The witnesses are proofs, not additional runtime snapshots. -/
namespace FRPSpec.PendingRetention
open PendingCrash Durability

inductive LocalEdit (cfg : Config) : LocalSnapshot → LocalSnapshot → LocalCause → Prop
  | frame {before after command} (changed : localChange cfg before command = .ok after) :
      LocalEdit cfg before after (.frame command)
  | relinquish (before : LocalSnapshot) (target : Nat) :
      LocalEdit cfg before {before with floor := target, pending := some target} (.relinquish target)
  | finish {before after target} (changed : finishRetirement before target = some after) :
      LocalEdit cfg before after (.finish target)

inductive PeerEdit (cfg : Config) : PeerSnapshot → PeerSnapshot → PeerCause → Prop
  | business {before after identity command reply effect prevented}
      (changed : peerDecision cfg before identity command = .ok (after,reply,effect,prevented))
      (different : after ≠ before) :
      PeerEdit cfg before after (.business identity command reply effect prevented)
  | floor (before : PeerSnapshot) (target : Nat) (increasing : before.floor < target) :
      PeerEdit cfg before {before with floor := target, pending := some target} (.floor target)
  | deletion (before : PeerSnapshot) (target : Nat) (pending : before.pending = some target) :
      PeerEdit cfg before {before with pending := none, entries := before.entries.filter (fun e => target ≤ e.1)} (.deletion target)

def LocalStage (cfg : Config) (bank : LocalBanks) : Option LocalCause → Prop
  | none => True
  | some cause => (∃ start, bank.AtCut start localSeed) ∧
      LocalEdit cfg bank.selected (LocalSnapshot.decode bank.target) cause

def PeerStage (cfg : Config) (bank : PeerBanks) : Option PeerCause → Prop
  | none => True
  | some cause => (∃ start, bank.AtCut start peerSeed) ∧
      PeerEdit cfg bank.selected (PeerSnapshot.decode bank.target) cause

def Staging (cfg : Config) (s : System) : Prop :=
  LocalStage cfg s.localBank s.localCause ∧ PeerStage cfg s.peer s.peerCause

theorem staging_initial (cfg : Config) : Staging cfg initial := ⟨trivial,trivial⟩

theorem LocalStage.begin (cfg : Config) (bank : LocalBanks) (target : LocalSnapshot)
    (cause : LocalCause) (edit : LocalEdit cfg bank.selected target cause) :
    LocalStage cfg (bank.begin target) (some cause) :=
  ⟨⟨bank.state.disk,SnapshotBanks.begin_atCut _ _ _⟩,edit⟩

theorem PeerStage.begin (cfg : Config) (bank : PeerBanks) (target : PeerSnapshot)
    (cause : PeerCause) (edit : PeerEdit cfg bank.selected target cause) :
    PeerStage cfg (bank.begin target) (some cause) :=
  ⟨⟨bank.state.disk,SnapshotBanks.begin_atCut _ _ _⟩,edit⟩

theorem LocalStage.progress {cfg : Config} {bank : LocalBanks} {cause : LocalCause}
    (staged : LocalStage cfg bank (some cause)) (silent : bank.progress.2 = false) :
    LocalStage cfg bank.progress.1 (some cause) := by
  obtain ⟨⟨start,cut⟩,edit⟩ := staged
  refine ⟨⟨start,SnapshotBanks.Worker.progress_atCut _ _ _ cut⟩,?_⟩
  rw [LocalBanks.progress_stutters bank silent]
  simpa only [LocalBanks.progress, SnapshotBanks.Worker.progress_target] using edit

theorem PeerStage.progress {cfg : Config} {bank : PeerBanks} {cause : PeerCause}
    (staged : PeerStage cfg bank (some cause)) (silent : bank.progress.2 = false) :
    PeerStage cfg bank.progress.1 (some cause) := by
  obtain ⟨⟨start,cut⟩,edit⟩ := staged
  refine ⟨⟨start,SnapshotBanks.Worker.progress_atCut _ _ _ cut⟩,?_⟩
  rw [PeerBanks.progress_stutters bank silent]
  simpa only [PeerBanks.progress, SnapshotBanks.Worker.progress_target] using edit

theorem LocalStage.publication {cfg : Config} {bank : LocalBanks} {cause : LocalCause}
    (staged : LocalStage cfg bank (some cause)) (published : bank.progress.2 = true) :
    LocalEdit cfg bank.selected bank.progress.1.selected cause := by
  obtain ⟨⟨start,cut⟩,edit⟩ := staged
  rw [LocalBanks.progress_publishes bank start cut published]
  exact edit

theorem PeerStage.publication {cfg : Config} {bank : PeerBanks} {cause : PeerCause}
    (staged : PeerStage cfg bank (some cause)) (published : bank.progress.2 = true) :
    PeerEdit cfg bank.selected bank.progress.1.selected cause := by
  obtain ⟨⟨start,cut⟩,edit⟩ := staged
  rw [PeerBanks.progress_publishes bank start cut published]
  exact edit


theorem Staging.beginLocal {cfg : Config} {s : System} (h : Staging cfg s)
    (target : LocalSnapshot) (cause : LocalCause)
    (edit : LocalEdit cfg s.localBank.selected target cause) :
    Staging cfg (FRPSpec.PendingRetention.beginLocal s target cause).system :=
  ⟨LocalStage.begin cfg s.localBank target cause edit,h.2⟩

theorem Staging.beginPeer {cfg : Config} {s : System} (h : Staging cfg s)
    (target : PeerSnapshot) (cause : PeerCause)
    (edit : PeerEdit cfg s.peer.selected target cause) :
    Staging cfg (FRPSpec.PendingRetention.beginPeer s target cause).system :=
  ⟨h.1,PeerStage.begin cfg s.peer target cause edit⟩

theorem Staging.pushRequest {cfg : Config} {s : System} (h : Staging cfg s)
    (packet : RequestPacket) : Staging cfg (FRPSpec.PendingRetention.pushRequest cfg s packet).system := by
  unfold FRPSpec.PendingRetention.pushRequest
  split <;> exact h

theorem Staging.pushReply {cfg : Config} {s : System} (h : Staging cfg s)
    (packet : ReplyPacket) : Staging cfg (FRPSpec.PendingRetention.pushReply cfg s packet).system := by
  unfold FRPSpec.PendingRetention.pushReply
  split <;> exact h

theorem Staging.localStep {cfg : Config} {s : System} (h : Staging cfg s)
    (command : LocalCommand) : Staging cfg (FRPSpec.PendingRetention.localStep cfg s command).system := by
  unfold FRPSpec.PendingRetention.localStep
  try dsimp only
  split
  · exact h
  · split
    · exact h
    · rename_i target changed
      split
      · split
        · exact h
        · split
          · exact h
          · exact Staging.beginLocal h _ _ (.frame changed)
      · exact Staging.beginLocal h _ _ (.frame changed)

theorem Staging.startRetirement {cfg : Config} {s : System} (h : Staging cfg s)
    (target : Nat) : Staging cfg (FRPSpec.PendingRetention.startRetirement s target).system := by
  unfold FRPSpec.PendingRetention.startRetirement
  try dsimp only
  repeat' split
  all_goals exact h

theorem Staging.scanRetirement {cfg : Config} {s : System} (h : Staging cfg s)
    (target cursor : Nat) : Staging cfg (FRPSpec.PendingRetention.scanRetirement s target cursor).system := by
  unfold FRPSpec.PendingRetention.scanRetirement
  try dsimp only
  split
  · split
    · exact h
    · split <;> exact h
  · exact Staging.beginLocal h _ _ (.relinquish _ _)

theorem Staging.requestStep {cfg : Config} {s : System} (h : Staging cfg s) :
    Staging cfg (FRPSpec.PendingRetention.requestStep cfg s).system := by
  unfold FRPSpec.PendingRetention.requestStep
  try dsimp only
  split
  · exact h
  · split
    · exact h
    · split
      · split
        · exact h
        · split
          · exact h
          · rename_i target reply effect prevented changed
            split
            · apply Staging.pushReply; exact h
            · exact Staging.beginPeer h _ _ (.business changed (by assumption))
      · split
        · exact h
        · split
          · apply Staging.pushReply; exact h
          · exact Staging.beginPeer h _ _ (.floor _ _ (by omega))

theorem Staging.replyStep {cfg : Config} {s : System} (h : Staging cfg s) :
    Staging cfg (FRPSpec.PendingRetention.replyStep cfg s).system := by
  unfold FRPSpec.PendingRetention.replyStep
  try dsimp only
  split
  · exact h
  · split
    · exact h
    · split
      · exact h
      · split
        · exact h
        · rename_i next changed
          exact Staging.beginLocal h _ _ (.finish changed)
      · split
        · exact h
        · split
          · exact h
          · rename_i next changed
            exact Staging.beginLocal h _ _ (.frame changed)


theorem staging_localPublished {cfg : Config} {s : System}
    (peer : PeerStage cfg s.peer s.peerCause) (cause : LocalCause) :
    Staging cfg (localPublished s cause).system := by
  cases cause with
  | frame command => cases command <;> exact ⟨trivial,peer⟩
  | relinquish | finish => exact ⟨trivial,peer⟩

theorem staging_peerPublished {cfg : Config} {s : System}
    (localStage : LocalStage cfg s.localBank s.localCause) (cause : PeerCause) :
    Staging cfg (peerPublished cfg s cause).system := by
  cases cause with
  | business => apply Staging.pushReply; exact ⟨localStage,trivial⟩
  | floor => exact ⟨localStage,trivial⟩
  | deletion => apply Staging.pushReply; exact ⟨localStage,trivial⟩

theorem staging_progress {cfg : Config} {s : System} (h : Staging cfg s) :
    Staging cfg (progress cfg s).system := by
  unfold progress
  try dsimp only
  split
  · exact h
  · split
    · split
      · exact h
      · exact h.scanRetirement _ _
    · split
      · split
        · exact h
        · split
          · apply staging_localPublished; exact h.2
          · constructor
            · simpa only [*] using LocalStage.progress (by simpa only [*] using h.1) (by simp_all)
            · exact h.2
      · split
        · split
          · exact h
          · split
            · apply staging_peerPublished; exact h.1
            · constructor
              · exact h.1
              · simpa only [*] using PeerStage.progress (by simpa only [*] using h.2) (by simp_all)
        · exact h

theorem staging_duplicateQueue {cfg : Config} {s : System} (h : Staging cfg s)
    (queue : Queue) (index : Nat) : Staging cfg (duplicateQueue cfg s queue index).system := by
  cases queue with
  | localOut => cases hd : duplicateList cfg.queueCapacity index s.localOut <;>
      simp only [duplicateQueue,hd,Option.map] <;> exact h
  | peerIn => cases hd : duplicateList cfg.queueCapacity index s.peerIn <;>
      simp only [duplicateQueue,hd,Option.map] <;> exact h
  | peerOut => cases hd : duplicateList cfg.queueCapacity index s.peerOut <;>
      simp only [duplicateQueue,hd,Option.map] <;> exact h
  | localIn => cases hd : duplicateList cfg.queueCapacity index s.localIn <;>
      simp only [duplicateQueue,hd,Option.map] <;> exact h

theorem staging_step {cfg : Config} {s : System} (h : Staging cfg s) (command : Command) :
    Staging cfg (step cfg s command).system := by
  cases command with
  | «local» c => exact h.localStep c
  | relinquishBefore t => exact h.startRetirement t
  | deliverRequest => exact h.requestStep
  | deliverReply => exact h.replyStep
  | progress => exact staging_progress h
  | duplicate q i => exact staging_duplicateQueue h q i
  | send identity operation =>
    simp only [step]
    split
    · exact h
    · split
      · exact h
      · split
        · exact h
        · exact h.pushRequest _
  | retryRetirement =>
    simp only [step]
    split
    · exact h
    · split
      · exact h
      · exact h.pushRequest _
  | resumeDeletion =>
    simp only [step]
    split
    · exact h
    · split
      · exact h
      · exact Staging.beginPeer h _ _ (.deletion _ _ (by assumption))
  | transferRequest | transferReply =>
    simp only [step]
    split
    · exact h
    · split <;> exact h
  | drop queue => cases queue <;> exact h
  | crashLocal => exact ⟨trivial,h.2⟩
  | crashPeer => exact ⟨h.1,trivial⟩
  | recoverLocal | recoverPeer | inspect | query =>
    simp only [step]
    split <;> exact h
  | cleanup | malformed => exact h

theorem staging_reachable {cfg : Config} {s : System} (h : Reachable cfg s) : Staging cfg s := by
  induction h with
  | initial => exact staging_initial cfg
  | next _ command ih => exact staging_step ih command


/-- Durable mutations and the eligibility scan have one serialized owner. -/
def Serialized (s : System) : Prop :=
  (s.localCause = none ∨ s.peerCause = none) ∧
  (s.localCause = none ∨ s.retirementScan = none) ∧
  (s.peerCause = none ∨ s.retirementScan = none)

theorem controllerIdle_owners {s : System} (idle : controllerIdle s = true) :
    s.localCause = none ∧ s.peerCause = none ∧ s.retirementScan = none := by
  simp [controllerIdle] at idle
  tauto

theorem serialized_initial : Serialized initial := by simp [Serialized,initial]

set_option maxHeartbeats 1200000 in
 theorem serialized_step {cfg : Config} {s : System} (h : Serialized s) (command : Command) :
    Serialized (step cfg s command).system := by
  cases command <;>
    simp only [step,localStep,startRetirement,scanRetirement,requestStep,replyStep,progress,
      localPublished,peerPublished,beginLocal,beginPeer,pushRequest,pushReply,duplicateQueue,
      reject,Serialized] at *
  all_goals repeat' first
    | simp_all [controllerIdle]
    | split
  rename_i queue index next t eq
  cases queue <;> dsimp only at eq
  all_goals obtain ⟨items,_,rfl⟩ := Option.map_eq_some_iff.mp eq
  all_goals exact h

 theorem serialized_reachable {cfg : Config} {s : System} (h : Reachable cfg s) : Serialized s := by
  induction h with
  | initial => exact serialized_initial
  | next _ command ih => exact serialized_step ih command


theorem localPublished_frame_label {cfg : Config} (s : System) (before : LocalSnapshot)
    (command : FrameCommand) (edit : localChange cfg before command = .ok s.localBank.selected) :
    (localPublished s (.frame command)).label = frameSourceLabel before.frame command := by
  have next := propose_nextIdentity _ _ _ (localChange_proposed edit)
  cases command <;> simp_all [localPublished,frameSourceLabel,admissionDelta]

def localEditLabel (before : LocalSnapshot) : LocalCause → SourceLabel
  | .frame command => frameSourceLabel before.frame command
  | _ => .internal

theorem LocalEdit.source {cfg : Config} {before after : LocalSnapshot} {cause : LocalCause}
    (edit : LocalEdit cfg before after cause) (history : Peer) (valid : before.frame.Valid)
    (coupled : FramePeer before.frame history)
    (fresh : (lookup before.frame.nextIdentity history).1 = none) :
    DelayStep (localEditLabel before cause) (sourceView before.frame history)
      (sourceView after.frame history) := by
  cases edit with
  | frame changed => exact localChange_sourceView history valid coupled fresh changed
  | relinquish => exact .internal _
  | finish changed =>
    unfold finishRetirement at changed
    split at changed <;> try contradiction
    cases changed
    exact .internal _

theorem LocalEdit.frame_changed {cfg : Config} {before after : LocalSnapshot} {command : FrameCommand}
    (edit : LocalEdit cfg before after (.frame command)) : localChange cfg before command = .ok after := by
  cases edit
  assumption

theorem LocalEdit.publication_label {cfg : Config} {before : LocalSnapshot}
    (s : System) (cause : LocalCause) (edit : LocalEdit cfg before s.localBank.selected cause) :
    (localPublished s cause).label = localEditLabel before cause := by
  cases cause with
  | frame command => exact localPublished_frame_label s before command edit.frame_changed
  | relinquish => rfl
  | finish => rfl


set_option maxHeartbeats 1200000 in
/-- Every durable publication is a progress microstep. Ordinary commands only
prepare updates, manipulate transport, or recover the already selected root. -/
theorem step_nonprogress_selected (cfg : Config) (s : System) (command : Command)
    (ordinary : command ≠ .progress) :
    (step cfg s command).system.localBank.selected = s.localBank.selected ∧
    (step cfg s command).system.peer.selected = s.peer.selected ∧
    (step cfg s command).label = .internal := by
  cases command <;>
    simp only [step,localStep,startRetirement,requestStep,replyStep,beginLocal,beginPeer,
      pushRequest,pushReply,duplicateQueue,reject] at *
  all_goals repeat' first
    | contradiction
    | simp_all
    | split
  rename_i queue index next t eq
  cases queue <;> dsimp only at eq
  all_goals obtain ⟨items,_,rfl⟩ := Option.map_eq_some_iff.mp eq
  all_goals simp_all

end FRPSpec.PendingRetention
