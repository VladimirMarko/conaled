import Applications.FRP.PendingRetention.Safety

/-! Durable deletion acknowledgement provenance for the closed controller. -/
set_option autoImplicit false
namespace FRPSpec.PendingRetention
open PendingCrash PendingMigration

def EntriesAbove (floor : Nat) (entries : Peer) : Prop := ∀ e ∈ entries, floor ≤ e.1

def DeletedPrefix (peer : PeerSnapshot) (target : Nat) : Prop :=
  target ≤ peer.floor ∧ EntriesAbove target peer.entries

def PeerClean (peer : PeerSnapshot) : Prop :=
  peer.pending = none → EntriesAbove peer.floor peer.entries

structure DeletionSafe (s : System) : Prop where
  clean : PeerClean s.peer.selected
  peerOut : ∀ target, ReplyPacket.deleted target ∈ s.peerOut → DeletedPrefix s.peer.selected target
  localIn : ∀ target, ReplyPacket.deleted target ∈ s.localIn → DeletedPrefix s.peer.selected target
  finishing : ∀ target, s.localCause = some (.finish target) → DeletedPrefix s.peer.selected target

theorem EntriesAbove.install {floor identity : Nat} {entries : Peer}
    (h : EntriesAbove floor entries) (above : floor ≤ identity) (entry : Ledger) :
    EntriesAbove floor (PendingCrash.install identity entry entries).1 := by
  induction entries with
  | nil => simpa [PendingCrash.install,EntriesAbove] using above
  | cons e rest ih =>
    rcases e with ⟨key,old⟩
    have head := h (key,old) (by simp)
    have tail : EntriesAbove floor rest := fun e he => h e (by simp [he])
    simp only [PendingCrash.install]
    split
    · simpa [EntriesAbove] using And.intro head tail
    · simpa [EntriesAbove] using And.intro head (ih tail)

theorem EntriesAbove.peerStep {floor identity : Nat} {entries : Peer}
    (h : EntriesAbove floor entries) (above : floor ≤ identity) (command : PeerCommand) :
    EntriesAbove floor (peerStep entries identity command).peer := by
  unfold PendingCrash.peerStep
  repeat' first | exact h | exact h.install above _ | dsimp only | split

theorem DeletedPrefix.lower {peer : PeerSnapshot} {target floor : Nat}
    (clean : EntriesAbove floor peer.entries) (below : target ≤ floor) (covered : floor ≤ peer.floor) :
    DeletedPrefix peer target := ⟨below.trans covered,fun e he => below.trans (clean e he)⟩

theorem PeerEdit.deletion_preserved {cfg : Config} {before after : PeerSnapshot} {cause : PeerCause}
    (edit : PeerEdit cfg before after cause) :
    ∀ target, DeletedPrefix before target → DeletedPrefix after target := by
  intro target h
  cases edit with
  | business changed different =>
    have above := PeerEdit.business_above (.business changed different)
    rcases peerDecision_cases changed with expired | performed
    · omega
    · rw [performed.2.1]
      exact ⟨h.1,h.2.peerStep (h.1.trans above) _⟩
  | floor new increasing => exact ⟨h.1.trans (Nat.le_of_lt increasing),h.2⟩
  | deletion new pending =>
    exact ⟨h.1,fun e he => h.2 e (List.mem_filter.mp he).1⟩

theorem PeerEdit.clean {cfg : Config} {before after : PeerSnapshot} {cause : PeerCause}
    (edit : PeerEdit cfg before after cause) (clean : PeerClean before)
    (pending : ∀ target ∈ before.pending, target = before.floor) : PeerClean after := by
  cases edit with
  | business changed different =>
    have above := PeerEdit.business_above (.business changed different)
    rcases peerDecision_cases changed with expired | performed
    · omega
    · rw [performed.2.1]
      intro none
      exact (clean none).peerStep above _
  | floor => intro impossible; cases impossible
  | deletion target selected =>
    have same := pending target (by simp [selected])
    intro _ e he
    have lower := (List.mem_filter.mp he).2
    simpa [same] using lower

theorem peerDecision_not_deleted {cfg : Config} {before after : PeerSnapshot}
    {identity : Nat} {command : PeerCommand} {reply : ReplyPacket} {effect prevented : Option Bool}
    (changed : peerDecision cfg before identity command = .ok (after,reply,effect,prevented)) :
    ∀ target, reply ≠ .deleted target := by
  rcases peerDecision_cases changed with expired | performed
  · simp [expired.2.2.1]
  · simp [performed.2.2.1]

theorem DeletionSafe.initial : DeletionSafe initial := by
  constructor
  · intro _ e impossible; cases impossible
  · intro t impossible; cases impossible
  · intro t impossible; cases impossible
  · intro t impossible; cases impossible

theorem DeletionSafe.congr {s t : System} (h : DeletionSafe s)
    (peer : t.peer.selected = s.peer.selected) (po : t.peerOut = s.peerOut)
    (li : t.localIn = s.localIn) (cause : t.localCause = s.localCause) : DeletionSafe t := by
  constructor
  · simpa only [peer] using h.clean
  · simpa only [peer,po] using h.peerOut
  · simpa only [peer,li] using h.localIn
  · simpa only [peer,cause] using h.finishing

theorem DeletionSafe.peerExtension {s t : System} (h : DeletionSafe s)
    (clean : PeerClean t.peer.selected)
    (extension : ∀ target, DeletedPrefix s.peer.selected target → DeletedPrefix t.peer.selected target)
    (po : t.peerOut = s.peerOut) (li : t.localIn = s.localIn)
    (cause : t.localCause = s.localCause) : DeletionSafe t :=
  ⟨clean,fun target member => extension target (h.peerOut target (po ▸ member)),
   fun target member => extension target (h.localIn target (li ▸ member)),
   fun target pending => extension target (h.finishing target (cause ▸ pending))⟩

theorem DeletionSafe.pushReply {s : System} (h : DeletionSafe s) (cfg : Config) (reply : ReplyPacket)
    (authentic : ∀ target, reply = .deleted target → DeletedPrefix s.peer.selected target) :
    DeletionSafe (FRPSpec.PendingRetention.pushReply cfg s reply).system := by
  unfold FRPSpec.PendingRetention.pushReply
  split
  · refine ⟨h.clean,?_,h.localIn,h.finishing⟩
    intro target member
    simp only [List.mem_append,List.mem_singleton] at member
    rcases member with old | equal
    · exact h.peerOut target old
    · exact authentic target equal.symm
  · exact h

theorem DeletionSafe.beginLocal {s : System} (h : DeletionSafe s) (target : LocalSnapshot)
    (cause : LocalCause) (authentic : ∀ t, cause = .finish t → DeletedPrefix s.peer.selected t) :
    DeletionSafe (FRPSpec.PendingRetention.beginLocal s target cause).system := by
  refine ⟨h.clean,h.peerOut,h.localIn,?_⟩
  intro t equal
  exact authentic t (Option.some.inj equal)

theorem DeletionSafe.beginPeer {s : System} (h : DeletionSafe s) (target : PeerSnapshot)
    (cause : PeerCause) : DeletionSafe (FRPSpec.PendingRetention.beginPeer s target cause).system :=
  h.congr (PeerBanks.begin_selected _ _) rfl rfl rfl

theorem DeletionSafe.requestStep {s : System} (h : DeletionSafe s) (cfg : Config) :
    DeletionSafe (FRPSpec.PendingRetention.requestStep cfg s).system := by
  unfold FRPSpec.PendingRetention.requestStep
  split
  · exact h
  · cases packets : s.peerIn with
    | nil => exact h
    | cons packet rest =>
      have consumed : DeletionSafe {s with peerIn := rest} := h.congr rfl rfl rfl rfl
      cases packet with
      | business identity command =>
        dsimp only
        split
        · exact h
        · split
          · exact consumed
          · rename_i target reply effect prevented changed
            split
            · exact consumed.pushReply cfg reply (fun t equal =>
                False.elim (peerDecision_not_deleted changed t equal))
            · exact consumed.beginPeer _ _
      | retire target =>
        dsimp only
        split
        · exact h
        · rename_i idle
          split
          · rename_i below
            have clean := h.clean (by simpa using idle)
            apply consumed.pushReply cfg (.deleted target)
            intro t equal
            cases equal
            exact DeletedPrefix.lower clean below (Nat.le_refl _)
          · exact consumed.beginPeer _ _

theorem DeletionSafe.replyStep {s : System} (h : DeletionSafe s) (cfg : Config) :
    DeletionSafe (FRPSpec.PendingRetention.replyStep cfg s).system := by
  unfold FRPSpec.PendingRetention.replyStep
  split
  · exact h
  · cases packets : s.localIn with
    | nil => exact h
    | cons packet rest =>
      have consumed : DeletionSafe {s with localIn := rest} :=
        ⟨h.clean,h.peerOut,fun t ht => h.localIn t (by simp [packets,ht]),h.finishing⟩
      cases packet with
      | expired i f => exact consumed
      | receipt receipt =>
        dsimp only
        split
        · exact consumed
        · split
          · exact consumed
          · exact consumed.beginLocal _ _ (by intro t impossible; cases impossible)
      | deleted target =>
        dsimp only
        split
        · exact consumed
        · apply consumed.beginLocal _ _
          intro t equal
          cases equal
          exact h.localIn target (by simp [packets])

theorem DeletionSafe.localStep {s : System} (h : DeletionSafe s) (cfg : Config) (c : LocalCommand) :
    DeletionSafe (FRPSpec.PendingRetention.localStep cfg s c).system := by
  unfold FRPSpec.PendingRetention.localStep
  dsimp only
  split
  · exact h
  · split
    · exact h
    · split
      · split
        · exact h
        · split
          · exact h
          · apply DeletionSafe.beginLocal
            · exact h.congr rfl rfl rfl rfl
            · intro t impossible; cases impossible
      · apply h.beginLocal
        intro t impossible; cases impossible

theorem DeletionSafe.duplicate {s : System} (h : DeletionSafe s) (cfg : Config)
    (queue : Queue) (index : Nat) :
    DeletionSafe (duplicateQueue cfg s queue index).system := by
  cases queue <;> simp only [duplicateQueue]
  all_goals split
  all_goals first
    | exact h
    | (rename_i t eq
       obtain ⟨items,produced,rfl⟩ := Option.map_eq_some_iff.mp eq
       first
       | exact h.congr rfl rfl rfl rfl
       | exact ⟨h.clean,fun target member =>
           duplicateList_all (P := fun (r : ReplyPacket) => ∀ t : Nat, r = ReplyPacket.deleted t → DeletedPrefix s.peer.selected t)
             (fun r hr t equal => h.peerOut t (by simpa only [equal] using hr)) produced _ member target rfl,
           h.localIn,h.finishing⟩
       | exact ⟨h.clean,h.peerOut,fun target member =>
           duplicateList_all (P := fun (r : ReplyPacket) => ∀ t : Nat, r = ReplyPacket.deleted t → DeletedPrefix s.peer.selected t)
             (fun r hr t equal => h.localIn t (by simpa only [equal] using hr)) produced _ member target rfl,
           h.finishing⟩)

theorem DeletionSafe.nonprogress {s : System} (h : DeletionSafe s) (cfg : Config)
    (command : Command) (ordinary : command ≠ .progress) :
    DeletionSafe (step cfg s command).system := by
  cases command with
  | «local» c => exact h.localStep cfg c
  | deliverRequest => exact h.requestStep cfg
  | deliverReply => exact h.replyStep cfg
  | duplicate q i => exact h.duplicate cfg q i
  | progress => exact False.elim (ordinary rfl)
  | transferReply =>
    simp only [step]
    split
    · exact h
    · cases packets : s.peerOut with
      | nil => exact h
      | cons packet rest =>
        refine ⟨h.clean,fun t ht => h.peerOut t (by simp [packets,ht]),?_,h.finishing⟩
        intro t member
        simp only [List.mem_append,List.mem_singleton] at member
        rcases member with old | equal
        · exact h.localIn t old
        · exact h.peerOut t (by simp [packets,equal])
  | drop q =>
    cases q
    · exact h.congr rfl rfl rfl rfl
    · exact h.congr rfl rfl rfl rfl
    · exact ⟨h.clean,fun t ht => h.peerOut t (List.mem_of_mem_tail ht),h.localIn,h.finishing⟩
    · exact ⟨h.clean,h.peerOut,fun t ht => h.localIn t (List.mem_of_mem_tail ht),h.finishing⟩
  | crashLocal => exact ⟨h.clean,h.peerOut,h.localIn,by intro t impossible; cases impossible⟩
  | crashPeer => exact h.congr rfl rfl rfl rfl
  | send | relinquishBefore | retryRetirement | resumeDeletion | transferRequest |
    recoverLocal | recoverPeer | cleanup | inspect | query | malformed =>
    simp only [step,startRetirement,pushRequest]
    repeat' first | exact h.congr rfl rfl rfl rfl | dsimp only | split

theorem DeletionSafe.localPublished {s : System} (h : DeletionSafe s) (cause : LocalCause) :
    DeletionSafe (FRPSpec.PendingRetention.localPublished s cause).system := by
  cases cause with
  | frame c => cases c <;> exact ⟨h.clean,h.peerOut,h.localIn,by intro t impossible; cases impossible⟩
  | relinquish => exact ⟨h.clean,h.peerOut,h.localIn,by intro t impossible; cases impossible⟩
  | finish => exact ⟨h.clean,h.peerOut,h.localIn,by intro t impossible; cases impossible⟩

theorem PeerEdit.business_not_deleted {cfg : Config} {before after : PeerSnapshot}
    {identity : Nat} {command : PeerCommand} {reply : ReplyPacket} {effect prevented : Option Bool}
    (edit : PeerEdit cfg before after (.business identity command reply effect prevented)) :
    ∀ target, reply ≠ .deleted target := by
  cases edit with
  | business changed different => exact peerDecision_not_deleted changed

theorem PeerEdit.deleted {cfg : Config} {before after : PeerSnapshot} {target : Nat}
    (edit : PeerEdit cfg before after (.deletion target))
    (pending : ∀ t ∈ before.pending, t = before.floor) : DeletedPrefix after target := by
  cases edit
  rename_i selected
  have same := pending target (by simp [selected])
  refine ⟨by simp [same],?_⟩
  intro e he
  exact of_decide_eq_true (List.mem_filter.mp he).2

theorem DeletionSafe.peerPublished {cfg : Config} {s : System} (h : DeletionSafe s)
    (bank : PeerBanks) (cause : PeerCause) (edit : PeerEdit cfg s.peer.selected bank.selected cause)
    (pending : ∀ target ∈ s.peer.selected.pending, target = s.peer.selected.floor) :
    DeletionSafe (FRPSpec.PendingRetention.peerPublished cfg {s with peer := bank} cause).system := by
  have base : DeletionSafe {s with peer := bank,peerCause := none} :=
    h.peerExtension (edit.clean h.clean pending) edit.deletion_preserved rfl rfl rfl
  cases cause with
  | business identity command reply effect prevented =>
    apply base.pushReply cfg reply
    intro t equal
    exact False.elim (edit.business_not_deleted t equal)
  | floor => exact base
  | deletion target =>
    apply base.pushReply cfg (.deleted target)
    intro t equal
    cases equal
    exact edit.deleted pending

theorem DeletionSafe.scan {s : System} (h : DeletionSafe s) (target cursor : Nat) :
    DeletionSafe (scanRetirement s target cursor).system := by
  unfold scanRetirement
  repeat' first
    | exact h.congr rfl rfl rfl rfl
    | (apply DeletionSafe.beginLocal
       · exact h.congr rfl rfl rfl rfl
       · intro t impossible; cases impossible)
    | dsimp only
    | split

theorem DeletionSafe.progress {cfg : Config} {s : System} {history : Peer}
    (h : DeletionSafe s) (safe : Safe cfg s history) :
    DeletionSafe (progress cfg s).system := by
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
          · have next : DeletionSafe {s with localBank := s.localBank.progress.1} :=
              h.congr rfl rfl rfl rfl
            simpa only [scan,localCause] using next.localPublished cause
          · simpa only [scan,localCause] using h.congr
              (t := {s with localBank := s.localBank.progress.1}) rfl rfl rfl rfl
      | none =>
        dsimp only
        cases peerCause : s.peerCause with
        | none => exact h
        | some cause =>
          dsimp only
          split
          · exact h
          · split
            · rename_i published
              simpa only [scan,localCause,peerCause] using h.peerPublished _ cause
                ((peerCause ▸ safe.staging.2).publication published) safe.semantic.relation.peerPending
            · rename_i silent
              simpa only [scan,localCause,peerCause] using h.congr
                (t := {s with peer := s.peer.progress.1})
                (s.peer.progress_stutters (Bool.eq_false_iff.mpr silent)) rfl rfl rfl

theorem DeletionSafe.step {cfg : Config} {s : System} {history : Peer}
    (h : DeletionSafe s) (safe : Safe cfg s history) (command : Command) :
    DeletionSafe (FRPSpec.PendingRetention.step cfg s command).system := by
  by_cases advancing : command = .progress
  · subst command; exact h.progress safe
  · exact h.nonprogress cfg command advancing

theorem initial_execution_deletion (cfg : Config) (commands : List Command) :
    DeletionSafe (execute cfg initial commands).system := by
  have paired := execute_induction cfg (fun s history => Safe cfg s history ∧ DeletionSafe s)
    (fun _ _ command h => ⟨h.1.step command,h.2.step h.1 command⟩)
    initial [] commands ⟨Safe.initial cfg,DeletionSafe.initial⟩
  exact paired.2

set_option maxHeartbeats 800000 in
theorem retirementComplete_witness (cfg : Config) (s : System) (command : Command) (target : Nat)
    (completed : (step cfg s command).observation = .retirementComplete target) :
    s.localCause = some (.finish target) ∧ (step cfg s command).system.peer.selected = s.peer.selected := by
  cases command <;>
    simp only [step,localStep,startRetirement,requestStep,replyStep,progress,scanRetirement,
      localPublished,peerPublished,pushRequest,pushReply,beginLocal,beginPeer,duplicateQueue,reject] at *
  all_goals repeat' first | contradiction | simp_all | split at completed

/-- A reported retirement completion certifies the selected peer floor and
absence of every entry in that prefix from the selected peer snapshot, for
the actual command trace. -/
theorem initial_retirement_complete (cfg : Config) (commands : List Command)
    (command : Command) (target : Nat)
    (completed : (step cfg (execute cfg initial commands).system command).observation = .retirementComplete target) :
    DeletedPrefix (step cfg (execute cfg initial commands).system command).system.peer.selected target := by
  obtain ⟨cause,peerSame⟩ := retirementComplete_witness cfg _ command target completed
  rw [peerSame]
  exact (initial_execution_deletion cfg commands).finishing target cause

/-- Pending retirement cannot admit another request, including before the
peer acknowledgement or while the local completion bank is being copied. -/
theorem pending_blocks_admission (cfg : Config) (s : System) (target : Nat) (input : Bool)
    (pending : s.localBank.selected.pending = some target) :
    (step cfg s (.local (.accept input))).observation = .refused .busy := by
  simp only [step,localStep,LocalCommand.frameCommand]
  split
  · rfl
  · simp [localChange,localChangeCore,pending,reject]

theorem finishRetirement_pending {before after : LocalSnapshot} {target : Nat}
    (changed : finishRetirement before target = some after) : before.pending = some target := by
  unfold finishRetirement at changed
  split at changed <;> first | contradiction | simpa using (by assumption : (before.pending == some target) = true)

theorem LocalEdit.pending_cleared {cfg : Config} {before after : LocalSnapshot}
    {cause : LocalCause} {target : Nat} (edit : LocalEdit cfg before after cause)
    (pending : before.pending = some target) (cleared : after.pending = none) :
    cause = .finish target := by
  cases edit with
  | frame changed => simp [(localChange_metadata changed).2,pending] at cleared
  | relinquish => cases cleared
  | finish changed =>
    have equal := Option.some.inj ((finishRetirement_pending changed).symm.trans pending)
    cases equal
    rfl

theorem localPublished_localBank (s : System) (cause : LocalCause) :
    (localPublished s cause).system.localBank = s.localBank := by
  cases cause with
  | frame command => cases command <;> rfl
  | relinquish => rfl
  | finish => rfl

theorem peerPublished_localBank (cfg : Config) (s : System) (cause : PeerCause) :
    (peerPublished cfg s cause).system.localBank = s.localBank := by
  cases cause <;> simp only [peerPublished,pushReply]
  all_goals repeat' first | rfl | split

theorem scanRetirement_selected (s : System) (target cursor : Nat) :
    (scanRetirement s target cursor).system.localBank.selected = s.localBank.selected := by
  unfold scanRetirement
  repeat' first | rfl | dsimp only | split

theorem progress_pending_cleared {cfg : Config} {s : System} {target : Nat}
    (staged : Staging cfg s) (pending : s.localBank.selected.pending = some target)
    (cleared : (progress cfg s).system.localBank.selected.pending = none) :
    (progress cfg s).observation = .retirementComplete target := by
  unfold progress at cleared ⊢
  split
  · simp_all [reject]
  · rename_i running
    simp only [running] at cleared
    cases scan : s.retirementScan with
    | some pair =>
      rcases pair with ⟨t,cursor⟩
      simp only [scan] at cleared
      dsimp only at cleared ⊢
      split
      · simp_all [reject]
      · have selected := scanRetirement_selected s t cursor
        simp_all
    | none =>
      simp only [scan] at cleared
      dsimp only at cleared ⊢
      cases localCause : s.localCause with
      | some cause =>
        simp only [localCause] at cleared
        dsimp only at cleared ⊢
        split
        · simp_all [reject]
        · rename_i awake
          simp only [awake] at cleared
          split
          · rename_i published
            have clear : s.localBank.progress.1.selected.pending = none := by
              simpa [published,localPublished_localBank] using cleared
            have finish := ((localCause ▸ staged.1).publication published).pending_cleared pending clear
            subst cause
            rfl
          · rename_i silent
            have stutter := s.localBank.progress_stutters (Bool.eq_false_iff.mpr silent)
            simp_all
      | none =>
        simp only [localCause] at cleared
        dsimp only at cleared ⊢
        cases peerCause : s.peerCause with
        | none => simp_all
        | some cause =>
          simp only [peerCause] at cleared
          dsimp only at cleared ⊢
          split
          · simp_all [reject]
          · rename_i awake
            simp only [awake] at cleared
            split <;> simp_all [peerPublished_localBank]

/-- The pending target can become clear only at its exact completion event.
Combined with completion provenance, this is the admission-reopening barrier. -/
theorem initial_pending_cleared (cfg : Config) (commands : List Command) (command : Command) (target : Nat)
    (pending : (execute cfg initial commands).system.localBank.selected.pending = some target)
    (cleared : (step cfg (execute cfg initial commands).system command).system.localBank.selected.pending = none) :
    (step cfg (execute cfg initial commands).system command).observation = .retirementComplete target ∧
      DeletedPrefix (step cfg (execute cfg initial commands).system command).system.peer.selected target := by
  have completed : (step cfg (execute cfg initial commands).system command).observation = .retirementComplete target := by
    by_cases advancing : command = .progress
    · subst command
      exact progress_pending_cleared (initial_execution_safe cfg commands).staging pending cleared
    · have same := (step_nonprogress_selected cfg (execute cfg initial commands).system command advancing).1
      rw [same,pending] at cleared
      cases cleared
  exact ⟨completed,initial_retirement_complete cfg commands command target completed⟩

/-- An empty initial peer cannot certify a nonempty retired prefix. -/
example : ¬DeletedPrefix ({} : PeerSnapshot) 1 := by
  intro certified
  have impossible := certified.1
  contradiction

example (cfg : Config) (commands : List Command) (target : Nat)
    (queued : ReplyPacket.deleted target ∈ (execute cfg initial commands).system.localIn) :
    DeletedPrefix (execute cfg initial commands).system.peer.selected target :=
  (initial_execution_deletion cfg commands).localIn target queued

end FRPSpec.PendingRetention
