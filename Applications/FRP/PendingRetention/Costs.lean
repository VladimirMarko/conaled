import Applications.FRP.PendingRetention.Encoding
import Mathlib.Data.Fintype.Vector
import Mathlib.Data.Fintype.Pi

/-! Executed work and fixed-region representation of the same closed executor.
Traces are observer output. They are never fields of the running service. -/
namespace FRPSpec.PendingRetention
open PendingCrash PendingMigration

/-- Pricing is applied to emitted work, including refused and interrupted work.
No operation-level tariff replaces the events of the actual executor. -/
def bill (price : Event → Nat) (events : List Event) : Nat :=
  (events.map price).sum

@[simp] theorem bill_append (price : Event → Nat) (xs ys : List Event) :
    bill price (xs ++ ys) = bill price xs + bill price ys := by
  simp [bill]

def executionBill (price : Event → Nat) (cfg : Config) (s : System) (cs : List Command) : Nat :=
  bill price (execute cfg s cs).events

theorem executionBill_append (price : Event → Nat) (cfg : Config) (s : System)
    (xs ys : List Command) :
    executionBill price cfg s (xs ++ ys) = executionBill price cfg s xs +
      executionBill price cfg (execute cfg s xs).system ys := by
  simp [executionBill, execute_append]

theorem executionBill_cons (price : Event → Nat) (cfg : Config) (s : System)
    (c : Command) (cs : List Command) :
    executionBill price cfg s (c :: cs) = bill price (step cfg s c).events +
      executionBill price cfg (step cfg s c).system cs := by
  simp [executionBill, execute]

/-- A fixed-cell work interpretation. Variable-size events count their visited
or copied slots; the other constructors denote one named bounded primitive.
This is not a CPU instruction count or a bound on Lean's heap allocator. -/
def cellWork : Event → Nat
  | .scan n | .copy n | .allocate n | .release n => n
  | _ => 1

/-- Separate resource dimensions retain scan and copy counts without choosing
exchange rates between them and the named fixed-size primitives. -/
inductive WorkDimension where
  | scans | copies | allocations | releases | primitives
  deriving DecidableEq, Repr

def dimensionPrice : WorkDimension → Event → Nat
  | .scans, .scan n => n
  | .copies, .copy n => n
  | .allocations, .allocate n => n
  | .releases, .release n => n
  | .primitives, .scan _ | .primitives, .copy _
  | .primitives, .allocate _ | .primitives, .release _ => 0
  | .primitives, _ => 1
  | _, _ => 0

def executionWork (cfg : Config) (s : System) (cs : List Command) : WorkDimension → Nat :=
  fun d => executionBill (dimensionPrice d) cfg s cs

theorem executionWork_append (cfg : Config) (s : System) (xs ys : List Command)
    (dimension : WorkDimension) :
    executionWork cfg s (xs ++ ys) dimension = executionWork cfg s xs dimension +
      executionWork cfg (execute cfg s xs).system ys dimension :=
  executionBill_append _ cfg s xs ys

/-- Failed work is retained when a later command crashes the service. -/
theorem failed_work_survives_suffix (cfg : Config) (s : System)
    (before after : List Command) :
    executionBill cellWork cfg s before ≤ executionBill cellWork cfg s (before ++ after) := by
  rw [executionBill_append]
  exact Nat.le_add_right _ _

example : executionBill cellWork ⟨4,3,2⟩ initial [.duplicate .localOut 0] = 2 := by decide
example : executionBill cellWork ⟨4,3,2⟩ initial
    [.duplicate .localOut 0,.crashLocal,.recoverLocal] = 5 := by decide

/-- All headers, including the inactive bank and unfinished copy, are charged. -/
def LocalHeaderBound (cfg : Config) (h : LocalHeader) : Prop :=
  h.1.Valid ∧ h.1.nextIdentity ≤ cfg.lifetime ∧ h.2.1 ≤ cfg.lifetime ∧
    ∀ n ∈ h.2.2, n ≤ cfg.lifetime

def PeerHeaderBound (cfg : Config) (h : PeerHeader) : Prop :=
  h.1 ≤ cfg.lifetime ∧ ∀ n ∈ h.2, n ≤ cfg.lifetime

def LocalBanksBound (cfg : Config) (b : LocalBanks) : Prop :=
  b.Bounded (LocalHeaderBound cfg) (fun r => r.identity ≤ cfg.lifetime) cfg.outcomeCapacity

def PeerBanksBound (cfg : Config) (b : PeerBanks) : Prop :=
  b.Bounded (PeerHeaderBound cfg) (fun r => r.1 ≤ cfg.lifetime) cfg.outcomeCapacity

@[simp] theorem local_payload_bound (cfg : Config) (s : LocalSnapshot) :
    s.encode.Bounded (LocalHeaderBound cfg) (fun r => r.identity ≤ cfg.lifetime)
      cfg.outcomeCapacity ↔ LocalBound cfg s := by
  simp [Durability.SnapshotBanks.Snapshot.Bounded, LocalHeaderBound, LocalSnapshot.encode, LocalBound, and_assoc]

@[simp] theorem peer_payload_bound (cfg : Config) (s : PeerSnapshot) :
    s.encode.Bounded (PeerHeaderBound cfg) (fun r => r.1 ≤ cfg.lifetime)
      cfg.outcomeCapacity ↔ PeerBound cfg s := by
  simp [Durability.SnapshotBanks.Snapshot.Bounded, PeerHeaderBound, PeerSnapshot.encode, PeerBound, and_assoc]

theorem LocalBanksBound.selected {cfg : Config} {b : LocalBanks}
    (h : LocalBanksBound cfg b) : LocalBound cfg b.selected := by
  exact (local_payload_bound cfg b.selected).mp (h.1.1 b.state.disk.selected)

theorem PeerBanksBound.selected {cfg : Config} {b : PeerBanks}
    (h : PeerBanksBound cfg b) : PeerBound cfg b.selected := by
  exact (peer_payload_bound cfg b.selected).mp (h.1.1 b.state.disk.selected)

theorem local_seed_bound (cfg : Config) : LocalHeaderBound cfg localSeed := by
  simp [LocalHeaderBound, localSeed, Frame.Valid, initialFrame, Slots.get]

theorem peer_seed_bound (cfg : Config) : PeerHeaderBound cfg peerSeed := by
  simp [PeerHeaderBound, peerSeed]

theorem LocalBanksBound.begin {cfg : Config} {b : LocalBanks} {t : LocalSnapshot}
    (hb : LocalBanksBound cfg b) (ht : LocalBound cfg t) : LocalBanksBound cfg (b.begin t) :=
  Durability.SnapshotBanks.begin_bounded localSeed _ _ _ _ _ (local_seed_bound cfg) hb.1.1
    ((local_payload_bound cfg t).mpr ht)

theorem PeerBanksBound.begin {cfg : Config} {b : PeerBanks} {t : PeerSnapshot}
    (hb : PeerBanksBound cfg b) (ht : PeerBound cfg t) : PeerBanksBound cfg (b.begin t) :=
  Durability.SnapshotBanks.begin_bounded peerSeed _ _ _ _ _ (peer_seed_bound cfg) hb.1.1
    ((peer_payload_bound cfg t).mpr ht)

theorem LocalBanksBound.progress {cfg : Config} {b : LocalBanks}
    (h : LocalBanksBound cfg b) : LocalBanksBound cfg b.progress.1 :=
  Durability.SnapshotBanks.Worker.progress_bounded _ _ _ _ h

theorem PeerBanksBound.progress {cfg : Config} {b : PeerBanks}
    (h : PeerBanksBound cfg b) : PeerBanksBound cfg b.progress.1 :=
  Durability.SnapshotBanks.Worker.progress_bounded _ _ _ _ h

def LocalCauseBound (cfg : Config) : LocalCause → Prop
  | .frame c => CommandBound cfg c
  | .relinquish t | .finish t => t ≤ cfg.lifetime

def PeerCauseBound (cfg : Config) : PeerCause → Prop
  | .business i _ r _ _ => i ≤ cfg.lifetime ∧ ReplyBound cfg r
  | .floor t | .deletion t => t ≤ cfg.lifetime

/-- Representation bounds only: source provenance is a separate invariant. -/
structure ResourceBound (cfg : Config) (s : System) : Prop where
  localBanksBound : LocalBanksBound cfg s.localBank
  peerBanksBound : PeerBanksBound cfg s.peer
  localCause : ∀ c ∈ s.localCause, LocalCauseBound cfg c
  peerCause : ∀ c ∈ s.peerCause, PeerCauseBound cfg c
  localOut : s.localOut.length ≤ cfg.queueCapacity ∧ ∀ p ∈ s.localOut, RequestBound cfg p
  peerIn : s.peerIn.length ≤ cfg.queueCapacity ∧ ∀ p ∈ s.peerIn, RequestBound cfg p
  peerOut : s.peerOut.length ≤ cfg.queueCapacity ∧ ∀ p ∈ s.peerOut, ReplyBound cfg p
  localIn : s.localIn.length ≤ cfg.queueCapacity ∧ ∀ p ∈ s.localIn, ReplyBound cfg p
  retirement : ∀ p ∈ s.retirementScan, p.1 ≤ cfg.lifetime ∧ p.2 ≤ cfg.lifetime


theorem ResourceBound.beginLocal {cfg : Config} {s : System} (hs : ResourceBound cfg s)
    (t : LocalSnapshot) (c : LocalCause) (ht : LocalBound cfg t) (hc : LocalCauseBound cfg c) :
    ResourceBound cfg (beginLocal s t c).system := by
  exact ⟨hs.localBanksBound.begin ht,hs.peerBanksBound,by simpa [FRPSpec.PendingRetention.beginLocal] using hc,
    hs.peerCause,hs.localOut,hs.peerIn,hs.peerOut,hs.localIn,hs.retirement⟩

theorem ResourceBound.beginPeer {cfg : Config} {s : System} (hs : ResourceBound cfg s)
    (t : PeerSnapshot) (c : PeerCause) (ht : PeerBound cfg t) (hc : PeerCauseBound cfg c) :
    ResourceBound cfg (beginPeer s t c).system := by
  exact ⟨hs.localBanksBound,hs.peerBanksBound.begin ht,hs.localCause,by simpa [FRPSpec.PendingRetention.beginPeer] using hc,
    hs.localOut,hs.peerIn,hs.peerOut,hs.localIn,hs.retirement⟩

theorem ResourceBound.pushRequest {cfg : Config} {s : System} (hs : ResourceBound cfg s)
    (p : RequestPacket) (hp : RequestBound cfg p) :
    ResourceBound cfg (pushRequest cfg s p).system := by
  unfold FRPSpec.PendingRetention.pushRequest
  split
  · refine ⟨hs.localBanksBound,hs.peerBanksBound,hs.localCause,hs.peerCause,?_,hs.peerIn,
      hs.peerOut,hs.localIn,hs.retirement⟩
    constructor
    · simp only [List.length_append,List.length_singleton]; omega
    · intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hs.localOut.2 x hx
      · exact (List.mem_singleton.mp hx).symm ▸ hp
  · exact hs

theorem ResourceBound.pushReply {cfg : Config} {s : System} (hs : ResourceBound cfg s)
    (p : ReplyPacket) (hp : ReplyBound cfg p) :
    ResourceBound cfg (pushReply cfg s p).system := by
  unfold FRPSpec.PendingRetention.pushReply
  split
  · refine ⟨hs.localBanksBound,hs.peerBanksBound,hs.localCause,hs.peerCause,hs.localOut,hs.peerIn,
      ?_,hs.localIn,hs.retirement⟩
    constructor
    · simp only [List.length_append,List.length_singleton]; omega
    · intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hs.peerOut.2 x hx
      · exact (List.mem_singleton.mp hx).symm ▸ hp
  · exact hs


theorem ResourceBound.localStep {cfg : Config} {s : System} (hs : ResourceBound cfg s)
    (c : LocalCommand) : ResourceBound cfg (localStep cfg s c).system := by
  unfold FRPSpec.PendingRetention.localStep
  dsimp only
  split
  · exact hs
  · split
    · exact hs
    · rename_i t ht
      have hb := localChange_bound ht
      have hc : LocalCauseBound cfg (.frame c.frameCommand) := by
        cases c <;> trivial
      cases c <;> simp only
      all_goals try exact hs.beginLocal _ _ hb hc
      split
      · exact hs
      · split
        · exact hs
        · exact (show ResourceBound cfg {s with prepared := some _} from
            ⟨hs.localBanksBound,hs.peerBanksBound,hs.localCause,hs.peerCause,hs.localOut,hs.peerIn,
              hs.peerOut,hs.localIn,hs.retirement⟩).beginLocal _ _ hb hc

theorem ResourceBound.startRetirement {cfg : Config} {s : System} (hs : ResourceBound cfg s)
    (target : Nat) : ResourceBound cfg (startRetirement s target).system := by
  unfold FRPSpec.PendingRetention.startRetirement
  dsimp only
  repeat' first | split | exact hs
  rename_i h₁ h₂ h₃ h₄
  refine ⟨hs.localBanksBound,hs.peerBanksBound,hs.localCause,hs.peerCause,hs.localOut,hs.peerIn,
    hs.peerOut,hs.localIn,?_⟩
  intro p hp
  simp only [Option.mem_def,Option.some.injEq] at hp
  subst p
  have hb := hs.localBanksBound.selected
  exact ⟨by have := hb.2.1; omega,hb.2.2.1⟩

theorem ResourceBound.scanRetirement {cfg : Config} {s : System} (hs : ResourceBound cfg s)
    (target cursor : Nat) (ht : target ≤ cfg.lifetime) :
    ResourceBound cfg (scanRetirement s target cursor).system := by
  have cleared : ResourceBound cfg {s with retirementScan := none} :=
    ⟨hs.localBanksBound,hs.peerBanksBound,hs.localCause,hs.peerCause,hs.localOut,hs.peerIn,
      hs.peerOut,hs.localIn,by simp⟩
  unfold FRPSpec.PendingRetention.scanRetirement
  dsimp only
  split
  · split
    · exact cleared
    · split
      · refine ⟨hs.localBanksBound,hs.peerBanksBound,hs.localCause,hs.peerCause,hs.localOut,hs.peerIn,
          hs.peerOut,hs.localIn,?_⟩
        intro p hp
        simp only [Option.mem_def,Option.some.injEq] at hp
        subst p
        exact ⟨ht,by omega⟩
      · exact cleared
  · apply cleared.beginLocal
    · have hb := hs.localBanksBound.selected
      exact ⟨hb.1,hb.2.1,ht,by simpa using ht,hb.2.2.2.2⟩
    · exact ht


theorem ResourceBound.requestStep {cfg : Config} {s : System} (hs : ResourceBound cfg s) :
    ResourceBound cfg (requestStep cfg s).system := by
  unfold FRPSpec.PendingRetention.requestStep
  dsimp only
  split
  · exact hs
  · cases he : s.peerIn with
    | nil => exact hs
    | cons packet rest =>
      have hp := hs.peerIn.2 packet (by simp [he])
      have consumed : ResourceBound cfg {s with peerIn := rest} := by
        refine ⟨hs.localBanksBound,hs.peerBanksBound,hs.localCause,hs.peerCause,hs.localOut,?_,
          hs.peerOut,hs.localIn,hs.retirement⟩
        exact ⟨by have := hs.peerIn.1; simp [he] at this; dsimp only; omega,
          fun p h => hs.peerIn.2 p (by simp [he,h])⟩
      cases packet with
      | business identity command =>
        dsimp only
        split
        · exact hs
        · split
          · exact consumed
          · rename_i t reply effect prevented hd
            have hb := peerDecision_bound hd
            split
            · exact consumed.pushReply _ hb.2
            · exact consumed.beginPeer _ _ hb.1 ⟨hp,hb.2⟩
      | retire target =>
        dsimp only
        split
        · exact hs
        · split
          · exact consumed.pushReply _ hp
          · apply consumed.beginPeer
            · have hb := hs.peerBanksBound.selected
              exact ⟨hp,by simpa [RequestBound] using hp,hb.2.2⟩
            · exact hp

theorem finishRetirement_bound {cfg : Config} {s t : LocalSnapshot} {target : Nat}
    (hs : LocalBound cfg s) (ht : finishRetirement s target = some t) : LocalBound cfg t := by
  unfold finishRetirement at ht
  split at ht
  · cases ht
    refine ⟨hs.1,hs.2.1,hs.2.2.1,by simp,?_,?_⟩
    · exact (List.length_filter_le _ _).trans hs.2.2.2.2.1
    · intro r hr
      exact hs.2.2.2.2.2 r (List.mem_of_mem_filter hr)
  · contradiction

theorem ResourceBound.replyStep {cfg : Config} {s : System} (hs : ResourceBound cfg s) :
    ResourceBound cfg (replyStep cfg s).system := by
  unfold FRPSpec.PendingRetention.replyStep
  dsimp only
  split
  · exact hs
  · cases he : s.localIn with
    | nil => exact hs
    | cons packet rest =>
      have hp := hs.localIn.2 packet (by simp [he])
      have consumed : ResourceBound cfg {s with localIn := rest} := by
        refine ⟨hs.localBanksBound,hs.peerBanksBound,hs.localCause,hs.peerCause,hs.localOut,hs.peerIn,
          hs.peerOut,?_,hs.retirement⟩
        exact ⟨by have := hs.localIn.1; simp [he] at this; dsimp only; omega,
          fun p h => hs.localIn.2 p (by simp [he,h])⟩
      cases packet with
      | expired i floor => exact consumed
      | deleted target =>
        dsimp only
        split
        · exact consumed
        · rename_i next hn
          exact consumed.beginLocal _ _ (finishRetirement_bound hs.localBanksBound.selected hn) hp
      | receipt receipt =>
        dsimp only
        split
        · exact consumed
        · split
          · exact consumed
          · rename_i next hn
            exact consumed.beginLocal _ _ (localChange_bound hn) hp


theorem ResourceBound.localPublished {cfg : Config} {s : System} (hs : ResourceBound cfg s)
    (cause : LocalCause) : ResourceBound cfg (localPublished s cause).system := by
  have base : ResourceBound cfg {s with localCause := none, active := some (reconstruct s.localBank.selected.frame), prepared := none} :=
    ⟨hs.localBanksBound,hs.peerBanksBound,by simp,hs.peerCause,hs.localOut,hs.peerIn,
      hs.peerOut,hs.localIn,hs.retirement⟩
  unfold FRPSpec.PendingRetention.localPublished
  cases cause with
  | frame c => cases c <;> exact ⟨hs.localBanksBound,hs.peerBanksBound,by simp,hs.peerCause,
      hs.localOut,hs.peerIn,hs.peerOut,hs.localIn,hs.retirement⟩
  | relinquish _ => exact base
  | finish _ => exact base

theorem ResourceBound.peerPublished {cfg : Config} {s : System} (hs : ResourceBound cfg s)
    (cause : PeerCause) (hc : PeerCauseBound cfg cause) :
    ResourceBound cfg (peerPublished cfg s cause).system := by
  have base : ResourceBound cfg {s with peerCause := none} :=
    ⟨hs.localBanksBound,hs.peerBanksBound,hs.localCause,by simp,hs.localOut,hs.peerIn,
      hs.peerOut,hs.localIn,hs.retirement⟩
  cases cause with
  | business i c r e p => exact base.pushReply _ hc.2
  | floor _ => exact base
  | deletion _ => exact base.pushReply _ hc

theorem ResourceBound.progress {cfg : Config} {s : System} (hs : ResourceBound cfg s) :
    ResourceBound cfg (progress cfg s).system := by
  unfold FRPSpec.PendingRetention.progress
  dsimp only
  split
  · exact hs
  · cases hr : s.retirementScan with
    | some pair =>
      dsimp only
      split
      · exact hs
      · exact hs.scanRetirement _ _ (hs.retirement pair hr).1
    | none =>
      dsimp only
      cases hl : s.localCause with
      | some cause =>
        dsimp only
        split
        · exact hs
        · have next : ResourceBound cfg {s with localBank := s.localBank.progress.1} :=
            ⟨hs.localBanksBound.progress,hs.peerBanksBound,hs.localCause,hs.peerCause,hs.localOut,
              hs.peerIn,hs.peerOut,hs.localIn,hs.retirement⟩
          split
          · simpa only [hr,hl] using next.localPublished cause
          · simpa only [hr,hl] using next
      | none =>
        dsimp only
        cases hp : s.peerCause with
        | some cause =>
          dsimp only
          split
          · exact hs
          · have next : ResourceBound cfg {s with peer := s.peer.progress.1} :=
              ⟨hs.localBanksBound,hs.peerBanksBound.progress,hs.localCause,hs.peerCause,hs.localOut,
                hs.peerIn,hs.peerOut,hs.localIn,hs.retirement⟩
            split
            · simpa only [hr,hl,hp] using next.peerPublished cause (hs.peerCause cause hp)
            · simpa only [hr,hl,hp] using next
        | none => exact hs


theorem LocalBanksBound.crash {cfg : Config} {b : LocalBanks}
    (h : LocalBanksBound cfg b) : LocalBanksBound cfg b.crash :=
  idle_bounded _ _ _ _ _ (local_seed_bound cfg) h.1.1

theorem PeerBanksBound.crash {cfg : Config} {b : PeerBanks}
    (h : PeerBanksBound cfg b) : PeerBanksBound cfg b.crash :=
  idle_bounded _ _ _ _ _ (peer_seed_bound cfg) h.1.1

theorem duplicateList_bound {α : Type} (p : α → Prop) {capacity index : Nat} {xs ys : List α}
    (hx : xs.length ≤ capacity ∧ ∀ x ∈ xs,p x)
    (h : duplicateList capacity index xs = some ys) :
    ys.length ≤ capacity ∧ ∀ y ∈ ys,p y := by
  unfold duplicateList at h
  split at h
  · simp at h
  · simp only [Option.bind_eq_bind] at h
    cases he : xs[index]? with
    | none => simp [he] at h
    | some x =>
      simp [he] at h
      subst ys
      constructor
      · simp only [List.length_append,List.length_singleton]; omega
      · intro y hy
        rcases List.mem_append.mp hy with hy | hy
        · exact hx.2 y hy
        · have eq := List.mem_singleton.mp hy
          subst y
          exact hx.2 x (List.mem_of_getElem? he)

theorem ResourceBound.duplicateQueue {cfg : Config} {s : System} (hs : ResourceBound cfg s)
    (queue : Queue) (index : Nat) : ResourceBound cfg (duplicateQueue cfg s queue index).system := by
  cases queue <;> unfold FRPSpec.PendingRetention.duplicateQueue
  all_goals dsimp only
  all_goals split
  all_goals try exact hs
  all_goals rename_i next hn
  all_goals simp only [Option.map_eq_some_iff] at hn
  all_goals obtain ⟨q,hq,rfl⟩ := hn
  · exact ⟨hs.localBanksBound,hs.peerBanksBound,hs.localCause,hs.peerCause,
      duplicateList_bound _ hs.localOut hq,hs.peerIn,hs.peerOut,hs.localIn,hs.retirement⟩
  · exact ⟨hs.localBanksBound,hs.peerBanksBound,hs.localCause,hs.peerCause,
      hs.localOut,duplicateList_bound _ hs.peerIn hq,hs.peerOut,hs.localIn,hs.retirement⟩
  · exact ⟨hs.localBanksBound,hs.peerBanksBound,hs.localCause,hs.peerCause,
      hs.localOut,hs.peerIn,duplicateList_bound _ hs.peerOut hq,hs.localIn,hs.retirement⟩
  · exact ⟨hs.localBanksBound,hs.peerBanksBound,hs.localCause,hs.peerCause,
      hs.localOut,hs.peerIn,hs.peerOut,duplicateList_bound _ hs.localIn hq,hs.retirement⟩

theorem list_tail_bound {α : Type} (p : α → Prop) {n : Nat} {xs : List α}
    (h : xs.length ≤ n ∧ ∀ x ∈ xs,p x) : xs.tail.length ≤ n ∧ ∀ x ∈ xs.tail,p x :=
  ⟨by simp only [List.length_tail]; omega,fun x hx => h.2 x (List.mem_of_mem_tail hx)⟩


theorem ResourceBound.step {cfg : Config} {s : System} (hs : ResourceBound cfg s)
    (c : Command) : ResourceBound cfg (step cfg s c).system := by
  cases c with
  | «local» c => exact hs.localStep c
  | send identity operation =>
    simp only [FRPSpec.PendingRetention.step]
    split
    · exact hs
    · split
      · exact hs
      · split
        · exact hs
        · rename_i packet hp
          exact hs.pushRequest _ (businessPacket_bound hs.localBanksBound.selected hp)
  | relinquishBefore target => exact hs.startRetirement target
  | retryRetirement =>
    simp only [FRPSpec.PendingRetention.step]
    split
    · exact hs
    · split
      · exact hs
      · rename_i target ht
        exact hs.pushRequest _ (hs.localBanksBound.selected.2.2.2.1 target ht)
  | resumeDeletion =>
    simp only [FRPSpec.PendingRetention.step]
    split
    · exact hs
    · split
      · exact hs
      · rename_i target ht
        apply hs.beginPeer
        · have hb := hs.peerBanksBound.selected
          refine ⟨hb.1,by simp,?_,?_⟩
          · exact (List.length_filter_le _ _).trans hb.2.2.1
          · intro r hr; exact hb.2.2.2 r (List.mem_of_mem_filter hr)
        · exact hs.peerBanksBound.selected.2.1 target ht
  | transferRequest =>
    simp only [FRPSpec.PendingRetention.step]
    split
    · exact hs
    · cases he : s.localOut with
      | nil => exact hs
      | cons p rest =>
        refine ⟨hs.localBanksBound,hs.peerBanksBound,hs.localCause,hs.peerCause,?_,?_,
          hs.peerOut,hs.localIn,hs.retirement⟩
        · simpa [he] using list_tail_bound _ hs.localOut
        · constructor
          · simp only [List.length_append,List.length_singleton]; omega
          · intro x hx
            rcases List.mem_append.mp hx with hx | hx
            · exact hs.peerIn.2 x hx
            · have : x = p := List.mem_singleton.mp hx
              subst x; exact hs.localOut.2 p (by simp [he])
  | transferReply =>
    simp only [FRPSpec.PendingRetention.step]
    split
    · exact hs
    · cases he : s.peerOut with
      | nil => exact hs
      | cons p rest =>
        refine ⟨hs.localBanksBound,hs.peerBanksBound,hs.localCause,hs.peerCause,hs.localOut,hs.peerIn,?_,?_,hs.retirement⟩
        · simpa [he] using list_tail_bound _ hs.peerOut
        · constructor
          · simp only [List.length_append,List.length_singleton]; omega
          · intro x hx
            rcases List.mem_append.mp hx with hx | hx
            · exact hs.localIn.2 x hx
            · have : x = p := List.mem_singleton.mp hx
              subst x; exact hs.peerOut.2 p (by simp [he])
  | duplicate q i => exact hs.duplicateQueue q i
  | drop q =>
    cases q
    · exact ⟨hs.localBanksBound,hs.peerBanksBound,hs.localCause,hs.peerCause,list_tail_bound _ hs.localOut,
        hs.peerIn,hs.peerOut,hs.localIn,hs.retirement⟩
    · exact ⟨hs.localBanksBound,hs.peerBanksBound,hs.localCause,hs.peerCause,hs.localOut,
        list_tail_bound _ hs.peerIn,hs.peerOut,hs.localIn,hs.retirement⟩
    · exact ⟨hs.localBanksBound,hs.peerBanksBound,hs.localCause,hs.peerCause,hs.localOut,
        hs.peerIn,list_tail_bound _ hs.peerOut,hs.localIn,hs.retirement⟩
    · exact ⟨hs.localBanksBound,hs.peerBanksBound,hs.localCause,hs.peerCause,hs.localOut,
        hs.peerIn,hs.peerOut,list_tail_bound _ hs.localIn,hs.retirement⟩
  | deliverRequest => exact hs.requestStep
  | deliverReply => exact hs.replyStep
  | progress => exact hs.progress
  | crashLocal =>
    exact ⟨hs.localBanksBound.crash,hs.peerBanksBound,by simp [FRPSpec.PendingRetention.step],hs.peerCause,
      hs.localOut,hs.peerIn,hs.peerOut,hs.localIn,by simp [FRPSpec.PendingRetention.step]⟩
  | crashPeer =>
    exact ⟨hs.localBanksBound,hs.peerBanksBound.crash,hs.localCause,by simp [FRPSpec.PendingRetention.step],
      hs.localOut,hs.peerIn,hs.peerOut,hs.localIn,hs.retirement⟩
  | recoverLocal =>
    simp only [FRPSpec.PendingRetention.step]
    split
    · exact ⟨hs.localBanksBound,hs.peerBanksBound,hs.localCause,hs.peerCause,
        hs.localOut,hs.peerIn,hs.peerOut,hs.localIn,hs.retirement⟩
    · exact hs
  | recoverPeer =>
    simp only [FRPSpec.PendingRetention.step]
    split
    · exact ⟨hs.localBanksBound,hs.peerBanksBound,hs.localCause,hs.peerCause,
        hs.localOut,hs.peerIn,hs.peerOut,hs.localIn,hs.retirement⟩
    · exact hs
  | cleanup => exact ⟨hs.localBanksBound,hs.peerBanksBound,hs.localCause,hs.peerCause,
      hs.localOut,hs.peerIn,hs.peerOut,hs.localIn,hs.retirement⟩
  | inspect => simp only [FRPSpec.PendingRetention.step]; split <;> exact hs
  | query _ => simp only [FRPSpec.PendingRetention.step]; split <;> exact hs
  | malformed => exact hs


theorem initial_resourceBound (cfg : Config) : ResourceBound cfg initial := by
  have hl : LocalBanksBound cfg (LocalBanks.initial {}) := by
    apply idle_bounded _ _ _ _ _ (local_seed_bound cfg)
    intro bank
    exact ⟨local_seed_bound cfg,Nat.zero_le _,by simp [LocalSnapshot.encode]⟩
  have hp : PeerBanksBound cfg (PeerBanks.initial {}) := by
    apply idle_bounded _ _ _ _ _ (peer_seed_bound cfg)
    intro bank
    exact ⟨peer_seed_bound cfg,Nat.zero_le _,by simp [PeerSnapshot.encode]⟩
  exact ⟨hl,hp,by simp [initial],by simp [initial],by simp [initial],by simp [initial],
    by simp [initial],by simp [initial],by simp [initial]⟩

/-- All reachable cuts, including interrupted copies and both independent
crashes, satisfy the same bounds. No successful-transaction premise occurs. -/
theorem reachable_resourceBound {cfg : Config} {s : System} (h : Reachable cfg s) :
    ResourceBound cfg s := by
  induction h with
  | initial => exact initial_resourceBound cfg
  | next _ c ih => exact ih.step c

theorem execution_resourceBound (cfg : Config) (cs : List Command) :
    ResourceBound cfg (execute cfg initial cs).system :=
  reachable_resourceBound (execute_reachable cfg initial cs .initial)

/-- No command-list length occurs in the bound, even for interrupted retries. -/
theorem every_prefix_resourceBound (cfg : Config) (cs : List Command) (cut : Nat) :
    ResourceBound cfg (execute cfg initial (cs.take cut)).system :=
  execution_resourceBound cfg (cs.take cut)

example : ResourceBound ⟨4,3,2⟩
    (execute ⟨4,3,2⟩ initial [.local (.accept true),.progress,.crashLocal,.crashPeer,
      .recoverPeer,.recoverLocal,.malformed]).system := execution_resourceBound _ _


theorem LocalHeaderBound.encodes {cfg : Config} {h : LocalHeader} (hh : LocalHeaderBound cfg h) :
    (Encoding.localHeader cfg.lifetime).encode h ≠ none := by
  simp only [Encoding.localHeader,Encoding.product_success,Encoding.optional_success,
    Encoding.number_success]
  exact ⟨Encoding.frame_success_of_valid _ _ hh.1 hh.2.1,hh.2.2⟩

theorem PeerHeaderBound.encodes {cfg : Config} {h : PeerHeader} (hh : PeerHeaderBound cfg h) :
    (Encoding.peerHeader cfg.lifetime).encode h ≠ none := by
  simpa only [Encoding.peerHeader,Encoding.product_success,Encoding.optional_success,
    Encoding.number_success,PeerHeaderBound] using hh

theorem LocalBanksBound.encodes {cfg : Config} {b : LocalBanks} (h : LocalBanksBound cfg b) :
    (Encoding.worker (Encoding.localHeader cfg.lifetime) (Encoding.outcome cfg.lifetime)
      cfg.outcomeCapacity).encode b ≠ none :=
  Encoding.worker_encodes _ _ _ _ _ _ h (fun _ h => h.encodes)
    (fun _ h => (Encoding.outcome_success _ _).mpr h)

theorem PeerBanksBound.encodes {cfg : Config} {b : PeerBanks} (h : PeerBanksBound cfg b) :
    (Encoding.worker (Encoding.peerHeader cfg.lifetime)
      (Encoding.product (Encoding.number cfg.lifetime) (Encoding.identity Ledger))
      cfg.outcomeCapacity).encode b ≠ none :=
  Encoding.worker_encodes _ _ _ _ _ _ h (fun _ h => h.encodes)
    (fun _ h => by simpa [Encoding.identity,Encoding.number_success] using h)

theorem LocalCauseBound.encodes {cfg : Config} {c : LocalCause} (h : LocalCauseBound cfg c) :
    (Encoding.localCause cfg.lifetime).encode c ≠ none := by
  cases c <;> simpa [Encoding.localCause,Encoding.identity,Encoding.number_success,
    Encoding.frameCommand_success,CommandBound,LocalCauseBound] using h

theorem PeerCauseBound.encodes {cfg : Config} {c : PeerCause} (h : PeerCauseBound cfg c) :
    (Encoding.peerCause cfg.lifetime).encode c ≠ none := by
  cases c <;> simpa [Encoding.peerCause,Encoding.identity,Encoding.number_success,
    Encoding.replyPacket_success,ReplyBound,PeerCauseBound] using h

/-- Every runtime value has an explicit finite code, including every stale
bank, partial copy, queued duplicate and saved dispatch field. -/
theorem ResourceBound.encodes {cfg : Config} {s : System} (h : ResourceBound cfg s) :
    (Encoding.system cfg).encode s ≠ none := by
  simp only [Encoding.system,Encoding.fields_success,Encoding.product_success,
    Encoding.optional_success,Encoding.sequence,Encoding.cells_success,
    Encoding.identity,Encoding.backend,Encoding.number_success]
  refine ⟨h.localBanksBound.encodes,h.peerBanksBound.encodes,?_,?_,?_,?_,?_,?_,by simp,by simp,?_,?_,?_,?_⟩
  · exact fun c hc => (h.localCause c hc).encodes
  · exact fun c hc => (h.peerCause c hc).encodes
  · exact ⟨h.localOut.1,fun p hp => (Encoding.requestPacket_success cfg p).mpr (h.localOut.2 p hp)⟩
  · exact ⟨h.peerIn.1,fun p hp => (Encoding.requestPacket_success cfg p).mpr (h.peerIn.2 p hp)⟩
  · exact ⟨h.peerOut.1,fun p hp => (Encoding.replyPacket_success cfg p).mpr (h.peerOut.2 p hp)⟩
  · exact ⟨h.localIn.1,fun p hp => (Encoding.replyPacket_success cfg p).mpr (h.localIn.2 p hp)⟩
  · intro b hb; simp
  · intro b hb; simp
  · intro b hb; simp
  · exact h.retirement

/-- Proof arguments select an already-successful executable encoding; they add
no ghost data to the code. -/
def encodeBounded (cfg : Config) (s : System) (h : ResourceBound cfg s) : Encoding.SystemCode cfg :=
  ((Encoding.system cfg).encode s).get (Option.isSome_iff_ne_none.mpr h.encodes)

theorem decode_encodeBounded (cfg : Config) (s : System) (h : ResourceBound cfg s) :
    (Encoding.system cfg).decode (encodeBounded cfg s h) = s := by
  apply Encoding.system_recover
  exact (Option.some_get _).symm

def packedBounded (cfg : Config) (s : System) (h : ResourceBound cfg s) :
    Fin (2 ^ Encoding.systemBits cfg) := Encoding.packSystem cfg (encodeBounded cfg s h)

theorem packedBounded_injective (cfg : Config) (s t : System)
    (hs : ResourceBound cfg s) (ht : ResourceBound cfg t)
    (h : packedBounded cfg s hs = packedBounded cfg t ht) : s = t := by
  have he := Encoding.packSystem_injective cfg h
  have := congrArg (Encoding.system cfg).decode he
  simpa only [decode_encodeBounded] using this


namespace Layout
open Encoding

def localBits (cfg : Config) : Nat := Bits.width (α := SnapshotCode (LocalHeaderCode cfg.lifetime)
  (OutcomeCode cfg.lifetime) cfg.outcomeCapacity)
def peerBits (cfg : Config) : Nat := Bits.width (α := SnapshotCode (PeerHeaderCode cfg.lifetime)
  (Name cfg.lifetime × Ledger) cfg.outcomeCapacity)
def requestBits (cfg : Config) : Nat := Bits.width (α := RequestPacketCode cfg.lifetime)
def replyBits (cfg : Config) : Nat := Bits.width (α := ReplyPacketCode cfg.lifetime)
/-- A rejected fresh insertion may materialize one record beyond peer capacity. -/
def peerHelperBits (cfg : Config) : Nat := Bits.width (α := SnapshotCode (PeerHeaderCode cfg.lifetime)
  (Name cfg.lifetime × Ledger) (cfg.outcomeCapacity + 1))

/-- Validator comparison proposals can temporarily increment K to K+1. -/
def validatorFrameBits (cfg : Config) : Nat := Bits.width (α := FrameCode (cfg.lifetime + 1))
def validatorCommandBits (cfg : Config) : Nat := Bits.width (α := FrameCommandCode cfg.lifetime)
def validatorListBits (cfg : Config) : Nat := 12 * (validatorCommandBits cfg + 1)
def validatorBits (cfg : Config) : Nat := 3 * validatorListBits cfg + 2 * validatorFrameBits cfg + 4

def cursorBits (cfg : Config) : Nat := Nat.clog 2 (2 * cfg.outcomeCapacity + 4)
def nameBits (cfg : Config) : Nat := Nat.clog 2 (cfg.lifetime + 1)

/-- Both saved causes are counted, including the pending frame command and
terminal publication label data. Queue lengths use their occupancy tags. -/
def controlBits (cfg : Config) : Nat :=
  2 * (1 + cursorBits cfg) + Bits.width (α := Option (LocalCauseCode cfg.lifetime)) +
  Bits.width (α := Option (PeerCauseCode cfg.lifetime)) + 2 + (2 * nameBits cfg + 1)

def requestQueueBits (cfg : Config) : Nat := cfg.queueCapacity * (requestBits cfg + 1)
def replyQueueBits (cfg : Config) : Nat := cfg.queueCapacity * (replyBits cfg + 1)

/-- Exact decomposition of the encoded stored state, before the three transient
packet/observation buffers and the conversion scratch backend are reserved. -/
theorem stored_bits (cfg : Config) : systemBits cfg =
    4 * localBits cfg + 4 * peerBits cfg + 2 * requestQueueBits cfg + 2 * replyQueueBits cfg +
      controlBits cfg + 3 * 4 := by
  simp only [systemBits,SystemCode,LocalCode,PeerCode,WorkerCode,
    product_width,optional_width,cells_width,localBits,peerBits,requestQueueBits,
    replyQueueBits,controlBits,cursorBits,nameBits,requestBits,replyBits,BackendCode]
  dsimp only [Bits.width]
  ring

/-- A single current-observation response fits the larger local snapshot region;
requests and replies fit their own code widths. Three buffers are reserved. -/
def packetBits (cfg : Config) : Nat := max (localBits cfg + 4) (max (requestBits cfg) (replyBits cfg))

def configBits (cfg : Config) : Nat := nameBits cfg + Nat.clog 2 (cfg.outcomeCapacity + 1) +
  Nat.clog 2 (cfg.queueCapacity + 1)

/-- These are allocated capacities, including empty/stale regions. The extra
backend slot covers conversion scratch even on a failed migration. -/
def bound (cfg : Config) : Nat :=
  4 * localBits cfg + 4 * peerBits cfg + 2 * requestQueueBits cfg + 2 * replyQueueBits cfg +
    3 * packetBits cfg + 4 * 4 + controlBits cfg + configBits cfg +
    2 * localBits cfg + 2 * peerHelperBits cfg + requestQueueBits cfg + replyQueueBits cfg + validatorBits cfg

theorem stored_le_bound (cfg : Config) : systemBits cfg ≤ bound cfg := by
  rw [stored_bits]
  unfold bound
  omega

inductive Region where
  | localDisk (bank : Bool) | localTarget | localBuffer
  | peerDisk (bank : Bool) | peerTarget | peerBuffer
  | requestQueue (ingress : Bool) | replyQueue (ingress : Bool)
  | packet (index : Fin 3) | backend (index : Fin 4) | controller
  | localHelper | peerHelper | requestHelper | replyHelper | localPrefix | peerPrefix
  | validatorList (index : Fin 3) | validatorFrame (index : Fin 2) | validatorCursor
  deriving DecidableEq, Repr

def capacity (cfg : Config) : Region → Nat
  | .localDisk _ | .localTarget | .localBuffer => localBits cfg
  | .peerDisk _ | .peerTarget | .peerBuffer => peerBits cfg
  | .requestQueue _ => requestQueueBits cfg
  | .replyQueue _ => replyQueueBits cfg
  | .packet _ => packetBits cfg
  | .backend _ => 4
  | .controller => controlBits cfg + configBits cfg
  | .localHelper | .localPrefix => localBits cfg
  | .peerHelper | .peerPrefix => peerHelperBits cfg
  | .requestHelper => requestQueueBits cfg
  | .replyHelper => replyQueueBits cfg
  | .validatorList _ => validatorListBits cfg
  | .validatorFrame _ => validatorFrameBits cfg
  | .validatorCursor => 4

/-- The complete allocated inventory, including scratch and empty regions. -/
def inventory : List Region :=
  [.localDisk false,.localDisk true,.localTarget,.localBuffer,
   .peerDisk false,.peerDisk true,.peerTarget,.peerBuffer,
   .requestQueue false,.requestQueue true,.replyQueue false,.replyQueue true,
   .packet 0,.packet 1,.packet 2,.backend 0,.backend 1,.backend 2,.backend 3,.controller,.localHelper,.peerHelper,.requestHelper,.replyHelper,.localPrefix,.peerPrefix,
   .validatorList 0,.validatorList 1,.validatorList 2,.validatorFrame 0,.validatorFrame 1,.validatorCursor]

theorem inventory_complete (r : Region) : r ∈ inventory := by
  cases r with
  | localDisk b | peerDisk b | requestQueue b | replyQueue b => cases b <;> decide
  | packet i | validatorList i | validatorFrame i => fin_cases i <;> decide
  | backend i => fin_cases i <;> decide
  | _ => decide

theorem inventory_unique : inventory.Nodup := by decide

theorem inventory_bits (cfg : Config) : (inventory.map (capacity cfg)).sum = bound cfg := by
  simp only [inventory,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,capacity]
  unfold bound validatorBits
  ring

/-- Region-tagged addresses cannot alias across owners. An offset is finite
by construction; all eight snapshot regions have independent address spaces. -/
abbrev Address (cfg : Config) := (region : Region) × Fin (capacity cfg region)

theorem address_regions_disjoint (cfg : Config) (a b : Address cfg)
    (h : a.1 ≠ b.1) : a ≠ b := fun eq => h (congrArg Sigma.fst eq)

def snapshotRegion (peer : Bool) (slot : Fin 4) : Region :=
  if peer then
    if slot = 0 then .peerDisk false else if slot = 1 then .peerDisk true
    else if slot = 2 then .peerTarget else .peerBuffer
  else
    if slot = 0 then .localDisk false else if slot = 1 then .localDisk true
    else if slot = 2 then .localTarget else .localBuffer

theorem snapshotRegion_injective : Function.Injective (fun p : Bool × Fin 4 => snapshotRegion p.1 p.2) := by
  decide

end Layout

/-- Uniform finite storage at every executable cut. The injection preserves the
complete machine state, not just its public observations. -/
def reachableCode (cfg : Config) (s : System) (h : Reachable cfg s) : Fin (2 ^ Layout.bound cfg) :=
  ⟨(packedBounded cfg s (reachable_resourceBound h)).val,
    (packedBounded cfg s (reachable_resourceBound h)).isLt.trans_le
      (Nat.pow_le_pow_right (by decide) (Layout.stored_le_bound cfg))⟩

set_option maxHeartbeats 1600000 in
theorem reachableCode_injective (cfg : Config) (s t : System)
    (hs : Reachable cfg s) (ht : Reachable cfg t)
    (h : reachableCode cfg s hs = reachableCode cfg t ht) : s = t := by
  apply packedBounded_injective cfg s t (reachable_resourceBound hs) (reachable_resourceBound ht)
  have values := congrArg (fun x : Fin (2 ^ Layout.bound cfg) => x.val) h
  change (packedBounded cfg s (reachable_resourceBound hs)).val =
    (packedBounded cfg t (reachable_resourceBound ht)).val at values
  apply Fin.ext
  exact values

theorem local_access_in_range {cfg : Config} {s : System} (h : Reachable cfg s)
    (op : Durability.SnapshotBanks.Primitive LocalHeader Outcome)
    (ho : s.localBank.nextOperation = some op) :
    op.Bounded (LocalHeaderBound cfg) (fun r => r.identity ≤ cfg.lifetime) cfg.outcomeCapacity := by
  have hb := (reachable_resourceBound h).localBanksBound.2
  exact Durability.SnapshotBanks.scheduleAt_bounded _ _ _ _ _ 0 _ _ hb.1 hb.2.2
    (by simpa using hb.2.1) ho

theorem peer_access_in_range {cfg : Config} {s : System} (h : Reachable cfg s)
    (op : Durability.SnapshotBanks.Primitive PeerHeader (Nat × Ledger))
    (ho : s.peer.nextOperation = some op) :
    op.Bounded (PeerHeaderBound cfg) (fun r => r.1 ≤ cfg.lifetime) cfg.outcomeCapacity := by
  have hb := (reachable_resourceBound h).peerBanksBound.2
  exact Durability.SnapshotBanks.scheduleAt_bounded _ _ _ _ _ 0 _ _ hb.1 hb.2.2
    (by simpa using hb.2.1) ho

/-- Every finite command suffix has a decodable bounded representation,
including cuts reached by refusal, independent crashes, and recovery. -/
theorem execution_encoding_roundtrip (cfg : Config) (cs : List Command) :
    (Encoding.system cfg).decode
      (encodeBounded cfg (execute cfg initial cs).system (execution_resourceBound cfg cs)) =
        (execute cfg initial cs).system :=
  decode_encodeBounded cfg _ _

example (cs : List Command) :
    ResourceBound ⟨4,3,2⟩ (execute ⟨4,3,2⟩ initial
      ([.local (.accept true), .progress, .crashPeer, .crashLocal, .recoverPeer, .recoverLocal] ++ cs)).system :=
  execution_resourceBound _ _

end FRPSpec.PendingRetention
