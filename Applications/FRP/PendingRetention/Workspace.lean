import Applications.FRP.PendingRetention.Costs

/-! Helper evaluation retains its source while materializing a bounded result.
The cuts below are actual recursive suffix results, not an extra runtime list.
Their enclosing source/result regions are distinct from all stored banks. -/
namespace FRPSpec.PendingRetention
open PendingCrash PendingMigration

namespace Workspace
universe u

def RecordsBound (bound capacity : Nat) (key : α → Nat) (xs : List α) : Prop :=
  xs.length ≤ capacity ∧ ∀ x ∈ xs, key x ≤ bound

theorem RecordsBound.drop {bound capacity : Nat} {key : α → Nat} {xs : List α}
    (h : RecordsBound bound capacity key xs) (cut : Nat) :
    RecordsBound bound capacity key (xs.drop cut) :=
  ⟨by simp only [List.length_drop]; have := h.1; omega, fun x mem => h.2 x (List.mem_of_mem_drop mem)⟩

theorem RecordsBound.take {bound capacity : Nat} {key : α → Nat} {xs : List α}
    (h : RecordsBound bound capacity key xs) (cut : Nat) :
    RecordsBound bound capacity key (xs.take cut) :=
  ⟨by simp only [List.length_take]; have := h.1; omega, fun x mem => h.2 x (List.mem_of_mem_take mem)⟩

theorem RecordsBound.map {bound capacity : Nat} {key : α → Nat} {xs : List α}
    (h : RecordsBound bound capacity key xs) (f : α → α)
    (preserves : ∀ x, key (f x) = key x) :
    RecordsBound bound capacity key (xs.map f) := by
  constructor
  · simpa using h.1
  · intro y hy
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hy
    simpa [preserves] using h.2 x hx

theorem RecordsBound.filter {bound capacity : Nat} {key : α → Nat} {xs : List α}
    (h : RecordsBound bound capacity key xs) (p : α → Bool) :
    RecordsBound bound capacity key (xs.filter p) :=
  ⟨(List.length_filter_le _ _).trans h.1, fun x mem => h.2 x (List.mem_of_mem_filter mem)⟩

/-- Recursive install allocates at most one additional record, including the
full-table insertion that is subsequently rejected by the capacity guard. -/
theorem install_length (xs : Peer) (identity : Nat) (entry : Ledger) :
    (install identity entry xs).1.length ≤ xs.length + 1 := by
  induction xs with
  | nil => simp [install]
  | cons head tail ih =>
    rcases head with ⟨key,old⟩
    simp only [install]
    split
    · simp
    · simpa only [List.length_cons] using Nat.add_le_add_right ih 1

theorem install_records {bound capacity : Nat} {xs : Peer}
    (h : RecordsBound bound capacity Prod.fst xs) (identity : Nat) (entry : Ledger)
    (small : identity ≤ bound) :
    RecordsBound bound (capacity + 1) Prod.fst (install identity entry xs).1 := by
  constructor
  · exact (install_length xs identity entry).trans (Nat.add_le_add_right h.1 1)
  · have names : PeerNamesBelow (bound + 1) xs := fun key value mem => Nat.lt_succ_of_le (h.2 (key,value) mem)
    have result := names.install identity entry (Nat.lt_succ_of_le small)
    intro x hx
    exact Nat.le_of_lt_succ (result x.1 x.2 hx)

theorem peerStep_records {cfg : Config} {s : PeerSnapshot}
    (h : PeerBound cfg s) (identity : Nat) (command : PeerCommand)
    (small : identity < cfg.lifetime) :
    RecordsBound cfg.lifetime (cfg.outcomeCapacity + 1) Prod.fst
      (peerStep s.entries identity command).peer := by
  have old : RecordsBound cfg.lifetime cfg.outcomeCapacity Prod.fst s.entries := ⟨h.2.2.1,h.2.2.2⟩
  dsimp only [peerStep]
  split
  · exact ⟨old.1.trans (Nat.le_succ _),old.2⟩
  · split
    · exact ⟨old.1.trans (Nat.le_succ _),old.2⟩
    · exact install_records old identity _ small.le

/-- These are the returned lists of every recursive invocation of the actual
install helper. The observer index does not reside in the service. -/
theorem install_recursive_cut {cfg : Config} {s : PeerSnapshot}
    (h : PeerBound cfg s) (identity : Nat) (entry : Ledger)
    (small : identity ≤ cfg.lifetime) (cut : Nat) :
    RecordsBound cfg.lifetime (cfg.outcomeCapacity + 1) Prod.fst
      (install identity entry (s.entries.drop cut)).1 :=
  install_records ((show RecordsBound cfg.lifetime cfg.outcomeCapacity Prod.fst s.entries from
    ⟨h.2.2.1,h.2.2.2⟩).drop cut) identity entry small

/-- Updating an outcome changes no name, so each recursive map cut fits the
same local helper region while its original source remains allocated. -/
theorem outcome_map_cut {cfg : Config} {s : LocalSnapshot}
    (h : LocalBound cfg s) (f : Outcome → Outcome)
    (preserves : ∀ x, (f x).identity = x.identity) (cut : Nat) :
    RecordsBound cfg.lifetime cfg.outcomeCapacity Outcome.identity
      ((s.outcomes.drop cut).map f) :=
  ((show RecordsBound cfg.lifetime cfg.outcomeCapacity Outcome.identity s.outcomes from
    ⟨h.2.2.2.2.1,h.2.2.2.2.2⟩).drop cut).map f preserves

theorem outcome_filter_cut {cfg : Config} {s : LocalSnapshot}
    (h : LocalBound cfg s) (target cut : Nat) :
    RecordsBound cfg.lifetime cfg.outcomeCapacity Outcome.identity
      ((s.outcomes.drop cut).filter (fun r => target ≤ r.identity)) :=
  ((show RecordsBound cfg.lifetime cfg.outcomeCapacity Outcome.identity s.outcomes from
    ⟨h.2.2.2.2.1,h.2.2.2.2.2⟩).drop cut).filter _

theorem remember_records {cfg : Config} {s : LocalSnapshot}
    (h : RecordsBound cfg.lifetime cfg.outcomeCapacity Outcome.identity s.outcomes)
    (receipt : Receipt) :
    RecordsBound cfg.lifetime cfg.outcomeCapacity Outcome.identity (remember s receipt).outcomes := by
  cases receipt with
  | mk identity answer =>
    cases answer <;> simp only [remember,terminalAnswer] <;> try exact h
    all_goals apply h.map
    all_goals intro x
    all_goals split <;> rfl

@[simp] theorem remember_header (s : LocalSnapshot) (r : Receipt) :
    (remember s r).frame = s.frame ∧ (remember s r).floor = s.floor ∧
      (remember s r).pending = s.pending := by
  cases r with
  | mk i answer => cases answer <;> simp [remember,terminalAnswer]

@[simp] theorem remember_frame (s : LocalSnapshot) (r : Receipt) :
    (remember s r).frame = s.frame := (remember_header s r).1
@[simp] theorem remember_floor (s : LocalSnapshot) (r : Receipt) :
    (remember s r).floor = s.floor := (remember_header s r).2.1
@[simp] theorem remember_pending (s : LocalSnapshot) (r : Receipt) :
    (remember s r).pending = s.pending := (remember_header s r).2.2

theorem localChangeCore_header {cfg : Config} {s t : LocalSnapshot} {c : FrameCommand}
    (h : LocalBound cfg s) (done : localChangeCore cfg s c = .ok t) :
    t.frame.Valid ∧ t.frame.nextIdentity ≤ cfg.lifetime ∧
      t.floor = s.floor ∧ t.pending = s.pending := by
  unfold localChangeCore at done
  generalize advanced : advance s.frame c = decision at done
  cases decision with
  | refused | stopped =>
    cases c <;> simp only at done
    all_goals repeat' first | split at done | contradiction
  | changed frame =>
    have valid := (advance_valid advanced).2
    have counter := advance_nextIdentity s.frame frame c advanced
    have old := h.2.1
    cases c <;> simp only [admissionDelta] at counter
    all_goals simp only [Bool.true_and,Bool.false_and,Bool.false_eq_true,↓reduceIte] at done
    all_goals repeat' first | split at done | contradiction
    all_goals cases done
    all_goals simp only [remember_frame,remember_floor,remember_pending]
    all_goals refine ⟨valid,?_,by trivial,by trivial⟩
    all_goals simp_all only [decide_eq_true_eq,not_le]
    all_goals omega

theorem localChangeCore_records {cfg : Config} {s t : LocalSnapshot} {c : FrameCommand}
    (h : LocalBound cfg s) (done : localChangeCore cfg s c = .ok t) :
    RecordsBound cfg.lifetime cfg.outcomeCapacity Outcome.identity t.outcomes := by
  have old : RecordsBound cfg.lifetime cfg.outcomeCapacity Outcome.identity s.outcomes :=
    ⟨h.2.2.2.2.1,h.2.2.2.2.2⟩
  unfold localChangeCore at done
  generalize advanced : advance s.frame c = decision at done
  cases decision with
  | refused | stopped =>
    cases c <;> simp only at done
    all_goals repeat' first | split at done | contradiction
  | changed frame =>
    cases c <;> simp only [Bool.true_and,Bool.false_and,Bool.false_eq_true,↓reduceIte] at done
    all_goals repeat' first | split at done | contradiction
    all_goals cases done
    all_goals first
      | exact old
      | apply remember_records; exact old
      | apply old.map; intro x; split <;> rfl
      | constructor
        · simp only [List.length_append,List.length_singleton]
          simp_all only [decide_eq_true_eq,not_le]
          omega
        · intro x hx
          rcases List.mem_append.mp hx with hx | hx
          · exact old.2 x hx
          · simp only [List.mem_singleton] at hx
            subst x
            exact h.2.1

/-- Raw helper results fit before the final finite-representation guard, so a
failed guard cannot hide an oversized temporary local snapshot. -/
theorem localChangeCore_bound {cfg : Config} {s t : LocalSnapshot} {c : FrameCommand}
    (h : LocalBound cfg s) (done : localChangeCore cfg s c = .ok t) : LocalBound cfg t := by
  obtain ⟨valid,names,floor,pending⟩ := localChangeCore_header h done
  have records := localChangeCore_records h done
  exact ⟨valid,names, floor ▸ h.2.2.1, pending ▸ h.2.2.2.1, records.1,records.2⟩

/-- Every materialized prefix of the actual local helper result is encodable
in its own region while all preceding stored bank regions remain owned. -/
theorem local_helper_cut {cfg : Config} {s t : LocalSnapshot} {c : FrameCommand}
    (h : LocalBound cfg s) (done : localChangeCore cfg s c = .ok t) (cut : Nat) :
    ({t.encode with items := t.outcomes.take cut}).Bounded
      (LocalHeaderBound cfg) (fun r : Outcome => r.identity ≤ cfg.lifetime) cfg.outcomeCapacity := by
  have full := (local_payload_bound cfg t).mpr (localChangeCore_bound h done)
  exact ⟨full.1, by exact (localChangeCore_records h done).take cut⟩

/-- The actual peer dispatch is evaluated only after its lifetime guard. Its
result fits U+1 even when the subsequent capacity test rejects it. -/
theorem peer_helper_cut {cfg : Config} {s : PeerSnapshot}
    (h : PeerBound cfg s) (identity : Nat) (command : PeerCommand)
    (small : identity < cfg.lifetime) (cut : Nat) :
    RecordsBound cfg.lifetime (cfg.outcomeCapacity + 1) Prod.fst
      ((peerStep s.entries identity command).peer.take cut) :=
  (peerStep_records h identity command small).take cut

/-- Helper results have separate addresses; neither helper overwrites the
selected source, stale banks, or unfinished recovery/copy buffers. -/
theorem local_helper_not_bank (peer bank : Bool) :
    Layout.Region.localHelper ≠ (if peer then .peerDisk bank else .localDisk bank) := by
  cases peer <;> simp

theorem peer_helper_not_bank (peer bank : Bool) :
    Layout.Region.peerHelper ≠ (if peer then .peerDisk bank else .localDisk bank) := by
  cases peer <;> simp

open Encoding

abbrev PeakCode (cfg : Config) := SystemCode cfg ×
  SnapshotCode (LocalHeaderCode cfg.lifetime) (OutcomeCode cfg.lifetime) cfg.outcomeCapacity ×
  SnapshotCode (PeerHeaderCode cfg.lifetime) (Name cfg.lifetime × Ledger) (cfg.outcomeCapacity + 1) ×
  Cells (RequestPacketCode cfg.lifetime) cfg.queueCapacity ×
  Cells (ReplyPacketCode cfg.lifetime) cfg.queueCapacity ×
  SnapshotCode (LocalHeaderCode cfg.lifetime) (OutcomeCode cfg.lifetime) cfg.outcomeCapacity ×
  SnapshotCode (PeerHeaderCode cfg.lifetime) (Name cfg.lifetime × Ledger) (cfg.outcomeCapacity + 1)

set_option synthInstance.maxSize 8192 in
 abbrev peakPacking (cfg : Config) : Bits (PeakCode cfg) := inferInstance

/-- Simultaneous storage of the old machine and both helper results fits the
allocated inventory. Old and new lists are never counted as one shared region. -/
theorem peak_width (cfg : Config) : (peakPacking cfg).width ≤ Layout.bound cfg := by
  change systemBits cfg + (Layout.localBits cfg + (Layout.peerHelperBits cfg +
    (Bits.width (α := Cells (RequestPacketCode cfg.lifetime) cfg.queueCapacity) +
     (Bits.width (α := Cells (ReplyPacketCode cfg.lifetime) cfg.queueCapacity) +
       (Layout.localBits cfg + Layout.peerHelperBits cfg))))) ≤ Layout.bound cfg
  rw [cells_width,cells_width]
  change systemBits cfg + (Layout.localBits cfg + (Layout.peerHelperBits cfg +
    (Layout.requestQueueBits cfg + (Layout.replyQueueBits cfg +
      (Layout.localBits cfg + Layout.peerHelperBits cfg))))) ≤ Layout.bound cfg
  rw [Layout.stored_bits]
  unfold Layout.bound
  omega

theorem peak_width_with_validator (cfg : Config) : (peakPacking cfg).width + Layout.validatorBits cfg ≤ Layout.bound cfg := by
  change systemBits cfg + (Layout.localBits cfg + (Layout.peerHelperBits cfg +
    (Bits.width (α := Cells (RequestPacketCode cfg.lifetime) cfg.queueCapacity) +
     (Bits.width (α := Cells (ReplyPacketCode cfg.lifetime) cfg.queueCapacity) +
       (Layout.localBits cfg + Layout.peerHelperBits cfg))))) + Layout.validatorBits cfg ≤ Layout.bound cfg
  rw [cells_width,cells_width]
  change systemBits cfg + (Layout.localBits cfg + (Layout.peerHelperBits cfg +
    (Layout.requestQueueBits cfg + (Layout.replyQueueBits cfg +
      (Layout.localBits cfg + Layout.peerHelperBits cfg))))) + Layout.validatorBits cfg ≤ Layout.bound cfg
  rw [Layout.stored_bits]
  unfold Layout.bound
  omega

set_option synthInstance.maxSize 8192 in
 def peakCode (cfg : Config) (p : PeakCode cfg) : Fin (2 ^ Layout.bound cfg) :=
  ⟨((peakPacking cfg).pack p).val,
    ((peakPacking cfg).pack p).isLt.trans_le (Nat.pow_le_pow_right (by decide) (peak_width cfg))⟩

/-- Appending or duplicating a packet retains the old queue and materializes
at most Q result cells. Every recursive append result is a suffix of this list. -/
theorem queue_append_cut {α : Type u} (p : α → Prop) (xs : List α) (packet : α)
    (capacity cut : Nat) (room : xs.length < capacity)
    (old : ∀ x ∈ xs, p x) (fresh : p packet) :
    ((xs ++ [packet]).drop cut).length ≤ capacity ∧
      ∀ x ∈ (xs ++ [packet]).drop cut, p x := by
  constructor
  · simp only [List.length_drop,List.length_append,List.length_singleton]
    omega
  · intro x hx
    rcases List.mem_append.mp (List.mem_of_mem_drop hx) with hx | hx
    · exact old x hx
    · simpa using (List.mem_singleton.mp hx) ▸ fresh

/-- The source comes from the actual execution, including unsuccessful prior
commands. Both helper bounds quantify over every materialization cut. -/
theorem execution_workspace (cfg : Config) (commands : List Command) :
    let s := (execute cfg initial commands).system
    ResourceBound cfg s ∧
    (∀ c t, localChangeCore cfg s.localBank.selected c = .ok t → ∀ cut,
      ({t.encode with items := t.outcomes.take cut}).Bounded
        (LocalHeaderBound cfg) (fun r : Outcome => r.identity ≤ cfg.lifetime) cfg.outcomeCapacity) ∧
    (∀ identity command, identity < cfg.lifetime → ∀ cut,
      RecordsBound cfg.lifetime (cfg.outcomeCapacity + 1) Prod.fst
        ((peerStep s.peer.selected.entries identity command).peer.take cut)) := by
  dsimp only
  have h := execution_resourceBound cfg commands
  exact ⟨h,fun _ _ done cut => local_helper_cut h.localBanksBound.selected done cut,
    fun i c small cut => peer_helper_cut h.peerBanksBound.selected i c small cut⟩

def localHelperCodec (cfg : Config) :=
  Encoding.snapshot (Encoding.localHeader cfg.lifetime) (Encoding.outcome cfg.lifetime) cfg.outcomeCapacity

def peerHelperCodec (cfg : Config) :=
  Encoding.snapshot (Encoding.peerHeader cfg.lifetime)
    (Encoding.product (Encoding.number cfg.lifetime) (Encoding.identity Ledger)) (cfg.outcomeCapacity + 1)

theorem local_helper_encodes {cfg : Config} {s t : LocalSnapshot} {c : FrameCommand}
    (h : LocalBound cfg s) (done : localChangeCore cfg s c = .ok t) (cut : Nat) :
    (localHelperCodec cfg).encode {t.encode with items := t.outcomes.take cut} ≠ none := by
  have hb := local_helper_cut h done cut
  apply (Encoding.snapshot_success _ _ _ _).mpr
  exact ⟨hb.1.encodes,hb.2.1,fun r hr => (Encoding.outcome_success _ _).mpr (hb.2.2 r hr)⟩

theorem peer_helper_encodes {cfg : Config} {s : PeerSnapshot}
    (h : PeerBound cfg s) (identity : Nat) (command : PeerCommand)
    (small : identity < cfg.lifetime) (cut : Nat) :
    (peerHelperCodec cfg).encode {s.encode with items :=
      (peerStep s.entries identity command).peer.take cut} ≠ none := by
  have records := peer_helper_cut h identity command small cut
  apply (Encoding.snapshot_success _ _ _ _).mpr
  refine ⟨(show PeerHeaderBound cfg s.encode.header from ⟨h.1,h.2.1⟩).encodes,records.1,?_⟩
  intro r hr
  simpa [Encoding.identity,Encoding.number_success] using records.2 r hr

def emptyCells {α : Type} : (n : Nat) → Encoding.Cells α n
  | 0 => ()
  | n+1 => (none,emptyCells n)

/-- Simultaneous exact codes for the old executed machine and both computed
helper prefixes. Each projects back to its actual value. `peakCode` places
this whole tuple within the separately owned allocated inventory. -/
theorem execution_peak (cfg : Config) (commands : List Command) (c : FrameCommand)
    (target : LocalSnapshot)
    (done : localChangeCore cfg (execute cfg initial commands).system.localBank.selected c = .ok target)
    (identity : Nat) (command : PeerCommand) (small : identity < cfg.lifetime)
    (localCut peerCut : Nat) :
    ∃ code : PeakCode cfg,
      (Encoding.system cfg).decode code.1 = (execute cfg initial commands).system ∧
      (localHelperCodec cfg).decode code.2.1 = {target.encode with items := target.outcomes.take localCut} ∧
      (peerHelperCodec cfg).decode code.2.2.1 =
        { (execute cfg initial commands).system.peer.selected.encode with items :=
          (peerStep (execute cfg initial commands).system.peer.selected.entries identity command).peer.take peerCut} := by
  let state := (execute cfg initial commands).system
  have bound := execution_resourceBound cfg commands
  have localOK := local_helper_encodes bound.localBanksBound.selected done localCut
  have peerOK := peer_helper_encodes bound.peerBanksBound.selected identity command small peerCut
  let localCode := ((localHelperCodec cfg).encode {target.encode with items := target.outcomes.take localCut}).get
    (Option.isSome_iff_ne_none.mpr localOK)
  let peerCode := ((peerHelperCodec cfg).encode {state.peer.selected.encode with
    items := (peerStep state.peer.selected.entries identity command).peer.take peerCut}).get
      (Option.isSome_iff_ne_none.mpr peerOK)
  refine ⟨(encodeBounded cfg state bound,localCode,peerCode,emptyCells _,emptyCells _,localCode,peerCode),
    decode_encodeBounded cfg state bound,?_,?_⟩
  · exact (localHelperCodec cfg).recover _ _ (Option.some_get _).symm
  · exact (peerHelperCodec cfg).recover _ _ (Option.some_get _).symm

theorem local_payload_encodes {cfg : Config} {payload : LocalPayload}
    (h : payload.Bounded (LocalHeaderBound cfg) (fun r => r.identity ≤ cfg.lifetime) cfg.outcomeCapacity) :
    (localHelperCodec cfg).encode payload ≠ none :=
  (Encoding.snapshot_success _ _ _ _).mpr
    ⟨h.1.encodes,h.2.1,fun r hr => (Encoding.outcome_success _ _).mpr (h.2.2 r hr)⟩

/-- A peer-only evaluation does not require a successful unrelated local
command. The local helper remains an empty, separately reserved region. -/
theorem execution_peer_peak (cfg : Config) (commands : List Command)
    (identity : Nat) (command : PeerCommand) (small : identity < cfg.lifetime) (cut : Nat) :
    ∃ code : PeakCode cfg,
      (Encoding.system cfg).decode code.1 = (execute cfg initial commands).system ∧
      (peerHelperCodec cfg).decode code.2.2.1 =
        { (execute cfg initial commands).system.peer.selected.encode with items :=
          (peerStep (execute cfg initial commands).system.peer.selected.entries identity command).peer.take cut} := by
  let state := (execute cfg initial commands).system
  have bound := execution_resourceBound cfg commands
  have localOK := local_payload_encodes
    (cfg := cfg) (payload := ⟨localSeed,[]⟩) ⟨local_seed_bound cfg,by simp,by simp⟩
  have peerOK := peer_helper_encodes bound.peerBanksBound.selected identity command small cut
  let localCode := ((localHelperCodec cfg).encode ⟨localSeed,[]⟩).get (Option.isSome_iff_ne_none.mpr localOK)
  let peerCode := ((peerHelperCodec cfg).encode {state.peer.selected.encode with
    items := (peerStep state.peer.selected.entries identity command).peer.take cut}).get
      (Option.isSome_iff_ne_none.mpr peerOK)
  refine ⟨(encodeBounded cfg state bound,localCode,peerCode,emptyCells _,emptyCells _,localCode,peerCode),
    decode_encodeBounded cfg state bound,?_⟩
  exact (peerHelperCodec cfg).recover _ _ (Option.some_get _).symm

theorem execution_local_peak (cfg : Config) (commands : List Command) (c : FrameCommand)
    (target : LocalSnapshot)
    (done : localChangeCore cfg (execute cfg initial commands).system.localBank.selected c = .ok target)
    (cut : Nat) :
    ∃ code : PeakCode cfg,
      (Encoding.system cfg).decode code.1 = (execute cfg initial commands).system ∧
      (localHelperCodec cfg).decode code.2.1 = {target.encode with items := target.outcomes.take cut} := by
  let state := (execute cfg initial commands).system
  have bound := execution_resourceBound cfg commands
  have localOK := local_helper_encodes bound.localBanksBound.selected done cut
  have peerOK : (peerHelperCodec cfg).encode ⟨peerSeed,[]⟩ ≠ none := by
    apply (Encoding.snapshot_success _ _ _ _).mpr
    exact ⟨(peer_seed_bound cfg).encodes,by simp,by simp⟩
  let localCode := ((localHelperCodec cfg).encode {target.encode with items := target.outcomes.take cut}).get
    (Option.isSome_iff_ne_none.mpr localOK)
  let peerCode := ((peerHelperCodec cfg).encode ⟨peerSeed,[]⟩).get (Option.isSome_iff_ne_none.mpr peerOK)
  refine ⟨(encodeBounded cfg state bound,localCode,peerCode,emptyCells _,emptyCells _,localCode,peerCode),
    decode_encodeBounded cfg state bound,?_⟩
  exact (localHelperCodec cfg).recover _ _ (Option.some_get _).symm

theorem request_append_encodes (cfg : Config) (xs : List RequestPacket) (packet : RequestPacket)
    (room : xs.length < cfg.queueCapacity) (old : ∀ p ∈ xs, RequestBound cfg p)
    (fresh : RequestBound cfg packet) (cut : Nat) :
    (Encoding.sequence (Encoding.requestPacket cfg.lifetime) cfg.queueCapacity).encode
      ((xs ++ [packet]).drop cut) ≠ none := by
  have h := queue_append_cut (RequestBound cfg) xs packet cfg.queueCapacity cut room old fresh
  exact (Encoding.cells_success _ _ _).mpr
    ⟨h.1,fun p hp => (Encoding.requestPacket_success cfg p).mpr (h.2 p hp)⟩

theorem reply_append_encodes (cfg : Config) (xs : List ReplyPacket) (packet : ReplyPacket)
    (room : xs.length < cfg.queueCapacity) (old : ∀ p ∈ xs, ReplyBound cfg p)
    (fresh : ReplyBound cfg packet) (cut : Nat) :
    (Encoding.sequence (Encoding.replyPacket cfg.lifetime) cfg.queueCapacity).encode
      ((xs ++ [packet]).drop cut) ≠ none := by
  have h := queue_append_cut (ReplyBound cfg) xs packet cfg.queueCapacity cut room old fresh
  exact (Encoding.cells_success _ _ _).mpr
    ⟨h.1,fun p hp => (Encoding.replyPacket_success cfg p).mpr (h.2 p hp)⟩

/-- The source and helper ownership bound also applies to deletion filters,
which retain their source while materializing a smaller table. -/
theorem peer_filter_cut {cfg : Config} {s : PeerSnapshot}
    (h : PeerBound cfg s) (target cut : Nat) :
    RecordsBound cfg.lifetime cfg.outcomeCapacity Prod.fst
      ((s.entries.drop cut).filter (fun r => target ≤ r.1)) :=
  ((show RecordsBound cfg.lifetime cfg.outcomeCapacity Prod.fst s.entries from
    ⟨h.2.2.1,h.2.2.2⟩).drop cut).filter _

/-- A bank record replacement retains the source, the actual `take` temporary,
and the append result at once. These occupy distinct allocated regions. -/
theorem bank_copy_cut {bound capacity : Nat} {key : α → Nat} {xs : List α}
    (h : RecordsBound bound capacity key xs) (index : Nat) (record : α)
    (indexBound : index < capacity) (recordBound : key record ≤ bound) (cut : Nat) :
    RecordsBound bound capacity key (xs.take index) ∧
    RecordsBound bound capacity key (((xs.take index) ++ [record]).drop cut) := by
  refine ⟨h.take index,?_⟩
  have room : (xs.take index).length < capacity := (List.length_take_le index xs).trans_lt indexBound
  exact queue_append_cut (fun r => key r ≤ bound) (xs.take index) record capacity cut room
    (h.take index).2 recordBound

/-- The rejecting helper really constructs one record when U is zero. -/
example : (peerDecisionCore ⟨4,0,2⟩ {} 0 (.reserve true)) = .error .full := by decide
example : (peerStep [] 0 (.reserve true)).peer.length = 1 := by decide
example : RecordsBound 4 1 Prod.fst (peerStep [] 0 (.reserve true)).peer :=
  peerStep_records (cfg := ⟨4,0,2⟩) (s := {}) (by decide) 0 (.reserve true) (by decide)

end Workspace
end FRPSpec.PendingRetention
