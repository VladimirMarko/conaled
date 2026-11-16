import Applications.Durability.SnapshotBanks
import Applications.FRP.PendingRetention.Model

/-! The pending consumer stores typed headers and bounded record populations.
Bank mechanics express persistence only; source provenance is proved by the
closed service executor, never assumed by a bank payload field. -/
namespace FRPSpec.PendingRetention
open Durability

abbrev LocalHeader := PendingCrash.Frame × Nat × Option Nat
abbrev PeerHeader := Nat × Option Nat
abbrev LocalPayload := SnapshotBanks.Snapshot LocalHeader Outcome
abbrev PeerPayload := SnapshotBanks.Snapshot PeerHeader (Nat × PendingMigration.Ledger)

def LocalSnapshot.encode (s : LocalSnapshot) : LocalPayload :=
  ⟨(s.frame,s.floor,s.pending),s.outcomes⟩
def LocalSnapshot.decode (s : LocalPayload) : LocalSnapshot :=
  ⟨s.header.1,s.header.2.1,s.header.2.2,s.items⟩
def PeerSnapshot.encode (s : PeerSnapshot) : PeerPayload :=
  ⟨(s.floor,s.pending),s.entries⟩
def PeerSnapshot.decode (s : PeerPayload) : PeerSnapshot :=
  ⟨s.header.1,s.header.2,s.items⟩

@[simp] theorem LocalSnapshot.decode_encode (s : LocalSnapshot) : LocalSnapshot.decode s.encode = s := rfl
@[simp] theorem PeerSnapshot.decode_encode (s : PeerSnapshot) : PeerSnapshot.decode s.encode = s := rfl
@[simp] theorem LocalSnapshot.encode_decode (s : LocalPayload) : (LocalSnapshot.decode s).encode = s := rfl
@[simp] theorem PeerSnapshot.encode_decode (s : PeerPayload) : (PeerSnapshot.decode s).encode = s := rfl

abbrev LocalBanks := SnapshotBanks.Worker LocalHeader Outcome
abbrev PeerBanks := SnapshotBanks.Worker PeerHeader (Nat × PendingMigration.Ledger)

def localSeed : LocalHeader := (PendingCrash.initialFrame,0,none)
def peerSeed : PeerHeader := (0,none)

def LocalBanks.selected (b : LocalBanks) : LocalSnapshot := LocalSnapshot.decode b.state.disk.root
def PeerBanks.selected (b : PeerBanks) : PeerSnapshot := PeerSnapshot.decode b.state.disk.root

def LocalBanks.begin (b : LocalBanks) (target : LocalSnapshot) : LocalBanks :=
  SnapshotBanks.begin localSeed b.state.disk target.encode
def PeerBanks.begin (b : PeerBanks) (target : PeerSnapshot) : PeerBanks :=
  SnapshotBanks.begin peerSeed b.state.disk target.encode

def LocalBanks.nextOperation (b : LocalBanks) := SnapshotBanks.operationAt b.target b.cursor.val
def PeerBanks.nextOperation (b : PeerBanks) := SnapshotBanks.operationAt b.target b.cursor.val

def LocalBanks.progress (b : LocalBanks) : LocalBanks × Bool := SnapshotBanks.Worker.progress b
def PeerBanks.progress (b : PeerBanks) : PeerBanks × Bool := SnapshotBanks.Worker.progress b

def LocalBanks.busy (b : LocalBanks) : Bool := SnapshotBanks.Worker.busy b
def PeerBanks.busy (b : PeerBanks) : Bool := SnapshotBanks.Worker.busy b

/-- Idle and recovered states retain two persistent banks and empty volatile
regions; no previous target or instruction list survives a crash. -/
def idle (disk : SnapshotBanks.Banks H R) (seed : H) : SnapshotBanks.Worker H R :=
  ⟨⟨disk,SnapshotBanks.empty seed⟩,SnapshotBanks.empty seed,⟨3,by simp [SnapshotBanks.empty]⟩⟩

def LocalBanks.crash (b : LocalBanks) : LocalBanks := idle b.state.disk localSeed
def PeerBanks.crash (b : PeerBanks) : PeerBanks := idle b.state.disk peerSeed

def LocalBanks.initial (s : LocalSnapshot := {}) : LocalBanks :=
  idle ⟨fun _ => s.encode,false⟩ localSeed
def PeerBanks.initial (s : PeerSnapshot := {}) : PeerBanks :=
  idle ⟨fun _ => s.encode,false⟩ peerSeed

@[simp] theorem LocalBanks.crash_selected (b : LocalBanks) : b.crash.selected = b.selected := rfl
@[simp] theorem PeerBanks.crash_selected (b : PeerBanks) : b.crash.selected = b.selected := rfl
@[simp] theorem LocalBanks.begin_selected (b : LocalBanks) (s : LocalSnapshot) :
    (b.begin s).selected = b.selected := rfl
@[simp] theorem PeerBanks.begin_selected (b : PeerBanks) (s : PeerSnapshot) :
    (b.begin s).selected = b.selected := rfl

theorem idle_bounded (hb : H → Prop) (rb : R → Prop) (capacity : Nat)
    (disk : SnapshotBanks.Banks H R) (seed : H) (hs : hb seed)
    (hd : ∀ bank,(disk.cells bank).Bounded hb rb capacity) :
    (idle disk seed).Bounded hb rb capacity := by
  exact ⟨⟨hd,hs,Nat.zero_le _,by intro r hr; exact False.elim (List.not_mem_nil hr)⟩,
    hs,Nat.zero_le _,by intro r hr; exact False.elim (List.not_mem_nil hr)⟩

theorem LocalBanks.progress_stutters (b : LocalBanks) (h : b.progress.2 = false) :
    b.progress.1.selected = b.selected :=
  congrArg LocalSnapshot.decode (SnapshotBanks.Worker.progress_stutters b h)
theorem PeerBanks.progress_stutters (b : PeerBanks) (h : b.progress.2 = false) :
    b.progress.1.selected = b.selected :=
  congrArg PeerSnapshot.decode (SnapshotBanks.Worker.progress_stutters b h)

theorem LocalBanks.progress_publishes (b : LocalBanks) (start : SnapshotBanks.Banks LocalHeader Outcome)
    (hc : b.AtCut start localSeed) (h : b.progress.2 = true) :
    b.progress.1.selected = LocalSnapshot.decode b.target :=
  congrArg LocalSnapshot.decode (SnapshotBanks.Worker.progress_publishes localSeed b start hc h)
theorem PeerBanks.progress_publishes (b : PeerBanks)
    (start : SnapshotBanks.Banks PeerHeader (Nat × PendingMigration.Ledger))
    (hc : b.AtCut start peerSeed) (h : b.progress.2 = true) :
    b.progress.1.selected = PeerSnapshot.decode b.target :=
  congrArg PeerSnapshot.decode (SnapshotBanks.Worker.progress_publishes peerSeed b start hc h)


theorem local_replacement_allowed (b : LocalBanks) (target : LocalSnapshot) :
    SnapshotBanks.Allowed (b.begin target).state (SnapshotBanks.replacement target.encode) :=
  SnapshotBanks.replacement_allowed b.state.disk target.encode localSeed

theorem peer_replacement_allowed (b : PeerBanks) (target : PeerSnapshot) :
    SnapshotBanks.Allowed (b.begin target).state (SnapshotBanks.replacement target.encode) :=
  SnapshotBanks.replacement_allowed b.state.disk target.encode peerSeed

/-- The serialized driver's mutation view permits the inactive overwrite. This
is an ownership obligation, not permission derived from payload validity. -/
theorem inactive_overwrite (selected : Bool) :
    (SnapshotBanks.Access.mutation selected).safeOverwrite (!selected) ∧ selected ≠ !selected :=
  SnapshotBanks.mutation_safe selected


/-- Direct local payload copy is the comparison specification, not another service. -/
structure DirectLocal where
  cells : Bool → LocalSnapshot
  selector : Bool
  buffer : LocalSnapshot

def DirectLocal.encode (s : DirectLocal) : SnapshotBanks.CopyState LocalHeader (Outcome) :=
  ⟨⟨fun b => (s.cells b).encode,s.selector⟩,s.buffer.encode⟩

def directLocalPrimitive (s : DirectLocal) : SnapshotBanks.Primitive LocalHeader (Outcome) → DirectLocal
  | .writeRecord i r => {s with buffer := {s.buffer with outcomes := s.buffer.outcomes.take i ++ [r]}}
  | .persistRecord i r =>
    {s with cells := fun b => if b = !s.selector then
      {s.cells b with outcomes := (s.cells b).outcomes.take i ++ [r]} else s.cells b}
  | .writeHeader h => {s with buffer := {s.buffer with frame := h.1, floor := h.2.1, pending := h.2.2}}
  | .persistHeader h => {s with cells := fun b => if b = !s.selector then
      {s.buffer with frame := h.1, floor := h.2.1, pending := h.2.2} else s.cells b}
  | .publish => {s with selector := !s.selector}

theorem directLocal_commutes (s : DirectLocal) (op : SnapshotBanks.Primitive LocalHeader (Outcome)) :
    (directLocalPrimitive s op).encode = SnapshotBanks.primitive s.encode op := by
  cases op <;> simp [directLocalPrimitive,DirectLocal.encode,LocalSnapshot.encode,
    SnapshotBanks.primitive,SnapshotBanks.Banks.putInactive]
  all_goals funext b; split <;> simp_all

theorem directLocal_fold (s : DirectLocal) (ops : List (SnapshotBanks.Primitive LocalHeader (Outcome))) :
    (ops.foldl directLocalPrimitive s).encode = ops.foldl SnapshotBanks.primitive s.encode := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih => simp only [List.foldl_cons,ih,directLocal_commutes]

def directLocalCut (cells : Bool → LocalSnapshot) (selector : Bool)
    (target : LocalSnapshot) (n : Nat) : DirectLocal :=
  ((SnapshotBanks.replacement target.encode).take n).foldl directLocalPrimitive ⟨cells,selector,{}⟩

theorem directLocal_cut (cells : Bool → LocalSnapshot) (selector : Bool)
    (target : LocalSnapshot) (n : Nat) :
    (directLocalCut cells selector target n).encode =
      SnapshotBanks.cut ⟨fun b => (cells b).encode,selector⟩ target.encode localSeed n := by
  rw [directLocalCut,directLocal_fold]
  rfl

theorem directLocal_old_or_new (cells : Bool → LocalSnapshot) (selector : Bool)
    (target : LocalSnapshot) (n : Nat) :
    let result := directLocalCut cells selector target n
    result.cells result.selector = cells selector ∨ result.cells result.selector = target := by
  have eq := congrArg (fun s : SnapshotBanks.CopyState LocalHeader (Outcome) => s.disk.root)
    (directLocal_cut cells selector target n)
  rcases SnapshotBanks.cut_old_or_new ⟨fun b => (cells b).encode,selector⟩ target.encode localSeed n with h | h
  · exact Or.inl (congrArg LocalSnapshot.decode (eq.trans h))
  · exact Or.inr (congrArg LocalSnapshot.decode (eq.trans h))

/-- Direct peer payload copy is the comparison specification, not another service. -/
structure DirectPeer where
  cells : Bool → PeerSnapshot
  selector : Bool
  buffer : PeerSnapshot

def DirectPeer.encode (s : DirectPeer) : SnapshotBanks.CopyState PeerHeader (Nat × PendingMigration.Ledger) :=
  ⟨⟨fun b => (s.cells b).encode,s.selector⟩,s.buffer.encode⟩

def directPeerPrimitive (s : DirectPeer) : SnapshotBanks.Primitive PeerHeader (Nat × PendingMigration.Ledger) → DirectPeer
  | .writeRecord i r => {s with buffer := {s.buffer with entries := s.buffer.entries.take i ++ [r]}}
  | .persistRecord i r =>
    {s with cells := fun b => if b = !s.selector then
      {s.cells b with entries := (s.cells b).entries.take i ++ [r]} else s.cells b}
  | .writeHeader h => {s with buffer := {s.buffer with floor := h.1, pending := h.2}}
  | .persistHeader h => {s with cells := fun b => if b = !s.selector then
      {s.buffer with floor := h.1, pending := h.2} else s.cells b}
  | .publish => {s with selector := !s.selector}

theorem directPeer_commutes (s : DirectPeer) (op : SnapshotBanks.Primitive PeerHeader (Nat × PendingMigration.Ledger)) :
    (directPeerPrimitive s op).encode = SnapshotBanks.primitive s.encode op := by
  cases op <;> simp [directPeerPrimitive,DirectPeer.encode,PeerSnapshot.encode,
    SnapshotBanks.primitive,SnapshotBanks.Banks.putInactive]
  all_goals funext b; split <;> simp_all

theorem directPeer_fold (s : DirectPeer) (ops : List (SnapshotBanks.Primitive PeerHeader (Nat × PendingMigration.Ledger))) :
    (ops.foldl directPeerPrimitive s).encode = ops.foldl SnapshotBanks.primitive s.encode := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih => simp only [List.foldl_cons,ih,directPeer_commutes]

def directPeerCut (cells : Bool → PeerSnapshot) (selector : Bool)
    (target : PeerSnapshot) (n : Nat) : DirectPeer :=
  ((SnapshotBanks.replacement target.encode).take n).foldl directPeerPrimitive ⟨cells,selector,{}⟩

theorem directPeer_cut (cells : Bool → PeerSnapshot) (selector : Bool)
    (target : PeerSnapshot) (n : Nat) :
    (directPeerCut cells selector target n).encode =
      SnapshotBanks.cut ⟨fun b => (cells b).encode,selector⟩ target.encode peerSeed n := by
  rw [directPeerCut,directPeer_fold]
  rfl

theorem directPeer_old_or_new (cells : Bool → PeerSnapshot) (selector : Bool)
    (target : PeerSnapshot) (n : Nat) :
    let result := directPeerCut cells selector target n
    result.cells result.selector = cells selector ∨ result.cells result.selector = target := by
  have eq := congrArg (fun s : SnapshotBanks.CopyState PeerHeader (Nat × PendingMigration.Ledger) => s.disk.root)
    (directPeer_cut cells selector target n)
  rcases SnapshotBanks.cut_old_or_new ⟨fun b => (cells b).encode,selector⟩ target.encode peerSeed n with h | h
  · exact Or.inl (congrArg PeerSnapshot.decode (eq.trans h))
  · exact Or.inr (congrArg PeerSnapshot.decode (eq.trans h))

end FRPSpec.PendingRetention
