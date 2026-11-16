import Applications.FRP.PendingRetention.Runtime
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Log

/-! Explicit finite field encodings for the bounded executor. Each bounded
sequence has fixed cells with occupancy tags; proof histories are not encoded. -/
namespace FRPSpec.PendingRetention
open PendingCrash PendingMigration

namespace Encoding

/-- Successful encoding recovers every stored field, not only observations. -/
structure Codec (α β : Type) where
  encode : α → Option β
  decode : β → α
  recover : ∀ a b, encode a = some b → decode b = a

def identity (α : Type) : Codec α α := ⟨some,id,by intro a b h; cases h; rfl⟩

def number (limit : Nat) : Codec Nat (Fin (limit + 1)) where
  encode n := if h : n ≤ limit then some ⟨n,by omega⟩ else none
  decode n := n.val
  recover a b h := by
    split at h
    · cases h; rfl
    · contradiction

theorem number_success (limit n : Nat) : (number limit).encode n ≠ none ↔ n ≤ limit := by
  simp [number]

def product (a : Codec α α') (b : Codec β β') : Codec (α × β) (α' × β') where
  encode x := do
    let left ← a.encode x.1
    let right ← b.encode x.2
    pure (left,right)
  decode x := (a.decode x.1,b.decode x.2)
  recover x y h := by
    simp only [Option.bind_eq_bind,Option.bind_eq_some_iff] at h
    obtain ⟨l,hl,r,hr,he⟩ := h
    cases he
    exact Prod.ext (a.recover _ _ hl) (b.recover _ _ hr)

def optional (a : Codec α β) : Codec (Option α) (Option β) where
  encode
    | none => some none
    | some x => (a.encode x).map some
  decode x := x.map a.decode
  recover x y h := by
    cases x with
    | none => cases h; rfl
    | some x =>
      obtain ⟨b,hb,he⟩ := Option.map_eq_some_iff.mp h
      subst y
      simp [a.recover x b hb]

/-- Retractions describe structure fields without changing their semantics. -/
def fields (a : Codec α β) (split : γ → α) (join : α → γ)
    (roundtrip : ∀ x,join (split x) = x) : Codec γ β where
  encode x := a.encode (split x)
  decode x := join (a.decode x)
  recover x y h := by rw [a.recover _ _ h,roundtrip]

/-- Fixed cells include stale/empty capacity. Length is represented by the
occupancy tags; no unbounded list tail is part of this representation. -/
def Cells (α : Type) : Nat → Type
  | 0 => Unit
  | n + 1 => Option α × Cells α n

instance cellsFinite [Finite α] (n : Nat) : Finite (Cells α n) := by
  induction n with
  | zero => exact inferInstanceAs (Finite Unit)
  | succ n ih => exact inferInstanceAs (Finite (Option α × Cells α n))

def encodeCells (a : Codec α β) : (n : Nat) → List α → Option (Cells β n)
  | 0, [] => some ()
  | 0, _ :: _ => none
  | n + 1, [] => do
      let tail ← encodeCells a n []
      pure (none,tail)
  | n + 1, x :: xs => do
      let head ← a.encode x
      let tail ← encodeCells a n xs
      pure (some head,tail)

def decodeCells (a : Codec α β) : (n : Nat) → Cells β n → List α
  | 0, _ => []
  | n + 1, (head,tail) => head.toList.map a.decode ++ decodeCells a n tail

theorem cells_recover (a : Codec α β) (n : Nat) (xs : List α) (code : Cells β n)
    (h : encodeCells a n xs = some code) : decodeCells a n code = xs := by
  induction n generalizing xs with
  | zero => cases xs <;> simp_all [encodeCells,decodeCells]
  | succ n ih =>
    cases xs with
    | nil =>
      simp only [encodeCells,Option.bind_eq_bind,Option.bind_eq_some_iff] at h
      obtain ⟨tail,ht,he⟩ := h
      cases he
      simpa [decodeCells] using ih [] tail ht
    | cons x xs =>
      simp only [encodeCells,Option.bind_eq_bind,Option.bind_eq_some_iff] at h
      obtain ⟨head,hh,tail,ht,he⟩ := h
      cases he
      simp [decodeCells,a.recover x head hh,ih xs tail ht]

def sequence (a : Codec α β) (capacity : Nat) : Codec (List α) (Cells β capacity) :=
  ⟨encodeCells a capacity,decodeCells a capacity,cells_recover a capacity⟩

theorem cells_success (a : Codec α β) (n : Nat) (xs : List α) :
    encodeCells a n xs ≠ none ↔ xs.length ≤ n ∧ ∀ x ∈ xs,a.encode x ≠ none := by
  induction n generalizing xs with
  | zero => cases xs <;> simp [encodeCells]
  | succ n ih =>
    cases xs with
    | nil =>
      have hh := ih []
      cases ht : encodeCells a n [] <;> simp_all [encodeCells]
    | cons x xs =>
      have hh := ih xs
      cases hx : a.encode x <;> cases ht : encodeCells a n xs <;>
        simp_all [encodeCells]


@[simp] theorem product_success (a : Codec α α') (b : Codec β β') (x : α × β) :
    (product a b).encode x ≠ none ↔ a.encode x.1 ≠ none ∧ b.encode x.2 ≠ none := by
  cases ha : a.encode x.1 <;> cases hb : b.encode x.2 <;> simp [product,ha,hb]

@[simp] theorem optional_success (a : Codec α β) (x : Option α) :
    (optional a).encode x ≠ none ↔ ∀ v ∈ x,a.encode v ≠ none := by
  cases x <;> simp [optional]

@[simp] theorem fields_success (a : Codec α β) (split : γ → α) (join : α → γ)
    (h : ∀ x,join (split x) = x) (x : γ) :
    (fields a split join h).encode x ≠ none ↔ a.encode (split x) ≠ none := Iff.rfl

instance : Fintype Migration.Kind := ⟨{.delay,.redundant},by intro x; cases x <;> simp⟩
instance : Fintype Phase :=
  ⟨{.accepted,.computed,.confirmed,.committed,.cancelled},by intro x; cases x <;> simp⟩
deriving instance Fintype for Answer
deriving instance Fintype for Ledger
deriving instance Fintype for PeerCommand

abbrev Name (limit : Nat) := Fin (limit + 1)
abbrev ReceiptCode (limit : Nat) := Name limit × Answer

def receipt (limit : Nat) : Codec Receipt (ReceiptCode limit) :=
  fields (product (number limit) (identity Answer))
    (fun r => (r.identity,r.answer)) (fun r => ⟨r.1,r.2⟩) (by intro r; cases r; rfl)

abbrev RequestCode (limit : Nat) :=
  Name limit × Bool × Option Bool × Option (ReceiptCode limit) × Phase × Bool

def request (limit : Nat) : Codec PendingCrash.Request (RequestCode limit) :=
  fields (product (number limit) (product (identity Bool) (product (identity (Option Bool))
    (product (optional (receipt limit)) (product (identity Phase) (identity Bool))))))
    (fun r => (r.identity,r.input,r.output,r.receipt,r.phase,r.routeOpen))
    (fun r => ⟨r.1,r.2.1,r.2.2.1,r.2.2.2.1,r.2.2.2.2.1,r.2.2.2.2.2⟩)
    (by intro r; cases r; rfl)

abbrev FrameCode (limit : Nat) := Migration.Kind × Bool ×
  (Option (RequestCode limit) × Option (RequestCode limit)) × Cells Bool 2 × Name limit

def frame (limit : Nat) : Codec Frame (FrameCode limit) :=
  fields (product (identity Migration.Kind) (product (identity Bool)
    (product (product (optional (request limit)) (optional (request limit)))
      (product (sequence (identity Bool) 2) (number limit)))))
    (fun f => (f.kind,f.logical,(f.requests.left,f.requests.right),f.order,f.nextIdentity))
    (fun f => ⟨f.1,f.2.1,⟨f.2.2.1.1,f.2.2.1.2⟩,f.2.2.2.1,f.2.2.2.2⟩)
    (by intro f; cases f with | mk k b r o n => cases r; rfl)

abbrev OutcomeCode (limit : Nat) := Name limit × Bool × Option Answer × Bool

def outcome (limit : Nat) : Codec Outcome (OutcomeCode limit) :=
  fields (product (number limit) (product (identity Bool)
    (product (identity (Option Answer)) (identity Bool))))
    (fun r => (r.identity,r.input,r.answer,r.released))
    (fun r => ⟨r.1,r.2.1,r.2.2.1,r.2.2.2⟩) (by intro r; cases r; rfl)

abbrev LocalHeaderCode (limit : Nat) := FrameCode limit × Name limit × Option (Name limit)
abbrev PeerHeaderCode (limit : Nat) := Name limit × Option (Name limit)

def localHeader (limit : Nat) : Codec LocalHeader (LocalHeaderCode limit) :=
  product (frame limit) (product (number limit) (optional (number limit)))
def peerHeader (limit : Nat) : Codec PeerHeader (PeerHeaderCode limit) :=
  product (number limit) (optional (number limit))

/-- Both banks, target staging and copy/recovery buffers use this same code. -/
abbrev SnapshotCode (H R : Type) (capacity : Nat) := H × Cells R capacity

def snapshot (header : Codec H H') (record : Codec R R') (capacity : Nat) :
    Codec (Durability.SnapshotBanks.Snapshot H R) (SnapshotCode H' R' capacity) :=
  fields (product header (sequence record capacity))
    (fun s => (s.header,s.items)) (fun s => ⟨s.1,s.2⟩) (by intro s; cases s; rfl)

@[simp] theorem receipt_success (limit : Nat) (r : Receipt) :
    (receipt limit).encode r ≠ none ↔ r.identity ≤ limit := by
  simp [receipt,identity,number_success]

@[simp] theorem request_success (limit : Nat) (r : PendingCrash.Request) :
    (request limit).encode r ≠ none ↔
      r.identity ≤ limit ∧ ∀ t ∈ r.receipt,t.identity ≤ limit := by
  simp [request,identity,number_success]

@[simp] theorem outcome_success (limit : Nat) (r : Outcome) :
    (outcome limit).encode r ≠ none ↔ r.identity ≤ limit := by
  simp [outcome,identity,number_success]


abbrev RequestPacketCode (limit : Nat) := Bool × Name limit × PeerCommand

def requestPacket (limit : Nat) : Codec RequestPacket (RequestPacketCode limit) :=
  fields (product (identity Bool) (product (number limit) (identity PeerCommand)))
    (fun p => match p with | .business i c => (false,i,c) | .retire t => (true,t,.query))
    (fun p => if p.1 then .retire p.2.1 else .business p.2.1 p.2.2)
    (by intro p; cases p <;> rfl)

abbrev ReplyPacketCode (limit : Nat) := Fin 3 × Name limit × Name limit × Answer

def replyPacket (limit : Nat) : Codec ReplyPacket (ReplyPacketCode limit) :=
  fields (product (identity (Fin 3)) (product (number limit)
    (product (number limit) (identity Answer))))
    (fun p => match p with
      | .receipt r => (0,r.identity,0,r.answer)
      | .expired i f => (1,i,f,.absent)
      | .deleted t => (2,t,0,.absent))
    (fun p => if p.1 = 0 then .receipt ⟨p.2.1,p.2.2.2⟩
      else if p.1 = 1 then .expired p.2.1 p.2.2.1 else .deleted p.2.1)
    (by intro p; cases p <;> rfl)

abbrev FrameCommandCode (limit : Nat) := Fin 7 × Bool × Option (ReceiptCode limit) × Migration.Kind

def frameCommand (limit : Nat) : Codec FrameCommand (FrameCommandCode limit) :=
  fields (product (identity (Fin 7)) (product (identity Bool)
    (product (optional (receipt limit)) (identity Migration.Kind))))
    (fun c => match c with
      | .accept x => (0,x,none,.delay)
      | .evaluate => (1,false,none,.delay)
      | .receive r => (2,false,some r,.delay)
      | .tickCommit => (3,false,none,.delay)
      | .close => (4,false,none,.delay)
      | .release => (5,false,none,.delay)
      | .migrate k => (6,false,none,k))
    (fun c => if c.1 = 0 then .accept c.2.1 else if c.1 = 1 then .evaluate
      else if c.1 = 2 then .receive (c.2.2.1.getD ⟨0,.absent⟩)
      else if c.1 = 3 then .tickCommit else if c.1 = 4 then .close
      else if c.1 = 5 then .release else .migrate c.2.2.2)
    (by intro c; cases c <;> rfl)

abbrev LocalCauseCode (limit : Nat) := Fin 3 × FrameCommandCode limit × Name limit

def localCause (limit : Nat) : Codec LocalCause (LocalCauseCode limit) :=
  fields (product (identity (Fin 3)) (product (frameCommand limit) (number limit)))
    (fun c => match c with
      | .frame f => (0,f,0) | .relinquish t => (1,.evaluate,t) | .finish t => (2,.evaluate,t))
    (fun c => if c.1 = 0 then .frame c.2.1 else if c.1 = 1 then .relinquish c.2.2 else .finish c.2.2)
    (by intro c; cases c <;> rfl)

abbrev PeerCauseCode (limit : Nat) :=
  Fin 3 × Name limit × PeerCommand × ReplyPacketCode limit × Option Bool × Option Bool

def peerCause (limit : Nat) : Codec PeerCause (PeerCauseCode limit) :=
  fields (product (identity (Fin 3)) (product (number limit) (product (identity PeerCommand)
    (product (replyPacket limit) (product (identity (Option Bool)) (identity (Option Bool)))))))
    (fun c => match c with
      | .business i q r e p => (0,i,q,r,e,p)
      | .floor t => (1,t,.query,.deleted 0,none,none)
      | .deletion t => (2,t,.query,.deleted 0,none,none))
    (fun c => if c.1 = 0 then .business c.2.1 c.2.2.1 c.2.2.2.1 c.2.2.2.2.1 c.2.2.2.2.2
      else if c.1 = 1 then .floor c.2.1 else .deletion c.2.1)
    (by intro c; cases c <;> rfl)

/-- The redundant backend's second cell is encoded as well as its logical bit. -/
def backend : Codec Migration.Backend (Migration.Kind × Bool × Bool) :=
  fields (identity (Migration.Kind × Bool × Bool))
    (fun b => match b with | .delay x => (.delay,x,false) | .redundant p => (.redundant,p.first,p.second))
    (fun b => Migration.realize b.1 b.2.1)
    (by intro b; cases b with
        | delay x => rfl
        | redundant p => cases p with | mk x y h => cases h; rfl)

@[simp] theorem requestPacket_success (cfg : Config) (p : RequestPacket) :
    (requestPacket cfg.lifetime).encode p ≠ none ↔ RequestBound cfg p := by
  cases p <;> simp [requestPacket,identity,number_success,RequestBound]

@[simp] theorem replyPacket_success (cfg : Config) (p : ReplyPacket) :
    (replyPacket cfg.lifetime).encode p ≠ none ↔ ReplyBound cfg p := by
  cases p <;> simp [replyPacket,identity,number_success,ReplyBound]

@[simp] theorem frameCommand_success (cfg : Config) (c : FrameCommand) :
    (frameCommand cfg.lifetime).encode c ≠ none ↔ CommandBound cfg c := by
  cases c <;> simp [frameCommand,identity,CommandBound]


abbrev WorkerCode (H R : Type) (capacity : Nat) :=
  (SnapshotCode H R capacity × SnapshotCode H R capacity) × Bool ×
    SnapshotCode H R capacity × SnapshotCode H R capacity × Name (2 * capacity + 3)

def worker (header : Codec H H') (record : Codec R R') (capacity : Nat) :
    Codec (Durability.SnapshotBanks.Worker H R) (WorkerCode H' R' capacity) :=
  fields
    (product (product (snapshot header record capacity) (snapshot header record capacity))
      (product (identity Bool) (product (snapshot header record capacity)
        (product (snapshot header record capacity) (number (2 * capacity + 3))))))
    (fun w => ((w.state.disk.cells false,w.state.disk.cells true),w.state.disk.selected,
      w.state.buffer,w.target,w.cursor.val))
    (fun w => ⟨⟨⟨fun b => if b then w.1.2 else w.1.1,w.2.1⟩,w.2.2.1⟩,
      w.2.2.2.1,⟨min w.2.2.2.2 (2 * w.2.2.2.1.items.length + 3),by omega⟩⟩)
    (by
      rintro ⟨⟨⟨cells,selected⟩,buffer⟩,target,cursor⟩
      have he : (fun b => if b then cells true else cells false) = cells := by
        funext b; cases b <;> rfl
      simp only [he]
      congr 1
      apply Fin.ext
      exact Nat.min_eq_left (by have := cursor.isLt; omega))

abbrev LocalCode (cfg : Config) := WorkerCode (LocalHeaderCode cfg.lifetime)
  (OutcomeCode cfg.lifetime) cfg.outcomeCapacity
abbrev PeerCode (cfg : Config) := WorkerCode (PeerHeaderCode cfg.lifetime)
  (Name cfg.lifetime × Ledger) cfg.outcomeCapacity
abbrev BackendCode := Migration.Kind × Bool × Bool
abbrev SystemCode (cfg : Config) :=
  LocalCode cfg × PeerCode cfg × Option (LocalCauseCode cfg.lifetime) ×
  Option (PeerCauseCode cfg.lifetime) × Cells (RequestPacketCode cfg.lifetime) cfg.queueCapacity ×
  Cells (RequestPacketCode cfg.lifetime) cfg.queueCapacity × Cells (ReplyPacketCode cfg.lifetime) cfg.queueCapacity ×
  Cells (ReplyPacketCode cfg.lifetime) cfg.queueCapacity × Bool × Bool ×
  Option BackendCode × Option BackendCode × Option BackendCode × Option (Name cfg.lifetime × Name cfg.lifetime)

def system (cfg : Config) : Codec System (SystemCode cfg) :=
  fields
    (product (worker (localHeader cfg.lifetime) (outcome cfg.lifetime) cfg.outcomeCapacity)
    (product (worker (peerHeader cfg.lifetime) (product (number cfg.lifetime) (identity Ledger)) cfg.outcomeCapacity)
    (product (optional (localCause cfg.lifetime)) (product (optional (peerCause cfg.lifetime))
    (product (sequence (requestPacket cfg.lifetime) cfg.queueCapacity)
    (product (sequence (requestPacket cfg.lifetime) cfg.queueCapacity)
    (product (sequence (replyPacket cfg.lifetime) cfg.queueCapacity)
    (product (sequence (replyPacket cfg.lifetime) cfg.queueCapacity)
    (product (identity Bool) (product (identity Bool)
    (product (optional backend) (product (optional backend) (product (optional backend)
      (optional (product (number cfg.lifetime) (number cfg.lifetime))))))))))))))))
    (fun s => (s.localBank,s.peer,s.localCause,s.peerCause,s.localOut,s.peerIn,s.peerOut,s.localIn,
      s.localDown,s.peerDown,s.active,s.prepared,s.former,s.retirementScan))
    (fun s => ⟨s.1,s.2.1,s.2.2.1,s.2.2.2.1,s.2.2.2.2.1,s.2.2.2.2.2.1,
      s.2.2.2.2.2.2.1,s.2.2.2.2.2.2.2.1,s.2.2.2.2.2.2.2.2.1,
      s.2.2.2.2.2.2.2.2.2.1,s.2.2.2.2.2.2.2.2.2.2.1,
      s.2.2.2.2.2.2.2.2.2.2.2.1,s.2.2.2.2.2.2.2.2.2.2.2.2.1,s.2.2.2.2.2.2.2.2.2.2.2.2.2⟩)
    (by intro s; cases s; rfl)

set_option synthInstance.maxSize 4096 in
instance (cfg : Config) : Finite (SystemCode cfg) := by
  unfold SystemCode LocalCode PeerCode WorkerCode SnapshotCode LocalHeaderCode PeerHeaderCode
    FrameCode RequestCode ReceiptCode OutcomeCode LocalCauseCode FrameCommandCode PeerCauseCode
    RequestPacketCode ReplyPacketCode BackendCode Name
  infer_instance

/-- Exact inverse on successful encoding. Invalid scalar ranges or population
lengths are rejected by the component codecs. -/
theorem system_recover (cfg : Config) (s : System) (code : SystemCode cfg)
    (h : (system cfg).encode s = some code) : (system cfg).decode code = s :=
  (system cfg).recover s code h


/-- Constructive fixed-width packing. The width follows the actual code fields;
no enumerated runtime history or cardinality-based choice is used. -/
class Bits (α : Type) where
  width : Nat
  pack : α → Fin (2 ^ width)
  injective : Function.Injective pack

instance : Bits Unit := ⟨0,fun _ => 0,by intro a b h; cases a; cases b; rfl⟩
instance : Bits Bool := ⟨1,fun b => ⟨b.toNat,by cases b <;> decide⟩,
  by intro a b h; cases a <;> cases b <;> simp_all⟩
instance (n : Nat) : Bits (Fin n) :=
  ⟨Nat.clog 2 n,fun i => ⟨i.val,i.isLt.trans_le (Nat.le_pow_clog (by decide) n)⟩,
    by intro a b h; exact Fin.ext (congrArg (fun i : Fin (2 ^ Nat.clog 2 n) => i.val) h)⟩

instance productBits [a : Bits α] [b : Bits β] : Bits (α × β) where
  width := a.width + b.width
  pack x := ⟨2 ^ b.width * (a.pack x.1).val + (b.pack x.2).val,by
    rw [Nat.pow_add]
    have ha := (a.pack x.1).isLt
    have hb := (b.pack x.2).isLt
    nlinarith⟩
  injective := by
    intro x y h
    have eq := congrArg Fin.val h
    have left := congrArg (fun n => n / 2 ^ b.width) eq
    have right := congrArg (fun n => n % 2 ^ b.width) eq
    have pos : 0 < 2 ^ b.width := Nat.two_pow_pos _
    simp only [Nat.mul_add_div pos,Nat.div_eq_of_lt (b.pack x.2).isLt,
      Nat.div_eq_of_lt (b.pack y.2).isLt,Nat.add_zero] at left
    simp only [Nat.mul_add_mod,Nat.mod_eq_of_lt (b.pack x.2).isLt,
      Nat.mod_eq_of_lt (b.pack y.2).isLt] at right
    exact Prod.ext (a.injective (Fin.ext left)) (b.injective (Fin.ext right))

instance optionBits [a : Bits α] : Bits (Option α) where
  width := a.width + 1
  pack x := match x with
    | none => ⟨0,by positivity⟩
    | some v => ⟨(a.pack v).val + 1,by
        have h := (a.pack v).isLt
        have pos : 0 < 2 ^ a.width := Nat.two_pow_pos _
        simp only [Nat.pow_succ]; omega⟩
  injective := by
    intro x y h
    cases x with
    | none => cases y with
      | none => rfl
      | some y => have := congrArg Fin.val h; dsimp at this; omega
    | some x => cases y with
      | none => have := congrArg Fin.val h; dsimp at this; omega
      | some y =>
        have hh := congrArg Fin.val h
        dsimp at hh
        have he : a.pack x = a.pack y := Fin.ext (by omega)
        exact congrArg some (a.injective he)

instance cellsBits [Bits α] : (n : Nat) → Bits (Cells α n)
  | 0 => inferInstanceAs (Bits Unit)
  | n + 1 => letI : Bits (Cells α n) := cellsBits n; inferInstanceAs (Bits (Option α × Cells α n))

private def kindCode : Migration.Kind → Fin 2 | .delay => 0 | .redundant => 1
instance : Bits Migration.Kind := ⟨1,kindCode,by decide⟩
private def phaseCode : Phase → Fin 8
  | .accepted => 0 | .computed => 1 | .confirmed => 2 | .committed => 3 | .cancelled => 4
instance : Bits Phase := ⟨3,phaseCode,by decide⟩
private def answerCode : Answer → Fin 16
  | .absent => 0
  | .reserved x => Fin.ofNat 16 (1 + x.toNat)
  | .published x y => Fin.ofNat 16 (3 + 2*x.toNat + y.toNat)
  | .prevented x => Fin.ofNat 16 (7 + x.toNat)
  | .tooLate x y => Fin.ofNat 16 (9 + 2*x.toNat + y.toNat)
  | .conflict => 13
instance : Bits Answer := ⟨4,answerCode,by decide⟩
private def ledgerCode : Ledger → Fin 8
  | .reserved x => Fin.ofNat 8 x.toNat
  | .published x y => Fin.ofNat 8 (2 + 2*x.toNat + y.toNat)
  | .cancelled x => Fin.ofNat 8 (6 + x.toNat)
instance : Bits Ledger := ⟨3,ledgerCode,by decide⟩
private def peerCommandCode : PeerCommand → Fin 16
  | .reserve x => Fin.ofNat 16 x.toNat
  | .query => 2
  | .publish x y => Fin.ofNat 16 (3 + 2*x.toNat + y.toNat)
  | .cancel x => Fin.ofNat 16 (7 + x.toNat)
instance : Bits PeerCommand := ⟨4,peerCommandCode,by decide⟩

set_option synthInstance.maxSize 4096 in
instance systemPacking (cfg : Config) : Bits (SystemCode cfg) := by
  unfold SystemCode LocalCode PeerCode WorkerCode SnapshotCode LocalHeaderCode PeerHeaderCode
    FrameCode RequestCode ReceiptCode OutcomeCode LocalCauseCode FrameCommandCode PeerCauseCode
    RequestPacketCode ReplyPacketCode BackendCode Name
  infer_instance

def systemBits (cfg : Config) : Nat := Bits.width (α := SystemCode cfg)

def packSystem (cfg : Config) (code : SystemCode cfg) : Fin (2 ^ systemBits cfg) := Bits.pack code

theorem packSystem_injective (cfg : Config) : Function.Injective (packSystem cfg) := Bits.injective


@[simp] theorem snapshot_success (header : Codec H H') (record : Codec R R')
    (capacity : Nat) (s : Durability.SnapshotBanks.Snapshot H R) :
    (snapshot header record capacity).encode s ≠ none ↔ header.encode s.header ≠ none ∧
      s.items.length ≤ capacity ∧ ∀ r ∈ s.items,record.encode r ≠ none := by
  simp [snapshot,sequence,cells_success]

@[simp] theorem worker_success (header : Codec H H') (record : Codec R R')
    (capacity : Nat) (w : Durability.SnapshotBanks.Worker H R) :
    (worker header record capacity).encode w ≠ none ↔
      ((snapshot header record capacity).encode (w.state.disk.cells false) ≠ none ∧
       (snapshot header record capacity).encode (w.state.disk.cells true) ≠ none) ∧
      (snapshot header record capacity).encode w.state.buffer ≠ none ∧
      (snapshot header record capacity).encode w.target ≠ none ∧
      w.cursor.val ≤ 2 * capacity + 3 := by
  simp [worker,identity,number_success]

private theorem valid_receipt_identity (state : Bool) (r : PendingCrash.Request)
    (h : requestValid state r) : ∀ t ∈ r.receipt,t.identity = r.identity := by
  cases hp : r.phase <;> simp [requestValid,hp] at h <;> aesop

theorem frame_success_of_valid (limit : Nat) (f : Frame) (h : f.Valid)
    (hn : f.nextIdentity ≤ limit) : (frame limit).encode f ≠ none := by
  have request_ok : ∀ slot : Bool,∀ r ∈ f.requests.get slot,(request limit).encode r ≠ none := by
    intro slot r hr
    have hh := h.2.2.2.1 slot r hr
    rw [request_success]
    refine ⟨by omega,?_⟩
    intro t ht
    rw [valid_receipt_identity f.logical r hh.2.1 t ht]
    omega
  simpa [frame,identity,sequence,cells_success,number_success,Slots.get] using
    And.intro (And.intro (request_ok false) (request_ok true)) (And.intro h.2.1 hn)


theorem worker_encodes (header : Codec H H') (record : Codec R R') (capacity : Nat)
    (hb : H → Prop) (rb : R → Prop) (w : Durability.SnapshotBanks.Worker H R)
    (h : w.Bounded hb rb capacity)
    (he : ∀ x,hb x → header.encode x ≠ none)
    (re : ∀ x,rb x → record.encode x ≠ none) :
    (worker header record capacity).encode w ≠ none := by
  have snapshot_ok : ∀ s : Durability.SnapshotBanks.Snapshot H R,
      s.Bounded hb rb capacity → (snapshot header record capacity).encode s ≠ none := by
    intro s hs
    exact (snapshot_success _ _ _ _).mpr ⟨he _ hs.1,hs.2.1,fun r hr => re r (hs.2.2 r hr)⟩
  rw [worker_success]
  refine ⟨⟨snapshot_ok _ (h.1.1 false),snapshot_ok _ (h.1.1 true)⟩,
    snapshot_ok _ h.1.2,snapshot_ok _ h.2,?_⟩
  have := w.cursor.isLt
  have := h.2.2.1
  omega


@[simp] theorem product_width [a : Bits α] [b : Bits β] :
    Bits.width (α := α × β) = a.width + b.width := rfl
@[simp] theorem optional_width [a : Bits α] :
    Bits.width (α := Option α) = a.width + 1 := rfl
@[simp] theorem cells_width [a : Bits α] (n : Nat) :
    Bits.width (α := Cells α n) = n * (a.width + 1) := by
  induction n with
  | zero => change 0 = 0 * (a.width + 1); omega
  | succ n ih =>
    change (a.width + 1) + Bits.width (α := Cells α n) = (n + 1) * (a.width + 1)
    rw [ih]
    ring

end Encoding
end FRPSpec.PendingRetention
