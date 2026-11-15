import Applications.FRP.PendingMigrationSource

/-! A durable lifetime-keyed peer. Publishing the receipt and producing the
modeled effect are one transition; local adapter crashes do not run this peer. -/
namespace FRPSpec.PendingCrash
open PendingMigration

/-- Each constructor records an executed operation, including failed work. -/
inductive Work where
  | peerProbe (identity : Nat)
  | peerWrite (identity : Nat)
  | recordCheck (journalIdentity : Nat)
  | cellProbe (address : Nat)
  | cellWrite (address : Nat)
  | cellPersist (address : Nat)
  | rootPublish
  | validateFrame
  | messageCheck
  | reconstruct
  | attempt (cells : Nat)
  | allocate (cells : Nat)
  | copy (cells : Nat)
  | release (cells : Nat)
  | convert (cells : Nat)
  deriving DecidableEq, Repr

inductive Answer where
  | absent
  | reserved (input : Bool)
  | published (input output : Bool)
  | prevented (input : Bool)
  | tooLate (input output : Bool)
  | conflict
  deriving DecidableEq, Repr

structure Receipt where
  identity : Nat
  answer : Answer
  deriving DecidableEq, Repr

inductive PeerCommand where
  | reserve (input : Bool)
  | query
  | publish (input output : Bool)
  | cancel (input : Bool)
  deriving DecidableEq, Repr

abbrev Peer := List (Nat × Ledger)

/-- The trace counts the actual linear search, including unsuccessful probes. -/
def lookup (identity : Nat) : Peer → Option Ledger × List Work
  | [] => (none, [])
  | (key, entry) :: rest =>
    if key = identity then (some entry, [.peerProbe key])
    else let r := lookup identity rest
         (r.1, .peerProbe key :: r.2)

def install (identity : Nat) (entry : Ledger) : Peer → Peer × List Work × Nat
  | [] => ([(identity, entry)], [.allocate 1, .peerWrite identity], 0)
  | (key, old) :: rest =>
    if key = identity then
      ((key, entry) :: rest, [.peerProbe key, .allocate 1, .peerWrite key], 1)
    else let r := install identity entry rest
         ((key, old) :: r.1, .peerProbe key :: (r.2.1 ++ [.allocate 1, .copy 1]), r.2.2 + 1)

/-- Terminal entries cannot be overwritten, even by conflicting retries. -/
def dispatch (entry : Option Ledger) (command : PeerCommand) :
    Option Ledger × Answer × Option Bool :=
  match entry, command with
  | none, .reserve x => (some (.reserved x), .reserved x, none)
  | none, _ => (none, .absent, none)
  | some (.reserved x), .reserve y =>
    (entry, if x = y then .reserved x else .conflict, none)
  | some (.reserved x), .query => (entry, .reserved x, none)
  | some (.reserved x), .publish y z =>
    if x = y then (some (.published x z), .published x z, some z)
    else (entry, .conflict, none)
  | some (.reserved x), .cancel y =>
    if x = y then (some (.cancelled x), .prevented x, none)
    else (entry, .conflict, none)
  | some (.published x z), .reserve y =>
    (entry, if x = y then .published x z else .conflict, none)
  | some (.published x z), .query => (entry, .published x z, none)
  | some (.published x z), .publish y w =>
    (entry, if x = y ∧ z = w then .published x z else .conflict, none)
  | some (.published x z), .cancel y =>
    (entry, if x = y then .tooLate x z else .conflict, none)
  | some (.cancelled x), .reserve y
  | some (.cancelled x), .publish y _
  | some (.cancelled x), .cancel y =>
    (entry, if x = y then .prevented x else .conflict, none)
  | some (.cancelled x), .query => (entry, .prevented x, none)

structure PeerResult where
  peer : Peer
  receipt : Receipt
  effect : Option Bool
  prevented : Option Bool
  work : List Work
  deriving DecidableEq, Repr

def peerStep (peer : Peer) (identity : Nat) (command : PeerCommand) : PeerResult :=
  let found := lookup identity peer
  let result := dispatch found.1 command
  let prevented := match found.1, command with
    | some (.reserved x), .cancel y => if x = y then some x else none
    | _, _ => none
  if result.1 = found.1 then
    ⟨peer, ⟨identity, result.2.1⟩, result.2.2, prevented, found.2⟩
  else match result.1 with
    | none => ⟨peer, ⟨identity, result.2.1⟩, result.2.2, prevented, found.2⟩
    | some entry =>
      let changed := install identity entry peer
      ⟨changed.1, ⟨identity, result.2.1⟩, result.2.2, prevented, found.2 ++ changed.2.1 ++ [.release changed.2.2]⟩

@[simp] theorem lookup_install_same (identity : Nat) (entry : Ledger) (peer : Peer) :
    (lookup identity (install identity entry peer).1).1 = some entry := by
  induction peer with
  | nil => simp [install, lookup]
  | cons p rest ih =>
    rcases p with ⟨key, old⟩
    by_cases h : key = identity
    · simp [install, lookup, h]
    · simp [install, lookup, h, ih]

@[simp] theorem lookup_install_other (identity other : Nat) (entry : Ledger) (peer : Peer)
    (hne : other ≠ identity) :
    (lookup other (install identity entry peer).1).1 = (lookup other peer).1 := by
  induction peer with
  | nil => simp [install, lookup, Ne.symm hne]
  | cons p rest ih =>
    rcases p with ⟨key, old⟩
    by_cases hi : key = identity
    · subst key; simp [install, lookup, Ne.symm hne]
    · by_cases ho : key = other <;> simp [install, lookup, hi, ho, ih, hne]

theorem dispatch_published_stable (x y : Bool) (c : PeerCommand) :
    (dispatch (some (.published x y)) c).1 = some (.published x y) ∧
      (dispatch (some (.published x y)) c).2.2 = none := by
  cases c <;> simp [dispatch]

theorem dispatch_cancelled_stable (x : Bool) (c : PeerCommand) :
    (dispatch (some (.cancelled x)) c).1 = some (.cancelled x) ∧
      (dispatch (some (.cancelled x)) c).2.2 = none := by
  cases c <;> simp [dispatch]

theorem dispatch_effect (entry : Option Ledger) (c : PeerCommand) (y : Bool)
    (he : (dispatch entry c).2.2 = some y) :
    ∃ x, entry = some (.reserved x) ∧ c = .publish x y ∧
      (dispatch entry c).1 = some (.published x y) := by
  cases entry with
  | none => cases c <;> simp [dispatch] at he
  | some entry =>
    cases entry with
    | published x z => have := (dispatch_published_stable x z c).2; simp [this] at he
    | cancelled x => have := (dispatch_cancelled_stable x c).2; simp [this] at he
    | reserved x =>
      cases c <;> simp only [dispatch] at he
      case reserve z => simp at he
      case query => simp at he
      case cancel z => split at he <;> simp_all
      case publish z w =>
        split at he
        · rename_i h; subst z
          simp only [Option.some.injEq] at he
          subst w
          exact ⟨x, rfl, rfl, by simp [dispatch]⟩
        · simp_all

theorem peerStep_effect (peer : Peer) (identity : Nat) (c : PeerCommand) :
    (peerStep peer identity c).effect = (dispatch (lookup identity peer).1 c).2.2 := by
  unfold peerStep
  dsimp only
  split
  · rfl
  · split <;> rfl

/-- The table records the effect before its reply can be lost. -/
theorem peer_effect_recorded (peer : Peer) (identity : Nat) (c : PeerCommand) (y : Bool)
    (he : (peerStep peer identity c).effect = some y) :
    ∃ x, (lookup identity (peerStep peer identity c).peer).1 = some (.published x y) := by
  rw [peerStep_effect] at he
  obtain ⟨x, hx, hc, _⟩ := dispatch_effect _ _ _ he
  refine ⟨x, ?_⟩
  simp [peerStep, hx, hc, dispatch]

theorem peerStep_other (peer : Peer) (identity other : Nat) (c : PeerCommand)
    (hne : other ≠ identity) :
    (lookup other (peerStep peer identity c).peer).1 = (lookup other peer).1 := by
  unfold peerStep
  dsimp only
  split
  · rfl
  · split
    · rfl
    · exact lookup_install_other _ _ _ _ hne

theorem peerStep_published (peer : Peer) (identity : Nat) (x y : Bool) (c : PeerCommand)
    (h : (lookup identity peer).1 = some (.published x y)) :
    (peerStep peer identity c).peer = peer ∧ (peerStep peer identity c).effect = none := by
  have hd := dispatch_published_stable x y c
  simp [peerStep, h, hd.1, hd.2]

theorem peerStep_cancelled (peer : Peer) (identity : Nat) (x : Bool) (c : PeerCommand)
    (h : (lookup identity peer).1 = some (.cancelled x)) :
    (peerStep peer identity c).peer = peer ∧ (peerStep peer identity c).effect = none := by
  have hd := dispatch_cancelled_stable x c
  simp [peerStep, h, hd.1, hd.2]

structure PeerExecution where
  peer : Peer
  receipts : List Receipt := []
  effects : List (Nat × Bool) := []
  work : List Work := []
  deriving DecidableEq, Repr

def peerExecute : Peer → List (Nat × PeerCommand) → PeerExecution
  | peer, [] => {peer := peer}
  | peer, (identity, command) :: commands =>
    let step := peerStep peer identity command
    let tail := peerExecute step.peer commands
    ⟨tail.peer, step.receipt :: tail.receipts,
      step.effect.toList.map (fun y => (identity,y)) ++ tail.effects,
      step.work ++ tail.work⟩

/-- Arbitrary subsequent operations, including retries under other identities,
retain a published result and cannot emit that identity again. -/
theorem peerExecute_published (peer : Peer) (identity : Nat) (x y : Bool)
    (commands : List (Nat × PeerCommand))
    (h : (lookup identity peer).1 = some (.published x y)) :
    (lookup identity (peerExecute peer commands).peer).1 = some (.published x y) ∧
      identity ∉ (peerExecute peer commands).effects.map Prod.fst := by
  induction commands generalizing peer with
  | nil => exact ⟨h, by simp [peerExecute]⟩
  | cons command commands ih =>
    rcases command with ⟨key, command⟩
    have hs : (lookup identity (peerStep peer key command).peer).1 = some (.published x y) := by
      by_cases he : identity = key
      · subst key; rw [(peerStep_published peer identity x y command h).1]; exact h
      · rw [peerStep_other _ _ _ _ he]; exact h
    obtain ⟨hp, hn⟩ := ih _ hs
    refine ⟨hp, ?_⟩
    simp only [peerExecute, List.map_append, List.mem_append, not_or]
    refine ⟨?_, hn⟩
    by_cases he : identity = key
    · subst key
      simp [(peerStep_published peer identity x y command h).2]
    · cases (peerStep peer key command).effect <;> simp [he]

/-- The modeled atomic peer produces at most one external effect per lifetime
identity, over every finite command trace, even when replies are lost. -/
theorem peer_effects_unique (peer : Peer) (commands : List (Nat × PeerCommand)) :
    ((peerExecute peer commands).effects.map Prod.fst).Nodup := by
  induction commands generalizing peer with
  | nil => simp [peerExecute]
  | cons command commands ih =>
    rcases command with ⟨identity, command⟩
    have ht := ih (peerStep peer identity command).peer
    cases he : (peerStep peer identity command).effect with
    | none => simpa [peerExecute, he] using ht
    | some y =>
      obtain ⟨x, hp⟩ := peer_effect_recorded peer identity command y he
      have hn := (peerExecute_published _ identity x y commands hp).2
      simpa [peerExecute, he] using List.nodup_cons.mpr ⟨hn, ht⟩

end FRPSpec.PendingCrash
