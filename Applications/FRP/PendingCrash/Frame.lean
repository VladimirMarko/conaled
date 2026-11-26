import Applications.FRP.PendingCrash.Peer

/-! Stable frames and their executable predecessor validator. A typed frame
alone is insufficient: recovery checks every admitted transition in order. -/
namespace FRPSpec.PendingCrash
open PendingMigration

structure Request where
  identity : Nat
  input : Bool
  output : Option Bool := none
  receipt : Option Receipt := none
  phase : Phase := .accepted
  routeOpen : Bool := true
  deriving DecidableEq, Repr

structure Frame where
  kind : Migration.Kind
  logical : Bool := false
  requests : Slots Request := {}
  order : List Bool := []
  nextIdentity : Nat := 0
  deriving DecidableEq, Repr

def initialFrame (kind : Migration.Kind := .delay) : Frame := {kind := kind}

def Frame.head (f : Frame) : Option (Bool × Request) := do
  let slot ← f.order.head?
  let r ← f.requests.get slot
  pure (slot, r)

def Frame.find (f : Frame) (identity : Nat) : Option (Bool × Request) :=
  [false, true].findSome? fun slot => do
    let r ← f.requests.get slot
    if r.identity = identity then some (slot,r) else none

def Frame.update (f : Frame) (slot : Bool) (r : Request) : Frame :=
  {f with requests := f.requests.put slot (some r)}

def terminal (phase : Phase) : Bool := phase == .committed || phase == .cancelled

def RequestValid (state : Bool) (r : Request) : Prop :=
  (r.routeOpen = false → terminal r.phase = true) ∧
  match r.phase with
  | .accepted => r.output = none ∧ r.receipt = none
  | .computed => r.output = some state ∧ r.receipt = none
  | .confirmed => r.output = some state ∧
      r.receipt = some ⟨r.identity, .published r.input state⟩
  | .committed => r.input = state ∧ ∃ y ∈ r.output,
      r.receipt = some ⟨r.identity, .published r.input y⟩
  | .cancelled => r.receipt = some ⟨r.identity, .prevented r.input⟩

instance (state : Bool) (r : Request) : Decidable (RequestValid state r) := by
  unfold RequestValid
  cases r.phase <;> infer_instance

/-- Finite slot checks retain the lifetime counter and the exact occupied order. -/
def Frame.Valid (f : Frame) : Prop :=
  f.order.Nodup ∧ f.order.length ≤ 2 ∧
  (∀ slot : Bool, slot ∈ f.order ↔ (f.requests.get slot).isSome = true) ∧
  (∀ slot : Bool, ∀ r ∈ f.requests.get slot,
    r.identity < f.nextIdentity ∧ RequestValid f.logical r ∧
    (slot ∈ f.order.tail → r.phase = .accepted ∨ r.phase = .cancelled)) ∧
  (∀ l ∈ f.requests.left, ∀ r ∈ f.requests.right, l.identity ≠ r.identity)

instance (f : Frame) : Decidable f.Valid := by unfold Frame.Valid; infer_instance

inductive FrameCommand where
  | accept (input : Bool)
  | evaluate
  | receive (receipt : Receipt)
  | tickCommit
  | close
  | release
  | migrate (target : Migration.Kind)
  deriving DecidableEq, Repr

inductive Decision where
  | refused
  | stopped
  | changed (frame : Frame)
  deriving DecidableEq, Repr

/-- Receipt reconciliation inspects only returned evidence, never the peer table. -/
def receive (f : Frame) (receipt : Receipt) : Decision :=
  match f.find receipt.identity with
  | none => .refused
  | some (slot,r) =>
    match receipt.answer with
    | .absent | .reserved _ | .conflict => .refused
    | .published x y | .tooLate x y =>
      if x ≠ r.input then .refused else
      if r.phase == .cancelled then .stopped else
      if r.phase == .accepted then .stopped else
      if r.output ≠ some y then .refused else
      if r.phase == .computed && f.order.head? == some slot && r.routeOpen then
        .changed (f.update slot {r with phase := .confirmed, receipt := some ⟨r.identity, .published x y⟩})
      else .refused
    | .prevented x =>
      if x ≠ r.input then .refused else
      if r.phase == .confirmed || r.phase == .committed then .stopped else
      if (r.phase == .accepted || r.phase == .computed) && r.routeOpen then
        .changed (f.update slot {r with phase := .cancelled, receipt := some ⟨r.identity, .prevented x⟩})
      else .refused

/-- Only named fields change. Runtime additionally enforces append/preparation
exclusion, receipt provenance and absence of owned callbacks at release. -/
def propose (f : Frame) (command : FrameCommand) : Decision :=
  match command with
  | .receive receipt => receive f receipt
  | .migrate target => .changed {f with kind := target}
  | .accept x =>
    if f.order.length ≥ 2 then .refused else
    let free := if (f.requests.get false).isNone then some false
      else if (f.requests.get true).isNone then some true else none
    match free with
    | none => .refused
    | some slot => .changed {f with
        requests := f.requests.put slot (some {identity := f.nextIdentity, input := x})
        order := f.order ++ [slot]
        nextIdentity := f.nextIdentity + 1}
  | _ => match f.head with
    | none => .refused
    | some (slot,r) => match command with
      | .evaluate =>
        if r.phase == .accepted && r.routeOpen then
          let evaluated := Migration.evaluate (Migration.realize f.kind f.logical) r.input
          .changed (f.update slot {r with phase := .computed, output := some evaluated.output})
        else .refused
      | .tickCommit =>
        if r.phase == .confirmed && r.routeOpen then
          .changed {(f.update slot {r with phase := .committed}) with logical := r.input}
        else .refused
      | .close =>
        if terminal r.phase && r.routeOpen then
          .changed (f.update slot {r with routeOpen := false})
        else .refused
      | .release =>
        if terminal r.phase && !r.routeOpen then
          .changed {f with requests := f.requests.put slot none, order := f.order.tail}
        else .refused
      | _ => .refused

/-- The validator enumerates all finite permitted edits, retaining arbitrary
lifetime identities by reading them from the preceding occupied slots. -/
def possibleCommands (f : Frame) : List FrameCommand :=
  [.accept false, .accept true, .evaluate, .tickCommit, .close, .release,
    .migrate .delay, .migrate .redundant] ++
  [false,true].flatMap fun slot => match f.requests.get slot with
    | none => []
    | some r => [.receive ⟨r.identity,.prevented r.input⟩] ++
        r.output.toList.map (fun y => .receive ⟨r.identity,.published r.input y⟩)

def successor (old next : Frame) : Bool :=
  decide old.Valid && decide next.Valid &&
    (possibleCommands old).any (fun c => propose old c == .changed next)

/-- Every runtime proposal passes the same validation used at restart. -/
def advance (f : Frame) (command : FrameCommand) : Decision :=
  match propose f command with
  | .changed next => if successor f next then .changed next else .stopped
  | d => d

/-- Recovering a well-typed but invalid frame sequence stops the adapter. -/
def validateFrames : Frame → List Frame → Option Frame
  | f, [] => if f.Valid then some f else none
  | f, next :: rest => if successor f next then validateFrames next rest else none

theorem successor_valid {f g : Frame} (h : successor f g = true) : f.Valid ∧ g.Valid := by
  simp only [successor, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1,h.1.2⟩

theorem advance_valid {f g : Frame} {c : FrameCommand}
    (h : advance f c = .changed g) : f.Valid ∧ g.Valid := by
  cases hp : propose f c with
  | refused => simp [advance, hp] at h
  | stopped => simp [advance, hp] at h
  | changed next =>
    simp only [advance, hp] at h
    split at h
    · rename_i hs
      cases h
      exact successor_valid hs
    · contradiction

theorem validateFrames_valid {f g : Frame} {frames : List Frame}
    (h : validateFrames f frames = some g) : g.Valid := by
  induction frames generalizing f with
  | nil =>
    simp only [validateFrames] at h
    split at h
    · cases h; assumption
    · contradiction
  | cons next rest ih =>
    simp only [validateFrames] at h
    split at h
    · exact ih h
    · contradiction

/-- Reconstruction uses the existing actual Circuit realizations. -/
def reconstruct (f : Frame) : Migration.Backend := Migration.realize f.kind f.logical

@[simp] theorem reconstruct_logical (f : Frame) : (reconstruct f).logical = f.logical :=
  Migration.realize_logical _ _

@[simp] theorem reconstruct_kind (f : Frame) : (reconstruct f).kind = f.kind :=
  Migration.realize_kind _ _

theorem reconstructed_evaluation (f : Frame) (input : Bool) :
    (Migration.evaluate (reconstruct f) input).output = f.logical ∧
      (Migration.evaluate (reconstruct f) input).candidate.logical = input :=
  ⟨(Migration.evaluate _ _).output_eq.trans (reconstruct_logical f),
    (Migration.evaluate _ _).state_eq⟩

example : (initialFrame .delay).Valid := by decide
example : validateFrames (initialFrame .delay)
    [{initialFrame .delay with nextIdentity := 7}] = none := by decide

end FRPSpec.PendingCrash
