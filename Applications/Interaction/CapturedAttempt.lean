import Applications.Interaction.Measurement
import Applications.Interaction.Snapshot

/-! # Captured inputs and one observed attempt

The source relations accept arbitrary values and read histories. The executable
observer consumes primitive responses; the OS adapter owes each response's local
premise. Neither finite observations nor a timeout imply physical termination.
-/
namespace Interaction.CapturedAttempt
open Measurement
universe u v w

/-- Independent source contract, with a separate admissibility witness for each read. -/
def CapturedExecution {A : Type u} {B : Type v} {H : Type w}
    (readA : H → A → Prop) (readB : H → B → Prop)
    (ha hb : H) (captured consumed : A × B) : Prop :=
  readA ha captured.1 ∧ readB hb captured.2 ∧ consumed = captured

/-- Local read, seal, and child-read premises, before composing their consequences.
The histories can describe nonatomic reads; the fixture uses stable read windows. -/
structure CaptureChain {A : Type u} {B : Type v} {H : Type w}
    (readA : H → A → Prop) (readB : H → B → Prop)
    (ha hb : H) (captured sealed consumed : A × B) : Prop where
  returnedA : readA ha captured.1
  returnedB : readB hb captured.2
  wroteA : sealed.1 = captured.1
  wroteB : sealed.2 = captured.2
  childReadA : consumed.1 = sealed.1
  childReadB : consumed.2 = sealed.2

theorem capture_chain {A : Type u} {B : Type v} {H : Type w}
    {ra : H → A → Prop} {rb : H → B → Prop} {ha hb : H}
    {c s x : A × B} (h : CaptureChain ra rb ha hb c s x) :
    CapturedExecution ra rb ha hb c x := by
  exact ⟨h.returnedA, h.returnedB,
    Prod.ext (h.childReadA.trans h.wroteA) (h.childReadB.trans h.wroteB)⟩

/-- The child-read premise supplies the snapshot consumer's execution relation. -/
theorem captured_step {A : Type u} {B : Type v} {H : Type w}
    {ra : H → A → Prop} {rb : H → B → Prop} {ha hb : H}
    {c s x live : A × B} (h : CaptureChain ra rb ha hb c s x) :
    Snapshot.CompileCaptured ⟨live, c, none⟩ ⟨live, c, some x⟩ := by
  exact ⟨rfl, congrArg some (capture_chain h).2.2⟩

/-- Capture progresses only after each read and seal returned. Failures leave a
prefix; complete input is exposed only after both seals. -/
inductive CaptureState (A : Type u) (B : Type v) where
  | empty
  | readA (a : A)
  | sealedA (a : A)
  | readB (a : A) (b : B)
  | sealed (a : A) (b : B)
  deriving Repr

inductive CaptureEvent (A : Type u) (B : Type v) where
  | readA (a : A)
  | sealA
  | readB (b : B)
  | sealB
  deriving Repr

def captureAdvance {A : Type u} {B : Type v} :
    CaptureState A B → CaptureEvent A B → Option (CaptureState A B)
  | .empty, .readA a => some (.readA a)
  | .readA a, .sealA => some (.sealedA a)
  | .sealedA a, .readB b => some (.readB a b)
  | .readB a b, .sealB => some (.sealed a b)
  | _, _ => none

def sealedValue {A : Type u} {B : Type v} : CaptureState A B → Option (A × B)
  | .sealed a b => some (a, b)
  | _ => none

/-- Independent legal capture transitions; source interference is separate. -/
inductive CaptureStep {A : Type u} {B : Type v} : CaptureState A B → CaptureState A B → Prop where
  | readA (a) : CaptureStep .empty (.readA a)
  | sealA (a) : CaptureStep (.readA a) (.sealedA a)
  | readB (a b) : CaptureStep (.sealedA a) (.readB a b)
  | sealB (a b) : CaptureStep (.readB a b) (.sealed a b)

theorem capture_advance_refines {A : Type u} {B : Type v} {s t : CaptureState A B}
    {e : CaptureEvent A B} (h : captureAdvance s e = some t) : CaptureStep s t := by
  cases s <;> cases e <;> simp [captureAdvance] at h
  all_goals subst t; constructor

theorem sealed_rejects {A : Type u} {B : Type v} (a : A) (b : B) (e : CaptureEvent A B) :
    captureAdvance (.sealed a b) e = none := by cases e <;> rfl

/-- Primitive observations are deliberately smaller than the detailed runtime log. -/
inductive Probe where
  | raw (value : Nat)
  | timeout
  | spawnFailed
  | unknownCompletion
  | channels (complete : Bool)
  | cleanup (status : Status)
  | publication (status : Status)
  deriving DecidableEq, Repr

def unknown : Observation := ⟨.unknown, false, .unknown, .unknown⟩

/-- Raw nonzero remains unknown: this interface does not decode signal encodings. -/
def observe (o : Observation) : Probe → Observation
  | .raw n => {o with completion := if n = 0 then .exited 0 else .unknown}
  | .timeout => {o with completion := .timedOut}
  | .spawnFailed => {o with completion := .spawnFailed}
  | .unknownCompletion => {o with completion := .unknown}
  | .channels b => {o with outputComplete := b}
  | .cleanup k => {o with cleanup := k}
  | .publication p => {o with publication := p}

/-- Each positive primitive response has its own external premise. Failures and
unknowns do not assert absence of an effect. Capture correspondence is separate. -/
def Supports (w : World) : Probe → Prop
  | .raw n => n = 0 → w.exitCode = some 0
  | .timeout | .spawnFailed | .unknownCompletion => True
  | .channels b => b = true → w.outputFinished = true
  | .cleanup k => k = .confirmed → w.cleaned = true
  | .publication p => p = .confirmed → w.published = true

/-- Permitted external steps preserve facts already established about this attempt.
They need not preserve other actors' live source files or imply any progress. -/
def Extends (w v : World) : Prop :=
  (∀ n, w.exitCode = some n → v.exitCode = some n) ∧
  (w.outputFinished = true → v.outputFinished = true) ∧
  (w.cleaned = true → v.cleaned = true) ∧
  (w.published = true → v.published = true)

theorem unknown_corresponds (w : World) : Corresponds w unknown := by
  simp [Corresponds, unknown]

theorem corresponds_extends {w v : World} {o : Observation}
    (h : Corresponds w o) (e : Extends w v) : Corresponds v o := by
  exact ⟨fun n hn => e.1 n (h.1 n hn), fun hb => e.2.1 (h.2.1 hb),
    fun hk => e.2.2.1 (h.2.2.1 hk), fun hp => e.2.2.2 (h.2.2.2 hp)⟩

theorem observe_supported {w : World} {o : Observation} (h : Corresponds w o)
    (p : Probe) (hp : Supports w p) : Corresponds w (observe o p) := by
  rcases h with ⟨hc, ho, hk, hu⟩
  cases p with
  | raw n =>
    by_cases hn : n = 0
    · simp only [observe, hn, ↓reduceIte, Corresponds, Completion.exited.injEq]
      exact ⟨fun k h => h ▸ hp hn, ho, hk, hu⟩
    · exact ⟨by simp [observe, hn], ho, hk, hu⟩
  | timeout => exact ⟨by simp [observe], ho, hk, hu⟩
  | spawnFailed => exact ⟨by simp [observe], ho, hk, hu⟩
  | unknownCompletion => exact ⟨by simp [observe], ho, hk, hu⟩
  | channels b => exact ⟨hc, hp, hk, hu⟩
  | cleanup k => exact ⟨hc, ho, hp, hu⟩
  | publication p => exact ⟨hc, ho, hk, hp⟩

/-- A supported prefix has concrete external witnesses, not just a universal
condition over a possibly empty observation fiber. -/
inductive Evidence : World → Observation → Prop where
  | initial (w) : Evidence w unknown
  | response {w v o} : Evidence w o → Extends w v → (p : Probe) →
      Supports v p → Evidence v (observe o p)

theorem evidence_corresponds {w : World} {o : Observation} (h : Evidence w o) :
    Corresponds w o := by
  induction h with
  | initial w => exact unknown_corresponds w
  | response _ e p hp ih => exact observe_supported (corresponds_extends ih e) p hp

/-- Public executable authorization and observation transitions. -/
inductive Event where
  | authorize
  | response (p : Probe)
  | pending
  deriving DecidableEq, Repr

structure Observer where
  controller : Controller := initial
  observed : Observation := unknown
  deriving Repr

def advance (s : Observer) : Event → Option Observer
  | .authorize => (begin s.controller).map fun c => {s with controller := c}
  | .response p => if s.controller.started then
      let o := observe s.observed p
      some ⟨record s.controller o, o⟩ else none
  | .pending => some s

/-- The adapter may issue only when the staged capture has both seal receipts. -/
def authorizeCaptured {A : Type u} {B : Type v} (capture : CaptureState A B)
    (s : Observer) : Option Observer :=
  (sealedValue capture).bind fun _ => advance s .authorize

theorem authorize_requires_sealed {A : Type u} {B : Type v}
    {capture : CaptureState A B} {s t : Observer}
    (h : authorizeCaptured capture s = some t) : ∃ inputs, sealedValue capture = some inputs := by
  cases he : sealedValue capture with
  | none => simp [authorizeCaptured, he] at h
  | some x => exact ⟨x, rfl⟩

theorem selected_exact {s t : Observer} {p : Probe}
    (h : advance s (.response p) = some t) :
    t.observed = observe s.observed p ∧
      t.controller.observation = some (observe s.observed p) := by
  cases hs : s.controller.started <;> simp [advance, hs] at h
  subst t
  exact ⟨rfl, rfl⟩

/-- Independent allowed control steps. No event grants permission after issuance. -/
inductive ControlStep : Observer → Observer → Prop where
  | issue (s) (h : s.controller.started = false) :
      ControlStep s {s with controller := {s.controller with started := true}}
  | response (s) (h : s.controller.started = true) (p : Probe) :
      ControlStep s ⟨record s.controller (observe s.observed p), observe s.observed p⟩
  | pending (s) : ControlStep s s

theorem advance_refines {s t : Observer} {e : Event} (h : advance s e = some t) :
    ControlStep s t := by
  cases e with
  | authorize =>
    cases hs : s.controller.started <;> simp [advance, begin, hs] at h
    subst t
    exact .issue s hs
  | response p =>
    cases hs : s.controller.started <;> simp [advance, hs] at h
    subst t
    exact .response s hs p
  | pending => simp [advance] at h; subst t; exact .pending s

theorem control_started {s t : Observer} (h : ControlStep s t)
    (hs : s.controller.started = true) : t.controller.started = true := by
  cases h with
  | issue hf => simp [hf] at hs
  | response => exact hs
  | pending => exact hs

theorem prefix_started {s t : Observer}
    (h : Relation.ReflTransGen ControlStep s t) (hs : s.controller.started = true) :
    t.controller.started = true := by
  induction h with
  | refl => exact hs
  | tail _ step ih => exact control_started step ih

theorem no_reexecution {s t : Observer} (h : Relation.ReflTransGen ControlStep s t)
    (hs : s.controller.started = true) : advance t .authorize = none := by
  simp [advance, begin, prefix_started h hs]

/-- A finite adapter event list can fail to be admissible; no fallback state. -/
def runEvents : Observer → List Event → Option Observer
  | s, [] => some s
  | s, e :: es => (advance s e).bind fun t => runEvents t es

def launches : List Event → Nat
  | [] => 0
  | .authorize :: es => 1 + launches es
  | _ :: es => launches es

theorem run_events_refines {s t : Observer} {events : List Event}
    (h : runEvents s events = some t) : Relation.ReflTransGen ControlStep s t := by
  induction events generalizing s with
  | nil => simp [runEvents] at h; subst t; exact .refl
  | cons e es ih =>
    cases he : advance s e with
    | none => simp [runEvents, he] at h
    | some u =>
      have hu : runEvents u es = some t := by simpa [runEvents, he] using h
      exact (Relation.ReflTransGen.single (advance_refines he)).trans (ih hu)

/-- Event accounting is a logical issuance bound, not an elapsed-time bound. -/
theorem launches_bound {s t : Observer} {events : List Event}
    (h : runEvents s events = some t) :
    launches events ≤ 1 := by
  -- The stronger conservation equation makes the bound independent of list length.
  have conservation : ∀ (es : List Event) (a b : Observer), runEvents a es = some b →
      launches es + (if a.controller.started then 1 else 0) =
        (if b.controller.started then 1 else 0) := by
    intro es
    induction es with
    | nil => intro a b h; simp [runEvents] at h; subst b; simp [launches]
    | cons e es ih =>
      intro a b h
      cases he : advance a e with
      | none => simp [runEvents, he] at h
      | some c =>
        have tail := ih c b (by simpa [runEvents, he] using h)
        cases e with
        | authorize =>
          cases ha : a.controller.started <;> simp [advance, begin, ha] at he
          subst c
          simpa [launches, ha, Nat.add_comm] using tail
        | response p =>
          cases ha : a.controller.started <;> simp [advance, ha] at he
          subst c
          simpa [launches, record, ha] using tail
        | pending =>
          simp [advance] at he
          subst c
          exact tail
  have eq := conservation events s t h
  cases hs : s.controller.started <;> cases ht : t.controller.started <;>
    simp [hs, ht] at eq ⊢ <;> omega

/-- The final physical statement is derived from primitive evidence, not assumed. -/
theorem success_sound {w : World} {o : Observation} (h : Evidence w o)
    (c : Controller) (selected : c.observation = some o) (ok : successful c = true) :
    Completed w := successful_world c o w selected (evidence_corresponds h) ok

/-- Joint consumer result: supported process evidence and composed capture premises.
The sealed-input equality is derived from the two write and two child-read laws. -/
theorem accepted_capture {A : Type u} {B : Type v} {H : Type w}
    {ra : H → A → Prop} {rb : H → B → Prop} {ha hb : H}
    {captured sealed consumed : A × B}
    (capture : CaptureChain ra rb ha hb captured sealed consumed)
    {world : World} {o : Observation} (evidence : Evidence world o)
    (c : Controller) (selected : c.observation = some o) (ok : successful c = true) :
    CapturedExecution ra rb ha hb captured consumed ∧ Completed world :=
  ⟨capture_chain capture, success_sound evidence c selected ok⟩

theorem run_started {states : Nat → Observer} (run : Interaction.Run ControlStep states)
    (h : (states 0).controller.started = true) : ∀ n, (states n).controller.started = true :=
  run.invariant h (fun _ _ hs step => control_started step hs)

/-- Stalling forever supplies no liveness claim, even after authorization. -/
theorem pending_run (s : Observer) : Interaction.Run ControlStep (fun _ => s) := by
  intro _
  exact .pending s


/-! ## Joint witnessed prefixes

The shared carrier does not define legal source executions: `SourceStep` does.
`next` is a separate target reducer. Events are normalized observations with
external primitive witnesses; they are not asserted to be a verified decoding of
Main's JSON. In particular actual exit/reap/publication effects are witnesses,
not knowledge inferred from an unknown observation.
-/
namespace Joint

structure Capture (A : Type u) (B : Type v) (H : Type w) where
  ha : H
  hb : H
  returned : A × B
  sealed : A × B
  deriving Repr

structure Execution (A : Type u) (B : Type v) (H : Type w) where
  capture : Capture A B H
  authorizedId : Nat
  childId : Nat
  consumed : A × B
  deriving Repr

inductive Phase (A : Type u) (B : Type v) (H : Type w) (P : Type) where
  | empty
  | readA (h : H) (a : A)
  | sealA (h : H) (a sealed : A)
  | readB (ha : H) (a sa : A) (hb : H) (b : B)
  | sealed (capture : Capture A B H)
  | authorized (capture : Capture A B H) (id : Nat)
  | running (execution : Execution A B H)
  | decided (execution : Execution A B H) (choice : Completion) (actualExit : Option Nat)
  | cleaned (execution : Execution A B H) (choice : Completion) (actualExit : Option Nat)
      (cleanup : Status) (reaped : Bool)
  | channels (execution : Execution A B H) (choice : Completion) (actualExit : Option Nat)
      (cleanup : Status) (reaped complete finished : Bool)
  | aborted (prior : Phase A B H P) (partialEffect : P)
  | requested (prior : Phase A B H P) (payload : P)
  | published (prior : Phase A B H P) (payload : P) (status : Status) (effect : Option P)
  | selected (prior : Phase A B H P) (payload : P) (status : Status) (effect : Option P)
  deriving Repr

variable {A : Type u} {B : Type v} {H : Type w} {P : Type}

def captureValid (ra : H → A → Prop) (rb : H → B → Prop) (c : Capture A B H) : Prop :=
  ra c.ha c.returned.1 ∧ rb c.hb c.returned.2 ∧
    c.sealed.1 = c.returned.1 ∧ c.sealed.2 = c.returned.2

def executionValid (ra : H → A → Prop) (rb : H → B → Prop) (e : Execution A B H) : Prop :=
  captureValid ra rb e.capture ∧ e.childId = e.authorizedId ∧
    e.consumed.1 = e.capture.sealed.1 ∧ e.consumed.2 = e.capture.sealed.2

/-- The completion decision is selected once. Reaping does not reselect it. -/
def exitSupported (c : Completion) (actual : Option Nat) : Prop :=
  ∀ n, c = .exited n → actual = some n

def beforePublication : Phase A B H P → Bool
  | .requested .. | .published .. | .selected .. | .aborted .. => false
  | _ => true

def canRequest : Phase A B H P → Bool
  | .channels .. | .aborted .. => true
  | _ => false

def observation : Phase A B H P → Observation
  | .decided _ c _ => ⟨c, false, .unknown, .unknown⟩
  | .cleaned _ c _ k _ => ⟨c, false, k, .unknown⟩
  | .channels _ c _ k _ b _ => ⟨c, b, k, .unknown⟩
  | .aborted p _ => {observation p with outputComplete := false, publication := .unknown}
  | .requested p _ => observation p
  | .published p _ k _ | .selected p _ k _ => {observation p with publication := k}
  | _ => unknown

/-- Actual invocation count, including under failure and lost acknowledgment. -/
def calls : Phase A B H P → Nat
  | .running .. | .decided .. | .cleaned .. | .channels .. => 1
  | .aborted p _ | .requested p _ | .published p _ _ _ | .selected p _ _ _ => calls p
  | _ => 0

inductive Event (A : Type u) (B : Type v) (H : Type w) (P : Type) where
  | readA (h : H) (a : A)
  | sealA (value : A)
  | readB (h : H) (b : B)
  | sealB (value : B)
  | authorize (id : Nat)
  | spawn (childId : Nat) (consumed : A × B)
  | wait (choice : Completion) (actualExit : Option Nat)
  | cleanup (status : Status) (actualExit : Option Nat) (reaped : Bool)
  | channels (complete finished : Bool)
  | abort (partialEffect : P)
  | request (payload : P)
  | publish (status : Status) (actualEffect : Option P)
  | select
  | pending
  | interfere (live : A × B)

structure State (A : Type u) (B : Type v) (H : Type w) (P : Type) where
  live : A × B
  phase : Phase A B H P := .empty

/-- Public observations and external witnesses are retained in the same prefix. -/
def nextPhase (s : Phase A B H P) (event : Event A B H P) : Option (Phase A B H P) :=
  match s, event with
  | .empty, .readA h a => some (.readA h a)
  | .readA h a, .sealA sa => some (.sealA h a sa)
  | .sealA ha a sa, .readB hb b => some (.readB ha a sa hb b)
  | .readB ha a sa hb b, .sealB sb => some (.sealed ⟨ha, hb, (a,b), (sa,sb)⟩)
  | .sealed c, .authorize id => some (.authorized c id)
  | .authorized c id, .spawn child x => some (.running ⟨c, id, child, x⟩)
  | .running e, .wait c actual => some (.decided e c actual)
  | .decided e c _old, .cleanup k actual reaped =>
      some (.cleaned e c actual k reaped)
  | .cleaned e c actual k reaped, .channels b finished =>
      some (.channels e c actual k reaped b finished)
  | _, .abort fragment => if beforePublication s then some (.aborted s fragment) else none
  | _, .request p => if canRequest s then some (.requested s p) else none
  | .requested prior p, .publish k effect => some (.published prior p k effect)
  | .published prior p k effect, .select => some (.selected prior p k effect)
  | _, .pending | _, .interfere _ => some s
  | _, _ => none

def next (s : State A B H P) (event : Event A B H P) : Option (State A B H P) :=
  (nextPhase s.phase event).map fun p =>
    ⟨match event with | .interfere live => live | _ => s.live, p⟩

/-- Local primitive obligations. No final correspondence or success is assumed.
Unknown publication permits any effect, including the exact requested value. -/
def Primitive (ra : H → A → Prop) (rb : H → B → Prop)
    (encode : Phase A B H P → P) (s : Phase A B H P) : Event A B H P → Prop
  | .readA h a => ra h a
  | .readB h b => rb h b
  | .sealA value => ∀ h a, s = .readA h a → value = a
  | .sealB value => ∀ ha a sa hb b, s = .readB ha a sa hb b → value = b
  | .spawn child x => ∀ c id, s = .authorized c id →
      child = id ∧ x.1 = c.sealed.1 ∧ x.2 = c.sealed.2
  | .wait c actual => exitSupported c actual
  | .cleanup k actual reaped =>
      (k = .confirmed → reaped = true) ∧
      ∀ e c old, s = .decided e c old → ∀ n, old = some n → actual = some n
  | .channels b finished => b = true → finished = true
  | .request p => p = encode s
  | .publish k effect => ∀ prior p, s = .requested prior p →
      k = .confirmed → effect = some p
  | _ => True

/-- Independent allowed source transitions, stated without the target reducer. -/
inductive PhaseStep (ra : H → A → Prop) (rb : H → B → Prop)
    (encode : Phase A B H P → P) : Phase A B H P → Event A B H P → Phase A B H P → Prop where
  | readA (h a) : ra h a → PhaseStep ra rb encode .empty (.readA h a) (.readA h a)
  | sealA (h a sa) : sa = a → PhaseStep ra rb encode (.readA h a) (.sealA sa) (.sealA h a sa)
  | readB (ha a sa hb b) : rb hb b →
      PhaseStep ra rb encode (.sealA ha a sa) (.readB hb b) (.readB ha a sa hb b)
  | sealB (ha a sa hb b sb) : sb = b → PhaseStep ra rb encode (.readB ha a sa hb b)
      (.sealB sb) (.sealed ⟨ha,hb,(a,b),(sa,sb)⟩)
  | authorize (c id) : PhaseStep ra rb encode (.sealed c) (.authorize id) (.authorized c id)
  | spawn (c id child x) : child = id → x.1 = c.sealed.1 → x.2 = c.sealed.2 →
      PhaseStep ra rb encode (.authorized c id) (.spawn child x) (.running ⟨c,id,child,x⟩)
  | wait (e c actual) : exitSupported c actual →
      PhaseStep ra rb encode (.running e) (.wait c actual) (.decided e c actual)
  | cleanup (e c old k actual reaped) : (k = .confirmed → reaped = true) →
      (∀ n, old = some n → actual = some n) →
      PhaseStep ra rb encode (.decided e c old) (.cleanup k actual reaped) (.cleaned e c actual k reaped)
  | channels (e c actual k reaped b finished) : (b = true → finished = true) →
      PhaseStep ra rb encode (.cleaned e c actual k reaped) (.channels b finished)
        (.channels e c actual k reaped b finished)
  | abort (s fragment) : beforePublication s = true →
      PhaseStep ra rb encode s (.abort fragment) (.aborted s fragment)
  | request (s p) : canRequest s = true → p = encode s →
      PhaseStep ra rb encode s (.request p) (.requested s p)
  | publish (s p k effect) : (k = .confirmed → effect = some p) →
      PhaseStep ra rb encode (.requested s p) (.publish k effect) (.published s p k effect)
  | select (s p k effect) :
      PhaseStep ra rb encode (.published s p k effect) .select (.selected s p k effect)
  | pending (s) : PhaseStep ra rb encode s .pending s
  | interfere (s live) : PhaseStep ra rb encode s (.interfere live) s

structure Source (A : Type u) (B : Type v) (H : Type w) (P : Type) where
  state : State A B H P

def Related (source : Source A B H P) (target : State A B H P) : Prop := source.state = target

def SourceStep (ra : H → A → Prop) (rb : H → B → Prop) (encode : Phase A B H P → P)
    (s : Source A B H P) (event : Event A B H P) (t : Source A B H P) : Prop :=
  PhaseStep ra rb encode s.state.phase event t.state.phase ∧
  t.state.live = (match event with | .interfere live => live | _ => s.state.live)

/-- Reducer acceptance alone is insufficient; the same event has local obligations. -/
inductive Admissible (ra : H → A → Prop) (rb : H → B → Prop) (encode : Phase A B H P → P) :
    State A B H P → List (Event A B H P) → State A B H P → Prop where
  | nil (s) : Admissible ra rb encode s [] s
  | cons {s t u event events} : next s event = some t → Primitive ra rb encode s.phase event →
      Admissible ra rb encode t events u → Admissible ra rb encode s (event :: events) u

inductive AllowedPrefix (ra : H → A → Prop) (rb : H → B → Prop) (encode : Phase A B H P → P) :
    Source A B H P → List (Event A B H P) → Source A B H P → Prop where
  | nil (s) : AllowedPrefix ra rb encode s [] s
  | cons {s t u event events} : SourceStep ra rb encode s event t →
      AllowedPrefix ra rb encode t events u → AllowedPrefix ra rb encode s (event :: events) u

/-- Cumulative source facts; publication is about the retained exact payload. -/
def Valid (ra : H → A → Prop) (rb : H → B → Prop) (encode : Phase A B H P → P) :
    Phase A B H P → Prop
  | .empty => True
  | .readA h a => ra h a
  | .sealA h a sa => ra h a ∧ sa = a
  | .readB ha a sa hb b => ra ha a ∧ sa = a ∧ rb hb b
  | .sealed c | .authorized c _ => captureValid ra rb c
  | .running e => executionValid ra rb e
  | .decided e c actual => executionValid ra rb e ∧ exitSupported c actual
  | .cleaned e c actual k reaped => executionValid ra rb e ∧ exitSupported c actual ∧
      (k = .confirmed → reaped = true)
  | .channels e c actual k reaped b finished => executionValid ra rb e ∧ exitSupported c actual ∧
      (k = .confirmed → reaped = true) ∧ (b = true → finished = true)
  | .aborted s _ => Valid ra rb encode s
  | .requested s p => Valid ra rb encode s ∧ canRequest s = true ∧ p = encode s
  | .published s p k effect | .selected s p k effect =>
      Valid ra rb encode s ∧ canRequest s = true ∧ p = encode s ∧
        (k = .confirmed → effect = some p)


 theorem next_phase_refines {ra : H → A → Prop} {rb : H → B → Prop}
    {encode : Phase A B H P → P} {s t : Phase A B H P} {event : Event A B H P}
    (step : nextPhase s event = some t) (primitive : Primitive ra rb encode s event) :
    PhaseStep ra rb encode s event t := by
  cases event <;> cases s <;>
    simp_all [nextPhase, beforePublication, canRequest, Primitive]
  all_goals subst t
  all_goals constructor <;> first | assumption | exact primitive.1 | exact primitive.2.1 | exact primitive.2.2 | exact primitive.2 | rfl

 theorem next_refines {ra : H → A → Prop} {rb : H → B → Prop}
    {encode : Phase A B H P → P} {s t : State A B H P} {event : Event A B H P}
    (step : next s event = some t) (primitive : Primitive ra rb encode s.phase event) :
    SourceStep ra rb encode ⟨s⟩ event ⟨t⟩ := by
  unfold next at step
  cases h : nextPhase s.phase event with
  | none => simp [h] at step
  | some p =>
    simp [h] at step
    subst t
    exact ⟨next_phase_refines h primitive, rfl⟩

/-- Existence is constructed for the exact admitted event list, not a separate
observation derivation or a hypothesized final correspondence. -/
theorem prefix_refines {ra : H → A → Prop} {rb : H → B → Prop}
    {encode : Phase A B H P → P} {initial target : State A B H P} {events}
    (history : Admissible ra rb encode initial events target) :
    ∃ source, AllowedPrefix ra rb encode ⟨initial⟩ events source ∧ Related source target := by
  induction history with
  | nil s => exact ⟨⟨s⟩, .nil _, rfl⟩
  | cons step primitive _ ih =>
    obtain ⟨source, allowed, related⟩ := ih
    exact ⟨source, .cons (next_refines step primitive) allowed, related⟩

theorem step_valid {ra : H → A → Prop} {rb : H → B → Prop}
    {encode : Phase A B H P → P} {s t event}
    (h : PhaseStep ra rb encode s event t) (valid : Valid ra rb encode s) :
    Valid ra rb encode t := by
  cases h <;> simp_all [Valid, captureValid, executionValid]
  case cleanup e c old k actual reaped hk preserve =>
    exact fun n hn => preserve n (valid.2 n hn)

theorem prefix_valid {ra : H → A → Prop} {rb : H → B → Prop}
    {encode : Phase A B H P → P} {s t events}
    (h : AllowedPrefix ra rb encode s events t) (valid : Valid ra rb encode s.state.phase) :
    Valid ra rb encode t.state.phase := by
  induction h with
  | nil => exact valid
  | cons step _ ih => exact ih (step_valid step.1 valid)

theorem calls_bound (s : Phase A B H P) : calls s ≤ 1 := by
  induction s <;> simp_all [calls]

/-- A source prefix cannot use a later reap as another completion decision. -/
theorem timeout_cannot_be_overwritten (e : Execution A B H) (actual : Option Nat)
    (choice : Completion) (later : Option Nat) :
    nextPhase (.decided e .timedOut actual : Phase A B H P) (.wait choice later) = none := rfl

theorem cleanup_keeps_choice (e : Execution A B H) (choice : Completion)
    (old actual : Option Nat) (k : Status) (reaped : Bool) :
    nextPhase (.decided e choice old : Phase A B H P) (.cleanup k actual reaped) =
      some (.cleaned e choice actual k reaped) := rfl

/-- Publication is gated on completed observation selection or a failed prefix. -/
theorem request_requires_ready {s : Phase A B H P} {p : P} {t}
    (h : nextPhase s (.request p) = some t) : canRequest s = true := by
  cases s <;> simp_all [nextPhase, canRequest]

def accepted : Phase A B H P → Bool
  | .selected prior _ status _ => Measurement.decide {observation prior with publication := status}
  | _ => false

/-- Independent joint postcondition retains the actual child identity, one
invocation, both boundary equalities and the exact acknowledged publication. -/
def JointSuccess (ra : H → A → Prop) (rb : H → B → Prop)
    (encode : Phase A B H P → P) (s : Phase A B H P) : Prop :=
  ∃ e c actual k reaped complete finished payload effect,
    s = .selected (.channels e c actual k reaped complete finished) payload .confirmed effect ∧
    CaptureChain ra rb e.capture.ha e.capture.hb e.capture.returned e.capture.sealed e.consumed ∧
    e.childId = e.authorizedId ∧ calls s = 1 ∧ c = .exited 0 ∧ actual = some 0 ∧
    complete = true ∧ finished = true ∧ k = .confirmed ∧ reaped = true ∧
    payload = encode (.channels e c actual k reaped complete finished) ∧ effect = some payload

theorem accepted_valid {ra : H → A → Prop} {rb : H → B → Prop}
    {encode : Phase A B H P → P} {s : Phase A B H P}
    (valid : Valid ra rb encode s) (ok : accepted s = true) : JointSuccess ra rb encode s := by
  cases s <;> simp only [accepted, Bool.false_eq_true] at ok
  case selected prior payload status effect =>
    obtain ⟨hp, ready, encoded, ack⟩ := valid
    have good := (Measurement.decide_iff _).mp ok
    cases prior <;> simp only [canRequest, Bool.false_eq_true] at ready
    case aborted prior fragment =>
      have bad := good.2.1
      simp [observation] at bad
    case channels e c actual k reaped complete finished =>
      simp only [Good, observation] at good
      rcases good with ⟨hc, hb, hk, hs⟩
      subst c; subst complete; subst k; subst status
      rcases hp with ⟨⟨⟨ha,hb,sa,sb⟩,id,xa,xb⟩,exit,clean,output⟩
      exact ⟨e, .exited 0, actual, .confirmed, reaped, true, finished, payload, effect,
        rfl, ⟨ha,hb,sa,sb,xa,xb⟩, id, rfl, rfl, exit 0 rfl, rfl,
        output rfl, rfl, clean rfl, encoded, ack rfl⟩

/-- The source witness and success refer to the same admitted prefix. -/
theorem joint_success {ra : H → A → Prop} {rb : H → B → Prop}
    {encode : Phase A B H P → P} {live : A × B} {events} {target : State A B H P}
    (history : Admissible ra rb encode ⟨live, .empty⟩ events target)
    (ok : accepted target.phase = true) :
    ∃ source, AllowedPrefix ra rb encode ⟨⟨live, .empty⟩⟩ events source ∧
      Related source target ∧ JointSuccess ra rb encode source.state.phase := by
  obtain ⟨source, allowed, related⟩ := prefix_refines history
  refine ⟨source, allowed, related, accepted_valid (prefix_valid allowed trivial) ?_⟩
  simpa [Related] using related ▸ ok

/-- External facts retained by the witnessed source state. Publication existence
alone is weaker than the exact-payload clause of `JointSuccess`. -/
def world : Phase A B H P → World
  | .decided _ _ actual => ⟨actual, false, false, false⟩
  | .cleaned _ _ actual _ reaped => ⟨actual, false, reaped, false⟩
  | .channels _ _ actual _ reaped _ finished => ⟨actual, finished, reaped, false⟩
  | .aborted prior _ | .requested prior _ => world prior
  | .published prior _ _ effect | .selected prior _ _ effect =>
      {world prior with published := effect.isSome}
  | _ => ⟨none, false, false, false⟩

/-- Only after deriving joint success do we project the same source facts to
Measurement; the world is not a separately chosen positive witness. -/
theorem joint_measurement {ra : H → A → Prop} {rb : H → B → Prop}
    {encode : Phase A B H P → P} {s : Phase A B H P}
    (h : JointSuccess ra rb encode s) :
    Corresponds (world s) (observation s) ∧ Completed (world s) := by
  rcases h with ⟨e,c,actual,k,reaped,b,finished,p,effect,rfl,chain,id,count,
    rfl,rfl,rfl,rfl,rfl,rfl,encoded,rfl⟩
  simp [Corresponds, observation, world, Completed]

/-- Arbitrary live interference preserves the entire retained attempt. -/
theorem interference_preserves (s : State A B H P) (live : A × B) :
    next s (.interfere live) = some ⟨live,s.phase⟩ := by
  cases s with
  | mk live phase => cases phase <;> rfl

theorem pending_source {ra : H → A → Prop} {rb : H → B → Prop}
    {encode : Phase A B H P → P} (s : Source A B H P) :
    Interaction.Run (fun a b => SourceStep ra rb encode a .pending b) (fun _ => s) := by
  intro _
  exact ⟨.pending _, rfl⟩


/-- Count actual spawn witnesses, not authorization records. -/
def spawnCount : List (Event A B H P) → Nat
  | [] => 0
  | .spawn _ _ :: events => 1 + spawnCount events
  | _ :: events => spawnCount events

theorem step_calls {ra : H → A → Prop} {rb : H → B → Prop}
    {encode : Phase A B H P → P} {s t event}
    (h : PhaseStep ra rb encode s event t) : calls t = calls s + spawnCount [event] := by
  cases h <;> simp [calls, spawnCount]

theorem prefix_calls {ra : H → A → Prop} {rb : H → B → Prop}
    {encode : Phase A B H P → P} {s t events}
    (h : AllowedPrefix ra rb encode s events t) :
    calls t.state.phase = calls s.state.phase + spawnCount events := by
  induction h with
  | nil => simp [spawnCount]
  | @cons s t u event events step tail ih =>
    have one := step_calls step.1
    have split : spawnCount (event :: events) = spawnCount [event] + spawnCount events := by
      cases event <;> simp [spawnCount]
    omega

theorem prefix_one_spawn {ra : H → A → Prop} {rb : H → B → Prop}
    {encode : Phase A B H P → P} {s t events}
    (h : AllowedPrefix ra rb encode s events t) : spawnCount events ≤ 1 := by
  have eq := prefix_calls h
  have bound := calls_bound t.state.phase
  omega

theorem no_authorize_after_spawn {s : Phase A B H P} (issued : calls s = 1) (id : Nat) :
    nextPhase s (.authorize id) = none := by
  cases s <;> simp_all [calls, nextPhase]

/-- Selecting a failure retains its payload just as selecting success does. -/
theorem selected_payload {ra : H → A → Prop} {rb : H → B → Prop}
    {encode : Phase A B H P → P} {prior : Phase A B H P} {p k effect}
    (h : Valid ra rb encode (.selected prior p k effect)) :
    p = encode prior ∧ observation (.selected prior p k effect) =
      {observation prior with publication := k} := ⟨h.2.2.1, rfl⟩

theorem selected_step_retains {ra : H → A → Prop} {rb : H → B → Prop}
    {encode : Phase A B H P → P} {prior : Phase A B H P} {p k effect event t}
    (h : PhaseStep ra rb encode (.selected prior p k effect) event t) :
    t = .selected prior p k effect := by
  cases h <;> simp_all [beforePublication, canRequest]

theorem selected_prefix_retains {ra : H → A → Prop} {rb : H → B → Prop}
    {encode : Phase A B H P → P} {s t events prior p k effect}
    (h : AllowedPrefix ra rb encode s events t)
    (selected : s.state.phase = .selected prior p k effect) :
    t.state.phase = .selected prior p k effect := by
  induction h with
  | nil => exact selected
  | cons step _ ih => exact ih (selected_step_retains (selected ▸ step.1))

/-- Arbitrarily long pending runs preserve the retained phase and invocation bound. -/
theorem pending_safe {ra : H → A → Prop} {rb : H → B → Prop}
    {encode : Phase A B H P → P} (s : Source A B H P) :
    ∀ n, calls ((fun _ : Nat => s) n).state.phase ≤ 1 :=
  (pending_source (ra := ra) (rb := rb) (encode := encode) s).invariant
    (calls_bound _) (fun _ _ _ _ => calls_bound _)

end Joint

end Interaction.CapturedAttempt
