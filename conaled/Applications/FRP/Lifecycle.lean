import Applications.FRP.Engine

/-! Sequential identified requests over retained source knowledge. Natural IDs
are a local high-water mark, not network exactly-once delivery acknowledgments. -/
namespace FRPSpec.Frontier.Lifecycle
open Trace
variable {T α : Type} [LinearOrder T]

inductive BeginStatus | accepted | busy | stale deriving DecidableEq, Repr
inductive Command (T α : Type)
  | begin (id : Nat) (time : T)
  | source (which : Source) (packet : Message T α)
  | process (id : Nat)
  | idle
  deriving DecidableEq, Repr
structure Response (T α : Type) where
  id : Nat
  time : T
  batch : List α
  deriving DecidableEq, Repr
structure Event (T α : Type) where
  status : Option BeginStatus
  response : Option (Response T α)
  deriving DecidableEq, Repr
structure State (T α : Type) where
  engine : Engine.MachineState T α
  last : Option Nat
  deriving DecidableEq, Repr

def init (sources : Inputs T α) : State T α := ⟨Engine.init sources,none⟩
def Fresh (last : Option Nat) (id : Nat) : Prop := match last with
  | none => True
  | some old => old < id
instance (last : Option Nat) (id : Nat) : Decidable (Fresh last id) := by
  unfold Fresh; split <;> infer_instance

def classify (s : State T α) (id : Nat) : BeginStatus :=
  match s.engine.request with
  | .pending _ => .busy
  | _ => if Fresh s.last id then .accepted else .stale

/-- Reset only the request cell; source values remain the actual retained ones. -/
def registered (s : State T α) (id : Nat) (time : T) : State T α :=
  ⟨{s.engine with request := .pending time},some id⟩

def project (id : Nat) : Command T α → Engine.Command T α
  | .source r m => .source r m
  | .process k => if id = k then .process else .idle
  | _ => .idle

def active (last : Option Nat) : Command T α → Engine.Command T α
  | .source r m => .source r m
  | .process k => if last = some k then .process else .idle
  | _ => .idle

def tag (last : Option Nat) (response : Option (T × List α)) : Option (Response T α) :=
  last.bind (fun id => response.map (fun (t,xs) => ⟨id,t,xs⟩))

def step (s : State T α) (c : Command T α) : State T α × Event T α :=
  match c with
  | .begin id time =>
    let status := classify s id
    (if status = .accepted then registered s id time else s,⟨some status,none⟩)
  | _ =>
    let next := Engine.step s.engine (active s.last c)
    (⟨next.1,s.last⟩,⟨none,tag s.last next.2⟩)

def run (s : State T α) : List (Command T α) → State T α × List (Event T α)
  | [] => (s,[])
  | c::cs => let next := step s c; let rest := run next.1 cs; (rest.1,next.2::rest.2)

def state (s : State T α) (commands : Nat → Command T α) : Nat → State T α
  | 0 => s
  | n+1 => (step (state s commands n) (commands n)).1

def event (s : State T α) (commands : Nat → Command T α) (n : Nat) :=
  (step (state s commands n) (commands n)).2

theorem registered_engine (s : State T α) (id : Nat) (time : T) :
    (registered s id time).engine =
      (Engine.step {s.engine with request := .absent} (.register time)).1 := by
  cases s with | mk e last => cases e; rfl

omit [LinearOrder T] in
theorem classify_pending (s : State T α) (id : Nat) (t : T)
    (h : s.engine.request = .pending t) : classify s id = .busy := by simp [classify,h]

omit [LinearOrder T] in
theorem accepted_fresh {s : State T α} {id : Nat} (h : classify s id = .accepted) :
    Fresh s.last id := by
  unfold classify at h
  split at h
  · contradiction
  · split at h <;> simp_all

/-- Busy rejection has priority even for a fresh ID and does not reserve it. -/
theorem begin_busy (s : State T α) (id : Nat) (time t : T)
    (h : s.engine.request = .pending t) :
    step s (.begin id time) = (s,⟨some .busy,none⟩) := by
  simp [step,classify_pending s id t h]

theorem step_last {s : State T α} (c : Command T α) :
    (step s c).1.last = s.last ∨
      ∃ id time, c = .begin id time ∧ classify s id = .accepted ∧
        (step s c).1 = registered s id time := by
  cases c with
  | begin id time =>
    by_cases h : classify s id = .accepted
    · exact .inr ⟨id,time,rfl,h,by simp [step,h]⟩
    · exact .inl (by simp [step,h])
  | source r m => exact .inl rfl
  | process id => exact .inl rfl
  | idle => exact .inl rfl

theorem step_valid {s : State T α} (h : s.engine.Valid) (c : Command T α) :
    (step s c).1.engine.Valid := by
  cases c with
  | begin id time =>
    by_cases hc : classify s id = .accepted
    · simpa [step,hc,registered,Engine.MachineState.Valid,Engine.MachineState.sources] using h
    · simpa [step,hc] using h
  | source r m => exact Engine.step_valid h _
  | process id => exact Engine.step_valid h _
  | idle => exact Engine.step_valid h _

theorem run_valid {s : State T α} (h : s.engine.Valid) (cs : List (Command T α)) :
    (run s cs).1.engine.Valid := by
  induction cs generalizing s with
  | nil => exact h
  | cons c cs ih => exact ih (step_valid h c)

theorem run_append (s : State T α) (xs ys : List (Command T α)) :
    run s (xs ++ ys) =
      let first := run s xs; let second := run first.1 ys
      (second.1,first.2 ++ second.2) := by
  induction xs generalizing s with
  | nil => rfl
  | cons c cs ih => simp [run,ih]

/-- The segment boundary is an acceptance status, not an output-equality premise. -/
def Segment (s : State T α) : List (Command T α) → Prop
  | [] => True
  | c::cs => (step s c).2.status ≠ some .accepted ∧ Segment (step s c).1 cs

theorem session_step (s : State T α) (id : Nat) (c : Command T α)
    (last : s.last = some id) (h : (step s c).2.status ≠ some .accepted) :
    (step s c).1.engine = (Engine.step s.engine (project id c)).1 ∧
    (step s c).1.last = some id ∧
    (step s c).2.response = tag (some id) (Engine.step s.engine (project id c)).2 := by
  cases c with
  | begin k t =>
    have hc : classify s k ≠ .accepted := by simpa [step] using h
    cases s with
    | mk e mark =>
      cases e with
      | mk l r q =>
        cases q <;> simp_all [step,project,Engine.step,Engine.update,Engine.pack,
          Engine.MachineState.sources,Engine.Command.action,Demand.next,Demand.emit,tag]
  | source r m => simp [step,active,project,last]
  | process k => simp [step,active,project,last]
  | idle => simp [step,active,project,last]

theorem session_run (s : State T α) (id : Nat) (cs : List (Command T α))
    (last : s.last = some id) (h : Segment s cs) :
    (run s cs).1.engine = (Engine.run s.engine (cs.map (project id))).1 ∧
    (run s cs).1.last = some id ∧
    (run s cs).2.map Event.response =
      ((Engine.run s.engine (cs.map (project id))).2.map (tag (some id))) := by
  induction cs generalizing s with
  | nil => exact ⟨rfl,last,rfl⟩
  | cons c cs ih =>
    obtain ⟨he,hl,hr⟩ := session_step s id c last h.1
    obtain ⟨ie,il,ir⟩ := ih (step s c).1 hl h.2
    simpa [run,Engine.run,he,hr] using And.intro ie (And.intro il ir)

end FRPSpec.Frontier.Lifecycle
