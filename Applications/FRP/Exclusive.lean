import Applications.FRP.LifecycleProgress

/-! Exclusive, serial requests. The runtime retains only the existing engine
state; increasing occurrence labels belong to the reference proof, not the API. -/
namespace FRPSpec.Frontier.Exclusive
open Trace
variable {T α : Type} [LinearOrder T]

inductive Command (T α : Type)
  | begin (time : T)
  | source (which : Source) (packet : Message T α)
  | process
  | idle
  deriving DecidableEq, Repr
inductive BeginStatus | accepted | busy deriving DecidableEq, Repr
structure Event (T α : Type) where
  status : Option BeginStatus
  response : Option (T × List α)
  deriving DecidableEq, Repr
abbrev State := Engine.MachineState

def init (sources : Inputs T α) : State T α := Engine.init sources

def project : Command T α → Engine.Command T α
  | .source r m => .source r m
  | .process => .process
  | _ => .idle

def step (s : State T α) (c : Command T α) : State T α × Event T α :=
  match c with
  | .begin t => match s.request with
    | .pending _ => (s,⟨some .busy,none⟩)
    | _ => ({s with request := .pending t},⟨some .accepted,none⟩)
  | _ => let next := Engine.step s (project c); (next.1,⟨none,next.2⟩)

def run (s : State T α) : List (Command T α) → State T α × List (Event T α)
  | [] => (s,[])
  | c::cs => let next := step s c; let rest := run next.1 cs; (rest.1,next.2::rest.2)

def state (s : State T α) (commands : Nat → Command T α) : Nat → State T α
  | 0 => s
  | n+1 => (step (state s commands n) (commands n)).1

def event (s : State T α) (commands : Nat → Command T α) (n : Nat) :=
  (step (state s commands n) (commands n)).2

theorem begin_busy (s : State T α) (t u : T) (h : s.request = .pending u) :
    step s (.begin t) = (s,⟨some .busy,none⟩) := by simp [step,h]

theorem begin_sources (s : State T α) (t : T) :
    (step s (.begin t)).1.sources = s.sources := by
  cases s with | mk l r q => cases q <;> rfl

theorem run_append (s : State T α) (xs ys : List (Command T α)) :
    run s (xs ++ ys) = let a := run s xs; let b := run a.1 ys; (b.1,a.2 ++ b.2) := by
  induction xs generalizing s with
  | nil => rfl
  | cons c cs ih => simp [run,ih]

/-- Proof-only label. Accepted begins advance it; busy begins do not. -/
def nextLabel (label : Nat) (s : State T α) (c : Command T α) : Nat :=
  if (step s c).2.status = some .accepted then label+1 else label

/-- This constructs admissible reference commands, rather than erasing arbitrary
identified traces. The initial reserved label zero has no accepted request. -/
def labelCommand (label : Nat) : Command T α → Lifecycle.Command T α
  | .begin t => .begin (label+1) t
  | .source r m => .source r m
  | .process => .process label
  | .idle => .idle

def reference (s : State T α) (label : Nat) : Lifecycle.State T α := ⟨s,some label⟩

def eraseStatus : Lifecycle.BeginStatus → BeginStatus
  | .accepted => .accepted
  | .busy => .busy
  | .stale => .busy

def erase (e : Lifecycle.Event T α) : Event T α :=
  ⟨e.status.map eraseStatus,e.response.map (fun r => (r.time,r.batch))⟩

/-- The stale case of eraseStatus is never produced by this constructed lift. -/
theorem step_refines (s : State T α) (label : Nat) (c : Command T α) :
    Lifecycle.step (reference s label) (labelCommand label c) =
      (reference (step s c).1 (nextLabel label s c),
       ⟨(step s c).2.status.map (fun k => match k with
          | .accepted => Lifecycle.BeginStatus.accepted | .busy => .busy),
        Lifecycle.tag (some label) (step s c).2.response⟩) := by
  cases c with
  | begin t =>
    cases h : s.request <;>
      simp [step,reference,labelCommand,Lifecycle.step,Lifecycle.classify,h,
        Lifecycle.Fresh,Lifecycle.registered,nextLabel,Lifecycle.tag]
  | source r m =>
    simp [step,reference,labelCommand,Lifecycle.step,Lifecycle.active,project,nextLabel]
  | process =>
    simp [step,reference,labelCommand,Lifecycle.step,Lifecycle.active,project,nextLabel]
  | idle =>
    simp [step,reference,labelCommand,Lifecycle.step,Lifecycle.active,project,nextLabel]

theorem step_erases (s : State T α) (label : Nat) (c : Command T α) :
    erase (Lifecycle.step (reference s label) (labelCommand label c)).2 = (step s c).2 := by
  rw [step_refines]
  cases h : (step s c).2 with | mk status response =>
    cases status with
    | none => cases response <;> rfl
    | some k => cases k <;> cases response <;> rfl

/-- Finite labelled trace and its final label, constructed from actual admissions. -/
def lift (s : State T α) (label : Nat) : List (Command T α) → Nat × List (Lifecycle.Command T α)
  | [] => (label,[])
  | c::cs => let rest := lift (step s c).1 (nextLabel label s c) cs
            (rest.1,labelCommand label c::rest.2)

theorem run_refines (s : State T α) (label : Nat) (cs : List (Command T α)) :
    (Lifecycle.run (reference s label) (lift s label cs).2).1 =
      reference (run s cs).1 (lift s label cs).1 ∧
    (Lifecycle.run (reference s label) (lift s label cs).2).2.map erase = (run s cs).2 := by
  induction cs generalizing s label with
  | nil => exact ⟨rfl,rfl⟩
  | cons c cs ih =>
    have hs := congrArg Prod.fst (step_refines s label c)
    have he := step_erases s label c
    obtain ⟨hi,ho⟩ := ih (step s c).1 (nextLabel label s c)
    simp only [lift,Lifecycle.run,run,hs,List.map_cons]
    exact ⟨hi,congrArg₂ List.cons he ho⟩

/-- Occurrence labels are specification indices, absent from State and step. -/
def label (s : State T α) (commands : Nat → Command T α) : Nat → Nat
  | 0 => 0
  | n+1 => nextLabel (label s commands n) (state s commands n) (commands n)
def labelled (s : State T α) (commands : Nat → Command T α) (n : Nat) :=
  labelCommand (label s commands n) (commands n)

theorem state_refines (s : State T α) (commands : Nat → Command T α) (n : Nat) :
    Lifecycle.state (reference s 0) (labelled s commands) n =
      reference (state s commands n) (label s commands n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [Lifecycle.state,ih,labelled,state,label]
    exact congrArg Prod.fst (step_refines _ _ _)

/-- Accepted occurrences strictly advance their proof labels, including equal timestamps. -/
theorem label_accepted (s : State T α) (commands : Nat → Command T α) (n : Nat)
    (h : (event s commands n).status = some .accepted) :
    label s commands (n+1) = label s commands n + 1 := by
  simp [label,nextLabel,event] at *
  simp [h]

theorem event_refines (s : State T α) (commands : Nat → Command T α) (n : Nat) :
    Lifecycle.event (reference s 0) (labelled s commands) n =
      ⟨(event s commands n).status.map (fun k => match k with
         | .accepted => Lifecycle.BeginStatus.accepted | .busy => .busy),
       Lifecycle.tag (some (label s commands n)) (event s commands n).response⟩ := by
  unfold Lifecycle.event
  rw [state_refines]
  exact congrArg Prod.snd (step_refines _ _ _)

theorem at_most_once (s : State T α) (commands : Nat → Command T α) {i j : Nat}
    (hij : i < j) {t u : T} {xs ys : List α}
    (hi : (event s commands i).response = some (t,xs))
    (hj : (event s commands j).response = some (u,ys)) :
    label s commands j ≠ label s commands i := by
  apply Lifecycle.at_most_once (reference s 0) (labelled s commands) hij
    (r := ⟨label s commands i,t,xs⟩) (r' := ⟨label s commands j,u,ys⟩)
  · simp [event_refines,hi,Lifecycle.tag]
  · simp [event_refines,hj,Lifecycle.tag]

theorem response_sound {s : State T α} {c : Command T α} {t : T} {xs : List α}
    (h : (step s c).2.response = some (t,xs)) (left right : T → List α)
    (hl : (s.sources .left).Completes left) (hr : (s.sources .right).Completes right) :
    xs = left t ++ right t := by
  apply Lifecycle.response_sound (s := reference s 0) (c := labelCommand 0 c)
    (r := ⟨0,t,xs⟩) _ left right hl hr
  simp [step_refines,h,Lifecycle.tag]

theorem step_valid {s : State T α} (h : s.Valid) (c : Command T α) :
    (step s c).1.Valid := by
  have hv := Lifecycle.step_valid (s := reference s 0) h (labelCommand 0 c)
  change (Lifecycle.step (reference s 0) (labelCommand 0 c)).1.engine.Valid at hv
  rw [step_refines] at hv
  exact hv

theorem run_valid {s : State T α} (h : s.Valid) (cs : List (Command T α)) :
    (run s cs).1.Valid := by
  induction cs generalizing s with
  | nil => exact h
  | cons c cs ih => exact ih (step_valid h c)

end FRPSpec.Frontier.Exclusive
