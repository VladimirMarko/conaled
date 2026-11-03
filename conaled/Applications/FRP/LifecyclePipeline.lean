import Applications.FRP.LifecycleProgress
import Applications.FRP.Pipeline

/-! Tagged lifecycle events and a continued compiled consumer. The runtime only
handles the current command; finite trace factorization is a specification. -/
namespace FRPSpec.Frontier.Lifecycle.Pipeline
open Trace Progress
variable {T α B S : Type} [LinearOrder T]

structure State (T α S : Type) where
  lifecycle : Lifecycle.State T α
  consumer : S
  deriving DecidableEq, Repr

abbrev Event (T α B : Type) := Lifecycle.Event T α × Option B

def init (sources : Inputs T α) (f : Feedback.Initialized (List α) B S) : State T α S :=
  ⟨Lifecycle.init sources,f.initial⟩

/-- Forget only the identity for the existing batch consumer, retaining the
complete tagged event independently in the output. -/
def untag (e : Lifecycle.Event T α) : Option (T × List α) :=
  e.response.map fun r => (r.time,r.batch)

def eventMealy (f : Feedback.Initialized (List α) B S) : Mealy S (Lifecycle.Event T α) (Option B) :=
  fun s e => Frontier.Pipeline.responseMealy f s (untag e)

def step (f : Feedback.Initialized (List α) B S) (s : State T α S) (c : Command T α) :
    State T α S × Event T α B :=
  let e := Lifecycle.step s.lifecycle c
  let d := eventMealy f s.consumer e.2
  (⟨e.1,d.2⟩,(e.2,d.1))

def run (f : Feedback.Initialized (List α) B S) (s : State T α S) :
    List (Command T α) → State T α S × List (Event T α B)
  | [] => (s,[])
  | c::cs => let next := step f s c; let rest := run f next.1 cs
             (rest.1,next.2::rest.2)

theorem step_original (f : Feedback.Initialized (List α) B S) (s : State T α S)
    (c : Command T α) : (step f s c).2.1 = (Lifecycle.step s.lifecycle c).2 := rfl

theorem begin_preserves_consumer (f : Feedback.Initialized (List α) B S)
    (s : State T α S) (id : Nat) (time : T) :
    (step f s (.begin id time)).1.consumer = s.consumer ∧
    (step f s (.begin id time)).2.2 = none := by
  simp [step,Lifecycle.step,eventMealy,untag,Frontier.Pipeline.responseMealy]

theorem run_factor (f : Feedback.Initialized (List α) B S) (s : State T α S)
    (cs : List (Command T α)) :
    run f s cs =
      let e := Lifecycle.run s.lifecycle cs
      let d := Feedback.run (eventMealy f) s.consumer e.2
      (⟨e.1,d.2⟩,e.2.zip d.1) := by
  induction cs generalizing s with
  | nil => rfl
  | cons c cs ih => simp only [run]; rw [ih]; simp [step,Lifecycle.run,Feedback.run]

theorem run_append (f : Feedback.Initialized (List α) B S) (s : State T α S)
    (xs ys : List (Command T α)) :
    run f s (xs ++ ys) =
      let first := run f s xs
      let second := run f first.1 ys
      (second.1,first.2 ++ second.2) := by
  induction xs generalizing s with
  | nil => rfl
  | cons c cs ih => simp [run,ih]

omit [LinearOrder T] in
theorem event_run (f : Feedback.Initialized (List α) B S) (s : S)
    (events : List (Lifecycle.Event T α)) :
    Feedback.run (eventMealy f) s events =
      Feedback.run (Frontier.Pipeline.responseMealy f) s (events.map untag) := by
  induction events generalizing s with
  | nil => rfl
  | cons e es ih => simp [Feedback.run,eventMealy,ih]

/-- Existing response adapter transport supplies the consumer proof; lifecycle
statuses and tagged originals stay identical at every command position. -/
theorem run_consumer_related {S' : Type} (f : Feedback.Initialized (List α) B S)
    (g : Feedback.Initialized (List α) B S') (R : S → S' → Prop)
    (localStep : ∀ xs s t, R s t →
      (f.step (xs,s)).1 = (g.step (xs,t)).1 ∧ R (f.step (xs,s)).2 (g.step (xs,t)).2)
    (lifecycle : Lifecycle.State T α) (s : S) (t : S') (h : R s t)
    (cs : List (Command T α)) :
    (run f ⟨lifecycle,s⟩ cs).2 = (run g ⟨lifecycle,t⟩ cs).2 ∧
      R (run f ⟨lifecycle,s⟩ cs).1.consumer (run g ⟨lifecycle,t⟩ cs).1.consumer := by
  simp only [run_factor,event_run]
  have hr := Frontier.Pipeline.response_run_related f g R localStep
    ((Lifecycle.run lifecycle cs).2.map untag) s t h
  exact ⟨congrArg (List.zip (Lifecycle.run lifecycle cs).2) hr.1,hr.2⟩

section Compilation
open FirstOrderCompiler
variable {Prim : Ty → Ty → Type} {Base : Type} {a b st : Ty}

/-- Compilation preserves the entire lifecycle execution and retained consumer
state, across any number of accepted sessions. -/
theorem compiled_run (K : Target Prim)
    {meaning : {a b : Ty} → Prim a b → Val Base a → Val Base b}
    (sound : Sound Base K meaning) (seed : Term Prim [] st)
    (body : Term Prim [a,st] (.prod b st)) (observe : List α → Val Base a)
    (sources : Inputs T α) (cs : List (Command T α)) :
    let f := Frontier.Pipeline.inputMap observe (ReactiveCompiler.realize K sound.denote
      (ReactiveCompiler.compile K seed body))
    let g := Frontier.Pipeline.inputMap observe (ReactiveCompiler.source meaning seed body)
    run f (init sources f) cs = run g (init sources g) cs := by
  dsimp only
  rw [ReactiveCompiler.realize_compile K sound]
end Compilation
end FRPSpec.Frontier.Lifecycle.Pipeline
