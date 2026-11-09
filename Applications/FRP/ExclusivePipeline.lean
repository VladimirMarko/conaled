import Applications.FRP.ExclusiveProgress
import Applications.FRP.Pipeline

/-! Exclusive request events and a continued compiled consumer. The runtime only
handles the current command; finite trace factorization is a specification. -/
namespace FRPSpec.Frontier.Exclusive.Pipeline
open Trace Progress
variable {T α B S : Type} [LinearOrder T]

structure State (T α S : Type) where
  requests : Exclusive.State T α
  consumer : S
  deriving DecidableEq, Repr

abbrev Event (T α B : Type) := Exclusive.Event T α × Option B

def init (sources : Inputs T α) (f : Feedback.Initialized (List α) B S) : State T α S :=
  ⟨Exclusive.init sources,f.initial⟩

def eventMealy (f : Feedback.Initialized (List α) B S) : Mealy S (Exclusive.Event T α) (Option B) :=
  fun s e => Frontier.Pipeline.responseMealy f s e.response

def step (f : Feedback.Initialized (List α) B S) (s : State T α S) (c : Command T α) :
    State T α S × Event T α B :=
  let e := Exclusive.step s.requests c
  let d := eventMealy f s.consumer e.2
  (⟨e.1,d.2⟩,(e.2,d.1))

def run (f : Feedback.Initialized (List α) B S) (s : State T α S) :
    List (Command T α) → State T α S × List (Event T α B)
  | [] => (s,[])
  | c::cs => let next := step f s c; let rest := run f next.1 cs
             (rest.1,next.2::rest.2)

theorem step_original (f : Feedback.Initialized (List α) B S) (s : State T α S)
    (c : Command T α) : (step f s c).2.1 = (Exclusive.step s.requests c).2 := rfl

theorem begin_preserves_consumer (f : Feedback.Initialized (List α) B S)
    (s : State T α S) (time : T) :
    (step f s (.begin time)).1.consumer = s.consumer ∧
    (step f s (.begin time)).2.2 = none := by
  cases h : s.requests.request <;>
    simp [step,Exclusive.step,h,eventMealy,Frontier.Pipeline.responseMealy]

theorem run_factor (f : Feedback.Initialized (List α) B S) (s : State T α S)
    (cs : List (Command T α)) :
    run f s cs =
      let e := Exclusive.run s.requests cs
      let d := Feedback.run (eventMealy f) s.consumer e.2
      (⟨e.1,d.2⟩,e.2.zip d.1) := by
  induction cs generalizing s with
  | nil => rfl
  | cons c cs ih => simp only [run]; rw [ih]; simp [step,Exclusive.run,Feedback.run]

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
    (events : List (Exclusive.Event T α)) :
    Feedback.run (eventMealy f) s events =
      Feedback.run (Frontier.Pipeline.responseMealy f) s (events.map Exclusive.Event.response) := by
  induction events generalizing s with
  | nil => rfl
  | cons e es ih => simp [Feedback.run,eventMealy,ih]

/-- Existing response adapter transport supplies the consumer proof; requests
statuses and original responses stay identical at every command position. -/
theorem run_consumer_related {S' : Type} (f : Feedback.Initialized (List α) B S)
    (g : Feedback.Initialized (List α) B S') (R : S → S' → Prop)
    (localStep : ∀ xs s t, R s t →
      (f.step (xs,s)).1 = (g.step (xs,t)).1 ∧ R (f.step (xs,s)).2 (g.step (xs,t)).2)
    (requests : Exclusive.State T α) (s : S) (t : S') (h : R s t)
    (cs : List (Command T α)) :
    (run f ⟨requests,s⟩ cs).2 = (run g ⟨requests,t⟩ cs).2 ∧
      R (run f ⟨requests,s⟩ cs).1.consumer (run g ⟨requests,t⟩ cs).1.consumer := by
  simp only [run_factor,event_run]
  have hr := Frontier.Pipeline.response_run_related f g R localStep
    ((Exclusive.run requests cs).2.map Exclusive.Event.response) s t h
  exact ⟨congrArg (List.zip (Exclusive.run requests cs).2) hr.1,hr.2⟩

section Compilation
open FirstOrderCompiler
variable {Prim : Ty → Ty → Type} {Base : Type} {a b st : Ty}

/-- Compilation preserves the entire requests execution and retained consumer
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
end FRPSpec.Frontier.Exclusive.Pipeline
