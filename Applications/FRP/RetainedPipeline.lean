import Applications.FRP.RetainedLifecycle

/-! Continued consumers use the existing tagged optional-response adapter.
Retention notices do not become fabricated empty batches. -/
namespace FRPSpec.Frontier.Retention.Pipeline
open Trace Progress
variable {T α B S : Type} [LinearOrder T]

structure State (T α S : Type) where
  retained : Retention.State T α
  consumer : S
  deriving DecidableEq, Repr

abbrev Output (T α B : Type) := Retention.Event T α × Option B

def init (q : T) (sources : Inputs T α) (f : Feedback.Initialized (List α) B S) : State T α S :=
  ⟨Retention.init q sources,f.initial⟩

def step (f : Feedback.Initialized (List α) B S) (s : State T α S)
    (c : Retention.Command T α) : State T α S × Output T α B :=
  let e := Retention.step s.retained c
  let d := Lifecycle.Pipeline.eventMealy f s.consumer e.2.native
  (⟨e.1,d.2⟩,(e.2,d.1))

def run (f : Feedback.Initialized (List α) B S) (s : State T α S) :
    List (Retention.Command T α) → State T α S × List (Output T α B)
  | [] => (s,[])
  | c::cs => let a := step f s c; let b := run f a.1 cs; (b.1,a.2::b.2)

/-- The same consumer receives exactly the native event at each command position. -/
theorem run_factor (f : Feedback.Initialized (List α) B S) (s : State T α S)
    (cs : List (Retention.Command T α)) :
    run f s cs =
      let e := Retention.run s.retained cs
      let d := Feedback.run (Lifecycle.Pipeline.eventMealy f) s.consumer (e.2.map Retention.Event.native)
      (⟨e.1,d.2⟩,e.2.zip d.1) := by
  induction cs generalizing s with
  | nil => rfl
  | cons c cs ih => simp only [run]; rw [ih]; simp [step,Retention.run,Feedback.run]

theorem consumer_refines (f : Feedback.Initialized (List α) B S)
    (s : Retention.State T α) (full : Lifecycle.State T α) (consumer : S)
    (h : Retention.Related s full) (cs : List (Retention.Command T α)) :
    (run f ⟨s,consumer⟩ cs).1.consumer =
      (Lifecycle.Pipeline.run f ⟨full,consumer⟩ (Retention.projected s cs)).1.consumer ∧
    ((run f ⟨s,consumer⟩ cs).2.map (fun e => (e.1.native,e.2))) =
      (Lifecycle.Pipeline.run f ⟨full,consumer⟩ (Retention.projected s cs)).2 := by
  have he := (Retention.run_refines s full h cs).2
  simp only [run_factor,Lifecycle.Pipeline.run_factor]
  constructor
  · simp only [he]
  · rw [← he]
    have zip_map (xs : List (Retention.Event T α)) (ys : List (Option B)) :
        (xs.zip ys).map (fun e => (e.1.native,e.2)) = (xs.map Retention.Event.native).zip ys := by
      induction xs generalizing ys with
      | nil => simp
      | cons x xs ih => cases ys <;> simp [ih]
    exact zip_map _ _

theorem run_append (f : Feedback.Initialized (List α) B S) (s : State T α S)
    (xs ys : List (Retention.Command T α)) :
    run f s (xs++ys) = let a := run f s xs; let b := run f a.1 ys; (b.1,a.2++b.2) := by
  induction xs generalizing s with
  | nil => rfl
  | cons c cs ih => simp [run,ih]

section Compilation
open FirstOrderCompiler
variable {Prim : Ty → Ty → Type} {Base : Type} {a b st : Ty}

theorem compiled_run (K : Target Prim)
    {meaning : {a b : Ty} → Prim a b → Val Base a → Val Base b}
    (sound : Sound Base K meaning) (seed : Term Prim [] st)
    (body : Term Prim [a,st] (.prod b st)) (observe : List α → Val Base a)
    (q : T) (sources : Inputs T α) (cs : List (Retention.Command T α)) :
    let f := Frontier.Pipeline.inputMap observe (ReactiveCompiler.realize K sound.denote
      (ReactiveCompiler.compile K seed body))
    let g := Frontier.Pipeline.inputMap observe (ReactiveCompiler.source meaning seed body)
    run f (init q sources f) cs = run g (init q sources g) cs := by
  dsimp only
  rw [ReactiveCompiler.realize_compile K sound]
end Compilation
end FRPSpec.Frontier.Retention.Pipeline
