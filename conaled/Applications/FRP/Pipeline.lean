import Applications.FRP.Engine
import Applications.FRP.ReactiveConsumers

/-! Incremental engine/consumer composition. Runtime processes one concrete
command and its actual emission; whole-trace factorization is proof-only. -/
namespace FRPSpec.Frontier.Pipeline
open Trace Progress
variable {T α B S : Type} [LinearOrder T]

structure State (T α S : Type) where
  engine : Engine.MachineState T α
  consumer : S
  deriving DecidableEq, Repr

abbrev Event (T α B : Type) := Option (T × List α) × Option B

def init (sources : Inputs T α) (f : Feedback.Initialized (List α) B S) : State T α S :=
  ⟨Engine.init sources,f.initial⟩

/-- Silence stutters; every emitted batch, including [], runs one consumer tick. -/
def responseMealy (f : Feedback.Initialized (List α) B S) :
    Mealy S (Option (T × List α)) (Option B) := fun s response =>
  match response with
  | none => (none,s)
  | some (_,xs) => let next := f.step (xs,s); (some next.1,next.2)

def step (f : Feedback.Initialized (List α) B S) (s : State T α S) (c : Engine.Command T α) :
    State T α S × Event T α B :=
  let engine := Engine.step s.engine c
  let consumer := responseMealy f s.consumer engine.2
  (⟨engine.1,consumer.2⟩,(engine.2,consumer.1))

def run (f : Feedback.Initialized (List α) B S) (s : State T α S) :
    List (Engine.Command T α) → State T α S × List (Event T α B)
  | [] => (s,[])
  | c::cs =>
    let next := step f s c
    let rest := run f next.1 cs
    (rest.1,next.2::rest.2)

theorem step_engine (f : Feedback.Initialized (List α) B S) (s : State T α S)
    (c : Engine.Command T α) : (step f s c).1.engine = (Engine.step s.engine c).1 := rfl

theorem step_original (f : Feedback.Initialized (List α) B S) (s : State T α S)
    (c : Engine.Command T α) : (step f s c).2.1 = (Engine.step s.engine c).2 := rfl

theorem step_silent (f : Feedback.Initialized (List α) B S) (s : State T α S)
    (c : Engine.Command T α) (h : (Engine.step s.engine c).2 = none) :
    (step f s c).1.consumer = s.consumer ∧ (step f s c).2 = (none,none) := by
  simp [step,h,responseMealy]

theorem step_emitted (f : Feedback.Initialized (List α) B S) (s : State T α S)
    (c : Engine.Command T α) (t : T) (xs : List α)
    (h : (Engine.step s.engine c).2 = some (t,xs)) :
    (step f s c).1.consumer = (f.step (xs,s.consumer)).2 ∧
      (step f s c).2 = (some (t,xs),some (f.step (xs,s.consumer)).1) := by
  simp [step,h,responseMealy]

/-- Both before/after boundaries and the response's processing position are exact. -/
theorem step_reference (f : Feedback.Initialized (List α) B S)
    (sources : Inputs T α) (ms : Streams T α) (actions : Nat → Demand.Action T)
    (n : Nat) (s : S) :
    step f ⟨Engine.reference sources ms actions n,s⟩ (Engine.commandAt ms actions n) =
      let next := responseMealy f s (Demand.response sources ms actions n)
      (⟨Engine.reference sources ms actions (n+1),next.2⟩,
        (Demand.response sources ms actions n,next.1)) := by
  simp only [step,Engine.step_refines]

/-- The full-response trace occurs only in this specification of the runtime
loop. Both original and derived optional lists retain every command position. -/
theorem run_factor (f : Feedback.Initialized (List α) B S) (s : State T α S)
    (cs : List (Engine.Command T α)) :
    run f s cs =
      let e := Engine.run s.engine cs
      let d := Feedback.run (responseMealy f) s.consumer e.2
      (⟨e.1,d.2⟩,e.2.zip d.1) := by
  induction cs generalizing s with
  | nil => rfl
  | cons c cs ih =>
    simp only [run]
    rw [ih]
    simp [step,Engine.run,Feedback.run]

theorem run_append (f : Feedback.Initialized (List α) B S) (s : State T α S)
    (xs ys : List (Engine.Command T α)) :
    run f s (xs ++ ys) =
      let first := run f s xs
      let second := run f first.1 ys
      (second.1,first.2 ++ second.2) := by
  induction xs generalizing s with
  | nil => rfl
  | cons c cs ih => simp [run,ih]

omit [LinearOrder T] in
/-- The existing completed-batch consumer is recovered by forgetting silent
output positions only after execution. Its retained state is unchanged. -/
theorem response_run_completed (f : Feedback.Initialized (List α) B S) (s : S)
    (events : List (Option (T × List α))) :
    let d := Feedback.run (responseMealy f) s events
    (d.1.filterMap id,d.2) =
      FRPSpec.Feedback.consume f s (events.map (Option.map Prod.snd)) := by
  induction events generalizing s with
  | nil => rfl
  | cons event events ih =>
    cases event with
    | none => simpa [Feedback.run,responseMealy,FRPSpec.Feedback.consume] using ih s
    | some p =>
      simpa [Feedback.run,responseMealy,FRPSpec.Feedback.consume] using
        congrArg (fun z : List B × S => ((f.step (p.2,s)).1 :: z.1,z.2))
          (ih (f.step (p.2,s)).2)

/-- No outputs occur in the alignment premise; it only identifies actions and
ordered pre-consumption packets, including rejected packets. -/
theorem run_reference (f : Feedback.Initialized (List α) B S)
    (sources : Inputs T α) (ms : Streams T α) (actions : Nat → Demand.Action T)
    (n : Nat) (s : S) (cs : List (Engine.Command T α))
    (h : Engine.Corresponds ms actions n cs) :
    run f ⟨Engine.reference sources ms actions n,s⟩ cs =
      let events := Engine.referenceEvents sources ms actions n cs.length
      let d := Feedback.run (responseMealy f) s events
      (⟨Engine.reference sources ms actions (n+cs.length),d.2⟩,events.zip d.1) := by
  rw [run_factor,Engine.run_refines sources ms actions cs n h]

omit [LinearOrder T] in
/-- Local state-representation changes preserve the complete optional observation
sequence. This lifts the existing finite feedback relation law. -/
theorem response_run_related {S' : Type} (f : Feedback.Initialized (List α) B S)
    (g : Feedback.Initialized (List α) B S') (R : S → S' → Prop)
    (localStep : ∀ xs s t, R s t →
      (f.step (xs,s)).1 = (g.step (xs,t)).1 ∧ R (f.step (xs,s)).2 (g.step (xs,t)).2)
    (events : List (Option (T × List α))) (s : S) (t : S') (h : R s t) :
    (Feedback.run (responseMealy f) s events).1 = (Feedback.run (responseMealy g) t events).1 ∧
      R (Feedback.run (responseMealy f) s events).2 (Feedback.run (responseMealy g) t events).2 := by
  have one : ∀ (a a' : Option (T × List α)) s t, a = a' → R s t →
      (responseMealy f s a).1 = (responseMealy g t a').1 ∧
        R (responseMealy f s a).2 (responseMealy g t a').2 := by
    intro a a' s t ha hr
    subst a'
    cases a with
    | none => exact ⟨rfl,hr⟩
    | some p =>
      have hl := localStep p.2 s t hr
      exact ⟨congrArg some hl.1,hl.2⟩
  have hr := Feedback.run_related (responseMealy f) (responseMealy g) Eq R Eq one
    (List.forall₂_same.mpr (fun _ _ => rfl) : List.Forall₂ Eq events events) h
  exact ⟨by simpa only [List.forall₂_eq_eq_eq] using hr.1,hr.2⟩

theorem run_consumer_related {S' : Type} (f : Feedback.Initialized (List α) B S)
    (g : Feedback.Initialized (List α) B S') (R : S → S' → Prop)
    (localStep : ∀ xs s t, R s t →
      (f.step (xs,s)).1 = (g.step (xs,t)).1 ∧ R (f.step (xs,s)).2 (g.step (xs,t)).2)
    (engine : Engine.MachineState T α) (s : S) (t : S') (h : R s t)
    (cs : List (Engine.Command T α)) :
    (run f ⟨engine,s⟩ cs).2 = (run g ⟨engine,t⟩ cs).2 ∧
      R (run f ⟨engine,s⟩ cs).1.consumer (run g ⟨engine,t⟩ cs).1.consumer := by
  simp only [run_factor]
  have hr := response_run_related f g R localStep (Engine.run engine cs).2 s t h
  exact ⟨congrArg (List.zip (Engine.run engine cs).2) hr.1,hr.2⟩

/-- Explicit payload observation; the original timestamped response is retained
separately by step/run and need not be recoverable from this observation. -/
def inputMap {A : Type} (observe : List α → A) (f : Feedback.Initialized A B S) :
    Feedback.Initialized (List α) B S where
  initial := f.initial
  step := fun (xs,s) => f.step (observe xs,s)

section Compilation
open FirstOrderCompiler
variable {Prim : Ty → Ty → Type} {Base : Type} {a b st : Ty}

/-- Source seed/body semantics, scalar compiler correctness and command refinement
compose into full finite paired-event and final-state agreement. -/
theorem compiled_reference (K : Target Prim)
    {meaning : {a b : Ty} → Prim a b → Val Base a → Val Base b}
    (sound : Sound Base K meaning) (seed : Term Prim [] st)
    (body : Term Prim [a,st] (.prod b st)) (observe : List α → Val Base a)
    (sources : Inputs T α) (ms : Streams T α) (actions : Nat → Demand.Action T)
    (cs : List (Engine.Command T α)) (h : Engine.Corresponds ms actions 0 cs) :
    let f := inputMap observe (ReactiveCompiler.realize K sound.denote
      (ReactiveCompiler.compile K seed body))
    let g := inputMap observe (ReactiveCompiler.source meaning seed body)
    let events := Engine.referenceEvents sources ms actions 0 cs.length
    let d := Feedback.run (responseMealy g) g.initial events
    run f (init sources f) cs =
      (⟨Engine.reference sources ms actions cs.length,d.2⟩,events.zip d.1) := by
  dsimp only
  rw [ReactiveCompiler.realize_compile K sound]
  simpa only [Engine.reference_zero,Nat.zero_add,init,inputMap] using
    run_reference (inputMap observe (ReactiveCompiler.source meaning seed body))
      sources ms actions 0 (ReactiveCompiler.source meaning seed body).initial cs h
end Compilation

end FRPSpec.Frontier.Pipeline
