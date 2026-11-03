import Applications.FRP.Pipeline
import SquareKit.PreservationBounds

/-! A compiled Boolean delay and a redundant finite-state realization. Cell
counts describe retained Boolean fields only, not Lean allocation, event history,
engine state or input/output buffers. This is the bounded experiment for #231. -/
namespace FRPSpec.FiniteDelay
open FirstOrderCompiler Progress Progress.Feedback
open Frontier Frontier.Trace

inductive Prim : Ty → Ty → Type where
  | seed : Prim .unit .base

def meaning : {a b : Ty} → Prim a b → Val Bool a → Val Bool b
  | _, _, .seed, _ => false

abbrev target := ListFoldCompiler.functionScalar meaning
abbrev sound := ListFoldCompiler.functionScalarSound meaning
def seed : Term Prim [] .base := .prim .seed .unit
def body : Term Prim [.base,.base] (.prod .base .base) :=
  .pair (.var (.there .here)) (.var .here)
def code := ReactiveCompiler.compile target seed body
def machine : Initialized Bool Bool Bool := ReactiveCompiler.realize target sound.denote code

/-- Independent equation: emit the previous input, then retain the new input. -/
def spec : Initialized Bool Bool Bool := ⟨fun (x,s) => (s,x),false⟩

theorem correct : machine = spec :=
  ReactiveCompiler.realize_compile target sound seed body

theorem step (x s : Bool) : machine.step (x,s) = (s,x) := by rw [correct]; rfl
theorem initial : machine.initial = false := by rw [correct]; rfl

/-- The second bit is redundant representation data, not an epoch or counter. -/
def redundant : Initialized Bool Bool (Bool × Bool) :=
  ⟨fun (x,s) => (s.1,(x,!x)),(false,true)⟩
def Related (s : Bool) (t : Bool × Bool) : Prop := t = (s,!s)

theorem related_step (x y : Bool) (s : Bool) (t : Bool × Bool)
    (same : x = y) (related : Related s t) :
    (machine.step (x,s)).1 = (redundant.step (y,t)).1 ∧
      Related (machine.step (x,s)).2 (redundant.step (y,t)).2 := by
  subst y
  rcases related with rfl
  rw [step]
  exact ⟨rfl,rfl⟩

theorem run_related (xs : List Bool) :
    (run machine.mealy machine.initial xs).1 =
      (run redundant.mealy redundant.initial xs).1 ∧
    Related (run machine.mealy machine.initial xs).2
      (run redundant.mealy redundant.initial xs).2 := by
  have h := Progress.Feedback.run_related machine.mealy redundant.mealy Eq Related Eq
    related_step (List.forall₂_same.mpr (fun _ _ => rfl) : List.Forall₂ Eq xs xs)
    (show Related machine.initial redundant.initial by rw [initial]; rfl)
  exact ⟨by simpa only [List.forall₂_eq_eq_eq] using h.1,h.2⟩

def consumer := Pipeline.inputMap (fun xs : List Bool => xs.any id) machine
def redundantConsumer := Pipeline.inputMap (fun xs : List Bool => xs.any id) redundant

/-- The compiled consumer agrees with an independent source/reference trace.
The premise aligns commands and delivered packets, not their observed outputs. -/
theorem compiled_reference {T : Type} [LinearOrder T] (sources : Inputs T Bool)
    (ms : Streams T Bool) (actions : Nat → Demand.Action T)
    (cs : List (Engine.Command T Bool)) (aligned : Engine.Corresponds ms actions 0 cs) :
    Pipeline.run consumer (Pipeline.init sources consumer) cs =
      let sourceConsumer := Pipeline.inputMap (fun xs : List Bool => xs.any id) spec
      let events := Engine.referenceEvents sources ms actions 0 cs.length
      let d := run (Pipeline.responseMealy sourceConsumer) sourceConsumer.initial events
      (⟨Engine.reference sources ms actions cs.length,d.2⟩,events.zip d.1) :=
  Pipeline.compiled_reference target sound seed body (fun xs => xs.any id)
    sources ms actions cs aligned

theorem pipeline_related {T : Type} [LinearOrder T] (sources : Inputs T Bool)
    (cs : List (Engine.Command T Bool)) :
    (Pipeline.run consumer (Pipeline.init sources consumer) cs).2 =
      (Pipeline.run redundantConsumer (Pipeline.init sources redundantConsumer) cs).2 ∧
    Related (Pipeline.run consumer (Pipeline.init sources consumer) cs).1.consumer
      (Pipeline.run redundantConsumer (Pipeline.init sources redundantConsumer) cs).1.consumer :=
  Pipeline.run_consumer_related consumer redundantConsumer Related
    (fun xs s t h => related_step (xs.any id) (xs.any id) s t rfl h)
    (Engine.init sources) machine.initial redundant.initial
    (by rw [initial]; rfl) cs

def cells (_ : Bool) : Nat := 1
def redundantCells (_ : Bool × Bool) : Nat := 2

/-- All command prefixes are covered, with the same source/target commands and
initial sources. This bound is only on the consumer's retained Boolean cells. -/
theorem pipeline_cells {T : Type} [LinearOrder T] (sources : Inputs T Bool) :
    ∀ cs : List (Engine.Command T Bool),
      redundantCells (Pipeline.run redundantConsumer (Pipeline.init sources redundantConsumer)
        cs).1.consumer ≤ 2 := by
  let source : Set Bool := {s | ∃ cs : List (Engine.Command T Bool),
    s = (Pipeline.run consumer (Pipeline.init sources consumer) cs).1.consumer}
  let targetStates : Set (Bool × Bool) := {t | ∃ cs : List (Engine.Command T Bool),
    t = (Pipeline.run redundantConsumer (Pipeline.init sources redundantConsumer) cs).1.consumer}
  have coverage : Interaction.Refines Related source targetStates := by
    rintro t ⟨cs,rfl⟩
    exact ⟨_,⟨cs,rfl⟩,(pipeline_related sources cs).2⟩
  have bounded := coverage.bound cells redundantCells (fun n => 2*n)
    (fun _ _ h => Nat.mul_le_mul_left 2 h) (fun _ _ _ => Nat.le_refl 2)
    1 (fun _ _ => Nat.le_refl 1)
  intro cs
  exact bounded _ ⟨cs,rfl⟩

/-- Progress on the synchronous interface is a separate, constructive witness.
It does not say that the frontier engine will receive adequate source packets. -/
theorem next_output (s x : Bool) : ∃ s', machine.step (x,s) = (s,s') :=
  ⟨x,step x s⟩

theorem two_delays (xs : List Bool) :
    run (seq machine machine).mealy (machine.initial,machine.initial) xs =
      let first := run machine.mealy machine.initial xs
      let second := run machine.mealy machine.initial first.1
      (second.1,(first.2,second.2)) := run_seq machine machine _ _ xs

end FRPSpec.FiniteDelay
