import Applications.FRP.Pipeline
import Examples.ReactiveTarget

/-! Literal command execution preserves timestamped responses alongside compiled
observations. No reference trace is needed by these runtime scripts. -/
namespace Examples.ReactivePipeline
open FRPSpec.Frontier FRPSpec.Reactive Progress
open FRPSpec.Frontier.Pipeline

abbrev jointConsumer := batches jointMachine
abbrev wiredConsumer := batches wired

def normal := Pipeline.run jointConsumer (Pipeline.init FRPTrace.start jointConsumer) FRPEngine.script

theorem normal_expected : normal.2 =
    [(none,none),(none,none),(none,none),(none,none),(some (2,[3,4,3]),some (1,10))] := by
  decide
example : normal.1.consumer = (1,10) := by decide

#eval (normal.2,normal.1.consumer)

example : (Pipeline.run wiredConsumer (Pipeline.init FRPTrace.start wiredConsumer) FRPEngine.script).2 =
    [(none,none),(none,none),(none,none),(none,none),(some (2,[3,4,3]),some (1,11))] := by decide

#eval let r := Pipeline.run wiredConsumer (Pipeline.init FRPTrace.start wiredConsumer) FRPEngine.script
      (r.2,r.1.consumer.1.2)

/-- Every command list compares the independently wired representation with its
joint specification; this consumes the generic relational pipeline result. -/
example (cs : List (Engine.Command ℚ Nat)) :
    (Pipeline.run wiredConsumer (Pipeline.init FRPTrace.start wiredConsumer) cs).2 =
      (Pipeline.run (batches wiredSpec) (Pipeline.init FRPTrace.start (batches wiredSpec)) cs).2 ∧
    StateRel
      (Pipeline.run wiredConsumer (Pipeline.init FRPTrace.start wiredConsumer) cs).1.consumer
      (Pipeline.run (batches wiredSpec) (Pipeline.init FRPTrace.start (batches wiredSpec)) cs).1.consumer := by
  exact run_consumer_related wiredConsumer (batches wiredSpec) StateRel
    (fun xs w s h => wired_step xs.sum xs.sum w s rfl h)
    (Engine.init FRPTrace.start) _ _ wired_initial cs

example : (Pipeline.run jointConsumer (Pipeline.init FRPTrace.start jointConsumer)
    [.register 1,.process,.process]).2 =
    [(none,none),(some (1,[]),some (1,0)),(none,none)] := by decide

example : (Pipeline.run jointConsumer (Pipeline.init FRPTrace.start jointConsumer)
    [.register 2,.process,.source .left ⟨2,[]⟩,.source .right ⟨2,[]⟩,.process]).1.consumer =
    (0,0) := by decide

example : (Pipeline.run jointConsumer (Pipeline.init FRPTrace.start jointConsumer)
    (FRPEngine.script ++ [.register 1,.process,.source .left FRPEngine.rejected,.process])).2 =
    [(none,none),(none,none),(none,none),(none,none),(some (2,[3,4,3]),some (1,10)),
      (none,none),(none,none),(none,none),(none,none)] := by decide

example : (Pipeline.run jointConsumer (Pipeline.init FRPTrace.start jointConsumer)
    [.register 2,.source .left FRPEngine.leftPacket,.source .left FRPEngine.rejected,
      .process,.source .right FRPEngine.rightPacket,.process]).2 =
    [(none,none),(none,none),(none,none),(none,none),(none,none),
      (some (2,[3,4,3]),some (1,10))] := by decide

example : (Pipeline.run jointConsumer (Pipeline.init FRPTrace.start jointConsumer)
    [.register 2,.process,.source .left ⟨2,[]⟩,.source .right ⟨2,[]⟩,.process]).2 =
    [(none,none),(none,none),(none,none),(none,none),(none,none)] := by decide

/-- Known empty output runs the compiled body, and both components advance on
this same processing transition. -/
example :
    let ready := (Pipeline.run jointConsumer (Pipeline.init FRPTrace.start jointConsumer)
      [.register 1]).1
    (Pipeline.step jointConsumer ready .process).1.consumer = (1,0) ∧
      (Pipeline.step jointConsumer ready .process).2 = (some (1,[]),some (1,0)) :=
  step_emitted jointConsumer _ .process 1 [] (by decide)

example :
    (Pipeline.step jointConsumer (Pipeline.init FRPTrace.start jointConsumer) .process).1.consumer =
      (0,0) ∧
    (Pipeline.step jointConsumer (Pipeline.init FRPTrace.start jointConsumer) .process).2 =
      (none,none) := step_silent _ _ _ rfl

/-- Chunked execution retains both source knowledge and consumer state. -/
def firstChunk : List (Engine.Command ℚ Nat) := [.register 2,.process,.source .left FRPEngine.leftPacket]
def secondChunk : List (Engine.Command ℚ Nat) := [.source .right FRPEngine.rightPacket,.process]
def resumed :=
  let first := Pipeline.run jointConsumer (Pipeline.init FRPTrace.start jointConsumer) firstChunk
  let second := Pipeline.run jointConsumer first.1 secondChunk
  (second.1,first.2 ++ second.2)

example : normal = resumed :=
  Pipeline.run_append jointConsumer (Pipeline.init FRPTrace.start jointConsumer) firstChunk secondChunk
example : resumed.1.consumer = (1,10) ∧ resumed.1.engine.request = .done := by decide

example (cs : List (Engine.Command ℚ Nat)) :
    Pipeline.run jointConsumer (Pipeline.init FRPTrace.start jointConsumer) cs =
      let engine := Engine.run (Engine.init FRPTrace.start) cs
      let consumer := Feedback.run (responseMealy jointConsumer) jointConsumer.initial engine.2
      (⟨engine.1,consumer.2⟩,engine.2.zip consumer.1) := run_factor _ _ _

/-- The optional adapter recovers the already verified completed-batch consumer. -/
example (events : List (Option (ℚ × List Nat))) :
    let d := Feedback.run (responseMealy jointConsumer) jointConsumer.initial events
    (d.1.filterMap id,d.2) =
      FRPSpec.Feedback.consume jointConsumer jointConsumer.initial (events.map (Option.map Prod.snd)) :=
  response_run_completed _ _ _

/-- Universal source-to-compiler-to-command execution, not a postulated equality
of observations. Packet compatibility is the only command premise. -/
example (cs : List (Engine.Command ℚ Nat)) (h : Engine.Corresponds FRPTrace.packets FRPDemand.early 0 cs) :
    Pipeline.run jointConsumer (Pipeline.init FRPTrace.start jointConsumer) cs =
      let events := Engine.referenceEvents FRPTrace.start FRPTrace.packets FRPDemand.early 0 cs.length
      let d := Feedback.run (responseMealy (batches jointSpec)) jointSpec.initial events
      (⟨Engine.reference FRPTrace.start FRPTrace.packets FRPDemand.early cs.length,d.2⟩,
        events.zip d.1) :=
  compiled_reference K sound jointSeed jointBody List.sum FRPTrace.start FRPTrace.packets
    FRPDemand.early cs h

example : Pipeline.run jointConsumer (Pipeline.init FRPTrace.start jointConsumer) FRPEngine.referenceScript =
    let events := Engine.referenceEvents FRPTrace.start FRPTrace.packets FRPDemand.early 0 8
    let d := Feedback.run (responseMealy (batches jointSpec)) jointSpec.initial events
    (⟨Engine.reference FRPTrace.start FRPTrace.packets FRPDemand.early 8,d.2⟩,events.zip d.1) :=
  compiled_reference K sound jointSeed jointBody List.sum FRPTrace.start FRPTrace.packets
    FRPDemand.early FRPEngine.referenceScript FRPEngine.referenceScript_corresponds

example (n : Nat) (s : Nat × Nat) :
    Pipeline.step jointConsumer ⟨Engine.reference FRPTrace.start FRPTrace.packets FRPDemand.early n,s⟩
      (Engine.commandAt FRPTrace.packets FRPDemand.early n) =
      let d := responseMealy jointConsumer s (Demand.response FRPTrace.start FRPTrace.packets FRPDemand.early n)
      (⟨Engine.reference FRPTrace.start FRPTrace.packets FRPDemand.early (n+1),d.2⟩,
        (Demand.response FRPTrace.start FRPTrace.packets FRPDemand.early n,d.1)) :=
  step_reference _ _ _ _ _ _

end Examples.ReactivePipeline
