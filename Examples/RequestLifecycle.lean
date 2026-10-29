import Applications.FRP.LifecyclePipeline
import Examples.ReactivePipeline

/-! Sequential sessions retain source knowledge and compiled consumer state. -/
namespace Examples.RequestLifecycle
open FRPSpec.Frontier FRPSpec.Reactive Progress

abbrev jointConsumer := batches jointMachine
abbrev wiredConsumer := batches wired

def first : List (Lifecycle.Command ℚ Nat) :=
  [.begin 0 2,.source .left FRPEngine.leftPacket,.source .right FRPEngine.rightPacket,.process 0]
def secondCommands : List (Lifecycle.Command ℚ Nat) := [.begin 1 2,.process 1]
def normal := Lifecycle.Pipeline.run jointConsumer (Lifecycle.Pipeline.init FRPTrace.start jointConsumer) (first ++ secondCommands)

example : normal.2 =
    [(⟨some .accepted,none⟩,none),(⟨none,none⟩,none),(⟨none,none⟩,none),
     (⟨none,some ⟨0,2,[3,4,3]⟩⟩,some (1,10)),(⟨some .accepted,none⟩,none),
     (⟨none,some ⟨1,2,[3,4,3]⟩⟩,some (2,20))] := by decide
example : normal.1.consumer = (2,20) := by decide
#eval (normal.2,normal.1.consumer)

def second : Lifecycle.State ℚ Nat := (Lifecycle.run (Lifecycle.init FRPTrace.start) (first ++ [.begin 1 2])).1
example : second.last = some 1 ∧ second.engine.request = .pending 2 := by decide
example : (Lifecycle.step second (.process 0)).1 = second ∧
    (Lifecycle.step second (.process 0)).2 = ⟨none,none⟩ := by decide
example : (Lifecycle.step second (.process 1)).2.response = some ⟨1,2,[3,4,3]⟩ := by decide
example : (Lifecycle.step second (.begin 2 1)).1 = second ∧
    (Lifecycle.step second (.begin 2 1)).2.status = some .busy := by decide
example : (Lifecycle.step (Lifecycle.step second (.process 1)).1 (.begin 2 1)).2.status = some .accepted := by decide
example : (Lifecycle.step second (.begin 0 5)).2.status = some .busy ∧
    (Lifecycle.step (Lifecycle.step second (.process 1)).1 (.begin 0 5)).2.status = some .stale := by decide
example : (Lifecycle.step (Lifecycle.step (Lifecycle.init FRPTrace.start) (.begin 0 2)).1 (.begin 0 5)).2.status =
    some .busy := by decide
example : (Lifecycle.step second (.source .left FRPEngine.rejected)).1 = second := by decide

example : (Lifecycle.Pipeline.run jointConsumer (Lifecycle.Pipeline.init FRPTrace.start jointConsumer)
    [.begin 0 1,.process 0,.process 0]).2 =
    [(⟨some .accepted,none⟩,none),(⟨none,some ⟨0,1,[]⟩⟩,some (1,0)),(⟨none,none⟩,none)] := by decide

example (cs : List (Lifecycle.Command ℚ Nat)) : ∀ source,
    ((Lifecycle.run (Lifecycle.init FRPTrace.start) cs).1.engine.sources source).Valid := by
  apply Lifecycle.run_valid
  intro source
  cases source <;> simp [Lifecycle.init,Engine.init,Engine.pack,Engine.MachineState.sources,
    FRPTrace.start,initial,FRPSpec.Frontier.State.Valid]

/-- Soundness uses current completion evidence, including the retained second
session's knowledge, rather than assuming valid packets identify an external truth. -/
example (left right : ℚ → List Nat)
    (hl : (second.engine.sources .left).Completes left)
    (hr : (second.engine.sources .right).Completes right) :
    [3,4,3] = left 2 ++ right 2 :=
  Lifecycle.response_sound (s := second) (c := .process 1)
    (r := ⟨1,2,[3,4,3]⟩) (by decide) left right hl hr

example (cs : List (Lifecycle.Command ℚ Nat)) (h : Lifecycle.Segment second cs) :
    (Lifecycle.run second cs).1.engine = (Engine.run second.engine (cs.map (Lifecycle.project 1))).1 ∧
    (Lifecycle.run second cs).1.last = some 1 ∧
    (Lifecycle.run second cs).2.map Lifecycle.Event.response =
      (Engine.run second.engine (cs.map (Lifecycle.project 1))).2.map (Lifecycle.tag (some 1)) :=
  Lifecycle.session_run second 1 cs (by decide) h
example : Lifecycle.Segment second [.begin 2 1,.process 0,.source .left FRPEngine.rejected,.process 1] := by
  simp [Lifecycle.Segment]
  decide

example (commands : Nat → Lifecycle.Command ℚ Nat) (i j : Nat) (h : i < j)
    (r r' : Lifecycle.Response ℚ Nat)
    (hi : (Lifecycle.event (Lifecycle.init FRPTrace.start) commands i).response = some r)
    (hj : (Lifecycle.event (Lifecycle.init FRPTrace.start) commands j).response = some r') : r'.id ≠ r.id :=
  Lifecycle.at_most_once _ commands h hi hj

example (commands : Nat → Lifecycle.Command ℚ Nat) (n : Nat)
    (r : Lifecycle.Response ℚ Nat)
    (h : (Lifecycle.event (Lifecycle.init FRPTrace.start) commands n).response = some r) :
    ∃ k, k < n ∧ commands k = .begin r.id r.time ∧
      (Lifecycle.event (Lifecycle.init FRPTrace.start) commands k).status = some .accepted :=
  Lifecycle.response_provenance FRPTrace.start commands n r h

example (commands : Nat → Lifecycle.Command ℚ Nat) :
    Monotone (fun n => Lifecycle.mark (Lifecycle.state (Lifecycle.init FRPTrace.start) commands n)) :=
  Lifecycle.marks_monotone _ commands

example (cs : List (Lifecycle.Command ℚ Nat)) :
    (Lifecycle.Pipeline.run wiredConsumer (Lifecycle.Pipeline.init FRPTrace.start wiredConsumer) cs).2 =
      (Lifecycle.Pipeline.run (batches wiredSpec) (Lifecycle.Pipeline.init FRPTrace.start (batches wiredSpec)) cs).2 ∧
    StateRel (Lifecycle.Pipeline.run wiredConsumer (Lifecycle.Pipeline.init FRPTrace.start wiredConsumer) cs).1.consumer
      (Lifecycle.Pipeline.run (batches wiredSpec) (Lifecycle.Pipeline.init FRPTrace.start (batches wiredSpec)) cs).1.consumer :=
  Lifecycle.Pipeline.run_consumer_related wiredConsumer (batches wiredSpec) StateRel
    (fun xs w s h => wired_step xs.sum xs.sum w s rfl h)
    (Lifecycle.init FRPTrace.start) _ _ wired_initial cs

example (cs : List (Lifecycle.Command ℚ Nat)) :
    Lifecycle.Pipeline.run jointConsumer (Lifecycle.Pipeline.init FRPTrace.start jointConsumer) cs =
      Lifecycle.Pipeline.run (batches jointSpec) (Lifecycle.Pipeline.init FRPTrace.start (batches jointSpec)) cs :=
  Lifecycle.Pipeline.compiled_run K sound jointSeed jointBody List.sum FRPTrace.start cs

example : normal =
    let a := Lifecycle.Pipeline.run jointConsumer (Lifecycle.Pipeline.init FRPTrace.start jointConsumer) first
    let b := Lifecycle.Pipeline.run jointConsumer a.1 secondCommands
    (b.1,a.2 ++ b.2) := Lifecycle.Pipeline.run_append _ _ _ _

/-- Source packets already retained by session zero satisfy advancement for
session one. No response equation appears in this delivery instance. -/
def commands : Nat → Lifecycle.Command ℚ Nat := fun _ => .process 1
def actions : Nat → Demand.Action ℚ
  | 0 => .register 2
  | _+1 => .process

def delivery : Trace.Delivery (Demand.sourceSchedule actions) where
  available := fun _ _ => 0
  monotone := fun _ _ _ _ => Nat.le_refl 0
  legal := by intro n source h; cases n <;> simp [Demand.sourceSchedule,actions] at h

theorem delivery_fair : delivery.Fair := by
  intro source n k h
  have hk : k = 0 := Nat.eq_zero_of_le_zero h
  subst k
  exact ⟨n,le_rfl,Nat.zero_le _⟩

theorem aligned : Engine.Aligned FRPTrace.stalled actions (Lifecycle.sessionCommands 1 2 commands) := by
  intro n
  cases n <;> simp [Lifecycle.sessionCommands,commands,Lifecycle.project,Engine.commandAt,actions]

theorem matching_fair : Lifecycle.ProcessingFair second commands 1 := by
  intro n time _ _ _
  exact ⟨n,le_rfl,rfl⟩

theorem second_eventually : ∃ n out, (Lifecycle.event second commands n).response = some ⟨1,2,out⟩ := by
  apply Lifecycle.eventual_response second commands 1 2 (by decide) (by decide)
    FRPTrace.stalled actions aligned delivery delivery_fair matching_fair
  intro source
  refine ⟨0,0,le_rfl,?_⟩
  cases source <;> decide

/-- Wrong-ID commands do not witness enabled processing fairness. -/
def wrong : Nat → Lifecycle.Command ℚ Nat := fun _ => .process 0
theorem wrong_stays (n : Nat) : Lifecycle.state second wrong n = second := by
  induction n with
  | zero => rfl
  | succ n ih => change (Lifecycle.step (Lifecycle.state second wrong n) (.process 0)).1 = second; rw [ih]; decide
example : ¬ Lifecycle.ProcessingFair second wrong 1 := by
  intro h
  obtain ⟨m,_,hm⟩ := h 0 2 (by decide) (by decide) ⟨[3,4,3],by decide⟩
  cases hm
example (n : Nat) : (Lifecycle.event second wrong n).response = none := by
  change (Lifecycle.step (Lifecycle.state second wrong n) (.process 0)).2.response = none
  rw [wrong_stays]; decide

def stalled : Lifecycle.State ℚ Nat := Lifecycle.registered (Lifecycle.init FRPTrace.start) 1 2
theorem stalled_stays (n : Nat) : Lifecycle.state stalled commands n = stalled := by
  induction n with
  | zero => rfl
  | succ n ih => change (Lifecycle.step (Lifecycle.state stalled commands n) (.process 1)).1 = stalled; rw [ih]; decide
example (n : Nat) : (Lifecycle.event stalled commands n).response = none := by
  change (Lifecycle.step (Lifecycle.state stalled commands n) (.process 1)).2.response = none
  rw [stalled_stays]; decide
example : Lifecycle.ProcessingFair stalled commands 1 := by
  intro n time _ _ _
  exact ⟨n,le_rfl,rfl⟩
example : ¬ (∀ source, ∃ k n, k ≤ delivery.available source n ∧
    (2:ℚ) < (Trace.sourcePrefix (stalled.engine.sources source) (FRPTrace.stalled source) k).frontier) := by
  intro h
  obtain ⟨k,n,hk,ht⟩ := h .left
  have hk' : k = 0 := Nat.eq_zero_of_le_zero hk
  subst k
  norm_num [Trace.sourcePrefix,stalled,Lifecycle.registered,Lifecycle.init,Engine.init,Engine.pack,
    Engine.MachineState.sources,FRPTrace.start,initial] at ht

end Examples.RequestLifecycle
