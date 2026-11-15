import Applications.FRP.ExclusivePipeline
import Examples.RequestLifecycle

/-! Actual exclusive requests through a compiled count/total consumer. -/
namespace Examples.ExclusiveRequests
open FRPSpec.Frontier FRPSpec.Reactive Progress
open Exclusive
abbrev jointConsumer := batches jointMachine
abbrev wiredConsumer := batches wired

def first : List (Command ℚ Nat) :=
  [.begin 2,.source .left FRPEngine.leftPacket,.source .right FRPEngine.rightPacket,.process]
def again : List (Command ℚ Nat) := [.begin 2,.process]
def normal := Exclusive.Pipeline.run jointConsumer (Exclusive.Pipeline.init FRPTrace.start jointConsumer)
  (first ++ again)

example : normal.2 =
    [(⟨some .accepted,none⟩,none),(⟨none,none⟩,none),(⟨none,none⟩,none),
     (⟨none,some (2,[3,4,3])⟩,some (1,10)),(⟨some .accepted,none⟩,none),
     (⟨none,some (2,[3,4,3])⟩,some (2,20))] := by decide
example : normal.1.consumer = (2,20) := by decide
#eval (normal.2,normal.1.consumer)

def second : Exclusive.State ℚ Nat := (Exclusive.run (Exclusive.init FRPTrace.start)
  (first ++ [.begin 2])).1
example : second.request = .pending 2 := by decide
example : (step second .process).2.response = some (2,[3,4,3]) := by decide
example : step second (.begin 1) = (second,⟨some .busy,none⟩) :=
  begin_busy second 1 2 (by decide)
example : (step second (.source .left FRPEngine.rejected)).1 = second := by decide
example : (step (step second .process).1 .process).2.response = none := by decide
example : (step (step second .process).1 (.begin 2)).2.status = some .accepted := by decide

/-- The concrete second request is accepted again even at the same timestamp.
A purported retransmission filter would therefore change this contract. -/
example : (Exclusive.run (Exclusive.init FRPTrace.start) (first ++ again)).2.filterMap Event.response =
    [(2,[3,4,3]),(2,[3,4,3])] := by decide

/-- A stale targeted callback stutters in the identified reference, but generic
current work completes the new ready request. Arbitrary erasure is unsound. -/
example : (Lifecycle.step RequestLifecycle.second (.process 0)).2.response = none ∧
    (step second .process).2.response = some (2,[3,4,3]) := by decide

example : (Exclusive.Pipeline.run jointConsumer (Exclusive.Pipeline.init FRPTrace.start jointConsumer)
    [.begin 1,.process,.process,.begin 1,.process]).2 =
    [(⟨some .accepted,none⟩,none),(⟨none,some (1,[])⟩,some (1,0)),(⟨none,none⟩,none),
     (⟨some .accepted,none⟩,none),(⟨none,some (1,[])⟩,some (2,0))] := by decide

example (cs : List (Command ℚ Nat)) :
    (Exclusive.run (Exclusive.init FRPTrace.start) cs).1.Valid := by
  apply run_valid
  intro source
  cases source <;> simp [Exclusive.init,Engine.init,Engine.pack,Engine.MachineState.sources,
    FRPTrace.start,initial,FRPSpec.Frontier.State.Valid]

example (left right : ℚ → List Nat)
    (hl : (second.sources .left).Completes left) (hr : (second.sources .right).Completes right) :
    [3,4,3] = left 2 ++ right 2 :=
  response_sound (s := second) (c := .process) (by decide) left right hl hr

/-- Constructing the lift introduces labels 1 and 2, not runtime metadata. -/
example : (lift (Exclusive.init FRPTrace.start) 0 (first ++ again)).2 =
    [.begin 1 2,.source .left FRPEngine.leftPacket,.source .right FRPEngine.rightPacket,
      .process 1,.begin 2 2,.process 2] := by decide
example (cs : List (Command ℚ Nat)) :
    (Lifecycle.run (reference (Exclusive.init FRPTrace.start) 0)
      (lift (Exclusive.init FRPTrace.start) 0 cs).2).2.map erase =
        (Exclusive.run (Exclusive.init FRPTrace.start) cs).2 :=
  (run_refines _ 0 cs).2

example (commands : Nat → Command ℚ Nat) {i j : Nat} (h : i < j)
    (hi : (event (Exclusive.init FRPTrace.start) commands i).response = some (2,[3,4,3]))
    (hj : (event (Exclusive.init FRPTrace.start) commands j).response = some (2,[3,4,3])) :
    label (Exclusive.init FRPTrace.start) commands j ≠ label (Exclusive.init FRPTrace.start) commands i :=
  at_most_once _ commands h hi hj
example (commands : Nat → Command ℚ Nat) (n : Nat) (t : ℚ) (xs : List Nat)
    (h : (event (Exclusive.init FRPTrace.start) commands n).response = some (t,xs)) :
    ∃ k, k < n ∧ commands k = .begin t ∧
      (event (Exclusive.init FRPTrace.start) commands k).status = some .accepted ∧
      label (Exclusive.init FRPTrace.start) commands (k+1) = label (Exclusive.init FRPTrace.start) commands n :=
  response_provenance _ commands n t xs h

example (cs : List (Command ℚ Nat)) :
    (Exclusive.Pipeline.run wiredConsumer (Exclusive.Pipeline.init FRPTrace.start wiredConsumer) cs).2 =
      (Exclusive.Pipeline.run (batches wiredSpec) (Exclusive.Pipeline.init FRPTrace.start (batches wiredSpec)) cs).2 ∧
    StateRel (Exclusive.Pipeline.run wiredConsumer (Exclusive.Pipeline.init FRPTrace.start wiredConsumer) cs).1.consumer
      (Exclusive.Pipeline.run (batches wiredSpec) (Exclusive.Pipeline.init FRPTrace.start (batches wiredSpec)) cs).1.consumer :=
  Exclusive.Pipeline.run_consumer_related wiredConsumer (batches wiredSpec) StateRel
    (fun xs w s h => wired_step xs.sum xs.sum w s rfl h)
    (Exclusive.init FRPTrace.start) _ _ wired_initial cs
example (cs : List (Command ℚ Nat)) :
    Exclusive.Pipeline.run jointConsumer (Exclusive.Pipeline.init FRPTrace.start jointConsumer) cs =
      Exclusive.Pipeline.run (batches jointSpec) (Exclusive.Pipeline.init FRPTrace.start (batches jointSpec)) cs :=
  Exclusive.Pipeline.compiled_run K sound jointSeed jointBody List.sum FRPTrace.start cs
example : normal =
    let a := Exclusive.Pipeline.run jointConsumer (Exclusive.Pipeline.init FRPTrace.start jointConsumer) first
    let b := Exclusive.Pipeline.run jointConsumer a.1 again
    (b.1,a.2 ++ b.2) := Exclusive.Pipeline.run_append _ _ _ _

/-- No new packets are needed to answer the retained second request. -/
def commands : Nat → Command ℚ Nat := fun _ => .process
example : Engine.Aligned FRPTrace.stalled RequestLifecycle.actions (sessionCommands 2 commands) := by
  intro n
  cases n <;> simp [sessionCommands,commands,project,Engine.commandAt,RequestLifecycle.actions]
theorem processing_fair : ProcessingFair second commands := by
  intro n t _ _; exact ⟨n,le_rfl,rfl⟩
theorem second_eventually : ∃ n out, (event second commands n).response = some (2,out) := by
  apply eventual_response second commands 2 (by decide) FRPTrace.stalled RequestLifecycle.actions
    (by intro n; cases n <;> simp [sessionCommands,commands,project,Engine.commandAt,RequestLifecycle.actions])
    RequestLifecycle.delivery RequestLifecycle.delivery_fair processing_fair
  intro source; refine ⟨0,0,le_rfl,?_⟩
  cases source <;> decide

/-- Source starvation remains possible even when process is always scheduled. -/
def stalled : Exclusive.State ℚ Nat := (step (Exclusive.init FRPTrace.start) (.begin 2)).1
theorem stalled_stays (n : Nat) : state stalled commands n = stalled := by
  induction n with
  | zero => rfl
  | succ n ih => change (step (state stalled commands n) .process).1 = stalled; rw [ih]; decide
example (n : Nat) : (event stalled commands n).response = none := by
  change (step (state stalled commands n) .process).2.response = none
  rw [stalled_stays]; decide
example : ProcessingFair stalled commands := by
  intro n t _ _; exact ⟨n,le_rfl,rfl⟩
example : ¬ (∀ source, ∃ k n, k ≤ RequestLifecycle.delivery.available source n ∧
    (2:ℚ) < (Trace.sourcePrefix (stalled.sources source) (FRPTrace.stalled source) k).frontier) := by
  intro h
  obtain ⟨k,n,hk,ht⟩ := h .left
  have hk' : k = 0 := Nat.eq_zero_of_le_zero hk
  subst k
  norm_num [Trace.sourcePrefix,stalled,step,Exclusive.init,Engine.init,Engine.pack,
    Engine.MachineState.sources,FRPTrace.start,initial] at ht

def idle : Nat → Command ℚ Nat := fun _ => .idle
theorem idle_stays (n : Nat) : state second idle n = second := by
  induction n with
  | zero => rfl
  | succ n ih => change (step (state second idle n) .idle).1 = second; rw [ih]; decide
example : ¬ ProcessingFair second idle := by
  intro h
  obtain ⟨m,_,hm⟩ := h 0 2 (by decide) ⟨[3,4,3],by decide⟩
  cases hm
example (n : Nat) : (event second idle n).response = none := by
  change (step (state second idle n) .idle).2.response = none
  rw [idle_stays]; decide

/-- Even empty responses can grow a natural-number consumer without bound. -/
def emptyDone : Exclusive.State ℚ Nat :=
  (Exclusive.run (Exclusive.init FRPTrace.start) [.begin 1,.process]).1

theorem empty_cycle (n : Nat) :
    (Exclusive.Pipeline.run jointConsumer ⟨emptyDone,(n,0)⟩ [.begin 1,.process]).1 =
      ⟨emptyDone,(n+1,0)⟩ := by rfl

def emptyCycles : Nat → List (Command ℚ Nat)
  | 0 => []
  | n+1 => emptyCycles n ++ [.begin 1,.process]

theorem empty_count (n : Nat) :
    (Exclusive.Pipeline.run jointConsumer ⟨emptyDone,(0,0)⟩ (emptyCycles n)).1 =
      ⟨emptyDone,(n,0)⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [emptyCycles,Exclusive.Pipeline.run_append,ih]
    exact empty_cycle n

end Examples.ExclusiveRequests
