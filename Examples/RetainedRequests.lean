import Applications.FRP.RetainedPipeline
import Applications.FRP.RetainedResource
import Examples.RequestLifecycle

/-! Literal request/consumer expectations and retention failure controls. -/
namespace Examples.RetainedRequests
open FRPSpec.Frontier FRPSpec.Reactive Progress
open Retention
abbrev consumer := batches jointMachine

def sources : Trace.Inputs Nat Nat
  | .left => ⟨4,[(1,[99]),(2,[3]),(2,[4])]⟩
  | .right => ⟨4,[(2,[3])]⟩
def commands : List (Retention.Command Nat Nat) :=
  [.advanceLower 2,.native (.begin 1 2),.native (.process 1),
   .native (.begin 2 2),.native (.process 2),.native (.begin 3 1)]
def result := Retention.Pipeline.run consumer (Retention.Pipeline.init 0 sources consumer) commands

example : result.2 =
    [(⟨some .advanced,⟨none,none⟩⟩,none),
     (⟨none,⟨some .accepted,none⟩⟩,none),
     (⟨none,⟨none,some ⟨1,2,[3,4,3]⟩⟩⟩,some (1,10)),
     (⟨none,⟨some .accepted,none⟩⟩,none),
     (⟨none,⟨none,some ⟨2,2,[3,4,3]⟩⟩⟩,some (2,20)),
     (⟨some .outsideRetention,⟨none,none⟩⟩,none)] := by decide
example : result.1.consumer = (2,20) := by decide
example : result.1.retained.machine.engine.left.log = [(2,[3]),(2,[4])] := by decide
example : result.1.retained.machine.last = some 2 := by decide

example (cs : List (Retention.Command Nat Nat)) :
    Retention.Pipeline.run consumer (Retention.Pipeline.init 0 sources consumer) cs =
      Retention.Pipeline.run (batches jointSpec)
        (Retention.Pipeline.init 0 sources (batches jointSpec)) cs :=
  Retention.Pipeline.compiled_run K sound jointSeed jointBody List.sum 0 sources cs

example (cs : List (Retention.Command Nat Nat)) :
    (Retention.Pipeline.run consumer (Retention.Pipeline.init 0 sources consumer) cs).1.consumer =
      (Lifecycle.Pipeline.run consumer (Lifecycle.Pipeline.init sources consumer)
        (Retention.projected (Retention.init 0 sources) cs)).1.consumer :=
  (Retention.Pipeline.consumer_refines consumer _ _ _ (init_related 0 sources) cs).1

def pending := (Retention.step (Retention.init 0 sources) (.native (.begin 7 2))).1
example : Retention.step pending (.advanceLower 3) =
    (pending,⟨some .pendingConflict,⟨none,none⟩⟩) := by decide
example : (Retention.step pending (.advanceLower 2)).1.machine.engine.request = .pending 2 := by decide
example : (Retention.step (Retention.step pending (.advanceLower 2)).1 (.native (.process 7))).2.native.response =
    some ⟨7,2,[3,4,3]⟩ := by decide
example : (Retention.step (Retention.init 2 sources) (.advanceLower 1)).2.notice = some .decreasing := by decide

/-- A lower bound ahead of the frontier also filters future accepted packets. -/
def future : Retention.State Nat Nat := Retention.init 5 (fun _ => initial 0)
def spanning : Trace.Message Nat Nat := ⟨7,[(2,[9]),(5,[8]),(6,[7])]⟩
example : (Retention.step future (.native (.source .left spanning))).1.machine.engine.left =
    ⟨7,[(5,[8]),(6,[7])]⟩ := by decide
example : (Retention.step future (.native (.source .left ⟨7,[(8,[9])]⟩))).1 = future := by decide

/-- Advancing an upper frontier does not remove old historical queries. -/
def fullAdvanced : FRPSpec.Frontier.State Nat Nat := Trace.process (sources .left) ⟨9,[]⟩
example : fullAdvanced.frontier = 9 ∧ batch fullAdvanced.log 1 = [99] ∧
    batch (crop 2 fullAdvanced).log 1 = [] := by decide
example : (Retention.step (Retention.init 2 sources) (.native (.begin 1 1))).2.native.response = none := by decide

example : Resource.Window 2 2 (sources .left |>.log |> cropLog 2) := by
  intro x hx
  simp [sources,cropLog] at hx
  rcases hx with rfl | rfl <;> decide
example : Resource.Density 2 (sources .left |>.log |> cropLog 2) := by
  intro t
  by_cases h : t=2
  · subst t; decide
  · simp [Resource.atTime,sources,cropLog,Ne.symm h]
example : (cropLog 2 (sources .left).log).length ≤ 2*2 :=
  Resource.retained_length 2 2 2 _
    (by intro x hx; simp [sources,cropLog] at hx; rcases hx with rfl | rfl <;> decide)
    (by intro t; by_cases h : t=2; subst t; decide; simp [Resource.atTime,sources,cropLog,Ne.symm h])
example (n : Nat) : Resource.Window 0 1 (List.replicate n (0,([] : List Nat))) ∧
    (List.replicate n (0,([] : List Nat))).length = n := Resource.unbounded_density n

example : Resource.logCost (fun _ => 2) id 1 1 [(2,[3]),(2,[4])] ≤ 32 := by
  apply Resource.encoded_bound 2 2 2 1 2 4 1 1
  · intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl <;> decide
  · intro t
    by_cases h : t=2
    · subst t; decide
    · simp [Resource.atTime,Ne.symm h]
  · intro x hx; exact le_rfl
  · intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl <;> decide
  · intro x hx a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl <;> simp_all

example (n : Nat) : Resource.logCost (fun _ => 1) id 1 1 [(0,[n])] = n+3 :=
  Resource.growing_payload n
example (q : Nat) : Resource.Window q 1 [(q,([] : List Nat))] ∧
    Resource.logCost id id 1 1 [(q,([] : List Nat))] = q+1 :=
  Resource.growing_timestamp q

#eval (result.2,result.1.consumer,result.1.retained.machine.engine.left.log)
end Examples.RetainedRequests
