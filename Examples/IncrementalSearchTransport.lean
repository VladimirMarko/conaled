import Applications.Search.Incremental.Transport
import Examples.IncrementalSearchUpdates

/-! Migration keeps the residual inconsistent vertex, followed by loss and
restoration of reachability. A separate fork graph exposes enumeration ties. -/
set_option autoImplicit false
set_option warningAsError true
namespace Examples.IncrementalSearchTransport
open Search.Incremental
open Search.Incremental.Transport
open Examples.IncrementalSearchUpdates

def swap : Relabel 4 := Equiv.swap 1 2

def migrated := session swap early

/-- All cached coordinates and the entire queue survive the switch. -/
example : migrated.observe = 1 ∧ migrated.state.g 1 = ⊤ ∧
    migrated.state.rhs 1 = 10 ∧ migrated.state.queue = [1] := by decide +kernel

example : state swap.symm migrated.state = early.state := state_inverse swap early.state

example : Valid migrated.graph (swap 0) migrated.state := valid swap early.valid

example : DistanceResult (graph swap earlyGraph) (swap 0) (swap 1) migrated.observe :=
  begin_correct swap earlyGraph early_positive 0 1 (fun _ => 0) (zero_heuristic early_positive 1)

def remove : Batch 4 := [⟨0,1,⊤⟩]
def restore : Batch 4 := [⟨0,1,5⟩, ⟨0,1,(2/11 : ℚ)⟩]
theorem remove_positive : PositiveBatch remove := by norm_num [remove, PositiveBatch]
theorem restore_positive : PositiveBatch restore := by norm_num [restore, PositiveBatch]

def removed := advance swap early remove remove_positive
  (zero_heuristic (applyBatch_positive early.graph early.positive remove remove_positive) 1)

def resumed := removed.advance (batch swap restore) (positiveBatch swap restore_positive)
  (zero_heuristic (applyBatch_positive removed.graph removed.positive
    (batch swap restore) (positiveBatch swap restore_positive)) (swap 1))

example : removed.observe = ⊤ := by decide +kernel
example : resumed.observe = (2/11 : ℚ) := by decide +kernel

/-- The second repair consumes the first repair's retained labels and queue. -/
example : DistanceResult resumed.graph (swap 0) (swap 1) resumed.observe :=
  Session.advance_correct removed _ _ _

example : DistanceResult (graph swap (applyBatch early.graph remove))
    (swap 0) (swap 1) removed.observe := advance_correct swap early _ _ _

example : batch swap restore = [⟨0,2,5⟩, ⟨0,2,(2/11 : ℚ)⟩] := rfl

/-- Native successor enumeration commutes for this sparse graph, although the
vertex permutation itself does not preserve the total vertex order. -/
def chain : Graph 4 := fun u v => if u = 0 ∧ v = 1 then 1 else if u = 1 ∧ v = 3 then 2 else ⊤
theorem chain_ordered : Ordered swap chain := by unfold Ordered; decide +kernel

def chainState : State 4 := initial 0

example : run (graph swap chain) (swap 0) (swap 3) (heuristic swap (fun _ => 0))
    8 (state swap chainState) = outcome swap (run chain 0 3 (fun _ => 0) 8 chainState) :=
  run_map swap chain chain_ordered 0 3 (fun _ => 0) 8 chainState

/-- Both successors have equal keys. Native enumeration visits 1 before 2,
while mapping the source queue places 2 before 1. -/
def forkGraph : Graph 4 := fun u v => if u = 0 ∧ (v = 1 ∨ v = 2) then 1 else ⊤
def sourceFork : State 4 := expand forkGraph 0 (initial 0) 0
def targetFork : State 4 := expand (graph swap forkGraph) (swap 0) (state swap (initial 0)) (swap 0)

example : (state swap sourceFork).queue = [2,1] ∧ targetFork.queue = [1,2] := by decide +kernel
example : select (fun _ => 0) (state swap sourceFork) = some 2 ∧
    select (fun _ => 0) targetFork = some 1 := by decide +kernel
example : ¬ Ordered swap forkGraph := by unfold Ordered; decide +kernel

theorem fork_positive : Positive forkGraph := by unfold Positive; decide +kernel

def forkSource := Session.begin forkGraph fork_positive 0 1 (fun _ => 0)
  (zero_heuristic fork_positive 1)
def forkTarget := Session.begin (graph swap forkGraph) (positive swap fork_positive)
  (swap 0) (swap 1) (heuristic swap (fun _ => 0))
  (consistent swap (zero_heuristic fork_positive 1))

/-- Equal distances do not imply equal non-goal cached labels after native
execution: the target processes the other tied vertex before reaching its goal. -/
example : (session swap forkSource).observe = forkTarget.observe ∧
    (session swap forkSource).state.g 1 = ⊤ ∧ forkTarget.state.g 1 = 1 := by decide +kernel

/-- First-tie selection itself commutes when the ordered queue is transported. -/
example : select (heuristic swap (fun _ => 0)) (state swap sourceFork) =
    (select (fun _ => 0) sourceFork).map swap := select_map swap (fun _ => 0) sourceFork

example : ((stateAdapter swap).forward early.state).1 = migrated.state := rfl
example : ((stateAdapter swap).backward migrated.state).1 = early.state :=
  state_inverse swap early.state

theorem chain_positive : Positive chain := by unfold Positive; decide +kernel

def chainBegin : Session 4 0 3 (fun _ => 0) := Session.begin chain chain_positive 0 3
  (fun _ => 0) (zero_heuristic chain_positive 3)
def chainRemove : Batch 4 := [⟨1,3,⊤⟩]
def chainRestore : Batch 4 := [⟨1,3,5⟩, ⟨1,3,2⟩]
theorem chainRemove_positive : PositiveBatch chainRemove := by norm_num [chainRemove, PositiveBatch]
theorem chainRestore_positive : PositiveBatch chainRestore := by norm_num [chainRestore, PositiveBatch]

def chainLost := chainBegin.advance chainRemove chainRemove_positive
  (zero_heuristic (applyBatch_positive chainBegin.graph chainBegin.positive _ chainRemove_positive) 3)
def chainBack := chainLost.advance chainRestore chainRestore_positive
  (zero_heuristic (applyBatch_positive chainLost.graph chainLost.positive _ chainRestore_positive) 3)

theorem chain_history : History chainBegin [chainBegin, chainLost, chainBack] :=
  .cons chainBegin chainRemove chainRemove_positive _
    (.cons chainLost chainRestore chainRestore_positive _ (.nil chainBack))

theorem chain_history_ordered :
    ∀ q ∈ [chainBegin, chainLost, chainBack], Ordered swap q.graph := by
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl <;> unfold Ordered <;> decide +kernel

/-- This is a history of native target repairs, not merely mapped observations. -/
example : History (session swap chainBegin)
    [session swap chainBegin, session swap chainLost, session swap chainBack] :=
  history_map swap chain_history chain_history_ordered

example : ∀ q ∈ [chainBegin, chainLost, chainBack],
    DistanceResult q.graph 0 3 q.observe :=
  history_correct chain_history (Session.begin_correct _ _ _ _ _ _)

example : [chainBegin.observe, chainLost.observe, chainBack.observe] = [3, ⊤, 3] := by decide +kernel

/-- The shared square and direct route use the same transported native input. -/
def repairInput : RepairInput 4 0 1 (fun _ => 0) :=
  ⟨early.graph, early.positive, early.state, early.valid, remove, remove_positive,
    zero_heuristic (applyBatch_positive early.graph early.positive remove remove_positive) 1⟩
example : DistanceResult (graph swap (applyBatch early.graph remove)) (swap 0) (swap 1)
    ((repairDistanceSquare 4 (swap 0) (swap 1) (heuristic swap (fun _ => 0))).impl
      (input swap repairInput)).2 := square_correct swap repairInput

example : (advance swap early remove remove_positive repairInput.final_heuristic).observe =
    (early.advance remove remove_positive repairInput.final_heuristic).observe :=
  advance_observe swap early remove remove_positive repairInput.final_heuristic

end Examples.IncrementalSearchTransport
