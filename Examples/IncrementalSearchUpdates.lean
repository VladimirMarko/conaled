import Applications.Search.Incremental.Interpretation
import Examples.IncrementalSearch

/-! Retained-state updates, calculated independently from the three-edge graph. -/
set_option autoImplicit false
set_option warningAsError true
namespace Examples.IncrementalSearchUpdates
open Search.Incremental Examples.IncrementalSearch

theorem triangle_positive : Positive triangle := by unfold Positive; decide +kernel

def started : Session 3 0 2 (fun _ => 0) := Session.begin triangle triangle_positive 0 2 (fun _ => 0)
  (zero_heuristic triangle_positive 2)

example : started.observe = (5/6 : ℚ) := by decide +kernel

def advanceZero (p : Session 3 0 2 (fun _ => 0)) (es : Batch 3) (hp : PositiveBatch es) : Session 3 0 2 (fun _ => 0) :=
  p.advance es hp (zero_heuristic (applyBatch_positive p.graph p.positive es hp) 2)

def decreased : Session 3 0 2 (fun _ => 0) := advanceZero started [⟨1,2,(1/7 : ℚ)⟩] (by norm_num [PositiveBatch])
example : decreased.observe = (9/14 : ℚ) := by decide +kernel

def increased : Session 3 0 2 (fun _ => 0) := advanceZero decreased [⟨1,2,3⟩] (by norm_num [PositiveBatch])
example : increased.observe = 2 := by decide +kernel

def lost : Session 3 0 2 (fun _ => 0) := advanceZero increased [⟨0,1,⊤⟩,⟨0,2,⊤⟩] (by norm_num [PositiveBatch])
example : lost.observe = ⊤ := by decide +kernel

/-- Last write wins, restoring a route with a denominator absent at initialization. -/
def restored : Session 3 0 2 (fun _ => 0) := advanceZero lost [⟨0,2,5⟩,⟨0,2,(2/11 : ℚ)⟩] (by norm_num [PositiveBatch])
example : restored.observe = (2/11 : ℚ) := by decide +kernel

example : (advanceZero restored [] (by simp [PositiveBatch])).observe = (2/11 : ℚ) := by decide +kernel

/-- The actual public update receives the universal independent-distance theorem. -/
theorem restored_correct : DistanceResult restored.graph 0 2 (restored.observe) :=
  Session.advance_correct lost _ _ _

def earlyGraph : Graph 4 := fun u v =>
  if u = 0 ∧ v = 1 then 1 else if u = 0 ∧ v = 2 then 10 else if u = 2 ∧ v = 3 then 1 else ⊤
theorem early_positive : Positive earlyGraph := by unfold Positive; decide +kernel

def early : Session 4 0 1 (fun _ => 0) := Session.begin earlyGraph early_positive 0 1 (fun _ => 0)
  (zero_heuristic early_positive 1)

/-- Goal1 is settled while vertex2 remains inconsistent and queued. -/
example : early.observe = 1 ∧ early.state.g 2 = ⊤ ∧ early.state.rhs 2 = 10 ∧ 2 ∈ early.state.queue := by
  decide +kernel

end Examples.IncrementalSearchUpdates
