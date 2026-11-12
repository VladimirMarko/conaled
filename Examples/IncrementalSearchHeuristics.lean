import Examples.IncrementalSearchSemantics
import Applications.Search.Incremental.Patches

/-! Positive self-loops, tied routes, and final-graph heuristic admission. -/
set_option autoImplicit false
set_option warningAsError true
namespace Examples.IncrementalSearchHeuristics
open Search.Incremental Examples.IncrementalSearchSemantics

def tied : Session 4 0 3 tieHeuristic :=
  Session.begin ties ties_positive 0 3 tieHeuristic tieHeuristic_consistent
example : tied.observe = (11/15 : ℚ) := by decide +kernel

def blockOne : Batch 4 := [⟨0,1,⊤⟩]
theorem blockOne_positive : PositiveBatch blockOne := by norm_num [PositiveBatch, blockOne]
theorem blockOne_heuristic : ConsistentHeuristic (applyBatch ties blockOne) 3 tieHeuristic := by
  unfold ConsistentHeuristic; decide +kernel
def alternate := tied.advance blockOne blockOne_positive blockOne_heuristic
example : alternate.observe = (11/15 : ℚ) := by decide +kernel

/-- An inadmissible intermediate graph is allowed inside an ordered batch. -/
def transient : Batch 4 := [⟨0,1,(1/100 : ℚ)⟩,⟨0,1,(1/3 : ℚ)⟩]
theorem transient_positive : PositiveBatch transient := by norm_num [PositiveBatch, transient]
example : ¬ ConsistentHeuristic (assign ties ⟨0,1,(1/100 : ℚ)⟩) 3 tieHeuristic := by
  unfold ConsistentHeuristic; decide +kernel
theorem transient_heuristic : ConsistentHeuristic (applyBatch ties transient) 3 tieHeuristic := by
  unfold ConsistentHeuristic; decide +kernel
def restoredTie := tied.advance transient transient_positive transient_heuristic
example : restoredTie.observe = (11/15 : ℚ) := by decide +kernel

/-- Positive loops do not change the zero-length start-to-start optimum. -/
def sameEndpoint := Session.begin disconnected disconnected_positive 0 0 (fun _ => 0)
  (zero_heuristic disconnected_positive 0)
example : sameEndpoint.observe = 0 := by decide +kernel

end Examples.IncrementalSearchHeuristics
