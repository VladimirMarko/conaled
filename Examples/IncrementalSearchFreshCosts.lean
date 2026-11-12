import Applications.Search.Incremental.FreshCosts
import Examples.IncrementalSearchSemantics

/-! Checked applications and public executable observations of the fresh-search
operation trace. Prices count logical scalar/cell calls, not elapsed time. -/
set_option autoImplicit false
set_option warningAsError true
namespace Examples.IncrementalSearchFreshCosts
open Search.Incremental
open IncrementalSearchSemantics

example : (FreshCosts.prepare disconnected heuristic).1 = Fresh.prepare disconnected heuristic :=
  FreshCosts.prepare_value _ _

example : (FreshCosts.result disconnected heuristic 0 1).1 = (2/7 : ℚ) := by
  rw [FreshCosts.result_value]
  exact distance_unique (Fresh.result_correct disconnected_positive heuristic_consistent 0)
    (bellman_correct disconnected_positive distances_nonnegative distances_bellman 1)

example : (FreshCosts.result disconnected (fun _ => 0) 0 2).1 = ⊤ := by
  rw [FreshCosts.result_value]
  exact distance_unique (Fresh.result_correct disconnected_positive
    (show ConsistentHeuristic disconnected 2 (fun _ => 0) by unfold ConsistentHeuristic; decide +kernel) 0)
    (bellman_correct disconnected_positive distances_nonnegative distances_bellman 2)

example : (FreshCosts.result ties tieHeuristic 0 3).1 = (11/15 : ℚ) := by
  rw [FreshCosts.result_value]
  exact distance_unique (Fresh.result_correct ties_positive tieHeuristic_consistent 0)
    (bellman_correct ties_positive tieDistances_nonnegative tieDistances_bellman 3)

/-- A separate query with different denominators really reconstructs its scale. -/
example : (FreshCosts.denominator [(1/2 : ℚ),1/3]).1 = 6 := by decide +kernel
example : (FreshCosts.denominator [(1/5 : ℚ),1/7]).1 = 35 := by decide +kernel
example : Accounting.bill Accounting.unitPrices (FreshCosts.denominator [(1/2 : ℚ),1/3]).2 = 18 := by
  decide +kernel

private def check {n : Nat} (name : String) (w : Graph n) (h : Fin n → ℚ)
    (start goal : Fin n) (expected : Cost) : IO Unit := do
  let measured := FreshCosts.result w h start goal
  let raw := Fresh.result w h start goal
  unless measured.1 == expected && raw == expected do
    throw (IO.userError (name ++ ": incorrect distance"))
  let events := measured.2
  unless events.contains .denominator && events.contains .multiply && events.contains .divide &&
      events.contains .compare && events.contains .allocate && events.contains .read do
    throw (IO.userError (name ++ ": missing exercised operation category"))
  IO.println s!"{name}: distance={repr measured.1}, unit bill={Accounting.bill Accounting.unitPrices events}"

def runtimeChecks : IO Unit := do
  check "fractional route" disconnected heuristic 0 1 (2/7 : ℚ)
  check "unreachable" disconnected (fun _ => 0) 0 2 ⊤
  check "start equals goal" disconnected (fun _ => 0) 0 0 (0 : ℚ)
  check "equal alternatives, nonzero heuristic" ties tieHeuristic 0 3 (11/15 : ℚ)

end Examples.IncrementalSearchFreshCosts
