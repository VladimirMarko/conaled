import Examples.IncrementalSearchFreshCosts
import Examples.IncrementalSearchHeuristics
import Examples.IncrementalSearchUpdates
import Examples.IncrementalSearchCosts

private def check (name : String) (ok : Bool) : IO Unit :=
  unless ok do throw (IO.userError name)

open Search.Incremental Examples.IncrementalSearchUpdates

def main : IO Unit := do
  check "increased cost repairs retained result" (decide (increased.observe = 2))
  check "initial rational shortest distance" (decide (started.observe = (5/6 : ℚ)))
  check "new denominator survives decrease" (decide (decreased.observe = (9/14 : ℚ)))
  check "blocked routes report unreachable" (decide (lost.observe = ⊤))
  check "ordered last assignment restores reachability" (decide (restored.observe = (2/11 : ℚ)))
  check "empty batch retains result" (decide ((advanceZero restored [] (by simp [PositiveBatch])).observe = (2/11 : ℚ)))
  check "early stop observes cheap goal" (decide (early.observe = 1))
  let reuse := Examples.IncrementalSearchCosts.reused
  let rerun := Examples.IncrementalSearchCosts.rerun
  check "measured repair and fresh query observe same distance" (decide (reuse.1.2 = 1 ∧ rerun.1 = 1))
  check "bounded repair bill" (decide (Accounting.bill Accounting.unitPrices reuse.2 = 110))
  check "bounded rerun bill includes patch" (decide (Accounting.bill Accounting.unitPrices rerun.2 = 559))
  check "adverse repair can cost more" (decide
    (Accounting.bill Accounting.unitPrices Examples.IncrementalSearchCosts.invalidated.2 = 641 ∧
     Accounting.bill Accounting.unitPrices Examples.IncrementalSearchCosts.adverseRerun.2 = 429))
  check "tied routes with nonzero heuristic" (decide
    (Examples.IncrementalSearchHeuristics.alternate.observe = (11/15 : ℚ)))
  check "only final graph must admit heuristic" (decide
    (Examples.IncrementalSearchHeuristics.restoredTie.observe = (11/15 : ℚ)))
  check "positive self-loops and start equals goal" (decide
    (Examples.IncrementalSearchHeuristics.sameEndpoint.observe = 0))
  Examples.IncrementalSearchSemantics.runtimeChecks
  Examples.IncrementalSearchFreshCosts.runtimeChecks
  IO.println "incremental search runtime checks passed"
