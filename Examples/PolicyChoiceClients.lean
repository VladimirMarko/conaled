import Applications.Parallel.PolicyChoice
import Applications.Sequences.LCA.PolicyChoice
import Examples.ScanSearch
import Examples.LCATree
import Examples.RealizationChoice

namespace Examples.PolicyChoiceClients
open Optimization.Choice Applications.Parallel

def context : Context := ⟨"synthetic-v1", "test", "fixture", "root", "one-total", [], []⟩

/-- Two explicit exploration observations; this is synthetic evidence, not timing. -/
def training (ctx : Context) (first second : String) : Option Epoch :=
  (do
    let epoch ← (Epoch.start ctx 1).record ctx ⟨first,0,20,true⟩
    epoch.record ctx ⟨second,0,10,true⟩).toOption

namespace Scan
open Examples.ScanSearch

def catalog := [coarseA,coarseB]
def scope := PolicyChoice.scope appendLeaf 9 none context
def ctx := admittedContext catalog (PolicyChoice.admitted appendLeaf 9 none) PolicyChoice.identify scope
def evidence := training ctx (PolicyChoice.identify coarseA) (PolicyChoice.identify coarseB)

example : PolicyChoice.choose catalog appendLeaf 9 none context 1 (fun _ => 0) none = some coarseA := by decide
example : PolicyChoice.choose catalog appendLeaf 9 none context 1 (fun _ => 0) evidence = some coarseB := by decide
example : PolicyChoice.choose catalog appendLeaf 9 (some 4) context 1 (fun _ => 0) none = some coarseB := by decide
example : PolicyChoice.choose catalog appendLeaf 9 (some 3) context 1 (fun _ => 0) evidence = none := by decide

/-- The policy law reaches the whole enclosing computation for every input and
monoid. No commutativity is assumed. -/
theorem trained_correct {M : Type*} [Monoid M] (xs : List M) (hx : xs.length = 9) :
    PolicyChoice.run (.prod coarseB .leaf) xs = sequential 1 xs :=
  PolicyChoice.chosen_correct (by decide :
    PolicyChoice.choose catalog appendLeaf 9 none context 1 (fun _ => 0) evidence = some coarseB) xs hx

example : PolicyChoice.run (.prod coarseB .leaf) (["a","b","c","d","e","f","g","h","i"].map FreeMonoid.of : List (FreeMonoid String)) =
    sequential 1 (["a","b","c","d","e","f","g","h","i"].map FreeMonoid.of : List (FreeMonoid String)) := by
  apply trained_correct
  rfl
end Scan

namespace Tree
open Sequences.LCA Sequences.LCA.TreeReduction
open LCATree

def req : Resources.Prepared.Requirements := ⟨none,1000,0,100000,100000⟩
def fixed := PolicyChoice.modeledTotal (tourSize 4) 1
def ctx := admittedContext PolicyChoice.catalog (fun c => Resources.Prepared.Feasible req
    (PolicyChoice.treeProfile 4 c) starSource) PolicyChoice.identify
    (PolicyChoice.scope 4 req {context with site := context.site ++ ":tree"})
def evidence := training ctx "direct" "sparse"

example : PolicyChoice.chooseTree req starSource context 1 fixed none = some .direct := by decide
example : PolicyChoice.chooseTree req starSource context 1 fixed evidence = some .sparse := by decide
example : (PolicyChoice.treeService .sparse starSource [siblingQuery]).1 = [0] := by
  rw [PolicyChoice.treeChosen_correct (by decide :
    PolicyChoice.chooseTree req starSource context 1 fixed evidence = some .sparse)]
  rfl
example : ((PolicyChoice.treeOps 4 .sparse).answer
    ((PolicyChoice.treeOps 4 .sparse).prepare starSource).1 siblingQuery).2 ≤ req.deadline :=
  PolicyChoice.treeChosen_query_bound (by decide :
    PolicyChoice.chooseTree req starSource context 1 fixed evidence = some .sparse) siblingQuery
end Tree
end Examples.PolicyChoiceClients
