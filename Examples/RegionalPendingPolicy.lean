import Applications.FRP.RegionalPendingPolicy

/-! Policy selects concrete pending executors. Transition admission remains
separate from both static and measured ordering. -/
namespace Examples.RegionalPendingPolicy
open FRPSpec.Regional FRPSpec.Regional.Pending

def sampleCatalog : List Candidate := [⟨.split,.delay⟩,⟨.fused,.delay⟩,⟨.checked,.redundant⟩]
def ctx := policyContext {} "pending-measured" sampleCatalog
def evidence : Optimization.Choice.Epoch :=
  ⟨ctx,1,sampleCatalog.map fun c => ⟨c.name,0,if c.cut == .checked then 0 else 100,true,ctx⟩⟩

example : (FRPSpec.Regional.Selection.validateEpoch evidence ctx).1 = true := by decide
example : (preparedTarget (propose (initial .split) {} "pending-measured" (some evidence) sampleCatalog).session).map
    (fun target => target.cut) = some .checked := by decide

/-- Target steady capacity alone cannot discard the old executor's requirement.
Here transfer scratch is smaller than the producer arena; old checked storage
is the discriminating term, rather than an invented migration-space penalty. -/
example : serviceCapacity .fused = 441 ∧ serviceCapacity .checked = 445 := by decide
example : (⟨Cut.fused,FRPSpec.Migration.Kind.delay⟩ : Candidate).eligible ⟨441,2,true,true⟩ := by decide
example : (propose (initial .checked) ⟨441,2,true,true⟩ "capacity-separator" none
    [⟨.fused,.delay⟩]).status = .capacity := by decide

example : (FRPSpec.Regional.Selection.validateEpoch evidence
    (policyContext {} "different-workload" sampleCatalog)).1 = false := by decide
example (candidate : Candidate) : candidateScore (some evidence) false candidate =
    (candidate.staticWork,[.rank 1]) := rfl

end Examples.RegionalPendingPolicy
