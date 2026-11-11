import Applications.FRP.BoundedFoldAdmission

/-! Frozen parity oracle and capacity/resource separating cases. -/
namespace FRPSpec.BoundedFold
open Progress.Feedback

def fixtures : List (Batch 3) :=
  [⟨[true,false],by decide⟩,⟨[],by decide⟩,⟨[true,true,true],by decide⟩,
    ⟨[false,true],by decide⟩]

/-- Literal result calculated before compiling the client. -/
theorem fixture : run (machine 3).mealy false fixtures = ([false,true,true,false],true) := by
  rw [run_correct]
  rfl

example : run (machine 0).mealy true [⟨[],by decide⟩] = ([true],true) := by
  rw [run_correct]
  rfl

example : (assess 3 true (.bounded (storage 3))).status = .accepted := by decide
example : (assess 3 true (.bounded (storage 3-1))).status = .rejected := by decide
example : (assess 3 false (.bounded (storage 3))).status = .unsupported := rfl
example : (assess 3 true (.bounded (storage 3))).run fixtures =
    some ([false,true,true,false],true) := by decide

example : ingest 0 [true] = none := rfl
example : (ingest 3 [true,false,true]).map Subtype.val = some [true,false,true] := rfl
example : ingest 3 [true,false,true,false] = none := rfl

example : run (Regional.machine 3).mealy (false,true) fixtures =
    ([true,false,false,true],(true,false)) := by
  rw [Regional.run_correct]
  rfl

/-- Arbitrary continuations use the actual current state. -/
example (s : Bool) (before after : List (Batch capacity)) :
    run (machine capacity).mealy (run (machine capacity).mealy s before).2 after =
      run (native capacity).mealy (run (native capacity).mealy s before).2 after :=
  continuation s before after

end FRPSpec.BoundedFold
