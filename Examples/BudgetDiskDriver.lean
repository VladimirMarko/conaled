import Applications.Orbifold.Driver.Protocol
import Applications.Orbifold.Driver.Timing
import Examples.NumericalMotion

/-! Checked command-level clients: the driver chooses ticks and acquires its own
success evidence. Literal budget expectations predate this implementation. -/
namespace Examples.BudgetDiskDriver
open Orbifold.DiskTransport Orbifold.DiskTransport.Numerical
open Orbifold.DiskTransport.Numerical.Driver

def refinement : Request :=
  ⟨[.command NumericalMotion.moveTick],1/32768,128,⟨4,16384⟩⟩
def word : Request :=
  ⟨[.command NumericalMotion.moveTick,.command NumericalMotion.turnTick,
    .command NumericalMotion.moveTick],1/8192,128,⟨4,16384⟩⟩
def relabeledWord : Request :=
  ⟨[.command NumericalMotion.moveTick,.relabel ⟨1,by decide⟩,
    .command NumericalMotion.turnTick,.command NumericalMotion.moveTick],1/8192,128,⟨4,16384⟩⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem refinement_success : (runRequest refinement).failure = none := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem word_success : (runRequest word).failure = none := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem relabeled_success : (runRequest relabeledWord).failure = none := by decide +kernel

theorem refinement_sound :
    Approx (runRequest refinement).final (executeEvents refinement.events Driver.initialPose) ∧
    TraceSound Driver.initialPose (runRequest refinement).observations ∧
    (runRequest refinement).final.error ≤ 1/32768 :=
  request_success refinement refinement_success

theorem word_sound :
    Approx (runRequest word).final (executeEvents word.events Driver.initialPose) ∧
    TraceSound Driver.initialPose (runRequest word).observations ∧
    (runRequest word).final.error ≤ 1/8192 :=
  request_success word word_success

theorem relabeled_sound :
    Approx (runRequest relabeledWord).final (executeEvents relabeledWord.events Driver.initialPose) ∧
    TraceSound Driver.initialPose (runRequest relabeledWord).observations ∧
    (runRequest relabeledWord).final.error ≤ 1/8192 :=
  request_success relabeledWord relabeled_success

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem refinement_observations :
    (runRequest refinement).elapsed = 1/1024 ∧
    (runRequest refinement).counts.1 = 3 ∧ (runRequest refinement).charged = 5 ∧
    (runRequest refinement).final.error = 160251/8589934592 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem failed_retry_preserves :
    let r := runRequest { refinement with work := 2 }
    r.failure = some .work ∧ r.final = Driver.initial ∧ r.elapsed = 0 ∧
      r.observations.length = 0 ∧ r.counts.1 = 1 ∧ r.charged = 2 := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem zero_and_hold_success :
    (runRequest ⟨[.command NumericalMotion.zeroTick],0,2,⟨1,16384⟩⟩).failure = none ∧
    (runRequest ⟨[.command NumericalMotion.holdTick],1/8192,2,⟨1,16384⟩⟩).failure = none := by
  decide +kernel

end Examples.BudgetDiskDriver
