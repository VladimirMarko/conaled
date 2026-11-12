import Applications.Parallel.FFTScalar

/-! Kernel-checked retained arithmetic costs for the six size16 realizations.
This separate module keeps the closed graph reductions reusable by other clients. -/
namespace Examples.MeasuredFFT
open Applications.Parallel.Factor Applications.Parallel.FFTScalar

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem right_baseline :
    ((circuit false (rightPow 4)).work, (circuit false (rightPow 4)).depth) = (188, 8) := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem left_baseline :
    ((circuit false (leftPow 4)).work, (circuit false (leftPow 4)).depth) = (188, 8) := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem bush_baseline :
    ((circuit false (bush 2)).work, (circuit false (bush 2)).depth) = (176, 6) := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem right_rewritten :
    ((circuit true (rightPow 4)).work, (circuit true (rightPow 4)).depth) = (176, 8) := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem left_rewritten :
    ((circuit true (leftPow 4)).work, (circuit true (leftPow 4)).depth) = (176, 8) := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem bush_rewritten :
    ((circuit true (bush 2)).work, (circuit true (bush 2)).depth) = (168, 6) := by
  decide +kernel

end Examples.MeasuredFFT
