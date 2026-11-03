import Applications.Parallel.MeasuredScan
import Mathlib.Algebra.FreeMonoid.Basic

/-! Checked circuit counts and timing interfaces for sixteen-input scans. -/
namespace Examples.MeasuredScan
open Applications.Parallel
open ScanPlan

def sequentialFour : ScanPlan := .prod (.prod pair .leaf) .leaf
def mixed : ScanPlan := .prod (pair.leftPow 3) (pair.rightPow 3)
def pairBlocks : ScanPlan := .comp (pair.rightPow 3) pair
def fourBlocks : ScanPlan := .comp sequentialFour sequentialFour

theorem rightTree_cost : ((pair.rightPow 4).work, (pair.rightPow 4).depth) = (32, 4) := by decide
theorem leftTree_cost : ((pair.leftPow 4).work, (pair.leftPow 4).depth) = (26, 6) := by decide
theorem bush_cost : ((bush 2).work, (bush 2).depth) = (29, 5) := by decide
theorem mixed_cost : (mixed.work, mixed.depth) = (31, 4) := by decide
theorem pairBlocks_cost : (pairBlocks.work, pairBlocks.depth) = (27, 5) := by decide
theorem fourBlocks_cost : (fourBlocks.work, fourBlocks.depth) = (24, 6) := by decide

theorem early_total : ((pair.leftPow 3).work, (pair.leftPow 3).depth,
    (pair.leftPow 3).totalArrival (fun _ => 0)) = (11, 4, 3) := by decide
theorem rightEight_cost : ((pair.rightPow 3).work, (pair.rightPow 3).depth) = (12, 3) := by decide
theorem mixed_adjustments : mixed.work = (pair.leftPow 3).work + (pair.rightPow 3).work + 8 := by decide

example : (ScanPlan.empty.work, ScanPlan.empty.depth) = (0, 0) := by decide
example : (ScanPlan.leaf.work, ScanPlan.leaf.depth) = (0, 0) := by decide
example : ScanPlan.leaf.arrivals (fun _ => 7) = [0, 7] := by decide
example : pair.arrivals (fun i => if i = 0 then 5 else 2) = [0, 5, 6] := by decide

example : ScanPlan.empty.outputs = [Wire.one] := rfl
example : ScanPlan.leaf.outputs = [Wire.one, Wire.input 0] := rfl
example : (mixed.arrivals (fun i => if i = 0 then 5 else 0)).foldl max 0 = 9 := by decide

/-- Ordered words exercise the universal compiler theorem in a noncommutative monoid. -/
theorem ordered_words :
    ((sequentialFour.shape.flatten (sequentialFour.circuit sequentialFour.inputWires).1).map
      (Wire.eval (fun i => FreeMonoid.of i)),
      Wire.eval (fun i => FreeMonoid.of i)
        (sequentialFour.circuit sequentialFour.inputWires).2) =
      ([FreeMonoid.ofList [], FreeMonoid.ofList [0], FreeMonoid.ofList [0, 1],
        FreeMonoid.ofList [0, 1, 2]], FreeMonoid.ofList [0, 1, 2, 3]) := by
  rw [ScanPlan.canonical_correct]
  rfl

/-- Circuit timing is obtained through the interpretation theorem, also for delayed inputs. -/
example :
    (pair.shape.map (Wire.timing (fun i => if i = 0 then 5 else 2))
      (pair.circuit pair.inputWires).1,
      Wire.timing (fun i => if i = 0 then 5 else 2) (pair.circuit pair.inputWires).2) =
      ((none, some 5), some 6) := by
  rw [ScanPlan.circuit_timing]
  rfl

example (t : Nat → Nat) (a : Wire) :
    Wire.eval (fun i => FreeMonoid.of i) (Wire.times .one a) =
      Wire.eval (fun i => FreeMonoid.of i) a ∧
    (Wire.gates (Wire.times .one a)).card ≤ (Wire.gates (.mul .one a)).card ∧
    Wire.arrival t (Wire.times .one a) ≤ Wire.arrival t (.mul .one a) := by
  exact ⟨by simp [Wire.eval], Wire.times_work_le _ _, Wire.arrival_times_le _ _ _⟩

end Examples.MeasuredScan
