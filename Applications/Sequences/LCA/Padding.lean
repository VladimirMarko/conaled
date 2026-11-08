import Applications.Sequences.LCA.BlockShape

/-! Extend the last short block upward. Only original positions are admitted
queries; increasing padding preserves the ±1 class domain without infinities. -/
namespace Sequences.LCA

def paddedDepth (depth : Nat → Int) (n i : Nat) : Int :=
  if i < n then depth i else depth (n-1) + (i-(n-1) : Nat)

theorem paddedDepth_eq (depth : Nat → Int) (hi : i < n) :
    paddedDepth depth n i = depth i := by simp [paddedDepth, hi]

theorem paddedDepth_steps (depth : Nat → Int) (hn : 0 < n)
    (h : UnitSteps (n-1) depth) (steps : Nat) : UnitSteps steps (paddedDepth depth n) := by
  intro i _
  by_cases hnext : i+1 < n
  · have hi : i < n := by omega
    simpa only [paddedDepth, hnext, hi, ite_true] using h i (by omega)
  · by_cases hi : i < n
    · have he : i = n-1 := by omega
      left
      simp only [paddedDepth, hnext, hi, ite_false, ite_true]
      rw [he]
      have hs : n-1+1-(n-1) = 1 := by omega
      simp [hs, add_assoc]
    · left
      simp only [paddedDepth, hnext, hi, ite_false]
      have hs : i+1-(n-1) = i-(n-1)+1 := by omega
      simp [hs, add_assoc]

theorem shifted_steps (depth : Nat → Int) (h : UnitSteps (offset+steps) depth) :
    UnitSteps steps (fun i => depth (offset+i)) := by
  intro i hi
  simpa [Nat.add_assoc] using h (offset+i) (by omega)

theorem padded_block_steps (depth : Nat → Int) (hn : 0 < n)
    (h : UnitSteps (n-1) depth) (block b : Nat) :
    UnitSteps (b-1) (fun i => paddedDepth depth n (block*b+i)) :=
  shifted_steps _ (paddedDepth_steps depth hn h _)

example : paddedDepth (fun i => if i = 0 then (2 : Int) else 1) 2 2 = 2 := by decide
example : paddedDepth (fun i => if i = 0 then (2 : Int) else 1) 2 3 = 3 := by decide

end Sequences.LCA
