import Applications.Resources.Knapsack

/-! Literal scalar source-model recovery. These equations are a reference
specification for the observation projection, separate from the simultaneous
multi-counter execution. Tariffs are mathematical charges, not elapsed time. -/
namespace Resources.Knapsack
open Optimization.KnapsackThinning
variable {α β γ : Type}

def sourceNextRun (i : Item α) (old : Array (Selection α)) (j : Nat) : Selection α × Nat :=
  if j < i.weight then (read old j, 7)
  else (better (read old j) (add i (read old (j-i.weight))), 30)

def sourceMapRun (f : β → γ × Nat) : List β → List γ × Nat
  | [] => ([], 1)
  | x :: xs => let a := f x; let r := sourceMapRun f xs; (a.1 :: r.1, a.2+r.2+2)

def sourceWritesRun (old : Array (Selection α)) : List (Nat × Selection α) → Array (Selection α) × Nat
  | [] => (old, 1)
  | p :: ps => let r := sourceWritesRun (old.setIfInBounds p.1 p.2) ps; (r.1,r.2+8)

def sourceCopyRun (old : Array (Selection α)) : Array (Selection α) × Nat :=
  (old.toList.toArray, 2*old.size+1)

def sourceStepRun (capacity : Nat) (i : Item α) (old : Array (Selection α)) : Array (Selection α) × Nat :=
  let m := sourceMapRun (fun j => let r := sourceNextRun i old j; ((j,r.1),r.2+1))
    (List.range (capacity+1))
  let c := sourceCopyRun old
  let w := sourceWritesRun c.1 m.1
  (w.1,m.2+c.2+w.2+3*(capacity+1)+6)

theorem sourceEntries_exact (i : Item α) (old : Array (Selection α)) (js : List Nat) :
    sourceMapRun (fun j => let r := sourceNextRun i old j; ((j,r.1),r.2+1)) js =
      (js.map (fun j => (j,next i old j)), 10*js.length+23*fits i.weight js+1) := by
  induction js with
  | nil => rfl
  | cons j js ih =>
    rw [sourceMapRun, ih]
    by_cases h : j < i.weight
    · simp [sourceNextRun, next, h, fits, Nat.mul_add]
      omega
    · simp [sourceNextRun, next, h, fits, Nat.mul_add]
      omega

theorem sourceWrites_exact (old : Array (Selection α)) (ps : List (Nat × Selection α)) :
    sourceWritesRun old ps = (assign old ps, 8*ps.length+1) := by
  induction ps generalizing old with
  | nil => rfl
  | cons p ps ih => simp [sourceWritesRun, ih, assign, DynamicProgramming.arrayAssign, Nat.mul_add, Nat.add_assoc]

theorem stepMeasured_sourceScalar (capacity : Nat) (i : Item α) (old : Array (Selection α)) :
    reweight (fun w : Work => w.2.2.2) (stepMeasured capacity i old) =
      sourceStepRun capacity i old := by
  rw [stepMeasured_exact]
  simp [reweight, sourceStepRun, sourceEntries_exact, sourceWrites_exact,
    sourceCopyRun, step, fits_range, Nat.mul_add]
  omega

/-- Arbitrary nonnegative scalar tariffs on the four distinct observations. -/
def tariff (tests comparisons updates work : Nat) : Work →+ Nat where
  toFun w := tests*w.1 + comparisons*w.2.1 + updates*w.2.2.1 + work*w.2.2.2
  map_zero' := by simp
  map_add' := by
    intro a b
    simp only [Prod.fst_add, Prod.snd_add, Nat.mul_add]
    omega

end Resources.Knapsack
