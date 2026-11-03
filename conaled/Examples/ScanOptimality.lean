import Applications.Parallel.PrefixDAG
import Examples.MeasuredScan
import Mathlib.Algebra.Group.PUnit

/-! Global lower bounds and checked scan optima in the declared circuit model. -/
namespace Examples.ScanOptimality
open Applications.Parallel
open Examples.MeasuredScan

/-- Membership is checked from the actual compiled ordered-word outputs. -/
theorem fourBlocks_prefixes : fourBlocks.sharedCircuit.ComputesPrefixes 16 := by
  rw [SharedCircuit.computesPrefixes_iff]
  decide

/-- The all-monoid correctness connection is inherited from the existing scanner. -/
theorem fourBlocks_semantics {M : Type*} [Monoid M] (v : Nat → M) :
    ((fourBlocks.shape.flatten (fourBlocks.circuit fourBlocks.inputWires).1).map (Wire.eval v),
      Wire.eval v (fourBlocks.circuit fourBlocks.inputWires).2) =
      sequential 1 ((List.range 16).map v) :=
  fourBlocks.canonical_correct v

theorem fourBlocks_global_sum :
    fourBlocks.sharedCircuit ∈ Optimization.minimizers
      {c | c.ComputesPrefixes 16} (fun c => c.work + c.depth) := by
  apply SharedCircuit.sum_minimizer_of_bound fourBlocks_prefixes
  have h := fourBlocks_cost
  change fourBlocks.work + fourBlocks.depth = 30
  have hw := congrArg Prod.fst h
  have hd := congrArg Prod.snd h
  omega

theorem fourBlocks_global_pareto :
    fourBlocks.sharedCircuit ∈ Optimization.pareto
      {c | c.ComputesPrefixes 16} (fun c => (c.work, c.depth)) := by
  apply SharedCircuit.pareto_of_bound fourBlocks_prefixes
  have h := fourBlocks_cost
  change fourBlocks.work + fourBlocks.depth = 30
  have hw := congrArg Prod.fst h
  have hd := congrArg Prod.snd h
  omega

/-- The same bound applies to every independently named, topologically ordered DAG. -/
theorem fourBlocks_le_named {n : Nat} (c : PrefixDAG.Circuit n)
    (h : c.ComputesPrefixes 16) : fourBlocks.work + fourBlocks.depth ≤ c.work + c.depth := by
  have hb := PrefixDAG.Circuit.work_depth_lower h
  have hw := congrArg Prod.fst fourBlocks_cost
  have hd := congrArg Prod.snd fourBlocks_cost
  omega

theorem sequentialFour_prefixes : sequentialFour.sharedCircuit.ComputesPrefixes 4 := by
  rw [SharedCircuit.computesPrefixes_iff]
  decide

/-- A sequential four-input scan attains the separate work bound. -/
theorem sequentialFour_work_optimal :
    sequentialFour.sharedCircuit ∈ Optimization.minimizers
      {c | c.ComputesPrefixes 4} SharedCircuit.work := by
  refine ⟨sequentialFour_prefixes, ?_⟩
  intro q hq
  exact SharedCircuit.prefix_work_lower hq

theorem rightTree_prefixes : (ScanPlan.pair.rightPow 4).sharedCircuit.ComputesPrefixes 16 := by
  rw [SharedCircuit.computesPrefixes_iff]
  decide

/-- Four binary levels are necessary for sixteen inputs and attained by this tree. -/
theorem rightTree_depth_optimal :
    (ScanPlan.pair.rightPow 4).sharedCircuit ∈ Optimization.minimizers
      {c | c.ComputesPrefixes 16} SharedCircuit.depth := by
  refine ⟨rightTree_prefixes, ?_⟩
  intro q hq
  have hb := SharedCircuit.prefix_depth_lower hq
  have hd : (ScanPlan.pair.rightPow 4).sharedCircuit.depth = 4 :=
    congrArg Prod.snd rightTree_cost
  change (ScanPlan.pair.rightPow 4).sharedCircuit.depth ≤ q.depth
  rw [hd]
  by_contra h
  have hp : 2 ^ q.depth ≤ 2 ^ 3 := Nat.pow_le_pow_right (by decide) (by omega)
  omega

/-- The three strict work improvements keep depth unchanged. -/
theorem scan_dominance_comparisons :
    mixed.work < (ScanPlan.pair.rightPow 4).work ∧
    mixed.depth = (ScanPlan.pair.rightPow 4).depth ∧
    pairBlocks.work < (ScanPlan.bush 2).work ∧
    pairBlocks.depth = (ScanPlan.bush 2).depth ∧
    fourBlocks.work < (ScanPlan.pair.leftPow 4).work ∧
    fourBlocks.depth = (ScanPlan.pair.leftPow 4).depth := by
  have hm := mixed_cost
  have hr := rightTree_cost
  have hp := pairBlocks_cost
  have hb := bush_cost
  have hf := fourBlocks_cost
  have hl := leftTree_cost
  simp only [Prod.mk.injEq] at *
  omega

example : ScanPlan.empty.sharedCircuit.ComputesPrefixes 0 := by intro i; exact Fin.elim0 i
example : ScanPlan.leaf.sharedCircuit.ComputesPrefixes 1 := by
  rw [SharedCircuit.computesPrefixes_iff]
  decide
example (c : SharedCircuit) (h : c.ComputesPrefixes 0) : 0 ≤ c.work + c.depth :=
  SharedCircuit.prefix_work_depth_lower h

/-- Identity gates remain admissible opponents; no normalization premise is needed. -/
def rawPair : SharedCircuit := ⟨[.input 0, .mul (.mul .one (.input 0)) (.input 1)]⟩
example : rawPair.ComputesPrefixes 2 := by
  rw [SharedCircuit.computesPrefixes_iff]
  decide
example : (rawPair.work, rawPair.depth) = (2, 2) := by decide
example : 2 ≤ rawPair.work + rawPair.depth := SharedCircuit.prefix_work_depth_lower (n := 2) (c := rawPair) (by
  rw [SharedCircuit.computesPrefixes_iff]; decide)

/-- In the singleton monoid every prefix can be a free identity constant. -/
def trivialOutputs : SharedCircuit := ⟨List.replicate 16 .one⟩
example : trivialOutputs.work = 0 := by decide
example (v : Nat → PUnit) : trivialOutputs.eval v = List.replicate 16 (1 : PUnit) := rfl
example (v : Nat → PUnit) (k : Fin 16) :
    ((List.range (k.val + 1)).map v).prod = 1 := Subsingleton.elim _ _
example : ¬ trivialOutputs.ComputesPrefixes 16 := by
  rw [SharedCircuit.computesPrefixes_iff]
  decide

/-- Duplicate named gates are retained separately; an unrelated third gate is dead. -/
def duplicateDAG : PrefixDAG.Circuit 3 :=
  ⟨.push (.push (.push .empty (.input 0) (.input 1)) (.input 0) (.input 1))
      (.input 1) (.input 0),
    [.input 0, .gate ⟨0, by decide⟩, .gate ⟨1, by decide⟩]⟩

example : duplicateDAG.work = 2 := by decide
example : duplicateDAG.compile.work = 1 := by decide
example : duplicateDAG.compile.work ≤ duplicateDAG.work := duplicateDAG.compile_work_le
example : duplicateDAG.compile.arrivals (fun i => if i = 0 then 5 else 2) = [5, 6, 6] := by
  rw [PrefixDAG.Circuit.compile_arrivals]
  rfl
example : duplicateDAG.compile.eval FreeMonoid.of =
    [FreeMonoid.ofList [0], FreeMonoid.ofList [0, 1], FreeMonoid.ofList [0, 1]] := by
  rw [PrefixDAG.Circuit.compile_eval]
  rfl
example : duplicateDAG.ComputesPrefixes 2 := by
  rw [PrefixDAG.Circuit.ComputesPrefixes, SharedCircuit.computesPrefixes_iff]
  decide
example : 2 ≤ duplicateDAG.work + duplicateDAG.depth :=
  PrefixDAG.Circuit.work_depth_lower (k := 2) (c := duplicateDAG) (by
    rw [PrefixDAG.Circuit.ComputesPrefixes, SharedCircuit.computesPrefixes_iff]
    decide)

end Examples.ScanOptimality
