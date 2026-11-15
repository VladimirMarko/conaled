import Applications.Resources.ListFusion
import Applications.Resources.Steepness
import Mathlib.Algebra.FreeMonoid.Basic

/-! Source cost distinctions and an actual measured sum consumer. -/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.ListFusionCosts
open Resources

theorem ordered_observations :
    (run (fun n s : Nat => (s + n, FreeAddMonoid.of n)) [3, 1, 4] 0).2 =
      FreeAddMonoid.ofList [3, 1, 4] := by
  rw [run_observation _ FreeAddMonoid.of (fun _ _ => rfl)]
  rfl

/-- Zero prices discard the observation, while the same append still executes. -/
theorem zero_price_append (xs ys : List Int) :
    ListAppend.weighted 0 0 xs ys = (xs ++ ys, 0) := by
  simp [ListAppend.weighted_exact]

theorem source_append (xs ys : List Int) :
    ListAppend.weighted 1 1 xs ys = (xs ++ ys, 2 * xs.length + 1) :=
  ListAppend.weighted_exact 1 1 xs ys

theorem direct_digits :
    ListExecution.foldl 1 (fun n d => 10 * n + d) 0 [2, 7, 1, 8] = (2718, 9) := by
  apply Prod.ext
  · rw [ListExecution.foldl_value]; rfl
  · rw [ListExecution.foldl_work]; rfl

theorem recursive_init_digits :
    ListExecution.foldlViaInit 1 (fun n d => 10 * n + d) 0 [2, 7, 1, 8] = (2718, 35) := by
  apply Prod.ext
  · rw [ListExecution.foldlViaInit_value]; rfl
  · rw [ListExecution.foldlViaInit_work]; rfl

theorem one_init_digits :
    ListExecution.foldlByInit 1 (fun n d => 10 * n + d) 0 [2, 7, 1, 8] = (2718, 20) := by
  apply Prod.ext
  · rw [ListExecution.foldlByInit_value]; rfl
  · rw [ListExecution.foldlByInit_work_cons]; rfl

theorem reversal_digits :
    ListExecution.foldlViaReverse 1 (fun n d => 10 * n + d) 0 [2, 7, 1, 8] = (2718, 18) := by
  apply Prod.ext
  · rw [ListExecution.foldlViaReverse_value]; rfl
  · rw [ListExecution.foldlViaReverse_work]; rfl

/-- Flipping the arguments does not alone turn a right fold into a left fold. -/
theorem recursive_head_digits :
    ListExecution.foldrViaHead 1 (fun d n => 10 * n + d) 0 [2, 7, 1, 8] = (8172, 17) := by
  apply Prod.ext
  · rw [ListExecution.foldrViaHead_value]; rfl
  · rw [ListExecution.foldrViaHead_work]; rfl

theorem one_head_digits :
    ListExecution.foldrByHead 1 (fun d n => 10 * n + d) 0 [2, 7, 1, 8] = (8172, 11) := by
  apply Prod.ext
  · rw [ListExecution.foldrByHead_value]; rfl
  · rw [ListExecution.foldrByHead_work_cons]; rfl

theorem empty_selectors :
    ListExecution.head ([] : List Nat) = (none, 1) ∧
    ListExecution.tail ([] : List Nat) = (none, 1) ∧
    ListExecution.init ([] : List Nat) = (none, 1) ∧
    ListExecution.last ([] : List Nat) = (none, 1) := by decide

theorem singleton_selectors :
    ListExecution.init [7] = (some [], 1) ∧ ListExecution.tail [7] = (some [], 1) := by decide

theorem source_reverse : (ListExecution.reverse ([2, 4, 6] : List Nat)).2 = 7 := by
  rw [ListExecution.reverse_work]; rfl

theorem source_selectors :
    (ListExecution.head [7, 8, 9]).2 = 1 ∧
    (ListExecution.init [7, 8, 9]).2 = 5 ∧ (ListExecution.last [7, 8, 9]).2 = 3 := by
  rw [ListExecution.head_work, ListExecution.init_work_cons, ListExecution.last_work_cons]
  decide

theorem fused_successors : (ListFusion.mapFused 1 1 1 1 Nat.succ Nat.succ [1, 2, 3]).2 = 13 := by
  rw [ListFusion.mapFused, ListFusion.map_work]; rfl

theorem materialized_successors :
    (ListFusion.mapTwice 1 1 1 1 Nat.succ Nat.succ [1, 2, 3]).2 = 20 := by
  rw [ListFusion.map_fusion_saving, fused_successors]; rfl

theorem no_dispatch_or_cell_saving (cf cg : Nat) (f g : Int → Int) (xs : List Int) :
    (ListFusion.mapTwice 0 0 cf cg f g xs).2 = (ListFusion.mapFused 0 0 cf cg f g xs).2 := by
  simpa using ListFusion.map_fusion_saving 0 0 cf cg f g xs

theorem long_block_costs :
    (ListFusion.concat1 ([[1, 2, 3]] : List (List Nat))).2 = 9 ∧
    (ListFusion.concat2 ([[1, 2, 3]] : List (List Nat))).2 = 3 := by
  rw [ListFusion.concat1_work, ListFusion.concat2_work]
  decide

theorem singleton_block_costs :
    (ListFusion.concat1 ([[1], [2], [3], [4]] : List (List Nat))).2 = 17 ∧
    (ListFusion.concat2 ([[1], [2], [3], [4]] : List (List Nat))).2 = 21 := by
  change (ListFusion.concat1 ([1, 2, 3, 4].map (fun x : Nat => [x]))).2 = 17 ∧
    (ListFusion.concat2 ([1, 2, 3, 4].map (fun x : Nat => [x]))).2 = 21
  rw [ListFusion.concat1_singletons_work, ListFusion.concat2_singletons_work]
  decide

theorem first_false_cost :
    ListFusion.takeWhile 1 1 1 (fun n : Nat => n < 3) [1, 2, 8, 9, 10] = ([1, 2], 8) :=
  ListFusion.takeWhile_failure 1 1 1 _ [1, 2] 8 [9, 10] (by decide) (by decide)

theorem no_false_at_nil :
    (ListFusion.takeWhile 0 0 1 (fun n : Nat => n < 3) [1, 2]).2 = 2 := by
  rw [ListFusion.takeWhile_tests]; rfl

theorem first_false_is_charged :
    (ListFusion.takeWhile 0 0 1 (fun n : Nat => n < 3) [1, 2, 8]).2 = 3 := by
  rw [ListFusion.takeWhile_tests]; rfl

theorem sumRun_eq_foldr (xs : List Int) :
    Steepness.sumRun xs = ListExecution.foldr 1 (· + ·) 0 xs := by
  apply Prod.ext
  · rw [Steepness.sumRun_value, ListExecution.foldr_value]
    rfl
  · rw [Steepness.sumRun_work, ListExecution.foldr_work]

def concatSquare := erasureSquare (ListFusion.concat1 (α := Int)) List.flatten
  ListFusion.concat1_value

/-- Both the materialized producer and this actual observer retain their costs. -/
def sumSquare : Squares.Square
    ⟨Measured (List Int) Nat, List Int, Prod.fst⟩
    ⟨Measured Int Nat, Int, Prod.fst⟩ where
  impl result := bind result Steepness.sumRun
  spec := List.sum
  commutes result := Steepness.sumRun_value result.1

def materializedSum := Squares.compose sumSquare concatSquare

theorem materializedSum_value (blocks : List (List Int)) :
    (materializedSum.impl blocks).1 = blocks.flatten.sum := materializedSum.commutes blocks

theorem materializedSum_eq (blocks : List (List Int)) :
    materializedSum.impl blocks = ListFusion.foldConcat 1 (· + ·) 0 blocks := by
  change Resources.bind (ListFusion.concat1 blocks) Steepness.sumRun = _
  unfold ListFusion.foldConcat Resources.bind
  rw [sumRun_eq_foldr]

theorem sum_fusion_saving (blocks : List (List Int)) :
    (materializedSum.impl blocks).2 =
      (ListFusion.foldConcatFused 1 (· + ·) 0 blocks).2 + 2 * blocks.flatten.length + 1 := by
  rw [materializedSum_eq]
  exact ListFusion.fold_concat_fusion_saving 1 (· + ·) 0 blocks

theorem sum_fusion_value (blocks : List (List Int)) :
    (ListFusion.foldConcatFused 1 (· + ·) 0 blocks).1 = blocks.flatten.sum := by
  rw [← ListFusion.fold_concat_fusion_value 1 (· + ·) 0 blocks,
    ← materializedSum_eq, materializedSum_value]

theorem signed_observation :
    materializedSum.impl [[-1, 2], [], [4]] = (5, 20) := by
  apply Prod.ext
  · rw [materializedSum_value]; rfl
  · rw [sum_fusion_saving, ListFusion.foldConcatFused_work]; rfl

theorem empty_observation : materializedSum.impl [] = (0, 2) := by
  apply Prod.ext
  · rw [materializedSum_value]; rfl
  · rw [sum_fusion_saving, ListFusion.foldConcatFused_work]; rfl

end Examples.ListFusionCosts
