import Mathlib.Algebra.Group.TypeTags.Basic
import Applications.Resources.BinaryCounter
import Applications.Resources.SymmetricWorkload
import Mathlib.Algebra.FreeMonoid.Basic

/-! Actual transitions, finite observations, and retained boundary potentials. -/
namespace Examples.PotentialAccounting
open Resources
namespace Counter
open Resources.BinaryCounter

example : (advanceSquare 4).impl [] = ([false,false,true], 7) := by
  change advanceWithCost 4 [] = _
  rw [advanceWithCost_eq]
  have h := totalCost_potential 4 []
  have cost : totalCost 4 [] = 7 := by change totalCost 4 [] + 1 = 8 at h; omega
  rw [cost]; rfl

example : value ((numericSquare 4).impl []).1 = 4 := (numericSquare 4).commutes []
example : ((observedCounter 4).impl []).1 = 4 := observedCounter_value _ _
example : ((observedCounter 4).impl []).2 = 7 := by
  rw [observedCounter_writes]
  have h := totalCost_potential 4 []
  change totalCost 4 [] + 1 = 8 at h
  omega
example : (bits 5).map value = [0,1,2,3,4] := bits_values 5
example : bitsTransitionCost 5 = 7 := by
  have h := totalCost_potential 4 []
  change totalCost 4 [] + 1 = 8 at h
  change totalCost 4 [] = 7
  omega
example : sourcePrefix 5 [] = some ((bits 5).map encode) := source_bits_eq 5

example : (advanceWithCost 1 [true,true,true]).2 +
    ones (advanceWithCost 1 [true,true,true]).1 = 5 := counter_potential _ _
example : (advanceWithCost 1 [true,true,true]).2 = 4 := by
  rw [advanceWithCost_eq]; rfl
example : value (inc [false,false]) = 1 := value_inc _
example : flipCost [false,false] + ones (inc [false,false]) = 2 := flipCost_potential _
example : ¬ Canonical [false,false] := by simp [Canonical]
example : value [false,false] < 2 ^ ([false,false] : Bits).length := value_lt_two_pow_length _
example (n : Nat) (bs : Bits) (h : bs ∈ bits n) : Canonical bs := bits_canonical n bs h
example : sourceInc [0,2] = some [1,2] := rfl
example : sourceInc [2] = none := rfl
example : sourcePrefix 0 [2] = some [] := rfl
example : sourcePrefix 1 [2] = some [[2]] := rfl
example : sourcePrefix 2 [2] = none := rfl
example : sourcePrefix 2 [0,2] = some [[0,2],[1,2]] := rfl
example : sourceInc (encode [true,true,false,true]) = some [0,0,1,1] := sourceInc_encode _
example : flipCost [true,true,false,true] = 3 := flipCost_eq_leadingOnes_add_one _
example (n : Nat) : (advanceWithCost n []).2 ≤ 2*n := counter_zero_bound n

example (bs : Bits) : advanceWithCost 0 bs = (bs,0) := run_nil _ _
example (bs : Bits) :
    run (fun (_ : Unit) => incWithCost) ([(),()] ++ [(),()]) bs =
      bind (advanceWithCost 2 bs) (advanceWithCost 2) := run_append _ _ _ _

end Counter

/-- Free-monoid observations distinguish execution order. -/
private def recordStep (i s : Nat) : Measured Nat (Additive (FreeMonoid Nat)) :=
  (s+i, Additive.ofMul (FreeMonoid.of i))
example : run recordStep ([1] ++ [2]) 0 =
    (3, Additive.ofMul (FreeMonoid.ofList [1,2])) := by
  rw [run_append]; rfl
example : run recordStep [] 7 = (7,0) := run_nil _ _

example : (7 + 3 ≤ 4 + 6) ↔ (7 : Int) ≤ 4 - 3 + 6 := charge_iff_signed 7 4 3 6
example :
    let step : Unit → Nat → Nat × Nat := fun _ s => (0,s)
    (∀ i s, (step i s).2 + (step i s).1 ≤ s + 0) ∧
      (run step [()] 1).2 > budget step (fun _ _ => 0) [()] 1 := initial_potential_matters

example (ops : List (Fin 3)) :
    budget (fun i (s : Nat) => (s+i.val,i.val)) (fun i _ => i.val) ops 0 ≤ 2 * ops.length :=
  budget_le_constant _ _ 2 (fun i _ => by omega) ops 0

namespace Symmetric
open Sequences.Symmetric Resources.SymmetricCosts

example : tailRun (([0],[1,2,3]) : SymList Nat) = (([3,2],[1]),10) := tailRun_singleton _ _
example : tailRun (([0],[1,2,3,4]) : SymList Nat) = (([4,3],[1,2]),12) := tailRun_singleton _ _
example : initRun (([1,2,3],[4]) : SymList Nat) = (([1],[3,2]),10) := initRun_singleton _ _
example : (rebalanceRun ([1,2,3,4] : List Nat)).2 = 11 := rebalanceRun_work _
example : (rebalanceRun ([1,2,3] : List Nat)).1 = splitSL [1,2,3] := rebalanceRun_value _
example : lengthRun ([1,2,3] : List Nat) = (3,4) := lengthRun_exact _
example : (reverseRun ([1,2] : List Nat) [9]).1 = [2,1,9] := reverseRun_value _ _
example : (splitRun 10 ([1,2] : List Nat)).2 = 3 := splitRun_work _ _

example : (execute .tail (([0],[1,2,3]) : SymList Nat)).charge = 3 := rfl
example : (execute .tail (([0],[]) : SymList Nat)).charge = 0 ∧
    (execute .tail (([0],[]) : SymList Nat)).work = 4 := by
  constructor
  · rfl
  · exact congrArg Prod.snd (tailRun_singleton 0 [])
example : (execute .head (nilSL : SymList Nat)).observation = some none :=
  head_observation _ inv_nilSL
example : (execute .tail (nilSL : SymList Nat)).observation = none := rfl
example : (execute .last (([1],[3,2]) : SymList Nat)).observation = some (some 3) :=
  last_observation _ (by simp [Sequences.Symmetric.Inv])

example : Inv (([0],[1,2,3]) : SymList Nat) ∧
    (run chargeStep [.tail] ([0],[1,2,3])).2 > 2 := initial_potential_needed
example : (measuredRun [.tail] (([0],[1,2,3]) : SymList Nat)).2.1 +
    potential (measuredRun [.tail] ([0],[1,2,3])).1 ≤ 4 :=
  (measuredRun_bounds _ _).1

private def mixed : List (Operation Nat) := [.cons 1, .snoc 2, .head, .tail, .snoc 3, .last]
example : ((observedWorkload mixed).impl nilSL).1 = some 2 := by
  rw [observedWorkload_value _ _ inv_nilSL]; rfl
example : fromSL (measuredRun mixed nilSL).1 = [2,3] := by
  rw [measuredRun_abstraction _ _ inv_nilSL]; rfl
example : Inv (measuredRun mixed nilSL).1 := measuredRun_inv _ _ inv_nilSL
example : ((observedWorkload mixed).impl nilSL).2 = (measuredRun mixed nilSL).2 :=
  observedWorkload_resources _ _
example : reweight (AddMonoidHom.fst Nat Nat) (measuredRun mixed nilSL) =
    run chargeStep mixed nilSL := measuredRun_charge _ _
example : reweight (AddMonoidHom.snd Nat Nat) (measuredRun mixed nilSL) =
    run workStep mixed nilSL := measuredRun_work _ _
example : (run workStep mixed nilSL).2 ≤ 48 := run_work_empty _
example : measuredRun ([] : List (Operation Nat)) nilSL = (nilSL,(0,0)) := run_nil _ _
example : measuredRun ([Operation.cons 1] ++ [.snoc 2,.tail]) nilSL =
    bind (measuredRun [.cons 1] nilSL) (measuredRun [.snoc 2,.tail]) := run_append _ _ _ _

end Symmetric
end Examples.PotentialAccounting
