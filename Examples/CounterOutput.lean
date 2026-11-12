import Applications.Resources.CounterOutput
import Applications.Sequences.Permutations

/-! Independent finite fixtures through the public counter/output contracts. -/
set_option autoImplicit false
set_option warningAsError true
namespace Examples.CounterOutput
open Resources Resources.BinaryCounter Resources.CounterOutput

-- Frozen source observations, not computed by the renderer.
def fiveStates : List Bits := [[], [true], [false,true], [true,true], [false,false,true]]
def fiveLines : List (List Symbol) :=
  [[.left,.right,.lineEnd],
   [.left,.digit true,.right,.lineEnd],
   [.left,.digit false,.digit true,.right,.lineEnd],
   [.left,.digit true,.digit true,.right,.lineEnd],
   [.left,.digit false,.digit false,.digit true,.right,.lineEnd]]

theorem prefix_five : prefixRun 5 [] = (fiveStates, 7) := by
  rw [prefixRun_eq]
  decide

theorem rendered_five : renderStates fiveStates = (fiveLines, 23) := by
  rw [renderStates_eq]
  decide

theorem decoded_five : (renderStates fiveStates).1.map decodeDigits = fiveStates :=
  renderStates_decode _

theorem actual_token_count : (renderStates fiveStates).2 =
    ((renderStates fiveStates).1.map List.length).sum := renderStates_actual_symbols _

theorem transition_bills : CounterGeometry.bills 4 [] = [1,2,1,3] := by decide

theorem printed_five : (printCounter 5 []).transitionWork = 7 ∧
    (printCounter 5 []).symbols = 23 ∧ (printCounter 5 []).lines = fiveLines := by
  simp only [printCounter, prefix_five, rendered_five]
  decide

theorem observed_numbers : ((printCounter 5 []).lines.map decodeDigits).map value =
    [0,1,2,3,4] := printCounter_values 5

theorem empty_prefix (seed : Bits) : prefixRun 0 seed = ([],0) := prefixRun_eq 0 seed

theorem single_empty : (printCounter 1 []).transitionWork = 0 ∧
    (printCounter 1 []).symbols = 3 := by decide

theorem noncanonical_decode :
    (printCounter 1 [false]).lines.map decodeDigits = [[false]] :=
  printCounter_states 1 [false]

theorem noncanonical_separation : value [] = value [false] ∧
    (printCounter 1 []).lines ≠ (printCounter 1 [false]).lines ∧
    (printCounter 1 []).symbols ≠ (printCounter 1 [false]).symbols := by decide

theorem carry_prefix : prefixRun 3 [true,true] =
    ([[true,true],[false,false,true],[true,false,true]],4) := by
  rw [prefixRun_eq]
  decide

theorem arbitrary_seed_bound (n : Nat) :
    digitMass (iteratePrefix inc n [false,true,false]) ≤
      n*3 + ∑ i ∈ Finset.range n, i := prefix_digitMass_bound n _

theorem symbol_bound (n : Nat) : (printCounter n []).symbols ≤ n*n+3*n :=
  printCounter_symbols_upper n

theorem combined_bound (n : Nat) :
    (printCounter n []).transitionWork + (printCounter n []).symbols ≤ 6*(n*n) :=
  compute_and_output_upper n

-- A distinct declared tariff, not the literal renderer's token count.
def comparisonCallback (bs : Bits) : Measured Bits StructuredLinear.Costs.Work :=
  (bs, StructuredLinear.Costs.tick .outputWrite (1+bs.length))

def comparisonRun := StructuredLinear.Costs.traverse comparisonCallback fiveStates

theorem comparison_values : comparisonRun.1 = fiveStates := by
  simp [comparisonRun, StructuredLinear.Costs.traverse_value, comparisonCallback]

theorem comparison_bill : comparisonRun.2 .outputWrite + (2*fiveStates.length+1) = 24 := by
  decide

theorem repriced_renderer (states : List Bits) :
    reweight outputCharge (StructuredLinear.Costs.traverse outputCallback states) =
      (states.map (fun bs => (outputCallback bs).1),
       (states.map (fun bs => outputCharge (outputCallback bs).2)).sum) :=
  traversal_reweight outputCharge outputCallback states

-- Observe existing insertion outputs; do not charge or replace their generation.
def inserted : List (List Nat) := Sequences.Permutations.insertsWith id 1 [1,2]
def insertionPrice (xs : List Nat) : Nat := xs[0]?.getD 0 + 2 * xs[1]?.getD 0
def insertionCallback (xs : List Nat) : Measured (List Nat × Nat) StructuredLinear.Costs.Work :=
  ((xs, insertionPrice xs), StructuredLinear.Costs.tick .outputWrite (insertionPrice xs))
def insertionObserved := StructuredLinear.Costs.traverse insertionCallback inserted

theorem insertion_values : inserted = [[1,1,2],[1,1,2],[1,2,1]] := by
  rw [inserted, Sequences.Permutations.insertsWith_eq_map]
  decide

theorem insertion_observed : insertionObserved.1 =
    [([1,1,2],3),([1,1,2],3),([1,2,1],5)] ∧
    insertionObserved.2 .outputWrite = 11 := by
  simp only [insertionObserved, StructuredLinear.Costs.traverse_value,
    StructuredLinear.Costs.traverse_cost, insertion_values]
  decide

end Examples.CounterOutput
