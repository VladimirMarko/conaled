import Applications.Resources.Coloring.Model
import Applications.Resources.Coloring.Invariants
import Mathlib.Tactic.Linarith

/-!
# Actual measured graph helpers

Predicates and insertions consume actual returned values. Removal erases the
outer binding before mapping every remaining payload, including unsuccessful
adjacency erase attempts. The weight of a scanned payload is its own degree.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Resources.Coloring

open Search.PositiveTrie Numerals.PositiveArithmetic Graphs.Coloring
open Resources.PositiveTrie
open scoped BigOperators

def adjRun (g : Graph) (key : Node) : Measured NodeSet Cost :=
  enter .adj (bind (lookup key g) (fun result =>
    observe .adjFound (if result.isSome then 1 else 0) (pure (result.getD .nil))))

def nodesRun (g : Graph) : Measured NodeSet Cost :=
  enter .nodes (mapFold (fun key _ state => insertSet key state) g .nil)

def subsetStep (predicate : Node → NodeSet → Measured Bool Cost)
    (key : Node) (value state : NodeSet) : Measured NodeSet Cost :=
  observe .predicate 1 (bind (predicate key value) (fun accepted =>
    if accepted then observe .candidateInsert 1 (insertSet key state) else pure state))

def subsetNodesRun (predicate : Node → NodeSet → Measured Bool Cost)
    (g : Graph) : Measured NodeSet Cost :=
  enter .subset (mapFold (subsetStep predicate) g .nil)

def lowDegreeRun (prices : Prices) (bound : Nat) (_key : Node) (value : NodeSet) :
    Measured Bool Cost :=
  enter .lowDegree (bind (observe .degreeCardinality 1 (cardinality prices value))
    (fun size => (decide (size < bound), arithmetic (prices.comparison size bound) + mark .comparison 1)))

def eligibleRun (prices : Prices) (bound : Nat) (g : Graph) : Measured NodeSet Cost :=
  enter .eligible (subsetNodesRun (lowDegreeRun prices bound) g)

def removeNodeRun (key : Node) (g : Graph) : Measured Graph Cost :=
  enter .remove (bind (observe .mapErase 1 (eraseMap key g)) (fun remaining =>
    observe .valueMap 1 (valueMap (fun value => observe .adjErase 1 (eraseSet key value)) remaining)))

@[simp] theorem adjRun_value (g : Graph) (key : Node) : (adjRun g key).1 = adj g key := by
  simp only [adjRun, enter_value, bind_value, lookup_value, observe_value, pure, adj]

@[simp] theorem nodesRun_value (g : Graph) : (nodesRun g).1 = nodes g := by
  simp only [nodesRun, enter_value, mapFold_value, insertSet_value, nodes, SparseMap.domain]

theorem subsetStep_value (predicate : Node → NodeSet → Measured Bool Cost)
    (key : Node) (value state : NodeSet) :
    (subsetStep predicate key value state).1 =
      if (predicate key value).1 then KeySet.add key state else state := by
  cases accepted : (predicate key value).1 <;>
    simp only [subsetStep, observe_value, bind_value, accepted, Bool.false_eq_true,
      ↓reduceIte, insertSet_value, pure]

theorem subsetNodesRun_value (predicate : Node → NodeSet → Measured Bool Cost) (g : Graph) :
    (subsetNodesRun predicate g).1 = subsetNodes (fun key value => (predicate key value).1) g := by
  simp only [subsetNodesRun, enter_value, mapFold_value, subsetStep_value, subsetNodes]

@[simp] theorem lowDegreeRun_value (prices : Prices) (bound : Nat) (key : Node) (value : NodeSet) :
    (lowDegreeRun prices bound key value).1 = lowDegree bound key value := by
  simp only [lowDegreeRun, enter_value, bind_value, observe_value, cardinality_value, lowDegree]

@[simp] theorem eligibleRun_value (prices : Prices) (bound : Nat) (g : Graph) :
    (eligibleRun prices bound g).1 = eligible bound g := by
  simp only [eligibleRun, enter_value, subsetNodesRun_value, lowDegreeRun_value, eligible]

@[simp] theorem removeNodeRun_value (key : Node) (g : Graph) :
    (removeNodeRun key g).1 = removeNode key g := by
  simp only [removeNodeRun, enter_value, bind_value, observe_value, eraseMap_value,
    valueMap_value, eraseSet_value, removeNode]

theorem adjRun_work_le (g : Graph) (key : Node) : work (adjRun g key).2 ≤ bitLength key + 1 := by
  have h := lookup_work_le key g
  simp only [adjRun, enter_work, bind_work, observe_work, pure, work_zero, Nat.add_zero]
  omega

theorem adjRun_count (event : Event) (g : Graph) (key : Node) :
    count event (adjRun g key).2 = (if event = .adj then 1 else 0) +
      (if event = .adjFound then (if (SparseMap.find key g).isSome then 1 else 0) else 0) := by
  simp only [adjRun, enter_count, bind_count, lookup_count, lookup_value, observe_count,
    pure, count_zero, Nat.add_zero, Nat.zero_add]

theorem lowDegreeRun_work (prices : Prices) (bound : Nat) (key : Node) (value : NodeSet) :
    work (lowDegreeRun prices bound key value).2 =
      1 + work (cardinality prices value).2 + prices.comparison (KeySet.cardinal value) bound := by
  simp only [lowDegreeRun, enter_work, bind_work, observe_work, observe_value, cardinality_value,
    work_add, work_arithmetic, work_mark, Nat.add_zero, Nat.add_assoc]

theorem lowDegreeRun_unit_work (bound : Nat) (key : Node) (value : NodeSet) :
    work (lowDegreeRun unitPrices bound key value).2 =
      3 * value.numNodes + KeySet.cardinal value + 3 := by
  rw [lowDegreeRun_work, cardinality_unit_work]
  dsimp only [unitPrices]
  omega

theorem cardinality_unit_work_le {bits : Nat} {set : NodeSet} (valid : SetValid bits set)
    (positive : 1 ≤ bits) : work (cardinality unitPrices set).2 ≤ 4 * KeySet.cardinal set * bits + 1 := by
  have nodes := valid.nodes_le
  have card := Nat.mul_le_mul_left (KeySet.cardinal set) positive
  rw [cardinality_unit_work]
  simp only [Nat.mul_one] at card
  simp only [Nat.mul_assoc]
  omega

theorem lowDegreeRun_unit_work_le {bits : Nat} {value : NodeSet} (valid : SetValid bits value)
    (positive : 1 ≤ bits) (bound : Nat) (key : Node) :
    work (lowDegreeRun unitPrices bound key value).2 ≤ 4 * KeySet.cardinal value * bits + 3 := by
  have h := cardinality_unit_work_le valid positive
  rw [lowDegreeRun_work]
  change 1 + work (cardinality unitPrices value).2 + 1 ≤ _
  omega

theorem choose_work_of_none {bits : Nat} {set : NodeSet} (valid : SetValid bits set)
    (absent : KeySet.choose set = none) : work (choose set).2 = 1 := by
  rw [Choice.eq_nil_of_normalized_none valid.normal absent]
  rfl

theorem choose_work_le_of_some {bits : Nat} {set : NodeSet} (valid : SetValid bits set)
    {key : Node} (chosen : KeySet.choose set = some key) : work (choose set).2 ≤ 3 * bits := by
  have nonempty : set ≠ .nil := by intro empty; subst set; cases chosen
  have calls := Choice.run_calls_add_one_le_of_bitLength valid.normal nonempty bits valid.bounded
  have wraps := Choice.run_wrappers chosen
  have bounded := valid.bounded key (KeySet.choose_mem set chosen)
  simp only [choose, reweight, work_structural]
  omega

theorem choose_work_le {bits : Nat} {set : NodeSet} (valid : SetValid bits set) :
    work (choose set).2 ≤ 3 * KeySet.cardinal set * bits + 1 := by
  cases chosen : KeySet.choose set with
  | none => rw [choose_work_of_none valid chosen]; omega
  | some key =>
      have positive : 0 < KeySet.cardinal set := by
        rw [← KeySet.observe_card]
        exact Finset.card_pos.mpr ⟨key, (KeySet.mem_observe key set).mpr (KeySet.choose_mem set chosen)⟩
      have hb := Nat.mul_le_mul_right bits positive
      have hw := choose_work_le_of_some valid chosen
      simp only [Nat.one_mul] at hb
      simp only [Nat.mul_assoc]
      omega

theorem difference_work_le {bits : Nat} {left : NodeSet} (valid : SetValid bits left)
    (right : NodeSet) : work (difference left right).2 ≤ 4 * (KeySet.cardinal left * bits) + 1 := by
  simpa only [difference, reweight, work_structural, pruneWork] using
    Pruning.diffRun_work_le_of_bitLength valid.normal right bits valid.bounded

theorem subsetStep_work (predicate : Node → NodeSet → Measured Bool Cost)
    (key : Node) (value state : NodeSet) :
    work (subsetStep predicate key value state).2 = work (predicate key value).2 +
      (if (predicate key value).1 then 2 * bitLength key else 0) := by
  cases accepted : (predicate key value).1 <;>
    simp only [subsetStep, observe_work, bind_work, accepted, Bool.false_eq_true,
      ↓reduceIte, insertSet_work, pure, work_zero]

theorem lowDegreeRun_count (event : Event) (prices : Prices) (bound : Nat) (key : Node)
    (value : NodeSet) : count event (lowDegreeRun prices bound key value).2 =
      (if event = .lowDegree then 1 else 0) + (if event = .degreeCardinality then 1 else 0) +
        (if event = .comparison then 1 else 0) := by
  simp only [lowDegreeRun, enter_count, bind_count, observe_count, cardinality_count,
    Nat.add_zero, count_add, count_arithmetic, count_mark, Nat.zero_add, Nat.add_assoc]

theorem subsetStep_count (event : Event) (predicate : Node → NodeSet → Measured Bool Cost)
    (key : Node) (value state : NodeSet) : count event (subsetStep predicate key value state).2 =
      (if event = .predicate then 1 else 0) + count event (predicate key value).2 +
        (if (predicate key value).1 then (if event = .candidateInsert then 1 else 0) else 0) := by
  cases accepted : (predicate key value).1 <;>
    simp only [subsetStep, observe_count, bind_count, accepted, Bool.false_eq_true,
      ↓reduceIte, insertSet_count, pure, count_zero, Nat.add_zero, Nat.add_assoc]

theorem removeNodeRun_count (event : Event) (key : Node) (g : Graph) :
    count event (removeNodeRun key g).2 = (if event = .remove then 1 else 0) +
      (if event = .mapErase then 1 else 0) + (if event = .valueMap then 1 else 0) +
        SparseMap.cardinal (SparseMap.erase key g) * (if event = .adjErase then 1 else 0) := by
  have h := valueMap_count_eq event (fun value => observe .adjErase 1 (eraseSet key value))
    (SparseMap.erase key g) (if event = .adjErase then 1 else 0)
    (fun _ _ _ => by simp only [observe_count, eraseSet_count, Nat.add_zero])
  simp only [removeNodeRun, enter_count, bind_count, observe_count, eraseMap_count,
    observe_value, eraseMap_value, Nat.add_zero, h, Nat.add_assoc]

def scanCount (event : Event) (vertices candidates : Nat) : Nat :=
  match event with
  | .eligible | .subset => 1
  | .predicate | .lowDegree | .degreeCardinality | .comparison => vertices
  | .candidateInsert => candidates
  | _ => 0

theorem eligibleRun_count (event : Event) (prices : Prices) (bound : Nat) (g : Graph) :
    count event (eligibleRun prices bound g).2 =
      scanCount event (SparseMap.cardinal g) (KeySet.cardinal (eligible bound g)) := by
  have h := run_projection (countHom event)
    (fun entry state => subsetStep (lowDegreeRun prices bound) entry.1 entry.2 state)
    (fun entry : Node × NodeSet =>
      (if event = .predicate then 1 else 0) + (if event = .lowDegree then 1 else 0) +
      (if event = .degreeCardinality then 1 else 0) + (if event = .comparison then 1 else 0) +
      (if lowDegree bound entry.1 entry.2 then (if event = .candidateInsert then 1 else 0) else 0))
    (fun entry state => by
      change count event (subsetStep (lowDegreeRun prices bound) entry.1 entry.2 state).2 = _
      rw [subsetStep_count, lowDegreeRun_count, lowDegreeRun_value]
      omega)
    (SparseMap.elements g) .nil
  change count event _ = _ at h
  simp only [eligibleRun, enter_count, subsetNodesRun, mapFold_count, h]
  cases event <;> simp [scanCount, List.map_const',
    SparseMap.elements_length, subsetNodes_cardinal, eligible]

theorem removeNodeRun_work_le {bits : Nat} {g : Graph} (valid : GraphValid bits g)
    (key : Node) (bounded : bitLength key ≤ bits) :
    work (removeNodeRun key g).2 ≤
      (6 * bits + 1) * SparseMap.cardinal (SparseMap.erase key g) + 3 * bits + 2 := by
  let remaining := SparseMap.erase key g
  have erased : work (eraseMap key g).2 ≤ 3 * bits :=
    (eraseMap_work_le key g).trans (Nat.mul_le_mul_left 3 bounded)
  have mapped := valueMap_work_le (fun value => observe .adjErase 1 (eraseSet key value)) remaining
    (3 * bits) (fun _ value _ => by
      rw [observe_work]
      exact (eraseSet_work_le key value).trans (Nat.mul_le_mul_left 3 bounded))
  have nodes : remaining.numNodes ≤ SparseMap.cardinal remaining * bits := (valid.erase key).nodes_le
  calc
    _ = 1 + (work (eraseMap key g).2 +
        work (valueMap (fun value => observe .adjErase 1 (eraseSet key value)) remaining).2) := by
      simp only [removeNodeRun, enter_work, bind_work, observe_work, observe_value,
        eraseMap_value, remaining]
    _ ≤ 1 + (3 * bits + (3 * (SparseMap.cardinal remaining * bits) +
        SparseMap.cardinal remaining + 1 + SparseMap.cardinal remaining * (3 * bits))) := by
      omega
    _ = _ := by dsimp only [remaining]; ring

theorem eligibleRun_work_le {bits : Nat} {g : Graph} (valid : GraphValid bits g)
    (positive : 1 ≤ bits) (bound : Nat) :
    work (eligibleRun unitPrices bound g).2 ≤
      4 * SparseMap.cardinal g * bits ^ 2 + 4 * degreeMass g * bits +
        2 * SparseMap.cardinal g * bits + 4 * SparseMap.cardinal g + 3 := by
  let step (entry : Node × NodeSet) (state : NodeSet) :=
    subsetStep (lowDegreeRun unitPrices bound) entry.1 entry.2 state
  let allowed (entry : Node × NodeSet) := SparseMap.find entry.1 g = some entry.2
  let weight (entry : Node × NodeSet) := 4 * bits * KeySet.cardinal entry.2 + (2 * bits + 3)
  have closed (entry : Node × NodeSet) (state : NodeSet) (input : allowed entry)
      (initial : SetValid bits state) : SetValid bits (step entry state).1 := by
    dsimp only [step]
    rw [subsetStep_value, lowDegreeRun_value]
    split_ifs
    · exact initial.add entry.1 (valid.bitLength_le entry.1 entry.2 input)
    · exact initial
  have bounded (entry : Node × NodeSet) (state : NodeSet) (input : allowed entry)
      (_initial : SetValid bits state) : work (step entry state).2 ≤ weight entry := by
    have low := lowDegreeRun_unit_work_le (valid.payload entry.1 entry.2 input) positive bound entry.1
    have key := valid.bitLength_le entry.1 entry.2 input
    dsimp only [step]
    rw [subsetStep_work, lowDegreeRun_value]
    calc
      _ ≤ 4 * KeySet.cardinal entry.2 * bits + 3 + 2 * bits := by
        split_ifs <;> omega
      _ = weight entry := by dsimp only [weight]; ring
  have bill := run_work_le_sum step allowed (SetValid bits) weight closed bounded (SparseMap.elements g)
    (fun entry member => (SparseMap.mem_elements entry.1 entry.2 g).mp member) .nil (SetValid.nil bits)
  have sum : ((SparseMap.elements g).map weight).sum =
      4 * bits * degreeMass g + SparseMap.cardinal g * (2 * bits + 3) :=
    sum_degree_weight (4 * bits) (2 * bits + 3) g
  rw [sum] at bill
  have prefixes := Traversal.map_prefixMass_one_le valid.normal bits valid.bitLength_le
  calc
    _ = 2 + (4 * Traversal.prefixMass g .one + SparseMap.cardinal g + 1 +
        work (Resources.run step (SparseMap.elements g) .nil).2) := by
      simp only [eligibleRun, enter_work, subsetNodesRun, mapFold_cost, work_add,
        work_structural, step, ← Nat.add_assoc]
    _ ≤ 2 + (4 * (SparseMap.cardinal g * bits ^ 2) + SparseMap.cardinal g + 1 +
        (4 * bits * degreeMass g + SparseMap.cardinal g * (2 * bits + 3))) := by omega
    _ = _ := by ring

theorem nodesRun_work (g : Graph) : work (nodesRun g).2 =
    4 * Traversal.prefixMass g .one + SparseMap.cardinal g + 2 +
      ((SparseMap.elements g).map (fun entry => 2 * bitLength entry.1)).sum := by
  have h := run_projection workHom
    (fun entry state => insertSet entry.1 state) (fun entry : Node × NodeSet => 2 * bitLength entry.1)
    (fun entry state => insertSet_work entry.1 state) (SparseMap.elements g) .nil
  change work _ = _ at h
  simp only [nodesRun, enter_work, mapFold_cost, work_add, work_structural]
  rw [h]
  simp only [← Nat.add_assoc]
  congr 1
  omega

theorem nodesRun_work_le {bits : Nat} {g : Graph} (valid : GraphValid bits g) :
    work (nodesRun g).2 ≤
      4 * SparseMap.cardinal g * bits ^ 2 + 2 * SparseMap.cardinal g * bits + SparseMap.cardinal g + 2 := by
  have h := run_work_le_sum (fun entry state => insertSet entry.1 state)
    (fun entry : Node × NodeSet => SparseMap.find entry.1 g = some entry.2)
    (fun _ => True) (fun _ => 2 * bits) (fun _ _ _ _ => trivial)
    (fun entry state found _ => by
      rw [insertSet_work]
      exact Nat.mul_le_mul_left 2 (valid.bitLength_le entry.1 entry.2 found))
    (SparseMap.elements g) (fun entry member => (SparseMap.mem_elements entry.1 entry.2 g).mp member)
    .nil trivial
  simp only [List.map_const', List.sum_replicate_nat, SparseMap.elements_length] at h
  have mass := Traversal.map_prefixMass_one_le valid.normal bits valid.bitLength_le
  simp only [nodesRun, enter_work, mapFold_cost, work_add, work_structural]
  nlinarith

theorem nodesRun_count (event : Event) (g : Graph) :
    count event (nodesRun g).2 = if event = .nodes then 1 else 0 := by
  have h := run_projection (countHom event) (fun entry state => insertSet entry.1 state)
    (fun _ : Node × NodeSet => 0) (fun entry state => insertSet_count event entry.1 state)
    (SparseMap.elements g) .nil
  change count event _ = _ at h
  simp only [nodesRun, enter_count, mapFold_count, h]
  simp

theorem adjRun_arithmetic (g : Graph) (key : Node) : arithmeticHom (adjRun g key).2 = 0 := by
  simp only [adjRun, enter_projection, bind_projection, observe_projection,
    arithmeticHom_structural, arithmeticHom_mark, lookup_arithmetic, pure, map_zero, Nat.zero_add]

theorem removeNodeRun_arithmetic (key : Node) (g : Graph) :
    arithmeticHom (removeNodeRun key g).2 = 0 := by
  have mapped (tree : Graph) : arithmeticHom
      (valueMap (fun value => observe .adjErase 1 (eraseSet key value)) tree).2 = 0 :=
    valueMap_arithmetic_zero _ (fun value => by
      simp only [observe_projection, arithmeticHom_mark, eraseSet_arithmetic, Nat.zero_add]) tree
  simp only [removeNodeRun, enter_projection, bind_projection, observe_projection,
    arithmeticHom_structural, arithmeticHom_mark, eraseMap_arithmetic, mapped, Nat.zero_add]

theorem lowDegreeRun_structural (prices : Prices) (bound : Nat) (key : Node) (value : NodeSet) :
    structuralHom (lowDegreeRun prices bound key value).2 = 2 * value.numNodes + 2 := by
  simp only [lowDegreeRun, enter_projection, bind_projection, observe_projection,
    structuralHom_structural, structuralHom_mark, cardinality_structural, map_add,
    structuralHom_arithmetic, Nat.add_zero, Nat.zero_add]
  omega

theorem lowDegreeRun_arithmetic (prices : Prices) (bound : Nat) (key : Node) (value : NodeSet) :
    arithmeticHom (lowDegreeRun prices bound key value).2 =
      Cardinality.arithmeticWork id prices.addition value + prices.comparison (KeySet.cardinal value) bound := by
  simp only [lowDegreeRun, enter_projection, bind_projection, observe_projection,
    arithmeticHom_structural, arithmeticHom_mark, cardinality_arithmetic, map_add,
    arithmeticHom_arithmetic, observe_value, cardinality_value, Nat.add_zero, Nat.zero_add]

theorem subsetStep_structural (prices : Prices) (bound : Nat) (key : Node) (value state : NodeSet) :
    structuralHom (subsetStep (lowDegreeRun prices bound) key value state).2 =
      2 * value.numNodes + 2 + (if lowDegree bound key value then 2 * bitLength key else 0) := by
  cases accepted : lowDegree bound key value <;>
    simp only [subsetStep, observe_projection, bind_projection, structuralHom_mark,
      lowDegreeRun_value, accepted, Bool.false_eq_true, ↓reduceIte, lowDegreeRun_structural,
      insertSet_structural, pure, map_zero, Nat.add_zero, Nat.zero_add]

theorem subsetStep_arithmetic (prices : Prices) (bound : Nat) (key : Node) (value state : NodeSet) :
    arithmeticHom (subsetStep (lowDegreeRun prices bound) key value state).2 =
      Cardinality.arithmeticWork id prices.addition value + prices.comparison (KeySet.cardinal value) bound := by
  cases accepted : lowDegree bound key value <;>
    simp only [subsetStep, observe_projection, bind_projection, arithmeticHom_mark,
      lowDegreeRun_value, accepted, Bool.false_eq_true, ↓reduceIte, lowDegreeRun_arithmetic,
      insertSet_arithmetic, pure, map_zero, Nat.add_zero, Nat.zero_add]

theorem eligibleRun_structural (prices : Prices) (bound : Nat) (g : Graph) :
    structuralHom (eligibleRun prices bound g).2 =
      4 * Traversal.prefixMass g .one + SparseMap.cardinal g + 3 +
        ((SparseMap.elements g).map (fun entry => 2 * entry.2.numNodes + 2 +
          (if lowDegree bound entry.1 entry.2 then 2 * bitLength entry.1 else 0))).sum := by
  have h := run_projection structuralHom
    (fun entry state => subsetStep (lowDegreeRun prices bound) entry.1 entry.2 state)
    (fun entry : Node × NodeSet => 2 * entry.2.numNodes + 2 +
      (if lowDegree bound entry.1 entry.2 then 2 * bitLength entry.1 else 0))
    (fun entry state => subsetStep_structural prices bound entry.1 entry.2 state) (SparseMap.elements g) .nil
  simp only [eligibleRun, subsetNodesRun, enter_projection, mapFold_cost, map_add,
    structuralHom_structural, structuralHom_mark, Nat.add_zero]
  rw [h]
  simp only [← Nat.add_assoc]
  congr 1
  omega

theorem eligibleRun_structural_eq (prices other : Prices) (bound : Nat) (g : Graph) :
    structuralHom (eligibleRun prices bound g).2 = structuralHom (eligibleRun other bound g).2 := by
  rw [eligibleRun_structural, eligibleRun_structural]

/-- Prices of the additions and comparison actually reached in one scan. -/
def scanTariff (prices : Prices) (bound : Nat) (g : Graph) : Nat :=
  ((SparseMap.elements g).map (fun entry => Cardinality.arithmeticWork id prices.addition entry.2 +
    prices.comparison (KeySet.cardinal entry.2) bound)).sum

theorem eligibleRun_arithmetic (prices : Prices) (bound : Nat) (g : Graph) :
    arithmeticHom (eligibleRun prices bound g).2 = scanTariff prices bound g := by
  have h := run_projection arithmeticHom
    (fun entry state => subsetStep (lowDegreeRun prices bound) entry.1 entry.2 state)
    (fun entry : Node × NodeSet => Cardinality.arithmeticWork id prices.addition entry.2 +
      prices.comparison (KeySet.cardinal entry.2) bound)
    (fun entry state => subsetStep_arithmetic prices bound entry.1 entry.2 state) (SparseMap.elements g) .nil
  simpa only [eligibleRun, subsetNodesRun, enter_projection, mapFold_cost, map_add,
    arithmeticHom_structural, arithmeticHom_mark, Nat.zero_add, scanTariff] using h

end Resources.Coloring
