import Applications.Resources.SearchTreeVisits
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
# Uniform successful search in the two three-key trees

FDSA's printed p.67 illustrates root 6 with leaves 3 and 9, and the increasing
right chain 3, 6, 9. The canonical FDSA-5-94 obligation fixes a uniform present-key
sample and one unit per nonempty visit. All costs below come from the existing
executed map lookup with a key-preserving constant payload.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.ThreeKeySearchMean
open Resources Resources.SearchTree
open Search.OrderedTree
open scoped BigOperators

def balanced : BinaryTree Nat :=
  .node 6 (.node 3 .nil .nil) (.node 9 .nil .nil)

def chain : BinaryTree Nat :=
  .node 3 .nil (.node 6 .nil (.node 9 .nil .nil))

/-- Constant payloads turn the displayed key trees into actual map inputs. -/
def withUnit (tree : BinaryTree Nat) : BinaryTree (Nat × Unit) :=
  tree.map (fun key => (key, ()))

theorem withUnit_keys (tree : BinaryTree Nat) : (withUnit tree).map Prod.fst = tree := by
  unfold withUnit
  rw [← BinaryTree.comp_map]
  change tree.map id = tree
  exact BinaryTree.id_map tree

theorem withUnit_ordered (tree : BinaryTree Nat) (ordered : Ordered tree) :
    OrderedBy Prod.fst (withUnit tree) := by
  rw [orderedBy_iff_map, withUnit_keys]
  exact ordered

theorem balanced_entries : entries balanced = [3, 6, 9] := rfl
theorem chain_entries : entries chain = [3, 6, 9] := rfl

theorem balanced_contains (key : Nat) :
    Contains key balanced ↔ key = 3 ∨ key = 6 ∨ key = 9 := by
  rw [contains_iff_mem_entries, balanced_entries]
  simp

theorem chain_contains (key : Nat) :
    Contains key chain ↔ key = 3 ∨ key = 6 ∨ key = 9 := by
  rw [contains_iff_mem_entries, chain_entries]
  simp

theorem balanced_ordered : Ordered balanced := by
  norm_num [balanced, Ordered, OrderedBy, All]

theorem chain_ordered : Ordered chain := by
  norm_num [chain, Ordered, OrderedBy, All]

def balancedMap : BinaryTree (Nat × Unit) := withUnit balanced
def chainMap : BinaryTree (Nat × Unit) := withUnit chain

theorem balancedMap_ordered : OrderedBy Prod.fst balancedMap :=
  withUnit_ordered balanced balanced_ordered

theorem chainMap_ordered : OrderedBy Prod.fst chainMap :=
  withUnit_ordered chain chain_ordered

/-- The observation pair is (nonempty visits, binary strict tests). -/
theorem balanced_run_three : lookupRun 3 balancedMap = (some (), (2, 3)) := by
  norm_num [balancedMap, withUnit, balanced, BinaryTree.map, lookupRun_node]

theorem balanced_run_six : lookupRun 6 balancedMap = (some (), (1, 2)) := by
  norm_num [balancedMap, withUnit, balanced, BinaryTree.map, lookupRun_node]

theorem balanced_run_nine : lookupRun 9 balancedMap = (some (), (2, 4)) := by
  norm_num [balancedMap, withUnit, balanced, BinaryTree.map, lookupRun_node]

theorem chain_run_three : lookupRun 3 chainMap = (some (), (1, 2)) := by
  norm_num [chainMap, withUnit, chain, BinaryTree.map, lookupRun_node]

theorem chain_run_six : lookupRun 6 chainMap = (some (), (2, 4)) := by
  norm_num [chainMap, withUnit, chain, BinaryTree.map, lookupRun_node]

theorem chain_run_nine : lookupRun 9 chainMap = (some (), (3, 6)) := by
  norm_num [chainMap, withUnit, chain, BinaryTree.map, lookupRun_node]

/-- The entire finite query population, with each present key appearing once. -/
def query (sample : Fin 3) : Nat := 3 * (sample.val + 1)

theorem query_injective : Function.Injective query := by
  intro first second equal
  apply Fin.ext
  dsimp [query] at equal
  omega

theorem query_range : Set.range query = {3, 6, 9} := by
  ext key
  constructor
  · rintro ⟨sample, rfl⟩
    fin_cases sample <;> norm_num [query]
  · intro present
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at present
    rcases present with rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩

theorem query_present (sample : Fin 3) :
    Contains (query sample) balanced ∧ Contains (query sample) chain := by
  rw [balanced_contains, chain_contains]
  fin_cases sample <;> norm_num [query]

theorem balanced_run (sample : Fin 3) :
    lookupRun (query sample) balancedMap =
      (some (), (![2, 1, 2] sample, ![3, 2, 4] sample)) := by
  fin_cases sample
  · exact balanced_run_three
  · exact balanced_run_six
  · exact balanced_run_nine

theorem chain_run (sample : Fin 3) :
    lookupRun (query sample) chainMap =
      (some (), (![1, 2, 3] sample, ![2, 4, 6] sample)) := by
  fin_cases sample
  · exact chain_run_three
  · exact chain_run_six
  · exact chain_run_nine

/-- The projected execution preserves success and derives the visit vector. -/
theorem balanced_visits_run (sample : Fin 3) :
    lookupVisitsRun (query sample) balancedMap = (some (), ![2, 1, 2] sample) := by
  simp only [lookupVisitsRun, balanced_run, reweight]

theorem chain_visits_run (sample : Fin 3) :
    lookupVisitsRun (query sample) chainMap = (some (), ![1, 2, 3] sample) := by
  simp only [lookupVisitsRun, chain_run, reweight]

theorem balanced_lookup_success (sample : Fin 3) :
    Search.OrderedMap.lookup (query sample) balancedMap = some () := by
  rw [← lookupVisitsRun_value, balanced_visits_run]

theorem chain_lookup_success (sample : Fin 3) :
    Search.OrderedMap.lookup (query sample) chainMap = some () := by
  rw [← lookupVisitsRun_value, chain_visits_run]

/-- Each sample has rational mass 1/3; no distribution on all naturals is used. -/
def uniformWeight (_ : Fin 3) : ℚ := 1 / 3

theorem uniformWeight_nonneg (sample : Fin 3) : 0 ≤ uniformWeight sample := by
  norm_num [uniformWeight]

theorem uniformWeight_sum : ∑ sample, uniformWeight sample = 1 := by
  norm_num [uniformWeight, Fin.sum_univ_succ]

/-- Finite rational expectation of an observation on this three-point sample. -/
def uniformMean (cost : Fin 3 → Nat) : ℚ :=
  ∑ sample, uniformWeight sample * (cost sample : ℚ)

theorem uniformMean_eq (cost : Fin 3 → Nat) :
    uniformMean cost = ((cost 0 : ℚ) + (cost 1 : ℚ) + (cost 2 : ℚ)) / 3 := by
  simp only [uniformMean, uniformWeight, Fin.sum_univ_succ, Fin.sum_univ_zero]
  norm_num
  ring

theorem balanced_visit_mean :
    uniformMean (fun sample => (lookupVisitsRun (query sample) balancedMap).2) = 5 / 3 := by
  rw [uniformMean_eq]
  norm_num [balanced_visits_run]

theorem chain_visit_mean :
    uniformMean (fun sample => (lookupVisitsRun (query sample) chainMap).2) = 2 := by
  rw [uniformMean_eq]
  norm_num [chain_visits_run]

theorem uniform_visits_strict :
    uniformMean (fun sample => (lookupVisitsRun (query sample) balancedMap).2) <
      uniformMean (fun sample => (lookupVisitsRun (query sample) chainMap).2) := by
  rw [balanced_visit_mean, chain_visit_mean]
  norm_num

/-- Counting actual binary tests gives different expectations from visits. -/
theorem balanced_binary_test_mean :
    uniformMean (fun sample => (lookupRun (query sample) balancedMap).2.2) = 3 := by
  rw [uniformMean_eq]
  norm_num [balanced_run]

theorem chain_binary_test_mean :
    uniformMean (fun sample => (lookupRun (query sample) chainMap).2.2) = 4 := by
  rw [uniformMean_eq]
  norm_num [chain_run]

theorem balanced_success_inspections (sample : Fin 3) :
    lookupInspections (query sample) balancedMap =
      (lookupVisitsRun (query sample) balancedMap).2 := by
  apply lookupInspections_eq_visits_of_success _ _ ()
  rw [balanced_visits_run]

theorem chain_success_inspections (sample : Fin 3) :
    lookupInspections (query sample) chainMap =
      (lookupVisitsRun (query sample) chainMap).2 := by
  apply lookupInspections_eq_visits_of_success _ _ ()
  rw [chain_visits_run]

/-- An equality hit visits one root while executing both strict tests. -/
theorem root_hit_separates_tariffs :
    lookupVisitsRun 6 balancedMap = (some (), 1) ∧
      (lookupRun 6 balancedMap).2.2 = 2 := by
  norm_num [lookupVisitsRun, balanced_run_six, reweight]

theorem balanced_missing_zero : lookupRun 0 balancedMap = (none, (2, 2)) := by
  norm_num [balancedMap, withUnit, balanced, BinaryTree.map, lookupRun_node]

theorem chain_missing_zero : lookupRun 0 chainMap = (none, (1, 1)) := by
  norm_num [chainMap, withUnit, chain, BinaryTree.map, lookupRun_node]

theorem missing_zero_inspections :
    (lookupVisitsRun 0 balancedMap).2 = 2 ∧ lookupInspections 0 balancedMap = 3 ∧
      (lookupVisitsRun 0 chainMap).2 = 1 ∧ lookupInspections 0 chainMap = 2 := by
  norm_num [lookupVisitsRun, lookupInspections, reweight,
    balanced_missing_zero, chain_missing_zero]

theorem empty_visits_and_inspections (key : Nat) :
    lookupVisitsRun (ν := Unit) key .nil = (none, 0) ∧
      lookupInspections (ν := Unit) key .nil = 1 := by
  exact ⟨lookupVisitsRun_nil key, lookupInspections_nil key⟩

/-- A different normalized distribution: all mass on the present key 3. -/
def concentratedWeight (sample : Fin 3) : ℚ := if sample = 0 then 1 else 0

theorem concentratedWeight_nonneg (sample : Fin 3) :
    0 ≤ concentratedWeight sample := by
  unfold concentratedWeight
  split <;> norm_num

theorem concentratedWeight_sum : ∑ sample, concentratedWeight sample = 1 := by
  norm_num [concentratedWeight, Fin.sum_univ_succ]

def concentratedMean (cost : Fin 3 → Nat) : ℚ :=
  ∑ sample, concentratedWeight sample * (cost sample : ℚ)

theorem concentratedMean_eq (cost : Fin 3 → Nat) :
    concentratedMean cost = (cost 0 : ℚ) := by
  simp [concentratedMean, concentratedWeight]

/-- Concentration at 3 reverses the preference established for uniform queries. -/
theorem concentrated_visits_reverse :
    concentratedMean (fun sample => (lookupVisitsRun (query sample) chainMap).2) = 1 ∧
      concentratedMean (fun sample => (lookupVisitsRun (query sample) balancedMap).2) = 2 ∧
      concentratedMean (fun sample => (lookupVisitsRun (query sample) chainMap).2) <
        concentratedMean (fun sample => (lookupVisitsRun (query sample) balancedMap).2) := by
  rw [concentratedMean_eq, concentratedMean_eq]
  norm_num [chain_visits_run, balanced_visits_run]

end Examples.ThreeKeySearchMean
