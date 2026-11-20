import Applications.Resources.RedBlack
import Applications.Resources.DecodedSearchTreeWorkload
import Applications.Resources.Workload
import Applications.Resources.Growth
import Applications.Search.RedBlack.Depth
import Applications.Search.RedBlack.Models
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Tactic.Ring

/-!
# Priced source work and balanced histories

Prices apply to the explicitly defined source observations. Pattern attempts
and individual datatype observations offer different pricing granularities;
neither is automatically a native instruction count. Comparison invocation
overhead and the comparator's own measured work remain separate. A uniform
comparison price is an assumption of a family, not a property of arbitrary Int
comparison or an unbounded family of fixed-width distinct keys.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.RedBlack

universe u v
variable {κ : Type u} {ν : Type v}

open Search.RedBlack (Tree)

/-- The chosen natural price of every named source observation. -/
def weighted (prices : Metric → Nat) (cost : Cost) : Nat :=
  ∑ metric, prices metric * cost metric

@[simp] theorem weighted_zero (prices : Metric → Nat) : weighted prices 0 = 0 := by
  simp [weighted]

theorem weighted_add (prices : Metric → Nat) (a b : Cost) :
    weighted prices (a + b) = weighted prices a + weighted prices b := by
  simp [weighted, Nat.mul_add, Finset.sum_add_distrib]

theorem weighted_mono (prices : Metric → Nat) {a b : Cost} (bound : a ≤ b) :
    weighted prices a ≤ weighted prices b :=
  Finset.sum_le_sum fun metric _ => Nat.mul_le_mul_left (prices metric) (bound metric)

/-- Prices can be moved through the existing measured bind and history executor. -/
def weightedHom (prices : Metric → Nat) : Cost →+ Nat where
  toFun := weighted prices
  map_zero' := weighted_zero prices
  map_add' := weighted_add prices

theorem weighted_eq (prices : Metric → Nat) (cost : Cost) :
    weighted prices cost =
      prices .visits * cost .visits + prices .comparisons * cost .comparisons +
      prices .comparatorWork * cost .comparatorWork +
      prices .balanceCalls * cost .balanceCalls +
      prices .patternAttempts * cost .patternAttempts +
      prices .datatypeObservations * cost .datatypeObservations +
      prices .nodeConstructions * cost .nodeConstructions +
      prices .terminalNils * cost .terminalNils +
      prices .rootInspections * cost .rootInspections +
      prices .enumerationCalls * cost .enumerationCalls +
      prices .consConstructions * cost .consConstructions := by
  change (∑ metric ∈ ({.visits, .comparisons, .comparatorWork, .balanceCalls,
    .patternAttempts, .datatypeObservations, .nodeConstructions,
    .terminalNils, .rootInspections, .enumerationCalls, .consConstructions} : Finset Metric),
      prices metric * cost metric) = _
  simp [add_assoc]

/-- A height envelope retains both invocation and internal comparison work. -/
def lookupEnvelope (height comparisonBound : Nat) : Cost
  | .visits => height
  | .comparisons => 2 * height
  | .comparatorWork => 2 * comparisonBound * height
  | .terminalNils => 1
  | _ => 0

def insertEnvelope (height comparisonBound : Nat) : Cost
  | .visits => height
  | .comparisons => 2 * height
  | .comparatorWork => 2 * comparisonBound * height
  | .balanceCalls => height
  | .patternAttempts => 5 * height
  | .datatypeObservations => 17 * height
  | .nodeConstructions => 3 * height + 2
  | .terminalNils => 1
  | .rootInspections => 1
  | _ => 0

def lookupSlope (prices : Metric → Nat) (comparisonBound : Nat) : Nat :=
  prices .visits + 2 * prices .comparisons +
    2 * comparisonBound * prices .comparatorWork

def lookupIntercept (prices : Metric → Nat) : Nat := prices .terminalNils

def insertSlope (prices : Metric → Nat) (comparisonBound : Nat) : Nat :=
  lookupSlope prices comparisonBound + prices .balanceCalls +
    5 * prices .patternAttempts + 17 * prices .datatypeObservations +
    3 * prices .nodeConstructions

def insertIntercept (prices : Metric → Nat) : Nat :=
  2 * prices .nodeConstructions + prices .terminalNils + prices .rootInspections

theorem weighted_lookupEnvelope (prices : Metric → Nat) (height comparisonBound : Nat) :
    weighted prices (lookupEnvelope height comparisonBound) =
      lookupSlope prices comparisonBound * height + lookupIntercept prices := by
  rw [weighted_eq]
  simp only [lookupEnvelope, lookupSlope, lookupIntercept]
  ring

theorem weighted_insertEnvelope (prices : Metric → Nat) (height comparisonBound : Nat) :
    weighted prices (insertEnvelope height comparisonBound) =
      insertSlope prices comparisonBound * height + insertIntercept prices := by
  rw [weighted_eq]
  simp only [insertEnvelope, insertSlope, lookupSlope, insertIntercept]
  ring

/-- Keep the actual small-size logarithm before forming an asymptotic majorant. -/
theorem affine_log_bound {tree : Tree κ ν} {parent : RBTree.RBColor} {blackHeight : Nat}
    (shape : Search.RedBlack.RB tree parent blackHeight) (a b cost : Nat)
    (bound : cost ≤ a * Search.RedBlack.height tree + b) :
    cost ≤ 2 * a * (tree.size + 1).log2 + b := by
  calc
    cost ≤ a * Search.RedBlack.height tree + b := bound
    _ ≤ a * (2 * (tree.size + 1).log2) + b :=
      Nat.add_le_add_right (Nat.mul_le_mul_left a shape.height_log_bound) b
    _ = 2 * a * (tree.size + 1).log2 + b := by ring

theorem affine_log_majorant {tree : Tree κ ν} {parent : RBTree.RBColor} {blackHeight : Nat}
    (shape : Search.RedBlack.RB tree parent blackHeight) (a b cost : Nat)
    (bound : cost ≤ a * Search.RedBlack.height tree + b) :
    cost ≤ (2 * a + b) * (1 + (tree.size + 1).log2) := by
  have exactBound := affine_log_bound shape a b cost bound
  nlinarith

/-- The family has its actual size function and uniform affine coefficients.
No assertion that the index equals size or that a finite carrier grows unbounded
is made. The operation-specific applications below discharge the affine premise. -/
theorem family_isBigO_of_affine (trees : Nat → Tree κ ν) (cost : Nat → Nat)
    (a b : Nat) (shapes : ∀ i, ∃ n, Search.RedBlack.RB (trees i) .red n)
    (bounds : ∀ i, cost i ≤ a * Search.RedBlack.height (trees i) + b) :
    Asymptotics.IsBigO Filter.atTop (fun i => (cost i : ℝ))
      (fun i => ((1 + ((trees i).size + 1).log2 : Nat) : ℝ)) := by
  apply Resources.isBigO_of_nat_bound _ _ (2 * a + b) 0
  intro i _
  obtain ⟨n, shape⟩ := shapes i
  exact affine_log_majorant shape a b (cost i) (bounds i)

/-- Every component is bounded using the actual finite-input comparator work. -/
theorem lookupRun_cost_le (cmp : κ → κ → Measured Bool Nat) (query : κ)
    (tree : Tree κ ν) (K : Nat)
    (comparison_bound : Search.RedBlack.ForallT
      (fun key _ => (cmp query key).2 ≤ K ∧ (cmp key query).2 ≤ K) tree) :
    (lookupRun cmp query tree).2 ≤ lookupEnvelope (Search.RedBlack.height tree) K := by
  intro metric
  cases metric
  case visits => exact lookupRun_visits_le_height cmp query tree
  case comparisons => exact lookupRun_comparisons_le_height cmp query tree
  case comparatorWork => exact lookupRun_comparatorWork_le_height cmp query tree K comparison_bound
  case terminalNils => exact lookupRun_terminalNils_le cmp query tree
  all_goals simp [lookupEnvelope, lookupRun_other]

theorem lookupRun_weighted_height (prices : Metric → Nat)
    (cmp : κ → κ → Measured Bool Nat) (query : κ) (tree : Tree κ ν) (K : Nat)
    (comparison_bound : Search.RedBlack.ForallT
      (fun key _ => (cmp query key).2 ≤ K ∧ (cmp key query).2 ≤ K) tree) :
    weighted prices (lookupRun cmp query tree).2 ≤
      lookupSlope prices K * Search.RedBlack.height tree + lookupIntercept prices := by
  calc
    weighted prices (lookupRun cmp query tree).2 ≤
        weighted prices (lookupEnvelope (Search.RedBlack.height tree) K) :=
      weighted_mono prices (lookupRun_cost_le cmp query tree K comparison_bound)
    _ = _ := weighted_lookupEnvelope prices _ K

/-- Ordering is unnecessary for the cost bound; it is separate from map meaning. -/
theorem lookupRun_weighted_log (prices : Metric → Nat)
    (cmp : κ → κ → Measured Bool Nat) (query : κ) (tree : Tree κ ν) (K : Nat)
    (comparison_bound : Search.RedBlack.ForallT
      (fun key _ => (cmp query key).2 ≤ K ∧ (cmp key query).2 ≤ K) tree)
    {parent : RBTree.RBColor} {n : Nat} (shape : Search.RedBlack.RB tree parent n) :
    weighted prices (lookupRun cmp query tree).2 ≤
      2 * lookupSlope prices K * (tree.size + 1).log2 + lookupIntercept prices :=
  affine_log_bound shape _ _ _ (lookupRun_weighted_height prices cmp query tree K comparison_bound)

/-- A uniform bound only on each actual query/tree pair is enough for this family. -/
theorem lookup_family_isBigO (prices : Metric → Nat)
    (comparators : Nat → κ → κ → Measured Bool Nat) (queries : Nat → κ)
    (trees : Nat → Tree κ ν) (K : Nat)
    (comparison_bounds : ∀ i, Search.RedBlack.ForallT
      (fun key _ => (comparators i (queries i) key).2 ≤ K ∧
        (comparators i key (queries i)).2 ≤ K) (trees i))
    (shapes : ∀ i, ∃ n, Search.RedBlack.RB (trees i) .red n) :
    Asymptotics.IsBigO Filter.atTop
      (fun i => (weighted prices (lookupRun (comparators i) (queries i) (trees i)).2 : ℝ))
      (fun i => ((1 + ((trees i).size + 1).log2 : Nat) : ℝ)) :=
  family_isBigO_of_affine trees _ (lookupSlope prices K) (lookupIntercept prices) shapes
    (fun i => lookupRun_weighted_height prices (comparators i) (queries i) (trees i) K
      (comparison_bounds i))

theorem unitComparator_localBound (ltb : κ → κ → Bool) (query : κ) (tree : Tree κ ν) :
    Search.RedBlack.ForallT
      (fun key _ => (unitComparator ltb query key).2 ≤ 1 ∧
        (unitComparator ltb key query).2 ≤ 1) tree := by
  apply (Search.RedBlack.forallT_elements_iff _ tree).mpr
  intro _ _
  exact ⟨Nat.le_refl 1, Nat.le_refl 1⟩

/-- This unit-comparison family prices source calls, without claiming constant
native execution time for arbitrary unbounded integer comparisons. -/
theorem lookup_unit_family_isBigO (prices : Metric → Nat)
    (ltb : κ → κ → Bool) (queries : Nat → κ) (trees : Nat → Tree κ ν)
    (shapes : ∀ i, ∃ n, Search.RedBlack.RB (trees i) .red n) :
    Asymptotics.IsBigO Filter.atTop
      (fun i => (weighted prices (lookupRun (unitComparator ltb) (queries i) (trees i)).2 : ℝ))
      (fun i => ((1 + ((trees i).size + 1).log2 : Nat) : ℝ)) :=
  lookup_family_isBigO prices (fun _ => unitComparator ltb) queries trees 1
    (fun i => unitComparator_localBound ltb (queries i) (trees i)) shapes

/-- The complete insertion envelope includes every balance and final blackening. -/
theorem insertRun_cost_le (cmp : κ → κ → Measured Bool Nat) (key : κ) (value : ν)
    (tree : Tree κ ν) (K : Nat)
    (comparison_bound : Search.RedBlack.ForallT
      (fun old _ => (cmp key old).2 ≤ K ∧ (cmp old key).2 ≤ K) tree) :
    (insertRun cmp key value tree).2 ≤ insertEnvelope (Search.RedBlack.height tree) K := by
  intro metric
  cases metric
  case visits => exact insertRun_visits_le_height cmp key value tree
  case comparisons => exact insertRun_comparisons_le_height cmp key value tree
  case comparatorWork => exact insertRun_comparatorWork_le_height cmp key value tree K comparison_bound
  case balanceCalls => exact insertRun_balanceCalls_le_height cmp key value tree
  case patternAttempts =>
    exact (insertRun_patternAttempts_le cmp key value tree).trans
      (Nat.mul_le_mul_left 5 (insertRun_balanceCalls_le_height cmp key value tree))
  case datatypeObservations =>
    exact (insertRun_datatypeObservations_le cmp key value tree).trans
      (Nat.mul_le_mul_left 17 (insertRun_balanceCalls_le_height cmp key value tree))
  case nodeConstructions => exact insertRun_nodeConstructions_le_height cmp key value tree
  case terminalNils => exact insertRun_terminalNils_le cmp key value tree
  case rootInspections => simp [insertEnvelope, insertRun_rootInspections]
  all_goals simp [insertEnvelope, insertRun_other]

theorem insertRun_weighted_height (prices : Metric → Nat)
    (cmp : κ → κ → Measured Bool Nat) (key : κ) (value : ν) (tree : Tree κ ν) (K : Nat)
    (comparison_bound : Search.RedBlack.ForallT
      (fun old _ => (cmp key old).2 ≤ K ∧ (cmp old key).2 ≤ K) tree) :
    weighted prices (insertRun cmp key value tree).2 ≤
      insertSlope prices K * Search.RedBlack.height tree + insertIntercept prices := by
  calc
    weighted prices (insertRun cmp key value tree).2 ≤
        weighted prices (insertEnvelope (Search.RedBlack.height tree) K) :=
      weighted_mono prices (insertRun_cost_le cmp key value tree K comparison_bound)
    _ = _ := weighted_insertEnvelope prices _ K

theorem insertRun_weighted_log (prices : Metric → Nat)
    (cmp : κ → κ → Measured Bool Nat) (key : κ) (value : ν) (tree : Tree κ ν) (K : Nat)
    (comparison_bound : Search.RedBlack.ForallT
      (fun old _ => (cmp key old).2 ≤ K ∧ (cmp old key).2 ≤ K) tree)
    {parent : RBTree.RBColor} {n : Nat} (shape : Search.RedBlack.RB tree parent n) :
    weighted prices (insertRun cmp key value tree).2 ≤
      2 * insertSlope prices K * (tree.size + 1).log2 + insertIntercept prices :=
  affine_log_bound shape _ _ _
    (insertRun_weighted_height prices cmp key value tree K comparison_bound)

theorem insert_family_isBigO (prices : Metric → Nat)
    (comparators : Nat → κ → κ → Measured Bool Nat) (keys : Nat → κ) (values : Nat → ν)
    (trees : Nat → Tree κ ν) (K : Nat)
    (comparison_bounds : ∀ i, Search.RedBlack.ForallT
      (fun key _ => (comparators i (keys i) key).2 ≤ K ∧
        (comparators i key (keys i)).2 ≤ K) (trees i))
    (shapes : ∀ i, ∃ n, Search.RedBlack.RB (trees i) .red n) :
    Asymptotics.IsBigO Filter.atTop
      (fun i => (weighted prices (insertRun (comparators i) (keys i) (values i) (trees i)).2 : ℝ))
      (fun i => ((1 + ((trees i).size + 1).log2 : Nat) : ℝ)) :=
  family_isBigO_of_affine trees _ (insertSlope prices K) (insertIntercept prices) shapes
    (fun i => insertRun_weighted_height prices (comparators i) (keys i) (values i) (trees i) K
      (comparison_bounds i))

theorem insert_unit_family_isBigO (prices : Metric → Nat)
    (ltb : κ → κ → Bool) (keys : Nat → κ) (values : Nat → ν) (trees : Nat → Tree κ ν)
    (shapes : ∀ i, ∃ n, Search.RedBlack.RB (trees i) .red n) :
    Asymptotics.IsBigO Filter.atTop
      (fun i => (weighted prices (insertRun (unitComparator ltb) (keys i) (values i) (trees i)).2 : ℝ))
      (fun i => ((1 + ((trees i).size + 1).log2 : Nat) : ℝ)) :=
  insert_family_isBigO prices (fun _ => unitComparator ltb) keys values trees 1
    (fun i => unitComparator_localBound ltb (keys i) (trees i)) shapes

private theorem coefficient_bound (base comparison terminal K : Nat) :
    2 * (base + K * comparison) + terminal ≤
      (2 * (base + comparison) + terminal) * (1 + K) := by
  calc
    _ ≤ 2 * (base + K * comparison) + terminal +
        ((2 * base + terminal) * K + 2 * comparison) := Nat.le_add_right _ _
    _ = _ := by ring

/-- A varying comparison-work bound stays as a factor of the family majorant. -/
theorem lookup_variable_family_isBigO (prices : Metric → Nat)
    (comparators : Nat → κ → κ → Measured Bool Nat) (queries : Nat → κ)
    (trees : Nat → Tree κ ν) (K : Nat → Nat)
    (comparison_bounds : ∀ i, Search.RedBlack.ForallT
      (fun key _ => (comparators i (queries i) key).2 ≤ K i ∧
        (comparators i key (queries i)).2 ≤ K i) (trees i))
    (shapes : ∀ i, ∃ n, Search.RedBlack.RB (trees i) .red n) :
    Asymptotics.IsBigO Filter.atTop
      (fun i => (weighted prices (lookupRun (comparators i) (queries i) (trees i)).2 : ℝ))
      (fun i => (((1 + K i) * (1 + ((trees i).size + 1).log2) : Nat) : ℝ)) := by
  apply Resources.isBigO_of_nat_bound _ _ (2 * lookupSlope prices 1 + lookupIntercept prices) 0
  intro i _
  obtain ⟨n, shape⟩ := shapes i
  have workBound := affine_log_majorant shape _ _ _
    (lookupRun_weighted_height prices (comparators i) (queries i) (trees i) (K i)
      (comparison_bounds i))
  have coefficient : 2 * lookupSlope prices (K i) + lookupIntercept prices ≤
      (2 * lookupSlope prices 1 + lookupIntercept prices) * (1 + K i) := by
    simpa [lookupSlope, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
      coefficient_bound (prices .visits + 2 * prices .comparisons)
        (2 * prices .comparatorWork) (lookupIntercept prices) (K i)
  exact workBound.trans (by
    simpa only [Nat.mul_assoc] using
      Nat.mul_le_mul_right (1 + ((trees i).size + 1).log2) coefficient)

theorem insert_variable_family_isBigO (prices : Metric → Nat)
    (comparators : Nat → κ → κ → Measured Bool Nat) (keys : Nat → κ) (values : Nat → ν)
    (trees : Nat → Tree κ ν) (K : Nat → Nat)
    (comparison_bounds : ∀ i, Search.RedBlack.ForallT
      (fun key _ => (comparators i (keys i) key).2 ≤ K i ∧
        (comparators i key (keys i)).2 ≤ K i) (trees i))
    (shapes : ∀ i, ∃ n, Search.RedBlack.RB (trees i) .red n) :
    Asymptotics.IsBigO Filter.atTop
      (fun i => (weighted prices (insertRun (comparators i) (keys i) (values i) (trees i)).2 : ℝ))
      (fun i => (((1 + K i) * (1 + ((trees i).size + 1).log2) : Nat) : ℝ)) := by
  apply Resources.isBigO_of_nat_bound _ _ (2 * insertSlope prices 1 + insertIntercept prices) 0
  intro i _
  obtain ⟨n, shape⟩ := shapes i
  have workBound := affine_log_majorant shape _ _ _
    (insertRun_weighted_height prices (comparators i) (keys i) (values i) (trees i) (K i)
      (comparison_bounds i))
  have coefficient : 2 * insertSlope prices (K i) + insertIntercept prices ≤
      (2 * insertSlope prices 1 + insertIntercept prices) * (1 + K i) := by
    have h := coefficient_bound
      (prices .visits + 2 * prices .comparisons + prices .balanceCalls +
        5 * prices .patternAttempts + 17 * prices .datatypeObservations + 3 * prices .nodeConstructions)
      (2 * prices .comparatorWork) (insertIntercept prices) (K i)
    convert h using 1 <;> simp only [insertSlope, lookupSlope] <;> ring
  exact workBound.trans (by
    simpa only [Nat.mul_assoc] using
      Nat.mul_le_mul_right (1 + ((trees i).size + 1).log2) coefficient)

/-- Standard scanl exposes the actual states before and after chronological writes. -/
def prefixTrees (ltb : κ → κ → Bool) (writes : List (κ × ν)) (tree : Tree κ ν) :
    List (Tree κ ν) :=
  writes.scanl (fun state binding => Search.RedBlack.insert ltb binding.1 binding.2 state) tree

@[simp] theorem prefixTrees_length (ltb : κ → κ → Bool) (writes : List (κ × ν))
    (tree : Tree κ ν) : (prefixTrees ltb writes tree).length = writes.length + 1 :=
  List.length_scanl

/-- A prefix observation is exactly the accepted chronological executor on take. -/
theorem prefixTrees_get (ltb : κ → κ → Bool) (writes : List (κ × ν)) (tree : Tree κ ν)
    (i : Nat) (inside : i ≤ writes.length) :
    (prefixTrees ltb writes tree)[i]'(by simpa only [prefixTrees_length] using Nat.lt_succ_of_le inside) =
      Search.OrderedMap.bindAll (Search.RedBlack.ops ltb) (writes.take i) tree := by
  have hi : i < (writes.scanl
      (fun state binding => Search.RedBlack.insert ltb binding.1 binding.2 state) tree).length := by
    simpa only [List.length_scanl] using Nat.lt_succ_of_le inside
  calc
    (prefixTrees ltb writes tree)[i] =
        (writes.scanl
          (fun state binding => Search.RedBlack.insert ltb binding.1 binding.2 state) tree)[i]'hi := rfl
    _ = (writes.take i).foldl
        (fun state binding => Search.RedBlack.insert ltb binding.1 binding.2 state) tree :=
      List.getElem_scanl hi
    _ = _ := by
      clear hi
      generalize writes.take i = initialWrites
      induction initialWrites generalizing tree with
      | nil => rfl
      | cons binding rest ih => exact ih _

theorem prefixTrees_bst (decode : κ → Int) (ltb : κ → κ → Bool)
    (hlt : ∀ a b, ltb a b = true ↔ decode a < decode b)
    (writes : List (κ × ν)) {tree : Tree κ ν} (valid : Search.RedBlack.BST decode tree) :
    ∀ state ∈ prefixTrees ltb writes tree, Search.RedBlack.BST decode state := by
  induction writes generalizing tree with
  | nil => simpa [prefixTrees] using valid
  | cons binding rest ih =>
      simp only [prefixTrees, List.scanl_cons, List.forall_mem_cons]
      exact ⟨valid, ih (Search.RedBlack.insert_bst decode ltb hlt valid binding.1 binding.2)⟩

/-- Shape preservation is independent of reflected ordering and decoder injection. -/
theorem prefixTrees_shape (ltb : κ → κ → Bool) (writes : List (κ × ν))
    {tree : Tree κ ν} (shape : ∃ n, Search.RedBlack.RB tree .red n) :
    ∀ state ∈ prefixTrees ltb writes tree, ∃ n, Search.RedBlack.RB state .red n := by
  induction writes generalizing tree with
  | nil => simpa [prefixTrees] using shape
  | cons binding rest ih =>
      simp only [prefixTrees, List.scanl_cons, List.forall_mem_cons]
      obtain ⟨n, shape⟩ := shape
      exact ⟨⟨n, shape⟩, ih (Search.RedBlack.insert_RB ltb binding.1 binding.2 shape)⟩

/-- The existing executor consumes actual measured insertion results in order. -/
def buildRun (cmp : κ → κ → Measured Bool Nat) (writes : List (κ × ν))
    (tree : Tree κ ν) : Measured (Tree κ ν) Cost :=
  Resources.run (fun binding state => insertRun cmp binding.1 binding.2 state) writes tree

@[simp] theorem buildRun_nil (cmp : κ → κ → Measured Bool Nat) (tree : Tree κ ν) :
    buildRun cmp [] tree = (tree, 0) := rfl

theorem buildRun_cons (cmp : κ → κ → Measured Bool Nat) (binding : κ × ν)
    (writes : List (κ × ν)) (tree : Tree κ ν) :
    buildRun cmp (binding :: writes) tree =
      bind (insertRun cmp binding.1 binding.2 tree) (buildRun cmp writes) := rfl

theorem buildRun_value (cmp : κ → κ → Measured Bool Nat) (writes : List (κ × ν))
    (tree : Tree κ ν) :
    (buildRun cmp writes tree).1 =
      Search.OrderedMap.bindAll (Search.RedBlack.ops (fun a b => (cmp a b).1)) writes tree := by
  induction writes generalizing tree with
  | nil => rfl
  | cons binding rest ih =>
      change (buildRun cmp rest (insertRun cmp binding.1 binding.2 tree).1).1 = _
      rw [ih, insertRun_value]
      rfl

theorem buildRun_value_of (cmp : κ → κ → Measured Bool Nat) (ltb : κ → κ → Bool)
    (agreement : ∀ a b, (cmp a b).1 = ltb a b) (writes : List (κ × ν)) (tree : Tree κ ν) :
    (buildRun cmp writes tree).1 = Search.OrderedMap.bindAll (Search.RedBlack.ops ltb) writes tree := by
  rw [buildRun_value]
  simp only [agreement]

theorem buildRun_bst (decode : κ → Int) (cmp : κ → κ → Measured Bool Nat)
    (hlt : ∀ a b, (cmp a b).1 = true ↔ decode a < decode b)
    (writes : List (κ × ν)) {tree : Tree κ ν} (valid : Search.RedBlack.BST decode tree) :
    Search.RedBlack.BST decode (buildRun cmp writes tree).1 := by
  unfold buildRun
  refine Resources.run_invariant _ _ ?_ writes tree valid
  intro binding state stateValid
  rw [insertRun_value]
  exact Search.RedBlack.insert_bst decode _ hlt stateValid binding.1 binding.2

theorem buildRun_shape (cmp : κ → κ → Measured Bool Nat) (writes : List (κ × ν))
    {tree : Tree κ ν} (shape : ∃ n, Search.RedBlack.RB tree .red n) :
    ∃ n, Search.RedBlack.RB (buildRun cmp writes tree).1 .red n := by
  unfold buildRun
  refine Resources.run_invariant _ (fun state => ∃ n, Search.RedBlack.RB state .red n)
    ?_ writes tree shape
  intro binding state stateShape
  obtain ⟨n, h⟩ := stateShape
  rw [insertRun_value]
  exact Search.RedBlack.insert_RB _ binding.1 binding.2 h

/-- Repricing commutes with the established measured executor. -/
theorem buildRun_reweight (prices : Metric → Nat) (cmp : κ → κ → Measured Bool Nat)
    (writes : List (κ × ν)) (tree : Tree κ ν) :
    reweight (weightedHom prices) (buildRun cmp writes tree) =
      Resources.run (fun binding state => reweight (weightedHom prices)
        (insertRun cmp binding.1 binding.2 state)) writes tree :=
  Resources.reweight_run (weightedHom prices) _ writes tree

/-- Observe each write's cost on its actual preceding source state. The final
scanl state has no following write and is discarded by ordinary zip. -/
def stepCosts (cmp : κ → κ → Measured Bool Nat) (writes : List (κ × ν))
    (tree : Tree κ ν) : List Cost :=
  (writes.zip (prefixTrees (fun a b => (cmp a b).1) writes tree)).map
    (fun entry => (insertRun cmp entry.1.1 entry.1.2 entry.2).2)

theorem buildRun_cost (cmp : κ → κ → Measured Bool Nat) (writes : List (κ × ν))
    (tree : Tree κ ν) : (buildRun cmp writes tree).2 = (stepCosts cmp writes tree).sum := by
  induction writes generalizing tree with
  | nil => rfl
  | cons binding rest ih =>
      change (insertRun cmp binding.1 binding.2 tree).2 +
        (buildRun cmp rest (insertRun cmp binding.1 binding.2 tree).1).2 = _
      rw [ih, insertRun_value]
      simp only [stepCosts, prefixTrees, List.scanl_cons, List.zip_cons_cons,
        List.map_cons, List.sum_cons]

theorem buildRun_weighted_cost (prices : Metric → Nat) (cmp : κ → κ → Measured Bool Nat)
    (writes : List (κ × ν)) (tree : Tree κ ν) :
    weighted prices (buildRun cmp writes tree).2 =
      ((stepCosts cmp writes tree).map (weighted prices)).sum := by
  rw [buildRun_cost]
  exact map_list_sum (weightedHom prices) _

/-- Every summand uses that write's actual state size and its local comparison
bound. Repeated keys need not increase those sizes. No write-count=size premise
or global comparison bound is used. -/
theorem buildRun_weighted_log_sum (prices : Metric → Nat)
    (cmp : κ → κ → Measured Bool Nat) (writes : List (κ × ν)) (tree : Tree κ ν)
    (K : (κ × ν) → Tree κ ν → Nat)
    (comparison_bounds : ∀ entry ∈ writes.zip (prefixTrees (fun a b => (cmp a b).1) writes tree),
      Search.RedBlack.ForallT
        (fun old _ => (cmp entry.1.1 old).2 ≤ K entry.1 entry.2 ∧
          (cmp old entry.1.1).2 ≤ K entry.1 entry.2) entry.2)
    (shape : ∃ n, Search.RedBlack.RB tree .red n) :
    weighted prices (buildRun cmp writes tree).2 ≤
      ((writes.zip (prefixTrees (fun a b => (cmp a b).1) writes tree)).map
        (fun entry => 2 * insertSlope prices (K entry.1 entry.2) *
          (entry.2.size + 1).log2 + insertIntercept prices)).sum := by
  rw [buildRun_weighted_cost]
  simp only [stepCosts, List.map_map, Function.comp_def]
  apply List.sum_le_sum
  intro entry member
  obtain ⟨binding, state⟩ := entry
  obtain ⟨n, stateShape⟩ := prefixTrees_shape (fun a b => (cmp a b).1) writes shape state
    (List.of_mem_zip member).2
  exact insertRun_weighted_log prices cmp binding.1 binding.2 state (K binding state)
    (comparison_bounds (binding, state) member) stateShape

/-- The source writes payload one on the supplied chronological keys. -/
def buildKeysRun (cmp : κ → κ → Measured Bool Nat) (keys : List κ) :
    Measured (Tree κ Nat) Cost :=
  buildRun cmp (Search.OrderedMap.Workload.sourceWrites keys) .nil

def queryStep (cmp : κ → κ → Measured Bool Nat) (tree : Tree κ Nat)
    (query : κ) (hits : Nat) : Measured Nat Cost :=
  bind (lookupRun cmp query tree) fun result =>
    pure (if result.getD 0 = 1 then hits + 1 else hits)

def queryRun (cmp : κ → κ → Measured Bool Nat) (queries : List κ)
    (tree : Tree κ Nat) : Measured Nat Cost :=
  Resources.run (queryStep cmp tree) queries 0

/-- Measured construction feeds its actual returned tree to the measured query phase. -/
def sourceRun (cmp : κ → κ → Measured Bool Nat) (inserted queries : List κ) :
    Measured Nat Cost :=
  bind (buildKeysRun cmp inserted) (queryRun cmp queries)

theorem queryRun_value (cmp : κ → κ → Measured Bool Nat) (queries : List κ)
    (tree : Tree κ Nat) :
    (queryRun cmp queries tree).1 = queries.foldl
      (fun hits query =>
        if Search.RedBlack.lookup (fun a b => (cmp a b).1) 0 query tree = 1
        then hits + 1 else hits) 0 := by
  rw [queryRun, Resources.run_state]
  congr 1
  funext hits query
  simp only [queryStep, bind_value, pure, lookupRun_value, Search.RedBlack.lookup]
  rfl

theorem sourceRun_work (cmp : κ → κ → Measured Bool Nat) (inserted queries : List κ) :
    (sourceRun cmp inserted queries).2 =
      (buildKeysRun cmp inserted).2 + (queryRun cmp queries (buildKeysRun cmp inserted).1).2 := rfl

theorem queryStep_cost (cmp : κ → κ → Measured Bool Nat) (tree : Tree κ Nat)
    (query : κ) (hits : Nat) : (queryStep cmp tree query hits).2 = (lookupRun cmp query tree).2 := by
  simp [queryStep, bind, pure]

/-- The accumulator changes the returned hit count, not the query's observed work. -/
theorem queryRun_cost (cmp : κ → κ → Measured Bool Nat) (queries : List κ)
    (tree : Tree κ Nat) :
    (queryRun cmp queries tree).2 = (queries.map (fun q => (lookupRun cmp q tree).2)).sum :=
  Resources.run_observation (queryStep cmp tree) (fun q => (lookupRun cmp q tree).2)
    (queryStep_cost cmp tree) queries 0

theorem queryRun_weighted_cost (prices : Metric → Nat) (cmp : κ → κ → Measured Bool Nat)
    (queries : List κ) (tree : Tree κ Nat) :
    weighted prices (queryRun cmp queries tree).2 =
      (queries.map (fun q => weighted prices (lookupRun cmp q tree).2)).sum := by
  rw [queryRun_cost]
  change (weightedHom prices) (queries.map (fun q => (lookupRun cmp q tree).2)).sum = _
  rw [map_list_sum, List.map_map]
  rfl

/-- Query-dependent comparator bounds remain in the sum; the tree is the actual
fixed result passed to this phase, and repeated queries are counted repeatedly. -/
theorem queryRun_weighted_log_sum (prices : Metric → Nat)
    (cmp : κ → κ → Measured Bool Nat) (queries : List κ) (tree : Tree κ Nat)
    (K : κ → Nat)
    (comparison_bounds : ∀ q ∈ queries,
      Search.RedBlack.ForallT (fun old _ => (cmp q old).2 ≤ K q ∧ (cmp old q).2 ≤ K q) tree)
    {n : Nat} (shape : Search.RedBlack.RB tree .red n) :
    weighted prices (queryRun cmp queries tree).2 ≤
      (queries.map (fun q => 2 * lookupSlope prices (K q) * (tree.size + 1).log2 +
        lookupIntercept prices)).sum := by
  rw [queryRun_weighted_cost]
  apply List.sum_le_sum
  intro q member
  exact lookupRun_weighted_log prices cmp q tree (K q) (comparison_bounds q member) shape

/-- Default parameters select the accepted model contract; optional meaning and
the actual measured history preserve every payload, including stored defaults.
BST validity is required here, while no color invariant is used. -/
theorem buildRun_meaning (decode : κ → Int) (cmp : κ → κ → Measured Bool Nat)
    (ltb : κ → κ → Bool) (agreement : ∀ a b, (cmp a b).1 = ltb a b)
    (hinj : Function.Injective decode)
    (hlt : ∀ a b, ltb a b = true ↔ decode a < decode b)
    (default : ν) (writes : List (κ × ν)) {tree : Tree κ ν}
    (valid : Search.RedBlack.BST decode tree) :
    letI := Representations.SignedComparison.linearOrderOfStrict decode ltb hinj hlt
    Search.RedBlack.enumAbs decode ltb hinj hlt (buildRun cmp writes tree).1 =
      Search.OrderedMap.writeAll writes (Search.RedBlack.enumAbs decode ltb hinj hlt tree) := by
  let _ : LinearOrder κ := Representations.SignedComparison.linearOrderOfStrict decode ltb hinj hlt
  rw [buildRun_value_of cmp ltb agreement]
  have meaning := (Search.RedBlack.model_enum_laws decode ltb hinj hlt default).setAll writes valid
  change Search.RedBlack.enumAbs decode ltb hinj hlt
      (Search.TotalTable.setAll (Search.TotalTable.ofPartial (Search.RedBlack.ops ltb) default)
        writes tree) = _ at meaning
  simpa only [Search.TotalTable.setAll_ofPartial] using meaning

/-- Both actual measured realizations implement the same complete chronological
meaning. Their shapes and their observed costs are allowed to differ. -/
theorem buildRun_meaning_agrees (decode : κ → Int) (cmp : κ → κ → Measured Bool Nat)
    (ltb : κ → κ → Bool) (agreement : ∀ a b, (cmp a b).1 = ltb a b)
    (hinj : Function.Injective decode)
    (hlt : ∀ a b, ltb a b = true ↔ decode a < decode b)
    (default : ν) (writes : List (κ × ν)) :
    Search.RedBlack.enumAbs decode ltb hinj hlt (buildRun cmp writes .nil).1 =
      Search.OrderedMap.DecodedKeys.enumAbs decode ltb hinj hlt
        (DecodedSearchTreeWorkload.buildRun ltb writes .nil).1 := by
  let _ : LinearOrder κ := Representations.SignedComparison.linearOrderOfStrict decode ltb hinj hlt
  rw [buildRun_meaning decode cmp ltb agreement hinj hlt default writes (Search.RedBlack.bst_nil decode),
    DecodedSearchTreeWorkload.buildRun_value]
  have meaning := Search.OrderedMap.DecodedKeys.enumAbs_setAll decode ltb hinj hlt default writes
    (t := .nil) (by trivial)
  change Search.OrderedMap.DecodedKeys.enumAbs decode ltb hinj hlt
      (Search.TotalTable.setAll
        (Search.TotalTable.ofPartial (Search.OrderedMap.DecodedKeys.ops ltb) default)
        writes .nil) = _ at meaning
  rw [Search.TotalTable.setAll_ofPartial] at meaning
  rw [meaning]
  rfl

/-- Optional search results agree for every query after the shared history. -/
theorem buildRun_lookup_agrees (decode : κ → Int) (cmp : κ → κ → Measured Bool Nat)
    (ltb : κ → κ → Bool) (agreement : ∀ a b, (cmp a b).1 = ltb a b)
    (hinj : Function.Injective decode)
    (hlt : ∀ a b, ltb a b = true ↔ decode a < decode b)
    (default : ν) (writes : List (κ × ν)) (query : κ) :
    Search.RedBlack.lookup? ltb query (buildRun cmp writes .nil).1 =
      Search.OrderedMap.DecodedKeys.lookup? ltb query
        (DecodedSearchTreeWorkload.buildRun ltb writes .nil).1 := by
  let _ : LinearOrder κ := Representations.SignedComparison.linearOrderOfStrict decode ltb hinj hlt
  have reflected : ∀ a b, (cmp a b).1 = true ↔ decode a < decode b := by
    simpa only [agreement] using hlt
  have validRB := buildRun_bst decode cmp reflected writes (Search.RedBlack.bst_nil decode)
  have laws := Search.OrderedMap.DecodedKeys.model_enum_laws decode ltb hinj hlt default
  have validOrdinary := laws.totalLaws.setAll_valid writes laws.empty_valid
  change Search.OrderedMap.DecodedKeys.BST decode
    (Search.TotalTable.setAll
      (Search.TotalTable.ofPartial (Search.OrderedMap.DecodedKeys.ops ltb) default)
      writes .nil) at validOrdinary
  rw [Search.TotalTable.setAll_ofPartial] at validOrdinary
  have validMeasured : Search.OrderedMap.DecodedKeys.BST decode
      (DecodedSearchTreeWorkload.buildRun ltb writes .nil).1 := by
    simpa only [DecodedSearchTreeWorkload.buildRun_value] using validOrdinary
  have same := congrFun (buildRun_meaning_agrees decode cmp ltb agreement hinj hlt default writes) query
  rw [Search.RedBlack.enumAbs_lookup decode ltb hinj hlt validRB,
    Search.OrderedMap.DecodedKeys.enumAbs_lookup decode ltb hinj hlt validMeasured] at same
  exact same

theorem sourceRun_agrees (decode : κ → Int) (cmp : κ → κ → Measured Bool Nat)
    (ltb : κ → κ → Bool) (agreement : ∀ a b, (cmp a b).1 = ltb a b)
    (hinj : Function.Injective decode)
    (hlt : ∀ a b, ltb a b = true ↔ decode a < decode b)
    (inserted queries : List κ) :
    (sourceRun cmp inserted queries).1 = (DecodedSearchTreeWorkload.sourceRun ltb inserted queries).1 := by
  rw [sourceRun, bind_value, queryRun_value,
    DecodedSearchTreeWorkload.sourceRun, bind_value, DecodedSearchTreeWorkload.queryRun_value]
  congr 1
  funext hits query
  have same := buildRun_lookup_agrees decode cmp ltb agreement hinj hlt 0
    (Search.OrderedMap.Workload.sourceWrites inserted) query
  simp only [Search.RedBlack.lookup, Search.OrderedMap.DecodedKeys.lookup, agreement,
    buildKeysRun, DecodedSearchTreeWorkload.buildKeysRun, same]
  rfl

/-- The independent checker observes membership in the supplied insertion list,
not shape, elapsed time, or another balanced-tree execution. -/
theorem sourceRun_independent_count (decode : κ → Int) (cmp : κ → κ → Measured Bool Nat)
    (ltb : κ → κ → Bool) (agreement : ∀ a b, (cmp a b).1 = ltb a b)
    (hinj : Function.Injective decode)
    (hlt : ∀ a b, ltb a b = true ↔ decode a < decode b)
    (inserted queries : List κ) :
    letI := Representations.SignedComparison.linearOrderOfStrict decode ltb hinj hlt
    (sourceRun cmp inserted queries).1 = Search.OrderedMap.Workload.expectedHits inserted queries := by
  rw [sourceRun_agrees decode cmp ltb agreement hinj hlt]
  exact DecodedSearchTreeWorkload.sourceRun_independent_count decode ltb hinj hlt inserted queries

/-- The accepted descending source schedule generates the same chronological
consecutive key lists for both measured phases, before any encoding assumption. -/
theorem sourceRun_consecutive_schedule (cmp : Nat → Nat → Measured Bool Nat) (n : Nat) :
    sourceRun cmp ((Search.OrderedMap.Workload.sourceIndices n).map (fun j => n - j))
      ((Search.OrderedMap.Workload.sourceIndices n).map (fun j => n - j)) =
      sourceRun cmp (List.range n) (List.range n) := by
  rw [Search.OrderedMap.Workload.sourceIndices_consecutive]

/-- Pricing enumeration exposes its exact linear source cost on every raw tree;
the arbitrary suffix contributes no traversal or construction charge. -/
theorem elementsAuxRun_weighted (prices : Metric → Nat) (tree : Tree κ ν)
    (suffix : List (κ × ν)) :
    weighted prices (elementsAuxRun tree suffix).2 =
      prices .enumerationCalls * (2 * tree.size + 1) + prices .consConstructions * tree.size := by
  rw [weighted_eq]
  simp only [elementsAuxRun_enumerationCalls, elementsAuxRun_consConstructions]
  simp [elementsAuxRun_other]

/-- Repricing retains the actual build/query phase split and the returned tree. -/
theorem sourceRun_weighted (prices : Metric → Nat) (cmp : κ → κ → Measured Bool Nat)
    (inserted queries : List κ) :
    weighted prices (sourceRun cmp inserted queries).2 =
      weighted prices (buildKeysRun cmp inserted).2 +
        weighted prices (queryRun cmp queries (buildKeysRun cmp inserted).1).2 := by
  rw [sourceRun_work, weighted_add]

end Resources.RedBlack
