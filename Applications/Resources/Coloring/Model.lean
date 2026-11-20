import Applications.Resources.ListExecution.MeasuredFold
import Applications.Resources.PositiveTrie.Finite
import Applications.Resources.PositiveTrie.Pruning
import Applications.Resources.PositiveTrie.Cardinality
import Applications.Resources.PositiveTrie.Choice
import Applications.Resources.PositiveTrie.ValueMap
import Applications.Resources.PositiveTrie.MapFold
import Applications.Resources.PositiveTrie.SetFold
import Applications.Resources.PositiveTrie.Enumeration
import Mathlib.Algebra.Group.Pi.Basic

/-!
# The Color source-event observation

Structural work and actual arithmetic tariffs are separate. Event counts are
observations of already charged actions, never a second charge. Every adapter
below retains the actual value produced by the accepted primitive executor.
No finite enumeration, reversal or size observation is inserted for a proof.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Resources.Coloring

open Search.PositiveTrie Numerals.PositiveArithmetic
open Resources.PositiveTrie

universe u v w
variable {α : Type u} {σ : Type v} {C : Type w}

inductive Event where
  | select | eligible | subset | predicate | lowDegree | degreeCardinality | comparison
  | candidateInsert | candidateChoice | remove | mapErase | valueMap | adjErase | selectedCons
  | adj | adjFound | nodes | colorsOf | available | difference | colorChoice | colorStep | colorList | color
  | paletteCardinality | neighborLookup | neighborSuccess | neighborInsert | assignmentWrite
  | listEntry | listCallback | addEdge | mkGraph | edgeRead | edgeSetInsert | edgeMapWrite
  | paletteSetup | paletteInsert | domainExport | assignmentExport | decode | exportCons
  | exportPair | pipeline
  deriving DecidableEq, Repr

abbrev Counters := Event → Nat
abbrev Cost := (Nat × Nat) × Counters

def structural (n : Nat) : Cost := ((n, 0), 0)
def arithmetic (n : Nat) : Cost := ((0, n), 0)
def mark (event : Event) (n : Nat) : Cost := ((0, 0), fun query => if query = event then n else 0)
def work (cost : Cost) : Nat := cost.1.1 + cost.1.2
def count (event : Event) (cost : Cost) : Nat := cost.2 event

@[simp] theorem work_zero : work 0 = 0 := rfl
@[simp] theorem work_add (left right : Cost) : work (left + right) = work left + work right := by
  dsimp [work]
  omega
@[simp] theorem work_structural (n : Nat) : work (structural n) = n := Nat.add_zero n
@[simp] theorem work_arithmetic (n : Nat) : work (arithmetic n) = n := Nat.zero_add n
@[simp] theorem work_mark (event : Event) (n : Nat) : work (mark event n) = 0 := rfl
@[simp] theorem count_zero (event : Event) : count event 0 = 0 := rfl
@[simp] theorem count_add (event : Event) (left right : Cost) :
    count event (left + right) = count event left + count event right := rfl
@[simp] theorem count_structural (event : Event) (n : Nat) : count event (structural n) = 0 := rfl
@[simp] theorem count_arithmetic (event : Event) (n : Nat) : count event (arithmetic n) = 0 := rfl
@[simp] theorem count_mark (query event : Event) (n : Nat) :
    count query (mark event n) = if query = event then n else 0 := rfl

def workHom : Cost →+ Nat where
  toFun := work
  map_zero' := work_zero
  map_add' := work_add

def structuralHom : Cost →+ Nat where
  toFun := fun cost => cost.1.1
  map_zero' := rfl
  map_add' := fun _ _ => rfl

def arithmeticHom : Cost →+ Nat where
  toFun := fun cost => cost.1.2
  map_zero' := rfl
  map_add' := fun _ _ => rfl

def countHom (event : Event) : Cost →+ Nat where
  toFun := count event
  map_zero' := rfl
  map_add' := fun _ _ => rfl

@[simp] theorem structuralHom_structural (n : Nat) : structuralHom (structural n) = n := rfl
@[simp] theorem structuralHom_arithmetic (n : Nat) : structuralHom (arithmetic n) = 0 := rfl
@[simp] theorem structuralHom_mark (event : Event) (n : Nat) : structuralHom (mark event n) = 0 := rfl
@[simp] theorem arithmeticHom_structural (n : Nat) : arithmeticHom (structural n) = 0 := rfl
@[simp] theorem arithmeticHom_arithmetic (n : Nat) : arithmeticHom (arithmetic n) = n := rfl
@[simp] theorem arithmeticHom_mark (event : Event) (n : Nat) : arithmeticHom (mark event n) = 0 := rfl

def observe (event : Event) (n : Nat) (result : Measured α Cost) : Measured α Cost :=
  (result.1, mark event n + result.2)

def enter (event : Event) (result : Measured α Cost) : Measured α Cost :=
  (result.1, structural 1 + mark event 1 + result.2)

@[simp] theorem observe_value (event : Event) (n : Nat) (result : Measured α Cost) :
    (observe event n result).1 = result.1 := rfl
@[simp] theorem enter_value (event : Event) (result : Measured α Cost) :
    (enter event result).1 = result.1 := rfl
@[simp] theorem observe_work (event : Event) (n : Nat) (result : Measured α Cost) :
    work (observe event n result).2 = work result.2 := by simp [observe]
@[simp] theorem enter_work (event : Event) (result : Measured α Cost) :
    work (enter event result).2 = 1 + work result.2 := by simp [enter]
@[simp] theorem observe_count (query event : Event) (n : Nat) (result : Measured α Cost) :
    count query (observe event n result).2 = (if query = event then n else 0) + count query result.2 :=
  rfl
@[simp] theorem enter_count (query event : Event) (result : Measured α Cost) :
    count query (enter event result).2 = (if query = event then 1 else 0) + count query result.2 := by
  simp [enter]
@[simp] theorem bind_work (result : Measured α Cost) (next : α → Measured σ Cost) :
    work (bind result next).2 = work result.2 + work (next result.1).2 := work_add _ _
@[simp] theorem bind_count (event : Event) (result : Measured α Cost)
    (next : α → Measured σ Cost) :
    count event (bind result next).2 = count event result.2 + count event (next result.1).2 := rfl

theorem bind_projection (projection : Cost →+ Nat) (result : Measured α Cost)
    (next : α → Measured σ Cost) :
    projection (bind result next).2 = projection result.2 + projection (next result.1).2 := map_add projection _ _

theorem enter_projection (projection : Cost →+ Nat) (event : Event) (result : Measured α Cost) :
    projection (enter event result).2 =
      projection (structural 1) + projection (mark event 1) + projection result.2 := by
  simp only [enter, map_add]

theorem observe_projection (projection : Cost →+ Nat) (event : Event) (n : Nat)
    (result : Measured α Cost) :
    projection (observe event n result).2 = projection (mark event n) + projection result.2 := map_add projection _ _

structure Prices where
  addition : Nat → Nat → Nat
  comparison : Nat → Nat → Nat

def unitPrices : Prices := ⟨Cardinality.unitPrice, fun _ _ => 1⟩

def lookup (key : PosNum) (tree : SparseMap α) : Measured (Option α) Cost :=
  reweight (fun cost => structural cost.1) (Finite.findRun key tree)

def insertMap (key : PosNum) (value : α) (tree : SparseMap α) : Measured (SparseMap α) Cost :=
  reweight (fun cost => structural (cost.1 + cost.2)) (Finite.mapAddRun key value tree)

def insertSet (key : PosNum) (tree : KeySet) : Measured KeySet Cost :=
  reweight (fun cost => structural (cost.1 + cost.2)) (Finite.setAddRun key tree)

def pruneWork (cost : Pruning.Cost) : Nat := cost.1 + cost.2.1 + cost.2.2

def eraseMap (key : PosNum) (tree : SparseMap α) : Measured (SparseMap α) Cost :=
  reweight (fun cost => structural (pruneWork cost)) (Pruning.mapEraseRun key tree)

def eraseSet (key : PosNum) (tree : KeySet) : Measured KeySet Cost :=
  reweight (fun cost => structural (pruneWork cost)) (Pruning.setEraseRun key tree)

def difference (left right : KeySet) : Measured KeySet Cost :=
  reweight (fun cost => structural (pruneWork cost)) (Pruning.diffRun left right)

def choose (tree : KeySet) : Measured (Option PosNum) Cost :=
  reweight (fun cost => structural (cost.1 + cost.2)) (Choice.run tree)

def cardinality (prices : Prices) (tree : KeySet) : Measured Nat Cost :=
  reweight (fun cost => structural cost.1.1 + arithmetic cost.2)
    (Cardinality.setRun prices.addition tree)

def mapFold (callback : PosNum → α → σ → Measured σ Cost) (tree : SparseMap α)
    (seed : σ) : Measured σ Cost :=
  reweight (fun cost => structural (MapFold.outerWork cost.1) + cost.2)
    (MapFold.run callback tree seed)

def setFold (callback : PosNum → σ → Measured σ Cost) (tree : KeySet)
    (seed : σ) : Measured σ Cost :=
  reweight (fun cost => structural (SetFold.outerWork cost.1) + cost.2)
    (SetFold.run callback tree seed)

def valueMap (callback : α → Measured σ Cost) (tree : SparseMap α) :
    Measured (SparseMap σ) Cost :=
  reweight (fun cost => structural (cost.1.1 + cost.1.2.1 + cost.1.2.2) + cost.2)
    (ValueMap.run callback tree)

def listFold (callback : α → σ → Measured σ Cost) (xs : List α)
    (seed : σ) : Measured σ Cost :=
  reweight (fun cost => structural (cost.1.1 + cost.1.2) +
    mark .listEntry cost.1.1 + mark .listCallback cost.1.2 + cost.2)
    (ListExecution.MeasuredFold.run callback xs seed)

@[simp] theorem lookup_value (key : PosNum) (tree : SparseMap α) :
    (lookup key tree).1 = SparseMap.find key tree := Finite.findRun_value key tree
@[simp] theorem insertMap_value (key : PosNum) (value : α) (tree : SparseMap α) :
    (insertMap key value tree).1 = SparseMap.add key value tree := Finite.mapAddRun_value key value tree
@[simp] theorem insertSet_value (key : PosNum) (tree : KeySet) :
    (insertSet key tree).1 = KeySet.add key tree := Finite.setAddRun_value key tree
@[simp] theorem eraseMap_value (key : PosNum) (tree : SparseMap α) :
    (eraseMap key tree).1 = SparseMap.erase key tree := Pruning.mapEraseRun_value key tree
@[simp] theorem eraseSet_value (key : PosNum) (tree : KeySet) :
    (eraseSet key tree).1 = KeySet.erase key tree := Pruning.setEraseRun_value key tree
@[simp] theorem difference_value (left right : KeySet) :
    (difference left right).1 = KeySet.diff left right := Pruning.diffRun_value left right
@[simp] theorem choose_value (tree : KeySet) : (choose tree).1 = KeySet.choose tree := Choice.run_value tree
@[simp] theorem cardinality_value (prices : Prices) (tree : KeySet) :
    (cardinality prices tree).1 = KeySet.cardinal tree := Cardinality.setRun_value prices.addition tree

theorem mapFold_value (callback : PosNum → α → σ → Measured σ Cost) (tree : SparseMap α)
    (seed : σ) : (mapFold callback tree seed).1 =
      SparseMap.fold (fun key value state => (callback key value state).1) tree seed :=
  MapFold.run_value callback tree seed

theorem setFold_value (callback : PosNum → σ → Measured σ Cost) (tree : KeySet)
    (seed : σ) : (setFold callback tree seed).1 =
      KeySet.fold (fun key state => (callback key state).1) tree seed := SetFold.run_value callback tree seed

theorem valueMap_value (callback : α → Measured σ Cost) (tree : SparseMap α) :
    (valueMap callback tree).1 = SparseMap.map (fun value => (callback value).1) tree :=
  ValueMap.run_value callback tree

theorem listFold_value (callback : α → σ → Measured σ Cost) (xs : List α) (seed : σ) :
    (listFold callback xs seed).1 = xs.foldr (fun x state => (callback x state).1) seed :=
  ListExecution.MeasuredFold.run_value callback xs seed

theorem mapFold_cost (callback : PosNum → α → σ → Measured σ Cost)
    (tree : SparseMap α) (seed : σ) :
    (mapFold callback tree seed).2 =
      structural (4 * Traversal.prefixMass tree .one + SparseMap.cardinal tree + 1) +
        (Resources.run (fun entry state => callback entry.1 entry.2 state)
          (SparseMap.elements tree) seed).2 := by
  have h := congrArg Prod.snd (MapFold.run_callback callback tree seed)
  simp only [mapFold, reweight, MapFold.run, MapFold.runFrom_outer_work]
  exact congrArg (_ + ·) h

theorem setFold_cost (callback : PosNum → σ → Measured σ Cost) (tree : KeySet) (seed : σ) :
    (setFold callback tree seed).2 =
      structural (4 * tree.numNodes + 2 * KeySet.keyMass tree + 1) +
        (Resources.run callback (KeySet.elements tree) seed).2 := by
  have h := congrArg Prod.snd (SetFold.run_callback callback tree seed)
  simp only [setFold, reweight, SetFold.run, SetFold.runFrom_outer_work, Traversal.reversalMass_one]
  exact congrArg (_ + ·) h

theorem listFold_cost (callback : α → σ → Measured σ Cost) (xs : List α) (seed : σ) :
    (listFold callback xs seed).2 = structural (2 * xs.length + 1) +
      mark .listEntry (xs.length + 1) + mark .listCallback xs.length +
        (Resources.run callback xs.reverse seed).2 := by
  have h := congrArg Prod.snd (ListExecution.MeasuredFold.run_callback callback xs seed)
  simp only [listFold, reweight, ListExecution.MeasuredFold.run_counts]
  rw [show xs.length + 1 + xs.length = 2 * xs.length + 1 by omega]
  exact congrArg (_ + ·) h

/-- Project callback work through the existing ordered runner, keeping its states. -/
theorem run_work_le_sum (callback : α → σ → Measured σ Cost)
    (allowed : α → Prop) (I : σ → Prop) (weight : α → Nat)
    (closed : ∀ x state, allowed x → I state → I (callback x state).1)
    (bounded : ∀ x state, allowed x → I state → work (callback x state).2 ≤ weight x)
    (xs : List α) (inputs : ∀ x ∈ xs, allowed x) (seed : σ) (initial : I seed) :
    work (Resources.run callback xs seed).2 ≤ (xs.map weight).sum := by
  have h := Resources.run_work_le_sum_on
    (fun x state => reweight workHom (callback x state)) allowed I weight closed bounded xs inputs seed initial
  rw [← Resources.reweight_run workHom] at h
  exact h

theorem listFold_work_le_sum (callback : α → σ → Measured σ Cost)
    (allowed : α → Prop) (I : σ → Prop) (weight : α → Nat)
    (closed : ∀ x state, allowed x → I state → I (callback x state).1)
    (bounded : ∀ x state, allowed x → I state → work (callback x state).2 ≤ weight x)
    (xs : List α) (inputs : ∀ x ∈ xs, allowed x) (seed : σ) (initial : I seed) :
    work (listFold callback xs seed).2 ≤ 2 * xs.length + 1 + (xs.map weight).sum := by
  have h := run_work_le_sum callback allowed I weight closed bounded xs.reverse
    (fun x member => inputs x (List.mem_reverse.mp member)) seed initial
  rw [List.map_reverse, List.sum_reverse] at h
  rw [listFold_cost]
  simp only [work_add, work_structural, work_mark, Nat.add_zero]
  exact Nat.add_le_add_left h _

theorem listFold_work_nil (callback : α → σ → Measured σ Cost) (seed : σ) :
    work (listFold callback [] seed).2 = 1 := rfl

theorem listFold_work_cons (callback : α → σ → Measured σ Cost)
    (x : α) (xs : List α) (seed : σ) :
    work (listFold callback (x :: xs) seed).2 =
      2 + work (listFold callback xs seed).2 +
        work (callback x (listFold callback xs seed).1).2 := by
  simp only [listFold, reweight, ListExecution.MeasuredFold.run_cons, work, structural, mark,
    Prod.fst_add, Prod.snd_add]
  omega

theorem lookup_work_le (key : PosNum) (tree : SparseMap α) :
    work (lookup key tree).2 ≤ bitLength key := by
  simpa only [lookup, reweight, work_structural] using Finite.findRun_calls_le key tree

theorem insertMap_work (key : PosNum) (value : α) (tree : SparseMap α) :
    work (insertMap key value tree).2 = 2 * bitLength key := by
  simp only [insertMap, reweight, Finite.mapAddRun_cost, work_structural, two_mul]

theorem insertSet_work (key : PosNum) (tree : KeySet) :
    work (insertSet key tree).2 = 2 * bitLength key := by
  simp only [insertSet, reweight, Finite.setAddRun_cost, work_structural, two_mul]

theorem eraseMap_work_le (key : PosNum) (tree : SparseMap α) :
    work (eraseMap key tree).2 ≤ 3 * bitLength key := by
  simpa only [eraseMap, reweight, work_structural, pruneWork] using Pruning.mapEraseRun_work_le key tree

theorem eraseSet_work_le (key : PosNum) (tree : KeySet) :
    work (eraseSet key tree).2 ≤ 3 * bitLength key := by
  simpa only [eraseSet, reweight, work_structural, pruneWork] using Pruning.setEraseRun_work_le key tree

theorem cardinality_unit_work (tree : KeySet) :
    work (cardinality unitPrices tree).2 = 3 * tree.numNodes + KeySet.cardinal tree + 1 := by
  simpa only [cardinality, reweight, work_add, work_structural, work_arithmetic, unitPrices] using
    Cardinality.setRun_unit_work tree

theorem cardinality_structural (prices : Prices) (tree : KeySet) :
    structuralHom (cardinality prices tree).2 = 2 * tree.numNodes + 1 := by
  change (Cardinality.setRun prices.addition tree).2.1.1 + 0 = _
  simpa only [Nat.add_zero] using congrArg Prod.fst (Cardinality.setRun_counts prices.addition tree)

theorem cardinality_arithmetic (prices : Prices) (tree : KeySet) :
    arithmeticHom (cardinality prices tree).2 = Cardinality.arithmeticWork id prices.addition tree := by
  change 0 + (Cardinality.setRun prices.addition tree).2.2 = _
  rw [Nat.zero_add]
  exact Cardinality.run_price id prices.addition tree

theorem cardinality_unit_arithmetic (tree : KeySet) :
    arithmeticHom (cardinality unitPrices tree).2 = tree.numNodes + KeySet.cardinal tree := by
  rw [cardinality_arithmetic, unitPrices, Cardinality.arithmeticWork_unit, Cardinality.occupiedCount_id]

theorem insertSet_structural (key : PosNum) (tree : KeySet) :
    structuralHom (insertSet key tree).2 = 2 * bitLength key := by
  change (Finite.setAddRun key tree).2.1 + (Finite.setAddRun key tree).2.2 = _
  rw [Finite.setAddRun_cost]
  omega

@[simp] theorem lookup_arithmetic (key : PosNum) (tree : SparseMap α) :
    arithmeticHom (lookup key tree).2 = 0 := rfl
@[simp] theorem insertMap_arithmetic (key : PosNum) (value : α) (tree : SparseMap α) :
    arithmeticHom (insertMap key value tree).2 = 0 := rfl
@[simp] theorem insertSet_arithmetic (key : PosNum) (tree : KeySet) :
    arithmeticHom (insertSet key tree).2 = 0 := rfl
@[simp] theorem eraseMap_arithmetic (key : PosNum) (tree : SparseMap α) :
    arithmeticHom (eraseMap key tree).2 = 0 := rfl
@[simp] theorem eraseSet_arithmetic (key : PosNum) (tree : KeySet) :
    arithmeticHom (eraseSet key tree).2 = 0 := rfl
@[simp] theorem difference_arithmetic (left right : KeySet) :
    arithmeticHom (difference left right).2 = 0 := rfl
@[simp] theorem choose_arithmetic (tree : KeySet) : arithmeticHom (choose tree).2 = 0 := rfl

@[simp] theorem lookup_count (event : Event) (key : PosNum) (tree : SparseMap α) :
    count event (lookup key tree).2 = 0 := rfl
@[simp] theorem insertMap_count (event : Event) (key : PosNum) (value : α) (tree : SparseMap α) :
    count event (insertMap key value tree).2 = 0 := rfl
@[simp] theorem insertSet_count (event : Event) (key : PosNum) (tree : KeySet) :
    count event (insertSet key tree).2 = 0 := rfl
@[simp] theorem eraseMap_count (event : Event) (key : PosNum) (tree : SparseMap α) :
    count event (eraseMap key tree).2 = 0 := rfl
@[simp] theorem eraseSet_count (event : Event) (key : PosNum) (tree : KeySet) :
    count event (eraseSet key tree).2 = 0 := rfl
@[simp] theorem difference_count (event : Event) (left right : KeySet) :
    count event (difference left right).2 = 0 := rfl
@[simp] theorem choose_count (event : Event) (tree : KeySet) : count event (choose tree).2 = 0 := rfl
@[simp] theorem cardinality_count (event : Event) (prices : Prices) (tree : KeySet) :
    count event (cardinality prices tree).2 = 0 := rfl

theorem run_projection (projection : Cost →+ Nat) (callback : α → σ → Measured σ Cost)
    (bill : α → Nat) (law : ∀ x state, projection (callback x state).2 = bill x)
    (xs : List α) (seed : σ) :
    projection (Resources.run callback xs seed).2 = (xs.map bill).sum := by
  have h := Resources.run_observation (fun x state => reweight projection (callback x state))
    bill law xs seed
  rw [← Resources.reweight_run projection] at h
  exact h

theorem listFold_work_eq (callback : α → σ → Measured σ Cost) (bill : α → Nat)
    (law : ∀ x state, work (callback x state).2 = bill x) (xs : List α) (seed : σ) :
    work (listFold callback xs seed).2 = 2 * xs.length + 1 + (xs.map bill).sum := by
  have h := run_projection workHom callback bill law xs.reverse seed
  change work _ = _ at h
  rw [List.map_reverse, List.sum_reverse] at h
  rw [listFold_cost]
  simp only [work_add, work_structural, work_mark, Nat.add_zero, h]

theorem setFold_arithmetic_zero (callback : PosNum → σ → Measured σ Cost)
    (law : ∀ key state, arithmeticHom (callback key state).2 = 0) (tree : KeySet) (seed : σ) :
    arithmeticHom (setFold callback tree seed).2 = 0 := by
  have h := run_projection arithmeticHom callback (fun _ => 0) law (KeySet.elements tree) seed
  simp only [List.map_const', List.sum_replicate_nat, Nat.mul_zero] at h
  simp only [setFold_cost, map_add, arithmeticHom_structural, Nat.zero_add, h]

theorem listFold_arithmetic_zero (callback : α → σ → Measured σ Cost)
    (law : ∀ x state, arithmeticHom (callback x state).2 = 0) (xs : List α) (seed : σ) :
    arithmeticHom (listFold callback xs seed).2 = 0 := by
  have h := run_projection arithmeticHom callback (fun _ => 0) law xs.reverse seed
  simp only [List.map_const', List.sum_replicate_nat, Nat.mul_zero] at h
  simp only [listFold_cost, map_add, arithmeticHom_structural, arithmeticHom_mark, Nat.zero_add, h]

theorem mapFold_count (event : Event) (callback : PosNum → α → σ → Measured σ Cost)
    (tree : SparseMap α) (seed : σ) :
    count event (mapFold callback tree seed).2 =
      count event (Resources.run (fun entry state => callback entry.1 entry.2 state)
        (SparseMap.elements tree) seed).2 := by
  rw [mapFold_cost]
  simp only [count_add, count_structural, Nat.zero_add]

theorem setFold_count (event : Event) (callback : PosNum → σ → Measured σ Cost)
    (tree : KeySet) (seed : σ) :
    count event (setFold callback tree seed).2 =
      count event (Resources.run callback (KeySet.elements tree) seed).2 := by
  rw [setFold_cost]
  simp only [count_add, count_structural, Nat.zero_add]

theorem listFold_count (event : Event) (callback : α → σ → Measured σ Cost)
    (xs : List α) (seed : σ) :
    count event (listFold callback xs seed).2 =
      (if event = .listEntry then xs.length + 1 else 0) +
      (if event = .listCallback then xs.length else 0) +
      count event (Resources.run callback xs.reverse seed).2 := by
  rw [listFold_cost]
  simp only [count_add, count_structural, count_mark, Nat.zero_add]

theorem listFold_count_nil (event : Event) (callback : α → σ → Measured σ Cost) (seed : σ) :
    count event (listFold callback [] seed).2 = if event = .listEntry then 1 else 0 := by
  rw [listFold_count]
  simp only [List.length_nil, List.reverse_nil, Resources.run_nil, count_zero,
    Nat.zero_add, Nat.add_zero, ite_self]

theorem listFold_count_cons (event : Event) (callback : α → σ → Measured σ Cost)
    (x : α) (xs : List α) (seed : σ) :
    count event (listFold callback (x :: xs) seed).2 =
      (if event = .listEntry then 1 else 0) + (if event = .listCallback then 1 else 0) +
      count event (listFold callback xs seed).2 +
      count event (callback x (listFold callback xs seed).1).2 := by
  simp only [listFold, reweight, ListExecution.MeasuredFold.run_cons, count, structural, mark,
    Prod.snd_add, Pi.add_apply]
  split_ifs <;> omega

theorem valueMap_observations_projection (projection : Cost →+ Nat)
    (callback : α → Measured σ Cost) (tree : SparseMap α) :
    projection (ValueMap.observations callback tree) =
      ValueMap.observations (fun value => reweight projection (callback value)) tree := by
  induction tree with
  | nil => exact map_zero projection
  | node value left right ihl ihr =>
      cases value <;> simp only [ValueMap.observations, ValueMap.payloadRun, map_add,
        map_zero, reweight, ihl, ihr]

theorem valueMap_work_le (callback : α → Measured σ Cost) (tree : SparseMap α) (bound : Nat)
    (bounded : ∀ key value, SparseMap.find key tree = some value → work (callback value).2 ≤ bound) :
    work (valueMap callback tree).2 ≤
      3 * tree.numNodes + SparseMap.cardinal tree + 1 + SparseMap.cardinal tree * bound := by
  have h := ValueMap.observations_le (fun value => reweight workHom (callback value)) tree bound bounded
  have hp := valueMap_observations_projection workHom callback tree
  change work (ValueMap.observations callback tree) = _ at hp
  calc
    _ = 3 * tree.numNodes + SparseMap.cardinal tree + 1 +
        work (ValueMap.observations callback tree) := by
      simp only [valueMap, reweight, work_add, work_structural, ValueMap.run_calls,
        ValueMap.run_callbacks, ValueMap.run_nodes, ValueMap.run_observations]
      omega
    _ ≤ _ := Nat.add_le_add_left (by rw [hp]; exact h) _

theorem valueMap_count_eq (event : Event) (callback : α → Measured σ Cost)
    (tree : SparseMap α) (bill : Nat)
    (law : ∀ key value, SparseMap.find key tree = some value → count event (callback value).2 = bill) :
    count event (valueMap callback tree).2 = SparseMap.cardinal tree * bill := by
  have obs : count event (ValueMap.observations callback tree) = SparseMap.cardinal tree * bill := by
    induction tree with
    | nil => simp only [ValueMap.observations, count_zero, SparseMap.cardinal, Nat.zero_mul]
    | node value left right ihl ihr =>
        have hl := ihl (fun key value found => law (.bit0 key) value found)
        have hr := ihr (fun key value found => law (.bit1 key) value found)
        cases value with
        | none =>
            simp only [ValueMap.observations, ValueMap.payloadRun, count_add, count_zero,
              Nat.zero_add, hl, hr, SparseMap.cardinal, Nat.add_mul]
        | some value =>
            have hv := law .one value rfl
            simp only [ValueMap.observations, ValueMap.payloadRun, count_add,
              hv, hl, hr, SparseMap.cardinal, Nat.add_mul, Nat.one_mul]
            omega
  simpa only [valueMap, reweight, count_add, count_structural, Nat.zero_add,
    ValueMap.run_observations] using obs

theorem valueMap_arithmetic_zero (callback : α → Measured σ Cost)
    (law : ∀ value, arithmeticHom (callback value).2 = 0) (tree : SparseMap α) :
    arithmeticHom (valueMap callback tree).2 = 0 := by
  have obs : arithmeticHom (ValueMap.observations callback tree) = 0 := by
    induction tree with
    | nil => exact map_zero arithmeticHom
    | node value left right ihl ihr =>
        cases value <;> simp only [ValueMap.observations, ValueMap.payloadRun, map_add,
          map_zero, law, ihl, ihr, Nat.zero_add]
  simp only [valueMap, reweight, map_add, arithmeticHom_structural, Nat.zero_add,
    ValueMap.run_observations, obs]

end Resources.Coloring
