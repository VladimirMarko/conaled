import Applications.Search.OrderedMap.Enumeration
import Applications.Search.OrderedMap.AssociationList
import Applications.Search.OrderedMap.TotalTable
import Mathlib.Data.List.Range

/-!
# Finite build/query workloads for the source unbalanced table

Chronological writes use the existing `bindAll` executor. Queries retain optional
bindings until a caller explicitly requests a default. The independent finite
model is the existing first-match list lookup on reversed chronological writes.
Repeated keys therefore keep their final value; a missing binding remains
different from a stored default.

The Extract companion program specializes this client to inserted payload 1,
lookup default 0, and a hit exactly when the observed value is 1. Its build and
query key lists are arbitrary finite lists: duplicates and absent queries are
allowed. Random generation, clocks, representation conversion and resource
measurements are separate clients of this pure contract. `expectedHits` uses
only decidable equality and membership in the original insertion history.

`sourceIndices` represents the companion program's descending loop indices
using an ordinary reversed range. Mapping its consecutive generator gives the
chronological key list `List.range n`; it introduces no second history executor.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Search.OrderedMap.Workload
universe u v w
variable {κ : Type u} {ν : Type v} {M : Type w}

/-- The independent finite reference model retains chronological last writes. -/
def model [DecidableEq κ] (writes : List (κ × ν)) (query : κ) : Option ν :=
  listLookup query writes.reverse

theorem bindAll_append (ops : Ops κ ν M) (first second : List (κ × ν)) (state : M) :
    bindAll ops (first ++ second) state = bindAll ops second (bindAll ops first state) := by
  induction first generalizing state with
  | nil => rfl
  | cons binding rest ih => exact ih (ops.bind binding.1 binding.2 state)

def sourceWrites (keys : List κ) : List (κ × Nat) := keys.map (fun key => (key, 1))

/-- The companion ML program visits `n, n-1, ..., 1`, stopping before zero.
This is an ordinary list schedule for the existing chronological executor. -/
def sourceIndices (n : Nat) : List Nat := (List.range' 1 n).reverse

@[simp] theorem sourceIndices_zero : sourceIndices 0 = [] := rfl

/-- At a positive index, execute that index first, then the remaining schedule. -/
theorem sourceIndices_succ (n : Nat) :
    sourceIndices (n + 1) = (n + 1) :: sourceIndices n := by
  simp [sourceIndices, List.range'_1_concat, List.reverse_append, Nat.add_comm]

@[simp] theorem sourceIndices_length (n : Nat) : (sourceIndices n).length = n := by
  simp [sourceIndices]

theorem mem_sourceIndices (n j : Nat) : j ∈ sourceIndices n ↔ 0 < j ∧ j ≤ n := by
  simp only [sourceIndices, List.mem_reverse, List.mem_range'_1]
  omega

/-- For the source's deterministic consecutive generator `f j = n-j`, both
descending-index phases produce the ascending keys `0, ..., n-1`. -/
theorem sourceIndices_consecutive (n : Nat) :
    (sourceIndices n).map (fun j => n - j) = List.range n := by
  rw [sourceIndices, List.reverse_range', List.map_map]
  calc
    (List.range n).map ((fun j => n - j) ∘ (fun i => 1 + n - 1 - i)) =
        (List.range n).map id := by
      apply List.map_congr_left
      intro k member
      have inside := List.mem_range.mp member
      dsimp
      omega
    _ = List.range n := List.map_id (List.range n)

/-- Independent membership check; duplicate queries are counted separately.
No key ordering, tree lookup, randomness, or timing premise is used. -/
def expectedHits [DecidableEq κ] (inserted queries : List κ) : Nat :=
  (queries.filter (fun query => decide (query ∈ inserted))).length

theorem listLookup_constant [DecidableEq κ] (keys : List κ) (value : ν) (query : κ) :
    listLookup query (keys.map (fun key => (key, value))) =
      if query ∈ keys then some value else none := by
  induction keys with
  | nil => rfl
  | cons key keys ih =>
      by_cases same : query = key
      · simp [listLookup, same]
      · simp [listLookup, same, ih]

section Ordered
variable [LinearOrder κ]

def buildFrom (writes : List (κ × ν)) (tree : BinaryTree (κ × ν)) : BinaryTree (κ × ν) :=
  bindAll (rawTrees κ ν) writes tree

def build (writes : List (κ × ν)) : BinaryTree (κ × ν) := buildFrom writes .nil

def queryResults (queries : List κ) (tree : BinaryTree (κ × ν)) : List (Option ν) :=
  queries.map (fun query => lookup query tree)

def queryValues (default : ν) (queries : List κ) (tree : BinaryTree (κ × ν)) : List ν :=
  queries.map (fun query => (lookup query tree).getD default)

@[simp] theorem buildFrom_nil (tree : BinaryTree (κ × ν)) : buildFrom [] tree = tree := rfl

theorem buildFrom_cons (key : κ) (value : ν) (rest : List (κ × ν))
    (tree : BinaryTree (κ × ν)) :
    buildFrom ((key, value) :: rest) tree = buildFrom rest (bind key value tree) := rfl

theorem buildFrom_append (first second : List (κ × ν)) (tree : BinaryTree (κ × ν)) :
    buildFrom (first ++ second) tree = buildFrom second (buildFrom first tree) :=
  bindAll_append _ first second tree

theorem build_snoc (writes : List (κ × ν)) (key : κ) (value : ν) :
    build (writes ++ [(key, value)]) = bind key value (build writes) :=
  buildFrom_append writes [(key, value)] .nil

theorem buildFrom_eq_setAll (default : ν) (writes : List (κ × ν))
    (tree : BinaryTree (κ × ν)) :
    buildFrom writes tree =
      TotalTable.setAll (TotalTable.ofPartial (rawTrees κ ν) default) writes tree :=
  (TotalTable.setAll_ofPartial _ default writes tree).symm

theorem buildFrom_lookup (writes : List (κ × ν)) (tree : BinaryTree (κ × ν)) (query : κ) :
    lookup query (buildFrom writes tree) = writeAll writes (pathObserve tree) query :=
  rawTrees_laws.lookup_bindAll writes tree query

theorem build_lookup (writes : List (κ × ν)) (query : κ) :
    lookup query (build writes) = model writes query := by
  have execution := buildFrom_lookup writes (.nil : BinaryTree (κ × ν)) query
  have reference := listObserve_reverse_append writes ([] : List (κ × ν))
  have point := congrFun reference query
  simpa only [build, pathObserve, lookup, List.append_nil, listObserve, listLookup, model]
    using execution.trans point.symm

theorem queryResults_model (writes : List (κ × ν)) (queries : List κ) :
    queryResults queries (build writes) = queries.map (model writes) := by
  simp only [queryResults, build_lookup]

theorem queryValues_model (default : ν) (writes : List (κ × ν)) (queries : List κ) :
    queryValues default queries (build writes) =
      queries.map (fun query => (model writes query).getD default) := by
  simp only [queryValues, build_lookup]

theorem buildFrom_ordered (writes : List (κ × ν)) (tree : BinaryTree (κ × ν))
    (ordered : Search.OrderedTree.OrderedBy Prod.fst tree) :
    Search.OrderedTree.OrderedBy Prod.fst (buildFrom writes tree) := by
  induction writes generalizing tree with
  | nil => exact ordered
  | cons binding rest ih =>
      exact ih _ (ordered_bind ordered binding.1 binding.2)

theorem build_ordered (writes : List (κ × ν)) :
    Search.OrderedTree.OrderedBy Prod.fst (build writes) :=
  buildFrom_ordered writes .nil trivial

theorem build_entries_lookup (writes : List (κ × ν)) (key : κ) (value : ν) :
    (key, value) ∈ Search.OrderedTree.entries (build writes) ↔ model writes key = some value := by
  rw [← lookup_eq_some_iff_mem_entries (build_ordered writes), build_lookup]

theorem build_entries_keys_nodup (writes : List (κ × ν)) :
    ((Search.OrderedTree.entries (build writes)).map Prod.fst).Nodup :=
  ordered_entries_keys_nodup (build_ordered writes)

theorem build_entries_keys_sorted (writes : List (κ × ν)) :
    ((Search.OrderedTree.entries (build writes)).map Prod.fst).Pairwise (· < ·) :=
  ordered_entries_keys_pairwise (build_ordered writes)

def buildKeys (keys : List κ) : BinaryTree (κ × Nat) := build (sourceWrites keys)

def queryHits (queries : List κ) (tree : BinaryTree (κ × Nat)) : Nat :=
  (queryValues 0 queries tree).count 1

def hits (inserted queries : List κ) : Nat := queryHits queries (buildKeys inserted)

theorem buildKeys_lookup (inserted : List κ) (query : κ) :
    lookup query (buildKeys inserted) = if query ∈ inserted then some 1 else none := by
  rw [buildKeys, build_lookup]
  simp only [model, sourceWrites, ← List.map_reverse, listLookup_constant, List.mem_reverse]

theorem buildKeys_ordered (inserted : List κ) :
    Search.OrderedTree.OrderedBy Prod.fst (buildKeys inserted) :=
  build_ordered (sourceWrites inserted)

theorem buildKeys_bound (inserted : List κ) (query : κ) :
    (lookup query (buildKeys inserted)).isSome = decide (query ∈ inserted) := by
  rw [buildKeys_lookup]
  split <;> simp_all

theorem buildKeys_elements_mem (inserted : List κ) (key : κ) (value : Nat) :
    (key, value) ∈ Search.OrderedTree.entries (buildKeys inserted) ↔
      key ∈ inserted ∧ value = 1 := by
  rw [← lookup_eq_some_iff_mem_entries (buildKeys_ordered inserted), buildKeys_lookup]
  by_cases present : key ∈ inserted <;> simp [present, eq_comm]

theorem queryValues_source (inserted queries : List κ) :
    queryValues 0 queries (buildKeys inserted) =
      queries.map (fun query => if query ∈ inserted then 1 else 0) := by
  unfold queryValues
  apply List.map_congr_left
  intro query _
  rw [buildKeys_lookup]
  split <;> rfl

theorem hits_eq_expected (inserted queries : List κ) :
    hits inserted queries = expectedHits inserted queries := by
  unfold hits queryHits
  rw [queryValues_source]
  induction queries with
  | nil => rfl
  | cons query queries ih =>
      by_cases present : query ∈ inserted <;>
        simp_all [expectedHits, Nat.add_comm]

theorem hits_all (inserted queries : List κ) (present : ∀ query ∈ queries, query ∈ inserted) :
    hits inserted queries = queries.length := by
  rw [hits_eq_expected]
  unfold expectedHits
  congr 1
  exact List.filter_eq_self.mpr (fun query member => decide_eq_true (present query member))

theorem hits_self (inserted : List κ) : hits inserted inserted = inserted.length :=
  hits_all inserted inserted (fun _ member => member)

theorem hits_le_queries (inserted queries : List κ) : hits inserted queries ≤ queries.length := by
  rw [hits_eq_expected]
  exact List.length_filter_le _ _

theorem source_consecutive_hits (n : Nat) : hits (List.range n) (List.range n) = n := by
  simpa using hits_self (List.range n)

/-- The actual source index order and consecutive generator feed the existing
build/query client. This does not assert that independently drawn queries hit. -/
theorem source_schedule_hits (n : Nat) :
    hits ((sourceIndices n).map (fun j => n - j))
      ((sourceIndices n).map (fun j => n - j)) = n := by
  rw [sourceIndices_consecutive]
  exact source_consecutive_hits n

end Ordered
end Search.OrderedMap.Workload
