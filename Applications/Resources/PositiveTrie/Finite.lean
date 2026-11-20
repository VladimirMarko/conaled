import Applications.Resources.PositiveTrie
import Applications.Search.PositiveTrie.Finite

/-!
# Exact optional-map and Boolean-set path resource adapters

These wrappers use the existing actual raw lookup and insertion executors.
The coordinates still count entered raw calls and constructed tree nodes;
the wrappers have zero additional tariff. Pruning erasure, traversal,
arithmetic, conversion and output costs are separate obligations.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Resources.PositiveTrie.Finite

open Search.PositiveTrie Numerals.PositiveArithmetic

universe u
variable {α : Type u}

def findRun (key : PosNum) (tree : SparseMap α) : Measured (Option α) Cost :=
  lookRun none key tree

theorem findRun_value (key : PosNum) (tree : SparseMap α) :
    (findRun key tree).1 = SparseMap.find key tree := lookRun_value none key tree

theorem findRun_calls_le (key : PosNum) (tree : SparseMap α) :
    (findRun key tree).2.1 ≤ bitLength key := lookRun_calls_le none key tree

theorem findRun_constructions (key : PosNum) (tree : SparseMap α) :
    (findRun key tree).2.2 = 0 := lookRun_constructions none key tree

def memRun (key : PosNum) (tree : KeySet) : Measured Bool Cost := lookRun false key tree

theorem memRun_value (key : PosNum) (tree : KeySet) :
    (memRun key tree).1 = KeySet.mem key tree := lookRun_value false key tree

theorem memRun_calls_le (key : PosNum) (tree : KeySet) :
    (memRun key tree).2.1 ≤ bitLength key := lookRun_calls_le false key tree

theorem memRun_constructions (key : PosNum) (tree : KeySet) :
    (memRun key tree).2.2 = 0 := lookRun_constructions false key tree

def mapAddRun (key : PosNum) (value : α) (tree : SparseMap α) :
    Measured (SparseMap α) Cost := insRun none key (some value) tree

theorem mapAddRun_value (key : PosNum) (value : α) (tree : SparseMap α) :
    (mapAddRun key value tree).1 = SparseMap.add key value tree :=
  insRun_value none key (some value) tree

theorem mapAddRun_cost (key : PosNum) (value : α) (tree : SparseMap α) :
    (mapAddRun key value tree).2 = (bitLength key, bitLength key) :=
  insRun_cost none key (some value) tree

def setAddRun (key : PosNum) (tree : KeySet) : Measured KeySet Cost :=
  insRun false key true tree

theorem setAddRun_value (key : PosNum) (tree : KeySet) :
    (setAddRun key tree).1 = KeySet.add key tree := insRun_value false key true tree

theorem setAddRun_cost (key : PosNum) (tree : KeySet) :
    (setAddRun key tree).2 = (bitLength key, bitLength key) := insRun_cost false key true tree

theorem findRun_mapAddRun_value (key : PosNum) (value : α) (tree : SparseMap α) :
    (findRun key (mapAddRun key value tree).1).1 = some value := by
  rw [findRun_value, mapAddRun_value, SparseMap.find_add_same]

theorem findRun_mapAddRun_cost (key : PosNum) (value : α) (tree : SparseMap α) :
    (findRun key (mapAddRun key value tree).1).2 = (bitLength key, 0) := by
  rw [mapAddRun_value]
  exact lookRun_ins_cost none key (some value) tree

theorem memRun_setAddRun_value (key : PosNum) (tree : KeySet) :
    (memRun key (setAddRun key tree).1).1 = true := by
  rw [memRun_value, setAddRun_value, KeySet.mem_add_same]

theorem memRun_setAddRun_cost (key : PosNum) (tree : KeySet) :
    (memRun key (setAddRun key tree).1).2 = (bitLength key, 0) := by
  rw [setAddRun_value]
  exact lookRun_ins_cost false key true tree

theorem mapAdd_find_value (key : PosNum) (value : α) (tree : SparseMap α) :
    (bind (mapAddRun key value tree) (findRun key)).1 = some value :=
  findRun_mapAddRun_value key value tree

theorem mapAdd_find_cost (key : PosNum) (value : α) (tree : SparseMap α) :
    (bind (mapAddRun key value tree) (findRun key)).2 =
      (2 * bitLength key, bitLength key) := by
  simp only [bind, mapAddRun_cost, findRun_mapAddRun_cost, Prod.mk_add_mk,
    Nat.add_zero, two_mul]

theorem setAdd_mem_value (key : PosNum) (tree : KeySet) :
    (bind (setAddRun key tree) (memRun key)).1 = true := memRun_setAddRun_value key tree

theorem setAdd_mem_cost (key : PosNum) (tree : KeySet) :
    (bind (setAddRun key tree) (memRun key)).2 = (2 * bitLength key, bitLength key) := by
  simp only [bind, setAddRun_cost, memRun_setAddRun_cost, Prod.mk_add_mk,
    Nat.add_zero, two_mul]

end Resources.PositiveTrie.Finite
