import Applications.Resources.TreeFlattening.Cached
import Applications.Resources.RandomAccess.EndObservation

/-! Actual flattening outputs feed suffix copying and fresh random-access construction.
Semantic decoding is separate from the operation counts. -/
set_option autoImplicit false
set_option warningAsError true
namespace Resources.TreeFlattening
open RandomAccess RandomAccessCosts Squares
universe u
variable {α : Type u}

def forestRepresentation (α : Type u) : Rep.{u} :=
  ⟨List (Tree α), List α, fun ts => ts.flatMap fromT⟩

def treeRepresentation (α : Type u) : Rep.{u} := ⟨Tree α, List α, fromT⟩

def stackSquare : Square (forestRepresentation α) (measuredSequence α) where
  impl := cachedFromTsWithCost
  spec := id
  commutes ts := congrArg Prod.fst (cachedFromTsWithCost_exact ts)

def recursiveSquare : Square (treeRepresentation α) (measuredSequence α) where
  impl := cachedFromTWithCost
  spec := id
  commutes := cachedFromTWithCost_value

def stackTreeSquare : Square (treeRepresentation α) (measuredSequence α) where
  impl t := cachedFromTsWithCost [t]
  spec := id
  commutes t := by
    change (cachedFromTsWithCost [t]).1 = fromT t
    rw [cachedFromTsWithCost_exact]; exact List.append_nil (fromT t)

def appendSquare (suffix : List α) : Square (measuredSequence α) (measuredSequence α) where
  impl result := bind result (fun xs => appendWithCost xs suffix)
  spec (xs : List α) := xs ++ suffix
  commutes result := congrArg Prod.fst (appendWithCost_exact result.1 suffix)

/-- Materialize the actual forest traversal, then copy that output onto a suffix. -/
def flattenAppend (suffix : List α) := Squares.compose (appendSquare suffix) stackSquare

theorem flattenAppend_value (ts : List (Tree α)) (suffix : List α) :
    ((flattenAppend suffix).impl ts).1 = ts.flatMap fromT ++ suffix :=
  (flattenAppend suffix).commutes ts

theorem flattenAppend_cost (ts : List (Tree α)) (suffix : List α) :
    ((flattenAppend suffix).impl ts).2 = pending (ts.map erase) + 1 + (ts.flatMap fromT).length := by
  change (cachedFromTsWithCost ts).2 + (appendWithCost (cachedFromTsWithCost ts).1 suffix).2 = _
  rw [cachedFromTsWithCost_exact, appendWithCost_exact]

/-- Existing construction consumes the preceding measured sequence and adds its work. -/
def measuredConstructionSquare : Square (measuredSequence α) (measuredRepresentation α) where
  impl result := bind result constructionSquare.impl
  spec := id
  commutes result := constructionSquare.commutes result.1

/-- Both flattening algorithms plug into the same construction/query consumer. -/
def flattenQuery (flatten : Square (treeRepresentation α) (measuredSequence α)) (query : Nat) :=
  Squares.compose (measuredLookupSquare query) (Squares.compose measuredConstructionSquare flatten)

theorem flattenQuery_value (flatten : Square (treeRepresentation α) (measuredSequence α))
    (query : Nat) (t : Tree α) :
    ((flattenQuery flatten query).impl t).1 = (show List α from flatten.spec (fromT t))[query]? :=
  (flattenQuery flatten query).commutes t

theorem flattenQuery_cost (flatten : Square (treeRepresentation α) (measuredSequence α))
    (query : Nat) (t : Tree α) :
    ((flattenQuery flatten query).impl t).2 = (flatten.impl t).2 +
      (toRARun (flatten.impl t).1).2 +
      (fetchRARun query (toRARun (flatten.impl t).1).1).2 := rfl

/-- The two executions agree on the queried sequence, without requiring equal work. -/
theorem flattenQuery_agreement (query : Nat) (t : Tree α) :
    ((flattenQuery recursiveSquare query).impl t).1 =
      ((flattenQuery stackTreeSquare query).impl t).1 := by
  rw [flattenQuery_value, flattenQuery_value]
  rfl

end Resources.TreeFlattening
