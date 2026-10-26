import Applications.Huffman.SourcePriority
import Applications.Optimization.Relations

/-! The tree consumer retains occurrences; the cost consumer forgets only its witness. -/
set_option autoImplicit false
set_option warningAsError true
namespace Huffman
open Bracketing Search.PriorityInterface
universe u z z'
variable {α : Type u}

theorem optimal_cost_unique (w : α → Nat) (xs : List α) (t s : Tree α)
    (ht : Optimal w xs t) (hs : Optimal w xs s) : pathCost w 0 t = pathCost w 0 s :=
  Nat.le_antisymm (ht.2 s hs.1) (hs.2 t ht.1)

namespace Priority
variable (Q : ExactQueue.{u,0,z} (Tree α) Nat)

theorem huffman_singleton (w : α → Nat) (a : α) : huffman Q w [a] = some (.leaf a) := by
  obtain ⟨t, ht, ho⟩ := huffman_optimal Q w [a] (by simp)
  have hf : fringeSpec t = [a] := by simpa [Feasible] using ho.1
  rw [(fringe_singleton_iff t a).mp hf] at ht
  exact ht

def costResult (w : α → Nat) (xs : List α) : Option Nat :=
  (huffman Q w xs).map (pathCost w 0)

theorem costResult_attained (w : α → Nat) (xs : List α) (n : Nat)
    (h : costResult Q w xs = some n) :
    ∃ t, huffman Q w xs = some t ∧ Optimal w xs t ∧ pathCost w 0 t = n := by
  obtain ⟨t, ht, he⟩ := Option.map_eq_some_iff.mp h
  exact ⟨t, ht, huffman_correct Q w xs t ht, he⟩

/-- Two implementations agree on costs, with no equality requirement on chosen trees. -/
theorem costResult_eq (R : ExactQueue.{u,0,z'} (Tree α) Nat) (w : α → Nat) (xs : List α) :
    costResult Q w xs = costResult R w xs := by
  by_cases hx : xs = []
  · simp [costResult, (huffman_none_iff Q w xs).mpr hx, (huffman_none_iff R w xs).mpr hx]
  · obtain ⟨t, ht, ho⟩ := huffman_optimal Q w xs hx
    obtain ⟨s, hs, hp⟩ := huffman_optimal R w xs hx
    simp only [costResult, ht, hs, Option.map_some]
    exact congrArg some (optimal_cost_unique w xs t s ho hp)
end Priority

/-- Independent permissible results, including the empty-input branch. -/
def ResultSpec (w : α → Nat) (xs : List α) : Option (Tree α) → Prop
  | none => xs = []
  | some t => Optimal w xs t

theorem resultSpec_correct (Q : ExactQueue.{u,0,z} (Tree α) Nat)
    (w : α → Nat) (xs : List α) : ResultSpec w xs (Priority.huffman Q w xs) := by
  cases h : Priority.huffman Q w xs with
  | none => exact (Priority.huffman_none_iff Q w xs).mp h
  | some t => exact Priority.huffman_correct Q w xs t h

/- The square framework fixes one universe for all representations. Lifting the
numeric observation preserves the tree algorithm's arbitrary label universe. -/
def treeSquare (Q : ExactQueue.{u,0,z} (Tree α) Nat) (w : α → Nat) :
    Relational.RelSquare (Optimization.inputRep (List α))
      (Optimization.membershipRep (I := List α) (id : Option (Tree α) → Option (Tree α))) where
  impl xs := (xs, Priority.huffman Q w xs)
  spec xs := (xs, {t | ResultSpec w xs t})
  preserves := by
    rintro xs _ rfl
    exact ⟨rfl, resultSpec_correct Q w xs⟩

def liftedCost (w : α → Nat) : Option (Tree α) → Option (ULift.{u} Nat) :=
  Option.map (fun t => ULift.up (pathCost w 0 t))

def costSquare (Q : ExactQueue.{u,0,z} (Tree α) Nat) (w : α → Nat) :
    Relational.RelSquare (Optimization.inputRep (List α))
      (Optimization.membershipRep (I := List α)
        (id : Option (ULift.{u} Nat) → Option (ULift.{u} Nat))) :=
  Relational.compose (Optimization.observationSquare (liftedCost w)) (treeSquare Q w)

theorem costSquare_impl (Q : ExactQueue.{u,0,z} (Tree α) Nat) (w : α → Nat) (xs : List α) :
    (costSquare Q w).impl xs = (xs, (Priority.costResult Q w xs).map ULift.up) := by
  simp [costSquare, treeSquare, Relational.compose, Optimization.observationSquare,
    liftedCost, Priority.costResult, Option.map_map, Function.comp_def]
  rfl

/-- Actual composition supplies an admissible witness for every observed cost. -/
theorem costSquare_permitted (Q : ExactQueue.{u,0,z} (Tree α) Nat) (w : α → Nat) (xs : List α) :
    ∃ result, ResultSpec w xs result ∧ liftedCost w result = ((costSquare Q w).impl xs).2 :=
  ((costSquare Q w).preserves (r := xs) (s := xs) rfl).2
end Huffman
