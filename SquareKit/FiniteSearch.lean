import Std

/-!
# Exact-depth finite search

Successors are ordered occurrences. Reaching the same state through two edges
counts twice; a dead end contributes nothing at positive depth. At depth zero
the current state is the sole occurrence. No finiteness of the state type is
required, only a finite successor list at each state.

`count` computes the length observation without constructing the full answer
list. `enumerate_map` transports the ordered specification along any decoder,
including a noninjective one. The source is recorded in
`docs/research/adwh-search-counting.md`.
-/

set_option autoImplicit false
set_option warningAsError true

namespace FiniteSearch

universe u v
variable {State : Type u}

def enumerate (next : State → List State) : Nat → State → List State
  | 0, state => [state]
  | depth + 1, state => (next state).flatMap (enumerate next depth)

/-- Leaf occurrence count at exactly the supplied depth. -/
def count (next : State → List State) : Nat → State → Nat
  | 0, _ => 1
  | depth + 1, state => ((next state).map (count next depth)).sum

theorem count_eq_length (next : State → List State) (depth : Nat) (state : State) :
    count next depth state = (enumerate next depth state).length := by
  induction depth generalizing state with
  | zero => rfl
  | succ depth ih =>
      simp only [count, enumerate, List.length_flatMap]
      apply congrArg List.sum
      apply List.map_congr_left
      intro child _
      exact ih child

theorem enumerate_add (next : State → List State) (depth remaining : Nat) (state : State) :
    enumerate next (depth + remaining) state =
      (enumerate next depth state).flatMap (enumerate next remaining) := by
  induction depth generalizing state with
  | zero => simp [enumerate]
  | succ depth ih =>
      rw [Nat.succ_add]
      simp only [enumerate, List.flatMap_assoc]
      apply congrArg (List.flatMap · (next state))
      funext child
      exact ih child

/-- Splitting at any complete frontier preserves every occurrence. -/
theorem count_partition (next : State → List State) (depth remaining : Nat) (state : State) :
    count next (depth + remaining) state =
      ((enumerate next depth state).map (count next remaining)).sum := by
  rw [count_eq_length, enumerate_add, List.length_flatMap]
  apply congrArg List.sum
  apply List.map_congr_left
  intro child _
  exact (count_eq_length next remaining child).symm

/-- A decoder must preserve successor order and multiplicity, not distinctness. -/
theorem enumerate_map {Target : Type v}
    (next : State → List State) (target : Target → List Target) (decode : State → Target)
    (law : ∀ state, (next state).map decode = target (decode state))
    (depth : Nat) (state : State) :
    (enumerate next depth state).map decode = enumerate target depth (decode state) := by
  induction depth generalizing state with
  | zero => rfl
  | succ depth ih =>
      simp only [enumerate, List.map_flatMap]
      rw [← law state, List.flatMap_map]
      simp only [ih]

/-- Count transport does not require an injective decoder. -/
theorem count_map {Target : Type v}
    (next : State → List State) (target : Target → List Target) (decode : State → Target)
    (law : ∀ state, (next state).map decode = target (decode state))
    (depth : Nat) (state : State) :
    count next depth state = count target depth (decode state) := by
  rw [count_eq_length, count_eq_length, ← enumerate_map next target decode law]
  exact (List.length_map _).symm

/-- A residual backend may decline any query. -/
abbrev Tail (State : Type u) := Nat → State → Option Nat

/-- Every returned answer must equal the count for its actual query. -/
def Exact (next : State → List State) (tail : Tail State) : Prop :=
  ∀ depth state value, tail depth state = some value → value = count next depth state

def countWith (next : State → List State) (tail : Tail State) : Nat → State → Nat
  | 0, _ => 1
  | depth + 1, state =>
      match tail (depth + 1) state with
      | some value => value
      | none => ((next state).map (countWith next tail depth)).sum

theorem countWith_eq_count (next : State → List State) (tail : Tail State)
    (exactTail : Exact next tail) (depth : Nat) (state : State) :
    countWith next tail depth state = count next depth state := by
  induction depth generalizing state with
  | zero => rfl
  | succ depth ih =>
      cases selected : tail (depth + 1) state with
      | some value =>
          simp only [countWith, selected]
          exact exactTail (depth + 1) state value selected
      | none =>
          simp only [countWith, selected, count]
          apply congrArg List.sum
          apply List.map_congr_left
          intro child _
          exact ih child

def noTail : Tail State := fun _ _ => none

theorem noTail_exact (next : State → List State) : Exact next noTail := by
  intro depth state value selected
  cases selected

end FiniteSearch
