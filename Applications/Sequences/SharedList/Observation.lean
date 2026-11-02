import Applications.Sequences.SharedList.Copy

/-! Ordinary relational-square clients for the shared-cell realization.
These adapters retain failure as `Option`; they do not require a total decoder
for malformed heaps or identify different roots with equal observations. -/
set_option autoImplicit false
set_option warningAsError true

namespace Sequences.SharedList
variable {α : Type}

def representation (α : Type) : Relational.RelRep :=
  ⟨Store α × Root, List α, fun state xs => Represents state.1.heap state.2 xs⟩

def optionalRepresentation (α : Type) : Relational.RelRep where
  R := Option (Store α × Root)
  S := Option (List α)
  Rel out value := match out, value with
    | none, none => True
    | some state, some xs => Represents state.1.heap state.2 xs
    | _, _ => False

def appendInput (α : Type) : Relational.RelRep where
  R := Store α × (Root × Root)
  S := List α × List α
  Rel input value := Represents input.1.heap input.2.1 value.1 ∧
    Represents input.1.heap input.2.2 value.2

def appendSquare (α : Type) :
    Relational.RelSquare (appendInput α) (optionalRepresentation α) where
  impl input := (appendRun input.1 input.2.1 input.2.2).1
  spec value := some (value.1 ++ value.2)
  preserves := by
    intro input value h
    obtain ⟨out, run, _, rep, _, _⟩ := appendRun_correct h.1 h.2
    rw [run]
    exact rep

def updateSquare (i : Nat) (x : α) :
    Relational.RelSquare (representation α) (optionalRepresentation α) where
  impl state := (updateRun state.1 state.2 i x).1
  spec xs := updateValue xs i x
  preserves := by
    intro state xs h
    by_cases inside : i < xs.length
    · obtain ⟨out, run, _, rep, _, _⟩ := updateRun_success h inside x
      change (optionalRepresentation α).Rel _ _
      rw [run]
      simp only [optionalRepresentation, updateValue, ite_eq_left inside]
      exact rep
    · have failed := updateRun_failure h (Nat.le_of_not_gt inside) x
      change (optionalRepresentation α).Rel _ _
      rw [failed]
      simp only [optionalRepresentation, updateValue, ite_eq_right inside]

def headSquare (α : Type) : Relational.RelSquare (optionalRepresentation α)
    ⟨Option α, Option α, Eq⟩ where
  impl out := out.bind fun state => head state.1 state.2
  spec value := value.bind List.head?
  preserves := by
    intro out value h
    cases out with
    | none =>
        cases value with
        | none => rfl
        | some xs => exact False.elim h
    | some state =>
        cases value with
        | none => exact False.elim h
        | some xs => exact head_correct h

/-- Compose the independently specified append and optional-head contracts. -/
def appendHeadSquare (α : Type) : Relational.RelSquare (appendInput α)
    ⟨Option α, Option α, Eq⟩ :=
  Relational.compose (headSquare α) (appendSquare α)

theorem appendHead_correct {s : Store α} {r q : Root} {xs ys : List α}
    (hx : Represents s.heap r xs) (hy : Represents s.heap q ys) :
    ((appendRun s r q).1.bind fun state => head state.1 state.2) =
      (xs ++ ys).head? :=
  (appendHeadSquare α).preserves (r := (s, (r, q))) (s := (xs, ys)) ⟨hx, hy⟩

theorem updateHead_correct {s : Store α} {r : Root} {xs : List α}
    (h : Represents s.heap r xs) (i : Nat) (x : α) :
    ((updateRun s r i x).1.bind fun state => head state.1 state.2) =
      (updateValue xs i x).bind List.head? :=
  (Relational.compose (headSquare α) (updateSquare i x)).preserves
    (r := (s, r)) (s := xs) h

end Sequences.SharedList
