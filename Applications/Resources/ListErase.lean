import Applications.Resources.Measured
import Applications.Search.OrderedMap.AssociationListEnumeration

/-!
# First-match erasure and unique-list update comparisons

The VFA ADT chapter's final list table has unique keys, but no key ordering.
Its update prepends the new binding after erasing the first old occurrence.
This realization counts one predicate invocation at each inspected list cell;
it stops at the first match and returns the actual reconstructed suffix.
Predicate internals, allocation, and native execution time are not counted.

The generic erasure also applies to raw lists with repeated keys. The subtype
adapter packages its actual returned list using the existing uniqueness proof;
it does not execute the pair/Sigma proof conversion used by the map owner.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.ListErase
universe u v w
variable {α : Type u} {κ : Type v} {ν : Type w}

/-- One Boolean predicate call per visited cell; a successful call stops. -/
def run (predicate : α → Bool) : List α → Measured (List α) Nat
  | [] => ([], 0)
  | value :: rest =>
      if predicate value then (rest, 1)
      else
        let result := run predicate rest
        (value :: result.1, result.2 + 1)

@[simp] theorem run_nil (predicate : α → Bool) : run predicate [] = ([], 0) := rfl

theorem run_cons (predicate : α → Bool) (value : α) (rest : List α) :
    run predicate (value :: rest) =
      if predicate value then (rest, 1)
      else (value :: (run predicate rest).1, (run predicate rest).2 + 1) := rfl

theorem run_value (predicate : α → Bool) (values : List α) :
    (run predicate values).1 = values.eraseP predicate := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
      simp only [run_cons, List.eraseP_cons]
      split <;> simp_all

theorem run_comparisons_le (predicate : α → Bool) (values : List α) :
    (run predicate values).2 ≤ values.length := by
  induction values with
  | nil => simp
  | cons value rest ih =>
      simp only [run_cons, List.length_cons]
      split <;> simp_all

/-- An unsuccessful traversal examines every cell and returns the same list. -/
theorem run_absent (predicate : α → Bool) (values : List α)
    (absent : ∀ value ∈ values, predicate value = false) :
    run predicate values = (values, values.length) := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
      have head := absent value (by simp)
      have tail : ∀ value ∈ rest, predicate value = false := by
        intro value member
        exact absent value (by simp [member])
      simp [run_cons, head, ih tail]

theorem run_hit (predicate : α → Bool) (value : α) (rest : List α)
    (hit : predicate value = true) :
    run predicate (value :: rest) = (rest, 1) := by
  simp [run_cons, hit]

/-- The number of calls is precisely the prefix length plus the first hit. -/
theorem run_first_hit (predicate : α → Bool) (before : List α)
    (value : α) (suffix : List α)
    (absent : ∀ item ∈ before, predicate item = false)
    (hit : predicate value = true) :
    run predicate (before ++ value :: suffix) = (before ++ suffix, before.length + 1) := by
  induction before with
  | nil => simpa using run_hit predicate value suffix hit
  | cons item before ih =>
      have head := absent item (by simp)
      have tail : ∀ item ∈ before, predicate item = false := by
        intro item member
        exact absent item (by simp [member])
      simp [run_cons, head, ih tail, Nat.add_assoc]

section DecidableKeys
variable [DecidableEq κ]
open Search.OrderedMap.AssociationListEnumeration

/-- The new head is constructed from the list actually returned by erasure. -/
def pairSetRun (key : κ) (value : ν) (bindings : List (κ × ν)) :
    Measured (List (κ × ν)) Nat :=
  bind (run (fun binding => decide (key = binding.1)) bindings)
    (fun rest => pure ((key, value) :: rest))

theorem pairSetRun_value (key : κ) (value : ν) (bindings : List (κ × ν)) :
    (pairSetRun key value bindings).1 = pairSet key value bindings := by
  simp [pairSetRun, pure, run_value, pairSet]

theorem pairSetRun_comparisons (key : κ) (value : ν) (bindings : List (κ × ν)) :
    (pairSetRun key value bindings).2 =
      (run (fun binding => decide (key = binding.1)) bindings).2 := by
  simp [pairSetRun, bind, pure]

theorem pairSetRun_comparisons_le (key : κ) (value : ν) (bindings : List (κ × ν)) :
    (pairSetRun key value bindings).2 ≤ bindings.length := by
  rw [pairSetRun_comparisons]
  exact run_comparisons_le _ _

theorem pairSetRun_absent (key : κ) (value : ν) (bindings : List (κ × ν))
    (absent : ∀ binding ∈ bindings, key ≠ binding.1) :
    pairSetRun key value bindings = ((key, value) :: bindings, bindings.length) := by
  have noHit : ∀ binding ∈ bindings, decide (key = binding.1) = false := by
    intro binding member
    exact decide_eq_false (absent binding member)
  simp [pairSetRun, run_absent _ _ noHit, bind, pure]

theorem pairSetRun_front (key : κ) (old value : ν) (rest : List (κ × ν)) :
    pairSetRun key value ((key, old) :: rest) = ((key, value) :: rest, 1) := by
  simp [pairSetRun, run_cons, bind, pure]

/-- The subtype contains the measured output, with the existing invariant proof. -/
def setRun (key : κ) (value : ν) (bindings : UniqueList κ ν) :
    Measured (UniqueList κ ν) Nat :=
  let result := pairSetRun key value bindings.1
  (⟨result.1, by
    change ((pairSetRun key value bindings.1).1.map Prod.fst).Nodup
    rw [pairSetRun_value]
    exact pairSet_nodup key value bindings.2⟩, result.2)

theorem setRun_value (key : κ) (value : ν) (bindings : UniqueList κ ν) :
    (setRun key value bindings).1 = set key value bindings := by
  apply Subtype.ext
  exact pairSetRun_value key value bindings.1

theorem setRun_entries (key : κ) (value : ν) (bindings : UniqueList κ ν) :
    (setRun key value bindings).1.1 = (pairSetRun key value bindings.1).1 := rfl

theorem setRun_comparisons (key : κ) (value : ν) (bindings : UniqueList κ ν) :
    (setRun key value bindings).2 = (pairSetRun key value bindings.1).2 := rfl

theorem setRun_comparisons_le (key : κ) (value : ν) (bindings : UniqueList κ ν) :
    (setRun key value bindings).2 ≤ bindings.1.length :=
  pairSetRun_comparisons_le key value bindings.1

theorem setRun_absent_comparisons (key : κ) (value : ν) (bindings : UniqueList κ ν)
    (absent : ∀ binding ∈ bindings.1, key ≠ binding.1) :
    (setRun key value bindings).2 = bindings.1.length := by
  rw [setRun_comparisons, pairSetRun_absent key value bindings.1 absent]

theorem setRun_toAList (key : κ) (value : ν) (bindings : UniqueList κ ν) :
    toAList (setRun key value bindings).1 = AList.insert key value (toAList bindings) := by
  rw [setRun_value, toAList_set]

/-- Both interfaces expose the same update result; the cost is additional data. -/
def pairSetSquare (key : κ) (value : ν) :=
  erasureSquare (pairSetRun key value) (pairSet key value) (pairSetRun_value key value)

def setSquare (key : κ) (value : ν) :=
  erasureSquare (setRun key value) (set key value) (setRun_value key value)

end DecidableKeys
end Resources.ListErase
