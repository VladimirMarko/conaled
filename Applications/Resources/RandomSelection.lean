import Applications.Selection.ThreeWay
import Applications.Resources.RandomQuickSort
import Applications.Resources.Partition
import Applications.Resources.SymmetricCosts

/-! An occurrence-pivot selection step with its actual source operations.

The pivot is retrieved by the measured list lookup, the full input is partitioned
once, and only the reached branch's lengths are measured. A left result names the
one recursive state; a right result terminates at the pivot value. The cost counts
one selection entry and the actual length, lookup and partition calls. Abstract
uniform choice has no charge here; this is not a random-bit sampler or a runtime
claim. The source step does not require distinct values or an inhabited payload.

The finite recursive execution and its expectation/tail proofs are developed
separately from this step interface. In particular, a pivot distribution alone
does not establish a randomized-selection complexity theorem.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.RandomSelection
open Applications.Selection
open scoped ENNReal
universe u
variable {α : Type u}

/-- Read a valid occurrence through the existing measured lookup. Its proof
argument removes the impossible failure branch without a fallback payload. -/
def pivotRun (xs : List α) (i : Fin xs.length) : Measured α Nat :=
  let r := ListCalls.lookupRun xs i.val
  (r.1.get (by simp [r, ListCalls.lookupRun_valid xs i.val i.isLt]), r.2)

theorem pivotRun_exact (xs : List α) (i : Fin xs.length) :
    pivotRun xs i = (xs[i.val]'i.isLt, i.val + 1) := by
  simp [pivotRun, ListCalls.lookupRun_valid xs i.val i.isLt]

section Ordered
variable [LinearOrder α]

/-- One active source call. `Sum.inl (j, ys)` is its selected recursive state;
`Sum.inr p` is its direct successful return. The equal length is measured only
after the left test fails. The input length is available for the uniform draw. -/
def stepRun (k : Nat) (xs : List α) (i : Fin xs.length) :
    Measured ((Nat × List α) ⊕ α) Nat :=
  let size := SymmetricCosts.lengthRun xs
  let pivot := pivotRun xs i
  let buckets := Partition.partitionRun pivot.1 xs
  let leftSize := SymmetricCosts.lengthRun buckets.1.1
  let first := 1 + size.2 + pivot.2 + buckets.2 + leftSize.2
  if k < leftSize.1 then (Sum.inl (k, buckets.1.1), first)
  else
    let equalSize := SymmetricCosts.lengthRun buckets.1.2.1
    if k < leftSize.1 + equalSize.1 then
      (Sum.inr pivot.1, first + equalSize.2)
    else (Sum.inl (k - leftSize.1 - equalSize.1, buckets.1.2.2),
      first + equalSize.2)

/-- Exact source accounting, derived from the measured operations. Primitive
comparisons, tuple construction and the abstract index draw add no call here. -/
theorem stepRun_eq (k : Nat) (xs : List α) (i : Fin xs.length) :
    let p := xs[i.val]'i.isLt
    let t := partition3 p xs
    stepRun k xs i =
      if k < t.1.length then
        (Sum.inl (k, t.1), 2 * xs.length + i.val + t.1.length + 5)
      else if k < t.1.length + t.2.1.length then
        (Sum.inr p, 2 * xs.length + i.val + t.1.length + t.2.1.length + 6)
      else (Sum.inl (k - t.1.length - t.2.1.length, t.2.2),
        2 * xs.length + i.val + t.1.length + t.2.1.length + 6) := by
  dsimp only
  simp only [stepRun, pivotRun_exact, SymmetricCosts.lengthRun_exact,
    Partition.partitionRun_value, Partition.partitionRun_cost,
    Applications.Selection.partition3]
  split_ifs with hl he <;> simp_all only [↓reduceIte]
  all_goals first | omega | (apply Prod.ext <;> first | rfl | omega)

/-- Pivot membership supplies decrease; a valid parent rank supplies a valid
child rank. Neither conclusion assumes distinctness of the input values. -/
theorem stepRun_child (k : Nat) (xs : List α) (i : Fin xs.length)
    (j : Nat) (ys : List α) (h : (stepRun k xs i).1 = Sum.inl (j, ys)) :
    ys.length < xs.length ∧ (k < xs.length → j < ys.length) := by
  have hs := partition_strict_sizes (xs[i.val]'i.isLt) xs (List.getElem_mem i.isLt)
  have ht := partition_lengths (xs[i.val]'i.isLt) xs
  rw [stepRun_eq] at h
  split_ifs at h with hl he
  · dsimp only at h
    have hj := congrArg Prod.fst (Sum.inl.inj h)
    have hy := congrArg Prod.snd (Sum.inl.inj h)
    dsimp only at hj hy
    subst j
    subst ys
    exact ⟨hs.1, fun _ => hl⟩
  · dsimp only at h
    have hj := congrArg Prod.fst (Sum.inl.inj h)
    have hy := congrArg Prod.snd (Sum.inl.inj h)
    dsimp only at hj hy
    subst j
    subst ys
    exact ⟨hs.2, fun hk => by omega⟩

private theorem equal_lookup (p : α) (xs : List α) (k : Nat)
    (hl : (partition3 p xs).1.length ≤ k)
    (he : k < (partition3 p xs).1.length + (partition3 p xs).2.1.length) :
    (partition3 p xs).2.1[k - (partition3 p xs).1.length]? = some p := by
  have hi : k - (partition3 p xs).1.length < (partition3 p xs).2.1.length := by omega
  have hp := ((partition_equal_mem p xs
    ((partition3 p xs).2.1[k - (partition3 p xs).1.length]'hi)).mp
      (List.getElem_mem hi)).2
  simp only [List.getElem?_eq_getElem hi, hp]

/-- Completing the one chosen child with its independent order-statistic
specification gives the original input's zero-based order statistic. -/
theorem stepRun_semantics (k : Nat) (xs : List α) (i : Fin xs.length) :
    (match (stepRun k xs i).1 with
      | Sum.inl (j, ys) => (ordered ys)[j]?
      | Sum.inr p => some p) = (ordered xs)[k]? := by
  have h := dispatch_value (fun j ys => (ordered ys)[j]?)
    (xs[i.val]'i.isLt) k xs (fun _ => rfl) (fun _ => rfl)
  rw [stepRun_eq]
  split_ifs with hl he
  · simpa only [dispatch, hl, ↓reduceIte] using h
  · have hp := equal_lookup (xs[i.val]'i.isLt) xs k (by omega) he
    simpa only [dispatch, hl, he, ↓reduceIte, hp] using h
  · simpa only [dispatch, hl, he, ↓reduceIte] using h

/-- The reached equal branch returns a correct occurrence rank, even when
several input occurrences have the same value. -/
theorem stepRun_ranked (k : Nat) (xs : List α) (i : Fin xs.length) (a : α)
    (h : (stepRun k xs i).1 = Sum.inr a) : RankedAt xs k a := by
  have hs := stepRun_semantics k xs i
  rw [h] at hs
  exact ranked_iff_index.mpr hs.symm

/-- Every active step pays between one and nine times its actual size in the
declared call tariff. The bound includes pivot retrieval and length traversals. -/
theorem stepRun_cost_bounds (k : Nat) (xs : List α) (i : Fin xs.length) :
    xs.length ≤ (stepRun k xs i).2 ∧ (stepRun k xs i).2 ≤ 9 * xs.length := by
  have hi := i.isLt
  have ht := partition_lengths (xs[i.val]'i.isLt) xs
  rw [stepRun_eq]
  split_ifs <;> dsimp only <;> constructor <;> omega

end Ordered

noncomputable section

/-- Push the existing uniform occurrence sampler through the actual lookup.
Repeated values retain their occurrence multiplicity. -/
def pivotLaw (head : α) (tail : List α) : PMF α :=
  PMF.map (fun i : Fin (tail.length + 1) => (pivotRun (head :: tail) i).1)
    (RandomQuickSort.uniformIndex tail.length)

theorem pivotLaw_support (head : α) (tail : List α) (a : α)
    (h : a ∈ (pivotLaw head tail).support) : a ∈ head :: tail := by
  obtain ⟨i, _, hi⟩ := (PMF.mem_support_map_iff _ _ _).mp h
  have hm : (head :: tail)[i.val]'i.isLt ∈ head :: tail := List.getElem_mem i.isLt
  rw [pivotRun_exact] at hi
  dsimp only at hi
  rw [← hi]
  exact hm

/-- Event probability counts indexed occurrences. The payload event need only
be Boolean; no measurable space or equality instance on payloads is required. -/
theorem pivotLaw_event (head : α) (tail : List α) (event : α → Bool) :
    PMF.map event (pivotLaw head tail) true =
      ((Finset.univ.filter (fun i : Fin (tail.length + 1) =>
        event ((head :: tail)[i.val]'i.isLt) = true)).card : ℝ≥0∞) /
          ((tail.length + 1 : Nat) : ℝ≥0∞) := by
  rw [pivotLaw, PMF.map_comp]
  simpa only [Function.comp_def, pivotRun_exact] using
    RandomQuickSort.uniformIndex_event tail.length
      (fun i => event ((pivotRun (head :: tail) i).1))

end
end Resources.RandomSelection
