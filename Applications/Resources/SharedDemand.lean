import Applications.Resources.Potential
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Logic.Function.Basic

/-! Pure measured callbacks with explicit sharing identities and an option cache.

A miss invokes the callback and stores its value; a hit returns the stored value
without invoking the callback. The observation charges callback work only. Cache
lookup, update and request administration carry no additional charge in this
model. Stable identity means that the same fixed pure callback is used throughout
a run, rather than that equal payloads must share a cache entry.

Only the remaining-work bound needs a finite identity catalogue. Its sum is an
eager-catalogue specification. Applying it to a source program requires a
correspondence: requested identities name that programme's eager computations,
their values are stable, and the sum of their work observations equals its eager
source count. This construction does not supply that simulation for an
unspecified programming language. Provenance: FDSA chapter 1, pp. 7–9;
`docs/research/fdsa-reconstruction-map.md`.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.SharedDemand
universe u v
variable {ι : Type u} {α : Type v}

abbrev Cache (ι : Type u) (α : Type v) := ι → Option α

/-- No payload value, equality or inhabitance is needed for an empty cache. -/
def empty : Cache ι α := fun _ => none

/-- Every stored value belongs to its identity's fixed pure computation. -/
def Valid (compute : ι → Unit → Measured α Nat) (cache : Cache ι α) : Prop :=
  ∀ i a, cache i = some a → a = (compute i ()).1

theorem empty_valid (compute : ι → Unit → Measured α Nat) :
    Valid compute empty := by
  intro i a h
  simp [empty] at h

/-- Return the new cache and demanded value, charging only a cache miss. -/
def request [DecidableEq ι] (compute : ι → Unit → Measured α Nat)
    (i : ι) (cache : Cache ι α) : Measured (Cache ι α × α) Nat :=
  match cache i with
  | some a => ((cache, a), 0)
  | none =>
      let result := compute i ()
      ((Function.update cache i (some result.1), result.1), result.2)

theorem request_hit [DecidableEq ι] (compute : ι → Unit → Measured α Nat)
    (i : ι) (cache : Cache ι α) (a : α) (hit : cache i = some a) :
    request compute i cache = ((cache, a), 0) := by
  simp only [request, hit]

theorem request_miss [DecidableEq ι] (compute : ι → Unit → Measured α Nat)
    (i : ι) (cache : Cache ι α) (miss : cache i = none) :
    request compute i cache =
      ((Function.update cache i (some (compute i ()).1), (compute i ()).1),
        (compute i ()).2) := by
  simp only [request, miss]

/-- The request's returned value is present under the requested identity. -/
theorem request_stores [DecidableEq ι] (compute : ι → Unit → Measured α Nat)
    (i : ι) (cache : Cache ι α) :
    (request compute i cache).1.1 i = some (request compute i cache).1.2 := by
  cases h : cache i <;> simp [request, h]

theorem request_valid [DecidableEq ι] (compute : ι → Unit → Measured α Nat)
    (i : ι) (cache : Cache ι α) (valid : Valid compute cache) :
    Valid compute (request compute i cache).1.1 := by
  cases h : cache i with
  | some a => simpa only [request_hit compute i cache a h] using valid
  | none =>
      simp only [request_miss compute i cache h]
      intro j a stored
      by_cases hji : j = i
      · subst j
        have same : (compute i ()).1 = a := by simpa using stored
        exact same.symm
      · exact valid j a (by simpa [Function.update_of_ne hji] using stored)

theorem request_value [DecidableEq ι] (compute : ι → Unit → Measured α Nat)
    (i : ι) (cache : Cache ι α) (valid : Valid compute cache) :
    (request compute i cache).1.2 = (compute i ()).1 :=
  request_valid compute i cache valid i _ (request_stores compute i cache)

/-- Project the cache transition into the existing measured workload executor. -/
def step [DecidableEq ι] (compute : ι → Unit → Measured α Nat)
    (i : ι) (cache : Cache ι α) : Measured (Cache ι α) Nat :=
  let result := request compute i cache
  (result.1.1, result.2)

theorem step_hit [DecidableEq ι] (compute : ι → Unit → Measured α Nat)
    (i : ι) (cache : Cache ι α) (a : α) (hit : cache i = some a) :
    step compute i cache = (cache, 0) := by
  simp only [step, request_hit compute i cache a hit]

theorem step_miss [DecidableEq ι] (compute : ι → Unit → Measured α Nat)
    (i : ι) (cache : Cache ι α) (miss : cache i = none) :
    step compute i cache =
      (Function.update cache i (some (compute i ()).1), (compute i ()).2) := by
  simp only [step, request_miss compute i cache miss]

theorem step_valid [DecidableEq ι] (compute : ι → Unit → Measured α Nat)
    (i : ι) (cache : Cache ι α) (valid : Valid compute cache) :
    Valid compute (step compute i cache).1 :=
  request_valid compute i cache valid

/-- Requests never remove or overwrite an already cached computation. -/
theorem step_preserves_cached [DecidableEq ι]
    (compute : ι → Unit → Measured α Nat) (i j : ι) (cache : Cache ι α)
    (a : α) (hit : cache j = some a) : (step compute i cache).1 j = some a := by
  by_cases same : j = i
  · subst j
    simpa only [step_hit compute i cache a hit] using hit
  · cases h : cache i with
    | some b => simpa only [step_hit compute i cache b h] using hit
    | none =>
        simpa only [step_miss compute i cache h, Function.update_of_ne same] using hit

theorem run_preserves_cached [DecidableEq ι]
    (compute : ι → Unit → Measured α Nat) (requests : List ι) (cache : Cache ι α)
    (i : ι) (a : α) (hit : cache i = some a) :
    (run (step compute) requests cache).1 i = some a :=
  run_invariant (step compute) (fun c => c i = some a)
    (fun j c h => step_preserves_cached compute j i c a h) requests cache hit

theorem run_valid [DecidableEq ι] (compute : ι → Unit → Measured α Nat)
    (requests : List ι) (cache : Cache ι α) (valid : Valid compute cache) :
    Valid compute (run (step compute) requests cache).1 :=
  run_invariant (step compute) (Valid compute) (step_valid compute)
    requests cache valid

/-- Every observation after an arbitrary request prefix has the eager value.
The next identity may already have occurred in the prefix. -/
theorem request_after_run_value [DecidableEq ι]
    (compute : ι → Unit → Measured α Nat) (requests : List ι)
    (i : ι) (cache : Cache ι α) (valid : Valid compute cache) :
    (request compute i (run (step compute) requests cache).1).1.2 =
      (compute i ()).1 :=
  request_value compute i _ (run_valid compute requests cache valid)

/-- Once an identity is cached, repeating it adds no callback work. -/
theorem run_replicate_hit [DecidableEq ι] (compute : ι → Unit → Measured α Nat)
    (i : ι) (cache : Cache ι α) (a : α) (hit : cache i = some a) (n : Nat) :
    run (step compute) (List.replicate n i) cache = (cache, 0) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [List.replicate_succ, run_cons, step_hit compute i cache a hit,
        ih, Nat.zero_add]

/-- A nonempty repeated demand invokes its callback exactly once. No finite
catalogue or validity premise is needed when starting from the empty cache. -/
theorem run_replicate_empty [DecidableEq ι] (compute : ι → Unit → Measured α Nat)
    (i : ι) (n : Nat) :
    run (step compute) (List.replicate (n + 1) i) empty =
      (Function.update empty i (some (compute i ()).1), (compute i ()).2) := by
  have hit : (Function.update (empty : Cache ι α) i (some (compute i ()).1)) i =
      some (compute i ()).1 := by simp
  simp only [List.replicate_succ, run_cons, step_miss compute i empty rfl,
    run_replicate_hit compute i _ _ hit n, Nat.add_zero]

section FiniteCatalogue
variable [Fintype ι]

/-- Eager-catalogue work that is still available to be charged by a miss. -/
def remaining (compute : ι → Unit → Measured α Nat) (cache : Cache ι α) : Nat :=
  ∑ i, match cache i with
    | none => (compute i ()).2
    | some _ => 0

theorem remaining_empty (compute : ι → Unit → Measured α Nat) :
    remaining compute empty = ∑ i, (compute i ()).2 := by
  simp [remaining, empty]

/-- Storing a previously missing value removes exactly that identity's work.
This accounting law does not assume that the stored payload is valid. -/
theorem remaining_store [DecidableEq ι] (compute : ι → Unit → Measured α Nat)
    (i : ι) (cache : Cache ι α) (a : α) (miss : cache i = none) :
    (compute i ()).2 + remaining compute (Function.update cache i (some a)) =
      remaining compute cache := by
  let unpaid (c : Cache ι α) (j : ι) : Nat :=
    match c j with
    | none => (compute j ()).2
    | some _ => 0
  have at_i : unpaid (Function.update cache i (some a)) i = 0 := by
    simp [unpaid]
  have away :
      (∑ j ∈ (Finset.univ : Finset ι).erase i,
        unpaid (Function.update cache i (some a)) j) =
      ∑ j ∈ (Finset.univ : Finset ι).erase i, unpaid cache j := by
    apply Finset.sum_congr rfl
    intro j hj
    simp only [unpaid, Function.update_of_ne (Finset.mem_erase.mp hj).1]
  have after : remaining compute (Function.update cache i (some a)) =
      ∑ j ∈ (Finset.univ : Finset ι).erase i, unpaid cache j := by
    calc
      remaining compute (Function.update cache i (some a)) =
          unpaid (Function.update cache i (some a)) i +
            ∑ j ∈ (Finset.univ : Finset ι).erase i,
              unpaid (Function.update cache i (some a)) j :=
        (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm
      _ = ∑ j ∈ (Finset.univ : Finset ι).erase i, unpaid cache j := by
        rw [at_i, away, Nat.zero_add]
  calc
    (compute i ()).2 + remaining compute (Function.update cache i (some a)) =
        unpaid cache i + ∑ j ∈ (Finset.univ : Finset ι).erase i, unpaid cache j := by
      rw [after]
      simp only [unpaid, miss]
    _ = remaining compute cache := Finset.add_sum_erase _ _ (Finset.mem_univ i)

/-- Every actual transition conserves charged plus remaining work. -/
theorem step_potential [DecidableEq ι] (compute : ι → Unit → Measured α Nat)
    (i : ι) (cache : Cache ι α) :
    (step compute i cache).2 + remaining compute (step compute i cache).1 =
      remaining compute cache := by
  cases h : cache i with
  | some a => simp only [step_hit compute i cache a h, Nat.zero_add]
  | none =>
      simpa only [step_miss compute i cache h] using
        remaining_store compute i cache (compute i ()).1 h

/-- The exact transition law telescopes along the existing actual executor. -/
theorem run_work_remaining [DecidableEq ι] (compute : ι → Unit → Measured α Nat)
    (requests : List ι) (cache : Cache ι α) :
    (run (step compute) requests cache).2 +
      remaining compute (run (step compute) requests cache).1 =
      remaining compute cache := by
  have exactWork := run_potential_exact (step compute) (fun _ _ => 0)
    (remaining compute)
    (fun i c => by simpa only [Nat.add_zero] using step_potential compute i c)
    requests cache
  simpa only [budget_constant, Nat.zero_mul, Nat.add_zero] using exactWork

theorem run_cost_le_remaining [DecidableEq ι]
    (compute : ι → Unit → Measured α Nat) (requests : List ι) (cache : Cache ι α) :
    (run (step compute) requests cache).2 ≤ remaining compute cache := by
  have exactWork := run_work_remaining compute requests cache
  omega

/-- Shared demand from an empty cache costs at most the eager-catalogue sum.
This includes an empty catalogue and empty or repeated request lists. -/
theorem run_cost_le_eager [DecidableEq ι] (compute : ι → Unit → Measured α Nat)
    (requests : List ι) :
    (run (step compute) requests empty).2 ≤ ∑ i, (compute i ()).2 := by
  simpa only [remaining_empty] using run_cost_le_remaining compute requests empty

end FiniteCatalogue
end Resources.SharedDemand
