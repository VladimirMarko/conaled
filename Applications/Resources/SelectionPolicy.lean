import Applications.Selection.ThreeWay
import Applications.Resources.Partition
import Applications.Resources.ListCalls

/-!
Measured deterministic three-way selection with an explicit pivot constructor.

The returned trace records the positive input sizes at active invocations.
Those sizes come from an actual measured length traversal. Each active step
also executes the supplied measured pivot, the one-pass partition, both bucket
lengths, and either sequential equal-block lookup or its actual recursive call.
One entry is charged for the selector itself. Primitive arithmetic, comparisons,
tuple construction and trace bookkeeping add no source calls. Fuel is the same
administrative depth parameter used by `Applications.Selection.runWith`; it is
not a claim about runtime fuel overhead. Adequacy is proved after erasure.

This realization deliberately includes its input-size traversal in the tariff.
It does not identify source calls with scan volume, comparison count or time.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.SelectionPolicy
universe u

/-- Optional value, active-size trace, and the separately accumulated calls. -/
abbrev Observed (α : Type u) := Measured (Option α × List Nat) Nat

/-- Extend the actual child result, retaining its value, trace and charge. -/
def prepend {α : Type u} (n c : Nat) (r : Observed α) : Observed α :=
  ((r.1.1, n :: r.1.2), c + r.2)

variable {α : Type u} [LinearOrder α]

/-- A measured policy supplies a value and its construction charge together.
The equal branch retains the source's positional lookup, including duplicates.
The empty/fuel-zero extension has one entry and no active trace. -/
def runWith (choose : List α → Measured (Option α) Nat) :
    Nat → Nat → List α → Observed α
  | 0, _, _ => ((none, []), 1)
  | _ + 1, _, [] => ((none, []), 1)
  | fuel + 1, k, x :: xs =>
      let n := SymmetricCosts.lengthRun (x :: xs)
      let pivot := choose (x :: xs)
      match pivot.1 with
      | none => ((none, [n.1]), n.2 + pivot.2 + 1)
      | some p =>
          let t := Partition.partitionRun p (x :: xs)
          let nl := SymmetricCosts.lengthRun t.1.1
          let ne := SymmetricCosts.lengthRun t.1.2.1
          let c := n.2 + pivot.2 + t.2 + nl.2 + ne.2 + 1
          if k < nl.1 then prepend n.1 c (runWith choose fuel k t.1.1)
          else if k < nl.1 + ne.1 then
            let r := ListCalls.lookupRun t.1.2.1 (k - nl.1)
            ((r.1, [n.1]), c + r.2)
          else prepend n.1 c (runWith choose fuel (k - nl.1 - ne.1) t.1.2.2)

theorem runWith_zero (choose : List α → Measured (Option α) Nat)
    (k : Nat) (xs : List α) : runWith choose 0 k xs = ((none, []), 1) := rfl

theorem runWith_nil (choose : List α → Measured (Option α) Nat)
    (fuel k : Nat) : runWith choose fuel k [] = ((none, []), 1) := by
  cases fuel <;> rfl

/-- Normalize only the primitive executions, preserving the actual child call.
The displayed tariff includes both bucket lengths even on a lower branch. -/
theorem runWith_step (choose : List α → Measured (Option α) Nat)
    (fuel k : Nat) (xs : List α) (hx : xs ≠ []) (p : α)
    (hp : (choose xs).1 = some p) :
    runWith choose (fuel + 1) k xs =
      let t := Applications.Selection.partition3 p xs
      let c := (xs.length + 1) + (choose xs).2 + (xs.length + 1) +
        (t.1.length + 1) + (t.2.1.length + 1) + 1
      if k < t.1.length then prepend xs.length c (runWith choose fuel k t.1)
      else if k < t.1.length + t.2.1.length then
        ((t.2.1[k - t.1.length]?, [xs.length]),
          c + (min (k - t.1.length) t.2.1.length + 1))
      else prepend xs.length c
        (runWith choose fuel (k - t.1.length - t.2.1.length) t.2.2) := by
  cases xs with
  | nil => exact (hx rfl).elim
  | cons x xs =>
      simp only [runWith, hp, SymmetricCosts.lengthRun_exact,
        Partition.partitionRun_value, Partition.partitionRun_cost,
        ListCalls.lookupRun_value, ListCalls.lookupRun_cost,
        Applications.Selection.partition3]
      rfl

/-- Trace instrumentation and measured primitives preserve the existing source
control flow at every fuel, including invalid indices and policy failure. -/
theorem runWith_value (choose : List α → Measured (Option α) Nat)
    (fuel k : Nat) (xs : List α) :
    (runWith choose fuel k xs).1.1 =
      Applications.Selection.runWith (fun ys => (choose ys).1) fuel k xs := by
  induction fuel generalizing k xs with
  | zero => rfl
  | succ fuel ih =>
      cases xs with
      | nil => rfl
      | cons x xs =>
          cases hp : (choose (x :: xs)).1 with
          | none => simp only [runWith, Applications.Selection.runWith, hp]
          | some p =>
              rw [runWith_step choose fuel k (x :: xs) (by simp) p hp]
              by_cases hl : k < (Applications.Selection.partition3 p (x :: xs)).1.length
              · simp [Applications.Selection.runWith, hp,
                  Applications.Selection.dispatch, hl, prepend, ih]
              · by_cases he : k < (Applications.Selection.partition3 p (x :: xs)).1.length +
                    (Applications.Selection.partition3 p (x :: xs)).2.1.length
                · simp [Applications.Selection.runWith, hp,
                    Applications.Selection.dispatch, hl, he]
                · simp [Applications.Selection.runWith, hp,
                    Applications.Selection.dispatch, hl, he, prepend, ih]

/-- Input length suffices for a valid input-occurrence policy. No distinctness
or valid-rank premise is needed for the optional value contract. -/
theorem runWith_correct (choose : List α → Measured (Option α) Nat)
    (hv : Applications.Selection.PivotValid (fun ys => (choose ys).1))
    (fuel k : Nat) (xs : List α) (hf : xs.length ≤ fuel) :
    (runWith choose fuel k xs).1.1 = (Applications.Selection.ordered xs)[k]? := by
  rw [runWith_value]
  exact Applications.Selection.runWith_value _ hv fuel xs hf k

end Resources.SelectionPolicy
