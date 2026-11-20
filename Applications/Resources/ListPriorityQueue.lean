import Applications.Resources.SelectionSort
import Applications.Resources.ListAppend
import Applications.Resources.UnaryComparison
import Applications.Search.ListMaximumQueue
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Data.Fintype.Basic

/-!
# Source list priority queues with measured comparisons

The comparator's returned Boolean chooses the actual recursive candidate before
the tail is traversed. Calls, comparison invocations, comparator work and source
cons constructions are separate observations. Pairs and Options are uncharged.
Merge counts append calls, including terminal nil, without another alias-entry
charge. These source prices do not describe native allocation or elapsed time.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.ListPriorityQueue

universe u
variable {α : Type u}

open Applications.Sorting

/-- Independent source observations; comparator work is supplied by its run. -/
inductive Metric where
  | calls
  | comparisons
  | comparisonWork
  | cons
  deriving DecidableEq

instance instFintypeMetric : Fintype Metric where
  elems := {.calls, .comparisons, .comparisonWork, .cons}
  complete metric := by cases metric <;> simp

abbrev Cost := Metric → Nat

/-- A named-coordinate vector, with pointwise addition. -/
def cost (calls comparisons comparisonWork cons : Nat) : Cost
  | .calls => calls
  | .comparisons => comparisons
  | .comparisonWork => comparisonWork
  | .cons => cons

/-- A unit comparison realizes the given executable relation. -/
def unitComparator (r : α → α → Prop) [DecidableRel r] (a b : α) :
    Measured Bool Nat := (decide (r a b), 1)

/-- Compare first, carry the chosen actual candidate, and reconstruct the
nonselected occurrence after the recursive result is returned. -/
def selectRun (cmp : α → α → Measured Bool Nat) (seed : α) :
    List α → Measured (α × List α) Cost
  | [] => ((seed, []), cost 1 0 0 0)
  | head :: tail =>
      let tested := cmp seed head
      if tested.1 then
        let child := selectRun cmp seed tail
        ((child.1.1, head :: child.1.2), cost 1 1 tested.2 1 + child.2)
      else
        let child := selectRun cmp head tail
        ((child.1.1, seed :: child.1.2), cost 1 1 tested.2 1 + child.2)

theorem selectRun_nil (cmp : α → α → Measured Bool Nat) (seed : α) :
    selectRun cmp seed [] = ((seed, []), cost 1 0 0 0) := rfl

theorem selectRun_cons_true (cmp : α → α → Measured Bool Nat)
    (seed head : α) (tail : List α) (keep : (cmp seed head).1 = true) :
    selectRun cmp seed (head :: tail) =
      (((selectRun cmp seed tail).1.1, head :: (selectRun cmp seed tail).1.2),
        cost 1 1 (cmp seed head).2 1 + (selectRun cmp seed tail).2) := by
  simp [selectRun, keep]

theorem selectRun_cons_false (cmp : α → α → Measured Bool Nat)
    (seed head : α) (tail : List α) (replace : (cmp seed head).1 = false) :
    selectRun cmp seed (head :: tail) =
      (((selectRun cmp head tail).1.1, seed :: (selectRun cmp head tail).1.2),
        cost 1 1 (cmp seed head).2 1 + (selectRun cmp head tail).2) := by
  simp [selectRun, replace]

/-- Arbitrary Boolean behavior still erases to the accepted source recurrence. -/
theorem selectRun_value (cmp : α → α → Measured Bool Nat) (seed : α) (xs : List α) :
    (selectRun cmp seed xs).1 =
      SourceSelection.select (fun a b => (cmp a b).1 = true) seed xs := by
  induction xs generalizing seed with
  | nil => rfl
  | cons head tail ih =>
      cases keep : (cmp seed head).1 <;>
        simp [selectRun, SourceSelection.select, keep, ih]

theorem selectRun_realizes (r : α → α → Prop) [DecidableRel r]
    (cmp : α → α → Measured Bool Nat)
    (realizes : ∀ a b, (cmp a b).1 = decide (r a b)) (seed : α) (xs : List α) :
    (selectRun cmp seed xs).1 = SourceSelection.select r seed xs := by
  induction xs generalizing seed with
  | nil => rfl
  | cons head tail ih =>
      by_cases keep : r seed head <;>
        simp [selectRun, SourceSelection.select, realizes, keep, ih]

theorem selectRun_calls (cmp : α → α → Measured Bool Nat) (seed : α) (xs : List α) :
    (selectRun cmp seed xs).2 .calls = xs.length + 1 := by
  induction xs generalizing seed with
  | nil => rfl
  | cons head tail ih =>
      cases keep : (cmp seed head).1 <;>
        simp [selectRun, cost, keep, ih, Nat.add_comm]

theorem selectRun_comparisons (cmp : α → α → Measured Bool Nat)
    (seed : α) (xs : List α) : (selectRun cmp seed xs).2 .comparisons = xs.length := by
  induction xs generalizing seed with
  | nil => rfl
  | cons head tail ih =>
      cases keep : (cmp seed head).1 <;>
        simp [selectRun, cost, keep, ih, Nat.add_comm]

theorem selectRun_cons (cmp : α → α → Measured Bool Nat) (seed : α) (xs : List α) :
    (selectRun cmp seed xs).2 .cons = xs.length := by
  induction xs generalizing seed with
  | nil => rfl
  | cons head tail ih =>
      cases keep : (cmp seed head).1 <;>
        simp [selectRun, cost, keep, ih, Nat.add_comm]

theorem selectRun_work_nil (cmp : α → α → Measured Bool Nat) (seed : α) :
    (selectRun cmp seed []).2 .comparisonWork = 0 := rfl

/-- Work follows the comparison's actual answer and resulting candidate. -/
theorem selectRun_work_step (cmp : α → α → Measured Bool Nat)
    (seed head : α) (tail : List α) :
    (selectRun cmp seed (head :: tail)).2 .comparisonWork = (cmp seed head).2 +
      if (cmp seed head).1 then (selectRun cmp seed tail).2 .comparisonWork
      else (selectRun cmp head tail).2 .comparisonWork := by
  cases keep : (cmp seed head).1 <;> simp [selectRun, cost, keep]

theorem selectRun_cost (cmp : α → α → Measured Bool Nat) (seed : α) (xs : List α) :
    (selectRun cmp seed xs).2 =
      cost (xs.length + 1) xs.length ((selectRun cmp seed xs).2 .comparisonWork) xs.length := by
  funext metric
  cases metric <;> simp [cost, selectRun_calls, selectRun_comparisons, selectRun_cons]

/-- Projecting unit comparison counts recovers the already accepted executor. -/
theorem selectRun_unit_projection (r : α → α → Prop) [DecidableRel r]
    (seed : α) (xs : List α) :
    ((selectRun (unitComparator r) seed xs).1,
      (selectRun (unitComparator r) seed xs).2 .comparisons) =
        SelectionSort.selectRun r seed xs := by
  rw [SelectionSort.selectRun_exact]
  exact Prod.ext (selectRun_realizes r _ (fun _ _ => rfl) seed xs)
    (selectRun_comparisons _ seed xs)

theorem selectRun_unit_work (r : α → α → Prop) [DecidableRel r]
    (seed : α) (xs : List α) :
    (selectRun (unitComparator r) seed xs).2 .comparisonWork = xs.length := by
  induction xs generalizing seed with
  | nil => rfl
  | cons head tail ih =>
      rw [selectRun_work_step]
      by_cases keep : r seed head <;> simp [unitComparator, keep, ih, Nat.add_comm]

theorem selectRun_unit_exact (r : α → α → Prop) [DecidableRel r]
    (seed : α) (xs : List α) :
    selectRun (unitComparator r) seed xs =
      (SourceSelection.select r seed xs, cost (xs.length + 1) xs.length xs.length xs.length) := by
  apply Prod.ext (selectRun_realizes r _ (fun _ _ => rfl) seed xs)
  rw [selectRun_cost, selectRun_unit_work]

/-- Occurrence preservation is independent of any law of the comparator. -/
theorem selectRun_perm (cmp : α → α → Measured Bool Nat) (seed : α) (xs : List α) :
    (seed :: xs).Perm ((selectRun cmp seed xs).1.1 :: (selectRun cmp seed xs).1.2) := by
  rw [selectRun_value]
  exact (SourceSelection.select_perm _ seed xs).symm

theorem selectRun_length (cmp : α → α → Measured Bool Nat) (seed : α) (xs : List α) :
    (selectRun cmp seed xs).1.2.length = xs.length := by
  rw [selectRun_value]
  exact SourceSelection.select_length _ seed xs

theorem selectRun_mem (cmp : α → α → Measured Bool Nat) (seed : α) (xs : List α) :
    (selectRun cmp seed xs).1.1 ∈ seed :: xs := by
  rw [selectRun_value]
  exact SourceSelection.select_mem _ seed xs

/-- An input predicate is preserved by both choices of recursive candidate. -/
theorem selectRun_work_le (cmp : α → α → Measured Bool Nat) (P : α → Prop) (C : Nat)
    (localBound : ∀ a b, P a → P b → (cmp a b).2 ≤ C)
    (seed : α) (xs : List α) (seed_ok : P seed) (input_ok : ∀ a ∈ xs, P a) :
    (selectRun cmp seed xs).2 .comparisonWork ≤ C * xs.length := by
  induction xs generalizing seed with
  | nil => simp [selectRun_work_nil]
  | cons head tail ih =>
      have head_ok := input_ok head List.mem_cons_self
      have tail_ok : ∀ a ∈ tail, P a := fun a ha => input_ok a (List.mem_cons_of_mem head ha)
      have tested := localBound seed head seed_ok head_ok
      have kept := ih seed seed_ok tail_ok
      have replaced := ih head head_ok tail_ok
      rw [selectRun_work_step]
      cases (cmp seed head).1 <;>
        simp only [Bool.false_eq_true, ↓reduceIte, List.length_cons, Nat.mul_add, Nat.mul_one] <;>
        omega

/-- It suffices to bound comparisons between occurrences in this input. -/
theorem selectRun_work_le_on_input (cmp : α → α → Measured Bool Nat)
    (seed : α) (xs : List α) (C : Nat)
    (localBound : ∀ a ∈ seed :: xs, ∀ b ∈ seed :: xs, (cmp a b).2 ≤ C) :
    (selectRun cmp seed xs).2 .comparisonWork ≤ C * xs.length :=
  selectRun_work_le cmp (fun a => a ∈ seed :: xs) C
    (fun a b ha hb => localBound a ha b hb) seed xs List.mem_cons_self
    (fun _ ha => List.mem_cons_of_mem seed ha)

/-- Empty has one declared operation entry and no construction/comparison. -/
def emptyRun : Measured (List α) Cost := ([], cost 1 0 0 0)

/-- Source insertion constructs one cons without inspecting the old queue. -/
def insertRun (key : α) (queue : List α) : Measured (List α) Cost :=
  (key :: queue, cost 1 0 0 1)

/-- Deletion charges its own entry and uses the selector's actual returned pair. -/
def deleteMaxRun (cmp : α → α → Measured Bool Nat) :
    List α → Measured (Option (α × List α)) Cost
  | [] => (none, cost 1 0 0 0)
  | seed :: tail =>
      let selected := selectRun cmp seed tail
      (some selected.1, cost 1 0 0 0 + selected.2)

theorem emptyRun_exact : (emptyRun : Measured (List α) Cost) = ([], cost 1 0 0 0) := rfl

theorem insertRun_exact (key : α) (queue : List α) :
    insertRun key queue = (key :: queue, cost 1 0 0 1) := rfl

theorem deleteMaxRun_nil (cmp : α → α → Measured Bool Nat) :
    deleteMaxRun cmp [] = (none, cost 1 0 0 0) := rfl

theorem deleteMaxRun_cons (cmp : α → α → Measured Bool Nat) (seed : α) (tail : List α) :
    deleteMaxRun cmp (seed :: tail) =
      (some (selectRun cmp seed tail).1, cost 1 0 0 0 + (selectRun cmp seed tail).2) := rfl

theorem deleteMaxRun_value (cmp : α → α → Measured Bool Nat) (queue : List α) :
    (deleteMaxRun cmp queue).1 = match queue with
      | [] => none
      | seed :: tail => some (SourceSelection.select (fun a b => (cmp a b).1 = true) seed tail) := by
  cases queue <;> simp [deleteMaxRun, selectRun_value]

theorem deleteMaxRun_calls (cmp : α → α → Measured Bool Nat) (queue : List α) :
    (deleteMaxRun cmp queue).2 .calls = queue.length + 1 := by
  cases queue <;> simp [deleteMaxRun, cost, selectRun_calls, Nat.add_comm, Nat.add_left_comm]

theorem deleteMaxRun_comparisons (cmp : α → α → Measured Bool Nat) (queue : List α) :
    (deleteMaxRun cmp queue).2 .comparisons = queue.length - 1 := by
  cases queue <;> simp [deleteMaxRun, cost, selectRun_comparisons]

theorem deleteMaxRun_cons_count (cmp : α → α → Measured Bool Nat) (queue : List α) :
    (deleteMaxRun cmp queue).2 .cons = queue.length - 1 := by
  cases queue <;> simp [deleteMaxRun, cost, selectRun_cons]

theorem deleteMaxRun_work_nil (cmp : α → α → Measured Bool Nat) :
    (deleteMaxRun cmp []).2 .comparisonWork = 0 := rfl

theorem deleteMaxRun_work_cons (cmp : α → α → Measured Bool Nat) (seed : α) (tail : List α) :
    (deleteMaxRun cmp (seed :: tail)).2 .comparisonWork =
      (selectRun cmp seed tail).2 .comparisonWork := by
  simp [deleteMaxRun, cost]

theorem deleteMaxRun_cost (cmp : α → α → Measured Bool Nat) (queue : List α) :
    (deleteMaxRun cmp queue).2 = cost (queue.length + 1) (queue.length - 1)
      ((deleteMaxRun cmp queue).2 .comparisonWork) (queue.length - 1) := by
  funext metric
  cases metric <;>
    simp [cost, deleteMaxRun_calls, deleteMaxRun_comparisons, deleteMaxRun_cons_count]

theorem deleteMaxRun_perm (cmp : α → α → Measured Bool Nat) (queue : List α)
    (key : α) (rest : List α) (removed : (deleteMaxRun cmp queue).1 = some (key, rest)) :
    queue.Perm (key :: rest) := by
  cases queue with
  | nil => simp [deleteMaxRun] at removed
  | cons seed tail =>
      have selected : (selectRun cmp seed tail).1 = (key, rest) := Option.some.inj removed
      simpa only [selected] using selectRun_perm cmp seed tail

theorem deleteMaxRun_length (cmp : α → α → Measured Bool Nat) (queue : List α)
    (key : α) (rest : List α) (removed : (deleteMaxRun cmp queue).1 = some (key, rest)) :
    rest.length + 1 = queue.length := by
  simpa only [List.length_cons] using (deleteMaxRun_perm cmp queue key rest removed).length_eq.symm

theorem deleteMaxRun_count [BEq α] (cmp : α → α → Measured Bool Nat) (queue : List α)
    (key : α) (rest : List α) (removed : (deleteMaxRun cmp queue).1 = some (key, rest))
    (query : α) : queue.count query = (if key == query then 1 else 0) + rest.count query := by
  have counted := (deleteMaxRun_perm cmp queue key rest removed).count_eq query
  simpa only [List.count_cons, Nat.add_comm] using counted

theorem deleteMaxRun_unit_work (r : α → α → Prop) [DecidableRel r] (queue : List α) :
    (deleteMaxRun (unitComparator r) queue).2 .comparisonWork = queue.length - 1 := by
  cases queue <;> simp [deleteMaxRun, cost, selectRun_unit_work]

theorem deleteMaxRun_work_le (cmp : α → α → Measured Bool Nat) (queue : List α) (C : Nat)
    (localBound : ∀ a ∈ queue, ∀ b ∈ queue, (cmp a b).2 ≤ C) :
    (deleteMaxRun cmp queue).2 .comparisonWork ≤ C * (queue.length - 1) := by
  cases queue with
  | nil => simp [deleteMaxRun_work_nil]
  | cons seed tail =>
      simpa only [deleteMaxRun_work_cons, List.length_cons, Nat.add_sub_cancel] using
        selectRun_work_le_on_input cmp seed tail C localBound

/-- Reprice the accepted recursive append, adding its terminal invocation once.
There is no separate source-merge alias charge or traversal of the right list. -/
def mergeRun (left right : List α) : Measured (List α) Cost :=
  reweight (fun copies => cost (copies + 1) 0 0 copies) (ListAppend.copies left right)

theorem mergeRun_exact (left right : List α) :
    mergeRun left right = (left ++ right, cost (left.length + 1) 0 0 left.length) := by
  simp [mergeRun, reweight, ListAppend.copies_exact]

theorem mergeRun_value (left right : List α) : (mergeRun left right).1 = left ++ right := by
  rw [mergeRun_exact]

theorem mergeRun_calls (left right : List α) :
    (mergeRun left right).2 .calls = left.length + 1 := by rw [mergeRun_exact]; rfl

theorem mergeRun_copies (left right : List α) :
    (mergeRun left right).2 .cons = left.length := by rw [mergeRun_exact]; rfl

theorem mergeRun_comparisons (left right : List α) :
    (mergeRun left right).2 .comparisons = 0 := by rw [mergeRun_exact]; rfl

theorem mergeRun_comparisonWork (left right : List α) :
    (mergeRun left right).2 .comparisonWork = 0 := by rw [mergeRun_exact]; rfl

theorem mergeRun_copy_projection (left right : List α) :
    ((mergeRun left right).1, (mergeRun left right).2 .cons) = ListAppend.copies left right := by
  rw [mergeRun_exact, ListAppend.copies_exact]
  rfl

/-- Any actual comparator realizing the non-strict source branch preserves it. -/
theorem selectRun_source (cmp : Nat → Nat → Measured Bool Nat)
    (realizes : ∀ candidate head, (cmp candidate head).1 = decide (head ≤ candidate))
    (seed : Nat) (tail : List Nat) :
    (selectRun cmp seed tail).1 = Search.ListMaximumQueue.selectMax seed tail :=
  selectRun_realizes (fun candidate head : Nat => head ≤ candidate) cmp realizes seed tail

theorem deleteMaxRun_source (cmp : Nat → Nat → Measured Bool Nat)
    (realizes : ∀ candidate head, (cmp candidate head).1 = decide (head ≤ candidate))
    (queue : List Nat) :
    (deleteMaxRun cmp queue).1 = Search.ListMaximumQueue.deleteMax queue := by
  cases queue <;> simp [deleteMaxRun, Search.ListMaximumQueue.deleteMax, selectRun_source cmp realizes]

theorem emptyRun_source : (emptyRun : Measured (List Nat) Cost).1 = Search.ListMaximumQueue.empty := rfl

theorem insertRun_source (key : Nat) (queue : List Nat) :
    (insertRun key queue).1 = Search.ListMaximumQueue.insert key queue := rfl

theorem mergeRun_source (left right : List Nat) :
    (mergeRun left right).1 = Search.ListMaximumQueue.merge left right := mergeRun_value left right

/-- Four independent nonnegative primitive weights; callers choose which
observations to price. This is not a claim that all four have unit runtime cost. -/
def price (weights observed : Cost) : Nat :=
  weights .calls * observed .calls + weights .comparisons * observed .comparisons +
    weights .comparisonWork * observed .comparisonWork + weights .cons * observed .cons

theorem price_mono (weights : Cost) {left right : Cost} (bounded : ∀ metric, left metric ≤ right metric) :
    price weights left ≤ price weights right :=
  Nat.add_le_add (Nat.add_le_add
    (Nat.add_le_add (Nat.mul_le_mul_left _ (bounded .calls))
      (Nat.mul_le_mul_left _ (bounded .comparisons)))
    (Nat.mul_le_mul_left _ (bounded .comparisonWork)))
    (Nat.mul_le_mul_left _ (bounded .cons))

theorem price_add (weights left right : Cost) :
    price weights (left + right) = price weights left + price weights right := by
  simp only [price, Pi.add_apply, Nat.mul_add]
  omega

theorem emptyRun_price (weights : Cost) :
    price weights (emptyRun : Measured (List α) Cost).2 = weights .calls := by
  simp [price, emptyRun, cost]

theorem insertRun_price (weights : Cost) (key : α) (queue : List α) :
    price weights (insertRun key queue).2 = weights .calls + weights .cons := by
  simp [price, insertRun, cost]

/-- Independent size envelope under comparator-work bound C per invocation. -/
def selectBudget (weights : Cost) (C n : Nat) : Nat :=
  price weights (cost (n + 1) n (C * n) n)

def deleteBudget (weights : Cost) (C N : Nat) : Nat :=
  price weights (cost (N + 1) (N - 1) (C * (N - 1)) (N - 1))

def linearCoefficient (weights : Cost) (C : Nat) : Nat :=
  weights .calls + weights .comparisons + weights .comparisonWork * C + weights .cons

theorem selectRun_price_le (weights : Cost) (cmp : α → α → Measured Bool Nat)
    (seed : α) (xs : List α) (C : Nat)
    (localBound : ∀ a ∈ seed :: xs, ∀ b ∈ seed :: xs, (cmp a b).2 ≤ C) :
    price weights (selectRun cmp seed xs).2 ≤ selectBudget weights C xs.length := by
  unfold selectBudget
  rw [selectRun_cost]
  apply price_mono
  intro metric
  cases metric <;> simp only [cost]
  · exact Nat.le_refl _
  · exact Nat.le_refl _
  · exact selectRun_work_le_on_input cmp seed xs C localBound
  · exact Nat.le_refl _

theorem deleteMaxRun_price_le (weights : Cost) (cmp : α → α → Measured Bool Nat)
    (queue : List α) (C : Nat)
    (localBound : ∀ a ∈ queue, ∀ b ∈ queue, (cmp a b).2 ≤ C) :
    price weights (deleteMaxRun cmp queue).2 ≤ deleteBudget weights C queue.length := by
  unfold deleteBudget
  rw [deleteMaxRun_cost]
  apply price_mono
  intro metric
  cases metric <;> simp only [cost]
  · exact Nat.le_refl _
  · exact Nat.le_refl _
  · exact deleteMaxRun_work_le cmp queue C localBound
  · exact Nat.le_refl _

theorem selectBudget_eq (weights : Cost) (C n : Nat) :
    selectBudget weights C n = linearCoefficient weights C * n + weights .calls := by
  simp only [selectBudget, price, cost, linearCoefficient]
  ring

theorem selectBudget_le_linear (weights : Cost) (C n : Nat) :
    selectBudget weights C n ≤ linearCoefficient weights C * (n + 1) := by
  have entry : weights .calls ≤ linearCoefficient weights C := by
    unfold linearCoefficient
    omega
  rw [selectBudget_eq, Nat.mul_add, Nat.mul_one]
  exact Nat.add_le_add_left entry _

theorem deleteBudget_le_linear (weights : Cost) (C N : Nat) :
    deleteBudget weights C N ≤ linearCoefficient weights C * (N + 1) := by
  apply le_trans (b := selectBudget weights C N) ?_ (selectBudget_le_linear weights C N)
  unfold deleteBudget selectBudget
  apply price_mono
  intro metric
  cases metric <;> simp only [cost]
  · exact Nat.le_refl _
  · exact Nat.sub_le N 1
  · exact Nat.mul_le_mul_left C (Nat.sub_le N 1)
  · exact Nat.sub_le N 1

theorem mergeRun_price (weights : Cost) (left right : List α) :
    price weights (mergeRun left right).2 =
      (weights .calls + weights .cons) * left.length + weights .calls := by
  rw [mergeRun_exact]
  simp only [price, cost, Nat.mul_zero, Nat.add_zero]
  ring

theorem mergeRun_price_le_left (weights : Cost) (left right : List α) :
    price weights (mergeRun left right).2 ≤
      (weights .calls + weights .cons) * (left.length + 1) := by
  rw [mergeRun_price, Nat.mul_add, Nat.mul_one]
  omega

theorem mergeRun_price_le_total (weights : Cost) (left right : List α) :
    price weights (mergeRun left right).2 ≤
      (weights .calls + weights .cons) * (left.length + right.length + 1) :=
  (mergeRun_price_le_left weights left right).trans
    (Nat.mul_le_mul_left _ (by omega))

/-- Real asymptotics for an actual family, with one uniform local work bound. -/
theorem selectRun_price_isBigO (weights : Cost) (cmp : α → α → Measured Bool Nat)
    (seeds : Nat → α) (inputs : Nat → List α) (C : Nat)
    (size : ∀ n, (inputs n).length ≤ n)
    (localBound : ∀ n, ∀ a ∈ seeds n :: inputs n, ∀ b ∈ seeds n :: inputs n, (cmp a b).2 ≤ C) :
    Asymptotics.IsBigO Filter.atTop
      (fun n => (price weights (selectRun cmp (seeds n) (inputs n)).2 : ℝ))
      (fun n => ((n + 1 : Nat) : ℝ)) :=
  Resources.isBigO_of_nat_bound _ _ (linearCoefficient weights C) 0 (fun n _ =>
    (selectRun_price_le weights cmp (seeds n) (inputs n) C (localBound n)).trans
      ((selectBudget_le_linear weights C _).trans
        (Nat.mul_le_mul_left _ (Nat.add_le_add_right (size n) 1))))

theorem deleteMaxRun_price_isBigO (weights : Cost) (cmp : α → α → Measured Bool Nat)
    (queues : Nat → List α) (C : Nat) (size : ∀ n, (queues n).length ≤ n)
    (localBound : ∀ n, ∀ a ∈ queues n, ∀ b ∈ queues n, (cmp a b).2 ≤ C) :
    Asymptotics.IsBigO Filter.atTop
      (fun n => (price weights (deleteMaxRun cmp (queues n)).2 : ℝ))
      (fun n => ((n + 1 : Nat) : ℝ)) :=
  Resources.isBigO_of_nat_bound _ _ (linearCoefficient weights C) 0 (fun n _ =>
    (deleteMaxRun_price_le weights cmp (queues n) C (localBound n)).trans
      ((deleteBudget_le_linear weights C _).trans
        (Nat.mul_le_mul_left _ (Nat.add_le_add_right (size n) 1))))

/-- The right family is unrestricted: append visits only the left spine. -/
theorem mergeRun_price_isBigO (weights : Cost) (left right : Nat → List α)
    (left_size : ∀ n, (left n).length ≤ n) :
    Asymptotics.IsBigO Filter.atTop
      (fun n => (price weights (mergeRun (left n) (right n)).2 : ℝ))
      (fun n => ((n + 1 : Nat) : ℝ)) :=
  Resources.isBigO_of_nat_bound _ _ (weights .calls + weights .cons) 0 (fun n _ =>
    (mergeRun_price_le_left weights (left n) (right n)).trans
      (Nat.mul_le_mul_left _ (Nat.add_le_add_right (left_size n) 1)))

theorem mergeRun_growing_left (a : α) (right : List α) (n : Nat) :
    (mergeRun (List.replicate n a) right).2 .cons = n := by
  rw [mergeRun_copies, List.length_replicate]

theorem mergeRun_empty_left (right : List α) :
    mergeRun [] right = (right, cost 1 0 0 0) := mergeRun_exact [] right

/-- Arbitrarily large total input can retain one append invocation and no copies. -/
theorem merge_no_total_lower (a : α) (K threshold : Nat) :
    ∃ left right : List α, threshold ≤ left.length + right.length ∧
      K * (mergeRun left right).2 .calls < left.length + right.length := by
  refine ⟨[], List.replicate (threshold + K + 1) a, ?_, ?_⟩ <;>
    simp only [List.length_nil, List.length_replicate, Nat.zero_add, mergeRun_calls] <;> omega

/-- Explicit lockstep unary comparison in the source's non-strict orientation. -/
def unaryMaxComparator (candidate head : Nat) : Measured Bool Nat :=
  UnaryComparison.unaryLERun head candidate

theorem unaryMaxComparator_value (candidate head : Nat) :
    (unaryMaxComparator candidate head).1 = decide (head ≤ candidate) := by
  rw [unaryMaxComparator, UnaryComparison.unaryLERun_spec]

theorem unaryMaxComparator_work (candidate head : Nat) :
    (unaryMaxComparator candidate head).2 = min head candidate + 1 :=
  UnaryComparison.unaryLERun_steps head candidate

theorem selectRun_unary_value (seed : Nat) (tail : List Nat) :
    (selectRun unaryMaxComparator seed tail).1 = Search.ListMaximumQueue.selectMax seed tail :=
  selectRun_source unaryMaxComparator unaryMaxComparator_value seed tail

theorem deleteMaxRun_unary_value (queue : List Nat) :
    (deleteMaxRun unaryMaxComparator queue).1 = Search.ListMaximumQueue.deleteMax queue :=
  deleteMaxRun_source unaryMaxComparator unaryMaxComparator_value queue

theorem selectRun_unary_work_le (seed : Nat) (tail : List Nat) (M : Nat)
    (seed_bound : seed ≤ M) (tail_bound : ∀ a ∈ tail, a ≤ M) :
    (selectRun unaryMaxComparator seed tail).2 .comparisonWork ≤ (M + 1) * tail.length := by
  apply selectRun_work_le unaryMaxComparator (fun a => a ≤ M) (M + 1) _ seed tail seed_bound tail_bound
  intro candidate head _candidate_bound head_bound
  rw [unaryMaxComparator_work]
  exact Nat.add_le_add_right ((Nat.min_le_left head candidate).trans head_bound) 1

theorem deleteMaxRun_unary_work_le (queue : List Nat) (M : Nat)
    (bounded : ∀ a ∈ queue, a ≤ M) :
    (deleteMaxRun unaryMaxComparator queue).2 .comparisonWork ≤ (M + 1) * (queue.length - 1) := by
  apply deleteMaxRun_work_le
  intro candidate _candidate_mem head head_mem
  rw [unaryMaxComparator_work]
  exact Nat.add_le_add_right ((Nat.min_le_left head candidate).trans (bounded head head_mem)) 1

theorem selectRun_unary_equal_work (key n : Nat) :
    (selectRun unaryMaxComparator key (List.replicate n key)).2 .comparisonWork = (key + 1) * n := by
  induction n with
  | zero => simp [selectRun_work_nil]
  | succ n ih =>
      rw [List.replicate_succ, selectRun_work_step]
      simp [unaryMaxComparator, UnaryComparison.unaryLERun_spec, ih, Nat.mul_add, Nat.add_comm]

theorem deleteMaxRun_unary_two_equal_work (key : Nat) :
    (deleteMaxRun unaryMaxComparator [key, key]).2 .comparisonWork = key + 1 := by
  simpa only [List.replicate_one, Nat.mul_one, deleteMaxRun_work_cons] using
    selectRun_unary_equal_work key 1

/-- Fixed queue length cannot bound unbounded-key unary-comparison work. -/
theorem unary_fixed_length_unbounded (budget : Nat) :
    ∃ queue : List Nat, queue.length = 2 ∧
      budget < (deleteMaxRun unaryMaxComparator queue).2 .comparisonWork := by
  refine ⟨[budget, budget], rfl, ?_⟩
  rw [deleteMaxRun_unary_two_equal_work]
  omega

end Resources.ListPriorityQueue
