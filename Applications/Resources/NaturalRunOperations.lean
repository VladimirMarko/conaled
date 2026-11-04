import Applications.Resources.DifferenceListCosts
import Applications.Resources.NaturalSorting

/-!
# Source operations of the natural-run scanner

FDSA, Chapter 2, pp. 21–25. This observation charges one scanner/worker
entry, one tested adjacent pair, the existing XD01 callback creation and
application observations, and one direct descending cons, terminal suffix
cell or emitted outer-run cons. A singleton callback's entry already covers
its own cons. Supplied builders and descending accumulators already exist.

The actual selected branch constructs, extends and applies the returned
callback. Value erasure uses `Rep`; uniform application work uses the separate
`AppCost` contract. Neither contract is inferred from the other. These are
source observations, not compiler allocations, key-evaluation costs or time.

The final merger observation is restricted to zero or one outer run. It adds
one dispatch entry, including the distinct `[[]]` case. There is no claim here
about the operational work of merging several runs. The existing comparison
counter remains unchanged.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.NaturalRunOperations

open Applications.Sorting
open DifferenceListCosts

universe u v
variable {α : Type u} {κ : Type v}

mutual
  /-- Execute the source scanner, including its actual singleton seed creation. -/
  def runsOpsBy (lt : α → α → Bool) : List α → Measured (List (List α)) Nat
    | [] => CallCount.tick (pure [])
    | [a] =>
        CallCount.tick (bind (CallCount.tick (pure [a]))
          (fun run => CallCount.tick (pure [run])))
    | a :: b :: xs =>
        CallCount.tick (bind (CallCount.tick (pure (lt b a))) (fun descending =>
          if descending then
            bind (CallCount.tick (pure [a])) (fun acc => descOpsBy lt b acc xs)
          else bind (createSingleton a) (fun f => ascOpsBy lt b f xs)))
  termination_by xs => xs.length
  decreasing_by all_goals simp_wf

  /-- Apply the actual builder only when its run ends; a continuation creates
  the singleton and composition through XD01's existing `pushRun`. -/
  def ascOpsBy (lt : α → α → Bool) (a : α) (f : Builder α) :
      List α → Measured (List (List α)) Nat
    | [] =>
        CallCount.tick (bind (CallCount.tick (pure [a])) (fun suffix =>
          bind (f suffix) (fun run => CallCount.tick (pure [run]))))
    | b :: bs =>
        CallCount.tick (bind (CallCount.tick (pure (lt b a))) (fun descending =>
          if descending then
            bind (CallCount.tick (pure [a])) (fun suffix =>
              bind (f suffix) (fun run =>
                bind (runsOpsBy lt (b :: bs))
                  (fun rest => CallCount.tick (pure (run :: rest)))))
          else bind (pushRun a f) (fun next => ascOpsBy lt b next bs)))
  termination_by ys => ys.length + 1
  decreasing_by all_goals simp_wf

  /-- Extend or emit the actual supplied descending accumulator. Its earlier
  construction and length do not contribute to this worker observation. -/
  def descOpsBy (lt : α → α → Bool) (a : α) (acc : List α) :
      List α → Measured (List (List α)) Nat
    | [] =>
        CallCount.tick (bind (CallCount.tick (pure (a :: acc)))
          (fun run => CallCount.tick (pure [run])))
    | b :: bs =>
        CallCount.tick (bind (CallCount.tick (pure (lt b a))) (fun descending =>
          if descending then
            bind (CallCount.tick (pure (a :: acc)))
              (fun next => descOpsBy lt b next bs)
          else
            bind (CallCount.tick (pure (a :: acc))) (fun run =>
              bind (runsOpsBy lt (b :: bs))
                (fun rest => CallCount.tick (pure (run :: rest))))))
  termination_by ys => ys.length + 1
  decreasing_by all_goals simp_wf
end

@[simp] theorem runsOpsBy_nil (lt : α → α → Bool) : runsOpsBy lt [] = ([], 1) := by
  rw [runsOpsBy]
  rfl

@[simp] theorem runsOpsBy_singleton (lt : α → α → Bool) (a : α) :
    runsOpsBy lt [a] = ([[a]], 3) := by
  rw [runsOpsBy]
  rfl

theorem runsOpsBy_cons_cons (lt : α → α → Bool) (a b : α) (xs : List α) :
    runsOpsBy lt (a :: b :: xs) =
      if lt b a then
        ((descOpsBy lt b [a] xs).1, 3 + (descOpsBy lt b [a] xs).2)
      else
        ((ascOpsBy lt b (singleton a) xs).1,
          3 + (ascOpsBy lt b (singleton a) xs).2) := by
  rw [runsOpsBy]
  cases lt b a with
  | false =>
    apply Prod.ext
    · rfl
    · change 1 + (1 + (ascOpsBy lt b (singleton a) xs).2) + 1 =
        3 + (ascOpsBy lt b (singleton a) xs).2
      omega
  | true =>
    apply Prod.ext
    · rfl
    · change 1 + (1 + (descOpsBy lt b [a] xs).2) + 1 =
        3 + (descOpsBy lt b [a] xs).2
      omega

@[simp] theorem ascOpsBy_nil (lt : α → α → Bool) (a : α) (f : Builder α) :
    ascOpsBy lt a f [] = ([(f [a]).1], (f [a]).2 + 3) := by
  rw [ascOpsBy]
  apply Prod.ext
  · rfl
  · change 1 + ((f [a]).2 + 1) + 1 = (f [a]).2 + 3
    omega

theorem ascOpsBy_cons (lt : α → α → Bool) (a b : α) (f : Builder α) (bs : List α) :
    ascOpsBy lt a f (b :: bs) =
      if lt b a then
        ((f [a]).1 :: (runsOpsBy lt (b :: bs)).1,
          (f [a]).2 + 4 + (runsOpsBy lt (b :: bs)).2)
      else
        ((ascOpsBy lt b (pushRun a f).1 bs).1,
          4 + (ascOpsBy lt b (pushRun a f).1 bs).2) := by
  rw [ascOpsBy]
  cases lt b a with
  | false =>
    apply Prod.ext
    · rfl
    · change 1 + (2 + (ascOpsBy lt b (pushRun a f).1 bs).2) + 1 =
        4 + (ascOpsBy lt b (pushRun a f).1 bs).2
      omega
  | true =>
    apply Prod.ext
    · rfl
    · change 1 + (1 + ((f [a]).2 + ((runsOpsBy lt (b :: bs)).2 + 1))) + 1 =
        (f [a]).2 + 4 + (runsOpsBy lt (b :: bs)).2
      omega

@[simp] theorem descOpsBy_nil (lt : α → α → Bool) (a : α) (acc : List α) :
    descOpsBy lt a acc [] = ([a :: acc], 3) := by
  rw [descOpsBy]
  rfl

theorem descOpsBy_cons (lt : α → α → Bool) (a b : α) (acc bs : List α) :
    descOpsBy lt a acc (b :: bs) =
      if lt b a then
        ((descOpsBy lt b (a :: acc) bs).1, 3 + (descOpsBy lt b (a :: acc) bs).2)
      else
        ((a :: acc) :: (runsOpsBy lt (b :: bs)).1,
          4 + (runsOpsBy lt (b :: bs)).2) := by
  rw [descOpsBy]
  cases lt b a with
  | false =>
    apply Prod.ext
    · rfl
    · change 1 + (1 + ((runsOpsBy lt (b :: bs)).2 + 1)) + 1 =
        4 + (runsOpsBy lt (b :: bs)).2
      omega
  | true =>
    apply Prod.ext
    · rfl
    · change 1 + (1 + (descOpsBy lt b (a :: acc) bs).2) + 1 =
        3 + (descOpsBy lt b (a :: acc) bs).2
      omega

theorem singleton_toDList (a : α) :
    toDList (singleton a) [a] (singleton_rep a) = Batteries.DList.singleton a := by
  rfl

mutual
  /-- Comparator laws, payload equality and payload inhabitation are unnecessary. -/
  theorem runsOpsBy_value (lt : α → α → Bool) (xs : List α) :
      (runsOpsBy lt xs).1 = runsBy lt xs := by
    match xs with
    | [] => rw [runsOpsBy_nil, runsBy_nil]
    | [a] => rw [runsOpsBy_singleton, runsBy_singleton]
    | a :: b :: bs =>
      rw [runsOpsBy_cons_cons, runsBy_cons_cons]
      cases lt b a with
      | false =>
        change (ascOpsBy lt b (singleton a) bs).1 =
          ascBy lt b (Batteries.DList.singleton a) bs
        rw [ascOpsBy_value lt b (singleton a) [a] (singleton_rep a) bs,
          singleton_toDList]
      | true =>
        change (descOpsBy lt b [a] bs).1 = descBy lt b [a] bs
        exact descOpsBy_value lt b [a] bs
  termination_by xs.length
  decreasing_by all_goals simp_wf

  /-- Only value representation is needed for this erasure; no cost contract is assumed. -/
  theorem ascOpsBy_value (lt : α → α → Bool) (a : α) (f : Builder α)
      (pref : List α) (rep : Rep f pref) (ys : List α) :
      (ascOpsBy lt a f ys).1 = ascBy lt a (toDList f pref rep) ys := by
    match ys with
    | [] => rw [ascOpsBy_nil, ascBy_nil]; rfl
    | b :: bs =>
      rw [ascOpsBy_cons, ascBy_cons]
      cases lt b a with
      | false =>
        change (ascOpsBy lt b (pushRun a f).1 bs).1 =
          ascBy lt b ((toDList f pref rep).push a) bs
        rw [ascOpsBy_value lt b (pushRun a f).1 (pref ++ [a])
          (pushRun_rep a f pref rep) bs, toDList_pushRun]
      | true =>
        change (f [a]).1 :: (runsOpsBy lt (b :: bs)).1 =
          (f [a]).1 :: runsBy lt (b :: bs)
        rw [runsOpsBy_value]
  termination_by ys.length + 1
  decreasing_by all_goals simp_wf

  theorem descOpsBy_value (lt : α → α → Bool) (a : α) (acc ys : List α) :
      (descOpsBy lt a acc ys).1 = descBy lt a acc ys := by
    match ys with
    | [] => rw [descOpsBy_nil, descBy_nil]
    | b :: bs =>
      rw [descOpsBy_cons, descBy_cons]
      cases lt b a with
      | false =>
        change (a :: acc) :: (runsOpsBy lt (b :: bs)).1 =
          (a :: acc) :: runsBy lt (b :: bs)
        rw [runsOpsBy_value]
      | true =>
        change (descOpsBy lt b (a :: acc) bs).1 = descBy lt b (a :: acc) bs
        exact descOpsBy_value lt b (a :: acc) bs
  termination_by ys.length + 1
  decreasing_by all_goals simp_wf
end

theorem runsOpsBy_perm (lt : α → α → Bool) (xs : List α) :
    (runsOpsBy lt xs).1.flatten.Perm xs := by
  rw [runsOpsBy_value]
  exact runsBy_perm lt xs

theorem runsOpsBy_flatten_length (lt : α → α → Bool) (xs : List α) :
    (runsOpsBy lt xs).1.flatten.length = xs.length := (runsOpsBy_perm lt xs).length_eq

theorem runsOpsBy_length_le (lt : α → α → Bool) (xs : List α) :
    (runsOpsBy lt xs).1.length ≤ xs.length := by
  rw [runsOpsBy_value]
  exact runsBy_length_le lt xs

theorem runsOpsBy_sorted [LinearOrder κ] (key : α → κ) (xs : List α) :
    ∀ run ∈ (runsOpsBy (fun a b => decide (key a < key b)) xs).1, KeySorted key run := by
  rw [runsOpsBy_value]
  exact runsOn_sorted key xs

mutual
  /-- The whole scanner is bounded directly, including run restarts. -/
  theorem runsOpsBy_work_le (lt : α → α → Bool) (xs : List α) :
      (runsOpsBy lt xs).2 ≤ 6 * xs.length + 1 := by
    match xs with
    | [] => rw [runsOpsBy_nil]; omega
    | [a] => rw [runsOpsBy_singleton]; simp
    | a :: b :: bs =>
      rw [runsOpsBy_cons_cons]
      cases lt b a with
      | false =>
        have ih := ascOpsBy_work_le lt b (singleton a) bs 1 (singleton_appCost a)
        change 3 + (ascOpsBy lt b (singleton a) bs).2 ≤
          6 * ((bs.length + 1) + 1) + 1
        omega
      | true =>
        have ih := descOpsBy_work_le lt b [a] bs
        change 3 + (descOpsBy lt b [a] bs).2 ≤ 6 * ((bs.length + 1) + 1) + 1
        omega
  termination_by xs.length
  decreasing_by all_goals simp_wf

  /-- The pending invocation weight is the potential. No Rep or sorted-prefix
  premise is used, even when the supplied callback has unusual values. -/
  theorem ascOpsBy_work_le (lt : α → α → Bool) (a : α) (f : Builder α)
      (ys : List α) (k : Nat) (cost : AppCost f k) :
      (ascOpsBy lt a f ys).2 ≤ k + 6 * ys.length + 5 := by
    match ys with
    | [] =>
      rw [ascOpsBy_nil]
      have ha := cost [a]
      change (f [a]).2 + 3 ≤ k + 6 * 0 + 5
      omega
    | b :: bs =>
      rw [ascOpsBy_cons]
      cases lt b a with
      | false =>
        have ih := ascOpsBy_work_le lt b (pushRun a f).1 bs (k + 2)
          (pushRun_appCost a f k cost)
        change 4 + (ascOpsBy lt b (pushRun a f).1 bs).2 ≤ k + 6 * (bs.length + 1) + 5
        omega
      | true =>
        have ih := runsOpsBy_work_le lt (b :: bs)
        have ha := cost [a]
        simp only [List.length_cons] at ih
        change (f [a]).2 + 4 + (runsOpsBy lt (b :: bs)).2 ≤ k + 6 * (bs.length + 1) + 5
        omega
  termination_by ys.length + 1
  decreasing_by all_goals simp_wf

  /-- The already supplied accumulator may have arbitrary contents and length. -/
  theorem descOpsBy_work_le (lt : α → α → Bool) (a : α) (acc ys : List α) :
      (descOpsBy lt a acc ys).2 ≤ 6 * ys.length + 5 := by
    match ys with
    | [] => rw [descOpsBy_nil]; simp
    | b :: bs =>
      rw [descOpsBy_cons]
      cases lt b a with
      | false =>
        have ih := runsOpsBy_work_le lt (b :: bs)
        simp only [List.length_cons] at ih
        change 4 + (runsOpsBy lt (b :: bs)).2 ≤ 6 * (bs.length + 1) + 5
        omega
      | true =>
        have ih := descOpsBy_work_le lt b (a :: acc) bs
        change 3 + (descOpsBy lt b (a :: acc) bs).2 ≤ 6 * (bs.length + 1) + 5
        omega
  termination_by ys.length + 1
  decreasing_by all_goals simp_wf
end

/-- The exact continuing path keeps the actual callback application in the
statement. It needs neither a representation nor a uniform cost contract. -/
theorem ascOpsBy_buildFrom (lt : α → α → Bool) (a last : α) (f : Builder α)
    (middle : List α)
    (chain : (a :: (middle ++ [last])).IsChain (fun x y => lt y x = false)) :
    ascOpsBy lt a f (middle ++ [last]) =
      ([((buildFrom (a :: middle) f).1 [last]).1],
        (buildFrom (a :: middle) f).2 + ((buildFrom (a :: middle) f).1 [last]).2 +
          2 * (middle.length + 1) + 3) := by
  induction middle generalizing a f with
  | nil =>
    have hc := List.isChain_cons_cons.mp chain
    rw [List.nil_append, ascOpsBy_cons, hc.1]
    change ((ascOpsBy lt last (pushRun a f).1 []).1,
      4 + (ascOpsBy lt last (pushRun a f).1 []).2) = _
    rw [ascOpsBy_nil, buildFrom_cons, buildFrom_nil]
    apply Prod.ext
    · rfl
    · change 4 + ((compose f (singleton a) [last]).2 + 3) =
        (2 + 0) + (compose f (singleton a) [last]).2 + 2 * (0 + 1) + 3
      omega
  | cons b middle ih =>
    have hc := List.isChain_cons_cons.mp chain
    rw [List.cons_append, ascOpsBy_cons, hc.1]
    change ((ascOpsBy lt b (pushRun a f).1 (middle ++ [last])).1,
      4 + (ascOpsBy lt b (pushRun a f).1 (middle ++ [last])).2) = _
    rw [ih b (pushRun a f).1 hc.2, buildFrom_cons]
    apply Prod.ext
    · rfl
    · change 4 + ((buildFrom (b :: middle) (compose f (singleton a))).2 +
        ((buildFrom (b :: middle) (compose f (singleton a))).1 [last]).2 +
          2 * (middle.length + 1) + 3) =
        (2 + (buildFrom (b :: middle) (compose f (singleton a))).2) +
          ((buildFrom (b :: middle) (compose f (singleton a))).1 [last]).2 +
            2 * ((middle.length + 1) + 1) + 3
      omega

/-- The source starts a nontrivial ascending run with a singleton, not identity. -/
def buildAscending (first : α) (middle : List α) : Measured (Builder α) Nat :=
  bind (createSingleton first) (buildFrom middle)

theorem buildAscending_eq (first : α) (middle : List α) :
    buildAscending first middle =
      ((buildFrom middle (singleton first)).1,
        1 + (buildFrom middle (singleton first)).2) := rfl

theorem buildAscending_cost (first : α) (middle : List α) :
    (buildAscending first middle).2 = 1 + 2 * middle.length := by
  change 1 + (buildFrom middle (singleton first)).2 = 1 + 2 * middle.length
  rw [buildFrom_cost]

theorem buildAscending_rep (first : α) (middle : List α) :
    Rep (buildAscending first middle).1 (first :: middle) :=
  buildFrom_rep middle (singleton first) [first] (singleton_rep first)

theorem buildAscending_appCost (first : α) (middle : List α) :
    AppCost (buildAscending first middle).1 (1 + 2 * middle.length) :=
  buildFrom_appCost middle (singleton first) 1 (singleton_appCost first)

theorem buildAscending_apply (first : α) (middle suffix : List α) :
    (buildAscending first middle).1 suffix =
      ((first :: middle) ++ suffix, 1 + 2 * middle.length) :=
  Prod.ext (buildAscending_rep first middle suffix) (buildAscending_appCost first middle suffix)

/-- The construction and invocation weights agree on this specific source path. -/
theorem buildAscending_weight (first : α) (middle suffix : List α) :
    (buildAscending first middle).2 + 1 = 2 * (first :: middle).length ∧
      ((buildAscending first middle).1 suffix).2 + 1 = 2 * (first :: middle).length := by
  rw [buildAscending_cost, buildAscending_appCost first middle suffix]
  simp only [List.length_cons]
  constructor <;> omega

/-- For a run of length r = middle.length + 2, both counts plus three equal 2r. -/
theorem buildAscending_counts_add_three (first : α) (middle : List α) (last : α) :
    (buildAscending first middle).2 + 3 = 2 * (first :: (middle ++ [last])).length ∧
      ((buildAscending first middle).1 [last]).2 + 3 =
        2 * (first :: (middle ++ [last])).length := by
  rw [buildAscending_cost, buildAscending_appCost first middle [last]]
  simp only [List.length_cons, List.length_append, List.length_nil]
  constructor <;> omega

theorem buildAscending_counts (first : α) (middle : List α) (last : α) :
    (buildAscending first middle).2 = 2 * (first :: (middle ++ [last])).length - 3 ∧
      ((buildAscending first middle).1 [last]).2 =
        2 * (first :: (middle ++ [last])).length - 3 := by
  have h := buildAscending_counts_add_three first middle last
  constructor <;> omega

/-- Direct source-path correspondence, before any value or uniform-cost
contract is substituted. The returned builder supplies the actual emitted run. -/
theorem runsOpsBy_buildAscending (lt : α → α → Bool) (first last : α)
    (middle : List α)
    (chain : (first :: (middle ++ [last])).IsChain (fun x y => lt y x = false)) :
    runsOpsBy lt (first :: (middle ++ [last])) =
      ([((buildAscending first middle).1 [last]).1],
        (buildAscending first middle).2 + ((buildAscending first middle).1 [last]).2 +
          2 * middle.length + 5) := by
  cases middle with
  | nil =>
    have hc := List.isChain_cons_cons.mp chain
    rw [List.nil_append, runsOpsBy_cons_cons, hc.1]
    change ((ascOpsBy lt last (singleton first) []).1,
      3 + (ascOpsBy lt last (singleton first) []).2) = _
    rw [ascOpsBy_nil, buildAscending_eq, buildFrom_nil]
    apply Prod.ext
    · rfl
    · rfl
  | cons a middle =>
    have hc := List.isChain_cons_cons.mp chain
    rw [List.cons_append, runsOpsBy_cons_cons, hc.1]
    change ((ascOpsBy lt a (singleton first) (middle ++ [last])).1,
      3 + (ascOpsBy lt a (singleton first) (middle ++ [last])).2) = _
    rw [ascOpsBy_buildFrom lt a last (singleton first) middle hc.2, buildAscending_eq]
    apply Prod.ext
    · rfl
    · change 3 + ((buildFrom (a :: middle) (singleton first)).2 +
        ((buildFrom (a :: middle) (singleton first)).1 [last]).2 +
          2 * (middle.length + 1) + 3) =
        (1 + (buildFrom (a :: middle) (singleton first)).2) +
          ((buildFrom (a :: middle) (singleton first)).1 [last]).2 +
            2 * (middle.length + 1) + 5
      omega

theorem ascOpsBy_work_of_chain (lt : α → α → Bool) (a : α) (f : Builder α)
    (ys : List α) (k : Nat) (cost : AppCost f k)
    (chain : (a :: ys).IsChain (fun x y => lt y x = false)) :
    (ascOpsBy lt a f ys).2 = k + 6 * ys.length + 3 := by
  induction ys generalizing a f k with
  | nil =>
    rw [ascOpsBy_nil]
    change (f [a]).2 + 3 = k + 3
    exact congrArg (fun n : Nat => n + 3) (cost [a])
  | cons b bs ih =>
    have hc := List.isChain_cons_cons.mp chain
    rw [ascOpsBy_cons, hc.1]
    change 4 + (ascOpsBy lt b (pushRun a f).1 bs).2 = k + 6 * (bs.length + 1) + 3
    have rest := ih b (pushRun a f).1 (k + 2) (pushRun_appCost a f k cost) hc.2
    omega

theorem descOpsBy_work_of_chain (lt : α → α → Bool) (a : α) (acc ys : List α)
    (chain : (a :: ys).IsChain (fun x y => lt y x = true)) :
    (descOpsBy lt a acc ys).2 = 3 * ys.length + 3 := by
  induction ys generalizing a acc with
  | nil => rw [descOpsBy_nil]; rfl
  | cons b bs ih =>
    have hc := List.isChain_cons_cons.mp chain
    rw [descOpsBy_cons, hc.1]
    change 3 + (descOpsBy lt b (a :: acc) bs).2 = 3 * (bs.length + 1) + 3
    have rest := ih b (a :: acc) hc.2
    omega

/-- The subtraction formula is proved through this unsaturated equality;
the source's two-element minimum is an explicit domain premise. -/
theorem runsOpsBy_work_ascending_add_five (lt : α → α → Bool) (xs : List α)
    (hlen : 2 ≤ xs.length) (chain : xs.IsChain (fun x y => lt y x = false)) :
    (runsOpsBy lt xs).2 + 5 = 6 * xs.length := by
  match xs with
  | [] => simp at hlen
  | [_] => simp at hlen
  | a :: b :: bs =>
    have hc := List.isChain_cons_cons.mp chain
    rw [runsOpsBy_cons_cons, hc.1]
    change (3 + (ascOpsBy lt b (singleton a) bs).2) + 5 =
      6 * ((bs.length + 1) + 1)
    have rest := ascOpsBy_work_of_chain lt b (singleton a) bs 1 (singleton_appCost a) hc.2
    omega

theorem runsOpsBy_work_ascending (lt : α → α → Bool) (xs : List α)
    (hlen : 2 ≤ xs.length) (chain : xs.IsChain (fun x y => lt y x = false)) :
    (runsOpsBy lt xs).2 = 6 * xs.length - 5 := by
  have h := runsOpsBy_work_ascending_add_five lt xs hlen chain
  omega

theorem runsOpsBy_of_ascending_chain (lt : α → α → Bool) (xs : List α)
    (hlen : 2 ≤ xs.length) (chain : xs.IsChain (fun x y => lt y x = false)) :
    runsOpsBy lt xs = ([xs], 6 * xs.length - 5) := by
  apply Prod.ext
  · rw [runsOpsBy_value]
    exact runsBy_of_ascending_chain lt xs (by intro h; subst xs; simp at hlen) chain
  · exact runsOpsBy_work_ascending lt xs hlen chain

/-- Singleton descent is included; empty input retains its separate one-entry law. -/
theorem runsOpsBy_work_descending (lt : α → α → Bool) (xs : List α)
    (hne : xs ≠ []) (chain : xs.IsChain (fun x y => lt y x = true)) :
    (runsOpsBy lt xs).2 = 3 * xs.length := by
  match xs with
  | [] => exact (hne rfl).elim
  | [a] => rw [runsOpsBy_singleton]; rfl
  | a :: b :: bs =>
    have hc := List.isChain_cons_cons.mp chain
    rw [runsOpsBy_cons_cons, hc.1]
    change 3 + (descOpsBy lt b [a] bs).2 = 3 * ((bs.length + 1) + 1)
    have rest := descOpsBy_work_of_chain lt b [a] bs hc.2
    omega

theorem runsOpsBy_of_descending_chain (lt : α → α → Bool) (xs : List α)
    (hne : xs ≠ []) (chain : xs.IsChain (fun x y => lt y x = true)) :
    runsOpsBy lt xs = ([xs.reverse], 3 * xs.length) := by
  apply Prod.ext
  · rw [runsOpsBy_value]
    exact runsBy_of_descending_chain lt xs hne chain
  · exact runsOpsBy_work_descending lt xs hne chain

theorem runsOpsBy_of_sorted [LinearOrder κ] (key : α → κ) (xs : List α)
    (sorted : KeySorted key xs) (hlen : 2 ≤ xs.length) :
    runsOpsBy (fun a b => decide (key a < key b)) xs = ([xs], 6 * xs.length - 5) :=
  runsOpsBy_of_ascending_chain _ xs hlen
    (sorted.isChain.imp (fun _ _ hxy => decide_eq_false (not_lt_of_ge hxy)))

theorem runsOpsBy_of_strictly_descending [LT κ] [DecidableLT κ]
    (key : α → κ) (xs : List α) (descending : xs.Pairwise (fun x y => key y < key x))
    (hne : xs ≠ []) :
    runsOpsBy (fun a b => decide (key a < key b)) xs = ([xs.reverse], 3 * xs.length) :=
  runsOpsBy_of_descending_chain _ xs hne
    (descending.isChain.imp (fun _ _ hxy => decide_eq_true hxy))

/-- Only the actual zero/single-run merger branches are assigned this observation. -/
def baseMergeOps : (xss : List (List α)) → xss.length ≤ 1 → Measured (List α) Nat
  | [], _ => CallCount.tick (pure [])
  | [xs], _ => CallCount.tick (pure xs)
  | _ :: _ :: _, h => False.elim (by simp only [List.length_cons] at h; omega)

@[simp] theorem baseMergeOps_nil (h : ([] : List (List α)).length ≤ 1) :
    baseMergeOps [] h = ([], 1) := rfl

@[simp] theorem baseMergeOps_singleton (xs : List α) (h : [xs].length ≤ 1) :
    baseMergeOps [xs] h = (xs, 1) := rfl

theorem baseMergeOps_spec (cmp : α → α → Bool) (xss : List (List α))
    (h : xss.length ≤ 1) : baseMergeOps xss h = (mergeAllBy cmp xss, 1) := by
  match xss with
  | [] => rw [baseMergeOps_nil, mergeAllBy_nil]
  | [xs] => rw [baseMergeOps_singleton, mergeAllBy_singleton]
  | _ :: _ :: _ => simp only [List.length_cons] at h; omega

/-- The bridge uses only the comparison program's two actual base equations. -/
theorem baseMergeOps_eq_tick_allRun (cmp : α → α → Bool) (xss : List (List α))
    (h : xss.length ≤ 1) :
    baseMergeOps xss h = CallCount.tick (BottomUpSorting.allRun cmp xss) := by
  match xss with
  | [] => rw [baseMergeOps_nil, BottomUpSorting.allRun_nil]; rfl
  | [xs] => rw [baseMergeOps_singleton, BottomUpSorting.allRun_singleton]; rfl
  | _ :: _ :: _ => simp only [List.length_cons] at h; omega

/-- Capture the actual scan once, then supply its returned run list to the
restricted source dispatch. The domain excludes all multi-run executions. -/
def singleRunOpsBy (lt : α → α → Bool) (xs : List α)
    (h : (runsBy lt xs).length ≤ 1) : Measured (List α) Nat :=
  let scanned := runsOpsBy lt xs
  let valid : scanned.1.length ≤ 1 := by
    change (runsOpsBy lt xs).1.length ≤ 1
    rw [runsOpsBy_value]
    exact h
  bind scanned (fun _ => baseMergeOps scanned.1 valid)

theorem singleRunOpsBy_spec (lt cmp : α → α → Bool) (xs : List α)
    (h : (runsBy lt xs).length ≤ 1) :
    singleRunOpsBy lt xs h = (sortNaturalBy lt cmp xs, (runsOpsBy lt xs).2 + 1) := by
  simp only [singleRunOpsBy, bind, baseMergeOps_spec cmp, runsOpsBy_value, sortNaturalBy]

theorem singleRunOpsBy_value (lt cmp : α → α → Bool) (xs : List α)
    (h : (runsBy lt xs).length ≤ 1) :
    (singleRunOpsBy lt xs h).1 = sortNaturalBy lt cmp xs :=
  congrArg Prod.fst (singleRunOpsBy_spec lt cmp xs h)

theorem singleRunOpsBy_work (lt : α → α → Bool) (xs : List α)
    (h : (runsBy lt xs).length ≤ 1) :
    (singleRunOpsBy lt xs h).2 = (runsOpsBy lt xs).2 + 1 :=
  congrArg Prod.snd (singleRunOpsBy_spec lt lt xs h)

theorem singleRunOpsBy_work_le (lt : α → α → Bool) (xs : List α)
    (h : (runsBy lt xs).length ≤ 1) :
    (singleRunOpsBy lt xs h).2 ≤ 6 * xs.length + 2 := by
  rw [singleRunOpsBy_work]
  have bound := runsOpsBy_work_le lt xs
  omega

theorem singleRunOpsBy_perm (lt : α → α → Bool) (xs : List α)
    (h : (runsBy lt xs).length ≤ 1) :
    (singleRunOpsBy lt xs h).1.Perm xs := by
  rw [singleRunOpsBy_value lt lt]
  exact sortNaturalBy_perm lt lt xs

theorem singleRunOpsBy_correct [LinearOrder κ] (key : α → κ) (xs : List α)
    (h : (runsOn key xs).length ≤ 1) :
    KeySorted key (singleRunOpsBy (fun a b => decide (key a < key b)) xs h).1 ∧
      (singleRunOpsBy (fun a b => decide (key a < key b)) xs h).1.Perm xs := by
  rw [singleRunOpsBy_value _ (fun a b => decide (key a ≤ key b))]
  exact sortNaturalOn_correct key xs

@[simp] theorem singleRunOpsBy_nil (lt : α → α → Bool)
    (h : (runsBy lt []).length ≤ 1) : singleRunOpsBy lt [] h = ([], 2) := by
  rw [singleRunOpsBy_spec lt lt, sortNaturalBy_nil, runsOpsBy_nil]

@[simp] theorem singleRunOpsBy_singleton (lt : α → α → Bool) (a : α)
    (h : (runsBy lt [a]).length ≤ 1) : singleRunOpsBy lt [a] h = ([a], 4) := by
  rw [singleRunOpsBy_spec lt lt, sortNaturalBy_singleton, runsOpsBy_singleton]

theorem runsBy_length_le_one_of_ascending_chain (lt : α → α → Bool) (xs : List α)
    (chain : xs.IsChain (fun x y => lt y x = false)) : (runsBy lt xs).length ≤ 1 := by
  cases xs with
  | nil => simp
  | cons a xs =>
    rw [runsBy_of_ascending_chain lt (a :: xs) (by simp) chain]
    exact Nat.le_refl 1

theorem runsBy_length_le_one_of_descending_chain (lt : α → α → Bool) (xs : List α)
    (chain : xs.IsChain (fun x y => lt y x = true)) : (runsBy lt xs).length ≤ 1 := by
  cases xs with
  | nil => simp
  | cons a xs =>
    rw [runsBy_of_descending_chain lt (a :: xs) (by simp) chain]
    exact Nat.le_refl 1

theorem singleRunOpsBy_of_ascending_chain (lt : α → α → Bool) (xs : List α)
    (h : (runsBy lt xs).length ≤ 1) (hlen : 2 ≤ xs.length)
    (chain : xs.IsChain (fun x y => lt y x = false)) :
    singleRunOpsBy lt xs h = (xs, 6 * xs.length - 4) := by
  apply Prod.ext
  · rw [singleRunOpsBy_value lt lt, sortNaturalBy_eq_mergeAll,
      runsBy_of_ascending_chain lt xs (by intro hz; subst xs; simp at hlen) chain,
      mergeAllBy_singleton]
  · rw [singleRunOpsBy_work]
    have exactWork := runsOpsBy_work_ascending_add_five lt xs hlen chain
    omega

theorem singleRunOpsBy_of_descending_chain (lt : α → α → Bool) (xs : List α)
    (h : (runsBy lt xs).length ≤ 1) (hne : xs ≠ [])
    (chain : xs.IsChain (fun x y => lt y x = true)) :
    singleRunOpsBy lt xs h = (xs.reverse, 3 * xs.length + 1) := by
  rw [singleRunOpsBy_spec lt lt, sortNaturalBy_eq_mergeAll,
    runsBy_of_descending_chain lt xs hne chain, mergeAllBy_singleton,
    runsOpsBy_work_descending lt xs hne chain]

theorem runsOn_length_le_one_of_sorted [LinearOrder κ] (key : α → κ) (xs : List α)
    (sorted : KeySorted key xs) : (runsOn key xs).length ≤ 1 :=
  runsBy_length_le_one_of_ascending_chain _ xs
    (sorted.isChain.imp (fun _ _ hxy => decide_eq_false (not_lt_of_ge hxy)))

theorem runsOn_length_le_one_of_strictly_descending [LT κ] [DecidableLT κ]
    (key : α → κ) (xs : List α) (descending : xs.Pairwise (fun x y => key y < key x)) :
    (runsOn key xs).length ≤ 1 :=
  runsBy_length_le_one_of_descending_chain _ xs
    (descending.isChain.imp (fun _ _ hxy => decide_eq_true hxy))

theorem singleRunOpsBy_of_sorted [LinearOrder κ] (key : α → κ) (xs : List α)
    (sorted : KeySorted key xs) (hlen : 2 ≤ xs.length) :
    singleRunOpsBy (fun a b => decide (key a < key b)) xs
      (runsOn_length_le_one_of_sorted key xs sorted) = (xs, 6 * xs.length - 4) :=
  singleRunOpsBy_of_ascending_chain _ xs _ hlen
    (sorted.isChain.imp (fun _ _ hxy => decide_eq_false (not_lt_of_ge hxy)))

theorem singleRunOpsBy_of_strictly_descending [LT κ] [DecidableLT κ]
    (key : α → κ) (xs : List α) (descending : xs.Pairwise (fun x y => key y < key x))
    (hne : xs ≠ []) :
    singleRunOpsBy (fun a b => decide (key a < key b)) xs
      (runsOn_length_le_one_of_strictly_descending key xs descending) =
        (xs.reverse, 3 * xs.length + 1) :=
  singleRunOpsBy_of_descending_chain _ xs _ hne
    (descending.isChain.imp (fun _ _ hxy => decide_eq_true hxy))

end Resources.NaturalRunOperations
