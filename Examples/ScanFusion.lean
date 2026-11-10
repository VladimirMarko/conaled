import Applications.Parallel.InclusiveScan
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Data.Int.Basic

/-!
# Checked inclusive scan and restricted fusion clients

Four entries are scanned with a composition of two pair plans. Word order,
additive totals, and interpretation to word lengths exercise the same public
scanner results. The even-state example retains the textbook correction to
unrestricted fold fusion.
-/

namespace Examples.ScanFusion

open Applications.Parallel SquareKit.ListFusion

/-- Two independently scanned chunks, with an outer scan of their totals. -/
def four : ScanPlan := .comp .pair .pair

def additiveInput : four.shape.Data (Multiplicative Nat) :=
  ((Multiplicative.ofAdd 1, Multiplicative.ofAdd 2),
   (Multiplicative.ofAdd 3, Multiplicative.ofAdd 4))

/-- The inclusive convention adds the final total, not another initial value. -/
theorem additive_four :
    (four.scanner.inclusive additiveInput).map Multiplicative.toAdd = [0, 1, 3, 6, 10] := by
  rw [Scanner.inclusive_correct]
  rfl

/-- A nonidentity seed belongs to the list bridge even though scanners start at one. -/
theorem additive_seed :
    ((sequential (Multiplicative.ofAdd (5 : Nat)) [Multiplicative.ofAdd 1, Multiplicative.ofAdd 2]).1 ++
      [(sequential (Multiplicative.ofAdd (5 : Nat)) [Multiplicative.ofAdd 1, Multiplicative.ofAdd 2]).2]).map
        Multiplicative.toAdd = [5, 6, 8] := by
  rw [sequential_scanl]
  rfl

/-- Empty plans exist in the current grammar and return the identity state. -/
theorem empty_plan :
    ((ScanPlan.empty.scanner : Scanner .empty (Multiplicative Nat)).inclusive PUnit.unit).map
      Multiplicative.toAdd = [0] := by
  change ((Scanner.unit : Scanner .empty (Multiplicative Nat)).inclusive PUnit.unit).map
    Multiplicative.toAdd = [0]
  rw [Scanner.inclusive_correct]
  rfl

theorem singleton_plan :
    ((ScanPlan.leaf.scanner : Scanner .leaf (Multiplicative Nat)).inclusive (Multiplicative.ofAdd 7)).map
      Multiplicative.toAdd = [0, 7] := by
  change ((Scanner.singleton : Scanner .leaf (Multiplicative Nat)).inclusive
    (Multiplicative.ofAdd 7)).map Multiplicative.toAdd = [0, 7]
  rw [Scanner.inclusive_correct]
  rfl

def words : four.shape.Data (FreeMonoid Nat) :=
  ((FreeMonoid.ofList [1, 2], FreeMonoid.ofList [3]),
   (FreeMonoid.ofList [4, 5], FreeMonoid.ofList [6]))

/-- Reversing either multiplication or chunk adjustment would change this list. -/
theorem ordered_words :
    (four.scanner.inclusive words).map FreeMonoid.toList =
      [[], [1, 2], [1, 2, 3], [1, 2, 3, 4, 5], [1, 2, 3, 4, 5, 6]] := by
  rw [Scanner.inclusive_correct]
  rfl

/-- A representation interpretation composed with every certified scan plan. -/
theorem word_lengths (p : ScanPlan) (x : p.shape.Data (FreeMonoid α)) :
    (p.scanner.inclusive x).map FreeMonoid.length =
      (p.shape.flatten x).scanl (fun n w => n + w.length) 0 := by
  apply Scanner.inclusive_fusion _ _ _ (fun _ => True) trivial
  · intro _ _ _; trivial
  · intro y z _
    exact List.length_append

theorem composed_word_lengths :
    (four.scanner.inclusive words).map FreeMonoid.length = [0, 2, 3, 5, 6] := by
  rw [word_lengths]
  rfl

/-- Arbitrary accumulator types remain available: input elements are not states. -/
theorem reverse_prefix_lengths (xs : List Nat) :
    (xs.scanl (fun acc x => x :: acc) []).map List.length =
      xs.scanl (fun n _ => n + 1) 0 := by
  apply scanl_reachable _ _ _ (fun _ => True) [] trivial
  · intro _ _ _; trivial
  · intro _ _ _; rfl

/-- The standard scan lemma connects the states to independently indexed prefixes. -/
theorem prefix_decimal :
    ([2, 7, 1, 8] : List Nat).scanl (fun n d => 10 * n + d) 0 =
      [0, 2, 27, 271, 2718] := by
  rw [scanl_prefix_values]
  rfl

theorem source_inits :
    ([1, 2, 3] : List Nat).inits = [[], [1], [1, 2], [1, 2, 3]] :=
  (inits_eq_range_take _).trans (by rfl)

theorem source_tails :
    ([1, 2, 3] : List Nat).tails = [[1, 2, 3], [2, 3], [3], []] :=
  (tails_eq_range_drop _).trans (by rfl)

/-- Literal prefix folds retain a nonidentity seed and decimal digit order. -/
theorem prefix_decimal_seed :
    ([2, 7] : List Nat).inits.map (List.foldl (fun n d => 10 * n + d) 5) =
      [5, 52, 527] :=
  (foldl_inits_eq_scanl _ _ _).trans (by rfl)

/-- Elements and accumulator states can have different types. -/
theorem prefix_ordered_accumulator :
    ([2, 7] : List Nat).inits.map (List.foldl (fun acc x => acc ++ [x]) [9]) =
      [[9], [9, 2], [9, 2, 7]] :=
  (foldl_inits_eq_scanl _ _ _).trans (by rfl)

/-- Odd states are discarded; all states reached by `doubleStep` from zero are even. -/
def replaceOdd (x : Int) : Int := if x % 2 = 0 then x else 0

def doubleStep (x y : Int) : Int := 2 * x + y

/-- The fold's independent arithmetic meaning includes negative integers. -/
theorem doubleStep_foldr (xs : List Int) :
    xs.foldr doubleStep 0 = 2 * xs.sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      rw [List.foldr_cons, List.sum_cons]
      change 2 * x + xs.foldr doubleStep 0 = 2 * (x + xs.sum)
      rw [ih, Int.mul_add]

theorem doubleStep_foldr_even (xs : List Int) : (xs.foldr doubleStep 0) % 2 = 0 := by
  rw [doubleStep_foldr]
  simp

/-- The source divisibility test is the existing remainder test. -/
theorem replaceOdd_dvd (x : Int) : replaceOdd x = if (2 : Int) ∣ x then x else 0 := by
  simp only [replaceOdd, Int.dvd_iff_emod_eq_zero]

theorem doubleStep_even (x y : Int) (hy : y % 2 = 0) :
    doubleStep x y % 2 = 0 := by
  simp [doubleStep, hy]

theorem replaceOdd_step (x y : Int) (hy : y % 2 = 0) :
    replaceOdd (doubleStep x y) = doubleStep x (replaceOdd y) := by
  simp only [replaceOdd, doubleStep_even x y hy, hy, ↓reduceIte]

/-- Source restricted right-fold fusion, using only a reachable-state law. -/
theorem restricted_foldr (xs : List Int) :
    replaceOdd (xs.foldr doubleStep 0) = xs.foldr doubleStep 0 :=
  foldr_reachable doubleStep doubleStep replaceOdd (fun y => y % 2 = 0)
    0 (by decide) doubleStep_even replaceOdd_step xs

/-- The exact reachable-context formulation also suffices for this client. -/
theorem restricted_foldr_via_context (xs : List Int) :
    replaceOdd (xs.foldr doubleStep 0) = xs.foldr doubleStep 0 := by
  apply (foldr_iff doubleStep doubleStep replaceOdd 0).mpr _ xs
  intro x ys
  exact replaceOdd_step x _ (doubleStep_foldr_even ys)

theorem signed_doubleStep : ([-3, 4, 2] : List Int).foldr doubleStep 0 = 6 :=
  (doubleStep_foldr _).trans (by rfl)

theorem signed_replacement : replaceOdd (([-3, 4, 2] : List Int).foldr doubleStep 0) = 6 :=
  (restricted_foldr _).trans signed_doubleStep

/-- The left-fold version preserves the same invariant at every prefix. -/
theorem restricted_scanl (xs : List Int) :
    (xs.scanl (fun y x => doubleStep x y) 0).map replaceOdd =
      xs.scanl (fun y x => doubleStep x y) 0 :=
  scanl_reachable _ _ replaceOdd (fun y => y % 2 = 0) 0 (by decide)
    (fun y x hy => doubleStep_even x y hy) (fun y x hy => replaceOdd_step x y hy) xs

theorem restricted_foldl (xs : List Int) :
    replaceOdd (xs.foldl (fun y x => doubleStep x y) 0) =
      xs.foldl (fun y x => doubleStep x y) 0 :=
  foldl_reachable _ _ replaceOdd (fun y => y % 2 = 0) 0 (by decide)
    (fun y x hy => doubleStep_even x y hy) (fun y x hy => replaceOdd_step x y hy) xs

/-- The global commuting law fails at the unreachable odd state one. -/
theorem unrestricted_law_false :
    ¬ ∀ x y : Int, replaceOdd (doubleStep x y) = doubleStep x (replaceOdd y) := by
  intro law
  have bad := law 1 1
  change (0 : Int) = 2 at bad
  omega

/-- Dropping the invariant on the initial state also makes fusion false. -/
theorem odd_seed_scan_fails :
    (([1] : List Int).scanl (fun y x => doubleStep x y) 1).map replaceOdd ≠
      ([1] : List Int).scanl (fun y x => doubleStep x y) (replaceOdd 1) := by
  decide

end Examples.ScanFusion
