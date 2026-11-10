import SquareKit.GuardedFold
import Applications.Sequences.OrderedSummary
import Mathlib.Algebra.Group.Int.Defs

/-!
# First-positive block prefixes and accumulated summaries

The independent specification retains whole-block order, negative mathematical
integers, empty blocks, and exhaustion. Cached realizations reuse ordered-summary
validity and a shared guarded-fold simulation. See
`docs/research/adwh-accumulation.md` for source provenance and statement review.
No allocation, machine-overflow, demand, or runtime bound is asserted here.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Sequences.Accumulation

universe u

/-- The total is nonpositive before every consumed whole block. -/
def NonpositiveBefore (s : Int) : List (List Int) → Prop
  | [] => True
  | block :: blocks => s ≤ 0 ∧ NonpositiveBefore (s + block.sum) blocks

/-- Independent first-positive-prefix specification, allowing exhaustion. -/
def CollapseSpec (acc : List Int) (blocks : List (List Int)) (out : List Int) : Prop :=
  ∃ used remaining, blocks = used ++ remaining ∧ out = acc ++ used.flatten ∧
    NonpositiveBefore acc.sum used ∧ (remaining = [] ∨ 0 < out.sum)

def collapseAux (acc : List Int) : List (List Int) → List Int
  | [] => acc
  | block :: blocks =>
      if 0 < acc.sum then acc else collapseAux (acc ++ block) blocks

def collapse (blocks : List (List Int)) : List Int := collapseAux [] blocks

theorem collapseAux_correct (acc : List Int) (blocks : List (List Int)) :
    CollapseSpec acc blocks (collapseAux acc blocks) := by
  induction blocks generalizing acc with
  | nil => exact ⟨[], [], rfl, by simp [collapseAux], True.intro, Or.inl rfl⟩
  | cons block blocks ih =>
    by_cases hs : 0 < acc.sum
    · exact ⟨[], block :: blocks, rfl, by simp [collapseAux, hs], True.intro,
        Or.inr (by simp [collapseAux, hs])⟩
    · rcases ih (acc ++ block) with ⟨used, remaining, hb, hout, hn, hstop⟩
      refine ⟨block :: used, remaining, by simp [hb], ?_, ⟨by omega, ?_⟩, ?_⟩
      · simpa [collapseAux, hs, List.append_assoc] using hout
      · simpa [List.sum_append] using hn
      · simpa [collapseAux, hs] using hstop

theorem collapseAux_unique (acc : List Int) (blocks : List (List Int)) (out : List Int)
    (h : CollapseSpec acc blocks out) : out = collapseAux acc blocks := by
  induction blocks generalizing acc out with
  | nil =>
    rcases h with ⟨used, remaining, hb, hout, _, _⟩
    rcases List.append_eq_nil_iff.mp hb.symm with ⟨rfl, rfl⟩
    simpa [collapseAux] using hout
  | cons block blocks ih =>
    rcases h with ⟨used, remaining, hb, hout, hn, hstop⟩
    by_cases hs : 0 < acc.sum
    · cases used with
      | nil => simpa [collapseAux, hs] using hout
      | cons y used => have hnonpos := hn.1; omega
    · cases used with
      | nil =>
        have hout' : out = acc := by simpa using hout
        have hremaining : remaining = block :: blocks := by simpa using hb.symm
        rcases hstop with hnil | hpos
        · simp [hremaining] at hnil
        · rw [hout'] at hpos; omega
      | cons y used =>
        have heq : block = y ∧ blocks = used ++ remaining := by simpa using hb
        rcases heq with ⟨rfl, hblocks⟩
        have hrest : CollapseSpec (acc ++ block) blocks out :=
          ⟨used, remaining, hblocks, by simpa [List.append_assoc] using hout,
            by simpa [List.sum_append] using hn.2, hstop⟩
        simpa [collapseAux, hs] using ih (acc ++ block) out hrest

theorem collapse_correct (blocks : List (List Int)) : CollapseSpec [] blocks (collapse blocks) :=
  collapseAux_correct [] blocks

theorem collapse_spec_iff (blocks : List (List Int)) (out : List Int) :
    CollapseSpec [] blocks out ↔ out = collapse blocks := by
  constructor
  · exact collapseAux_unique [] blocks out
  · intro h; rw [h]; exact collapse_correct blocks

/-- A global proper-prefix consequence of the running-total specification. -/
theorem nonpositiveBefore_take (s : Int) (used : List (List Int))
    (h : NonpositiveBefore s used) (k : Nat) (hk : k < used.length) :
    s + ((used.take k).flatten).sum ≤ 0 := by
  induction used generalizing s k with
  | nil => simp at hk
  | cons block blocks ih =>
    cases k with
    | zero => simpa using h.1
    | succ k =>
      have ht := ih (s + block.sum) h.2 k (by simpa using hk)
      simpa [List.sum_append, Int.add_assoc] using ht

theorem collapseSpec_prefix (acc : List Int) (blocks : List (List Int)) (out : List Int)
    (h : CollapseSpec acc blocks out) :
    ∃ k, k ≤ blocks.length ∧ out = acc ++ (blocks.take k).flatten ∧
      (k = blocks.length ∨ 0 < out.sum) ∧
      ∀ j < k, acc.sum + ((blocks.take j).flatten).sum ≤ 0 := by
  rcases h with ⟨used, remaining, rfl, rfl, hn, hstop⟩
  refine ⟨used.length, by simp, by simp, ?_, ?_⟩
  · rcases hstop with rfl | hpos
    · exact Or.inl (by simp)
    · exact Or.inr hpos
  · intro j hj
    have htake : (used ++ remaining).take j = used.take j :=
      List.take_append_of_le_length (Nat.le_of_lt hj)
    rw [htake]
    exact nonpositiveBefore_take acc.sum used hn j hj

/-- Every shorter block prefix has nonpositive sum; the chosen prefix is positive or exhaustive. -/
theorem collapse_shortest_prefix (blocks : List (List Int)) :
    ∃ k, k ≤ blocks.length ∧ collapse blocks = (blocks.take k).flatten ∧
      (k = blocks.length ∨ 0 < (collapse blocks).sum) ∧
      ∀ j < k, ((blocks.take j).flatten).sum ≤ 0 := by
  simpa using collapseSpec_prefix [] blocks (collapse blocks) (collapse_correct blocks)

/-- The source executor is a specialization of the finite guarded fold. -/
theorem collapseAux_eq_run (acc : List Int) (blocks : List (List Int)) :
    collapseAux acc blocks = SquareKit.GuardedFold.run
      (fun xs : List Int => decide (0 < xs.sum)) List.append acc blocks := by
  induction blocks generalizing acc with
  | nil => rfl
  | cons block blocks ih =>
      simp only [collapseAux, SquareKit.GuardedFold.run, decide_eq_true_eq]
      split <;> simp_all

open OrderedSummary

/-- Addition is the existing ordered-summary monoid via its standard wrapper. -/
def sumMeasure (x : Int) : Multiplicative Int := Multiplicative.ofAdd x

@[simp] theorem summary_sum (xs : List Int) :
    summary sumMeasure xs = Multiplicative.ofAdd xs.sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      change summary sumMeasure ([x] ++ xs) = _
      rw [summary_append, summary_singleton, ih]
      rfl

/-- One executor serves list and difference-list representations. -/
def cachedRun {R : Type u} (append : R → R → R) :
    R × Multiplicative Int → List (R × Multiplicative Int) → R × Multiplicative Int :=
  SquareKit.GuardedFold.run (fun c => decide (0 < c.2.toAdd)) (appendCache append)

/-- Only valid caches and represented appends are required. The result retains
the full sequence as well as its cached observation. -/
theorem cachedRun_refines {R : Type u} (Inv : R → Prop) (decode : R → List Int)
    (append : R → R → R)
    (closed : ∀ x y, Inv x → Inv y → Inv (append x y))
    (observes : ∀ x y, Inv x → Inv y → decode (append x y) = decode x ++ decode y)
    (seed : R × Multiplicative Int) (initial : Valid Inv decode sumMeasure seed)
    (blocks : List (R × Multiplicative Int))
    (valid : ∀ c ∈ blocks, Valid Inv decode sumMeasure c) :
    Valid Inv decode sumMeasure (cachedRun append seed blocks) ∧
      decode (cachedRun append seed blocks).1 =
        collapseAux (decode seed.1) (blocks.map (fun c => decode c.1)) := by
  rw [collapseAux_eq_run]
  apply SquareKit.GuardedFold.refine
    (fun c : R × Multiplicative Int => decide (0 < c.2.toAdd))
    (fun xs : List Int => decide (0 < xs.sum)) (appendCache append) List.append
    (fun c : R × Multiplicative Int => decode c.1)
    (fun c xs => Valid Inv decode sumMeasure c ∧ decode c.1 = xs)
    (Valid Inv decode sumMeasure)
    ?_ ?_ blocks valid seed (decode seed.1) ⟨initial, rfl⟩
  · intro c xs h
    have cacheValue : c.2 = Multiplicative.ofAdd xs.sum := by
      rw [h.1.2, h.2, summary_sum]
    rw [cacheValue]
    rfl
  · intro c xs b hc hb _
    refine ⟨append_valid Inv decode sumMeasure append closed observes hc.1 hb, ?_⟩
    change decode (append c.1 b.1) = xs ++ decode b.1
    rw [observes _ _ hc.1.1 hb.1, hc.2]

/-- Preserve the source's zip of input blocks with their separately mapped sums.
The pair order matches the existing ordered-summary cache interface. -/
def labelSums (blocks : List (List Int)) : List (List Int × Multiplicative Int) :=
  blocks.zip (blocks.map (fun block => Multiplicative.ofAdd block.sum))

theorem labelSums_eq_map (blocks : List (List Int)) :
    labelSums blocks = blocks.map (cache id sumMeasure) := by
  induction blocks <;> simp_all [labelSums, cache]

theorem labelSums_valid (blocks : List (List Int)) :
    ∀ c ∈ labelSums blocks, listValid sumMeasure c := by
  intro c hc
  rw [labelSums_eq_map] at hc
  obtain ⟨xs, _, rfl⟩ := List.mem_map.mp hc
  exact cache_valid (fun _ => True) id sumMeasure trivial

@[simp] theorem labelSums_values (blocks : List (List Int)) :
    (labelSums blocks).map Prod.fst = blocks := by
  simp [labelSums_eq_map, cache, List.map_map, Function.comp_def]

def cachedResult (blocks : List (List Int)) : List Int × Multiplicative Int :=
  cachedRun List.append ([], 1) (labelSums blocks)

def collapseCached (blocks : List (List Int)) : List Int := (cachedResult blocks).1

theorem cachedResult_refines (blocks : List (List Int)) :
    listValid sumMeasure (cachedResult blocks) ∧ collapseCached blocks = collapse blocks := by
  simpa only [cachedResult, collapseCached, collapse, id_eq, labelSums_values] using
    cachedRun_refines (fun _ => True) id List.append
      (fun _ _ _ _ => trivial) (fun _ _ _ _ => rfl)
      ([], 1) (list_empty sumMeasure) (labelSums blocks) (labelSums_valid blocks)

theorem collapseCached_correct (blocks : List (List Int)) :
    CollapseSpec [] blocks (collapseCached blocks) := by
  rw [(cachedResult_refines blocks).2]
  exact collapse_correct blocks

def differenceLabels (blocks : List (List Int)) :
    List (Batteries.DList Int × Multiplicative Int) :=
  (labelSums blocks).map (fun c => (Batteries.DList.ofList c.1, c.2))

theorem differenceLabels_valid (blocks : List (List Int)) :
    ∀ c ∈ differenceLabels blocks, dlistValid sumMeasure c := by
  intro c hc
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hc
  have h := labelSums_valid blocks p hp
  simpa only [dlistValid, Valid, Batteries.DList.toList_ofList, listValid, id_eq] using h

@[simp] theorem differenceLabels_values (blocks : List (List Int)) :
    (differenceLabels blocks).map (fun c => c.1.toList) = blocks := by
  simp [differenceLabels, List.map_map, Function.comp_def,
    Batteries.DList.toList_ofList, labelSums_values]

def differenceResult (blocks : List (List Int)) : Batteries.DList Int × Multiplicative Int :=
  cachedRun (· ++ ·) (Batteries.DList.empty, 1) (differenceLabels blocks)

def collapseDifference (blocks : List (List Int)) : List Int :=
  (differenceResult blocks).1.toList

theorem differenceResult_refines (blocks : List (List Int)) :
    dlistValid sumMeasure (differenceResult blocks) ∧
      collapseDifference blocks = collapse blocks := by
  simpa only [differenceResult, collapseDifference, collapse,
    Batteries.DList.toList_empty, differenceLabels_values] using
    cachedRun_refines (fun _ => True) Batteries.DList.toList (· ++ ·)
      (fun _ _ _ _ => trivial) (fun _ _ _ _ => Batteries.DList.toList_append _ _)
      (Batteries.DList.empty, 1) (dlist_empty sumMeasure)
      (differenceLabels blocks) (differenceLabels_valid blocks)

/-- The source difference-function claim holds at every tail, including nonempty
ones; equality only at `[]` would be a weaker contract. -/
theorem differenceResult_apply (blocks : List (List Int)) (tail : List Int) :
    (differenceResult blocks).1.apply tail = collapse blocks ++ tail := by
  rw [(differenceResult blocks).1.invariant tail]
  change collapseDifference blocks ++ tail = _
  rw [(differenceResult_refines blocks).2]

theorem collapseDifference_correct (blocks : List (List Int)) :
    CollapseSpec [] blocks (collapseDifference blocks) := by
  rw [(differenceResult_refines blocks).2]
  exact collapse_correct blocks

/-- The optimized result feeds the already shared summary observation. -/
def differenceSquare : Relational.RelSquare
    ⟨List (List Int), List (List Int), Eq⟩
    (representation (fun _ => True) Batteries.DList.toList sumMeasure) where
  impl := differenceResult
  spec := collapse
  preserves h := by
    subst h
    obtain ⟨valid, value⟩ := differenceResult_refines _
    exact ⟨valid.1, value, by rw [valid.2]; exact congrArg (summary sumMeasure) value⟩

def collapseSummary := Relational.compose
  (summarySquare (fun _ => True) Batteries.DList.toList sumMeasure) differenceSquare

theorem collapseSummary_correct (blocks : List (List Int)) :
    Multiplicative.toAdd (α := Int) (collapseSummary.impl blocks) = (collapse blocks).sum := by
  have h := collapseSummary.preserves (show blocks = blocks from rfl)
  change collapseSummary.impl blocks = summary sumMeasure (collapse blocks) at h
  rw [summary_sum] at h
  exact congrArg (Multiplicative.toAdd (α := Int)) h

end Sequences.Accumulation
