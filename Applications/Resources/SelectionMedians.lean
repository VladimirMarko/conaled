import Applications.Resources.Chunks
import Applications.Resources.SelectionAuxiliary
import Applications.Selection.MedianOfMedians
import Mathlib.Algebra.Order.BigOperators.Group.List

/-! Measured chunk medians for FDSA Chapter 3 and Appendix B.2.

The callback extracts the payload from its actual successful slow-median run.
Nonemptiness discharges the impossible optional failure without an inhabitant,
default value, filtering pass, or separately evaluated specification median.
The proof-carrying attach adapter records the callback's domain; the source
tariff charges the actual median calls and the ordinary map entries. These
observations are source call counts, not claims about Lean allocation costs.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.SelectionMedians
open Applications.Selection Applications.Sequences.Chunks
open Resources.SelectionAuxiliary
universe u
variable {α : Type u} [LinearOrder α]

/-- Extract the value and count of the actual run on a nonempty input. -/
def slowMedianValueRun (xs : List α) (hx : xs ≠ []) : Measured α Nat :=
  let r := slowMedianRun xs
  match h : r.1 with
  | none => False.elim (hx ((slowMedianRun_none xs).mp h))
  | some a => (a, r.2)

theorem slowMedianValueRun_of_some (xs : List α) (hx : xs ≠ []) (a : α)
    (ha : (slowMedianRun xs).1 = some a) :
    slowMedianValueRun xs hx = (a, (slowMedianRun xs).2) := by
  unfold slowMedianValueRun
  split
  next h => exact False.elim (hx ((slowMedianRun_none xs).mp h))
  next b hb =>
    have hba : b = a := Option.some.inj (hb.symm.trans ha)
    exact Prod.ext hba rfl

theorem slowMedianValueRun_of_run (xs : List α) (hx : xs ≠ []) (a : α) (c : Nat)
    (h : slowMedianRun xs = (some a, c)) : slowMedianValueRun xs hx = (a, c) := by
  have hv : (slowMedianRun xs).1 = some a := congrArg Prod.fst h
  have hc : (slowMedianRun xs).2 = c := congrArg Prod.snd h
  rw [slowMedianValueRun_of_some xs hx a hv, hc]

theorem slowMedianValueRun_some (xs : List α) (hx : xs ≠ []) :
    some (slowMedianValueRun xs hx).1 = (slowMedianRun xs).1 := by
  cases h : (slowMedianRun xs).1 with
  | none => exact False.elim (hx ((slowMedianRun_none xs).mp h))
  | some a => rw [slowMedianValueRun_of_some xs hx a h]

theorem slowMedianValueRun_cost (xs : List α) (hx : xs ≠ []) :
    (slowMedianValueRun xs hx).2 = (slowMedianRun xs).2 := by
  cases h : (slowMedianRun xs).1 with
  | none => exact False.elim (hx ((slowMedianRun_none xs).mp h))
  | some a => rw [slowMedianValueRun_of_some xs hx a h]

theorem slowMedianValueRun_ranked (xs : List α) (hx : xs ≠ []) :
    RankedAt xs ((xs.length - 1) / 2) (slowMedianValueRun xs hx).1 :=
  (slowMedianRun_some_iff xs _).mp (slowMedianValueRun_some xs hx).symm

theorem slowMedianValueRun_mem (xs : List α) (hx : xs ≠ []) :
    (slowMedianValueRun xs hx).1 ∈ xs := (slowMedianValueRun_ranked xs hx).mem

theorem slowMedianValueRun_value (xs : List α) (hx : xs ≠ []) :
    (slowMedianValueRun xs hx).1 = lowerMedianValue xs hx :=
  (slowMedianValueRun_ranked xs hx).unique (lowerMedianValue_ranked xs hx)

theorem slowMedianValueRun_small_bound (xs : List α) (hx : xs ≠ [])
    (hn : xs.length ≤ 5) : (slowMedianValueRun xs hx).2 ≤ 47 := by
  rw [slowMedianValueRun_cost]
  exact slowMedianRun_small_bound xs hx hn

/-- Each occurrence executes its own measured median callback. -/
def mapSlowMedianRun (xss : List (List α))
    (hne : ∀ ys ∈ xss, ys ≠ []) : Measured (List α) Nat :=
  ListCalls.mapRun (fun ys : {ys // ys ∈ xss} =>
    slowMedianValueRun ys.val (hne ys.val ys.property)) xss.attach

theorem mapSlowMedianRun_value (xss : List (List α))
    (hne : ∀ ys ∈ xss, ys ≠ []) :
    (mapSlowMedianRun xss hne).1 =
      xss.attach.map (fun ys => lowerMedianValue ys.val (hne ys.val ys.property)) := by
  simp only [mapSlowMedianRun, ListCalls.mapRun_value, slowMedianValueRun_value]

/-- An observation of the returned payloads, not another execution pass. -/
theorem mapSlowMedianRun_some_values (xss : List (List α))
    (hne : ∀ ys ∈ xss, ys ≠ []) :
    (mapSlowMedianRun xss hne).1.map some = xss.map (fun ys => (slowMedianRun ys).1) := by
  simp only [mapSlowMedianRun, ListCalls.mapRun_value, List.map_map,
    Function.comp_def, slowMedianValueRun_some]
  exact List.attach_map_val (f := fun ys => (slowMedianRun ys).1)

theorem mapSlowMedianRun_length (xss : List (List α))
    (hne : ∀ ys ∈ xss, ys ≠ []) : (mapSlowMedianRun xss hne).1.length = xss.length := by
  simp only [mapSlowMedianRun_value, List.length_map, List.length_attach]

/-- Exact callback sum plus one map call per element and its empty call. -/
theorem mapSlowMedianRun_cost (xss : List (List α))
    (hne : ∀ ys ∈ xss, ys ≠ []) :
    (mapSlowMedianRun xss hne).2 =
      (xss.map (fun ys => (slowMedianRun ys).2)).sum + xss.length + 1 := by
  simp only [mapSlowMedianRun, ListCalls.mapRun_cost, slowMedianValueRun_cost,
    List.length_attach]
  exact congrArg (fun cs : List Nat => cs.sum + xss.length + 1)
    (List.attach_map_val (l := xss) (f := fun ys => (slowMedianRun ys).2))

/-- Retain the group parameter for the later generalized-group exercise. -/
theorem mapSlowMedianRun_bound (xss : List (List α))
    (hne : ∀ ys ∈ xss, ys ≠ []) (d : Nat)
    (hlen : ∀ ys ∈ xss, ys.length ≤ d) :
    (mapSlowMedianRun xss hne).2 ≤ (d ^ 2 + 4 * d + 3) * xss.length + 1 := by
  have hcallback (ys : List α) (hy : ys ∈ xss) :
      (slowMedianRun ys).2 ≤ d ^ 2 + 4 * d + 2 := by
    have hs := slowMedianRun_cost_bound ys (hne ys hy)
    have hl := hlen ys hy
    have hsq : ys.length * ys.length ≤ d * d := Nat.mul_le_mul hl hl
    nlinarith
  have hsum : (xss.map (fun ys => (slowMedianRun ys).2)).sum ≤
      (d ^ 2 + 4 * d + 2) * xss.length := by
    have h := List.sum_le_length_nsmul (xss.map (fun ys => (slowMedianRun ys).2))
      (d ^ 2 + 4 * d + 2) (by
        intro c hc
        obtain ⟨ys, hy, rfl⟩ := List.mem_map.mp hc
        exact hcallback ys hy)
    simpa only [List.length_map, Nat.nsmul_eq_mul, Nat.mul_comm] using h
  rw [mapSlowMedianRun_cost]
  nlinarith

theorem mapSlowMedianRun_small_bound (xss : List (List α))
    (hne : ∀ ys ∈ xss, ys ≠ []) (hlen : ∀ ys ∈ xss, ys.length ≤ 5) :
    (mapSlowMedianRun xss hne).2 ≤ 48 * xss.length + 1 := by
  have h := mapSlowMedianRun_bound xss hne 5 hlen
  norm_num at h
  exact h

theorem mapSlowMedianRun_chop_five_bound (xs : List α) :
    (mapSlowMedianRun (chop 5 xs) (chop_mem_ne_nil 5 xs)).2 ≤ 10 * xs.length + 48 := by
  have h := mapSlowMedianRun_small_bound (chop 5 xs) (chop_mem_ne_nil 5 xs)
    (length_mem_chop 5 xs)
  rw [length_chop, Nat.ceilDiv_eq_add_pred_div] at h
  omega

/-- Execute chopping once, then the payload map on the returned chunks.
The nonrecursive composition adds no entry beyond its component executions. -/
def chunkMediansRun (d : Nat) (xs : List α) : Measured (List α) Nat :=
  let chunks := Resources.Chunks.chopRun d xs
  let medians := mapSlowMedianRun chunks.1
    (fun ys hy => Resources.Chunks.chopRun_mem_ne_nil d xs ys hy)
  (medians.1, chunks.2 + medians.2)

theorem chunkMediansRun_value (d : Nat) (xs : List α) :
    (chunkMediansRun d xs).1 = chunkMedians d xs := by
  simp only [chunkMediansRun, mapSlowMedianRun_value, Resources.Chunks.chopRun_value,
    chunkMedians]

theorem chunkMediansRun_some_values (d : Nat) (xs : List α) :
    (chunkMediansRun d xs).1.map some = (chop d xs).map (fun ys => (slowMedianRun ys).1) := by
  simpa only [chunkMediansRun, Resources.Chunks.chopRun_value] using
    mapSlowMedianRun_some_values (chop d xs) (chop_mem_ne_nil d xs)

theorem chunkMediansRun_cost_split (d : Nat) (xs : List α) :
    (chunkMediansRun d xs).2 = (Resources.Chunks.chopRun d xs).2 +
      (mapSlowMedianRun (chop d xs) (chop_mem_ne_nil d xs)).2 := by
  simp only [chunkMediansRun, Resources.Chunks.chopRun_value]

theorem chunkMediansRun_cost (d : Nat) (xs : List α) :
    (chunkMediansRun d xs).2 = (Resources.Chunks.chopRun d xs).2 +
      ((chop d xs).map (fun ys => (slowMedianRun ys).2)).sum + (xs.length ⌈/⌉ d) + 1 := by
  rw [chunkMediansRun_cost_split, mapSlowMedianRun_cost, length_chop]
  omega

theorem chunkMediansRun_cost_positive (d : Nat) (xs : List α) (hd : 0 < d) :
    (chunkMediansRun d xs).2 = 2 * xs.length + 4 * (xs.length ⌈/⌉ d) +
      ((chop d xs).map (fun ys => (slowMedianRun ys).2)).sum + 2 := by
  rw [chunkMediansRun_cost, Resources.Chunks.chopRun_cost d xs hd]
  omega

theorem chunkMediansRun_length (d : Nat) (xs : List α) :
    (chunkMediansRun d xs).1.length = xs.length ⌈/⌉ d := by
  rw [chunkMediansRun_value, length_chunkMedians]

theorem chunkMediansRun_eq_nil_iff (d : Nat) (xs : List α) :
    (chunkMediansRun d xs).1 = [] ↔ d = 0 ∨ xs = [] := by
  rw [chunkMediansRun_value, chunkMedians_eq_nil_iff]

theorem chunkMediansRun_mem (d : Nat) (xs : List α) (a : α)
    (ha : a ∈ (chunkMediansRun d xs).1) : a ∈ xs := by
  rw [chunkMediansRun_value] at ha
  exact mem_chunkMedians d xs a ha

theorem chunkMediansRun_bound (d : Nat) (xs : List α) :
    (chunkMediansRun d xs).2 ≤
      5 * xs.length + (d ^ 2 + 4 * d + 3) * (xs.length ⌈/⌉ d) + 2 := by
  have hc := Resources.Chunks.chopRun_cost_bound d xs
  have hm := mapSlowMedianRun_bound (chop d xs) (chop_mem_ne_nil d xs) d
    (length_mem_chop d xs)
  rw [length_chop] at hm
  rw [chunkMediansRun_cost_split]
  omega

theorem chunkMediansRun_five_bound (xs : List α) :
    (chunkMediansRun 5 xs).2 ≤ 15 * xs.length + 49 := by
  have hc := Resources.Chunks.chopRun_cost_bound 5 xs
  have hm := mapSlowMedianRun_chop_five_bound xs
  rw [chunkMediansRun_cost_split]
  omega

end Resources.SelectionMedians
