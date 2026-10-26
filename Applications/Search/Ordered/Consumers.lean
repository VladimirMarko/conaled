import Applications.Search.Ordered.Global
import Squares
import Mathlib.Data.Nat.Find

/-! Exact inversion and rounding share the proved search algorithms through squares. -/
set_option autoImplicit false
set_option warningAsError true
namespace OrderedSearch

/-- The standard least witness, independently of either search implementation. -/
def leastIndex (f : Nat → Nat) (hf : StrictMono f) (target : Nat) : Nat :=
  Nat.find (show ∃ n, target ≤ f n from ⟨target, hf.le_apply⟩)

theorem leastIndex_spec (f : Nat → Nat) (hf : StrictMono f) (target : Nat) :
    LeastThreshold f target (leastIndex f hf target) :=
  by
    unfold LeastThreshold leastIndex
    exact ⟨Nat.find_spec (p := fun n => target ≤ f n) _, fun _ h => Nat.find_min' (p := fun n => target ≤ f n) _ h⟩

abbrev natRep : Squares.Rep := ⟨Nat, Nat, id⟩
abbrev optionalIndexRep : Squares.Rep := ⟨Option Nat, Option Nat, id⟩
abbrev roundedRep : Squares.Rep := ⟨Nat × Nat, Nat × Nat, id⟩

/-- Actual doubling and binary threshold search followed by the final equality test. -/
def preimageSquare (f : Nat → Nat) (hf : StrictMono f) :
    Squares.Square natRep optionalIndexRep where
  impl target := (search4 f hf target).head?
  spec target := (search f target).head?
  commutes target := congrArg List.head? (search4_eq_search f hf target)

/-- Interpret an optional index witness as its represented value. -/
def valueSquare (f : Nat → Nat) : Squares.Square optionalIndexRep optionalIndexRep where
  impl := Option.map f
  spec := Option.map f
  commutes _ := rfl

def preimageValue (f : Nat → Nat) (hf : StrictMono f) :
    Squares.Square natRep optionalIndexRep :=
  Squares.compose (valueSquare f) (preimageSquare f hf)

theorem preimage_some_iff (f : Nat → Nat) (hf : StrictMono f) (target n : Nat) :
    (preimageSquare f hf).impl target = some n ↔ f n = target := by
  have he := (preimageSquare f hf).commutes target
  change (search4 f hf target).head? = (search f target).head? at he
  rw [show (preimageSquare f hf).impl target = (search f target).head? from he]
  constructor
  · intro h
    exact (mem_search f hf target n).mp (List.mem_of_mem_head? h)
  · intro h
    have hs : search f target = [n] := by
      apply short_lists_eq
      · rw [← search1_eq_search]
        exact exhaustiveInterval_length_le f hf target 0 (target + 1)
      · simp
      · intro x
        rw [mem_search f hf, List.mem_singleton]
        exact ⟨fun hx => hf.injective (hx.trans h.symm), fun hx => hx ▸ h⟩
    rw [hs]
    rfl

theorem preimage_none_iff (f : Nat → Nat) (hf : StrictMono f) (target : Nat) :
    (preimageSquare f hf).impl target = none ↔ ∀ n, f n ≠ target := by
  constructor
  · intro h n hn
    have := (preimage_some_iff f hf target n).mpr hn
    rw [h] at this
    contradiction
  · intro h
    cases he : (preimageSquare f hf).impl target with
    | none => rfl
    | some n => exact False.elim (h n ((preimage_some_iff f hf target n).mp he))

theorem preimageValue_hit (f : Nat → Nat) (hf : StrictMono f) (target n : Nat)
    (h : f n = target) : (preimageValue f hf).impl target = some target := by
  change ((preimageSquare f hf).impl target).map f = some target
  rw [(preimage_some_iff f hf target n).mpr h]
  simp [h]

theorem preimageValue_miss (f : Nat → Nat) (hf : StrictMono f) (target : Nat)
    (h : ∀ n, f n ≠ target) : (preimageValue f hf).impl target = none := by
  change ((preimageSquare f hf).impl target).map f = none
  rw [(preimage_none_iff f hf target).mpr h]
  rfl

/-- The exact threshold square uses the standard least-witness specification. -/
def thresholdSquare (f : Nat → Nat) (hf : StrictMono f) : Squares.Square natRep natRep where
  impl target := smallest f target (bound f hf target)
  spec := leastIndex f hf
  commutes target := leastThreshold_unique f target _ _
    (smallest_spec f hf target _) (leastIndex_spec f hf target)

def roundingObservation (f : Nat → Nat) : Squares.Square natRep roundedRep where
  impl n := (n, f n)
  spec n := (n, f n)
  commutes _ := rfl

def roundUp (f : Nat → Nat) (hf : StrictMono f) : Squares.Square natRep roundedRep :=
  Squares.compose (roundingObservation f) (thresholdSquare f hf)

/-- Rounding returns a least index and the actual value at that index. -/
theorem roundUp_spec (f : Nat → Nat) (hf : StrictMono f) (target : Nat) :
    let p := (roundUp f hf).impl target
    p.2 = f p.1 ∧ target ≤ p.2 ∧ ∀ j, j < p.1 → f j < target := by
  have he := (roundUp f hf).commutes target
  change (roundUp f hf).impl target = (leastIndex f hf target, f (leastIndex f hf target)) at he
  rw [he]
  have hs := leastIndex_spec f hf target
  exact ⟨rfl, hs.1, fun j hj => Nat.lt_of_not_ge (fun h => Nat.not_le_of_gt hj (hs.2 j h))⟩

/-- Away from index zero, the returned value brackets the target with its predecessor. -/
theorem roundUp_sandwich (f : Nat → Nat) (hf : StrictMono f) (target : Nat)
    (h : 0 < ((roundUp f hf).impl target).1) :
    f (((roundUp f hf).impl target).1 - 1) < target ∧
      target ≤ ((roundUp f hf).impl target).2 := by
  have hs := roundUp_spec f hf target
  exact ⟨hs.2.2 _ (by omega), hs.2.1⟩

end OrderedSearch
