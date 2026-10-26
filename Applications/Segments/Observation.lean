import Applications.Segments.Maximum
import Applications.Optimization.Relations
import Mathlib.Algebra.Order.BigOperators.Group.List

/-! The selected contiguous witness and its optimum-score observation share an
independent feasible set. Forgetting the witness preserves attained optimality. -/
set_option autoImplicit false
set_option warningAsError true

namespace Segments

abbrev Problem := Nat × List Int

def feasible (i : Problem) : Set (List Int) :=
  {p | p.IsInfix i.2 ∧ p.length ≤ i.1}

def objective (_ : Problem) (p : List Int) : OrderDual Int := OrderDual.toDual p.sum

theorem segmentOptimal_iff_minimizer (bound : Nat) (xs p : List Int) :
    SegmentOptimal bound xs p ↔ p ∈ Optimization.minimizers (feasible (bound, xs))
      (objective (bound, xs)) := by
  constructor
  · intro h
    exact ⟨⟨h.1, h.2.1⟩, fun _ hq => h.2.2 _ hq.1 hq.2⟩
  · intro h
    exact ⟨h.1.1, h.1.2, fun _ hp hb => h.2 ⟨hp, hb⟩⟩

def witnessSquare : Relational.RelSquare (Optimization.inputRep Problem)
    (Optimization.membershipRep (I := Problem) (id : List Int → List Int)) :=
  Optimization.selectionSquare feasible objective id
    (fun i => maxSegmentThinScan i.1 i.2)
    (fun _ => (segmentOptimal_iff_minimizer ..).mp (maxSegmentThinScan_optimal ..))

/-- Forget the witness, retaining the original problem and all admissible scores. -/
def scoreObservation : Relational.RelSquare
    (Optimization.membershipRep (I := Problem) (id : List Int → List Int))
    (Optimization.membershipRep (I := Problem) (id : Int → Int)) :=
  Optimization.observationSquare List.sum

def scoreSquare : Relational.RelSquare (Optimization.inputRep Problem)
    (Optimization.membershipRep (I := Problem) (id : Int → Int)) :=
  Relational.compose scoreObservation witnessSquare

theorem selected_witness_optimal (i : Problem) :
    SegmentOptimal i.1 i.2 (maxSegmentThinScan i.1 i.2) := by
  exact (segmentOptimal_iff_minimizer ..).mpr
    ((witnessSquare.preserves (r := i) (s := i) rfl).2)

/-- The composed observation is attained by a globally optimal contiguous witness. -/
theorem selected_score_attained (i : Problem) :
    ∃ p, SegmentOptimal i.1 i.2 p ∧ p.sum = (scoreSquare.impl i).2 := by
  have h := (scoreSquare.preserves (r := i) (s := i) rfl).2
  obtain ⟨p, hp, he⟩ := h
  exact ⟨p, (segmentOptimal_iff_minimizer ..).mpr hp, he⟩

theorem selected_score_eq (i : Problem) (p : List Int) (hp : SegmentOptimal i.1 i.2 p) :
    (scoreSquare.impl i).2 = p.sum := by
  obtain ⟨q, hq, he⟩ := selected_score_attained i
  exact he.symm.trans (optimal_segment_sum_unique _ _ _ _ hq hp)

/-- Strictly negative input has no nonempty segment with nonnegative sum. -/
theorem maxSegmentThinScan_of_negative (bound : Nat) (xs : List Int)
    (hx : ∀ x ∈ xs, x < 0) : maxSegmentThinScan bound xs = [] := by
  let p := maxSegmentThinScan bound xs
  have hp := maxSegmentThinScan_optimal bound xs
  have nonneg := maxSegmentThinScan_nonnegative bound xs
  by_contra hn
  obtain ⟨x, hm⟩ := List.exists_mem_of_ne_nil p hn
  have each (y : Int) (hy : y ∈ p) : y < 0 := hx y (hp.1.sublist.subset hy)
  have neg := List.sum_lt_sum (fun y : Int => y) (fun _ : Int => 0)
    (fun y hy => le_of_lt (each y hy)) ⟨x, hm, each x hm⟩
  have negative : p.sum < 0 := by simpa using neg
  exact (not_lt_of_ge nonneg) negative

end Segments
