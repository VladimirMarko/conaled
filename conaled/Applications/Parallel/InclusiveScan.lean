import Applications.Parallel.ScanPlan
import SquareKit.ListFusion

/-!
# Inclusive states from certified parallel scanners

Append the final total to the exclusive prefixes. Multiplication remains
ordered, and only the specialization to a monoid uses parallel scanning.
Arbitrary accumulator fusion remains in `SquareKit.ListFusion`.
-/

namespace Applications.Parallel

universe u v
variable {M : Type u} [Monoid M]

/-- Inclusive states contain the initial seed and the final accumulator. -/
theorem sequential_scanl (seed : M) (xs : List M) :
    (sequential seed xs).1 ++ [(sequential seed xs).2] = xs.scanl (· * ·) seed := by
  induction xs generalizing seed with
  | nil => simp
  | cons x xs ih => simp only [sequential_cons, List.cons_append, List.scanl_cons, ih]

namespace Scanner

/-- Decode the existing result, without rerunning a sequential scan. -/
def inclusive {s : Shape} (p : Scanner s M) (x : s.Data M) : List M :=
  let result := p.run x
  s.flatten result.1 ++ [result.2]

theorem inclusive_correct {s : Shape} (p : Scanner s M) (x : s.Data M) :
    p.inclusive x = (s.flatten x).scanl (· * ·) 1 := by
  have h := congrArg (fun result : List M × M => result.1 ++ [result.2]) (p.correct x)
  exact h.trans (sequential_scanl 1 _)

/-- Interpret all states using a law that need hold only on reachable states. -/
theorem inclusive_fusion {s : Shape} {B : Type v} (p : Scanner s M)
    (h : M → B) (g : B → M → B) (P : M → Prop)
    (base : P 1) (step : ∀ y x, P y → P (y * x))
    (law : ∀ y x, P y → h (y * x) = g (h y) x) (x : s.Data M) :
    (p.inclusive x).map h = (s.flatten x).scanl g (h 1) := by
  rw [p.inclusive_correct]
  exact SquareKit.ListFusion.scanl_reachable (· * ·) g h P 1 base step law _

end Scanner

end Applications.Parallel
