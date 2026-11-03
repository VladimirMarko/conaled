import SquareKit.RelationalCategory
import Applications.Intervals.Arithmetic
import Applications.Timing.Digital

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace Examples.RelationalBridge
open SquareKit Relational

/-- Multiplication's local enclosure proof survives the shared witness map. -/
theorem interval_multiplication {I J : IntervalAnalysis.Interval} {x y : ℚ}
    (hx : IntervalAnalysis.Contains I x) (hy : IntervalAnalysis.Contains J y) :
    let p : (witness (product IntervalAnalysis.representation IntervalAnalysis.representation)).R :=
      ⟨((I, J), (x, y)), ⟨hx, hy⟩⟩
    let q := (RelationalCategory.witnessMap.map IntervalAnalysis.mulSquare).left p
    IntervalAnalysis.Contains q.val.1 q.val.2 := by
  exact (RelationalCategory.witnessMap.map IntervalAnalysis.mulSquare).left
    ⟨((I, J), (x, y)), ⟨hx, hy⟩⟩ |>.property

/-- Arbitrary stable inputs compose through the shared relational operations. -/
theorem timing_composition {a b c : FirstOrderCompiler.Ty}
    (g : Applications.Timing.Digital b c) (f : Applications.Timing.Digital a b)
    {s τ v} (h : Applications.Timing.Stable a s τ v) :
    Applications.Timing.Stable c (g.analog (f.analog s))
      (g.timing (f.timing τ)) (g.value (f.value v)) :=
  (RelationalCategory.ops.comp g.relation f.relation).preserves (r := s) (s := (τ, v)) h

/-- The very same composition is a comma morphism on total witnesses. -/
theorem timing_witness_composition {a b c : FirstOrderCompiler.Ty}
    (g : Applications.Timing.Digital b c) (f : Applications.Timing.Digital a b) :
    RelationalCategory.witnessMap.map (Applications.Timing.Digital.compose g f).relation =
      Comma.Exact.categoryOps.comp (RelationalCategory.witnessMap.map g.relation)
        (RelationalCategory.witnessMap.map f.relation) := by
  rw [Applications.Timing.Digital.relation_compose]
  exact RelationalCategory.witnessMap_laws.comp _ _

/-- A nonidentity graph conversion retains both distinct horizontal functions. -/
def successor : Squares.Square (⟨Nat, Nat, fun n => n + 3⟩ : Squares.Rep)
    (⟨Nat, Nat, fun n => n + 3⟩ : Squares.Rep) where
  impl n := n + 1
  spec n := n + 1
  commutes n := Nat.add_right_comm n 1 3

theorem successor_graph :
    (RelationalCategory.graphMap.map (Comma.Exact.ofSquare successor)).impl (4 : Nat) = (5 : Nat) ∧
    (RelationalCategory.graphMap.map (Comma.Exact.ofSquare successor)).spec (7 : Nat) = (8 : Nat) ∧
    toSquare (RelationalCategory.graphMap.map (Comma.Exact.ofSquare successor)) = successor :=
  ⟨rfl, rfl, RelationalCategory.exact_roundtrip successor⟩
end Examples.RelationalBridge
