import SquareKit.DependentOperation.SelectorBase
import SquareKit.DependentOperation.Local

/-! Compositional boundary proofs for the independently specified selector. -/
namespace SquareKit.DependentOperation.Selector

def bytecode {V : Nat → Type} {n} (t : Term Op V n) : Code Low V :=
  (emit @instructions t).lower lower

theorem quotation {V : Nat → Type} {n} (t : Term Op V n) :
    bytecode t = emit (fun o => (instructions o).flatMap lower) t :=
  emit_lower @instructions lower t

theorem total_sound {V : Nat → Type} (ρ : ∀ n, V n → Position n)
    {n} (t : Term Op V n) :
    (bytecode t).run runTotal (fun n v => total n (ρ n v)) = total n (eval @operate ρ t) := by
  rw [quotation]
  exact emit_sound @operate (fun o => (instructions o).flatMap lower) runTotal total
    total_local ρ t

theorem distances_sound {V : Nat → Type} (ρ : ∀ n, V n → Position n)
    {n} (t : Term Op V n) :
    (bytecode t).run runDistances (fun n v => distances n (ρ n v)) =
      distances n (eval @operate ρ t) := by
  rw [quotation]
  exact emit_sound @operate (fun o => (instructions o).flatMap lower) runDistances distances
    distances_local ρ t

end SquareKit.DependentOperation.Selector
