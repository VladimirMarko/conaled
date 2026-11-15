import SquareKit.GuardedStreams
import Mathlib.Data.ZMod.Basic

/-! The guarded solution theorem is used for the original defining equations,
modular reuse, changed initial fillers, substitution and a lossy interpretation. -/
namespace SquareKit.GuardedStreams.Examples

example (n : Nat) : (ones : Stream Nat) n = 1 := ones_eq n
example (n : Nat) : (sums : Stream Nat) n = n + 1 := sums_eq n
example : (sums : Stream Nat) 0 = 1 := sums_eq 0
example : (sums : Stream Nat) 4 = 5 := sums_eq 4

/-- The recursive operation is replaced using its independently proved meaning,
not by assuming either fixed-point equation has a unique solution. -/
theorem replace_ones :
    solve (sumsBody : Stream Nat → Stream Nat) 1 =
      solve (cons 1 ∘ addLeft (fun _ => 1)) 47 := by
  apply solve_congr sums_guarded
  intro s
  simp only [sumsBody, Function.comp_apply]
  congr 1
  funext n
  simp only [addLeft, ones_eq]

/-- Causal context after a guard: the whole substituted body stays admissible. -/
def successor (s : Stream Nat) : Stream Nat := fun n => s n + 1

theorem successor_causal : Causal successor := by
  intro n s t h
  exact congrArg (fun x => x + 1) (h n (Nat.le_refl n))

theorem outer_context_guarded : Guarded (successor ∘ cons 0) :=
  causal_comp_guarded successor_causal (cons_guarded 0)

theorem outer_context_meaning : solve (successor ∘ cons 0) 19 = fun n => n + 1 := by
  apply Eq.symm
  apply unique outer_context_guarded
  funext n
  cases n <;> rfl

/-- Two causal substitutions can be composed before a guard. -/
theorem nested_substitution_guarded : Guarded (cons 0 ∘ (successor ∘ successor)) :=
  guarded_comp_causal (cons_guarded 0) (causal_comp successor_causal successor_causal)

/-- Reduction modulo two is noninjective, but transports the entire recursively
constructed solution via the local interpretation square. -/
def parity : Nat →+ ZMod 2 := Nat.castAddMonoidHom (ZMod 2)

theorem parity_sums : parity ∘ (sums : Stream Nat) = (sums : Stream (ZMod 2)) :=
  sums_map parity (by simp [parity])

theorem parity_five : (sums : Stream (ZMod 2)) 4 = 1 := by
  rw [← congrFun parity_sums 4]
  change parity ((sums : Stream Nat) 4) = 1
  rw [sums_eq]
  rfl

theorem parity_not_injective : ¬ Function.Injective parity := by
  intro h
  have bad : (0 : Nat) = 2 := h (by decide)
  contradiction

example : ¬ Guarded (id : Stream Nat → Stream Nat) := identity_not_guarded
example : (fun _ : Nat => 0) ≠ (fun _ : Nat => 1) := identity_two_solutions.2.2

end SquareKit.GuardedStreams.Examples
