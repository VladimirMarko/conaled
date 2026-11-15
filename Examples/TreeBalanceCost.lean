import Applications.Resources.TreeBalance
import Examples.TreeBalance

/-! Connected clients of the actual prefix-balancing execution.
The expected successful counts are 1, 7, and 21 at sizes 0, 3, and 10.
The failed request for one node from an empty list costs 2, demonstrating why
the successful-input premise cannot be removed from the general count law.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.TreeBalanceCost
open Trees.Balance Resources.TreeBalance Examples.TreeBalance
universe u
variable {α : Type u}

/-- A generic valid execution supplies the ordered decomposition and exact cost. -/
theorem valid_execution {n : Nat} {xs : List α} (h : n ≤ xs.length) :
    ∃ t zs, balRun n xs = (some (t, zs), 2 * n + 1) ∧
      xs = Trees.inorder t ++ zs ∧ t.numNodes = n ∧ zs = xs.drop n := by
  obtain ⟨t, zs, hs⟩ := bal_exists h
  exact ⟨t, zs, balRun_of_some hs, (bal_spec hs).1, (bal_spec hs).2, bal_suffix hs⟩

theorem prefix_execution («prefix» suffix : List α) :
    ∃ t, balRun «prefix».length («prefix» ++ suffix) =
        (some (t, suffix), 2 * «prefix».length + 1) ∧
      Trees.inorder t = «prefix» ∧ t.numNodes = «prefix».length :=
  balRun_prefix «prefix» suffix

theorem zero_execution (xs : List α) : balRun 0 xs = (some (.nil, xs), 1) :=
  balRun_zero xs

theorem three_execution : balRun 3 [9, 3, 7, 8, 8] = (some (threeTree, [8, 8]), 7) :=
  balRun_of_some three_consumption

theorem three_call_count : (balRun 3 [9, 3, 7, 8, 8]).2 = 7 :=
  balRun_cost (by decide)

theorem figure_execution : balRun 10 figureInput = (some (figureTree, []), 21) :=
  balRun_of_some figure_consumption

theorem figure_call_count : (balRun 10 figureInput).2 = 21 :=
  balRun_cost (by decide)

theorem failed_one_execution : balRun 1 ([] : List Nat) = (none, 2) := by
  rw [balRun_succ]
  simp only [show (0 + 1) / 2 = 0 from rfl, balRun_zero,
    Resources.bind, Resources.pure, Resources.CallCount.tick]
  rfl

theorem failed_count_differs : (balRun 1 ([] : List Nat)).2 ≠ 2 * 1 + 1 := by
  rw [failed_one_execution]
  decide

/-- Refinement is unconditional even where the successful-input count is false. -/
theorem failed_value_refines :
    (balRun 1 ([] : List Nat)).1 = bal 1 ([] : List Nat) :=
  balRun_value _ _

end Examples.TreeBalanceCost
