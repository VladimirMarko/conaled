import Applications.Trees.Balance
import Applications.Resources.CallCount

/-! Actual recursive call accounting for FDSA Chapter 4 prefix balancing.
`balRun` follows the same recursive and data-dependent branches as `bal`.
Each invocation, including zero, charges one entry through `CallCount.tick`;
arithmetic, variables, pattern matching, and constructors are uncharged
primitives in this source model. Failed executions retain their actual costs.

The exact `2*n+1` law requires sufficient input. It neither counts the direct
inorder traversal preceding `balanceTree` nor establishes Lean runtime,
allocation, or integer-bit complexity. Provenance:
`docs/research/fdsa-reconstruction-map.md`.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.TreeBalance
universe u
variable {α : Type u}

/-- Execute the sequential consumer with one charge per recursive entry. -/
def balRun (n : Nat) (xs : List α) : Measured (Option (BinaryTree α × List α)) Nat :=
  CallCount.tick <|
    match n with
    | 0 => Resources.pure (some (.nil, xs))
    | k + 1 =>
        Resources.bind (balRun ((k + 1) / 2) xs) fun left =>
          match left with
          | none => Resources.pure none
          | some (_, []) => Resources.pure none
          | some (l, a :: ys) =>
              Resources.bind (balRun (k - (k + 1) / 2) ys) fun right =>
                match right with
                | none => Resources.pure none
                | some (r, zs) => Resources.pure (some (.node a l r, zs))
termination_by n
decreasing_by all_goals omega

@[simp] theorem balRun_zero (xs : List α) : balRun 0 xs = (some (.nil, xs), 1) := by
  simp only [balRun, CallCount.tick, Resources.pure]

theorem balRun_succ (k : Nat) (xs : List α) :
    balRun (k + 1) xs =
      CallCount.tick
        (Resources.bind (balRun ((k + 1) / 2) xs) fun left =>
          match left with
          | none => Resources.pure none
          | some (_, []) => Resources.pure none
          | some (l, a :: ys) =>
              Resources.bind (balRun (k - (k + 1) / 2) ys) fun right =>
                match right with
                | none => Resources.pure none
                | some (r, zs) => Resources.pure (some (.node a l r, zs))) := by
  rw [balRun]

/-- Erasing the observation agrees for successful and failed inputs alike. -/
theorem balRun_value (n : Nat) (xs : List α) :
    (balRun n xs).1 = Trees.Balance.bal n xs := by
  induction n using Nat.strong_induction_on generalizing xs with
  | h n ih =>
      cases n with
      | zero => rw [balRun_zero, Trees.Balance.bal_zero]
      | succ k =>
          rw [balRun_succ, CallCount.tick_value, Resources.bind_value,
            ih ((k + 1) / 2) (by omega) xs, Trees.Balance.bal_succ]
          cases hl : Trees.Balance.bal ((k + 1) / 2) xs with
          | none => rfl
          | some p =>
              rcases p with ⟨l, ys⟩
              cases ys with
              | nil => rfl
              | cons a ys =>
                  rw [Resources.bind_value, ih (k - (k + 1) / 2) (by omega) ys]
                  cases Trees.Balance.bal (k - (k + 1) / 2) ys with
                  | none => rfl
                  | some q => rcases q with ⟨r, zs⟩; rfl

/-- A valid size-n request makes exactly 2*n+1 calls, including empty calls. -/
theorem balRun_cost {n : Nat} {xs : List α} (h : n ≤ xs.length) :
    (balRun n xs).2 = 2 * n + 1 := by
  induction n using Nat.strong_induction_on generalizing xs with
  | h n ih =>
      cases n with
      | zero => rw [balRun_zero]
      | succ k =>
          have hleftDomain : (k + 1) / 2 ≤ xs.length := by omega
          obtain ⟨l, ys, hl⟩ := Trees.Balance.bal_exists hleftDomain
          have hleftSpec := Trees.Balance.bal_spec hl
          have hlength : xs.length = (k + 1) / 2 + ys.length := by
            rw [hleftSpec.1, List.length_append, Trees.inorder_length, hleftSpec.2]
          cases ys with
          | nil =>
              simp only [List.length_nil] at hlength
              omega
          | cons a ys =>
              simp only [List.length_cons] at hlength
              have hrightDomain : k - (k + 1) / 2 ≤ ys.length := by omega
              obtain ⟨r, zs, hr⟩ := Trees.Balance.bal_exists hrightDomain
              have hleftValue : (balRun ((k + 1) / 2) xs).1 = some (l, a :: ys) :=
                (balRun_value _ _).trans hl
              have hrightValue : (balRun (k - (k + 1) / 2) ys).1 = some (r, zs) :=
                (balRun_value _ _).trans hr
              have hleftCost := ih ((k + 1) / 2) (by omega) hleftDomain
              have hrightCost := ih (k - (k + 1) / 2) (by omega) hrightDomain
              rw [balRun_succ, CallCount.tick_cost]
              simp only [Resources.bind, hleftValue, hrightValue, Resources.pure]
              rw [hleftCost, hrightCost]
              omega

/-- Package the independently established value and cost observations. -/
theorem balRun_eq {n : Nat} {xs : List α} (h : n ≤ xs.length) :
    balRun n xs = (Trees.Balance.bal n xs, 2 * n + 1) := by
  apply Prod.ext
  · exact balRun_value n xs
  · exact balRun_cost h

theorem balRun_of_some {n : Nat} {xs zs : List α} {t : BinaryTree α}
    (h : Trees.Balance.bal n xs = some (t, zs)) :
    balRun n xs = (some (t, zs), 2 * n + 1) := by
  have hdomain := (Trees.Balance.bal_succeeds_iff n xs).mp ⟨t, zs, h⟩
  rw [balRun_eq hdomain, h]

/-- Sequential clients retain their exact suffix as well as the call count. -/
theorem balRun_prefix (prefix suffix : List α) :
    ∃ t, balRun prefix.length (prefix ++ suffix) =
        (some (t, suffix), 2 * prefix.length + 1) ∧
      Trees.inorder t = prefix ∧ t.numNodes = prefix.length := by
  obtain ⟨t, h, hi, hn⟩ := Trees.Balance.bal_prefix prefix suffix
  exact ⟨t, balRun_of_some h, hi, hn⟩

end Resources.TreeBalance
