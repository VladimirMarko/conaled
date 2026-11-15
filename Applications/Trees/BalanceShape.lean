import Applications.Trees.Balance
import Applications.Trees.Shape

/-! Almost completeness and exact discrete heights of the actual consuming
balancer. Shape follows the successful sequential branches before logarithm
laws are applied. Nil-fallback wrappers remain almost complete on failure,
while requested-size height formulas retain their sufficient-input domain.
Source and statement assessment: `docs/research/fdsa-tree-balancing.md`.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Trees.Balance
universe u
variable {α : Type u}

/-- A successful consumer result is almost complete without an extra domain
premise: its actual child requests already give the required adjacent sizes. -/
theorem bal_almostComplete {n : Nat} {xs zs : List α} {t : BinaryTree α}
    (h : bal n xs = some (t, zs)) : AlmostComplete t := by
  induction n using Nat.strong_induction_on generalizing xs t zs with
  | h n ih =>
      cases n with
      | zero =>
          simp only [bal_zero, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          exact almostComplete_nil
      | succ k =>
          cases hl : bal ((k + 1) / 2) xs with
          | none => simp only [bal_succ, hl] at h; cases h
          | some p =>
              rcases p with ⟨l, ys⟩
              cases ys with
              | nil => simp only [bal_succ, hl] at h; cases h
              | cons a ys =>
                  cases hr : bal (k - (k + 1) / 2) ys with
                  | none => simp only [bal_succ, hl, hr] at h; cases h
                  | some q =>
                      rcases q with ⟨r, ws⟩
                      simp only [bal_succ, hl, hr, Option.some.injEq, Prod.mk.injEq] at h
                      rcases h with ⟨rfl, rfl⟩
                      have hleft := ih ((k + 1) / 2) (by omega)
                        (xs := xs) (t := l) (zs := a :: ys) hl
                      have hright := ih (k - (k + 1) / 2) (by omega)
                        (xs := ys) (t := r) (zs := ws) hr
                      have hleftSize := (bal_spec hl).2
                      have hrightSize := (bal_spec hr).2
                      apply almostComplete_node_of_numLeaves a l r hleft hright <;>
                        simp only [BinaryTree.numLeaves_eq_numNodes_succ,
                          hleftSize, hrightSize] <;> omega

theorem bal_height {n : Nat} {xs zs : List α} {t : BinaryTree α}
    (h : bal n xs = some (t, zs)) : t.height = Nat.clog 2 (n + 1) := by
  simpa only [BinaryTree.numLeaves_eq_numNodes_succ, (bal_spec h).2] using
    height_eq_clog_numLeaves t (bal_almostComplete h)

theorem bal_minHeight {n : Nat} {xs zs : List α} {t : BinaryTree α}
    (h : bal n xs = some (t, zs)) : minHeight t = Nat.log 2 (n + 1) := by
  simpa only [BinaryTree.numLeaves_eq_numNodes_succ, (bal_spec h).2] using
    minHeight_eq_log_numLeaves t (bal_almostComplete h)

/-- The explicit failure fallback is nil, so this invariant is unconditional. -/
theorem almostComplete_balList (n : Nat) (xs : List α) : AlmostComplete (balList n xs) := by
  cases h : bal n xs with
  | none =>
      rw [balList_of_none h]
      exact almostComplete_nil
  | some p =>
      rcases p with ⟨t, zs⟩
      rw [balList_of_some h]
      exact bal_almostComplete h

theorem height_balList {n : Nat} {xs : List α} (h : n ≤ xs.length) :
    (balList n xs).height = Nat.clog 2 (n + 1) := by
  obtain ⟨t, zs, hs⟩ := bal_exists h
  rw [balList_of_some hs]
  exact bal_height hs

theorem minHeight_balList {n : Nat} {xs : List α} (h : n ≤ xs.length) :
    minHeight (balList n xs) = Nat.log 2 (n + 1) := by
  obtain ⟨t, zs, hs⟩ := bal_exists h
  rw [balList_of_some hs]
  exact bal_minHeight hs

theorem almostComplete_balanceList (xs : List α) : AlmostComplete (balanceList xs) :=
  almostComplete_balList xs.length xs

theorem height_balanceList (xs : List α) :
    (balanceList xs).height = Nat.clog 2 (xs.length + 1) :=
  height_balList (Nat.le_refl xs.length)

theorem minHeight_balanceList (xs : List α) :
    minHeight (balanceList xs) = Nat.log 2 (xs.length + 1) :=
  minHeight_balList (Nat.le_refl xs.length)

theorem almostComplete_balTree (n : Nat) (t : BinaryTree α) : AlmostComplete (balTree n t) :=
  almostComplete_balList n (inorder t)

theorem height_balTree {n : Nat} (t : BinaryTree α) (h : n ≤ t.numNodes) :
    (balTree n t).height = Nat.clog 2 (n + 1) :=
  height_balList (by simpa only [inorder_length] using h)

theorem minHeight_balTree {n : Nat} (t : BinaryTree α) (h : n ≤ t.numNodes) :
    minHeight (balTree n t) = Nat.log 2 (n + 1) :=
  minHeight_balList (by simpa only [inorder_length] using h)

theorem almostComplete_balanceTree (t : BinaryTree α) : AlmostComplete (balanceTree t) :=
  almostComplete_balTree t.numNodes t

theorem height_balanceTree (t : BinaryTree α) :
    (balanceTree t).height = Nat.clog 2 (t.numNodes + 1) :=
  height_balTree t (Nat.le_refl t.numNodes)

theorem minHeight_balanceTree (t : BinaryTree α) :
    minHeight (balanceTree t) = Nat.log 2 (t.numNodes + 1) :=
  minHeight_balTree t (Nat.le_refl t.numNodes)

end Trees.Balance
