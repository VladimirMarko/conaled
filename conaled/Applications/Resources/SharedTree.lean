import Applications.Search.SharedTree.Balanced
import Applications.Resources.Growth

/-!
# Structural work of shared-tree construction

Work is recursive visits plus freshly allocated modeled cells. A visit carries
bounded arithmetic/control overhead when those operations have unit cost.
The logarithmic statements use the floor binary logarithm of the requested
unfolded node count. Bounds apply from size two; the exact formulas also cover
zero and one. No bound on Lean bignum arithmetic or machine allocation follows.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.SharedTree

open Search.SharedTree

variable {α : Type}

def completeWork (x : α) (d : Nat) (s : Store α) : Nat :=
  (completeRun x d s).2 + ((completeRun x d s).1.1.next - s.next)

def pairedWork (x : α) (n : Nat) (s : Store α) : Nat :=
  (create2Run x n s).2 + ((create2Run x n s).1.1.next - s.next)

theorem completeWork_exact (x : α) (d : Nat) (s : Store α) :
    completeWork x d s = 2 * d + 1 := by
  obtain ⟨_, _, frontier, visits⟩ := completeRun_correct x d s
  simp only [completeWork, frontier, visits]
  omega

theorem pairedWork_exact (x : α) (n : Nat) (s : Store α) :
    pairedWork x n s = 3 * Nat.log2 (n + 1) + 2 := by
  obtain ⟨_, _, _, frontier, visits⟩ := create2Run_correct x n s
  simp only [pairedWork, frontier, visits]
  omega

theorem completeWork_linear (x : α) (s : Store α) :
    Asymptotics.IsBigO Filter.atTop (fun d : Nat => (completeWork x d s : ℝ))
      (fun d : Nat => (d : ℝ)) :=
  Resources.isBigO_of_nat_bound (fun d => completeWork x d s) id 3 1 (by
    intro d hd
    rw [completeWork_exact]
    change 2 * d + 1 ≤ 3 * d
    omega)

private theorem log2_mono {m n : Nat} (h : m ≤ n) : Nat.log2 m ≤ Nat.log2 n := by
  by_cases hm : m = 0
  · subst m
    exact Nat.zero_le _
  · have hn : n ≠ 0 := by omega
    exact (Nat.le_log2 hn).mpr ((Nat.log2_self_le hm).trans h)

private theorem log2_succ_le {n : Nat} (hn : 1 ≤ n) :
    Nat.log2 (n + 1) ≤ Nat.log2 n + 1 := by
  have h := log2_mono (show n + 1 ≤ 2 * n by omega)
  rw [Nat.log2_two_mul (by omega : n ≠ 0)] at h
  exact h

private theorem log2_pos {n : Nat} (hn : 2 ≤ n) : 1 ≤ Nat.log2 n :=
  (Nat.le_log2 (by omega : n ≠ 0)).mpr (by simpa using hn)

theorem pairedWork_logarithmic (x : α) (s : Store α) :
    Asymptotics.IsBigO Filter.atTop (fun n : Nat => (pairedWork x n s : ℝ))
      (fun n : Nat => (Nat.log2 n : ℝ)) :=
  Resources.isBigO_of_nat_bound (fun n => pairedWork x n s) Nat.log2 8 2 (by
    intro n hn
    rw [pairedWork_exact]
    have h := log2_succ_le (by omega : 1 ≤ n)
    have positive := log2_pos hn
    omega)

end Resources.SharedTree
