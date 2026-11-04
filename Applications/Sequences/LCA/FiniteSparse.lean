import Applications.Sequences.LCA.Sparse
import Applications.Resources.Measured

/-! Finite sparse rows. Each level is computed from the preceding stored row.
Out-of-range cells wrap, but the correctness theorem only exposes intervals
contained in the input, where no wrap occurs. -/
namespace Sequences.LCA
open PreparedRMQ Resources
variable {α : Type} [LinearOrder α]

def nextSparseRow (row : Vector α n) (level : Nat) : Vector α n :=
  Vector.ofFn fun i : Fin n => min (row[i.val])
    (row[(i.val + 2 ^ level) % n]'(Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)))

def finiteRow (input : Vector α n) : Nat → Vector α n
  | 0 => input
  | k+1 => nextSparseRow (finiteRow input k) k

def vectorRead (input : Vector α n) (hn : 0 < n) (i : Nat) : α :=
  input[i % n]'(Nat.mod_lt _ hn)

theorem finiteRow_correct (input : Vector α n) (hn : 0 < n) (k : Nat)
    (i : Fin n) (hi : i.val + 2 ^ k ≤ n) :
    (finiteRow input k)[i.val] = sparseRow (vectorRead input hn) k i.val := by
  induction k generalizing i with
  | zero => simp [finiteRow, sparseRow, vectorRead, Nat.mod_eq_of_lt i.isLt]
  | succ k ih =>
    have hp := Nat.two_pow_pos k
    have h₁ : i.val + 2 ^ k ≤ n := by rw [pow_succ] at hi; omega
    have h₂ : i.val + 2 ^ k < n := by rw [pow_succ] at hi; omega
    simp only [finiteRow, nextSparseRow, Vector.getElem_ofFn, sparseRow]
    rw [ih i h₁]
    congr 1
    have hj : (i.val + 2 ^ k) % n = i.val + 2 ^ k := Nat.mod_eq_of_lt h₂
    have hh : (i.val + 2 ^ k) % n + 2 ^ k ≤ n := by rw [hj]; rw [pow_succ] at hi; omega
    simpa only [hj] using ih ⟨(i.val + 2 ^ k) % n, Nat.mod_lt _ hn⟩ hh

/-- Materialized levels use the most recent stored row; earlier levels are
retained for indexed query lookup. -/
def buildSparse (input : Vector α n) : (levels : Nat) → Vector (Vector α n) (levels+1)
  | 0 => #v[input]
  | k+1 =>
    let previous := buildSparse input k
    previous.push (nextSparseRow previous[k] k)

theorem buildSparse_get (input : Vector α n) (levels : Nat) (k : Fin (levels+1)) :
    (buildSparse input levels)[k.val] = finiteRow input k.val := by
  induction levels with
  | zero =>
    have hk : k = 0 := by apply Fin.ext; omega
    subst k
    rfl
  | succ levels ih =>
    by_cases hk : k.val < levels+1
    · simpa [buildSparse, Vector.get, hk, Nat.ne_of_lt hk] using ih ⟨k.val, hk⟩
    · have he : k.val = levels+1 := by omega
      simp only [buildSparse, he, Vector.getElem_push_eq, finiteRow]
      congr 1
      exact ih ⟨levels, by omega⟩

end Sequences.LCA
