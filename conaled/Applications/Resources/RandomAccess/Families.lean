import Applications.Resources.RandomAccess.Bulk

/-! Worst-case families and limits of index-only and pointwise lower bounds.
Provenance and statement review: `docs/research/adwh-random-access-costs.md`. -/
namespace Resources.RandomAccessCosts
open RandomAccess
universe u
variable {α : Type u}

def perfectTree (x : α) : Nat → Tree α
  | 0 => .leaf x
  | p + 1 => node (perfectTree x p) (perfectTree x p)

theorem perfectTree_valid (x : α) (p : Nat) : Perfect p (perfectTree x p) := by
  induction p with
  | zero => exact Perfect.leaf x
  | succ p ih => exact perfect_node ih ih

/-- A single highest one-digit, preceded by exactly p zero-digits. -/
def sparse (p : Nat) (t : Tree α) : RAList α := List.replicate p .zero ++ [.one t]

theorem sparse_valid (r p : Nat) {t : Tree α} (h : Perfect (r + p) t) :
    Valid r (sparse p t) := by
  induction p generalizing r with
  | zero => exact Valid.one (by simpa using h) (Valid.nil _)
  | succ p ih =>
    change Valid r (.zero :: sparse p t)
    apply Valid.zero
    · simp [sparse]
    · exact ih (r + 1) (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h)

theorem sparse_value (p : Nat) (t : Tree α) : fromRA (sparse p t) = fromT t := by
  induction p with
  | zero => simp [sparse, fromRA]
  | succ p ih => exact ih

theorem perfectTree_values (x : α) (p : Nat) :
    fromT (perfectTree x p) = List.replicate (2 ^ p) x := by
  induction p with
  | zero => rfl
  | succ p ih =>
    simp only [perfectTree, node, fromT, ih]
    rw [List.replicate_append_replicate]
    congr 1
    rw [Nat.pow_succ]
    omega

theorem sparse_fetch_cost_at (p : Nat) {t : Tree α} (h : Perfect p t)
    (k : Nat) (hk : k < size t) :
    (fetchRARun k (sparse p t)).2 = 2 * p + 2 := by
  have aux : ∀ q, (fetchRARun k (sparse q t)).2 = q + (fetchTRun k t).2 + 1 := by
    intro q
    induction q with
    | zero => simp [sparse, fetchRARun, hk]
    | succ q ih =>
      change (fetchRARun k (sparse q t)).2 + 1 = _
      omega
  rw [aux, fetchTRun_count h]
  omega

theorem sparse_fetch_cost (p : Nat) {t : Tree α} (h : Perfect p t) :
    (fetchRARun 0 (sparse p t)).2 = 2 * p + 2 := by
  apply sparse_fetch_cost_at p h 0
  rw [size_eq_pow h]
  exact Nat.two_pow_pos _

/-- Every fixed index, including arbitrarily large indices, admits unbounded
successful lookup cost when the represented list length is unrestricted. -/
theorem no_index_only_bound (x : α) (k B : Nat) :
    ∃ ds, Inv ds ∧ (fetchRARun k ds).1 = some x ∧ B < (fetchRARun k ds).2 := by
  let p := k + B + 1
  let t := perfectTree x p
  have ht : Perfect p t := perfectTree_valid x p
  have hv : Inv (sparse p t) := sparse_valid 0 p (by simpa using ht)
  have hp : p < 2 ^ p := Nat.lt_two_pow_self
  have hk : k < 2 ^ p := by dsimp [p] at *; omega
  refine ⟨sparse p t, hv, ?_, ?_⟩
  · rw [fetchRARun_refinement hv, sparse_value, perfectTree_values]
    simp [hk]
  · rw [sparse_fetch_cost_at p ht k (by simpa [size_eq_pow ht] using hk)]
    dsimp [p]
    omega

/-- Stronger than a counterexample at log(0): no uniform bound depending only
on the index exists, even for successful lookup at the fixed index zero. -/
theorem no_index_only_zero_bound (x : α) (B : Nat) :
    ∃ ds, Inv ds ∧ (fetchRARun 0 ds).1 = some x ∧ B < (fetchRARun 0 ds).2 := no_index_only_bound x 0 B

/-- This rules out an eventual uniform O(log k) assertion as well: no arbitrary
index-only bound can cover all valid representations beyond any threshold. -/
theorem no_eventual_index_function_bound (x : α) (bound : Nat → Nat) (K : Nat) :
    ∃ k ds, K ≤ k ∧ Inv ds ∧ (fetchRARun k ds).1 = some x ∧
      bound k < (fetchRARun k ds).2 := by
  obtain ⟨ds, hv, he, hc⟩ := no_index_only_bound x K (bound K)
  exact ⟨K, ds, Nat.le_refl _, hv, he, hc⟩

theorem sparse_update_zero (p : Nat) {t : Tree α} (h : Perfect p t) (x : α) :
    updateRA 0 x (sparse p t) = sparse p (updateT 0 x t) := by
  have hp : 0 < size t := by rw [size_eq_pow h]; exact Nat.two_pow_pos _
  have aux : ∀ q, updateRA 0 x (sparse q t) = sparse q (updateT 0 x t) := by
    intro q
    induction q with
    | zero => simp [sparse, updateRA, hp]
    | succ q ih => exact congrArg (Digit.zero :: ·) ih
  exact aux p

theorem bulk_sparse_zero_cost (p : Nat) {t : Tree α} (h : Perfect p t) (xs : List α) :
    (bulkRun (sparse p t) (xs.map (fun x => (0, x)))).2 = xs.length * (2 * p + 3) := by
  induction xs generalizing t with
  | nil => simp [bulkRun_nil]
  | cons x xs ih =>
    have hc := sparse_fetch_cost p h
    have hr := ih (perfect_updateT h 0 x)
    simp only [List.map_cons, bulkRun_cons, updateRARun_count, updateRARun_value,
      sparse_update_zero p h] at *
    rw [hr, hc]
    simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

theorem bulk_head_zero_cost (t : RAList α) (x : α) (xs : List α) :
    (bulkRun (.one (.leaf x) :: t) (xs.map (fun y => (0, y)))).2 = 3 * xs.length := by
  induction xs generalizing x with
  | nil => rfl
  | cons y xs ih =>
    simp only [List.map_cons, bulkRun_cons, updateRARun, size, Nat.zero_lt_succ,
      ↓reduceIte, updateTRun, ih, List.length_cons, Nat.mul_add, Nat.mul_one]
    omega

/-- Even a single update has no uniform positive logarithmic lower bound. -/
theorem no_all_inputs_log_lower (x : α) (C : Nat) :
    ∃ ds, Inv ds ∧ (bulkRun ds [(0, x)]).2 = 3 ∧
      C * (bulkRun ds [(0, x)]).2 < (fromRA ds).length.log2 := by
  let p := 3 * C + 1
  let t := perfectTree x (p + 1)
  let ds := Digit.one (.leaf x) :: sparse p t
  have ht : Perfect (p + 1) t := perfectTree_valid x (p + 1)
  have hd : Inv ds := Valid.one (Perfect.leaf x)
    (sparse_valid 1 p (by simpa [Nat.add_comm] using ht))
  have hc : (bulkRun ds [(0, x)]).2 = 3 := rfl
  have hn : (fromRA ds).length = 1 + 2 ^ (p + 1) := by
    simp [ds, fromRA, sparse_value, fromT_length ht, fromT, Nat.add_comm]
  have hl : p + 1 ≤ (fromRA ds).length.log2 := by
    apply (Nat.le_log2 (by rw [hn]; omega)).mpr
    rw [hn]
    omega
  refine ⟨ds, hd, hc, ?_⟩
  rw [hc]
  dsimp [p] at hl
  omega

end Resources.RandomAccessCosts
