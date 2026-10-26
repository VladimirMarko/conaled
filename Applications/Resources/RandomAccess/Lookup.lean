import Applications.Sequences.RandomAccess.Representation
import Applications.Resources.Workload
import Mathlib.Data.Nat.Log

/-! Actual branch visits and represented-length logarithmic bounds.
Provenance and statement review: `docs/research/adwh-random-access-costs.md`. -/
namespace Resources.RandomAccessCosts
open RandomAccess
universe u
variable {α : Type u}

def fetchListRun (k : Nat) : List α → Option α × Nat
  | [] => (none, 1)
  | x :: xs =>
      if k = 0 then (some x, 1)
      else let rest := fetchListRun (k - 1) xs; (rest.1, rest.2 + 1)

theorem fetchListRun_value (k : Nat) (xs : List α) :
    (fetchListRun k xs).1 = fetch k xs := by
  induction xs generalizing k with
  | nil => rfl
  | cons x xs ih => cases k <;> simp [fetchListRun, fetch, ih]

theorem fetchListRun_count (k : Nat) (xs : List α) (hk : k < xs.length) :
    (fetchListRun k xs).2 = k + 1 := by
  induction xs generalizing k with
  | nil => simp at hk
  | cons x xs ih =>
    cases k with
    | zero => rfl
    | succ k => simp [fetchListRun, ih k (by simpa using hk)]

def fetchTRun (k : Nat) : Tree α → Option α × Nat
  | .leaf x => (if k = 0 then some x else none, 1)
  | .node n l r =>
      let rest := if k < n / 2 then fetchTRun k l else fetchTRun (k - n / 2) r
      (rest.1, rest.2 + 1)

theorem fetchTRun_value (k : Nat) (t : Tree α) : (fetchTRun k t).1 = fetchT k t := by
  induction t generalizing k with
  | leaf x => rfl
  | node n l r ihl ihr => simp only [fetchTRun, fetchT]; split <;> simp [ihl, ihr]

theorem fetchTRun_count {p : Nat} {t : Tree α} (h : Perfect p t) (k : Nat) :
    (fetchTRun k t).2 = p + 1 := by
  induction h generalizing k with
  | leaf x => rfl
  | node p l r hl hr ihl ihr => simp only [fetchTRun]; split <;> simp [ihl, ihr]

def fetchRARun (k : Nat) : RAList α → Option α × Nat
  | [] => (none, 1)
  | .zero :: ds => let rest := fetchRARun k ds; (rest.1, rest.2 + 1)
  | .one t :: ds =>
      let rest := if k < size t then fetchTRun k t else fetchRARun (k - size t) ds
      (rest.1, rest.2 + 1)

theorem fetchRARun_value (k : Nat) (ds : RAList α) :
    (fetchRARun k ds).1 = fetchRA k ds := by
  induction ds generalizing k with
  | nil => rfl
  | cons d ds ih =>
    cases d with
    | zero => exact ih k
    | one t => simp only [fetchRARun, fetchRA]; split <;> simp [fetchTRun_value, ih]

theorem fetchRARun_refinement {r : Nat} {ds : RAList α} (h : Valid r ds) (k : Nat) :
    (fetchRARun k ds).1 = (fromRA ds)[k]? := by
  rw [fetchRARun_value, fetchRA_refinement h]

theorem fetchRARun_count_bound {r : Nat} {ds : RAList α} (h : Valid r ds) (k : Nat) :
    (fetchRARun k ds).2 ≤ r + 2 * ds.length + 1 := by
  induction h generalizing k with
  | nil r => simp [fetchRARun]
  | zero hne h ih =>
    have hb := ih k
    simp only [fetchRARun, List.length_cons]
    omega
  | @one r t ds ht h ih =>
    simp only [fetchRARun]
    split
    · rw [fetchTRun_count ht]
      simp only [List.length_cons]
      omega
    · have hb := ih (k - size t)
      simp only [List.length_cons]
      omega

/-- The highest one-digit cannot be hidden by trailing zeros in a valid list. -/
theorem valid_length_lower {r : Nat} {ds : RAList α}
    (h : Valid r ds) (hne : ds ≠ []) :
    2 ^ (r + ds.length - 1) ≤ (fromRA ds).length := by
  induction h with
  | nil r => exact False.elim (hne rfl)
  | @zero r ds htail h ih =>
    have hi := ih htail
    simpa only [List.length_cons, fromRA, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using hi
  | @one r t ds ht h ih =>
    cases ds with
    | nil => simp [fromRA, fromT_length ht]
    | cons d ds =>
      have hi := ih (by simp)
      have he : r + (Digit.one t :: d :: ds).length - 1 =
          (r + 1) + (d :: ds).length - 1 := by simp only [List.length_cons]; omega
      rw [he]
      exact Nat.le_trans hi (by simp [fromRA])

theorem digits_log_bound {ds : RAList α} (h : Inv ds) :
    ds.length ≤ (fromRA ds).length.log2 + 1 := by
  by_cases he : ds = []
  · simp [he]
  · have hb := valid_length_lower h he
    have hn : (fromRA ds).length ≠ 0 := by
      intro hz
      have hp : 0 < 2 ^ (0 + ds.length - 1) := Nat.two_pow_pos _
      omega
    have hl := (Nat.le_log2 hn).mpr hb
    omega

theorem valid_length_upper {r : Nat} {ds : RAList α} (h : Valid r ds) :
    (fromRA ds).length + 2 ^ r ≤ 2 ^ (r + ds.length) := by
  induction h with
  | nil r => simp [fromRA]
  | @zero r ds hne h ih =>
    have he : r + (Digit.zero :: ds).length = (r + 1) + ds.length := by
      simp only [List.length_cons]; omega
    rw [he]
    simp only [fromRA, Nat.pow_succ] at *
    omega
  | @one r t ds ht h ih =>
    have he : r + (Digit.one t :: ds).length = (r + 1) + ds.length := by
      simp only [List.length_cons]; omega
    rw [he]
    simp only [fromRA, List.length_append, fromT_length ht, Nat.pow_succ] at *
    omega

theorem digits_log_exact {ds : RAList α} (h : Inv ds) (hne : ds ≠ []) :
    ds.length = (fromRA ds).length.log2 + 1 := by
  have hl := digits_log_bound h
  have hu := valid_length_upper h
  have hn : (fromRA ds).length ≠ 0 := by
    intro hz
    exact fromRA_ne_nil h hne (List.length_eq_zero_iff.mp hz)
  have hb : (fromRA ds).length < 2 ^ ds.length := by
    simp only [Nat.zero_add, Nat.pow_zero] at hu
    omega
  have ht := (Nat.log2_lt hn).mpr hb
  omega

/-- Looking up the last element reaches the highest one-digit and its full depth. -/
theorem fetchRARun_last_count {r : Nat} {ds : RAList α}
    (h : Valid r ds) (hne : ds ≠ []) :
    (fetchRARun ((fromRA ds).length - 1) ds).2 = r + 2 * ds.length := by
  induction h with
  | nil r => exact False.elim (hne rfl)
  | @zero r ds htail h ih =>
    have hi := ih htail
    simp only [fetchRARun, fromRA, List.length_cons]
    omega
  | @one r t ds ht h ih =>
    have htpos : 0 < (fromT t).length := by
      rw [fromT_length ht]; exact Nat.two_pow_pos _
    by_cases he : ds = []
    · subst ds
      have hk : (fromRA [.one t]).length - 1 < size t := by
        simp only [fromRA, List.length_append, List.length_nil, Nat.add_zero,
          fromT_length_eq_size ht] at *
        omega
      rw [fetchRARun, ite_eq_left hk, fetchTRun_count ht]
      simp
    · have hp : 0 < (fromRA ds).length :=
        List.length_pos_iff.mpr (fromRA_ne_nil h he)
      have hk : ¬ (fromRA (.one t :: ds)).length - 1 < size t := by
        simp only [fromRA, List.length_append, fromT_length_eq_size ht]
        omega
      have hs : (fromRA (.one t :: ds)).length - 1 - size t =
          (fromRA ds).length - 1 := by
        simp only [fromRA, List.length_append, fromT_length_eq_size ht]
        omega
      rw [fetchRARun, ite_eq_right hk, hs, ih he]
      simp only [List.length_cons]
      omega

theorem fetchRARun_log_bound {ds : RAList α} (h : Inv ds) (k : Nat) :
    (fetchRARun k ds).2 ≤ 2 * (fromRA ds).length.log2 + 3 := by
  have hc := fetchRARun_count_bound h k
  have hl := digits_log_bound h
  omega

def updateTRun (k : Nat) (x : α) : Tree α → Tree α × Nat
  | .leaf y => (if k = 0 then .leaf x else .leaf y, 1)
  | .node n l r =>
      if k < n / 2 then
        let next := updateTRun k x l
        (.node n next.1 r, next.2 + 1)
      else
        let next := updateTRun (k - n / 2) x r
        (.node n l next.1, next.2 + 1)

theorem updateTRun_value (k : Nat) (x : α) (t : Tree α) :
    (updateTRun k x t).1 = updateT k x t := by
  induction t generalizing k with
  | leaf y => rfl
  | node n l r ihl ihr => simp only [updateTRun, updateT]; split <;> simp [ihl, ihr]

theorem updateTRun_count (k : Nat) (x : α) (t : Tree α) :
    (updateTRun k x t).2 = (fetchTRun k t).2 := by
  induction t generalizing k with
  | leaf y => rfl
  | node n l r ihl ihr => simp only [updateTRun, fetchTRun]; split <;> simp [ihl, ihr]

def updateRARun (k : Nat) (x : α) : RAList α → RAList α × Nat
  | [] => ([], 1)
  | .zero :: ds =>
      let rest := updateRARun k x ds
      (.zero :: rest.1, rest.2 + 1)
  | .one t :: ds =>
      if k < size t then
        let next := updateTRun k x t
        (.one next.1 :: ds, next.2 + 1)
      else
        let rest := updateRARun (k - size t) x ds
        (.one t :: rest.1, rest.2 + 1)

theorem updateRARun_value (k : Nat) (x : α) (ds : RAList α) :
    (updateRARun k x ds).1 = updateRA k x ds := by
  induction ds generalizing k with
  | nil => rfl
  | cons d ds ih =>
    cases d with
    | zero => simp [updateRARun, updateRA, ih]
    | one t => simp only [updateRARun, updateRA]; split <;> simp [updateTRun_value, ih]

theorem updateRARun_count (k : Nat) (x : α) (ds : RAList α) :
    (updateRARun k x ds).2 = (fetchRARun k ds).2 := by
  induction ds generalizing k with
  | nil => rfl
  | cons d ds ih =>
    cases d with
    | zero => simp [updateRARun, fetchRARun, ih]
    | one t => simp only [updateRARun, fetchRARun]; split <;> simp [updateTRun_count, ih]

theorem updateRARun_refinement {r : Nat} {ds : RAList α}
    (h : Valid r ds) (k : Nat) (x : α) :
    fromRA (updateRARun k x ds).1 = (fromRA ds).set k x := by
  rw [updateRARun_value, updateRA_refinement h]

theorem updateRARun_log_bound {ds : RAList α} (h : Inv ds) (k : Nat) (x : α) :
    (updateRARun k x ds).2 ≤ 2 * (fromRA ds).length.log2 + 3 := by
  rw [updateRARun_count]
  exact fetchRARun_log_bound h k

theorem updateRA_digit_length (k : Nat) (x : α) (ds : RAList α) :
    (updateRA k x ds).length = ds.length := by
  induction ds generalizing k with
  | nil => rfl
  | cons d ds ih =>
    cases d with
    | zero => simp [updateRA, ih]
    | one t => simp only [updateRA]; split <;> simp [ih]


end Resources.RandomAccessCosts
