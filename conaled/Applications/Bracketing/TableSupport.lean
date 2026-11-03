import Applications.DynamicProgramming.Batch
import Applications.Bracketing.Cached

namespace Bracketing
open DynamicProgramming
variable {α β : Type}

def interval (ws : List α) (i j : Nat) : List α := (ws.drop i).take (j+1-i)

theorem interval_length (ws : List α) (i j : Nat) (hij : i ≤ j) (hj : j < ws.length) :
    (interval ws i j).length = j+1-i := by
  simp only [interval, List.length_take, List.length_drop]
  exact Nat.min_eq_left (by omega)

theorem interval_nonempty (ws : List α) (i j : Nat) (hij : i ≤ j) (hj : j < ws.length) :
    interval ws i j ≠ [] := by
  intro he
  have hl := interval_length ws i j hij hj
  rw [he] at hl
  simp only [List.length_nil] at hl
  omega

theorem interval_singleton (ws : List α) (i : Nat) (hi : i < ws.length) :
    interval ws i i = [ws[i]] := by
  simp [interval, List.take_one, hi]

theorem interval_whole (ws : List α) (hn : ws ≠ []) : interval ws 0 (ws.length-1) = ws := by
  have hp := List.length_pos_iff.mpr hn
  simp [interval, Nat.sub_add_cancel (by omega : 1 ≤ ws.length)]

theorem interval_take_cut (ws : List α) (i j k : Nat) (hik : i ≤ k) (hkj : k < j) :
    (interval ws i j).take (k+1-i) = interval ws i k := by
  simp only [interval, List.take_take]
  congr 1
  omega

theorem interval_drop_cut (ws : List α) (i j k : Nat) (hik : i ≤ k) :
    (interval ws i j).drop (k+1-i) = interval ws (k+1) j := by
  simp only [interval, List.drop_take, List.drop_drop]
  rw [show i+(k+1-i)=k+1 by omega,
    show j+1-i-(k+1-i)=j+1-(k+1) by omega]

theorem interval_split (ws : List α) (i j k : Nat) (hik : i ≤ k) (hkj : k < j) :
    interval ws i j = interval ws i k ++ interval ws (k+1) j := by
  rw [← interval_take_cut ws i j k hik hkj, ← interval_drop_cut ws i j k hik]
  exact (List.take_append_drop _ _).symm

def cellIndex (n i j : Nat) : Nat := i * n + j

theorem cellIndex_lt (n i j : Nat) (hi : i < n) (hj : j < n) :
    cellIndex n i j < n * n := by
  have h1 : i * n + j < (i + 1) * n := by
    rw [Nat.add_mul, Nat.one_mul]
    omega
  exact Nat.lt_of_lt_of_le h1 (Nat.mul_le_mul_right n (by omega))

theorem cellIndex_injective (n i j p q : Nat) (hj : j < n) (hq : q < n)
    (he : cellIndex n i j = cellIndex n p q) : i = p ∧ j = q := by
  have hd := congrArg (fun k => k / n) he
  have hp : 0 < n := by omega
  simp only [cellIndex] at hd
  rw [Nat.mul_comm i n, Nat.mul_comm p n, Nat.mul_add_div hp, Nat.mul_add_div hp,
    Nat.div_eq_of_lt hj, Nat.div_eq_of_lt hq, Nat.add_zero, Nat.add_zero] at hd
  subst p
  constructor
  · rfl
  · exact Nat.add_left_cancel he

theorem option_mapM_of_map {α β : Type} (xs : List α) (fn : α → Option β)
    (ys : List β) (he : xs.map fn = ys.map some) : xs.mapM fn = some ys := by
  induction xs generalizing ys with
  | nil =>
    have hy : ys = [] := List.map_eq_nil_iff.mp he.symm
    subst ys
    rfl
  | cons x xs ih =>
    cases ys with
    | nil => simp at he
    | cons y ys =>
      have h := List.cons.inj he
      simp only [List.mapM_cons, h.1, ih ys h.2]
      rfl

theorem option_mapM_congr {α β : Type} (xs : List α) (fn gn : α → Option β)
    (he : ∀ x ∈ xs, fn x = gn x) : xs.mapM fn = xs.mapM gn := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.mapM_cons, List.mapM_cons, he x (by simp),
      ih (fun y hy => he y (List.mem_cons_of_mem _ hy))]


end Bracketing
