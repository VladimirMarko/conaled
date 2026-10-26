import Applications.Sequences.RandomAccess.Basic

set_option autoImplicit false
set_option warningAsError true

namespace RandomAccess
universe u
variable {α : Type u}

/-- Compatibility name for standard optional List indexing. -/
abbrev fetch (k : Nat) (xs : List α) : Option α := xs[k]?

theorem fetch_eq_getElem (k : Nat) (xs : List α) : fetch k xs = xs[k]? := rfl

def fetchT (k : Nat) : Tree α → Option α
  | .leaf x => if k = 0 then some x else none
  | .node n l r => if k < n / 2 then fetchT k l else fetchT (k - n / 2) r

def fetchRA (k : Nat) : RAList α → Option α
  | [] => none
  | .zero :: ds => fetchRA k ds
  | .one t :: ds => if k < size t then fetchT k t else fetchRA (k - size t) ds

theorem half_pow_succ (rank : Nat) : 2 ^ (rank + 1) / 2 = 2 ^ rank := by
  rw [Nat.pow_succ]
  omega

theorem fetchT_refinement {rank : Nat} {t : Tree α} (h : Perfect rank t) (k : Nat) :
    fetchT k t = (fromT t)[k]? := by
  induction h generalizing k with
  | leaf x => cases k <;> simp [fetchT, fromT]
  | node rank l r hl hr ihl ihr =>
    rw [fetchT, half_pow_succ]
    by_cases hk : k < 2 ^ rank
    · rw [ite_eq_left hk, ihl, fromT, List.getElem?_append_left]
      simpa only [fromT_length hl] using hk
    · rw [ite_eq_right hk, ihr, fromT, List.getElem?_append_right]
      · rw [fromT_length hl]
      · rw [fromT_length hl]
        omega

theorem fetchRA_refinement {rank : Nat} {ds : RAList α} (h : Valid rank ds) (k : Nat) :
    fetchRA k ds = (fromRA ds)[k]? := by
  induction h generalizing k with
  | nil rank => rfl
  | zero hne h ih => exact ih k
  | @one rank t ds ht h ih =>
    rw [fetchRA]
    by_cases hk : k < size t
    · rw [ite_eq_left hk, fetchT_refinement ht, fromRA, List.getElem?_append_left]
      simpa only [fromT_length_eq_size ht] using hk
    · rw [ite_eq_right hk, ih, fromRA, List.getElem?_append_right]
      · rw [fromT_length_eq_size ht]
      · rw [fromT_length_eq_size ht]
        omega

theorem fetchRA_toRA (k : Nat) (xs : List α) : fetchRA k (toRA xs) = fetch k xs := by
  rw [fetchRA_refinement (inv_toRA xs), fromRA_toRA, fetch_eq_getElem]

def updateT (k : Nat) (x : α) : Tree α → Tree α
  | .leaf y => if k = 0 then .leaf x else .leaf y
  | .node n l r =>
    if k < n / 2 then .node n (updateT k x l) r else .node n l (updateT (k - n / 2) x r)

def updateRA (k : Nat) (x : α) : RAList α → RAList α
  | [] => []
  | .zero :: ds => .zero :: updateRA k x ds
  | .one t :: ds =>
    if k < size t then .one (updateT k x t) :: ds else .one t :: updateRA (k - size t) x ds

theorem perfect_updateT {rank : Nat} {t : Tree α} (h : Perfect rank t) (k : Nat) (x : α) :
    Perfect rank (updateT k x t) := by
  induction h generalizing k with
  | leaf y =>
    rw [updateT]
    split <;> apply Perfect.leaf
  | node rank l r hl hr ihl ihr =>
    rw [updateT]
    split
    · exact Perfect.node rank _ _ (ihl k) hr
    · exact Perfect.node rank _ _ hl (ihr _)

theorem updateT_refinement {rank : Nat} {t : Tree α} (h : Perfect rank t) (k : Nat) (x : α) :
    fromT (updateT k x t) = (fromT t).set k x := by
  induction h generalizing k with
  | leaf y => cases k <;> simp [updateT, fromT]
  | node rank l r hl hr ihl ihr =>
    rw [updateT, half_pow_succ]
    by_cases hk : k < 2 ^ rank
    · rw [ite_eq_left hk, fromT, fromT, ihl, List.set_append_left]
      simpa only [fromT_length hl] using hk
    · rw [ite_eq_right hk, fromT, fromT, ihr, List.set_append_right]
      · rw [fromT_length hl]
      · rw [fromT_length hl]
        omega

theorem updateRA_ne_nil (k : Nat) (x : α) {ds : RAList α} (h : ds ≠ []) :
    updateRA k x ds ≠ [] := by
  cases ds with
  | nil => exact False.elim (h rfl)
  | cons d ds =>
    cases d with
    | zero => simp [updateRA]
    | one t => simp only [updateRA]; split <;> simp

theorem valid_updateRA {rank : Nat} {ds : RAList α} (h : Valid rank ds) (k : Nat) (x : α) :
    Valid rank (updateRA k x ds) := by
  induction h generalizing k with
  | nil rank => exact Valid.nil _
  | zero hne h ih => exact Valid.zero (updateRA_ne_nil k x hne) (ih k)
  | one ht h ih =>
    rw [updateRA]
    split
    · exact Valid.one (perfect_updateT ht k x) h
    · exact Valid.one ht (ih _)

theorem updateRA_refinement {rank : Nat} {ds : RAList α} (h : Valid rank ds) (k : Nat) (x : α) :
    fromRA (updateRA k x ds) = (fromRA ds).set k x := by
  induction h generalizing k with
  | nil rank => rfl
  | zero hne h ih => exact ih k
  | @one rank t ds ht h ih =>
    rw [updateRA]
    by_cases hk : k < size t
    · rw [ite_eq_left hk, fromRA, updateT_refinement ht, fromRA, List.set_append_left]
      simpa only [fromT_length_eq_size ht] using hk
    · rw [ite_eq_right hk, fromRA, ih, fromRA, List.set_append_right]
      · rw [fromT_length_eq_size ht]
      · rw [fromT_length_eq_size ht]
        omega

theorem updateRA_toRA (k : Nat) (x : α) (xs : List α) :
    fromRA (updateRA k x (toRA xs)) = xs.set k x := by
  rw [updateRA_refinement (inv_toRA xs), fromRA_toRA]


theorem fetchRA_none_iff {rank : Nat} {ds : RAList α} (h : Valid rank ds) (k : Nat) :
    fetchRA k ds = none ↔ (fromRA ds).length ≤ k := by
  rw [fetchRA_refinement h, List.getElem?_eq_none_iff]

end RandomAccess
