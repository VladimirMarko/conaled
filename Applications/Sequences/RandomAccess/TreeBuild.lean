import Applications.Sequences.RandomAccess.Borrow

set_option autoImplicit false
set_option warningAsError true

namespace RandomAccess
universe u
variable {α : Type u}

/-- Correct cached sizes without a balance requirement. -/
def Cached : Tree α → Prop
  | .leaf _ => True
  | .node n l r => n = size l + size r ∧ Cached l ∧ Cached r

theorem cached_size_refinement (t : Tree α) (h : Cached t) : size t = (fromT t).length := by
  induction t with
  | leaf x => rfl
  | node n l r ihl ihr =>
    simp only [size, fromT, List.length_append]
    rw [h.1, ihl h.2.1, ihr h.2.2]

/-- Correct cached counts agree with the existing uncached tree size observation. -/
theorem cached_size_erasure (t : Tree α) (h : Cached t) :
    size t = Bracketing.size (erase t) :=
  (cached_size_refinement t h).trans
    ((congrArg List.length (fromT_eq_fringe t)).trans (Bracketing.fringeSpec_length _))

theorem Perfect.cached {rank : Nat} {t : Tree α} (h : Perfect rank t) : Cached t := by
  induction h with
  | leaf x => trivial
  | node rank l r hl hr ihl ihr =>
    refine ⟨?_, ihl, ihr⟩
    rw [size_eq_pow hl, size_eq_pow hr, Nat.pow_succ]
    omega

theorem tree_split_bounds (xs : List α) (h : 2 ≤ xs.length) :
    (0 < (xs.take (xs.length / 2)).length ∧ (xs.take (xs.length / 2)).length < xs.length) ∧
    (0 < (xs.drop (xs.length / 2)).length ∧ (xs.drop (xs.length / 2)).length < xs.length) := by
  have hd := Nat.div_le_self xs.length 2
  simp only [List.length_take, List.length_drop]
  omega

/-- Source `tree`, returning `none` on its previously undefined empty input. -/
def tree : List α → Option (Tree α)
  | [] => none
  | [x] => some (.leaf x)
  | x :: y :: xs =>
    let zs := x :: y :: xs
    match tree (zs.take (zs.length / 2)), tree (zs.drop (zs.length / 2)) with
    | some l, some r => some (node l r)
    | _, _ => none
termination_by xs => xs.length
decreasing_by
  · exact (tree_split_bounds _ (by simp)).1.2
  · exact (tree_split_bounds _ (by simp)).2.2

theorem tree_spec (xs : List α) (hne : xs ≠ []) :
    ∃ t, tree xs = some t ∧ fromT t = xs ∧ Cached t := by
  induction xs using (measure (fun ys : List α => ys.length)).wf.induction with
  | h xs ih =>
    cases xs with
    | nil => exact False.elim (hne rfl)
    | cons x xs =>
      cases xs with
      | nil => exact ⟨.leaf x, by rw [tree], rfl, True.intro⟩
      | cons y xs =>
        let zs := x :: y :: xs
        let as := zs.take (zs.length / 2)
        let bs := zs.drop (zs.length / 2)
        have hb := tree_split_bounds zs (by simp [zs])
        have hane : as ≠ [] := by intro he; have := hb.1.1; change 0 < as.length at this; simp [he] at this
        have hbne : bs ≠ [] := by intro he; have := hb.2.1; change 0 < bs.length at this; simp [he] at this
        obtain ⟨l, hl, hla, hlc⟩ := ih as hb.1.2 hane
        obtain ⟨r, hr, hrb, hrc⟩ := ih bs hb.2.2 hbne
        refine ⟨node l r, ?_, ?_, ⟨rfl, hlc, hrc⟩⟩
        · rw [tree]
          change (match tree as, tree bs with
            | some l, some r => some (node l r)
            | _, _ => none) = some (node l r)
          rw [hl, hr]
        · change fromT l ++ fromT r = zs
          rw [hla, hrb]
          exact List.take_append_drop _ zs

theorem tree_abstraction (xs : List α) :
    (tree xs).map fromT = if xs.isEmpty then none else some xs := by
  by_cases hne : xs = []
  · subst xs; simp [tree]
  · obtain ⟨t, ht, habs, hc⟩ := tree_spec xs hne
    simp only [ht, Option.map_some, habs, List.isEmpty_eq_false_iff.mpr hne,
      Bool.false_eq_true, ↓reduceIte]

/-- A power-of-two input length produces exactly a perfect tree of that rank. -/
theorem tree_perfect (rank : Nat) (xs : List α) (hlen : xs.length = 2 ^ rank) :
    ∃ t, tree xs = some t ∧ Perfect rank t := by
  induction rank generalizing xs with
  | zero =>
    cases xs with
    | nil => simp at hlen
    | cons x xs =>
      have hx : xs = [] := by
        apply List.length_eq_zero_iff.mp
        simp only [List.length_cons, Nat.pow_zero] at hlen
        omega
      subst xs
      exact ⟨.leaf x, by rw [tree], Perfect.leaf x⟩
  | succ rank ih =>
    have hp : 0 < 2 ^ rank := Nat.pow_pos (by decide)
    have hpow : 2 ^ (rank + 1) = 2 ^ rank + 2 ^ rank := by rw [Nat.pow_succ]; omega
    cases xs with
    | nil => simp only [List.length_nil] at hlen; omega
    | cons x xs =>
      cases xs with
      | nil => simp only [List.length_cons, List.length_nil] at hlen; omega
      | cons y xs =>
        let zs := x :: y :: xs
        let as := zs.take (zs.length / 2)
        let bs := zs.drop (zs.length / 2)
        have haz : as.length = 2 ^ rank := by
          simp only [as, List.length_take]
          change min ((x :: y :: xs).length / 2) (x :: y :: xs).length = _
          rw [hlen, half_pow_succ, hpow]
          omega
        have hbz : bs.length = 2 ^ rank := by
          simp only [bs, List.length_drop]
          change (x :: y :: xs).length - (x :: y :: xs).length / 2 = _
          rw [hlen, half_pow_succ, hpow]
          omega
        obtain ⟨l, hl, hlp⟩ := ih as haz
        obtain ⟨r, hr, hrp⟩ := ih bs hbz
        refine ⟨node l r, ?_, perfect_node hlp hrp⟩
        rw [tree]
        change (match tree as, tree bs with
          | some l, some r => some (node l r)
          | _, _ => none) = some (node l r)
        rw [hl, hr]


end RandomAccess
