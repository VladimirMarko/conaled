import Applications.Sequences.RandomAccess.Access

set_option autoImplicit false
set_option warningAsError true

namespace RandomAccess
universe u
variable {α : Type u}

/-- Binary borrowing; malformed or empty inputs report failure explicitly. -/
def unconsT : RAList α → Option (Tree α × RAList α)
  | [] => none
  | .one t :: ds => some (t, if ds.isEmpty then [] else .zero :: ds)
  | .zero :: ds =>
    match unconsT ds with
    | some (.node _ l r, ys) => some (l, .one r :: ys)
    | _ => none

def unconsRA (ds : RAList α) : Option (α × RAList α) :=
  match unconsT ds with
  | some (.leaf x, ys) => some (x, ys)
  | _ => none

theorem unconsT_consT {rank : Nat} {ds : RAList α} (h : Valid rank ds) (t : Tree α) :
    unconsT (consT t ds) = some (t, ds) := by
  induction h generalizing t with
  | nil rank => rfl
  | zero hne h ih => simp [consT, unconsT, List.isEmpty_eq_false_iff.mpr hne]
  | one ht h ih => simp only [consT, unconsT, ih, node]

theorem unconsRA_consRA (x : α) {ds : RAList α} (h : Inv ds) :
    unconsRA (consRA x ds) = some (x, ds) := by
  simp only [unconsRA, consRA, unconsT_consT h]

/-- Borrowing removes a tree of exactly the current rank and preserves validity. -/
theorem unconsT_spec {rank : Nat} {ds : RAList α} (h : Valid rank ds) (hne : ds ≠ []) :
    ∃ t ys, unconsT ds = some (t, ys) ∧ Perfect rank t ∧ Valid rank ys ∧
      fromRA ds = fromT t ++ fromRA ys ∧ consT t ys = ds := by
  induction h with
  | nil rank => exact False.elim (hne rfl)
  | @one rank t ds ht h ih =>
    cases ds with
    | nil => exact ⟨t, [], rfl, ht, Valid.nil _, rfl, rfl⟩
    | cons d ds =>
      exact ⟨t, .zero :: d :: ds, rfl, ht, Valid.zero (by simp) h, rfl, rfl⟩
  | @zero rank ds htail h ih =>
    obtain ⟨t, ys, he, ht, hy, habs, hbuild⟩ := ih htail
    cases ht with
    | node rank l r hl hr =>
      refine ⟨l, .one r :: ys, ?_, hl, Valid.one hr hy, ?_, ?_⟩
      · simp only [unconsT, he]
      · simpa only [fromRA, fromT, List.append_assoc] using habs
      · have hsize : size l + size r = 2 ^ (rank + 1) := by
          rw [size_eq_pow hl, size_eq_pow hr, Nat.pow_succ]
          omega
        simp only [consT, node, hsize, hbuild]

theorem unconsRA_spec {ds : RAList α} (h : Inv ds) (hne : ds ≠ []) :
    ∃ x ys, unconsRA ds = some (x, ys) ∧ Inv ys ∧
      fromRA ds = x :: fromRA ys ∧ consRA x ys = ds := by
  obtain ⟨t, ys, he, ht, hy, habs, hbuild⟩ := unconsT_spec h hne
  cases ht with
  | leaf x =>
    refine ⟨x, ys, ?_, hy, ?_, hbuild⟩
    · simp only [unconsRA, he]
    · simpa only [fromT, List.singleton_append] using habs

def unconsList : List α → Option (α × List α)
  | [] => none
  | x :: xs => some (x, xs)

theorem unconsRA_refinement {ds : RAList α} (h : Inv ds) :
    (unconsRA ds).map (fun p => (p.1, fromRA p.2)) = unconsList (fromRA ds) := by
  by_cases hne : ds = []
  · subst ds; rfl
  · obtain ⟨x, ys, he, hy, habs, hbuild⟩ := unconsRA_spec h hne
    simp only [he, Option.map_some, habs, unconsList]

theorem unconsRA_valid {ds : RAList α} (h : Inv ds) {x : α} {ys : RAList α}
    (he : unconsRA ds = some (x, ys)) : Inv ys := by
  have hne : ds ≠ [] := by
    intro hn
    subst ds
    simp [unconsRA, unconsT] at he
  obtain ⟨z, zs, hz, hvalid, habs, hbuild⟩ := unconsRA_spec h hne
  rw [he] at hz
  have hp := Option.some.inj hz
  cases hp
  exact hvalid

theorem consRA_unconsRA {ds : RAList α} (h : Inv ds) {x : α} {ys : RAList α}
    (he : unconsRA ds = some (x, ys)) : consRA x ys = ds := by
  have hne : ds ≠ [] := by
    intro hn
    subst ds
    simp [unconsRA, unconsT] at he
  obtain ⟨z, zs, hz, hvalid, habs, hbuild⟩ := unconsRA_spec h hne
  rw [he] at hz
  have hp := Option.some.inj hz
  cases hp
  exact hbuild

def headRA (ds : RAList α) : Option α := (unconsRA ds).map Prod.fst

def tailRA (ds : RAList α) : Option (RAList α) := (unconsRA ds).map Prod.snd

theorem headRA_refinement {ds : RAList α} (h : Inv ds) :
    headRA ds = (fromRA ds).head? := by
  by_cases hne : ds = []
  · subst ds; rfl
  · obtain ⟨x, ys, he, hy, habs, hbuild⟩ := unconsRA_spec h hne
    simp only [headRA, he, Option.map_some, habs, List.head?_cons]

theorem tailRA_refinement {ds : RAList α} (h : Inv ds) :
    (tailRA ds).map fromRA = if (fromRA ds).isEmpty then none else some (fromRA ds).tail := by
  by_cases hne : ds = []
  · subst ds; rfl
  · obtain ⟨x, ys, he, hy, habs, hbuild⟩ := unconsRA_spec h hne
    simp only [tailRA, he, Option.map_some, habs, List.isEmpty_cons, Bool.false_eq_true,
      ↓reduceIte, List.tail_cons]

/-- Correct sizes, perfect subtrees, and no trailing zeros give canonical representation. -/
theorem toRA_fromRA {ds : RAList α} (h : Inv ds) : toRA (fromRA ds) = ds := by
  induction ds using (measure (fun xs : RAList α => (fromRA xs).length)).wf.induction with
  | h ds ih =>
    by_cases hne : ds = []
    · subst ds; rfl
    · obtain ⟨x, ys, he, hy, habs, hbuild⟩ := unconsRA_spec h hne
      have hlt : (fromRA ys).length < (fromRA ds).length := by rw [habs]; simp
      rw [habs]
      change consRA x (toRA (fromRA ys)) = ds
      rw [ih ys hlt hy, hbuild]

theorem valid_abstraction_injective {xs ys : RAList α} (hx : Inv xs) (hy : Inv ys)
    (he : fromRA xs = fromRA ys) : xs = ys :=
  (toRA_fromRA hx).symm.trans ((congrArg toRA he).trans (toRA_fromRA hy))

theorem updateRA_out_of_range {ds : RAList α} (h : Inv ds) (k : Nat) (x : α)
    (hk : (fromRA ds).length ≤ k) : updateRA k x ds = ds := by
  apply valid_abstraction_injective (valid_updateRA h k x) h
  rw [updateRA_refinement h]
  exact List.set_eq_of_length_le hk


end RandomAccess
