import Applications.Sequences.Symmetric.Core

/-! Exact finite prefix enumeration through shared scan fusion and nested symmetric lists.
Source provenance and statement review: `docs/research/adwh-symmetric-lists.md`. -/

namespace Sequences.Symmetric
universe u
variable {α : Type u}

abbrev inits (xs : List α) := xs.inits

private theorem scanl_append (xs acc : List α) :
    xs.scanl (fun ys x => ys ++ [x]) acc = xs.inits.map (acc ++ ·) := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih => simp [List.scanl_cons, ih, List.map_map, List.append_assoc]

theorem scanl_snocSL_refinement (xs : List α) (s : SymList α) (h : Inv s) :
    (xs.scanl (fun q x => snocSL x q) s).map fromSL =
      (inits xs).map (fun ys => fromSL s ++ ys) := by
  rw [SquareKit.ListFusion.scanl_reachable
    (fun q x => snocSL x q) (fun ys x => ys ++ [x]) fromSL Inv s h
    (fun q x _ => inv_snocSL x q) (fun q x hq => fromSL_snocSL x q hq)]
  exact scanl_append xs (fromSL s)

def initsViaSL (xs : List α) : List (List α) :=
  (xs.scanl (fun s x => snocSL x s) nilSL).map fromSL

theorem initsViaSL_eq_inits (xs : List α) : initsViaSL xs = inits xs := by
  simpa [initsViaSL] using scanl_snocSL_refinement xs nilSL inv_nilSL

theorem scanl_reverse_refinement (xs acc : List α) :
    (xs.scanl (fun ys x => x :: ys) acc).map List.reverse =
      (inits xs).map (fun ys => acc.reverse ++ ys) := by
  rw [SquareKit.ListFusion.scanl_reachable
    (fun ys x => x :: ys) (fun ys x => ys ++ [x]) List.reverse (fun _ => True) acc
    trivial (by simp) (by intros; simp)]
  exact scanl_append xs acc.reverse

/-- The source's `inits'`: accumulate reversed prefixes, then reverse each one. -/
def initsReverseScan (xs : List α) : List (List α) :=
  (xs.scanl (fun ys x => x :: ys) []).map List.reverse

theorem initsReverseScan_eq_inits (xs : List α) : initsReverseScan xs = inits xs := by
  simpa [initsReverseScan] using scanl_reverse_refinement xs []

theorem inits_append_singleton (xs : List α) (x : α) :
    inits (xs ++ [x]) = inits xs ++ [xs ++ [x]] := by
  simp [inits]

theorem inits_eq_dropLast_append (xs : List α) (h : xs ≠ []) :
    inits xs = inits xs.dropLast ++ [xs] := by
  have he := List.dropLast_concat_getLast h
  conv => lhs; rw [← he]
  rw [inits_append_singleton, he]

/-- The source exercise builds a symmetric list of all symmetric-list prefixes. -/
def initsSL (s : SymList α) : SymList (SymList α) :=
  if _h : nullSL s then snocSL s nilSL
  else snocSL s (initsSL (initSL s))
termination_by lengthSL s
decreasing_by
  apply initSL_length_lt
  intro he
  exact _h ((nullSL_eq_true_iff_nilSL s).mpr he)

theorem inv_initsSL (s : SymList α) : Inv (initsSL s) := by
  rw [initsSL]
  split <;> apply inv_snocSL

theorem fromSL_initsSL (s : SymList α) (h : Inv s) :
    (fromSL (initsSL s)).map fromSL = inits (fromSL s) := by
  induction s using (measure lengthSL).wf.induction with
  | h s ih =>
    rw [initsSL]
    split
    · rename_i he
      have hs := (nullSL_eq_true_iff_nilSL s).mp he
      subst s
      rfl
    · rename_i hn
      have hne : s ≠ nilSL := fun he => hn ((nullSL_eq_true_iff_nilSL s).mpr he)
      rw [fromSL_snocSL _ _ (inv_initsSL _), List.map_append]
      rw [ih _ (initSL_length_lt s hne) (inv_initSL s h), fromSL_initSL s h]
      have hxs : fromSL s ≠ [] := by
        intro he
        have hlen : lengthSL s = 0 := by rw [← length_fromSL, he]; rfl
        exact hne ((lengthSL_eq_zero_iff s).mp hlen)
      simpa only [List.map_cons, List.map_nil] using (inits_eq_dropLast_append _ hxs).symm

theorem initsSL_members_valid (s : SymList α) (h : Inv s) :
    ∀ t ∈ fromSL (initsSL s), Inv t := by
  induction s using (measure lengthSL).wf.induction with
  | h s ih =>
    rw [initsSL]
    split
    · rename_i he
      have hs := (nullSL_eq_true_iff_nilSL s).mp he
      subst s
      intro t ht
      simp [snocSL, fromSL, nilSL] at ht
      subst t
      exact inv_nilSL
    · rename_i hn
      have hne : s ≠ nilSL := fun he => hn ((nullSL_eq_true_iff_nilSL s).mpr he)
      rw [fromSL_snocSL _ _ (inv_initsSL _)]
      intro t ht
      rcases List.mem_append.mp ht with ht | ht
      · exact ih _ (initSL_length_lt s hne) (inv_initSL s h) t ht
      · have he := List.mem_singleton.mp ht
        subst t
        exact h

end Sequences.Symmetric
