import Applications.Sorting.Sort

/-! Occurrence ranks, independent of pivot policies or sorting implementations. -/
set_option autoImplicit false
set_option warningAsError true

namespace Applications.Selection
universe u v
variable {α : Type u} {β : Type v}

/-- A zero-based position among input occurrences, including repeated values. -/
def RankedAt [LE α] (xs : List α) (k : Nat) (a : α) : Prop :=
  ∃ pre post, (pre ++ a :: post).Perm xs ∧ pre.length = k ∧
    (∀ y ∈ pre, y ≤ a) ∧ (∀ y ∈ post, a ≤ y)

theorem pairwise_ranked [LE α] {ys xs : List α} {k : Nat} {a : α}
    (hs : ys.Pairwise (· ≤ ·)) (hp : ys.Perm xs) (ha : ys[k]? = some a) :
    RankedAt xs k a := by
  induction ys generalizing xs k with
  | nil => simp at ha
  | cons x ys ih =>
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at ha
      subst a
      exact ⟨[], ys, hp, rfl, by simp, (List.pairwise_cons.mp hs).1⟩
    | succ k =>
      have ht : ys[k]? = some a := ha
      obtain ⟨pre, post, he, hl, lo, hi⟩ :=
        ih (List.pairwise_cons.mp hs).2 (List.Perm.refl ys) ht
      refine ⟨x :: pre, post, (he.cons x).trans hp, by simp [hl], ?_, hi⟩
      intro y hy
      rcases List.mem_cons.mp hy with heq | hy
      · subst y
        exact (List.pairwise_cons.mp hs).1 a (List.mem_of_getElem? ht)
      · exact lo y hy

/-- Relabeling may identify values: order preservation alone transports ranks. -/
theorem RankedAt.map [Preorder α] [Preorder β] {xs : List α} {k : Nat} {a : α}
    (h : RankedAt xs k a) (f : α → β) (hf : Monotone f) :
    RankedAt (xs.map f) k (f a) := by
  obtain ⟨pre, post, hp, hk, hlo, hhi⟩ := h
  refine ⟨pre.map f, post.map f, ?_, by simpa using hk, ?_, ?_⟩
  · simpa using hp.map f
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    exact hf (hlo x hx)
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    exact hf (hhi x hx)

section Linear
variable [LinearOrder α]

abbrev ordered (xs : List α) := Applications.Sorting.sortOn id xs

theorem ordered_perm (xs : List α) : (ordered xs).Perm xs :=
  Applications.Sorting.sortBy_perm _ xs

theorem ordered_pairwise (xs : List α) : (ordered xs).Pairwise (· ≤ ·) :=
  (Applications.Sorting.sortOn_correct id xs).1

/-- Sorting is a realization of the independent permutation-and-bounds contract. -/
theorem ranked_iff_index {xs : List α} {k : Nat} {a : α} :
    RankedAt xs k a ↔ (ordered xs)[k]? = some a := by
  constructor
  · rintro ⟨pre, post, hp, hk, hlo, hhi⟩
    have he : ordered xs = ordered pre ++ a :: ordered post := by
      apply List.Perm.eq_of_pairwise (fun _ _ _ _ hab hba => le_antisymm hab hba)
      · exact ordered_pairwise xs
      · rw [List.pairwise_append, List.pairwise_cons]
        refine ⟨ordered_pairwise pre, ⟨?_, ordered_pairwise post⟩, ?_⟩
        · intro b hb
          exact hhi b ((ordered_perm post).mem_iff.mp hb)
        · intro b hb c hc
          have hb' := hlo b ((ordered_perm pre).mem_iff.mp hb)
          rcases List.mem_cons.mp hc with rfl | hc
          · exact hb'
          · exact le_trans hb' (hhi c ((ordered_perm post).mem_iff.mp hc))
      · exact (ordered_perm xs).trans
          (((ordered_perm pre).append ((ordered_perm post).cons a)).trans hp).symm
    rw [he, ← hk, ← (ordered_perm pre).length_eq]
    simp
  · exact pairwise_ranked (ordered_pairwise xs) (ordered_perm xs)

theorem RankedAt.unique {xs : List α} {k : Nat} {a b : α}
    (ha : RankedAt xs k a) (hb : RankedAt xs k b) : a = b :=
  Option.some.inj ((ranked_iff_index.mp ha).symm.trans (ranked_iff_index.mp hb))

end Linear
end Applications.Selection
