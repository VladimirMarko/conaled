import Applications.Sequences.Occurrences
import Mathlib.Data.List.Permutation

/-!
# Ordered permutation generation

Mathlib's `List.permutations'` is the insertion recursion. `bySelection`
instead chooses each input position in order, without requiring element
equality. `byErasure` chooses each occurrence but removes the first equal
element, so it requires executable equality. The independent value relation
is `List.Perm`; outer-list permutation additionally preserves occurrences.

The source correspondence and the distinction between enumeration order,
membership, multiplicity and work are recorded in
`docs/research/adwh-permutations.md`.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Sequences.Permutations

universe u v
variable {α : Type u} {β : Type v}

/-- Compatibility name for the shared ordered positional choices. -/
def picks : List α → List (α × List α) := Sequences.Occurrences.picks

theorem mem_picks_iff (xs : List α) (x : α) (ys : List α) :
    (x, ys) ∈ picks xs ↔ ∃ front back, xs = front ++ x :: back ∧ ys = front ++ back :=
  Sequences.Occurrences.mem_picks_iff xs x ys

theorem picks_perm (xs : List α) (p : α × List α) (h : p ∈ picks xs) :
    (p.1 :: p.2).Perm xs := by
  rcases p with ⟨x, ys⟩
  rcases (mem_picks_iff xs x ys).mp h with ⟨front, back, rfl, rfl⟩
  exact List.perm_middle.symm

theorem picks_remainder_length (xs : List α) (p : α × List α) (h : p ∈ picks xs) :
    p.2.length + 1 = xs.length := (picks_perm xs p h).length_eq

theorem picks_length (xs : List α) : (picks xs).length = xs.length := by
  induction xs <;> simp_all [picks, Sequences.Occurrences.picks]

theorem picks_fst (xs : List α) : (picks xs).map Prod.fst = xs :=
  Sequences.Occurrences.picks_fst xs

theorem picks_complete (xs : List α) (x : α) (h : x ∈ xs) :
    ∃ ys, (x, ys) ∈ picks xs := by
  rw [← picks_fst xs] at h
  rcases List.mem_map.mp h with ⟨⟨y, ys⟩, hp, heq⟩
  cases heq
  exact ⟨ys, hp⟩

theorem picks_map (f : α → β) (xs : List α) :
    picks (xs.map f) = (picks xs).map (fun p => (f p.1, p.2.map f)) := by
  induction xs <;> simp_all [picks, Sequences.Occurrences.picks, List.map_map,
    Function.comp_def]

/-- Actual positional-selection recursion; the attached proofs only justify decrease. -/
def bySelection (xs : List α) : List (List α) :=
  if xs = [] then [[]] else
    (picks xs).attach.flatMap (fun p => (bySelection p.val.2).map (p.val.1 :: ·))
termination_by xs.length
decreasing_by
  have h := picks_remainder_length xs p.val p.property
  omega

theorem bySelection_eqn (xs : List α) :
    bySelection xs = if xs = [] then [[]] else
      (picks xs).flatMap (fun p => (bySelection p.2).map (p.1 :: ·)) := by
  rw [bySelection]
  split
  · rfl
  · exact congrArg List.flatten (List.attach_map_val
      (f := fun p : α × List α => (bySelection p.2).map (p.1 :: ·)))

theorem bySelection_mem_iff (xs ys : List α) : ys ∈ bySelection xs ↔ ys.Perm xs := by
  rw [bySelection_eqn]
  by_cases hx : xs = []
  · subst xs; simp
  · simp only [hx, ↓reduceIte, List.mem_flatMap, List.mem_map]
    constructor
    · rintro ⟨p, hp, zs, hz, rfl⟩
      exact (((bySelection_mem_iff p.2 zs).mp hz).cons p.1).trans (picks_perm xs p hp)
    · intro h
      cases ys with
      | nil => exact False.elim (hx (List.perm_nil.mp h.symm))
      | cons y ys =>
          have hy : y ∈ xs := h.mem_iff.mp List.mem_cons_self
          rcases picks_complete xs y hy with ⟨zs, hp⟩
          have hrest : ys.Perm zs := (h.trans (picks_perm xs (y, zs) hp).symm).cons_inv
          exact ⟨(y, zs), hp, ys, (bySelection_mem_iff zs ys).mpr hrest, rfl⟩
termination_by xs.length
decreasing_by
  all_goals
    exact Nat.lt_of_lt_of_eq (Nat.lt_succ_self _) (picks_remainder_length xs _ hp)

theorem bySelection_map (f : α → β) (xs : List α) :
    bySelection (xs.map f) = (bySelection xs).map (List.map f) := by
  rw [bySelection_eqn (xs.map f), bySelection_eqn xs]
  by_cases hx : xs = []
  · subst xs; simp
  · simp only [List.map_eq_nil_iff, hx, ↓reduceIte]
    rw [picks_map, List.flatMap_map, List.map_flatMap]
    apply congrArg List.flatten
    apply List.map_congr_left
    intro p hp
    rw [bySelection_map f p.2]
    simp only [List.map_map, List.map_cons, Function.comp_def]
termination_by xs.length
decreasing_by exact Nat.lt_of_lt_of_eq (Nat.lt_succ_self _) (picks_remainder_length xs p hp)

theorem bySelection_nodup (xs : List α) (h : xs.Nodup) : (bySelection xs).Nodup := by
  rw [bySelection_eqn]
  split
  · simp
  · apply List.pairwise_flatMap.mpr
    constructor
    · intro p hp
      have hn : (p.1 :: p.2).Nodup := (picks_perm xs p hp).nodup_iff.mpr h
      apply List.pairwise_map.mpr
      exact (bySelection_nodup p.2 (List.nodup_cons.mp hn).2).imp
        (fun {a b} hab heq => hab (List.cons.inj heq).2)
    · have hheads : (picks xs).Pairwise (fun p q => p.1 ≠ q.1) := by
        apply List.pairwise_map.mp
        change ((picks xs).map Prod.fst).Nodup
        rw [picks_fst]
        exact h
      apply hheads.imp
      intro p q hne as has bs hbs heq
      rcases List.mem_map.mp has with ⟨us, _, rfl⟩
      rcases List.mem_map.mp hbs with ⟨vs, _, rfl⟩
      exact hne (List.cons.inj heq).1
termination_by xs.length
decreasing_by exact Nat.lt_of_lt_of_eq (Nat.lt_succ_self _) (picks_remainder_length xs p hp)

private theorem tagged_nodup (xs : List α) : xs.zipIdx.Nodup := by
  have h : ((xs.zipIdx).map Prod.snd).Nodup := by
    rw [List.zipIdx_map_snd]
    exact List.nodup_range'
  exact List.Pairwise.of_map Prod.snd
    (fun a b hne heq => hne (congrArg Prod.snd heq)) h

/-- Positional tagging preserves the multiplicities of repeated values. -/
theorem insertion_perm_selection (xs : List α) : xs.permutations'.Perm (bySelection xs) := by
  have hinsert : xs.zipIdx.permutations'.Nodup :=
    (List.permutations_perm_permutations' _).nodup_iff.mp
      (List.nodup_permutations _ (tagged_nodup xs))
  have hp : xs.zipIdx.permutations'.Perm (bySelection xs.zipIdx) :=
    (List.perm_ext_iff_of_nodup hinsert
      (bySelection_nodup _ (tagged_nodup xs))).mpr (fun ys => by
        rw [List.mem_permutations', bySelection_mem_iff])
  have mapped := hp.map (List.map Prod.fst)
  simpa only [List.map_permutations', ← bySelection_map, List.zipIdx_map_fst] using mapped

theorem insertion_length (xs : List α) : xs.permutations'.length = Nat.factorial xs.length :=
  (List.permutations_perm_permutations' xs).length_eq.symm.trans
    (List.length_permutations xs)

theorem bySelection_length (xs : List α) : (bySelection xs).length = Nat.factorial xs.length :=
  (insertion_perm_selection xs).length_eq.symm.trans (insertion_length xs)

theorem insertion_head (xs : List α) : xs.permutations'.head? = some xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      rcases List.head?_eq_some_iff.mp ih with ⟨xss, h⟩
      rw [List.permutations', h, List.flatMap_cons, List.head?_append]
      cases xs <;> rfl

theorem bySelection_head (xs : List α) : (bySelection xs).head? = some xs := by
  induction xs with
  | nil => rw [bySelection_eqn]; rfl
  | cons x xs ih =>
      rw [bySelection_eqn]
      simp [picks, Sequences.Occurrences.picks, ih]

/-- The standard insertion generator is also the right-fold presentation. -/
theorem insertion_fold (xs : List α) :
    xs.foldr (fun x xss => xss.flatMap (List.permutations'Aux x)) [[]] =
      xs.permutations' := by
  induction xs <;> simp_all

theorem mem_inserts_iff (x : α) (xs zs : List α) :
    zs ∈ List.permutations'Aux x xs ↔
      ∃ front back, xs = front ++ back ∧ zs = front ++ x :: back := by
  induction xs generalizing zs with
  | nil =>
      constructor
      · intro h
        exact ⟨[], [], rfl, by simpa using h⟩
      · rintro ⟨front, back, h, hzs⟩
        rcases List.append_eq_nil_iff.mp h.symm with ⟨rfl, rfl⟩
        simp [hzs]
  | cons y ys ih =>
      constructor
      · intro h
        rcases List.mem_cons.mp h with h | h
        · exact ⟨[], y :: ys, rfl, h⟩
        · rcases List.mem_map.mp h with ⟨ws, hw, rfl⟩
          rcases (ih ws).mp hw with ⟨front, back, hys, hws⟩
          exact ⟨y :: front, back, by simp [hys], by simp [hws]⟩
      · rintro ⟨front, back, hxs, hzs⟩
        cases front with
        | nil =>
            simp only [List.nil_append] at hxs hzs
            subst back
            subst zs
            exact List.mem_cons_self
        | cons z front =>
            simp only [List.cons_append, List.cons.injEq] at hxs
            rcases hxs with ⟨rfl, hys⟩
            rw [hzs]
            exact List.mem_cons_of_mem _ (List.mem_map.mpr
              ⟨front ++ x :: back, (ih _).mpr ⟨front, back, hys, rfl⟩, rfl⟩)

theorem inserts_perm (x : α) (xs zs : List α) (h : zs ∈ List.permutations'Aux x xs) :
    zs.Perm (x :: xs) := by
  rcases (mem_inserts_iff x xs zs).mp h with ⟨front, back, rfl, rfl⟩
  exact List.perm_middle

theorem inserts_head (x : α) (xs : List α) :
    (List.permutations'Aux x xs).head? = some (x :: xs) := by
  cases xs <;> rfl

theorem inserts_erase [DecidableEq α] (x : α) (xs zs : List α)
    (fresh : x ∉ xs) (h : zs ∈ List.permutations'Aux x xs) : zs.erase x = xs := by
  rcases (mem_inserts_iff x xs zs).mp h with ⟨front, back, rfl, rfl⟩
  have hfront : x ∉ front := fun hx => fresh (List.mem_append_left back hx)
  rw [List.erase_append_right (x :: back) hfront, List.erase_cons_head]

/-- Apply an arbitrary result function while constructing each insertion. -/
def insertsWith (f : List α → β) (x : α) : List α → List β
  | [] => [f [x]]
  | y :: ys => f (x :: y :: ys) :: insertsWith (fun zs => f (y :: zs)) x ys

theorem insertsWith_eq_map (f : List α → β) (x : α) (xs : List α) :
    insertsWith f x xs = (List.permutations'Aux x xs).map f := by
  induction xs generalizing f <;> simp_all [insertsWith, List.map_map]

/-- Literal head/tail fold step, with an explicit empty fallback off its reached states. -/
def insertStep (x y : α) (yss : List (List α)) : List (List α) :=
  match yss.head? with
  | none => []
  | some zs =>
      match zs.tail? with
      | none => []
      | some ys => (x :: y :: ys) :: yss.map (y :: ·)

theorem insertStep_correct (x y : α) (xs : List α) :
    insertStep x y (List.permutations'Aux x xs) = List.permutations'Aux x (y :: xs) := by
  simp [insertStep, inserts_head]

theorem insertion_step_fold (x : α) (xs : List α) :
    xs.foldr (insertStep x) [[x]] = List.permutations'Aux x xs := by
  induction xs <;> simp_all [insertStep_correct]

section Erasure

variable [DecidableEq α]

/-- Every input occurrence is chosen; equal choices erase the same first occurrence. -/
def byErasure (xs : List α) : List (List α) :=
  if xs = [] then [[]] else
    xs.attach.flatMap (fun x => (byErasure (xs.erase x.val)).map (x.val :: ·))
termination_by xs.length
decreasing_by
  have h := List.length_erase_add_one x.property
  omega

theorem byErasure_eqn (xs : List α) :
    byErasure xs = if xs = [] then [[]] else
      xs.flatMap (fun x => (byErasure (xs.erase x)).map (x :: ·)) := by
  rw [byErasure]
  split
  · rfl
  · exact congrArg List.flatten (List.attach_map_val
      (f := fun x : α => (byErasure (xs.erase x)).map (x :: ·)))

theorem byErasure_mem_iff (xs ys : List α) : ys ∈ byErasure xs ↔ ys.Perm xs := by
  rw [byErasure_eqn]
  by_cases hx : xs = []
  · subst xs; simp
  · simp only [hx, ↓reduceIte, List.mem_flatMap, List.mem_map]
    constructor
    · rintro ⟨x, hmem, zs, hz, rfl⟩
      exact (((byErasure_mem_iff (xs.erase x) zs).mp hz).cons x).trans
        (List.perm_cons_erase hmem).symm
    · intro h
      cases ys with
      | nil => exact False.elim (hx (List.perm_nil.mp h.symm))
      | cons y ys =>
          have hmem : y ∈ xs := h.mem_iff.mp List.mem_cons_self
          have hrest : ys.Perm (xs.erase y) :=
            (h.trans (List.perm_cons_erase hmem)).cons_inv
          exact ⟨y, hmem, ys, (byErasure_mem_iff (xs.erase y) ys).mpr hrest, rfl⟩
termination_by xs.length
decreasing_by
  all_goals
    have h := List.length_erase_add_one hmem
    omega

theorem byErasure_head (xs : List α) : (byErasure xs).head? = some xs := by
  induction xs with
  | nil => rw [byErasure_eqn]; rfl
  | cons x xs ih =>
      rw [byErasure_eqn]
      simp [ih]

/-- The source exercise's missing-base variant is total but enumerates nothing. -/
def byErasureWithoutBase (xs : List α) : List (List α) :=
  xs.attach.flatMap (fun x => (byErasureWithoutBase (xs.erase x.val)).map (x.val :: ·))
termination_by xs.length
decreasing_by
  have h := List.length_erase_add_one x.property
  omega

theorem byErasureWithoutBase_eq_nil (xs : List α) : byErasureWithoutBase xs = [] := by
  rw [byErasureWithoutBase]
  apply List.flatMap_eq_nil_iff.mpr
  intro x _
  rw [byErasureWithoutBase_eq_nil (xs.erase x.val)]
  rfl
termination_by xs.length
decreasing_by
  have h := List.length_erase_add_one x.property
  omega

end Erasure

end Sequences.Permutations
