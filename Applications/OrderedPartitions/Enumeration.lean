import Applications.OrderedPartitions.Right
import Mathlib.Data.List.Perm.Basic

/-! Grouped and recursive source generators recover exactly the right-extending enumeration order. -/
set_option autoImplicit false
set_option warningAsError true
namespace OrderedPartitions
universe u
variable {α : Type u}

def groupedStep (x : α) : List (Partition α) → List (Partition α)
  | [[]] => [[[x]]]
  | ps => ps.map (consBlock x) ++ ps.map (glueLeft x)

def partsGrouped (xs : List α) : List (Partition α) := xs.foldr groupedStep [[]]

@[simp] theorem partsGrouped_nil : partsGrouped ([] : List α) = [[]] := rfl

@[simp] theorem partsGrouped_cons (x : α) (xs : List α) :
    partsGrouped (x :: xs) = groupedStep x (partsGrouped xs) := rfl

theorem groupedStep_of_ne_special (x : α) (ps : List (Partition α)) (hp : ps ≠ [[]]) :
    groupedStep x ps = ps.map (consBlock x) ++ ps.map (glueLeft x) := by
  cases ps with
  | nil => rfl
  | cons p ps =>
    cases p with
    | nil => cases ps with
      | nil => exact False.elim (hp rfl)
      | cons => rfl
    | cons => rfl

theorem grouped_map_perm {β : Type u} (f g : α → β) (xs : List α) :
    (xs.map f ++ xs.map g).Perm (xs.flatMap (fun x => [f x, g x])) := by
  simpa [← List.map_eq_flatMap] using
    List.flatMap_append_perm xs (fun x => [f x]) (fun x => [g x])

theorem stepLeft_of_nonempty (x : α) (ps : List (Partition α))
    (hp : ∀ p ∈ ps, p ≠ []) :
    stepLeft x ps = ps.flatMap (fun p => [consBlock x p, glueLeft x p]) := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    have hpn := hp p (by simp)
    have hps : ∀ q ∈ ps, q ≠ [] := fun q hq => hp q (by simp [hq])
    cases p with
    | nil => exact False.elim (hpn rfl)
    | cons block rest =>
      change [consBlock x (block :: rest), glueLeft x (block :: rest)] ++ stepLeft x ps = _
      rw [ih hps]
      rfl

theorem groupedStep_perm_stepLeft (x : α) (ps : List (Partition α))
    (hp : ∀ p ∈ ps, p ≠ []) : (groupedStep x ps).Perm (stepLeft x ps) := by
  have hspecial : ps ≠ [[]] := by
    intro h
    exact hp [] (by simp [h]) rfl
  rw [groupedStep_of_ne_special x ps hspecial, stepLeft_of_nonempty x ps hp]
  exact grouped_map_perm (consBlock x) (glueLeft x) ps

theorem partsGrouped_perm_left (xs : List α) : (partsGrouped xs).Perm (partsLeft xs) := by
  induction xs with
  | nil => exact .rfl
  | cons x xs ih =>
    cases xs with
    | nil => exact .rfl
    | cons y ys =>
      have hp : ∀ p ∈ partsGrouped (y :: ys), p ≠ [] := by
        intro p h
        exact partsLeft_member_ne_nil (y :: ys) (by simp) p (ih.mem_iff.mp h)
      exact (groupedStep_perm_stepLeft x _ hp).trans (ih.flatMap_right (extendLeft x))

theorem mem_partsGrouped (xs : List α) (p : Partition α) :
    p ∈ partsGrouped xs ↔ IsPartition xs p :=
  (partsGrouped_perm_left xs).mem_iff.trans (mem_partsLeft xs p)

theorem partsGrouped_nodup (xs : List α) : (partsGrouped xs).Nodup :=
  (partsGrouped_perm_left xs).symm.nodup (partsLeft_nodup xs)

theorem length_partsGrouped (xs : List α) :
    (partsGrouped xs).length = if xs.isEmpty then 1 else 2 ^ (xs.length - 1) := by
  rw [(partsGrouped_perm_left xs).length_eq, length_partsLeft]

theorem partsGrouped_ne_special (x : α) (xs : List α) :
    partsGrouped (x :: xs) ≠ [[]] := by
  intro h
  have hp : IsPartition (x :: xs) [] := (mem_partsGrouped (x :: xs) []).mp (by simp [h])
  simp [IsPartition] at hp

/-- All splits with a nonempty prefix, in increasing prefix-length order. -/
def splits : List α → List (List α × List α)
  | [] => []
  | x :: xs => ([x], xs) :: (splits xs).map (fun (ys, zs) => (x :: ys, zs))

theorem mem_splits (xs ys zs : List α) :
    (ys, zs) ∈ splits xs ↔ ys ≠ [] ∧ ys ++ zs = xs := by
  induction xs generalizing ys zs with
  | nil =>
    simp only [splits, List.not_mem_nil, false_iff, not_and]
    intro h hcat
    exact h (List.append_eq_nil_iff.mp hcat).1
  | cons x xs ih =>
    constructor
    · intro h
      simp only [splits, List.mem_cons, List.mem_map, Prod.exists] at h
      rcases h with h | ⟨us, vs, hs, heq⟩
      · cases h
        simp
      · obtain ⟨_, hcat⟩ := (ih us vs).mp hs
        cases heq
        exact ⟨by simp, by simp [hcat]⟩
    · rintro ⟨hne, hcat⟩
      cases ys with
      | nil => exact False.elim (hne rfl)
      | cons y ys =>
        have heq : y = x ∧ ys ++ zs = xs := by simpa using hcat
        obtain ⟨rfl, htail⟩ := heq
        cases ys with
        | nil =>
          have hz : zs = xs := by simpa using htail
          subst zs
          simp [splits]
        | cons z ys =>
          have hm := (ih (z :: ys) zs).mpr ⟨by simp, htail⟩
          simp only [splits, List.mem_cons, List.mem_map]
          exact Or.inr ⟨(z :: ys, zs), hm, rfl⟩

theorem splits_snd_length_lt (xs : List α) (p : List α × List α)
    (hp : p ∈ splits xs) : p.2.length < xs.length := by
  obtain ⟨hne, hcat⟩ := (mem_splits xs p.1 p.2).mp hp
  have hlen := congrArg List.length hcat
  have hpos : 0 < p.1.length := List.length_pos_iff.mpr hne
  simp only [List.length_append] at hlen
  omega

/-- Actual recursive source `parts`, with proof-only split membership for termination. -/
def partsRecursive : (xs : List α) → List (Partition α)
  | [] => [[]]
  | x :: xs =>
    (splits (x :: xs)).attach.flatMap (fun p =>
      (partsRecursive p.val.2).map (List.cons p.val.1))
termination_by xs => xs.length
decreasing_by exact splits_snd_length_lt _ _ p.property

@[simp] theorem partsRecursive_nil : partsRecursive ([] : List α) = [[]] := by
  rw [partsRecursive]

/-- Proof attachments disappear from the source-equation correspondence. -/
theorem partsRecursive_cons (x : α) (xs : List α) :
    partsRecursive (x :: xs) =
      (splits (x :: xs)).flatMap (fun p => (partsRecursive p.2).map (List.cons p.1)) := by
  rw [partsRecursive]
  exact congrArg List.flatten
    (List.attach_map_val (l := splits (x :: xs))
      (f := fun p : List α × List α => (partsRecursive p.2).map (List.cons p.1)))

theorem partsRecursive_cons_cons (x y : α) (ys : List α) :
    partsRecursive (x :: y :: ys) =
      (partsRecursive (y :: ys)).map (consBlock x) ++
      (partsRecursive (y :: ys)).map (glueLeft x) := by
  rw [partsRecursive_cons]
  simp only [splits, List.flatMap_cons, List.flatMap_map]
  congr 1
  rw [partsRecursive_cons, List.map_flatMap]
  simp only [splits, List.flatMap_cons, List.flatMap_map,
    List.map_map, Function.comp_def, glueLeft]

/-- The recursive prefix-first enumeration is exactly the grouped source fold. -/
theorem partsRecursive_eq_grouped (xs : List α) : partsRecursive xs = partsGrouped xs := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    cases xs with
    | nil => simp [partsRecursive_cons, splits, partsGrouped, groupedStep]
    | cons y ys =>
      rw [partsRecursive_cons_cons, ih, partsGrouped_cons x (y :: ys),
        groupedStep_of_ne_special x _ (partsGrouped_ne_special y ys)]

theorem mem_partsRecursive (xs : List α) (p : Partition α) :
    p ∈ partsRecursive xs ↔ IsPartition xs p := by
  rw [partsRecursive_eq_grouped]
  exact mem_partsGrouped xs p

theorem partsRecursive_nodup (xs : List α) : (partsRecursive xs).Nodup := by
  rw [partsRecursive_eq_grouped]
  exact partsGrouped_nodup xs

theorem length_partsRecursive (xs : List α) :
    (partsRecursive xs).length = if xs.isEmpty then 1 else 2 ^ (xs.length - 1) := by
  rw [partsRecursive_eq_grouped]
  exact length_partsGrouped xs

theorem partsRecursive_perm_left (xs : List α) : (partsRecursive xs).Perm (partsLeft xs) := by
  rw [partsRecursive_eq_grouped]
  exact partsGrouped_perm_left xs


theorem extendRight_append_singleton (x : α) (p : Partition α) (block : List α) :
    extendRight x (p ++ [block]) =
      [p ++ [block] ++ [[x]], p ++ [block ++ [x]]] := by
  have hext : extendRight x (p ++ [block]) =
      [snocBlock x (p ++ [block]), bindRight x (p ++ [block])] := by
    cases p <;> rfl
  rw [hext]
  simp only [snocBlock, bindRight_append_singleton]

theorem extendRight_consBlock (x z : α) (p : Partition α) (hp : p ≠ []) :
    extendRight z (consBlock x p) = (extendRight z p).map (consBlock x) := by
  induction p using snoc_induction with
  | nil => exact False.elim (hp rfl)
  | snoc p block ih =>
    change extendRight z (([x] :: p) ++ [block]) = _
    rw [extendRight_append_singleton, extendRight_append_singleton]
    simp [consBlock]

theorem extendRight_glueLeft (x z : α) (p : Partition α) (hp : p ≠ []) :
    extendRight z (glueLeft x p) = (extendRight z p).map (glueLeft x) := by
  induction p using snoc_induction with
  | nil => exact False.elim (hp rfl)
  | snoc p block ih =>
    rw [extendRight_append_singleton]
    cases p with
    | nil => simp [glueLeft, extendRight, snocBlock, bindRight]
    | cons b bs =>
      change extendRight z (((x :: b) :: bs) ++ [block]) = _
      rw [extendRight_append_singleton]
      simp [glueLeft]

theorem stepRight_map_consBlock (x z : α) (ps : List (Partition α))
    (hp : ∀ p ∈ ps, p ≠ []) :
    stepRight z (ps.map (consBlock x)) = (stepRight z ps).map (consBlock x) := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    have hpn : p ≠ [] := hp p (by simp)
    have hps : ∀ q ∈ ps, q ≠ [] := fun q hq => hp q (by simp [hq])
    change extendRight z (consBlock x p) ++ stepRight z (ps.map (consBlock x)) =
      (extendRight z p ++ stepRight z ps).map (consBlock x)
    rw [List.map_append, extendRight_consBlock x z p hpn, ih hps]

theorem stepRight_map_glueLeft (x z : α) (ps : List (Partition α))
    (hp : ∀ p ∈ ps, p ≠ []) :
    stepRight z (ps.map (glueLeft x)) = (stepRight z ps).map (glueLeft x) := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    have hpn : p ≠ [] := hp p (by simp)
    have hps : ∀ q ∈ ps, q ≠ [] := fun q hq => hp q (by simp [hq])
    change extendRight z (glueLeft x p) ++ stepRight z (ps.map (glueLeft x)) =
      (extendRight z p ++ stepRight z ps).map (glueLeft x)
    rw [List.map_append, extendRight_glueLeft x z p hpn, ih hps]

theorem stepRight_append (x : α) (ps qs : List (Partition α)) :
    stepRight x (ps ++ qs) = stepRight x ps ++ stepRight x qs := by
  simp only [stepRight, List.flatMap_append]

theorem partsRight_cons_cons (x y : α) (ys : List α) :
    partsRight (x :: y :: ys) =
      (partsRight (y :: ys)).map (consBlock x) ++
      (partsRight (y :: ys)).map (glueLeft x) := by
  induction ys using snoc_induction with
  | nil => rfl
  | snoc ys z ih =>
    have hp : ∀ p ∈ partsRight (y :: ys), p ≠ [] := by
      intro p hm heq
      have hf := ((mem_partsRight (y :: ys) p).mp hm).1
      subst p
      simp at hf
    change partsRight ((x :: y :: ys) ++ [z]) =
      (partsRight ((y :: ys) ++ [z])).map (consBlock x) ++
      (partsRight ((y :: ys) ++ [z])).map (glueLeft x)
    simp only [partsRight_append_singleton]
    rw [ih, stepRight_append]
    rw [stepRight_map_consBlock x z _ hp, stepRight_map_glueLeft x z _ hp]

/-- Exact equality, as requested by source prop_parts3; no tie/order quotient is taken. -/
theorem partsRecursive_eq_right (xs : List α) : partsRecursive xs = partsRight xs := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    cases xs with
    | nil => rw [partsRecursive_eq_grouped]; rfl
    | cons y ys => rw [partsRecursive_cons_cons, partsRight_cons_cons, ih]

theorem partsGrouped_eq_right (xs : List α) : partsGrouped xs = partsRight xs := by
  rw [← partsRecursive_eq_grouped, partsRecursive_eq_right]


end OrderedPartitions
