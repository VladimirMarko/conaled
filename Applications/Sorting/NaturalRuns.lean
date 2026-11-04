import Applications.Sorting.Stable
import Batteries.Data.DList
import Mathlib.Data.Multiset.AddSub

/-!
The natural-run scanner from FDSA, Chapter 2, with its actual mutual workers.
Ascending builders use `Batteries.DList`; descending accumulators use lists.
These declarations concern returned values, not builder or machine costs.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Applications.Sorting

universe u v
variable {α : Type u} {κ : Type v}

/-- The source's law for every raw difference-list function. -/
def DListLaw (f : List α → List α) : Prop :=
  ∀ xs ys, f (xs ++ ys) = f xs ++ ys

theorem dListLaw_iff (f : List α → List α) :
    DListLaw f ↔ ∀ ys, f ys = f [] ++ ys := by
  constructor
  · intro h ys
    simpa only [List.nil_append] using h [] ys
  · intro h xs ys
    rw [h (xs ++ ys), h xs, List.append_assoc]

theorem dListLaw_cons (a : α) : DListLaw (List.cons a) := by
  intro xs ys
  rfl

theorem DListLaw.push {f : List α → List α} (h : DListLaw f) (a : α) :
    DListLaw (fun ys => f (a :: ys)) := by
  intro xs ys
  exact h (a :: xs) ys

/-- Wrap the original function; do not evaluate and rebuild its prefix. -/
def dListOfLaw (f : List α → List α) (h : DListLaw f) : Batteries.DList α :=
  ⟨f, (dListLaw_iff f).mp h⟩

@[simp] theorem dListOfLaw_apply (f : List α → List α) (h : DListLaw f)
    (ys : List α) : (dListOfLaw f h).apply ys = f ys := rfl

@[simp] theorem dListOfLaw_toList (f : List α → List α) (h : DListLaw f) :
    (dListOfLaw f h).toList = f [] := rfl

theorem dListOfLaw_push (f : List α → List α) (h : DListLaw f) (a : α) :
    (dListOfLaw f h).push a = dListOfLaw (fun ys => f (a :: ys)) (h.push a) := rfl

theorem dList_apply_eq (d : Batteries.DList α) (ys : List α) :
    d.apply ys = d.toList ++ ys := by
  cases d with
  | mk f h => exact h ys

theorem dList_push_apply (d : Batteries.DList α) (a : α) (ys : List α) :
    (d.push a).apply ys = d.apply (a :: ys) := by
  cases d
  rfl

mutual
  /-- Test the first pair once, then choose the corresponding source worker. -/
  def runsBy (lt : α → α → Bool) : List α → List (List α)
    | [] => []
    | [a] => [[a]]
    | a :: b :: xs =>
        if lt b a then descBy lt b [a] xs
        else ascBy lt b (Batteries.DList.singleton a) xs
  termination_by xs => xs.length
  decreasing_by all_goals simp_wf <;> omega

  /-- The builder represents the consumed prefix before the current element. -/
  def ascBy (lt : α → α → Bool) (a : α) (d : Batteries.DList α) :
      List α → List (List α)
    | [] => [d.apply [a]]
    | b :: bs =>
        if lt b a then d.apply [a] :: runsBy lt (b :: bs)
        else ascBy lt b (d.push a) bs
  termination_by ys => ys.length + 1
  decreasing_by all_goals simp_wf <;> omega

  /-- The accumulator contains the consumed descending prefix in reverse order. -/
  def descBy (lt : α → α → Bool) (a : α) (acc : List α) :
      List α → List (List α)
    | [] => [a :: acc]
    | b :: bs =>
        if lt b a then descBy lt b (a :: acc) bs
        else (a :: acc) :: runsBy lt (b :: bs)
  termination_by ys => ys.length + 1
  decreasing_by all_goals simp_wf <;> omega
end

@[simp] theorem runsBy_nil (lt : α → α → Bool) : runsBy lt [] = [] := by
  rw [runsBy]

@[simp] theorem runsBy_singleton (lt : α → α → Bool) (a : α) :
    runsBy lt [a] = [[a]] := by
  rw [runsBy]

theorem runsBy_cons_cons (lt : α → α → Bool) (a b : α) (xs : List α) :
    runsBy lt (a :: b :: xs) =
      if lt b a then descBy lt b [a] xs
      else ascBy lt b (Batteries.DList.singleton a) xs := by
  rw [runsBy]

@[simp] theorem ascBy_nil (lt : α → α → Bool) (a : α) (d : Batteries.DList α) :
    ascBy lt a d [] = [d.apply [a]] := by
  rw [ascBy]

theorem ascBy_cons (lt : α → α → Bool) (a b : α) (d : Batteries.DList α)
    (bs : List α) :
    ascBy lt a d (b :: bs) =
      if lt b a then d.apply [a] :: runsBy lt (b :: bs)
      else ascBy lt b (d.push a) bs := by
  rw [ascBy]

@[simp] theorem descBy_nil (lt : α → α → Bool) (a : α) (acc : List α) :
    descBy lt a acc [] = [a :: acc] := by
  rw [descBy]

theorem descBy_cons (lt : α → α → Bool) (a b : α) (acc bs : List α) :
    descBy lt a acc (b :: bs) =
      if lt b a then descBy lt b (a :: acc) bs
      else (a :: acc) :: runsBy lt (b :: bs) := by
  rw [descBy]

/-- The raw source worker is available for every function satisfying its D law. -/
abbrev ascSourceBy (lt : α → α → Bool) (a : α) (f : List α → List α)
    (h : DListLaw f) (ys : List α) : List (List α) :=
  ascBy lt a (dListOfLaw f h) ys

theorem ascSourceBy_nil (lt : α → α → Bool) (a : α) (f : List α → List α)
    (h : DListLaw f) : ascSourceBy lt a f h [] = [f [a]] := by
  exact ascBy_nil lt a (dListOfLaw f h)

theorem ascSourceBy_cons (lt : α → α → Bool) (a b : α) (f : List α → List α)
    (h : DListLaw f) (bs : List α) :
    ascSourceBy lt a f h (b :: bs) =
      if lt b a then f [a] :: runsBy lt (b :: bs)
      else ascSourceBy lt b (fun ys => f (a :: ys)) (h.push a) bs := by
  simpa only [ascSourceBy, dListOfLaw_apply, dListOfLaw_push] using
    ascBy_cons lt a b (dListOfLaw f h) bs

mutual
  /-- Every input occurrence appears in exactly one emitted run. -/
  theorem runsBy_perm (lt : α → α → Bool) (xs : List α) :
      (runsBy lt xs).flatten.Perm xs := by
    cases xs with
    | nil => simp
    | cons a xs =>
      cases xs with
      | nil => simp
      | cons b bs =>
        rw [runsBy_cons_cons]
        split
        · simpa using descBy_perm lt b [a] bs
        · simpa only [Batteries.DList.toList_singleton, List.singleton_append] using
            ascBy_perm lt b (Batteries.DList.singleton a) bs
  termination_by xs.length
  decreasing_by all_goals simp_wf <;> omega

  /-- The arbitrary builder prefix precedes the current element chronologically. -/
  theorem ascBy_perm (lt : α → α → Bool) (a : α) (d : Batteries.DList α)
      (ys : List α) : (ascBy lt a d ys).flatten.Perm (d.toList ++ a :: ys) := by
    cases ys with
    | nil => simp [dList_apply_eq]
    | cons b bs =>
      rw [ascBy_cons]
      split
      · simpa only [List.flatten_cons, dList_apply_eq, List.append_assoc,
          List.singleton_append] using
          (runsBy_perm lt (b :: bs)).append_left (d.apply [a])
      · simpa only [Batteries.DList.toList_push, List.append_assoc,
          List.singleton_append] using ascBy_perm lt b (d.push a) bs
  termination_by ys.length + 1
  decreasing_by all_goals simp_wf <;> omega

  /-- The arbitrary descending accumulator is in reverse chronological order. -/
  theorem descBy_perm (lt : α → α → Bool) (a : α) (acc ys : List α) :
      (descBy lt a acc ys).flatten.Perm (acc.reverse ++ a :: ys) := by
    cases ys with
    | nil =>
      simpa only [descBy_nil, List.flatten_cons, List.flatten_nil, List.append_nil,
        List.reverse_cons] using (List.reverse_perm (a :: acc)).symm
    | cons b bs =>
      rw [descBy_cons]
      split
      · simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using
          descBy_perm lt b (a :: acc) bs
      · simpa only [List.flatten_cons, List.reverse_cons, List.append_assoc,
          List.singleton_append] using
          ((List.reverse_perm (a :: acc)).symm.append (runsBy_perm lt (b :: bs)))
  termination_by ys.length + 1
  decreasing_by all_goals simp_wf <;> omega
end

theorem runsBy_multiset (lt : α → α → Bool) (xs : List α) :
    ((runsBy lt xs).flatten : Multiset α) = (xs : Multiset α) :=
  Multiset.coe_eq_coe.mpr (runsBy_perm lt xs)

theorem ascBy_multiset (lt : α → α → Bool) (a : α) (d : Batteries.DList α)
    (ys : List α) : ((ascBy lt a d ys).flatten : Multiset α) =
      (d.toList : Multiset α) + ((a :: ys : List α) : Multiset α) := by
  rw [Multiset.coe_add]
  exact Multiset.coe_eq_coe.mpr (ascBy_perm lt a d ys)

theorem descBy_multiset (lt : α → α → Bool) (a : α) (acc ys : List α) :
    ((descBy lt a acc ys).flatten : Multiset α) =
      (acc : Multiset α) + ((a :: ys : List α) : Multiset α) := by
  rw [Multiset.coe_add]
  exact Multiset.coe_eq_coe.mpr
    ((descBy_perm lt a acc ys).trans ((List.reverse_perm acc).append_right (a :: ys)))

@[simp] theorem runsBy_flatten_length (lt : α → α → Bool) (xs : List α) :
    (runsBy lt xs).flatten.length = xs.length := (runsBy_perm lt xs).length_eq

theorem ascBy_flatten_length (lt : α → α → Bool) (a : α) (d : Batteries.DList α)
    (ys : List α) : (ascBy lt a d ys).flatten.length = d.toList.length + 1 + ys.length := by
  simpa only [List.length_append, List.length_cons, Nat.add_assoc, Nat.add_comm 1] using
    (ascBy_perm lt a d ys).length_eq

theorem descBy_flatten_length (lt : α → α → Bool) (a : α) (acc ys : List α) :
    (descBy lt a acc ys).flatten.length = acc.length + 1 + ys.length := by
  simpa only [List.length_append, List.length_cons, List.length_reverse,
    Nat.add_assoc, Nat.add_comm 1] using (descBy_perm lt a acc ys).length_eq

theorem mem_runsBy_flatten (lt : α → α → Bool) (xs : List α) (a : α) :
    a ∈ (runsBy lt xs).flatten ↔ a ∈ xs := (runsBy_perm lt xs).mem_iff

mutual
  /-- No empty run is emitted, even for a comparator without order laws. -/
  theorem runsBy_nonempty (lt : α → α → Bool) (xs : List α) :
      ∀ run ∈ runsBy lt xs, run ≠ [] := by
    cases xs with
    | nil => simp
    | cons a xs =>
      cases xs with
      | nil => simp
      | cons b bs =>
        rw [runsBy_cons_cons]
        split
        · exact descBy_nonempty lt b [a] bs
        · exact ascBy_nonempty lt b (Batteries.DList.singleton a) bs
  termination_by xs.length
  decreasing_by all_goals simp_wf <;> omega

  theorem ascBy_nonempty (lt : α → α → Bool) (a : α) (d : Batteries.DList α)
      (ys : List α) : ∀ run ∈ ascBy lt a d ys, run ≠ [] := by
    have he : d.apply [a] ≠ [] := by simp [dList_apply_eq]
    cases ys with
    | nil => simpa using he
    | cons b bs =>
      rw [ascBy_cons]
      split
      · simpa only [List.mem_cons, forall_eq_or_imp] using
          And.intro he (runsBy_nonempty lt (b :: bs))
      · exact ascBy_nonempty lt b (d.push a) bs
  termination_by ys.length + 1
  decreasing_by all_goals simp_wf <;> omega

  theorem descBy_nonempty (lt : α → α → Bool) (a : α) (acc ys : List α) :
      ∀ run ∈ descBy lt a acc ys, run ≠ [] := by
    cases ys with
    | nil => simp
    | cons b bs =>
      rw [descBy_cons]
      split
      · exact descBy_nonempty lt b (a :: acc) bs
      · simpa using runsBy_nonempty lt (b :: bs)
  termination_by ys.length + 1
  decreasing_by all_goals simp_wf <;> omega
end

mutual
  /-- The number of runs is bounded by the number of input elements. -/
  theorem runsBy_length_le (lt : α → α → Bool) (xs : List α) :
      (runsBy lt xs).length ≤ xs.length := by
    cases xs with
    | nil => simp
    | cons a xs =>
      cases xs with
      | nil => simp
      | cons b bs =>
        rw [runsBy_cons_cons]
        split
        · have h := descBy_length_le lt b [a] bs
          simp only [List.length_cons]
          omega
        · have h := ascBy_length_le lt b (Batteries.DList.singleton a) bs
          simp only [List.length_cons]
          omega
  termination_by xs.length
  decreasing_by all_goals simp_wf <;> omega

  /-- The bound is independent of the size of the arbitrary consumed prefix. -/
  theorem ascBy_length_le (lt : α → α → Bool) (a : α) (d : Batteries.DList α)
      (ys : List α) : (ascBy lt a d ys).length ≤ ys.length + 1 := by
    cases ys with
    | nil => simp
    | cons b bs =>
      rw [ascBy_cons]
      split
      · have h := runsBy_length_le lt (b :: bs)
        simp only [List.length_cons] at h ⊢
        omega
      · have h := ascBy_length_le lt b (d.push a) bs
        simp only [List.length_cons]
        omega
  termination_by ys.length + 1
  decreasing_by all_goals simp_wf <;> omega

  theorem descBy_length_le (lt : α → α → Bool) (a : α) (acc ys : List α) :
      (descBy lt a acc ys).length ≤ ys.length + 1 := by
    cases ys with
    | nil => simp
    | cons b bs =>
      rw [descBy_cons]
      split
      · have h := descBy_length_le lt b (a :: acc) bs
        simp only [List.length_cons]
        omega
      · have h := runsBy_length_le lt (b :: bs)
        simp only [List.length_cons] at h ⊢
        omega
  termination_by ys.length + 1
  decreasing_by all_goals simp_wf <;> omega
end

theorem ascBy_ne_nil (lt : α → α → Bool) (a : α) (d : Batteries.DList α)
    (ys : List α) : ascBy lt a d ys ≠ [] := by
  intro h
  have hl := ascBy_flatten_length lt a d ys
  simp only [h, List.flatten_nil, List.length_nil] at hl
  omega

theorem descBy_ne_nil (lt : α → α → Bool) (a : α) (acc ys : List α) :
    descBy lt a acc ys ≠ [] := by
  intro h
  have hl := descBy_flatten_length lt a acc ys
  simp only [h, List.flatten_nil, List.length_nil] at hl
  omega

@[simp] theorem runsBy_eq_nil_iff (lt : α → α → Bool) (xs : List α) :
    runsBy lt xs = [] ↔ xs = [] := by
  constructor
  · intro h
    have hp := runsBy_perm lt xs
    rw [h, List.flatten_nil] at hp
    exact (List.Perm.nil_eq hp).symm
  · rintro rfl
    exact runsBy_nil lt

theorem ascSourceBy_perm (lt : α → α → Bool) (a : α) (f : List α → List α)
    (h : DListLaw f) (ys : List α) :
    (ascSourceBy lt a f h ys).flatten.Perm (f [] ++ a :: ys) :=
  ascBy_perm lt a (dListOfLaw f h) ys

theorem ascSourceBy_flatten_length (lt : α → α → Bool) (a : α)
    (f : List α → List α) (h : DListLaw f) (ys : List α) :
    (ascSourceBy lt a f h ys).flatten.length = (f []).length + 1 + ys.length :=
  ascBy_flatten_length lt a (dListOfLaw f h) ys

private theorem pairwise_snoc (r : α → α → Prop) (xs : List α) (a : α)
    (hp : xs.Pairwise r) (hb : ∀ x ∈ xs, r x a) : (xs ++ [a]).Pairwise r := by
  apply List.pairwise_append.mpr
  refine ⟨hp, by simp, ?_⟩
  intro x hx y hy
  have hy' : y = a := by simpa only [List.mem_singleton] using hy
  subst y
  exact hb x hx

mutual
  /-- Ordering is observed separately; compatibility is required only on the input. -/
  theorem runsBy_pairwise_on (r : α → α → Prop) (lt : α → α → Bool)
      (ht : ∀ ⦃x y z : α⦄, r x y → r y z → r x z) (xs : List α)
      (hc : ∀ x ∈ xs, ∀ y ∈ xs,
        (lt x y = true → r x y) ∧ (lt x y = false → r y x)) :
      ∀ run ∈ runsBy lt xs, run.Pairwise r := by
    cases xs with
    | nil => simp
    | cons a xs =>
      cases xs with
      | nil => simp
      | cons b bs =>
        have hc' : ∀ x ∈ b :: bs, ∀ y ∈ b :: bs,
            (lt x y = true → r x y) ∧ (lt x y = false → r y x) :=
          fun x hx y hy => hc x (List.mem_cons.mpr (Or.inr hx))
            y (List.mem_cons.mpr (Or.inr hy))
        rw [runsBy_cons_cons]
        split
        · rename_i hba
          apply descBy_pairwise_on r lt ht b [a] bs hc' (by simp)
          intro x hx
          have hx' : x = a := by simpa only [List.mem_singleton] using hx
          subst x
          exact (hc b (by simp) a (by simp)).1 hba
        · rename_i hba
          apply ascBy_pairwise_on r lt ht b (Batteries.DList.singleton a) bs hc'
          · simp only [Batteries.DList.toList_singleton, List.pairwise_singleton]
          · intro x hx
            have hx' : x = a := by
              simpa only [Batteries.DList.toList_singleton, List.mem_singleton] using hx
            subst x
            exact (hc b (by simp) a (by simp)).2 (Bool.eq_false_iff.mpr hba)
  termination_by xs.length
  decreasing_by all_goals simp_wf <;> omega

  /-- Every lawful builder is allowed; its sorted prefix and upper bound are explicit. -/
  theorem ascBy_pairwise_on (r : α → α → Prop) (lt : α → α → Bool)
      (ht : ∀ ⦃x y z : α⦄, r x y → r y z → r x z) (a : α) (d : Batteries.DList α) (ys : List α)
      (hc : ∀ x ∈ a :: ys, ∀ y ∈ a :: ys,
        (lt x y = true → r x y) ∧ (lt x y = false → r y x))
      (hp : d.toList.Pairwise r) (hb : ∀ x ∈ d.toList, r x a) :
      ∀ run ∈ ascBy lt a d ys, run.Pairwise r := by
    have he : (d.apply [a]).Pairwise r := by
      rw [dList_apply_eq]
      exact pairwise_snoc r d.toList a hp hb
    cases ys with
    | nil => simpa using he
    | cons b bs =>
      have hc' : ∀ x ∈ b :: bs, ∀ y ∈ b :: bs,
          (lt x y = true → r x y) ∧ (lt x y = false → r y x) :=
        fun x hx y hy => hc x (List.mem_cons.mpr (Or.inr hx))
          y (List.mem_cons.mpr (Or.inr hy))
      rw [ascBy_cons]
      split
      · intro run hr
        rcases List.mem_cons.mp hr with hr | hr
        · subst run
          exact he
        · exact runsBy_pairwise_on r lt ht (b :: bs) hc' run hr
      · rename_i hba
        have hab : r a b := (hc b (by simp) a (by simp)).2 (Bool.eq_false_iff.mpr hba)
        apply ascBy_pairwise_on r lt ht b (d.push a) bs hc'
        · rw [Batteries.DList.toList_push]
          exact pairwise_snoc r d.toList a hp hb
        · intro x hx
          rw [Batteries.DList.toList_push, List.mem_append] at hx
          rcases hx with hx | hx
          · exact ht (hb x hx) hab
          · have hx' : x = a := by simpa only [List.mem_singleton] using hx
            subst x
            exact hab
  termination_by ys.length + 1
  decreasing_by all_goals simp_wf <;> omega

  /-- An arbitrary descending accumulator needs its own sortedness and lower bound. -/
  theorem descBy_pairwise_on (r : α → α → Prop) (lt : α → α → Bool)
      (ht : ∀ ⦃x y z : α⦄, r x y → r y z → r x z) (a : α) (acc ys : List α)
      (hc : ∀ x ∈ a :: ys, ∀ y ∈ a :: ys,
        (lt x y = true → r x y) ∧ (lt x y = false → r y x))
      (hp : acc.Pairwise r) (hb : ∀ x ∈ acc, r a x) :
      ∀ run ∈ descBy lt a acc ys, run.Pairwise r := by
    have he : (a :: acc).Pairwise r := List.pairwise_cons.mpr ⟨hb, hp⟩
    cases ys with
    | nil => simpa using he
    | cons b bs =>
      have hc' : ∀ x ∈ b :: bs, ∀ y ∈ b :: bs,
          (lt x y = true → r x y) ∧ (lt x y = false → r y x) :=
        fun x hx y hy => hc x (List.mem_cons.mpr (Or.inr hx))
          y (List.mem_cons.mpr (Or.inr hy))
      rw [descBy_cons]
      split
      · rename_i hba
        have hrel : r b a := (hc b (by simp) a (by simp)).1 hba
        apply descBy_pairwise_on r lt ht b (a :: acc) bs hc' he
        intro x hx
        rcases List.mem_cons.mp hx with hx | hx
        · subst x
          exact hrel
        · exact ht hrel (hb x hx)
      · intro run hr
        rcases List.mem_cons.mp hr with hr | hr
        · subst run
          exact he
        · exact runsBy_pairwise_on r lt ht (b :: bs) hc' run hr
  termination_by ys.length + 1
  decreasing_by all_goals simp_wf <;> omega
end

theorem ascSourceBy_pairwise_on (r : α → α → Prop) (lt : α → α → Bool)
    (ht : ∀ ⦃x y z : α⦄, r x y → r y z → r x z) (a : α) (f : List α → List α) (h : DListLaw f) (ys : List α)
    (hc : ∀ x ∈ a :: ys, ∀ y ∈ a :: ys,
      (lt x y = true → r x y) ∧ (lt x y = false → r y x))
    (hp : (f []).Pairwise r) (hb : ∀ x ∈ f [], r x a) :
    ∀ run ∈ ascSourceBy lt a f h ys, run.Pairwise r :=
  ascBy_pairwise_on r lt ht a (dListOfLaw f h) ys hc hp hb

theorem runsBy_sorted_compatible_on [LE κ] [Std.IsPreorder κ]
    (key : α → κ) (lt : α → α → Bool) (xs : List α)
    (hc : ∀ x ∈ xs, ∀ y ∈ xs,
      (lt x y = true → key x ≤ key y) ∧ (lt x y = false → key y ≤ key x)) :
    ∀ run ∈ runsBy lt xs, KeySorted key run :=
  runsBy_pairwise_on (fun x y => key x ≤ key y) lt
    (fun _ _ _ hab hbc => Std.le_trans hab hbc) xs hc

theorem ascBy_sorted_compatible_on [LE κ] [Std.IsPreorder κ]
    (key : α → κ) (lt : α → α → Bool) (a : α) (d : Batteries.DList α) (ys : List α)
    (hc : ∀ x ∈ a :: ys, ∀ y ∈ a :: ys,
      (lt x y = true → key x ≤ key y) ∧ (lt x y = false → key y ≤ key x))
    (hp : KeySorted key d.toList) (hb : ∀ x ∈ d.toList, key x ≤ key a) :
    ∀ run ∈ ascBy lt a d ys, KeySorted key run :=
  ascBy_pairwise_on (fun x y => key x ≤ key y) lt
    (fun _ _ _ hab hbc => Std.le_trans hab hbc) a d ys hc hp hb

theorem descBy_sorted_compatible_on [LE κ] [Std.IsPreorder κ]
    (key : α → κ) (lt : α → α → Bool) (a : α) (acc ys : List α)
    (hc : ∀ x ∈ a :: ys, ∀ y ∈ a :: ys,
      (lt x y = true → key x ≤ key y) ∧ (lt x y = false → key y ≤ key x))
    (hp : KeySorted key acc) (hb : ∀ x ∈ acc, key a ≤ key x) :
    ∀ run ∈ descBy lt a acc ys, KeySorted key run :=
  descBy_pairwise_on (fun x y => key x ≤ key y) lt
    (fun _ _ _ hab hbc => Std.le_trans hab hbc) a acc ys hc hp hb

/-- Adjacent false comparisons suffice for a single ascending worker output. -/
theorem ascBy_of_chain (lt : α → α → Bool) (a : α) (d : Batteries.DList α)
    (ys : List α) (h : (a :: ys).IsChain (fun x y => lt y x = false)) :
    ascBy lt a d ys = [d.apply (a :: ys)] := by
  induction ys generalizing a d with
  | nil => exact ascBy_nil lt a d
  | cons b bs ih =>
    have hc := List.isChain_cons_cons.mp h
    simp only [ascBy_cons, hc.1, Bool.false_eq_true, ↓reduceIte]
    rw [ih b (d.push a) hc.2, dList_push_apply]

/-- Adjacent true comparisons suffice; the arbitrary accumulator is unchanged. -/
theorem descBy_of_chain (lt : α → α → Bool) (a : α) (acc ys : List α)
    (h : (a :: ys).IsChain (fun x y => lt y x = true)) :
    descBy lt a acc ys = [ys.reverse ++ a :: acc] := by
  induction ys generalizing a acc with
  | nil => simp
  | cons b bs ih =>
    have hc := List.isChain_cons_cons.mp h
    simp only [descBy_cons, hc.1, ↓reduceIte]
    rw [ih b (a :: acc) hc.2]
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append]

theorem runsBy_of_ascending_chain (lt : α → α → Bool) (xs : List α)
    (hne : xs ≠ []) (h : xs.IsChain (fun x y => lt y x = false)) :
    runsBy lt xs = [xs] := by
  cases xs with
  | nil => exact (hne rfl).elim
  | cons a xs =>
    cases xs with
    | nil => exact runsBy_singleton lt a
    | cons b bs =>
      have hc := List.isChain_cons_cons.mp h
      simp only [runsBy_cons_cons, hc.1, Bool.false_eq_true, ↓reduceIte]
      rw [ascBy_of_chain lt b (Batteries.DList.singleton a) bs hc.2]
      rfl

theorem runsBy_of_descending_chain (lt : α → α → Bool) (xs : List α)
    (hne : xs ≠ []) (h : xs.IsChain (fun x y => lt y x = true)) :
    runsBy lt xs = [xs.reverse] := by
  cases xs with
  | nil => exact (hne rfl).elim
  | cons a xs =>
    cases xs with
    | nil => simp
    | cons b bs =>
      have hc := List.isChain_cons_cons.mp h
      simp only [runsBy_cons_cons, hc.1, ↓reduceIte]
      rw [descBy_of_chain lt b [a] bs hc.2]
      simp only [List.reverse_cons, List.append_assoc, List.singleton_append]

/-- Compare keys while retaining the complete payload records. -/
abbrev runsOn [LT κ] [DecidableLT κ] (key : α → κ) (xs : List α) : List (List α) :=
  runsBy (fun a b => decide (key a < key b)) xs

theorem runsOn_sorted [LinearOrder κ] (key : α → κ) (xs : List α) :
    ∀ run ∈ runsOn key xs, KeySorted key run := by
  apply runsBy_sorted_compatible_on key
  intro x _ y _
  exact ⟨fun h => le_of_lt (of_decide_eq_true h),
    fun h => le_of_not_gt (of_decide_eq_false h)⟩

theorem ascBy_sorted [LinearOrder κ] (key : α → κ) (a : α)
    (d : Batteries.DList α) (ys : List α)
    (hp : KeySorted key d.toList) (hb : ∀ x ∈ d.toList, key x ≤ key a) :
    ∀ run ∈ ascBy (fun x y => decide (key x < key y)) a d ys, KeySorted key run := by
  apply ascBy_sorted_compatible_on key _ a d ys _ hp hb
  intro x _ y _
  exact ⟨fun h => le_of_lt (of_decide_eq_true h),
    fun h => le_of_not_gt (of_decide_eq_false h)⟩

theorem descBy_sorted [LinearOrder κ] (key : α → κ) (a : α) (acc ys : List α)
    (hp : KeySorted key acc) (hb : ∀ x ∈ acc, key a ≤ key x) :
    ∀ run ∈ descBy (fun x y => decide (key x < key y)) a acc ys, KeySorted key run := by
  apply descBy_sorted_compatible_on key _ a acc ys _ hp hb
  intro x _ y _
  exact ⟨fun h => le_of_lt (of_decide_eq_true h),
    fun h => le_of_not_gt (of_decide_eq_false h)⟩

theorem ascSourceBy_sorted [LinearOrder κ] (key : α → κ) (a : α)
    (f : List α → List α) (h : DListLaw f) (ys : List α)
    (hp : KeySorted key (f [])) (hb : ∀ x ∈ f [], key x ≤ key a) :
    ∀ run ∈ ascSourceBy (fun x y => decide (key x < key y)) a f h ys,
      KeySorted key run :=
  ascBy_sorted key a (dListOfLaw f h) ys hp hb

/-- The source best-case value law excludes the empty input explicitly. -/
theorem runsOn_of_sorted [LinearOrder κ] (key : α → κ) (xs : List α)
    (h : KeySorted key xs) (hne : xs ≠ []) : runsOn key xs = [xs] := by
  apply runsBy_of_ascending_chain _ xs hne
  exact h.isChain.imp (fun _ _ hxy => decide_eq_false (not_lt_of_ge hxy))

/-- The reversal law needs only the supplied strict comparisons, not order axioms. -/
theorem runsOn_of_strictly_descending [LT κ] [DecidableLT κ]
    (key : α → κ) (xs : List α) (h : xs.Pairwise (fun x y => key y < key x))
    (hne : xs ≠ []) : runsOn key xs = [xs.reverse] := by
  apply runsBy_of_descending_chain _ xs hne
  exact h.isChain.imp (fun _ _ hxy => decide_eq_true hxy)

end Applications.Sorting
