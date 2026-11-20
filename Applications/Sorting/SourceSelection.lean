import Applications.Sorting.Specification
import Applications.Sequences.Multiplicity

/-!
# Selection with an explicitly reconstructed remainder

The VFA selection recurrence retains every occurrence and the source's exact
remainder order. Fuel and length-founded recursion are separate executable
definitions. The relation is arbitrary for occurrence and fuel laws; ordering
requires totality and transitivity, but neither antisymmetry nor payload equality.
The direct contents proof follows the executed branches independently of Perm.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Applications.Sorting.SourceSelection

universe u
variable {α : Type u}

/-- Compare the current candidate with each tail element and reconstruct the
remainder in the source order. Ties take the first branch. -/
def select (r : α → α → Prop) [DecidableRel r] (x : α) : List α → α × List α
  | [] => (x, [])
  | h :: t =>
      if r x h then
        let p := select r x t
        (p.1, h :: p.2)
      else
        let p := select r h t
        (p.1, x :: p.2)

theorem select_nil (r : α → α → Prop) [DecidableRel r] (x : α) :
    select r x [] = (x, []) := rfl

theorem select_cons (r : α → α → Prop) [DecidableRel r] (x h : α) (t : List α) :
    select r x (h :: t) = if r x h then
      ((select r x t).1, h :: (select r x t).2)
    else ((select r h t).1, x :: (select r h t).2) := rfl

/-- This occurrence law needs no order laws at all. -/
theorem select_perm (r : α → α → Prop) [DecidableRel r] (x : α) (xs : List α) :
    ((select r x xs).1 :: (select r x xs).2).Perm (x :: xs) := by
  induction xs generalizing x with
  | nil => exact List.Perm.refl _
  | cons h t ih =>
      by_cases hx : r x h
      · simp only [select, hx, ↓reduceIte]
        exact (List.Perm.swap h _ _).trans
          ((List.Perm.cons h (ih x)).trans (List.Perm.swap x h t))
      · simp only [select, hx, ↓reduceIte]
        exact (List.Perm.swap x _ _).trans (List.Perm.cons x (ih h))

theorem select_length (r : α → α → Prop) [DecidableRel r] (x : α) (xs : List α) :
    (select r x xs).2.length = xs.length := by
  have h := (select_perm r x xs).length_eq
  simpa only [List.length_cons] using Nat.succ.inj h

theorem select_mem (r : α → α → Prop) [DecidableRel r] (x : α) (xs : List α) :
    (select r x xs).1 ∈ x :: xs :=
  (select_perm r x xs).mem_iff.mp List.mem_cons_self

/-- Zero fuel discards the unprocessed suffix, exactly as in the source. -/
def sortFuel (r : α → α → Prop) [DecidableRel r] : List α → Nat → List α
  | _, 0 => []
  | [], _ + 1 => []
  | x :: xs, n + 1 =>
      let p := select r x xs
      p.1 :: sortFuel r p.2 n

theorem sortFuel_zero (r : α → α → Prop) [DecidableRel r] (xs : List α) :
    sortFuel r xs 0 = [] := rfl

theorem sortFuel_nil (r : α → α → Prop) [DecidableRel r] (n : Nat) :
    sortFuel r [] n = [] := by cases n <;> rfl

theorem sortFuel_cons (r : α → α → Prop) [DecidableRel r] (x : α)
    (xs : List α) (n : Nat) :
    sortFuel r (x :: xs) (n + 1) =
      (select r x xs).1 :: sortFuel r (select r x xs).2 n := rfl

theorem sortFuel_length (r : α → α → Prop) [DecidableRel r] (xs : List α)
    (n : Nat) : (sortFuel r xs n).length = min xs.length n := by
  induction n generalizing xs with
  | zero => simp [sortFuel]
  | succ n ih =>
      cases xs with
      | nil => simp [sortFuel]
      | cons x xs =>
          simp only [sortFuel_cons, List.length_cons, ih, select_length]
          omega

theorem sortFuel_perm (r : α → α → Prop) [DecidableRel r] (xs : List α)
    (n : Nat) (hn : xs.length ≤ n) : (sortFuel r xs n).Perm xs := by
  induction n generalizing xs with
  | zero =>
      have hx : xs = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hn)
      subst xs
      exact List.Perm.refl _
  | succ n ih =>
      cases xs with
      | nil => exact List.Perm.refl _
      | cons x xs =>
          rw [sortFuel_cons]
          apply (List.Perm.cons _ (ih (select r x xs).2 ?_)).trans
            (select_perm r x xs)
          rw [select_length]
          simpa only [List.length_cons, Nat.succ_le_succ_iff] using hn

def sort (r : α → α → Prop) [DecidableRel r] (xs : List α) : List α :=
  sortFuel r xs xs.length

theorem sort_perm (r : α → α → Prop) [DecidableRel r] (xs : List α) :
    (sort r xs).Perm xs := sortFuel_perm r xs xs.length (Nat.le_refl _)

/-- Direct recurrence proof, independent of permutation and its count bridge.
Even an unlawful Boolean equality still observes the same stored occurrences. -/
theorem select_contents [BEq α] (r : α → α → Prop) [DecidableRel r]
    (x : α) (xs : List α) :
    Sequences.Multiplicity.contents ((select r x xs).1 :: (select r x xs).2) =
      Sequences.Multiplicity.contents (x :: xs) := by
  induction xs generalizing x with
  | nil => rfl
  | cons h t ih =>
      by_cases hx : r x h
      · simp only [select, hx, ↓reduceIte]
        funext a
        have hi := congrFun (ih x) a
        simp only [Sequences.Multiplicity.contents_cons] at hi ⊢
        omega
      · simp only [select, hx, ↓reduceIte]
        funext a
        have hi := congrFun (ih h) a
        simp only [Sequences.Multiplicity.contents_cons] at hi ⊢
        omega

theorem sortFuel_contents [BEq α] (r : α → α → Prop) [DecidableRel r]
    (xs : List α) (n : Nat) (hn : xs.length ≤ n) :
    Sequences.Multiplicity.contents (sortFuel r xs n) =
      Sequences.Multiplicity.contents xs := by
  induction n generalizing xs with
  | zero =>
      have hx : xs = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hn)
      subst xs
      rfl
  | succ n ih =>
      cases xs with
      | nil => rfl
      | cons x xs =>
          have hr : (select r x xs).2.length ≤ n := by
            rw [select_length]
            simpa only [List.length_cons, Nat.succ_le_succ_iff] using hn
          rw [sortFuel_cons, Sequences.Multiplicity.contents_cons, ih _ hr]
          simpa only [Sequences.Multiplicity.contents_cons] using select_contents r x xs

theorem sort_contents [BEq α] (r : α → α → Prop) [DecidableRel r] (xs : List α) :
    Sequences.Multiplicity.contents (sort r xs) = Sequences.Multiplicity.contents xs :=
  sortFuel_contents r xs xs.length (Nat.le_refl _)

/-- A separate, transparent length-founded program. The recursive argument is
the actual reconstructed remainder, not a structural subterm of the input. -/
def sortWF (r : α → α → Prop) [DecidableRel r] : List α → List α
  | [] => []
  | x :: xs =>
      let p := select r x xs
      p.1 :: sortWF r p.2
termination_by xs => xs.length
decreasing_by
  simp only [select_length, List.length_cons]
  omega

theorem sortWF_nil (r : α → α → Prop) [DecidableRel r] :
    sortWF r [] = [] := by rw [sortWF]

theorem sortWF_cons (r : α → α → Prop) [DecidableRel r] (x : α) (xs : List α) :
    sortWF r (x :: xs) = (select r x xs).1 :: sortWF r (select r x xs).2 := by
  rw [sortWF]

/-- Agreement is proved through the two recurrences, without order assumptions. -/
theorem sortFuel_eq_sortWF (r : α → α → Prop) [DecidableRel r] (xs : List α)
    (n : Nat) (hn : xs.length ≤ n) : sortFuel r xs n = sortWF r xs := by
  induction n generalizing xs with
  | zero =>
      have hx : xs = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hn)
      subst xs
      exact (sortWF_nil r).symm
  | succ n ih =>
      cases xs with
      | nil => exact (sortWF_nil r).symm
      | cons x xs =>
          rw [sortFuel_cons, sortWF_cons, ih]
          rw [select_length]
          simpa only [List.length_cons, Nat.succ_le_succ_iff] using hn

theorem sort_eq_sortWF (r : α → α → Prop) [DecidableRel r] (xs : List α) :
    sort r xs = sortWF r xs := sortFuel_eq_sortWF r xs xs.length (Nat.le_refl _)

theorem sortFuel_saturated (r : α → α → Prop) [DecidableRel r] (xs : List α)
    (n : Nat) (hn : xs.length ≤ n) : sortFuel r xs n = sort r xs :=
  (sortFuel_eq_sortWF r xs n hn).trans (sort_eq_sortWF r xs).symm

/-- Insufficient fuel computes precisely the corresponding output prefix. -/
theorem sortFuel_prefix (r : α → α → Prop) [DecidableRel r] (xs : List α)
    (n : Nat) : sortFuel r xs n = (sortWF r xs).take n := by
  induction n generalizing xs with
  | zero => simp [sortFuel_zero]
  | succ n ih =>
      cases xs with
      | nil => simp [sortFuel_nil, sortWF_nil]
      | cons x xs => rw [sortFuel_cons, sortWF_cons, List.take_succ_cons, ih]

theorem sortWF_perm (r : α → α → Prop) [DecidableRel r] (xs : List α) :
    (sortWF r xs).Perm xs := by
  rw [← sort_eq_sortWF]
  exact sort_perm r xs

theorem sortFuel_mem (r : α → α → Prop) [DecidableRel r] (xs : List α)
    (n : Nat) {a : α} (ha : a ∈ sortFuel r xs n) : a ∈ xs := by
  rw [sortFuel_prefix] at ha
  exact (sortWF_perm r xs).mem_iff.mp (List.mem_of_mem_take ha)

/-- Insufficient fuel is exactly the failure of occurrence preservation. -/
theorem sortFuel_perm_iff (r : α → α → Prop) [DecidableRel r] (xs : List α)
    (n : Nat) : (sortFuel r xs n).Perm xs ↔ xs.length ≤ n := by
  constructor
  · intro h
    have hl := h.length_eq
    rw [sortFuel_length] at hl
    omega
  · exact sortFuel_perm r xs n

/-- If the seed is already a lower bound, select preserves it and the exact
tail. This is input-local and does not need global order laws. -/
theorem select_of_lower (r : α → α → Prop) [DecidableRel r] (x : α) (xs : List α)
    (hx : ∀ a ∈ xs, r x a) : select r x xs = (x, xs) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      have ha := hx a List.mem_cons_self
      have ht : ∀ b ∈ xs, r x b := fun b hb => hx b (List.mem_cons_of_mem a hb)
      simp only [select, ha, ↓reduceIte, ih ht]

theorem sortWF_of_pairwise (r : α → α → Prop) [DecidableRel r] (xs : List α)
    (hx : xs.Pairwise r) : sortWF r xs = xs := by
  induction xs with
  | nil => exact sortWF_nil r
  | cons x xs ih =>
      obtain ⟨hl, ht⟩ := List.pairwise_cons.mp hx
      rw [sortWF_cons, select_of_lower r x xs hl]
      exact congrArg (List.cons x) (ih ht)

theorem sort_of_pairwise (r : α → α → Prop) [DecidableRel r] (xs : List α)
    (hx : xs.Pairwise r) : sort r xs = xs := by
  rw [sort_eq_sortWF]
  exact sortWF_of_pairwise r xs hx

section Order
variable (r : α → α → Prop) [DecidableRel r] [Std.Total r] [IsTrans α r]

theorem select_lower (x : α) (xs : List α) :
    ∀ a ∈ x :: xs, r (select r x xs).1 a := by
  induction xs generalizing x with
  | nil =>
      intro a ha
      have hx : a = x := List.mem_singleton.mp ha
      subst a
      exact (Std.Total.total (r := r) x x).elim id id
  | cons h t ih =>
      by_cases hx : r x h
      · simp only [select, hx, ↓reduceIte]
        intro a ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact ih a a List.mem_cons_self
        · rcases List.mem_cons.mp ha with rfl | ha
          · exact IsTrans.trans _ _ _ (ih x x List.mem_cons_self) hx
          · exact ih x a (List.mem_cons_of_mem x ha)
      · simp only [select, hx, ↓reduceIte]
        have hh : r h x := (Std.Total.total (r := r) x h).resolve_left hx
        intro a ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact IsTrans.trans _ _ _ (ih h h List.mem_cons_self) hh
        · exact ih h a ha

theorem select_le_seed (x : α) (xs : List α) : r (select r x xs).1 x :=
  select_lower r x xs x List.mem_cons_self

theorem select_smallest (x : α) (xs : List α) :
    ∀ a ∈ (select r x xs).2, r (select r x xs).1 a := by
  intro a ha
  exact select_lower r x xs a
    ((select_perm r x xs).mem_iff.mp (List.mem_cons_of_mem _ ha))

/-- A truncated result is ordered, even though it loses occurrences. -/
theorem sortFuel_pairwise (xs : List α) (n : Nat) : (sortFuel r xs n).Pairwise r := by
  induction n generalizing xs with
  | zero => exact List.Pairwise.nil
  | succ n ih =>
      cases xs with
      | nil => exact List.Pairwise.nil
      | cons x xs =>
          rw [sortFuel_cons, List.pairwise_cons]
          refine ⟨?_, ih _⟩
          intro a ha
          exact select_smallest r x xs a (sortFuel_mem r _ n ha)

theorem sort_pairwise (xs : List α) : (sort r xs).Pairwise r :=
  sortFuel_pairwise r xs xs.length

theorem sortWF_pairwise (xs : List α) : (sortWF r xs).Pairwise r := by
  rw [← sort_eq_sortWF]
  exact sort_pairwise r xs

theorem sort_correct (xs : List α) : (sort r xs).Pairwise r ∧ (sort r xs).Perm xs :=
  ⟨sort_pairwise r xs, sort_perm r xs⟩

theorem sortWF_correct (xs : List α) :
    (sortWF r xs).Pairwise r ∧ (sortWF r xs).Perm xs :=
  ⟨sortWF_pairwise r xs, sortWF_perm r xs⟩

theorem sort_idempotent (xs : List α) : sort r (sort r xs) = sort r xs :=
  sort_of_pairwise r (sort r xs) (sort_pairwise r xs)

end Order

end Applications.Sorting.SourceSelection
