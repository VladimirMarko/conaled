import Applications.Subsequences.Candidates
import Applications.Segments.Prefixes
import Applications.Sorting.SourceMerge

/-! Length-key merge and actual adjacent thinning of increasing subsequences. -/
set_option autoImplicit false
set_option warningAsError true
namespace Subsequences
universe u
variable {α : Type u}
open Optimization.Thinning (Covers IsThinning Represents bump thinBy)
open Segments (LengthOrdered)

/-- Standard merge has the same left-biased recurrence as the source. -/
abbrev sourceMerge (cmp : α → α → Bool) (xs ys : List α) : List α :=
  List.merge xs ys cmp

theorem sourceMerge_eq_List_merge (cmp : α → α → Bool) (xs ys : List α) :
    sourceMerge cmp xs ys = List.merge xs ys cmp := rfl

theorem sourceMerge_perm (cmp : α → α → Bool) (xs ys : List α) :
    (sourceMerge cmp xs ys).Perm (xs ++ ys) := List.merge_perm_append cmp

def sourceMergeBy (cmp : α → α → Bool) (xss : List (List α)) : List α :=
  xss.foldr (sourceMerge cmp) []

theorem sourceMerge_mem (cmp : α → α → Bool) (xs ys : List α) (x : α) :
    x ∈ sourceMerge cmp xs ys ↔ x ∈ xs ∨ x ∈ ys := List.mem_merge

theorem sourceMergeBy_pair (cmp : α → α → Bool) (xs ys : List α) :
    sourceMergeBy cmp [xs, ys] = sourceMerge cmp xs ys := by
  simp [sourceMergeBy, sourceMerge]

/-- Merging changes order but preserves every occurrence. -/
theorem sourceMergeBy_perm (cmp : α → α → Bool) (xss : List (List α)) :
    (sourceMergeBy cmp xss).Perm xss.flatten := by
  induction xss with
  | nil => exact .refl _
  | cons xs xss ih =>
    change (List.merge xs (sourceMergeBy cmp xss) cmp).Perm (xs ++ xss.flatten)
    exact (List.merge_perm_append cmp).trans ((List.Perm.refl xs).append ih)

/-- Source LINE275-278, with empty candidates deliberately kept separate. -/
def UpDominates : List Int → List Int → Prop
  | [], [] => True
  | _ :: _, [] => False
  | [], _ :: _ => False
  | x :: xs, y :: ys => y ≤ x ∧ ys.length ≤ xs.length

instance : DecidableRel UpDominates := fun p q =>
  match p, q with
  | [], [] => inferInstanceAs (Decidable True)
  | _ :: _, [] => inferInstanceAs (Decidable False)
  | [], _ :: _ => inferInstanceAs (Decidable False)
  | _ :: _, _ :: _ => inferInstanceAs (Decidable (_ ∧ _))

theorem upDominates_refl (p : List Int) : UpDominates p p := by
  cases p <;> simp [UpDominates]

theorem upDominates_trans (p q r : List Int) (hpq : UpDominates p q)
    (hqr : UpDominates q r) : UpDominates p r := by
  cases p <;> cases q <;> cases r <;> simp_all [UpDominates]; omega

theorem upDominates_length (p q : List Int) (h : UpDominates p q) :
    q.length ≤ p.length := by
  cases p <;> cases q <;> simp_all [UpDominates]

theorem upDominates_nil (p : List Int) : UpDominates p [] ↔ p = [] := by
  cases p <;> simp [UpDominates]

/-- The thin-map compatibility used in the printed derivation. -/
theorem upDominates_cons (x : Int) (p q : List Int) (h : UpDominates p q) :
    UpDominates (x :: p) (x :: q) :=
  ⟨Int.le_refl _, upDominates_length p q h⟩

/-- The thin-filter compatibility used in the printed derivation. -/
theorem upDominates_canPrepend (x : Int) (p q : List Int) (h : UpDominates p q)
    (hq : canPrepend x q = true) : canPrepend x p = true := by
  cases p <;> cases q <;>
    simp_all [UpDominates, canPrepend_nil, canPrepend_cons]; omega

theorem upDominates_total_equal_length (p q : List Int) (h : p.length = q.length) :
    UpDominates p q ∨ UpDominates q p := by
  cases p <;> cases q <;> simp_all [UpDominates]; omega

/-- Nonempty heads decrease from an earlier retained candidate to a later one. -/
def HeadDecreasing : List Int → List Int → Prop
  | x :: _, y :: _ => y < x
  | _, _ => True

def UpBefore (p q : List Int) : Prop := p.length < q.length ∧ HeadDecreasing p q

theorem upBefore_trans (p q r : List Int) (hpq : UpBefore p q) (hqr : UpBefore q r) :
    UpBefore p r := by
  cases p <;> cases q <;> cases r <;>
    simp_all [UpBefore, HeadDecreasing]; omega

theorem upBefore_of_incomparable (p q : List Int) (hl : p.length ≤ q.length)
    (hpq : ¬ UpDominates p q) (hqp : ¬ UpDominates q p) : UpBefore p q := by
  cases p <;> cases q <;> simp_all [UpBefore, HeadDecreasing, UpDominates]; omega

theorem upBefore_of_dominating_left (p q r : List Int) (hpq : UpDominates p q)
    (hl : p.length ≤ q.length) (hqr : UpBefore q r) : UpBefore p r := by
  cases p <;> cases q <;> cases r <;>
    simp_all [UpBefore, HeadDecreasing, UpDominates]; omega

theorem upBefore_incomparable (p q : List Int) (h : UpBefore p q) :
    ¬ UpDominates p q ∧ ¬ UpDominates q p := by
  cases p <;> cases q <;> simp_all [UpBefore, HeadDecreasing, UpDominates]

/-- On length-sorted input, the ACTUAL adjacent bump produces strict frontier order.
This proof uses its first/second guard priority, not the generic insertion algorithm. -/
theorem upThin_ordered (ps : List (List Int))
    (hs : ps.Pairwise (fun p q => p.length ≤ q.length)) :
    (thinBy UpDominates ps).Pairwise UpBefore := by
  induction ps with
  | nil => simp [thinBy]
  | cons p ps ih =>
    have hbefore := (List.pairwise_cons.mp hs).1
    have hout := ih (List.pairwise_cons.mp hs).2
    have hsub := (Optimization.Thinning.thinBy_correct UpDominates
      upDominates_refl upDominates_trans ps).1
    change (bump UpDominates p (thinBy UpDominates ps)).Pairwise UpBefore
    cases he : thinBy UpDominates ps with
    | nil => simp [bump]
    | cons q qs =>
      rw [he] at hout
      have hle : p.length ≤ q.length := hbefore q (hsub.subset (by rw [he]; simp))
      have hh := List.pairwise_cons.mp hout
      by_cases hpq : UpDominates p q
      · simp only [bump, ite_eq_left hpq]
        exact List.pairwise_cons.mpr ⟨fun r hr =>
          upBefore_of_dominating_left p q r hpq hle (hh.1 r hr), hh.2⟩
      · by_cases hqp : UpDominates q p
        · simpa only [bump, ite_eq_right hpq, ite_eq_left hqp] using hout
        · simp only [bump, ite_eq_right hpq, ite_eq_right hqp]
          have hpqb := upBefore_of_incomparable p q hle hpq hqp
          refine List.pairwise_cons.mpr ⟨?_, hout⟩
          intro r hr
          rcases List.mem_cons.mp hr with rfl | hr
          · exact hpqb
          · exact upBefore_trans p q r hpqb (hh.1 r hr)

/-- The source merge comparison is non-strict, so the first list wins a tie. -/
def lengthLE (p q : List α) : Bool := decide (p.length ≤ q.length)

/-- Literal source LINE318-320: filter/map, mergeBy, then adjacent thinBy. -/
def lusStep (x : Int) (ps : List (List Int)) : List (List Int) :=
  thinBy UpDominates (sourceMergeBy lengthLE
    [ps, (ps.filter (canPrepend x)).map (List.cons x)])

def lusStates (xs : List Int) : List (List Int) := xs.foldr lusStep [[]]

/-- Source LINE317. Nonemptiness of the reachable state makes the default unused. -/
def lus (xs : List Int) : List Int := (lusStates xs).getLastD []

theorem lusStep_eq (x : Int) (ps : List (List Int)) :
    lusStep x ps = thinBy UpDominates
      (sourceMerge lengthLE ps ((ps.filter (canPrepend x)).map (List.cons x))) := by
  rw [lusStep, sourceMergeBy_pair]

/-- The selected merge specializes the shared source recurrence by length. -/
theorem lengthMerge_source (ps qs : List (List Int)) :
    letI : LE (List Int) := ⟨fun p q => p.length ≤ q.length⟩
    letI : DecidableLE (List Int) := fun p q => inferInstanceAs (Decidable (p.length ≤ q.length))
    Applications.Sorting.sourceMerge ps qs = sourceMerge lengthLE ps qs :=
  Applications.Sorting.mergeBy_source List.length ps qs

/-- Local adjacent thinning preserves the order in the MERGED candidate list. -/
theorem lusStep_refinement (x : Int) (ps : List (List Int)) :
    IsThinning UpDominates
      (sourceMergeBy lengthLE [ps, (ps.filter (canPrepend x)).map (List.cons x)])
      (lusStep x ps) :=
  Optimization.Thinning.thinBy_correct UpDominates upDominates_refl upDominates_trans _

theorem lusStep_sublist_merge (x : Int) (ps : List (List Int)) :
    (lusStep x ps).Sublist
      (sourceMergeBy lengthLE [ps, (ps.filter (canPrepend x)).map (List.cons x)]) :=
  (lusStep_refinement x ps).1

/-- Against the unmerged generation, the required relation here is membership. -/
theorem lusStep_subset_upStep (x : Int) (ps : List (List Int)) :
    lusStep x ps ⊆ upStep x ps := by
  intro p hp
  have hm := (lusStep_sublist_merge x ps).subset hp
  rw [sourceMergeBy_pair, sourceMerge_mem] at hm
  exact List.mem_append.mpr hm

theorem lusStep_covers (x : Int) (ps : List (List Int)) :
    Covers UpDominates (lusStep x ps) (upStep x ps) := by
  intro p hp
  apply (lusStep_refinement x ps).2 p
  rw [sourceMergeBy_pair, sourceMerge_mem]
  exact List.mem_append.mp hp

theorem upStep_subset (x : Int) (ps qs : List (List Int)) (h : ps ⊆ qs) :
    upStep x ps ⊆ upStep x qs := by
  intro p hp
  simp only [upStep, List.mem_append, List.mem_map, List.mem_filter] at hp ⊢
  rcases hp with hp | ⟨q, ⟨hq, hc⟩, rfl⟩
  · exact Or.inl (h hp)
  · exact Or.inr ⟨q, ⟨h hq, hc⟩, rfl⟩

/-- Compatibility with the complete independent step follows from the two source laws. -/
theorem upStep_covers (x : Int) (ps qs : List (List Int))
    (h : Covers UpDominates ps qs) : Covers UpDominates (upStep x ps) (upStep x qs) := by
  intro p hp
  simp only [upStep, List.mem_append, List.mem_map, List.mem_filter] at hp
  rcases hp with hp | ⟨q, ⟨hq, hc⟩, rfl⟩
  · obtain ⟨r, hr, hd⟩ := h p hp
    exact ⟨r, List.mem_append_left _ hr, hd⟩
  · obtain ⟨r, hr, hd⟩ := h q hq
    refine ⟨x :: r, List.mem_append_right _ (List.mem_map.mpr
      ⟨r, List.mem_filter.mpr ⟨hr, upDominates_canPrepend x r q hd hc⟩, rfl⟩),
      upDominates_cons x r q hd⟩

theorem lusStates_subset_upStates (xs : List Int) : lusStates xs ⊆ upStates xs := by
  induction xs with
  | nil => exact fun _ h => h
  | cons x xs ih =>
    exact fun _ h => upStep_subset x (lusStates xs) (upStates xs) ih
      (lusStep_subset_upStep x (lusStates xs) h)

/-- Every independently feasible increasing sublist is covered by a retained witness. -/
theorem lusStates_covers (xs : List Int) : Covers UpDominates (lusStates xs) (upStates xs) := by
  induction xs with
  | nil => exact fun p hp => ⟨p, hp, upDominates_refl p⟩
  | cons x xs ih =>
    change Covers UpDominates (lusStep x (lusStates xs)) (upStep x (upStates xs))
    intro p hp
    obtain ⟨q, hq, hqp⟩ := upStep_covers x (lusStates xs) (upStates xs) ih p hp
    obtain ⟨r, hr, hrq⟩ := lusStep_covers x (lusStates xs) q hq
    exact ⟨r, hr, upDominates_trans r q p hrq hqp⟩

/-- Global representatives may be reordered relative to the unmerged generator. -/
theorem lusStates_refinement (xs : List Int) :
    Represents UpDominates (upStates xs) (lusStates xs) :=
  ⟨lusStates_subset_upStates xs, lusStates_covers xs⟩

theorem lusStates_feasible (xs p : List Int) (hp : p ∈ lusStates xs) :
    p.Sublist xs ∧ Increasing p :=
  (mem_upStates xs p).mp (lusStates_subset_upStates xs hp)

/-- Coverage stated without an enumerator in its assumptions. -/
theorem lusStates_covers_sublist (xs candidate : List Int)
    (hs : candidate.Sublist xs) (hi : Increasing candidate) :
    ∃ representative ∈ lusStates xs, UpDominates representative candidate :=
  lusStates_covers xs candidate ((mem_upStates xs candidate).mpr ⟨hs, hi⟩)

@[simp] theorem empty_mem_lusStates (xs : List Int) : [] ∈ lusStates xs := by
  obtain ⟨p, hp, hd⟩ := lusStates_covers xs [] (empty_mem_upStates xs)
  have he := (upDominates_nil p).mp hd
  simpa only [he] using hp

theorem lusStates_ne_nil (xs : List Int) : lusStates xs ≠ [] :=
  List.ne_nil_of_mem (empty_mem_lusStates xs)

theorem sourceMerge_length_sorted (ps qs : List (List α))
    (hp : ps.Pairwise (fun p q => p.length ≤ q.length))
    (hq : qs.Pairwise (fun p q => p.length ≤ q.length)) :
    (sourceMerge lengthLE ps qs).Pairwise (fun p q => p.length ≤ q.length) :=
  Applications.Sorting.mergeBy_sorted List.length ps qs hp hq

theorem lusStep_ordered (x : Int) (ps : List (List Int)) (hs : ps.Pairwise UpBefore) :
    (lusStep x ps).Pairwise UpBefore := by
  rw [lusStep_eq]
  apply upThin_ordered
  have hp := hs.imp (fun h => Nat.le_of_lt h.1)
  apply sourceMerge_length_sorted _ _ hp
  apply List.pairwise_map.mpr
  exact (hp.sublist List.filter_sublist).imp (fun h => Nat.succ_le_succ h)

theorem lusStates_ordered (xs : List Int) : (lusStates xs).Pairwise UpBefore := by
  induction xs with
  | nil => simp [lusStates]
  | cons x xs ih => exact lusStep_ordered x (lusStates xs) ih

theorem lusStates_lengthOrdered (xs : List Int) : LengthOrdered (lusStates xs) :=
  (lusStates_ordered xs).imp (fun h => h.1)

theorem lusStates_antichain (xs : List Int) :
    (lusStates xs).Pairwise (fun p q => ¬ UpDominates p q ∧ ¬ UpDominates q p) :=
  (lusStates_ordered xs).imp (fun h => upBefore_incomparable _ _ h)

theorem lusStates_nodup (xs : List Int) : (lusStates xs).Nodup := by
  apply (lusStates_ordered xs).imp
  intro p q h he
  exact Nat.ne_of_lt h.1 (congrArg List.length he)

end Subsequences
