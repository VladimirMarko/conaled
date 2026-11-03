import Applications.Search.OrderedTree.Basic

/-!
# Candidate search and aborting insertion

The candidate is the latest node for which the query was not smaller. Its
strict lower bound on the remaining subtree explains why it can replace all
earlier candidates. Only a final equality is needed. The bounds count actual
element comparisons, not node visits.

`none` in insertion is a propagated duplicate abort. Mapping constructors over
the optional result rebuilds ancestors only after success. The one outer
handler returns the original tree. Physical zero allocation is a separate
contract for the cell-graph realization, not a consequence of value equality.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Search.OrderedTree
universe u
variable {α : Type u} [LinearOrder α]

def LowerBound : Option α → BinaryTree α → Prop
  | none, _ => True
  | some c, t => All (fun y => c < y) t

theorem LowerBound.left {c : Option α} {y : α} {l r : BinaryTree α}
    (h : LowerBound c (.node y l r)) : LowerBound c l := by
  cases c with
  | none => trivial
  | some c => exact h.2.1

theorem LowerBound.right {c : Option α} {y : α} {l r : BinaryTree α}
    (h : LowerBound c (.node y l r)) : LowerBound c r := by
  cases c with
  | none => trivial
  | some c => exact h.2.2

/-- One `<` comparison per nonempty node; a present final candidate adds one
equality comparison. A missing candidate needs no element comparison. -/
def memberCandidateRun (x : α) (candidate : Option α) :
    BinaryTree α → Resources.Measured Bool Nat
  | .nil => match candidate with
      | none => (false, 0)
      | some c => (decide (x = c), 1)
  | .node y l r =>
      if x < y then
        let q := memberCandidateRun x candidate l
        (q.1, q.2 + 1)
      else
        let q := memberCandidateRun x (some y) r
        (q.1, q.2 + 1)

def memberCandidate (x : α) (t : BinaryTree α) : Bool :=
  (memberCandidateRun x none t).1

theorem memberCandidateRun_correct {t : BinaryTree α} {candidate : Option α}
    (ordered : Ordered t) (lower : LowerBound candidate t) (x : α) :
    (memberCandidateRun x candidate t).1 = true ↔
      Contains x t ∨ candidate = some x := by
  induction t generalizing candidate with
  | nil => cases candidate <;> simp [memberCandidateRun, Contains, eq_comm]
  | node y l r hl hr =>
      by_cases xy : x < y
      · rw [memberCandidateRun, ite_eq_left xy]
        exact (hl ordered.1 lower.left).trans
          (or_congr (contains_left_iff ordered xy).symm Iff.rfl)
      · have old : candidate ≠ some x := by
          intro eq
          subst candidate
          exact xy lower.1
        have noleft : ¬ Contains x l := fun h => xy (ordered.2.2.1.of_contains h)
        rw [memberCandidateRun, ite_eq_right xy]
        have next := hr ordered.2.1 (show LowerBound (some y) r from ordered.2.2.2)
        simpa only [Contains, noleft, false_or, old, or_false, Option.some.injEq,
          or_comm, eq_comm] using next

theorem memberCandidate_correct {t : BinaryTree α} (ordered : Ordered t) (x : α) :
    memberCandidate x t = true ↔ Contains x t := by
  simpa [memberCandidate] using
    memberCandidateRun_correct ordered (show LowerBound none t from trivial) x

theorem memberCandidateRun_bound (x : α) (candidate : Option α) (t : BinaryTree α) :
    (memberCandidateRun x candidate t).2 ≤ t.height + 1 := by
  induction t generalizing candidate with
  | nil => cases candidate <;> simp [memberCandidateRun]
  | node y l r hl hr =>
      by_cases xy : x < y
      · rw [memberCandidateRun, ite_eq_left xy]
        have bound := hl candidate
        have le : l.height ≤ max l.height r.height := Nat.le_max_left _ _
        simp only [BinaryTree.height]
        omega
      · rw [memberCandidateRun, ite_eq_right xy]
        have bound := hr (some y)
        have le : r.height ≤ max l.height r.height := Nat.le_max_right _ _
        simp only [BinaryTree.height]
        omega

/-- Exercise2.3's duplicate exception as an optional result. Each ancestor
propagates `none` rather than handling it. -/
def insertAbortRun (x : α) : BinaryTree α → Resources.Measured (Option (BinaryTree α)) Nat
  | .nil => (some (.node x .nil .nil), 0)
  | .node y l r =>
      if x < y then
        let q := insertAbortRun x l
        (q.1.map (fun l' => .node y l' r), q.2 + 1)
      else if y < x then
        let q := insertAbortRun x r
        (q.1.map (fun r' => .node y l r'), q.2 + 2)
      else (none, 2)

/-- The single duplicate-abort handler. -/
def insertAbort (x : α) (t : BinaryTree α) : BinaryTree α :=
  (insertAbortRun x t).1.getD t

theorem insertAbortRun_isNone (x : α) (t : BinaryTree α) :
    (insertAbortRun x t).1.isNone = member x t := by
  induction t with
  | nil => rfl
  | node y l r hl hr =>
      by_cases xy : x < y
      · simpa only [insertAbortRun, member, memberRun, ite_eq_left xy, Option.isNone_map]
          using hl
      · by_cases yx : y < x
        · simpa only [insertAbortRun, member, memberRun, ite_eq_right xy, ite_eq_left yx,
            Option.isNone_map] using hr
        · simp [insertAbortRun, member, memberRun, xy, yx]

theorem insertAbortRun_none_iff (x : α) (t : BinaryTree α) :
    (insertAbortRun x t).1 = none ↔ member x t = true := by
  have h := insertAbortRun_isNone x t
  constructor
  · intro result
    rw [result] at h
    exact h.symm
  · intro present
    rw [present] at h
    cases result : (insertAbortRun x t).1 with
    | none => rfl
    | some v => simp [result] at h

theorem insertAbortRun_success {x : α} {t out : BinaryTree α}
    (success : (insertAbortRun x t).1 = some out) : out = insert x t := by
  induction t generalizing out with
  | nil => simpa [insertAbortRun, insert] using success.symm
  | node y l r hl hr =>
      by_cases xy : x < y
      · simp only [insertAbortRun, ite_eq_left xy] at success
        obtain ⟨q, hq, eq⟩ := Option.map_eq_some_iff.mp success
        rw [← eq, insert, ite_eq_left xy, hl hq]
      · by_cases yx : y < x
        · simp only [insertAbortRun, ite_eq_right xy, ite_eq_left yx] at success
          obtain ⟨q, hq, eq⟩ := Option.map_eq_some_iff.mp success
          rw [← eq, insert, ite_eq_right xy, ite_eq_left yx, hr hq]
        · simp [insertAbortRun, xy, yx] at success

theorem insert_of_member {x : α} {t : BinaryTree α}
    (present : member x t = true) : insert x t = t := by
  induction t with
  | nil => simp [member, memberRun] at present
  | node y l r hl hr =>
      by_cases xy : x < y
      · have found : member x l = true := by
          simpa only [member, memberRun, ite_eq_left xy] using present
        rw [insert, ite_eq_left xy, hl found]
      · by_cases yx : y < x
        · have found : member x r = true := by
            simpa only [member, memberRun, ite_eq_right xy, ite_eq_left yx] using present
          rw [insert, ite_eq_right xy, ite_eq_left yx, hr found]
        · simp only [insert, ite_eq_right xy, ite_eq_right yx]

theorem insertAbort_eq_insert (x : α) (t : BinaryTree α) :
    insertAbort x t = insert x t := by
  cases result : (insertAbortRun x t).1 with
  | none =>
      simpa only [insertAbort, result, Option.getD_none] using
        (insert_of_member ((insertAbortRun_none_iff x t).mp result)).symm
  | some out =>
      simpa only [insertAbort, result, Option.getD_some] using
        insertAbortRun_success result

theorem insertAbortRun_comparisons (x : α) (t : BinaryTree α) :
    (insertAbortRun x t).2 = (memberRun x t).2 := by
  induction t with
  | nil => rfl
  | node y l r hl hr =>
      by_cases xy : x < y
      · simp [insertAbortRun, memberRun, xy, hl]
      · by_cases yx : y < x <;> simp [insertAbortRun, memberRun, xy, yx, hr]

/-- The combined candidate-search and duplicate-abort traversal. Equality is
tested only at an empty node. Constructors are mapped over successful returns,
so an abort propagates through every ancestor without a handler there. -/
def insertCandidateRun (x : α) (candidate : Option α) :
    BinaryTree α → Resources.Measured (Option (BinaryTree α)) Nat
  | .nil => match candidate with
      | none => (some (.node x .nil .nil), 0)
      | some c => (if x = c then none else some (.node x .nil .nil), 1)
  | .node y l r =>
      if x < y then
        let q := insertCandidateRun x candidate l
        (q.1.map (fun l' => .node y l' r), q.2 + 1)
      else
        let q := insertCandidateRun x (some y) r
        (q.1.map (fun r' => .node y l r'), q.2 + 1)

/-- One outer handler for the combined traversal. -/
def insertCandidate (x : α) (t : BinaryTree α) : BinaryTree α :=
  (insertCandidateRun x none t).1.getD t

theorem insertCandidateRun_isNone (x : α) (candidate : Option α) (t : BinaryTree α) :
    (insertCandidateRun x candidate t).1.isNone = (memberCandidateRun x candidate t).1 := by
  induction t generalizing candidate with
  | nil =>
      cases candidate with
      | none => rfl
      | some c => by_cases eq : x = c <;> simp [insertCandidateRun, memberCandidateRun, eq]
  | node y l r hl hr =>
      by_cases xy : x < y
      · simpa only [insertCandidateRun, memberCandidateRun, ite_eq_left xy, Option.isNone_map]
          using hl candidate
      · simpa only [insertCandidateRun, memberCandidateRun, ite_eq_right xy, Option.isNone_map]
          using hr (some y)

theorem insertCandidateRun_none_iff {t : BinaryTree α} {candidate : Option α}
    (ordered : Ordered t) (lower : LowerBound candidate t) (x : α) :
    (insertCandidateRun x candidate t).1 = none ↔ Contains x t ∨ candidate = some x := by
  have h := insertCandidateRun_isNone x candidate t
  have correct := memberCandidateRun_correct ordered lower x
  constructor
  · intro result
    rw [result] at h
    exact correct.mp h.symm
  · intro present
    have found := correct.mpr present
    rw [found] at h
    cases result : (insertCandidateRun x candidate t).1 with
    | none => rfl
    | some v => simp [result] at h

theorem insertCandidateRun_success {x : α} {t out : BinaryTree α}
    {candidate : Option α} (ordered : Ordered t) (lower : LowerBound candidate t)
    (success : (insertCandidateRun x candidate t).1 = some out) :
    out = insert x t := by
  induction t generalizing candidate out with
  | nil =>
      cases candidate with
      | none => simpa [insertCandidateRun, insert] using success.symm
      | some c =>
          by_cases eq : x = c
          · simp [insertCandidateRun, eq] at success
          · simpa [insertCandidateRun, eq, insert] using success.symm
  | node y l r hl hr =>
      by_cases xy : x < y
      · simp only [insertCandidateRun, ite_eq_left xy] at success
        obtain ⟨q, hq, eq⟩ := Option.map_eq_some_iff.mp success
        rw [← eq, insert, ite_eq_left xy, hl ordered.1 lower.left hq]
      · simp only [insertCandidateRun, ite_eq_right xy] at success
        obtain ⟨q, hq, eq⟩ := Option.map_eq_some_iff.mp success
        have nextLower : LowerBound (some y) r := ordered.2.2.2
        by_cases yx : y < x
        · rw [← eq, insert, ite_eq_right xy, ite_eq_left yx,
            hr ordered.2.1 nextLower hq]
        · have equal : x = y := le_antisymm (le_of_not_gt yx) (le_of_not_gt xy)
          have abort := (insertCandidateRun_none_iff ordered.2.1 nextLower x).mpr
            (Or.inr (congrArg some equal.symm))
          rw [abort] at hq
          contradiction

theorem insertCandidate_eq_insert {t : BinaryTree α} (ordered : Ordered t) (x : α) :
    insertCandidate x t = insert x t := by
  have lower : LowerBound none t := trivial
  cases result : (insertCandidateRun x none t).1 with
  | none =>
      have present : Contains x t := by
        simpa using (insertCandidateRun_none_iff ordered lower x).mp result
      have unchanged := insert_of_member ((member_correct ordered x).mpr present)
      simpa only [insertCandidate, result, Option.getD_none] using unchanged.symm
  | some out =>
      simpa only [insertCandidate, result, Option.getD_some] using
        insertCandidateRun_success ordered lower result

theorem insertCandidateRun_comparisons (x : α) (candidate : Option α) (t : BinaryTree α) :
    (insertCandidateRun x candidate t).2 = (memberCandidateRun x candidate t).2 := by
  induction t generalizing candidate with
  | nil => cases candidate <;> rfl
  | node y l r hl hr =>
      by_cases xy : x < y
      · simp [insertCandidateRun, memberCandidateRun, xy, hl]
      · simp [insertCandidateRun, memberCandidateRun, xy, hr]

theorem insertCandidateRun_bound (x : α) (candidate : Option α) (t : BinaryTree α) :
    (insertCandidateRun x candidate t).2 ≤ t.height + 1 := by
  rw [insertCandidateRun_comparisons]
  exact memberCandidateRun_bound x candidate t

/-- The combined algorithm's semantic and comparison conclusions hold together
for the same traversal. Allocation is intentionally not inferred here. -/
theorem insertCandidate_correct {t : BinaryTree α} (ordered : Ordered t) (x : α) :
    Ordered (insertCandidate x t) ∧
      (∀ z, Contains z (insertCandidate x t) ↔ z = x ∨ Contains z t) ∧
      (insertCandidateRun x none t).2 ≤ t.height + 1 := by
  rw [insertCandidate_eq_insert ordered x]
  exact ⟨ordered_insert ordered x, fun z => contains_insert x z t,
    insertCandidateRun_bound x none t⟩

end Search.OrderedTree
