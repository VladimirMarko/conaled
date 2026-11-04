import Applications.Resources.SelectionMedians
import Applications.Resources.Partition

/-! Nested median-of-medians execution for FDSA Chapter 3.

Every invocation evaluates its entry length once. The recursive branch executes
chopping and the median map, recursively selects one median, and then executes
the source partition. It evaluates the equal-bucket length only after the left
branch has failed, and recurses into at most one strict bucket.

The private valid-rank worker returns an input member. That modest invariant
justifies strict child decrease before rank correctness is proved; no balance,
growth, pivot-rank, or cost law is assumed by the construction. The supplied
entry-length observation is an actual cached length execution, including its
count. Proofs, comparisons and projections have the source's zero tariff.

The public operation uses Option without requiring an inhabited payload type.
Its invalid-rank guard reuses the entry length. The resulting n+2 invalid count
belongs to this total extension of the source's valid-rank operation.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.Selection
open Applications.Selection
open Resources.SelectionAuxiliary Resources.SelectionMedians
universe u
variable {α : Type u} [LinearOrder α]

omit [LinearOrder α] in
private theorem length_value (xs : List α) :
    (SymmetricCosts.lengthRun xs).1 = xs.length :=
  congrArg Prod.fst (SymmetricCosts.lengthRun_exact xs)

private theorem partition_value (p : α) (xs : List α) :
    (Partition.partitionRun p xs).1 = partition3 p xs :=
  Partition.partitionRun_value p xs

private theorem left_member (p : α) (xs : List α) (a : α)
    (ha : a ∈ (Partition.partitionRun p xs).1.1) : a ∈ xs := by
  rw [partition_value] at ha
  exact ((partition_left_mem p xs a).mp ha).1

private theorem right_member (p : α) (xs : List α) (a : α)
    (ha : a ∈ (Partition.partitionRun p xs).1.2.2) : a ∈ xs := by
  rw [partition_value] at ha
  exact ((partition_right_mem p xs a).mp ha).1

private theorem strict_sizes (p : α) (xs : List α) (hp : p ∈ xs) :
    (Partition.partitionRun p xs).1.1.length < xs.length ∧
      (Partition.partitionRun p xs).1.2.2.length < xs.length := by
  rw [partition_value]
  exact partition_strict_sizes p xs hp

private theorem right_rank (p : α) (xs : List α) (k : Nat)
    (hk : k < xs.length)
    (he : ¬ k < (SymmetricCosts.lengthRun (Partition.partitionRun p xs).1.1).1 +
      (SymmetricCosts.lengthRun (Partition.partitionRun p xs).1.2.1).1) :
    k - (SymmetricCosts.lengthRun (Partition.partitionRun p xs).1.1).1 -
        (SymmetricCosts.lengthRun (Partition.partitionRun p xs).1.2.1).1 <
      (SymmetricCosts.lengthRun (Partition.partitionRun p xs).1.2.2).1 := by
  simp only [length_value, partition_value] at he ⊢
  have h := partition_lengths p xs
  omega

private theorem medians_positive (d : Nat) (xs : List α)
    (hd : 2 ≤ d) (hx : 0 < xs.length) :
    0 < (chunkMediansRun d xs).1.length := by
  apply List.length_pos_iff.mpr
  intro h
  rcases (chunkMediansRun_eq_nil_iff d xs).mp h with h | h
  · omega
  · subst xs
    simp only [List.length_nil] at hx
    omega

private theorem medians_shorter (d : Nat) (xs : List α)
    (hd : 2 ≤ d) (hx : 1 < xs.length) :
    (chunkMediansRun d xs).1.length < xs.length := by
  rw [chunkMediansRun_length]
  have hc : xs.length ⌈/⌉ d ≤ xs.length - 1 := by
    apply (ceilDiv_le_iff_le_mul (by omega : 0 < d)).mpr
    calc
      xs.length ≤ 2 * (xs.length - 1) := by omega
      _ ≤ d * (xs.length - 1) := Nat.mul_le_mul_right _ hd
  omega

private theorem median_rank (d : Nat) (xs : List α)
    (hd : 2 ≤ d) (hx : 0 < xs.length) :
    ((xs.length ⌈/⌉ d) - 1) / 2 <
      (SymmetricCosts.lengthRun (chunkMediansRun d xs).1).1 := by
  have hp := medians_positive d xs hd hx
  rw [chunkMediansRun_length] at hp
  rw [length_value, chunkMediansRun_length]
  omega

/-- The cached observation contributes its actual cost at this invocation.
The result carries membership solely to support noncircular termination. -/
private def selectWorker (d cutoff : Nat) (hd : 2 ≤ d) (hc : 1 ≤ cutoff)
    (k : Nat) (xs : List α) (nr : Measured Nat Nat)
    (hn : nr = SymmetricCosts.lengthRun xs) (hk : k < nr.1) :
    Measured {a // a ∈ xs} Nat :=
  have hlen : nr.1 = xs.length := by rw [hn, SymmetricCosts.lengthRun_exact]
  if hsmall : nr.1 ≤ cutoff then
    let r := slowSelectRun k xs
    match h : r.1 with
    | none => False.elim (by
        have hi := (slowSelectRun_none k xs).mp h
        omega)
    | some a =>
        (⟨a, ((slowSelectRun_some_iff k xs a).mp h).mem⟩, 1 + nr.2 + r.2)
  else
    let med := chunkMediansRun d xs
    let i := ((nr.1 ⌈/⌉ d) - 1) / 2
    let pivot := selectWorker d cutoff hd hc i med.1
      (SymmetricCosts.lengthRun med.1) rfl (by
        dsimp only [i, med]
        rw [hlen]
        exact median_rank d xs hd (by omega))
    let p := pivot.1.val
    have hp : p ∈ xs := chunkMediansRun_mem d xs p pivot.1.property
    let parts := Partition.partitionRun p xs
    let lower := SymmetricCosts.lengthRun parts.1.1
    let common := 1 + nr.2 + med.2 + pivot.2 + parts.2 + lower.2
    if hl : k < lower.1 then
      let child := selectWorker d cutoff hd hc k parts.1.1
        (SymmetricCosts.lengthRun parts.1.1) rfl hl
      (⟨child.1.val, left_member p xs child.1.val child.1.property⟩, common + child.2)
    else
      let equal := SymmetricCosts.lengthRun parts.1.2.1
      if he : k < lower.1 + equal.1 then
        (⟨p, hp⟩, common + equal.2)
      else
        let child := selectWorker d cutoff hd hc (k - lower.1 - equal.1) parts.1.2.2
          (SymmetricCosts.lengthRun parts.1.2.2) rfl
          (right_rank p xs k (by omega) he)
        (⟨child.1.val, right_member p xs child.1.val child.1.property⟩,
          common + equal.2 + child.2)
termination_by xs.length
decreasing_by
  · exact medians_shorter d xs hd (by omega)
  · exact (strict_sizes p xs hp).1
  · exact (strict_sizes p xs hp).2

omit [LinearOrder α] in
private def observe {xs : List α} (r : Measured {a // a ∈ xs} Nat) :
    Measured (Option α) Nat := (some r.1.val, r.2)

/-- Execute the nested selector for a group size and a finite base cutoff.
The constraints ensure termination; a linear bound additionally requires a
contracting grouping regime and a separately proved source-cost comparison. -/
def selectRunWith (groupSize cutoff : Nat) (hd : 2 ≤ groupSize) (hc : 1 ≤ cutoff)
    (k : Nat) (xs : List α) : Measured (Option α) Nat :=
  let nr := SymmetricCosts.lengthRun xs
  if hk : k < nr.1 then
    observe (selectWorker groupSize cutoff hd hc k xs nr rfl hk)
  else (none, 1 + nr.2)

/-- The book uses groups of five and insertion selection through size twenty. -/
def selectRun (k : Nat) (xs : List α) : Measured (Option α) Nat :=
  selectRunWith 5 20 (by decide) (by decide) k xs

private theorem worker_observe (d cutoff : Nat) (hd : 2 ≤ d) (hc : 1 ≤ cutoff)
    (k : Nat) (xs : List α) (nr : Measured Nat Nat)
    (hn : nr = SymmetricCosts.lengthRun xs) (hk : k < nr.1) :
    selectRunWith d cutoff hd hc k xs = observe (selectWorker d cutoff hd hc k xs nr hn hk) := by
  subst nr
  unfold selectRunWith
  dsimp only
  rw [dif_pos hk]

/-- The optional extension stops after its entry and the one cached length. -/
theorem selectRunWith_of_invalid (d cutoff : Nat) (hd : 2 ≤ d) (hc : 1 ≤ cutoff)
    (k : Nat) (xs : List α) (hk : xs.length ≤ k) :
    selectRunWith d cutoff hd hc k xs = (none, xs.length + 2) := by
  unfold selectRunWith
  dsimp only
  rw [dif_neg (by simpa only [length_value] using Nat.not_lt.mpr hk)]
  rw [SymmetricCosts.lengthRun_exact]
  exact Prod.ext rfl (by omega)

theorem selectRunWith_nil (d cutoff : Nat) (hd : 2 ≤ d) (hc : 1 ≤ cutoff) (k : Nat) :
    selectRunWith d cutoff hd hc k ([] : List α) = (none, 2) :=
  selectRunWith_of_invalid d cutoff hd hc k [] (Nat.zero_le k)

/-- Validity is established before any rank-correctness induction. -/
theorem selectRunWith_exists (d cutoff : Nat) (hd : 2 ≤ d) (hc : 1 ≤ cutoff)
    (k : Nat) (xs : List α) (hk : k < xs.length) :
    ∃ a, (selectRunWith d cutoff hd hc k xs).1 = some a := by
  have hi : k < (SymmetricCosts.lengthRun xs).1 := by rw [length_value]; exact hk
  rw [worker_observe d cutoff hd hc k xs (SymmetricCosts.lengthRun xs) rfl hi]
  exact ⟨_, rfl⟩

/-- Every returned payload is a member, independently of its eventual rank law. -/
theorem selectRunWith_mem (d cutoff : Nat) (hd : 2 ≤ d) (hc : 1 ≤ cutoff)
    (k : Nat) (xs : List α) (a : α)
    (ha : (selectRunWith d cutoff hd hc k xs).1 = some a) : a ∈ xs := by
  by_cases hk : k < xs.length
  · have hi : k < (SymmetricCosts.lengthRun xs).1 := by rw [length_value]; exact hk
    rw [worker_observe d cutoff hd hc k xs (SymmetricCosts.lengthRun xs) rfl hi] at ha
    have he : (selectWorker d cutoff hd hc k xs (SymmetricCosts.lengthRun xs) rfl hi).1.val =
        a := Option.some.inj ha
    exact he ▸ (selectWorker d cutoff hd hc k xs (SymmetricCosts.lengthRun xs) rfl hi).1.property
  · rw [selectRunWith_of_invalid d cutoff hd hc k xs (Nat.le_of_not_gt hk)] at ha
    cases ha

/-- The base branch executes the actual insertion/lookup helper. -/
theorem selectRunWith_small (d cutoff : Nat) (hd : 2 ≤ d) (hc : 1 ≤ cutoff)
    (k : Nat) (xs : List α) (hk : k < xs.length) (hs : xs.length ≤ cutoff) :
    selectRunWith d cutoff hd hc k xs =
      ((slowSelectRun k xs).1,
        1 + (SymmetricCosts.lengthRun xs).2 + (slowSelectRun k xs).2) := by
  have hi : k < (SymmetricCosts.lengthRun xs).1 := by rw [length_value]; exact hk
  rw [worker_observe d cutoff hd hc k xs (SymmetricCosts.lengthRun xs) rfl hi]
  rw [selectWorker]
  dsimp only
  rw [dif_pos (by simpa only [length_value] using hs)]
  dsimp only
  split
  next h =>
    have hbad := (slowSelectRun_none k xs).mp h
    omega
  next a ha =>
    exact Prod.ext ha.symm rfl

/-- The full recursive source equation uses the value returned by its own
median recursion. The premise identifies that observed value; it assumes
neither its rank, its cost, nor a bound on either strict bucket. -/
theorem selectRunWith_step (d cutoff : Nat) (hd : 2 ≤ d) (hc : 1 ≤ cutoff)
    (k : Nat) (xs : List α) (hk : k < xs.length) (hs : cutoff < xs.length)
    (p : α)
    (hp : (selectRunWith d cutoff hd hc (((xs.length ⌈/⌉ d) - 1) / 2)
      (chunkMediansRun d xs).1).1 = some p) :
    selectRunWith d cutoff hd hc k xs =
      let t := partition3 p xs
      let pivot := selectRunWith d cutoff hd hc (((xs.length ⌈/⌉ d) - 1) / 2)
        (chunkMediansRun d xs).1
      let common := 1 + (SymmetricCosts.lengthRun xs).2 + (chunkMediansRun d xs).2 +
        pivot.2 + (Partition.partitionRun p xs).2 + (SymmetricCosts.lengthRun t.1).2
      if k < t.1.length then
        let child := selectRunWith d cutoff hd hc k t.1
        (child.1, common + child.2)
      else if k < t.1.length + t.2.1.length then
        (some p, common + (SymmetricCosts.lengthRun t.2.1).2)
      else
        let child := selectRunWith d cutoff hd hc (k - t.1.length - t.2.1.length) t.2.2
        (child.1, common + (SymmetricCosts.lengthRun t.2.1).2 + child.2) := by
  have hm := median_rank d xs hd (by omega)
  let pr := selectWorker d cutoff hd hc (((xs.length ⌈/⌉ d) - 1) / 2)
    (chunkMediansRun d xs).1 (SymmetricCosts.lengthRun (chunkMediansRun d xs).1) rfl hm
  have hpr : selectRunWith d cutoff hd hc (((xs.length ⌈/⌉ d) - 1) / 2)
      (chunkMediansRun d xs).1 = observe pr :=
    worker_observe d cutoff hd hc _ _ _ rfl hm
  have hpv : pr.1.val = p :=
    Option.some.inj ((congrArg Prod.fst hpr).symm.trans hp)
  subst p
  have hi : k < (SymmetricCosts.lengthRun xs).1 := by rw [length_value]; exact hk
  rw [worker_observe d cutoff hd hc k xs (SymmetricCosts.lengthRun xs) rfl hi]
  rw [selectWorker]
  dsimp only
  rw [dif_neg (by simpa only [length_value] using Nat.not_le.mpr hs)]
  dsimp only
  by_cases hl : k < (partition3 pr.1.val xs).1.length
  · have hj : k < (SymmetricCosts.lengthRun (partition3 pr.1.val xs).1).1 := by
      rw [length_value]
      exact hl
    have child_eq := worker_observe d cutoff hd hc k (partition3 pr.1.val xs).1
      (SymmetricCosts.lengthRun (partition3 pr.1.val xs).1) rfl hj
    simp only [length_value, partition_value, hl, ↓reduceDIte, ↓reduceIte,
      hpr, child_eq, observe]
  · by_cases he : k < (partition3 pr.1.val xs).1.length +
        (partition3 pr.1.val xs).2.1.length
    · simp only [length_value, partition_value, hl, he, ↓reduceDIte, ↓reduceIte,
        hpr, observe]
    · have hj : k - (partition3 pr.1.val xs).1.length -
          (partition3 pr.1.val xs).2.1.length <
          (SymmetricCosts.lengthRun (partition3 pr.1.val xs).2.2).1 := by
        rw [length_value]
        have hsum := partition_lengths pr.1.val xs
        omega
      have child_eq := worker_observe d cutoff hd hc
        (k - (partition3 pr.1.val xs).1.length - (partition3 pr.1.val xs).2.1.length)
        (partition3 pr.1.val xs).2.2
        (SymmetricCosts.lengthRun (partition3 pr.1.val xs).2.2) rfl hj
      simp only [length_value, partition_value, hl, he, ↓reduceDIte, ↓reduceIte,
        hpr, child_eq, observe]

/-- Project the count from the proved execution equation. In particular, the
equal-length traversal is absent from the left branch, and the equal branch
has no second recursive selection call. -/
theorem selectRunWith_cost_step (d cutoff : Nat) (hd : 2 ≤ d) (hc : 1 ≤ cutoff)
    (k : Nat) (xs : List α) (hk : k < xs.length) (hs : cutoff < xs.length)
    (p : α)
    (hp : (selectRunWith d cutoff hd hc (((xs.length ⌈/⌉ d) - 1) / 2)
      (chunkMediansRun d xs).1).1 = some p) :
    (selectRunWith d cutoff hd hc k xs).2 =
      let t := partition3 p xs
      1 + (SymmetricCosts.lengthRun xs).2 + (chunkMediansRun d xs).2 +
        (selectRunWith d cutoff hd hc (((xs.length ⌈/⌉ d) - 1) / 2)
          (chunkMediansRun d xs).1).2 + (Partition.partitionRun p xs).2 +
        (SymmetricCosts.lengthRun t.1).2 +
        (if k < t.1.length then (selectRunWith d cutoff hd hc k t.1).2
        else (SymmetricCosts.lengthRun t.2.1).2 +
          if k < t.1.length + t.2.1.length then 0
          else (selectRunWith d cutoff hd hc (k - t.1.length - t.2.1.length) t.2.2).2) := by
  have h := congrArg Prod.snd (selectRunWith_step d cutoff hd hc k xs hk hs p hp)
  dsimp only at h ⊢
  by_cases hl : k < (partition3 p xs).1.length
  · simpa only [hl, ↓reduceIte] using h
  · by_cases he : k < (partition3 p xs).1.length + (partition3 p xs).2.1.length
    · simpa only [hl, he, ↓reduceIte, Nat.add_zero] using h
    · simpa only [hl, he, ↓reduceIte, Nat.add_assoc] using h

/-- Every grouping/cutoff in the terminating parameter range returns the
requested occurrence, including arbitrary duplicates and invalid ranks. -/
theorem selectRunWith_value (d cutoff : Nat) (hd : 2 ≤ d) (hc : 1 ≤ cutoff)
    (k : Nat) (xs : List α) :
    (selectRunWith d cutoff hd hc k xs).1 = (ordered xs)[k]? := by
  by_cases hk : k < xs.length
  · by_cases hs : xs.length ≤ cutoff
    · rw [selectRunWith_small d cutoff hd hc k xs hk hs]
      exact slowSelectRun_value k xs
    · have hi : ((xs.length ⌈/⌉ d) - 1) / 2 < (chunkMediansRun d xs).1.length := by
        simpa only [length_value] using median_rank d xs hd (by omega)
      obtain ⟨p, hp⟩ := selectRunWith_exists d cutoff hd hc _ _ hi
      have hp_mem : p ∈ xs := chunkMediansRun_mem d xs p
        (selectRunWith_mem d cutoff hd hc _ _ p hp)
      rw [selectRunWith_step d cutoff hd hc k xs hk (Nat.lt_of_not_ge hs) p hp,
        ordered_getElem?_partition p xs k]
      dsimp only
      by_cases hl : k < (partition3 p xs).1.length
      · simp only [hl, ↓reduceIte]
        exact selectRunWith_value d cutoff hd hc k (partition3 p xs).1
      · by_cases he : k < (partition3 p xs).1.length + (partition3 p xs).2.1.length
        · simp only [hl, he, ↓reduceIte]
        · simp only [hl, he, ↓reduceIte]
          exact selectRunWith_value d cutoff hd hc
            (k - (partition3 p xs).1.length - (partition3 p xs).2.1.length)
            (partition3 p xs).2.2
  · rw [selectRunWith_of_invalid d cutoff hd hc k xs (Nat.le_of_not_gt hk)]
    symm
    apply List.getElem?_eq_none_iff.mpr
    simpa only [(ordered_perm xs).length_eq] using Nat.le_of_not_gt hk
termination_by xs.length
decreasing_by
  · exact (partition_strict_sizes p xs hp_mem).1
  · exact (partition_strict_sizes p xs hp_mem).2

theorem selectRunWith_some_iff (d cutoff : Nat) (hd : 2 ≤ d) (hc : 1 ≤ cutoff)
    (k : Nat) (xs : List α) (a : α) :
    (selectRunWith d cutoff hd hc k xs).1 = some a ↔ RankedAt xs k a := by
  rw [selectRunWith_value, ← ranked_iff_index]

theorem selectRunWith_none_iff (d cutoff : Nat) (hd : 2 ≤ d) (hc : 1 ≤ cutoff)
    (k : Nat) (xs : List α) :
    (selectRunWith d cutoff hd hc k xs).1 = none ↔ xs.length ≤ k := by
  rw [selectRunWith_value, List.getElem?_eq_none_iff, (ordered_perm xs).length_eq]

/-- Preserve the repository's one-based public selection interface. -/
theorem selectRunWith_public (d cutoff : Nat) (hd : 2 ≤ d) (hc : 1 ≤ cutoff)
    (k : Nat) (xs : List α) :
    (selectRunWith d cutoff hd hc k xs).1 = sortSelect (k + 1) xs := by
  rw [selectRunWith_value]
  simp [sortSelect]

theorem selectRun_value (k : Nat) (xs : List α) :
    (selectRun k xs).1 = (ordered xs)[k]? :=
  selectRunWith_value 5 20 (by decide) (by decide) k xs

theorem selectRun_some_iff (k : Nat) (xs : List α) (a : α) :
    (selectRun k xs).1 = some a ↔ RankedAt xs k a :=
  selectRunWith_some_iff 5 20 (by decide) (by decide) k xs a

theorem selectRun_none_iff (k : Nat) (xs : List α) :
    (selectRun k xs).1 = none ↔ xs.length ≤ k :=
  selectRunWith_none_iff 5 20 (by decide) (by decide) k xs

theorem selectRun_of_invalid (k : Nat) (xs : List α) (hk : xs.length ≤ k) :
    selectRun k xs = (none, xs.length + 2) :=
  selectRunWith_of_invalid 5 20 (by decide) (by decide) k xs hk

theorem selectRun_nil (k : Nat) : selectRun k ([] : List α) = (none, 2) :=
  selectRunWith_nil 5 20 (by decide) (by decide) k

theorem selectRun_small (k : Nat) (xs : List α) (hk : k < xs.length)
    (hs : xs.length ≤ 20) :
    selectRun k xs = ((slowSelectRun k xs).1,
      1 + (SymmetricCosts.lengthRun xs).2 + (slowSelectRun k xs).2) :=
  selectRunWith_small 5 20 (by decide) (by decide) k xs hk hs

theorem selectRun_step (k : Nat) (xs : List α) (hk : k < xs.length)
    (hs : 20 < xs.length) (p : α)
    (hp : (selectRun (((xs.length ⌈/⌉ 5) - 1) / 2) (chunkMediansRun 5 xs).1).1 = some p) :
    selectRun k xs =
      let t := partition3 p xs
      let pivot := selectRun (((xs.length ⌈/⌉ 5) - 1) / 2) (chunkMediansRun 5 xs).1
      let common := 1 + (SymmetricCosts.lengthRun xs).2 + (chunkMediansRun 5 xs).2 +
        pivot.2 + (Partition.partitionRun p xs).2 + (SymmetricCosts.lengthRun t.1).2
      if k < t.1.length then
        let child := selectRun k t.1
        (child.1, common + child.2)
      else if k < t.1.length + t.2.1.length then
        (some p, common + (SymmetricCosts.lengthRun t.2.1).2)
      else
        let child := selectRun (k - t.1.length - t.2.1.length) t.2.2
        (child.1, common + (SymmetricCosts.lengthRun t.2.1).2 + child.2) :=
  selectRunWith_step 5 20 (by decide) (by decide) k xs hk hs p hp

theorem selectRun_cost_step (k : Nat) (xs : List α) (hk : k < xs.length)
    (hs : 20 < xs.length) (p : α)
    (hp : (selectRun (((xs.length ⌈/⌉ 5) - 1) / 2) (chunkMediansRun 5 xs).1).1 = some p) :
    (selectRun k xs).2 =
      let t := partition3 p xs
      1 + (SymmetricCosts.lengthRun xs).2 + (chunkMediansRun 5 xs).2 +
        (selectRun (((xs.length ⌈/⌉ 5) - 1) / 2) (chunkMediansRun 5 xs).1).2 +
        (Partition.partitionRun p xs).2 + (SymmetricCosts.lengthRun t.1).2 +
        (if k < t.1.length then (selectRun k t.1).2
        else (SymmetricCosts.lengthRun t.2.1).2 +
          if k < t.1.length + t.2.1.length then 0
          else (selectRun (k - t.1.length - t.2.1.length) t.2.2).2) :=
  selectRunWith_cost_step 5 20 (by decide) (by decide) k xs hk hs p hp

end Resources.Selection
