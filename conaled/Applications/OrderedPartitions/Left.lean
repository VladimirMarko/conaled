import SquareKit.ListFusion

/-! Ordered contiguous partitions and exact suffix-closed left pruning.
The independent contract retains input order, occurrences and nonempty blocks. -/
set_option autoImplicit false
set_option warningAsError true
namespace OrderedPartitions
universe u
variable {α : Type u}

abbrev Partition (α : Type u) := List (List α)

def NonemptyBlocks (p : Partition α) : Prop :=
  ∀ block ∈ p, block ≠ []

def IsPartition (xs : List α) (p : Partition α) : Prop :=
  p.flatten = xs ∧ NonemptyBlocks p

def consBlock (x : α) (p : Partition α) : Partition α := [x] :: p

/-- The unused empty case totalizes the source's partial `glue`. -/
def glueLeft (x : α) : Partition α → Partition α
  | [] => [[x]]
  | block :: rest => (x :: block) :: rest

def extendLeft (x : α) : Partition α → List (Partition α)
  | [] => [consBlock x []]
  | block :: rest => [consBlock x (block :: rest), glueLeft x (block :: rest)]

def stepLeft (x : α) (ps : List (Partition α)) : List (Partition α) :=
  ps.flatMap (extendLeft x)

def partsLeft (xs : List α) : List (Partition α) :=
  xs.foldr stepLeft [[]]

@[simp] theorem partsLeft_nil : partsLeft ([] : List α) = [[]] := rfl

@[simp] theorem partsLeft_cons (x : α) (xs : List α) :
    partsLeft (x :: xs) = stepLeft x (partsLeft xs) := rfl

@[simp] theorem nonemptyBlocks_nil : NonemptyBlocks ([] : Partition α) := by
  simp [NonemptyBlocks]

@[simp] theorem nonemptyBlocks_cons (block : List α) (rest : Partition α) :
    NonemptyBlocks (block :: rest) ↔ block ≠ [] ∧ NonemptyBlocks rest := by
  simp [NonemptyBlocks]

theorem partition_nil_iff (p : Partition α) : IsPartition [] p ↔ p = [] := by
  cases p with
  | nil => simp [IsPartition]
  | cons block rest =>
    constructor
    · rintro ⟨hflat, hblocks⟩
      have hb := (nonemptyBlocks_cons block rest).mp hblocks
      have hempty : block = [] := (List.append_eq_nil_iff.mp hflat).1
      exact False.elim (hb.1 hempty)
    · simp

theorem extendLeft_partition (x : α) (xs : List α) (p q : Partition α)
    (hp : IsPartition xs p) (hq : q ∈ extendLeft x p) :
    IsPartition (x :: xs) q := by
  cases p with
  | nil =>
    have hxs : xs = [] := by simpa [IsPartition] using hp.1.symm
    subst xs
    have hq' : q = [[x]] := by simpa [extendLeft, consBlock] using hq
    subst q
    simp [IsPartition]
  | cons block rest =>
    simp only [extendLeft, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · simpa [IsPartition, consBlock, hp.1] using hp.2
    · exact ⟨by simpa [glueLeft] using congrArg (List.cons x) hp.1,
        (nonemptyBlocks_cons _ _).mpr ⟨by simp, (nonemptyBlocks_cons _ _).mp hp.2 |>.2⟩⟩

theorem partition_cons_iff (x : α) (xs : List α) (q : Partition α) :
    IsPartition (x :: xs) q ↔
      ∃ p, IsPartition xs p ∧ q ∈ extendLeft x p := by
  constructor
  · rintro ⟨hflat, hblocks⟩
    cases q with
    | nil => simp at hflat
    | cons block rest =>
      obtain ⟨hne, hrest⟩ := (nonemptyBlocks_cons block rest).mp hblocks
      cases block with
      | nil => exact False.elim (hne rfl)
      | cons y ys =>
        have heq : y = x ∧ ys ++ rest.flatten = xs := by simpa using hflat
        obtain ⟨rfl, heq⟩ := heq
        cases ys with
        | nil =>
          refine ⟨rest, ⟨by simpa using heq, hrest⟩, ?_⟩
          cases rest <;> simp [extendLeft, consBlock]
        | cons z zs =>
          refine ⟨(z :: zs) :: rest, ⟨heq, (nonemptyBlocks_cons _ _).mpr ⟨by simp, hrest⟩⟩, ?_⟩
          simp [extendLeft, glueLeft]
  · rintro ⟨p, hp, hq⟩
    exact extendLeft_partition x xs p q hp hq

/-- Complete membership against flattening and nonempty blocks. -/
theorem mem_partsLeft (xs : List α) (p : Partition α) :
    p ∈ partsLeft xs ↔ IsPartition xs p := by
  induction xs generalizing p with
  | nil => simp [partition_nil_iff]
  | cons x xs ih =>
    simp only [partsLeft_cons, stepLeft, List.mem_flatMap, ih]
    exact (partition_cons_iff x xs p).symm

theorem partsLeft_members_nonempty (xs : List α) (p : Partition α)
    (hp : p ∈ partsLeft xs) : NonemptyBlocks p :=
  ((mem_partsLeft xs p).mp hp).2

theorem partsLeft_member_ne_nil (xs : List α) (hx : xs ≠ [])
    (p : Partition α) (hp : p ∈ partsLeft xs) : p ≠ [] := by
  intro heq
  have hf := ((mem_partsLeft xs p).mp hp).1
  rw [heq] at hf
  exact hx hf.symm

/-- Inverse of one extension on partitions with nonempty blocks. -/
def undoLeft : Partition α → Partition α
  | [] => []
  | [] :: rest => rest
  | [_] :: rest => rest
  | (_ :: y :: ys) :: rest => (y :: ys) :: rest

theorem undo_extendLeft (x : α) (p q : Partition α)
    (hp : NonemptyBlocks p) (hq : q ∈ extendLeft x p) : undoLeft q = p := by
  cases p with
  | nil =>
    have hq' : q = [[x]] := by simpa [extendLeft, consBlock] using hq
    subst q
    rfl
  | cons block rest =>
    have hb := (nonemptyBlocks_cons block rest).mp hp
    cases block with
    | nil => exact False.elim (hb.1 rfl)
    | cons y ys =>
      simp only [extendLeft, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl <;> rfl

theorem extendLeft_nodup (x : α) (p : Partition α) (hp : NonemptyBlocks p) :
    (extendLeft x p).Nodup := by
  cases p with
  | nil => simp [extendLeft]
  | cons block rest =>
    have hb := (nonemptyBlocks_cons block rest).mp hp
    cases block with
    | nil => exact False.elim (hb.1 rfl)
    | cons y ys => simp [extendLeft, consBlock, glueLeft, List.nodup_cons]

theorem stepLeft_nodup (x : α) (ps : List (Partition α)) (hn : ps.Nodup)
    (hv : ∀ p ∈ ps, NonemptyBlocks p) : (stepLeft x ps).Nodup := by
  change List.Pairwise (fun p q => p ≠ q) (ps.flatMap (extendLeft x))
  rw [List.pairwise_flatMap]
  refine ⟨fun p hp => extendLeft_nodup x p (hv p hp), ?_⟩
  apply List.Pairwise.imp_of_mem (p := hn)
  intro p q hp hq hpq a ha b hb hab
  have heq := congrArg undoLeft hab
  rw [undo_extendLeft x p a (hv p hp) ha,
      undo_extendLeft x q b (hv q hq) hb] at heq
  exact hpq heq

/-- No partition is emitted twice, even if the input has repeated elements. -/
theorem partsLeft_nodup (xs : List α) : (partsLeft xs).Nodup := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    exact stepLeft_nodup x (partsLeft xs) ih (partsLeft_members_nonempty xs)

theorem length_extendLeft_nonempty (x : α) (p : Partition α) (hp : p ≠ []) :
    (extendLeft x p).length = 2 := by
  cases p with
  | nil => exact False.elim (hp rfl)
  | cons block rest => rfl

theorem length_stepLeft (x : α) (ps : List (Partition α))
    (hp : ∀ p ∈ ps, p ≠ []) : (stepLeft x ps).length = 2 * ps.length := by
  induction ps with
  | nil => simp [stepLeft]
  | cons p ps ih =>
    have hpn : p ≠ [] := hp p (by simp)
    have hps : ∀ q ∈ ps, q ≠ [] := fun q hq => hp q (by simp [hq])
    change (extendLeft x p ++ stepLeft x ps).length = 2 * (ps.length + 1)
    rw [List.length_append, length_extendLeft_nonempty x p hpn, ih hps]
    omega

/-- The singleton/empty boundary is explicit: a nonempty n-element list has 2^(n-1) partitions. -/
theorem length_partsLeft_cons (x : α) (xs : List α) :
    (partsLeft (x :: xs)).length = 2 ^ xs.length := by
  induction xs generalizing x with
  | nil => rfl
  | cons y ys ih =>
    rw [partsLeft_cons, length_stepLeft x (partsLeft (y :: ys))
      (partsLeft_member_ne_nil (y :: ys) (by simp)), ih]
    simp [Nat.pow_succ, Nat.mul_comm]

theorem length_partsLeft (xs : List α) :
    (partsLeft xs).length = if xs.isEmpty then 1 else 2 ^ (xs.length - 1) := by
  cases xs with
  | nil => rfl
  | cons x xs => simpa using length_partsLeft_cons x xs

def allOk (ok : List α → Bool) (p : Partition α) : Bool := p.all ok

@[simp] theorem allOk_nil (ok : List α → Bool) : allOk ok [] = true := rfl

@[simp] theorem allOk_cons (ok : List α → Bool) (block : List α) (p : Partition α) :
    allOk ok (block :: p) = (ok block && allOk ok p) := rfl

/-- Empty output is never passed to source `head`; false makes that extension total. -/
def headOk (ok : List α → Bool) : Partition α → Bool
  | [] => false
  | block :: _ => ok block

def SuffixClosed (ok : List α → Bool) : Prop :=
  ∀ xs ys, ok (xs ++ ys) = true → ok ys = true

def PrefixClosed (ok : List α → Bool) : Prop :=
  ∀ xs ys, ok (xs ++ ys) = true → ok xs = true

def prunedStepLeft (ok : List α → Bool) (x : α)
    (ps : List (Partition α)) : List (Partition α) :=
  ps.flatMap (fun p => (extendLeft x p).filter (headOk ok))

def prunedPartsLeft (ok : List α → Bool) (xs : List α) : List (Partition α) :=
  xs.foldr (prunedStepLeft ok) [[]]

theorem allOk_eq_true_iff (ok : List α → Bool) (p : Partition α) :
    allOk ok p = true ↔ ∀ block ∈ p, ok block = true := by
  simp [allOk]

theorem filter_extendLeft (ok : List α → Bool) (hs : SuffixClosed ok)
    (x : α) (p : Partition α) :
    (extendLeft x p).filter (allOk ok) =
      if allOk ok p then (extendLeft x p).filter (headOk ok) else [] := by
  cases p with
  | nil =>
    cases h : ok [x] <;> simp [extendLeft, consBlock, headOk, h]
  | cons block rest =>
    have hback : ok (x :: block) = true → ok block = true := by
      intro h
      exact hs [x] block h
    cases hb : ok block <;> cases hr : allOk ok rest <;>
      cases hx : ok (x :: block) <;> cases hsingle : ok [x] <;>
      simp_all [extendLeft, consBlock, glueLeft, headOk]

theorem filter_stepLeft (ok : List α → Bool) (hs : SuffixClosed ok)
    (x : α) (ps : List (Partition α)) :
    (stepLeft x ps).filter (allOk ok) =
      prunedStepLeft ok x (ps.filter (allOk ok)) := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [stepLeft, List.flatMap_cons, List.filter_append] at ih ⊢
    rw [filter_extendLeft ok hs x p, ih]
    cases h : allOk ok p <;> simp [h, prunedStepLeft]

/-- Exact enumeration equality, including order and multiplicities, for suffix-closed pruning. -/
theorem filter_partsLeft (ok : List α → Bool) (hs : SuffixClosed ok) (xs : List α) :
    (partsLeft xs).filter (allOk ok) = prunedPartsLeft ok xs := by
  exact SquareKit.ListFusion.foldr_reachable stepLeft (prunedStepLeft ok)
    (List.filter (allOk ok)) (fun _ => True) [[]] trivial (fun _ _ _ => trivial)
    (fun x ps _ => filter_stepLeft ok hs x ps) xs

theorem mem_prunedPartsLeft (ok : List α → Bool) (hs : SuffixClosed ok)
    (xs : List α) (p : Partition α) :
    p ∈ prunedPartsLeft ok xs ↔
      IsPartition xs p ∧ ∀ block ∈ p, ok block = true := by
  rw [← filter_partsLeft ok hs]
  simp [mem_partsLeft, allOk_eq_true_iff]

theorem prunedPartsLeft_nodup (ok : List α → Bool) (hs : SuffixClosed ok)
    (xs : List α) : (prunedPartsLeft ok xs).Nodup := by
  rw [← filter_partsLeft ok hs]
  exact (partsLeft_nodup xs).filter _

theorem prunedPartsLeft_sublist (ok : List α → Bool) (hs : SuffixClosed ok)
    (xs : List α) : (prunedPartsLeft ok xs).Sublist (partsLeft xs) := by
  rw [← filter_partsLeft ok hs]
  exact List.filter_sublist

theorem prunedPartsLeft_length_le (ok : List α → Bool) (hs : SuffixClosed ok)
    (xs : List α) : (prunedPartsLeft ok xs).length ≤ (partsLeft xs).length :=
  (prunedPartsLeft_sublist ok hs xs).length_le


end OrderedPartitions
