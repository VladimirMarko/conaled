import Applications.Segments.Candidates
import SquareKit.ListFusion
import Mathlib.Data.List.Sublists

/-! Ordered subsequence enumeration and independently specified increasing optima. -/
set_option autoImplicit false
set_option warningAsError true
namespace Subsequences
universe u
variable {α : Type u}
open Segments (maxsWith maxsWith_ne_nil maxsWith_covers mem_maxsWith
  maxsWith_sublist maxsWith_eq_filter_of_mem)

/-- The source skip block precedes the take block. -/
def subseqStep (x : α) (ps : List (List α)) : List (List α) :=
  ps ++ ps.map (List.cons x)

abbrev subseqs (xs : List α) : List (List α) := xs.sublists'

def subseqExtend (x : α) (ys : List α) : List (List α) := [ys, x :: ys]

abbrev subseqs1 (xs : List α) : List (List α) := xs.sublists

@[simp] theorem subseqs_nil : subseqs ([] : List α) = [[]] := rfl

theorem subseqs_cons (x : α) (xs : List α) :
    subseqs (x :: xs) = subseqs xs ++ (subseqs xs).map (List.cons x) :=
  List.sublists'_cons x xs

@[simp] theorem subseqs1_nil : subseqs1 ([] : List α) = [[]] := rfl

theorem subseqs1_cons (x : α) (xs : List α) :
    subseqs1 (x :: xs) = (subseqs1 xs).flatMap (subseqExtend x) :=
  List.sublists_cons x xs

theorem subseqs_eq_foldr (xs : List α) : subseqs xs = xs.foldr subseqStep [[]] := by
  induction xs with
  | nil => rfl
  | cons x xs ih => rw [subseqs_cons, List.foldr_cons, ← ih]; rfl

theorem subseqs1_eq_foldr (xs : List α) :
    subseqs1 xs = xs.foldr (fun x ps => ps.flatMap (subseqExtend x)) [[]] := by
  induction xs with
  | nil => rfl
  | cons x xs ih => rw [subseqs1_cons, List.foldr_cons, ← ih]

theorem mem_subseqs (xs ys : List α) : ys ∈ subseqs xs ↔ ys.Sublist xs :=
  List.mem_sublists'

theorem subseqExtend_perm (x : α) (ps : List (List α)) :
    (ps.flatMap (subseqExtend x)).Perm (ps ++ ps.map (List.cons x)) := by
  change (ps.flatMap (fun p => [p, x :: p])).Perm _
  simpa [← List.map_eq_flatMap] using
    (List.flatMap_append_perm ps (fun p => [p]) (fun p => [x :: p])).symm

theorem subseqs1_perm_subseqs (xs : List α) : (subseqs1 xs).Perm (subseqs xs) :=
  List.sublists_perm_sublists' xs

theorem mem_subseqs1 (xs ys : List α) : ys ∈ subseqs1 xs ↔ ys.Sublist xs :=
  List.mem_sublists

theorem subseqs_length (xs : List α) : (subseqs xs).length = 2 ^ xs.length :=
  List.length_sublists' xs

theorem subseqs1_length (xs : List α) : (subseqs1 xs).length = 2 ^ xs.length :=
  List.length_sublists xs

@[simp] theorem empty_mem_subseqs (xs : List α) : [] ∈ subseqs xs :=
  (mem_subseqs xs []).mpr (List.nil_sublist xs)

@[simp] theorem self_mem_subseqs (xs : List α) : xs ∈ subseqs xs :=
  (mem_subseqs xs xs).mpr (.refl xs)

/-- Actual source LINE203-204: adjacent comparisons, zipped with tail, then Boolean and. -/
def up (xs : List Int) : Bool := (xs.zipWith (fun x y => decide (x < y)) xs.tail).and

/-- Independent increasingness of every earlier/later element pair. -/
def Increasing (xs : List Int) : Prop := xs.Pairwise (fun x y => x < y)

/-- Source ok at LINE228. The empty-list guard makes the total head default irrelevant. -/
def canPrepend (x : Int) (ys : List Int) : Bool :=
  ys.isEmpty || decide (x < ys.headD 0)

@[simp] theorem up_nil : up [] = true := rfl

@[simp] theorem up_singleton (x : Int) : up [x] = true := rfl

@[simp] theorem canPrepend_nil (x : Int) : canPrepend x [] = true := rfl

@[simp] theorem canPrepend_cons (x y : Int) (ys : List Int) :
    canPrepend x (y :: ys) = decide (x < y) := rfl

/-- The actual zip/and definition obeys the historical adjacent recursive equation. -/
theorem up_cons (x : Int) (xs : List Int) : up (x :: xs) = (canPrepend x xs && up xs) := by
  cases xs <;> rfl

theorem canPrepend_iff (x : Int) (ys : List Int) (hy : Increasing ys) :
    canPrepend x ys = true ↔ ∀ y ∈ ys, x < y := by
  cases ys with
  | nil => simp
  | cons y ys =>
    rw [canPrepend_cons, decide_eq_true_eq]
    constructor
    · intro hxy z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact hxy
      · have hyz := (List.pairwise_cons.mp hy).1 z hz
        omega
    · intro h
      exact h y (by simp)

theorem up_correct (xs : List Int) : up xs = true ↔ Increasing xs := by
  induction xs with
  | nil => simp [Increasing]
  | cons x xs ih =>
    rw [up_cons, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨hc, hi⟩
      exact List.pairwise_cons.mpr ⟨(canPrepend_iff x xs hi).mp hc, hi⟩
    · intro hi
      obtain ⟨hfirst, hrest⟩ := List.pairwise_cons.mp hi
      exact ⟨(canPrepend_iff x xs hrest).mpr hfirst, hrest⟩

/-- The actual filtered step displayed on printed p268, before any thinning. -/
def upStep (x : Int) (ps : List (List Int)) : List (List Int) :=
  ps ++ (ps.filter (canPrepend x)).map (List.cons x)

def upStates (xs : List Int) : List (List Int) := xs.foldr upStep [[]]

/-- Exact one-step filter fusion, valid for arbitrary candidate lists and multiplicities. -/
theorem filter_subseqStep (x : Int) (ps : List (List Int)) :
    (subseqStep x ps).filter up = upStep x (ps.filter up) := by
  simp only [subseqStep, upStep, List.filter_append, List.filter_map, List.filter_filter,
    Function.comp_def, up_cons]

/-- Exact ordered-list equality, not only membership or optimal-length equivalence. -/
theorem filter_subseqs (xs : List Int) : (subseqs xs).filter up = upStates xs := by
  rw [subseqs_eq_foldr]
  exact SquareKit.ListFusion.foldr_reachable subseqStep upStep (List.filter up)
    (fun _ => True) [[]] trivial (fun _ _ _ => trivial)
    (fun x ps _ => filter_subseqStep x ps) xs

theorem mem_upStates (xs ys : List Int) :
    ys ∈ upStates xs ↔ List.Sublist ys xs ∧ Increasing ys := by
  rw [← filter_subseqs]
  simp only [List.mem_filter, mem_subseqs, up_correct]

@[simp] theorem empty_mem_upStates (xs : List Int) : [] ∈ upStates xs :=
  (mem_upStates xs []).mpr ⟨List.nil_sublist xs, by simp [Increasing]⟩

theorem upStates_ne_nil (xs : List Int) : upStates xs ≠ [] := by
  intro h
  have hm := empty_mem_upStates xs
  simp [h] at hm

/-- This only bounds output entries of the unthinned filtered enumeration. -/
theorem upStates_length_le (xs : List Int) : (upStates xs).length ≤ 2 ^ xs.length := by
  rw [← filter_subseqs, ← subseqs_length xs]
  exact List.length_filter_le _ _

/-! ## Actual all-optima LUS and independent global maximality -/

/-- The independent contract quantifies over every increasing input sublist. -/
def LusOptimal (xs result : List Int) : Prop :=
  result.Sublist xs ∧ Increasing result ∧
    ∀ candidate, candidate.Sublist xs → Increasing candidate →
      candidate.length ≤ result.length

/-- Source LINE230–231, with length scores embedded from Nat into Int.
This retains all tied occurrences in the first generator's order. -/
def lus0 (xs : List Int) : List (List Int) :=
  maxsWith (fun ys => (ys.length : Int)) ((subseqs xs).filter up)

/-- Exact source filter-fusion identity, retaining ordered-list multiplicities. -/
theorem lus0_eq_upStates (xs : List Int) :
    lus0 xs = maxsWith (fun ys => (ys.length : Int)) (upStates xs) := by
  rw [lus0, filter_subseqs]

theorem mem_lus0 (xs result : List Int) : result ∈ lus0 xs ↔ LusOptimal xs result := by
  rw [lus0_eq_upStates, mem_maxsWith]
  constructor
  · rintro ⟨hr, hmax⟩
    obtain ⟨hs, hi⟩ := (mem_upStates xs result).mp hr
    refine ⟨hs, hi, ?_⟩
    intro candidate hc hci
    exact Int.ofNat_le.mp (hmax candidate ((mem_upStates xs candidate).mpr ⟨hc, hci⟩))
  · rintro ⟨hs, hi, hmax⟩
    refine ⟨(mem_upStates xs result).mpr ⟨hs, hi⟩, ?_⟩
    intro candidate hc
    obtain ⟨hsub, hinc⟩ := (mem_upStates xs candidate).mp hc
    exact Int.ofNat_le.mpr (hmax candidate hsub hinc)

/-- Every independent optimum identifies the same exact ordered result filter. -/
theorem lus0_eq_filter (xs result : List Int) (h : LusOptimal xs result) :
    lus0 xs = (upStates xs).filter (fun ys => decide (ys.length = result.length)) := by
  have hm := (mem_lus0 xs result).mpr h
  rw [lus0_eq_upStates] at hm ⊢
  simpa only [Int.ofNat_inj] using maxsWith_eq_filter_of_mem
    (fun ys : List Int => (ys.length : Int)) (upStates xs) result hm

theorem lus0_sublist_upStates (xs : List Int) : (lus0 xs).Sublist (upStates xs) := by
  rw [lus0_eq_upStates]
  exact maxsWith_sublist _ _

theorem lus0_ne_nil (xs : List Int) : lus0 xs ≠ [] := by
  rw [lus0_eq_upStates]
  exact maxsWith_ne_nil _ _ (upStates_ne_nil xs)

/-- Every feasible independent candidate is no longer than a returned optimum. -/
theorem lus0_covers (xs candidate : List Int) (hs : candidate.Sublist xs)
    (hi : Increasing candidate) :
    ∃ result ∈ lus0 xs, candidate.length ≤ result.length := by
  obtain ⟨result, hr, hlen⟩ := maxsWith_covers
    (fun ys : List Int => (ys.length : Int)) (upStates xs) candidate
    ((mem_upStates xs candidate).mpr ⟨hs, hi⟩)
  exact ⟨result, by rwa [lus0_eq_upStates], Int.ofNat_le.mp hlen⟩

theorem lusOptimal_length_eq (xs first second : List Int)
    (hf : LusOptimal xs first) (hs : LusOptimal xs second) :
    first.length = second.length :=
  Nat.le_antisymm (hs.2.2 first hf.1 hf.2.1) (hf.2.2 second hs.1 hs.2.1)

theorem lusOptimal_length_le (xs result : List Int) (h : LusOptimal xs result) :
    result.length ≤ xs.length := h.1.length_le

/-- Full increasing input is optimal; this is independent of an enumerator. -/
theorem lusOptimal_self (xs : List Int) (hi : Increasing xs) : LusOptimal xs xs :=
  ⟨.refl _, hi, fun _ hs _ => hs.length_le⟩

theorem self_mem_lus0_iff (xs : List Int) : xs ∈ lus0 xs ↔ Increasing xs := by
  rw [mem_lus0]
  exact ⟨fun h => h.2.1, lusOptimal_self xs⟩

/-- For increasing input the maximizing value-list is uniquely the whole input.
This assertion concerns values, not the number of occurrences in an output list. -/
theorem lusOptimal_of_increasing (xs result : List Int) (hi : Increasing xs) :
    LusOptimal xs result ↔ result = xs := by
  constructor
  · intro h
    exact h.1.eq_of_length_le (h.2.2 xs (.refl _) hi)
  · rintro rfl
    exact lusOptimal_self _ hi

@[simp] theorem lus0_nil : lus0 [] = [[]] := rfl

end Subsequences
