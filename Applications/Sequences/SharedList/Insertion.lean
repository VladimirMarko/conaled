import Applications.Sequences.SharedList.Observation
import Applications.Sequences.SharedList.Live
import Applications.Resources.InsertionWork

/-!
# Insertion through immutable list roots

The operation reads actual heap links. A successful head comparison allocates
one cell pointing to the existing matched root; failed comparisons copy the
traversed prefix. Observations count head comparisons and recursive entries.
Fresh allocation is independently observed through the frontier. The operation
refines the source insertion, but it does not assert compiler allocation or GC.
Source correspondence: `docs/research/vfa-coverage.md`, VFA Sort, CTB-81.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Sequences.SharedList
variable {α : Type}

/-- Exactly the source heads passed before the first successful comparison. -/
abbrev passedPrefix (rel : α → α → Prop) [DecidableRel rel] (x : α) (xs : List α) :
    List α := xs.takeWhile (fun y => decide (¬ rel x y))

abbrev remainingSuffix (rel : α → α → Prop) [DecidableRel rel] (x : α)
    (xs : List α) : List α := xs.dropWhile (fun y => decide (¬ rel x y))

theorem insertion_calls_eq_prefix (rel : α → α → Prop) [DecidableRel rel]
    (x : α) (xs : List α) :
    (Resources.InsertionSort.insertRun rel x xs).2 = (passedPrefix rel x xs).length + 1 := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
      by_cases h : rel x y <;>
        simp [Resources.InsertionSort.insertRun, passedPrefix, List.takeWhile, h, ih]

/-- Malformed roots and exhausted fuel fail explicitly. Valid input supplies fuel
from its frontier, as in the existing append/update implementations. -/
def insertRunFuel (rel : α → α → Prop) [DecidableRel rel] (x : α) :
    Nat → Store α → Root → Resources.Measured (Option (Store α × Root)) (Nat × Nat)
  | _, s, none => (some (allocate s x none), (0, 1))
  | 0, _, some _ => (none, (0, 0))
  | fuel + 1, s, some a =>
      match s.heap a with
      | none => (none, (0, 1))
      | some (y, q) =>
          if rel x y then (some (allocate s x (some a)), (1, 1))
          else
            let rest := insertRunFuel rel x fuel s q
            (rest.1.map (fun out => allocate out.1 y out.2), rest.2 + (1, 1))

/-- Execution identifies the actual stopping root and exactly the prefix allocated
around it. The suffix observation alone would not identify that root. -/
theorem insertRunFuel_path (rel : α → α → Prop) [DecidableRel rel] (x : α)
    {s : Store α} {r : Root} {xs : List α} (h : Represents s.heap r xs)
    {fuel : Nat} (enough : xs.length ≤ fuel) :
    ∃ q, insertRunFuel rel x fuel s r =
        (some (prepend (passedPrefix rel x xs ++ [x]) s q),
          (Resources.InsertionSort.insertComparisons rel x xs,
            (Resources.InsertionSort.insertRun rel x xs).2)) ∧
      advance (passedPrefix rel x xs).length s r = some q ∧
      Represents s.heap q (remainingSuffix rel x xs) := by
  induction h generalizing fuel with
  | nil => cases fuel <;> exact ⟨none, rfl, rfl, .nil⟩
  | @cons a y r ys lookup below rest ih =>
      cases fuel with
      | zero => simp at enough
      | succ fuel =>
          by_cases hxy : rel x y
          · refine ⟨some a, ?_, ?_, ?_⟩
            · simp [insertRunFuel, lookup, hxy, passedPrefix, List.takeWhile,
                prepend, Resources.InsertionSort.insertComparisons_cons,
                Resources.InsertionSort.insertRun]
            · simp [passedPrefix, List.takeWhile, hxy, advance]
            · simpa [remainingSuffix, List.dropWhile, hxy] using
                (Represents.cons lookup below rest)
          · obtain ⟨q, run, shared, rep⟩ := ih (by simpa using enough)
            refine ⟨q, ?_, ?_, ?_⟩
            · simp [insertRunFuel, lookup, hxy, run, passedPrefix, List.takeWhile,
                prepend, Resources.InsertionSort.insertComparisons_cons,
                Resources.InsertionSort.insertRun]
            · simpa [passedPrefix, List.takeWhile, hxy, advance, read, lookup] using shared
            · simpa [remainingSuffix, List.dropWhile, hxy] using rep

def insertRun (rel : α → α → Prop) [DecidableRel rel] (x : α) (s : Store α)
    (r : Root) : Resources.Measured (Option (Store α × Root)) (Nat × Nat) :=
  insertRunFuel rel x s.next s r

theorem insertRun_path (rel : α → α → Prop) [DecidableRel rel] (x : α)
    {s : Store α} {r : Root} {xs : List α} (h : Represents s.heap r xs) :
    ∃ q, insertRun rel x s r =
        (some (prepend (passedPrefix rel x xs ++ [x]) s q),
          (Resources.InsertionSort.insertComparisons rel x xs,
            (Resources.InsertionSort.insertRun rel x xs).2)) ∧
      advance (passedPrefix rel x xs).length s r = some q ∧
      Represents s.heap q (remainingSuffix rel x xs) :=
  insertRunFuel_path rel x h h.length_le_next

/-- Prepending a prefix reaches the exact original suffix root. -/
theorem prepend_advance (pre : List α) (s : Store α) (q : Root) :
    advance pre.length (prepend pre s q).1 (prepend pre s q).2 = some q := by
  induction pre with
  | nil => rfl
  | cons x pre ih =>
      have kept := advance_mono
        (allocate_extends (prepend pre s q).1 x (prepend pre s q).2) ih
      simpa [prepend, advance, read, allocate_lookup] using kept

/-- Exact fresh allocation and root identity supplement value correspondence.
Every old represented root is retained by the returned heap extension. -/
theorem insertRun_correct (rel : α → α → Prop) [DecidableRel rel] (x : α)
    {s : Store α} {r : Root} {xs : List α} (h : Represents s.heap r xs) :
    ∃ out q, insertRun rel x s r = (some out,
        (Resources.InsertionSort.insertComparisons rel x xs,
          (Resources.InsertionSort.insertRun rel x xs).2)) ∧
      Durability.Extends s.heap out.1.heap ∧
      Represents out.1.heap out.2 (List.orderedInsert rel x xs) ∧
      out.1.next = s.next + (Resources.InsertionSort.insertRun rel x xs).2 ∧
      advance (Resources.InsertionSort.insertRun rel x xs).2 out.1 out.2 = some q ∧
      advance ((Resources.InsertionSort.insertRun rel x xs).2 - 1) s r = some q := by
  obtain ⟨q, run, oldShared, suffix⟩ := insertRun_path rel x h
  have hp := prepend_correct (passedPrefix rel x xs ++ [x]) suffix
  refine ⟨prepend (passedPrefix rel x xs ++ [x]) s q, q, run, hp.1, ?_, ?_, ?_, ?_⟩
  · rw [List.orderedInsert_eq_take_drop]
    simpa [passedPrefix, remainingSuffix, List.append_assoc] using hp.2.1
  · simpa [insertion_calls_eq_prefix] using hp.2.2
  · simpa [insertion_calls_eq_prefix] using
      prepend_advance (passedPrefix rel x xs ++ [x]) s q
  · simpa [insertion_calls_eq_prefix] using oldShared

/-- The product relation retains both the optional representation and exact costs. -/
def insertMeasuredSquare (rel : α → α → Prop) [DecidableRel rel] (x : α) :
    Relational.RelSquare (representation α)
      (Relational.product (optionalRepresentation α) ⟨Nat × Nat, Nat × Nat, Eq⟩) where
  impl state := insertRun rel x state.1 state.2
  spec xs := (some (List.orderedInsert rel x xs),
    (Resources.InsertionSort.insertComparisons rel x xs,
      (Resources.InsertionSort.insertRun rel x xs).2))
  preserves := by
    intro state xs h
    obtain ⟨out, _, run, _, rep, _⟩ := insertRun_correct rel x h
    rw [run]
    exact ⟨rep, rfl⟩

def insertSquare (rel : α → α → Prop) [DecidableRel rel] (x : α) :
    Relational.RelSquare (representation α) (optionalRepresentation α) :=
  Relational.compose (Relational.first (optionalRepresentation α) ⟨Nat × Nat, Nat × Nat, Eq⟩)
    (insertMeasuredSquare rel x)

/-- A consumer composes the existing optional-head observation with insertion. -/
theorem insertHead_correct (rel : α → α → Prop) [DecidableRel rel] (x : α)
    {s : Store α} {r : Root} {xs : List α} (h : Represents s.heap r xs) :
    ((insertRun rel x s r).1.bind fun state => head state.1 state.2) =
      (List.orderedInsert rel x xs).head? :=
  (Relational.compose (headSquare α) (insertSquare rel x)).preserves
    (r := (s, r)) (s := xs) h

/-- With only the returned root retained, exactly one additional element cell
is reachable. This is not an assertion that unreachable cells were reclaimed. -/
theorem insertRun_live_card (rel : α → α → Prop) [DecidableRel rel] (x : α)
    {s : Store α} {r : Root} {xs : List α} (h : Represents s.heap r xs)
    {out : Store α × Root} (success : (insertRun rel x s r).1 = some out) :
    (liveCells out.1 [out.2]).card = xs.length + 1 := by
  obtain ⟨out', _, run, _, rep, _⟩ := insertRun_correct rel x h
  have eq : out' = out := Option.some.inj ((congrArg Prod.fst run).symm.trans success)
  subst out'
  simpa only [List.orderedInsert_length] using liveCells_single_card rep

/-- Keeping the original root retains its complete footprint in addition to
the fresh copied prefix. Other old roots can only add reachable cells. -/
theorem insertRun_live_retained (rel : α → α → Prop) [DecidableRel rel] (x : α)
    {s : Store α} {r : Root} {xs : List α} (h : Represents s.heap r xs)
    {out : Store α × Root} (success : (insertRun rel x s r).1 = some out) :
    liveCells out.1 [out.2, r] =
      Finset.Ico s.next (s.next + (Resources.InsertionSort.insertRun rel x xs).2) ∪
        liveCells s [r] := by
  obtain ⟨q, run, shared, suffix⟩ := insertRun_path rel x h
  have eq : out = prepend (passedPrefix rel x xs ++ [x]) s q :=
    Option.some.inj (success.symm.trans (congrArg Prod.fst run))
  rw [eq]
  simpa [insertion_calls_eq_prefix] using
    liveCells_prepend_retained (passedPrefix rel x xs ++ [x]) suffix h
      (liveCells_advance_subset shared)

theorem insertRun_live_retained_card (rel : α → α → Prop) [DecidableRel rel] (x : α)
    {s : Store α} {r : Root} {xs : List α} (h : Represents s.heap r xs)
    {out : Store α × Root} (success : (insertRun rel x s r).1 = some out) :
    (liveCells out.1 [out.2, r]).card =
      (Resources.InsertionSort.insertRun rel x xs).2 + xs.length := by
  rw [insertRun_live_retained rel x h success,
    Finset.card_union_of_disjoint (liveCells_disjoint_fresh s [r] _),
    liveCells_single_card h]
  simp

/-- Exactly the copied old prefix becomes unreachable from the result. The
original root must be dropped for those cells to be eligible for reclamation. -/
theorem insertRun_unreachable_card (rel : α → α → Prop) [DecidableRel rel] (x : α)
    {s : Store α} {r : Root} {xs : List α} (h : Represents s.heap r xs)
    {out : Store α × Root} (success : (insertRun rel x s r).1 = some out) :
    (liveCells s [r] \ liveCells out.1 [out.2]).card =
      (passedPrefix rel x xs).length := by
  obtain ⟨q, run, shared, suffix⟩ := insertRun_path rel x h
  have eq : out = prepend (passedPrefix rel x xs ++ [x]) s q :=
    Option.some.inj (success.symm.trans (congrArg Prod.fst run))
  rw [eq, liveCells_prepend _ suffix]
  have difference : liveCells s [r] \
      (Finset.Ico s.next (s.next + (passedPrefix rel x xs ++ [x]).length) ∪
        liveCells s [q]) = liveCells s [r] \ liveCells s [q] := by
    ext a
    simp only [Finset.mem_sdiff, Finset.mem_union]
    constructor
    · rintro ⟨old, outside⟩
      exact ⟨old, fun tail => outside (Or.inr tail)⟩
    · rintro ⟨old, outside⟩
      refine ⟨old, ?_⟩
      rintro (fresh | tail)
      · exact Finset.disjoint_left.mp (liveCells_disjoint_fresh s [r] _) fresh old
      · exact outside tail
  rw [difference, Finset.card_sdiff_of_subset (liveCells_advance_subset shared),
    liveCells_single_card h, liveCells_single_card suffix]
  have lengths : (passedPrefix rel x xs).length + (remainingSuffix rel x xs).length =
      xs.length := by
    simpa only [passedPrefix, remainingSuffix, List.length_append] using
      congrArg List.length (List.takeWhile_append_dropWhile
        (p := fun y => decide (¬ rel x y)) (l := xs))
  omega

end Sequences.SharedList
