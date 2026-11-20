import Applications.Sequences.SharedList.Insertion
import Examples.InsertionWork

/-!
VFA Sort's sharing example, interpreted in the existing immutable-cell model.
An arbitrary suffix is shared by root identity. Fresh allocation, literal source
constructors and root-relative live cells have separate checked observations.
No collector, byte size, runtime allocator or peak-space theorem is assumed.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.SharedInsertion
open Sequences.SharedList

/-- The generic path theorem supplies an actual stopping root, independent of
the suffix values and of any unrelated cells in the store. -/
theorem source_shared_root {s : Store Nat} {r : Root} (tail : List Nat)
    (h : Represents s.heap r ([1, 3, 4, 8] ++ tail)) :
    ∃ out q, insertRun (· ≤ ·) 7 s r = (some out, (4, 4)) ∧
      Durability.Extends s.heap out.1.heap ∧
      Represents out.1.heap out.2 ([1, 3, 4, 7, 8] ++ tail) ∧
      out.1.next = s.next + 4 ∧
      advance 4 out.1 out.2 = some q ∧ advance 3 s r = some q ∧
      Represents s.heap q (8 :: tail) := by
  obtain ⟨q, run, shared, suffix⟩ := insertRun_path (· ≤ ·) 7 h
  have stopped : (Resources.InsertionSort.insertRun (· ≤ ·) 7
      ([1, 3, 4, 8] ++ tail)).2 = 4 :=
    (InsertionSorting.measured_insert_stopping tail).2
  have passed : passedPrefix (· ≤ ·) 7 ([1, 3, 4, 8] ++ tail) = [1, 3, 4] := by
    simp [passedPrefix, List.takeWhile]
  have hs : Represents s.heap q (8 :: tail) := by
    simpa [remainingSuffix, List.dropWhile] using suffix
  have hp := prepend_correct [1, 3, 4, 7] hs
  refine ⟨prepend [1, 3, 4, 7] s q, q, ?_, hp.1, ?_, ?_, ?_, ?_, hs⟩
  · rw [passed, stopped, InsertionWork.source_comparisons] at run
    exact run
  · simpa using hp.2.1
  · simpa using hp.2.2
  · exact prepend_advance [1, 3, 4, 7] s q
  · simpa [passed] using shared

/-- Dropping the old root makes exactly its first three cells unreachable from
the result. Keeping it instead leaves four additional live cells. -/
theorem source_live_cells {s : Store Nat} {r : Root} (tail : List Nat)
    (h : Represents s.heap r ([1, 3, 4, 8] ++ tail))
    {out : Store Nat × Root} (success : (insertRun (· ≤ ·) 7 s r).1 = some out) :
    (liveCells s [r]).card = tail.length + 4 ∧
      (liveCells out.1 [out.2]).card = tail.length + 5 ∧
      (liveCells s [r] \ liveCells out.1 [out.2]).card = 3 ∧
      (liveCells out.1 [out.2, r]).card = tail.length + 8 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have cells := liveCells_single_card h
    simp only [List.length_append, List.length_cons, List.length_nil] at cells
    omega
  · have cells := insertRun_live_card (· ≤ ·) 7 h success
    simp only [List.length_append, List.length_cons, List.length_nil] at cells
    omega
  · simpa [passedPrefix, List.takeWhile] using
      insertRun_unreachable_card (· ≤ ·) 7 h success
  · have calls := (InsertionSorting.measured_insert_stopping tail).2
    have cells := insertRun_live_retained_card (· ≤ ·) 7 h success
    rw [calls] at cells
    simp only [List.length_append, List.length_cons, List.length_nil] at cells
    omega

/-- The source's Y is an external price per abstract live element cell. These
equalities distinguish net live growth from four fresh allocations and five
literal source constructor requests. They do not measure physical bytes. -/
theorem source_cell_price {s : Store Nat} {r : Root} (tail : List Nat)
    (h : Represents s.heap r ([1, 3, 4, 8] ++ tail))
    {out : Store Nat × Root} (success : (insertRun (· ≤ ·) 7 s r).1 = some out)
    (Y : Nat) :
    ((liveCells out.1 [out.2]).card - (liveCells s [r]).card) * Y = (4 - 3) * Y ∧
      ((liveCells out.1 [out.2, r]).card - (liveCells s [r]).card) * Y = 4 * Y ∧
      Resources.InsertionSort.insertConstructors (· ≤ ·) 7 ([1, 3, 4, 8] ++ tail) = 5 := by
  obtain ⟨old, result, _, retained⟩ := source_live_cells tail h success
  rw [old, result, retained, InsertionWork.source_constructor_requests]
  simp

/-- The actual optional-head client consumes the composed relational square. -/
theorem source_head {s : Store Nat} {r : Root} (tail : List Nat)
    (h : Represents s.heap r ([1, 3, 4, 8] ++ tail)) :
    ((insertRun (· ≤ ·) 7 s r).1.bind fun state => head state.1 state.2) = some 1 := by
  simpa [List.orderedInsert] using insertHead_correct (· ≤ ·) 7 h

theorem empty_insertion (s : Store Nat) :
    insertRun (· ≤ ·) 7 s none = (some (allocate s 7 none), (0, 1)) := by
  cases hn : s.next <;> simp [insertRun, hn, insertRunFuel]

/-- Equal heads stop immediately and share the complete old root. -/
theorem tied_root {s : Store Nat} {r : Root} (tail : List Nat)
    (h : Represents s.heap r (7 :: tail)) :
    insertRun (· ≤ ·) 7 s r = (some (allocate s 7 r), (1, 1)) := by
  obtain ⟨q, run, shared, _⟩ := insertRun_path (· ≤ ·) 7 h
  have eq : r = q := by simpa [passedPrefix, List.takeWhile, advance] using shared
  simpa [passedPrefix, List.takeWhile, prepend, ← eq,
    Resources.InsertionSort.insertRun, Resources.InsertionSort.insertComparisons_cons] using run

/-- An exhausted traversal reaches null and allocates one more cell than tests. -/
theorem full_traversal :
    ∃ out, insertRun (· ≤ ·) 4 (load [1, 2, 3]).1 (load [1, 2, 3]).2 =
        (some out, (3, 4)) ∧
      Represents out.1.heap out.2 [1, 2, 3, 4] ∧ out.1.next = 7 := by
  obtain ⟨out, _, run, _, rep, fresh, _⟩ :=
    insertRun_correct (· ≤ ·) 4 (load_represents [1, 2, 3])
  refine ⟨out, ?_, ?_, ?_⟩
  · simpa [Resources.InsertionSort.insertRun,
      Resources.InsertionSort.insertComparisons_cons,
      Resources.InsertionSort.insertComparisons_nil] using run
  · exact rep
  · simpa [load_next, Resources.InsertionSort.insertRun] using fresh

/-- Fuel failure and an invalid lookup are distinct observed failures. -/
theorem failure_boundaries :
    insertRunFuel (· ≤ ·) 7 0 (load [8]).1 (load [8]).2 = (none, (0, 0)) ∧
      insertRunFuel (· ≤ ·) 7 1 (empty : Store Nat) (some 0) = (none, (0, 1)) := by
  constructor <;> rfl

/-- A represented input is available for every suffix; the footprint claims
are not guarded by an unrealizable abstract heap assumption. -/
theorem loaded_source (tail : List Nat) :
    ∃ out, insertRun (· ≤ ·) 7 (load ([1, 3, 4, 8] ++ tail)).1
        (load ([1, 3, 4, 8] ++ tail)).2 = (some out, (4, 4)) ∧
      (liveCells out.1 [out.2]).card = tail.length + 5 := by
  obtain ⟨out, _, run, _⟩ := source_shared_root tail (load_represents _)
  exact ⟨out, run, (source_live_cells tail (load_represents _) (congrArg Prod.fst run)).2.1⟩

end Examples.SharedInsertion
