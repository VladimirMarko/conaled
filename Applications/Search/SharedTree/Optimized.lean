import Applications.Search.SharedTree.Path
import Applications.Search.OrderedTree.Candidate

/-!
# Aborting insertion through immutable roots

The raw traversals distinguish invalid input/fuel (`none`), duplicate abort
(`some none`), and insertion success (`some (some out)`). Constructors call the
actual cell allocator only after recursive success. A single outer handler
returns the exact original store and root on a duplicate abort.

The three measures count comparisons, structural visits, and fresh cells. They
describe the explicit cell model, not Lean's allocator or exception runtime.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Search.SharedTree
variable {α : Type} [LinearOrder α]

/-- Common successful-outcome contract. `Option.Rel` adds the matching abort
case without identifying it with invalid-input failure. -/
def Inserted (before : Store α) (root : Root) (path : List Branch) (cells : Nat)
    (out : Store α × Root) (value : BinaryTree α) : Prop :=
  Durability.Extends before.heap out.1.heap ∧
    Represents out.1.heap out.2 value ∧
    out.1.next = before.next + cells ∧
    Rebuilds before.heap out.1.heap root out.2 path

def abortProfile (x : α) (t : BinaryTree α) : Nat × Nat × Nat :=
  ((OrderedTree.insertAbortRun x t).2, (searchPathBy id x t).length + 1,
    if (OrderedTree.insertAbortRun x t).1.isSome then (searchPathBy id x t).length + 1 else 0)

def insertAbortRunFuel : Nat → Store α → Root → α →
    Resources.Measured (Option (Option (Store α × Root))) (Nat × Nat × Nat)
  | _, s, none, x => (some (some (allocate s x none none)), (0, 1, 1))
  | 0, _, some _, _ => (none, (0, 0, 0))
  | fuel + 1, s, some a, x =>
      match s.heap a with
      | none => (none, (0, 1, 0))
      | some ((y, l), r) =>
          if x < y then
            let rest := insertAbortRunFuel fuel s l x
            match rest.1 with
            | none => (none, (rest.2.1 + 1, rest.2.2.1 + 1, rest.2.2.2))
            | some none => (some none, (rest.2.1 + 1, rest.2.2.1 + 1, rest.2.2.2))
            | some (some out) => (some (some (allocate out.1 y out.2 r)),
                (rest.2.1 + 1, rest.2.2.1 + 1, rest.2.2.2 + 1))
          else if y < x then
            let rest := insertAbortRunFuel fuel s r x
            match rest.1 with
            | none => (none, (rest.2.1 + 2, rest.2.2.1 + 1, rest.2.2.2))
            | some none => (some none, (rest.2.1 + 2, rest.2.2.1 + 1, rest.2.2.2))
            | some (some out) => (some (some (allocate out.1 y l out.2)),
                (rest.2.1 + 2, rest.2.2.1 + 1, rest.2.2.2 + 1))
          else (some none, (2, 1, 0))

/-- This handler occurs only at the public boundary, not inside either loop. -/
def handleAbort (s : Store α) (root : Root)
    (run : Resources.Measured (Option (Option (Store α × Root))) (Nat × Nat × Nat)) :
    Resources.Measured (Option (Store α × Root)) (Nat × Nat × Nat) :=
  (run.1.map (fun out => out.getD (s, root)), run.2)

def insertAbortRun (s : Store α) (root : Root) (x : α) :
    Resources.Measured (Option (Store α × Root)) (Nat × Nat × Nat) :=
  handleAbort s root (insertAbortRunFuel s.next s root x)

theorem insertAbortRunFuel_refines {s : Store α} {root : Root} {t : BinaryTree α}
    (h : Represents s.heap root t) {fuel : Nat} (enough : t.height ≤ fuel) (x : α) :
    ∃ out, insertAbortRunFuel fuel s root x = (some out, abortProfile x t) ∧
      Option.Rel (Inserted s root (searchPathBy id x t) (abortProfile x t).2.2)
        out (OrderedTree.insertAbortRun x t).1 := by
  induction h generalizing fuel with
  | nil =>
      refine ⟨some (allocate s x none none), ?_, .some ?_⟩
      · simp [insertAbortRunFuel, abortProfile, searchPathBy, OrderedTree.insertAbortRun]
      · exact ⟨allocate_extends _ _ _ _, allocate_represents .nil .nil x,
          rfl, .here _ _⟩
  | @node a y l r lt rt lookup leftBelow rightBelow hl hr ihl ihr =>
      cases fuel with
      | zero => simp [BinaryTree.height] at enough
      | succ fuel =>
          have leftEnough : lt.height ≤ fuel := by
            have le := Nat.le_max_left lt.height rt.height
            simp only [BinaryTree.height] at enough
            omega
          have rightEnough : rt.height ≤ fuel := by
            have le := Nat.le_max_right lt.height rt.height
            simp only [BinaryTree.height] at enough
            omega
          by_cases xy : x < y
          · obtain ⟨out, run, rel⟩ := ihl leftEnough
            generalize source : (OrderedTree.insertAbortRun x lt).1 = value at rel
            cases rel with
            | none =>
                refine ⟨none, ?_, ?_⟩
                · simp [insertAbortRunFuel, lookup, xy, run, abortProfile, searchPathBy, id_eq,
                    OrderedTree.insertAbortRun, source]
                · simp only [OrderedTree.insertAbortRun, ite_eq_left xy, source,
                    Option.map_none]
                  exact .none
            | @some out value info =>
                obtain ⟨extension, rep, count, rebuilt⟩ := info
                have grown := allocate_extends out.1 y out.2 r
                refine ⟨some (allocate out.1 y out.2 r), ?_, ?_⟩
                · simp [insertAbortRunFuel, lookup, xy, run, abortProfile, searchPathBy, id_eq,
                    OrderedTree.insertAbortRun, source, Nat.add_assoc]
                · simp only [OrderedTree.insertAbortRun, ite_eq_left xy, source,
                    Option.map_some]
                  apply Option.Rel.some
                  refine ⟨extension.trans grown, allocate_represents rep (hr.mono extension) y,
                    ?_, ?_⟩
                  · rw [allocate_next, count]
                    simp [abortProfile, searchPathBy, id_eq, OrderedTree.insertAbortRun, xy, source,
                      Nat.add_assoc]
                  · simpa only [searchPathBy, id_eq, ite_eq_left xy, allocate_root] using
                      Rebuilds.left lookup (allocate_lookup out.1 y out.2 r) (rebuilt.mono grown)
          · by_cases yx : y < x
            · obtain ⟨out, run, rel⟩ := ihr rightEnough
              generalize source : (OrderedTree.insertAbortRun x rt).1 = value at rel
              cases rel with
              | none =>
                  refine ⟨none, ?_, ?_⟩
                  · simp [insertAbortRunFuel, lookup, xy, yx, run, abortProfile, searchPathBy, id_eq,
                      OrderedTree.insertAbortRun, source]
                  · simp only [OrderedTree.insertAbortRun, ite_eq_right xy, ite_eq_left yx,
                      source, Option.map_none]
                    exact .none
              | @some out value info =>
                  obtain ⟨extension, rep, count, rebuilt⟩ := info
                  have grown := allocate_extends out.1 y l out.2
                  refine ⟨some (allocate out.1 y l out.2), ?_, ?_⟩
                  · simp [insertAbortRunFuel, lookup, xy, yx, run, abortProfile, searchPathBy, id_eq,
                      OrderedTree.insertAbortRun, source, Nat.add_assoc]
                  · simp only [OrderedTree.insertAbortRun, ite_eq_right xy, ite_eq_left yx,
                      source, Option.map_some]
                    apply Option.Rel.some
                    refine ⟨extension.trans grown,
                      allocate_represents (hl.mono extension) rep y, ?_, ?_⟩
                    · rw [allocate_next, count]
                      simp [abortProfile, searchPathBy, id_eq, OrderedTree.insertAbortRun, xy, yx,
                        source, Nat.add_assoc]
                    · simpa only [searchPathBy, id_eq, ite_eq_right xy, ite_eq_left yx,
                        allocate_root] using
                        Rebuilds.right lookup (allocate_lookup out.1 y l out.2) (rebuilt.mono grown)
            · refine ⟨none, ?_, ?_⟩
              · simp [insertAbortRunFuel, lookup, xy, yx, abortProfile, searchPathBy, id_eq,
                  OrderedTree.insertAbortRun]
              · simp only [OrderedTree.insertAbortRun, ite_eq_right xy, ite_eq_right yx]
                exact .none

/-- Candidate search continues to an empty node, even after passing an equal
label. Its path is independent of the remembered candidate's value. -/
def candidatePath (x : α) : BinaryTree α → List Branch
  | .nil => []
  | .node y l r =>
      if x < y then .left :: candidatePath x l else .right :: candidatePath x r

def candidateProfile (x : α) (candidate : Option α) (t : BinaryTree α) : Nat × Nat × Nat :=
  ((OrderedTree.insertCandidateRun x candidate t).2, (candidatePath x t).length + 1,
    if (OrderedTree.insertCandidateRun x candidate t).1.isSome then
      (candidatePath x t).length + 1 else 0)

def insertCandidateRunFuel : Nat → Store α → Root → α → Option α →
    Resources.Measured (Option (Option (Store α × Root))) (Nat × Nat × Nat)
  | _, s, none, x, candidate => match candidate with
      | none => (some (some (allocate s x none none)), (0, 1, 1))
      | some c => if x = c then (some none, (1, 1, 0))
          else (some (some (allocate s x none none)), (1, 1, 1))
  | 0, _, some _, _, _ => (none, (0, 0, 0))
  | fuel + 1, s, some a, x, candidate =>
      match s.heap a with
      | none => (none, (0, 1, 0))
      | some ((y, l), r) =>
          if x < y then
            let rest := insertCandidateRunFuel fuel s l x candidate
            match rest.1 with
            | none => (none, (rest.2.1 + 1, rest.2.2.1 + 1, rest.2.2.2))
            | some none => (some none, (rest.2.1 + 1, rest.2.2.1 + 1, rest.2.2.2))
            | some (some out) => (some (some (allocate out.1 y out.2 r)),
                (rest.2.1 + 1, rest.2.2.1 + 1, rest.2.2.2 + 1))
          else
            let rest := insertCandidateRunFuel fuel s r x (some y)
            match rest.1 with
            | none => (none, (rest.2.1 + 1, rest.2.2.1 + 1, rest.2.2.2))
            | some none => (some none, (rest.2.1 + 1, rest.2.2.1 + 1, rest.2.2.2))
            | some (some out) => (some (some (allocate out.1 y l out.2)),
                (rest.2.1 + 1, rest.2.2.1 + 1, rest.2.2.2 + 1))

def insertCandidateRun (s : Store α) (root : Root) (x : α) :
    Resources.Measured (Option (Store α × Root)) (Nat × Nat × Nat) :=
  handleAbort s root (insertCandidateRunFuel s.next s root x none)

theorem candidatePath_length_le (x : α) (t : BinaryTree α) :
    (candidatePath x t).length ≤ t.height := by
  induction t with
  | nil => simp [candidatePath]
  | node y l r hl hr =>
      have leLeft := Nat.le_max_left l.height r.height
      have leRight := Nat.le_max_right l.height r.height
      simp only [candidatePath]
      split <;> simp only [List.length_cons, BinaryTree.height] <;> omega

theorem insertCandidateRunFuel_refines {s : Store α} {root : Root} {t : BinaryTree α}
    (h : Represents s.heap root t) {fuel : Nat} (enough : t.height ≤ fuel)
    (x : α) (candidate : Option α) :
    ∃ out, insertCandidateRunFuel fuel s root x candidate =
        (some out, candidateProfile x candidate t) ∧
      Option.Rel (Inserted s root (candidatePath x t) (candidateProfile x candidate t).2.2)
        out (OrderedTree.insertCandidateRun x candidate t).1 := by
  induction h generalizing fuel candidate with
  | nil =>
      cases candidate with
      | none =>
          refine ⟨some (allocate s x none none), ?_, .some ?_⟩
          · simp [insertCandidateRunFuel, candidateProfile, candidatePath,
              OrderedTree.insertCandidateRun]
          · exact ⟨allocate_extends _ _ _ _, allocate_represents .nil .nil x,
              rfl, .here _ _⟩
      | some c =>
          by_cases eq : x = c
          · refine ⟨none, ?_, ?_⟩
            · simp [insertCandidateRunFuel, candidateProfile, candidatePath,
                OrderedTree.insertCandidateRun, eq]
            · simp only [OrderedTree.insertCandidateRun, ite_eq_left eq]
              exact .none
          · refine ⟨some (allocate s x none none), ?_, ?_⟩
            · simp [insertCandidateRunFuel, candidateProfile, candidatePath,
                OrderedTree.insertCandidateRun, eq]
            · simp only [OrderedTree.insertCandidateRun, ite_eq_right eq]
              apply Option.Rel.some
              refine ⟨allocate_extends _ _ _ _, allocate_represents .nil .nil x, ?_, .here _ _⟩
              simp [candidateProfile, candidatePath, OrderedTree.insertCandidateRun, eq]
  | @node a y l r lt rt lookup leftBelow rightBelow hl hr ihl ihr =>
      cases fuel with
      | zero => simp [BinaryTree.height] at enough
      | succ fuel =>
          have leftEnough : lt.height ≤ fuel := by
            have le := Nat.le_max_left lt.height rt.height
            simp only [BinaryTree.height] at enough
            omega
          have rightEnough : rt.height ≤ fuel := by
            have le := Nat.le_max_right lt.height rt.height
            simp only [BinaryTree.height] at enough
            omega
          by_cases xy : x < y
          · obtain ⟨out, run, rel⟩ := ihl leftEnough candidate
            generalize source : (OrderedTree.insertCandidateRun x candidate lt).1 = value at rel
            cases rel with
            | none =>
                refine ⟨none, ?_, ?_⟩
                · simp [insertCandidateRunFuel, lookup, xy, run, candidateProfile, candidatePath,
                    OrderedTree.insertCandidateRun, source]
                · simp only [OrderedTree.insertCandidateRun, ite_eq_left xy, source,
                    Option.map_none]
                  exact .none
            | @some out value info =>
                obtain ⟨extension, rep, count, rebuilt⟩ := info
                have grown := allocate_extends out.1 y out.2 r
                refine ⟨some (allocate out.1 y out.2 r), ?_, ?_⟩
                · simp [insertCandidateRunFuel, lookup, xy, run, candidateProfile, candidatePath,
                    OrderedTree.insertCandidateRun, source, Nat.add_assoc]
                · simp only [OrderedTree.insertCandidateRun, ite_eq_left xy, source,
                    Option.map_some]
                  apply Option.Rel.some
                  refine ⟨extension.trans grown, allocate_represents rep (hr.mono extension) y,
                    ?_, ?_⟩
                  · rw [allocate_next, count]
                    simp [candidateProfile, candidatePath, OrderedTree.insertCandidateRun, xy,
                      source, Nat.add_assoc]
                  · simpa only [candidatePath, ite_eq_left xy, allocate_root] using
                      Rebuilds.left lookup (allocate_lookup out.1 y out.2 r) (rebuilt.mono grown)
          · obtain ⟨out, run, rel⟩ := ihr rightEnough (some y)
            generalize source : (OrderedTree.insertCandidateRun x (some y) rt).1 = value at rel
            cases rel with
            | none =>
                refine ⟨none, ?_, ?_⟩
                · simp [insertCandidateRunFuel, lookup, xy, run, candidateProfile, candidatePath,
                    OrderedTree.insertCandidateRun, source]
                · simp only [OrderedTree.insertCandidateRun, ite_eq_right xy, source,
                    Option.map_none]
                  exact .none
            | @some out value info =>
                obtain ⟨extension, rep, count, rebuilt⟩ := info
                have grown := allocate_extends out.1 y l out.2
                refine ⟨some (allocate out.1 y l out.2), ?_, ?_⟩
                · simp [insertCandidateRunFuel, lookup, xy, run, candidateProfile, candidatePath,
                    OrderedTree.insertCandidateRun, source, Nat.add_assoc]
                · simp only [OrderedTree.insertCandidateRun, ite_eq_right xy, source,
                    Option.map_some]
                  apply Option.Rel.some
                  refine ⟨extension.trans grown,
                    allocate_represents (hl.mono extension) rep y, ?_, ?_⟩
                  · rw [allocate_next, count]
                    simp [candidateProfile, candidatePath, OrderedTree.insertCandidateRun, xy,
                      source, Nat.add_assoc]
                  · simpa only [candidatePath, ite_eq_right xy, allocate_root] using
                      Rebuilds.right lookup (allocate_lookup out.1 y l out.2) (rebuilt.mono grown)

theorem abortProfile_bounds (x : α) (t : BinaryTree α) :
    (abortProfile x t).1 ≤ 2 * t.height ∧
      (abortProfile x t).2.1 ≤ t.height + 1 ∧
      (abortProfile x t).2.2 ≤ t.height + 1 := by
  refine ⟨?_, Nat.add_le_add_right (searchPathBy_length_le id x t) 1, ?_⟩
  · change (OrderedTree.insertAbortRun x t).2 ≤ _
    rw [OrderedTree.insertAbortRun_comparisons]
    exact OrderedTree.memberRun_bound x t
  · have bound := searchPathBy_length_le id x t
    change (if (OrderedTree.insertAbortRun x t).1.isSome then
      (searchPathBy id x t).length + 1 else 0) ≤ t.height + 1
    split <;> omega

theorem candidateProfile_bounds (x : α) (candidate : Option α) (t : BinaryTree α) :
    (candidateProfile x candidate t).1 ≤ t.height + 1 ∧
      (candidateProfile x candidate t).2.1 ≤ t.height + 1 ∧
      (candidateProfile x candidate t).2.2 ≤ t.height + 1 := by
  refine ⟨OrderedTree.insertCandidateRun_bound x candidate t,
    Nat.add_le_add_right (candidatePath_length_le x t) 1, ?_⟩
  have bound := candidatePath_length_le x t
  change (if (OrderedTree.insertCandidateRun x candidate t).1.isSome then
    (candidatePath x t).length + 1 else 0) ≤ t.height + 1
  split <;> omega

omit [LinearOrder α] in
private theorem handled_represents {s : Store α} {root : Root} {t : BinaryTree α}
    {path : List Branch} {cells : Nat} {out : Option (Store α × Root)}
    {value : Option (BinaryTree α)} (h : Represents s.heap root t)
    (rel : Option.Rel (Inserted s root path cells) out value) :
    Represents (out.getD (s, root)).1.heap (out.getD (s, root)).2 (value.getD t) := by
  cases rel with
  | none => exact h
  | some info => exact info.2.1

/-- The operational value refinement needs no search-order invariant. Order
is required separately when interpreting this value as the intended set. -/
theorem insertAbortRun_value {s : Store α} {root : Root} {t : BinaryTree α}
    (h : Represents s.heap root t) (x : α) :
    ∃ out, insertAbortRun s root x = (some out, abortProfile x t) ∧
      Represents out.1.heap out.2 (OrderedTree.insertAbort x t) := by
  obtain ⟨out, run, rel⟩ := insertAbortRunFuel_refines h h.height_le_next x
  refine ⟨out.getD (s, root), ?_, handled_represents h rel⟩
  simp only [insertAbortRun, handleAbort, run, Option.map_some]

theorem insertCandidateRun_value {s : Store α} {root : Root} {t : BinaryTree α}
    (h : Represents s.heap root t) (x : α) :
    ∃ out, insertCandidateRun s root x = (some out, candidateProfile x none t) ∧
      Represents out.1.heap out.2 (OrderedTree.insertCandidate x t) := by
  obtain ⟨out, run, rel⟩ := insertCandidateRunFuel_refines h h.height_le_next x none
  refine ⟨out.getD (s, root), ?_, handled_represents h rel⟩
  simp only [insertCandidateRun, handleAbort, run, Option.map_some]

theorem insertAbortRun_profile {s : Store α} {root : Root} {t : BinaryTree α}
    (h : Represents s.heap root t) (x : α) :
    (insertAbortRun s root x).2 = abortProfile x t := by
  obtain ⟨out, run, _⟩ := insertAbortRunFuel_refines h h.height_le_next x
  simp only [insertAbortRun, handleAbort, run]

theorem insertCandidateRun_profile {s : Store α} {root : Root} {t : BinaryTree α}
    (h : Represents s.heap root t) (x : α) :
    (insertCandidateRun s root x).2 = candidateProfile x none t := by
  obtain ⟨out, run, _⟩ := insertCandidateRunFuel_refines h h.height_le_next x none
  simp only [insertCandidateRun, handleAbort, run]

/-- Duplicate insertion returns the identical store/root pair and performs
zero fresh-cell allocations. The comparison and visit counts are retained. -/
theorem insertAbortRun_duplicate {s : Store α} {root : Root} {t : BinaryTree α}
    (h : Represents s.heap root t) (ordered : OrderedTree.Ordered t) {x : α}
    (present : OrderedTree.Contains x t) :
    insertAbortRun s root x =
      (some (s, root), ((OrderedTree.insertAbortRun x t).2, (searchPathBy id x t).length + 1, 0)) := by
  have source := (OrderedTree.insertAbortRun_none_iff x t).mpr
    ((OrderedTree.member_correct ordered x).mpr present)
  obtain ⟨out, run, rel⟩ := insertAbortRunFuel_refines h h.height_le_next x
  rw [source] at rel
  cases rel
  simp [insertAbortRun, handleAbort, run, abortProfile, source]

theorem insertCandidateRun_duplicate {s : Store α} {root : Root} {t : BinaryTree α}
    (h : Represents s.heap root t) (ordered : OrderedTree.Ordered t) {x : α}
    (present : OrderedTree.Contains x t) :
    insertCandidateRun s root x =
      (some (s, root), ((OrderedTree.insertCandidateRun x none t).2,
        (candidatePath x t).length + 1, 0)) := by
  have source := (OrderedTree.insertCandidateRun_none_iff ordered
    (show OrderedTree.LowerBound none t from trivial) x).mpr (Or.inl present)
  obtain ⟨out, run, rel⟩ := insertCandidateRunFuel_refines h h.height_le_next x none
  rw [source] at rel
  cases rel
  simp [insertCandidateRun, handleAbort, run, candidateProfile, source]

theorem insertAbortRun_absent {s : Store α} {root : Root} {t : BinaryTree α}
    (h : Represents s.heap root t) (ordered : OrderedTree.Ordered t) {x : α}
    (absent : ¬ OrderedTree.Contains x t) :
    ∃ out, insertAbortRun s root x = (some out, abortProfile x t) ∧
      Inserted s root (searchPathBy id x t) ((searchPathBy id x t).length + 1)
        out (OrderedTree.insert x t) := by
  obtain ⟨result, run, rel⟩ := insertAbortRunFuel_refines h h.height_le_next x
  cases source : (OrderedTree.insertAbortRun x t).1 with
  | none =>
      exact False.elim (absent ((OrderedTree.member_correct ordered x).mp
        ((OrderedTree.insertAbortRun_none_iff x t).mp source)))
  | some value =>
      have valueEq := OrderedTree.insertAbortRun_success source
      rw [source] at rel
      cases rel with
      | @some out _ info =>
          refine ⟨out, ?_, ?_⟩
          · simp only [insertAbortRun, handleAbort, run, Option.map_some, Option.getD_some]
          · simpa [abortProfile, source, valueEq] using info

theorem insertCandidateRun_absent {s : Store α} {root : Root} {t : BinaryTree α}
    (h : Represents s.heap root t) (ordered : OrderedTree.Ordered t) {x : α}
    (absent : ¬ OrderedTree.Contains x t) :
    ∃ out, insertCandidateRun s root x = (some out, candidateProfile x none t) ∧
      Inserted s root (candidatePath x t) ((candidatePath x t).length + 1)
        out (OrderedTree.insert x t) := by
  obtain ⟨result, run, rel⟩ := insertCandidateRunFuel_refines h h.height_le_next x none
  have lower : OrderedTree.LowerBound none t := trivial
  cases source : (OrderedTree.insertCandidateRun x none t).1 with
  | none =>
      have present := (OrderedTree.insertCandidateRun_none_iff ordered lower x).mp source
      exact False.elim (absent (by simpa using present))
  | some value =>
      have valueEq := OrderedTree.insertCandidateRun_success ordered lower source
      rw [source] at rel
      cases rel with
      | @some out _ info =>
          refine ⟨out, ?_, ?_⟩
          · simp only [insertCandidateRun, handleAbort, run, Option.map_some, Option.getD_some]
          · simpa [candidateProfile, source, valueEq] using info

theorem insertAbortRun_retention {s : Store α} {root old : Root}
    {t previous : BinaryTree α} (h : Represents s.heap root t)
    (kept : Represents s.heap old previous) (ordered : OrderedTree.Ordered t) (x : α) :
    ∃ out, insertAbortRun s root x = (some out, abortProfile x t) ∧
      Durability.Extends s.heap out.1.heap ∧
      Represents out.1.heap out.2 (OrderedTree.insert x t) ∧
      Represents out.1.heap old previous ∧
      out.1.next = s.next + (abortProfile x t).2.2 ∧
      (∀ probe, Diverges (searchPathBy id x t) probe →
        follow out.1.heap probe out.2 = follow out.1.heap probe root) ∧
      (abortProfile x t).1 ≤ 2 * t.height := by
  by_cases present : OrderedTree.Contains x t
  · have source := (OrderedTree.insertAbortRun_none_iff x t).mpr
      ((OrderedTree.member_correct ordered x).mpr present)
    have unchanged := OrderedTree.insert_of_member
      ((OrderedTree.member_correct ordered x).mpr present)
    refine ⟨(s, root), ?_, Durability.Extends.refl _, ?_, kept, ?_,
      fun _ _ => rfl, (abortProfile_bounds x t).1⟩
    · simpa [abortProfile, source] using insertAbortRun_duplicate h ordered present
    · simpa only [unchanged] using h
    · simp [abortProfile, source]
  · obtain ⟨out, run, extension, rep, count, rebuilt⟩ := insertAbortRun_absent h ordered present
    refine ⟨out, run, extension, rep, kept.mono extension, ?_,
      rebuilt.off_path extension, (abortProfile_bounds x t).1⟩
    have source : (OrderedTree.insertAbortRun x t).1 ≠ none := by
      intro aborted
      exact present ((OrderedTree.member_correct ordered x).mp
        ((OrderedTree.insertAbortRun_none_iff x t).mp aborted))
    simpa [abortProfile, Option.isSome_iff_ne_none.mpr source] using count

/-- The same combined execution simultaneously preserves the inserted value,
every retained old tree, actual off-path addresses, and its comparison bound. -/
theorem insertCandidateRun_retention {s : Store α} {root old : Root}
    {t previous : BinaryTree α} (h : Represents s.heap root t)
    (kept : Represents s.heap old previous) (ordered : OrderedTree.Ordered t) (x : α) :
    ∃ out, insertCandidateRun s root x = (some out, candidateProfile x none t) ∧
      Durability.Extends s.heap out.1.heap ∧
      Represents out.1.heap out.2 (OrderedTree.insert x t) ∧
      Represents out.1.heap old previous ∧
      out.1.next = s.next + (candidateProfile x none t).2.2 ∧
      (∀ probe, Diverges (candidatePath x t) probe →
        follow out.1.heap probe out.2 = follow out.1.heap probe root) ∧
      (candidateProfile x none t).1 ≤ t.height + 1 := by
  by_cases present : OrderedTree.Contains x t
  · have source := (OrderedTree.insertCandidateRun_none_iff ordered
      (show OrderedTree.LowerBound none t from trivial) x).mpr (Or.inl present)
    have unchanged := OrderedTree.insert_of_member
      ((OrderedTree.member_correct ordered x).mpr present)
    refine ⟨(s, root), ?_, Durability.Extends.refl _, ?_, kept, ?_,
      fun _ _ => rfl, (candidateProfile_bounds x none t).1⟩
    · simpa [candidateProfile, source] using insertCandidateRun_duplicate h ordered present
    · simpa only [unchanged] using h
    · simp [candidateProfile, source]
  · obtain ⟨out, run, extension, rep, count, rebuilt⟩ := insertCandidateRun_absent h ordered present
    refine ⟨out, run, extension, rep, kept.mono extension, ?_,
      rebuilt.off_path extension, (candidateProfile_bounds x none t).1⟩
    have source : (OrderedTree.insertCandidateRun x none t).1 ≠ none := by
      intro aborted
      have found := (OrderedTree.insertCandidateRun_none_iff ordered
        (show OrderedTree.LowerBound none t from trivial) x).mp aborted
      exact present (by simpa using found)
    simpa [candidateProfile, Option.isSome_iff_ne_none.mpr source] using count

end Search.SharedTree
